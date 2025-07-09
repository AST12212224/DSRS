#include <stdio.h>
#include <stdlib.h>
#include <math.h>

// Function to find the automatic start index where both up_up and low_low > 0
int find_start_index(long long up_up[], long long low_low[], long long size) {
    for (long long i = 0; i < size; i++) {
        if (up_up[i] > 0 && low_low[i] > 0) {
            return i;
        }
    }
    return size; // skip all if nothing found
}

int main() {
    long long l, mu;

    // Input
    printf("Enter limit l: ");
    scanf("%lld", &l);

    printf("Enter mu: ");
    scanf("%lld", &mu);

    // Arrays (allocated dynamically)
    long long* up = (long long*)malloc(l * sizeof(long long));
    long long* low = (long long*)malloc(l * sizeof(long long));
    long long* up_up = (long long*)malloc((l - 1) * sizeof(long long));
    long long* low_low = (long long*)malloc((l - 1) * sizeof(long long));

    if (!up || !low || !up_up || !low_low) {
        printf("Memory allocation failed.\n");
        return 1;
    }

    // Compute up and low
    for (long long n = 0; n < l; n++) {
        long double div = (long double)(n * n) / mu;
        up[n] = (long long)ceill(div);
        low[n] = (long long)floorl(div);
    }

    // Compute up_up and low_low
    for (long long n = 0; n < l - 1; n++) {
        up_up[n] = up[n + 1] - up[n];
        low_low[n] = low[n + 1] - low[n];
    }

    // Ask if user wants to provide their own start indices
    char choice;
    printf("Do you want to provide your own start indices? (y/n): ");
    scanf(" %c", &choice);

    long long start_index_up = 0;
    long long start_index_low = 0;

    if (choice == 'y' || choice == 'Y') {
        // Display first mu elements of up_up horizontally
        printf("First %lld elements of up_up:\n", mu);
        for (long long i = 0; i < mu && i < l - 1; i++) {
            printf("[%lld] %lld   ", i + 1, up_up[i]);
        }
        printf("\n");

        // Display first mu elements of low_low horizontally
        printf("First %lld elements of low_low:\n", mu);
        for (long long i = 0; i < mu && i < l - 1; i++) {
            printf("[%lld] %lld   ", i + 1, low_low[i]);
        }
        printf("\n");

        // Get user-defined start indices (1-based)
        printf("Enter start index for up_up: ");
        scanf("%lld", &start_index_up);

        printf("Enter start index for low_low: ");
        scanf("%lld", &start_index_low);

        // Convert to 0-based
        start_index_up -= 1;
        start_index_low -= 1;

        // Validate
        if (start_index_up < 0 || start_index_up >= l - 1 || start_index_low < 0 || start_index_low >= l - 1) {
            printf("Invalid start indices. Exiting.\n");
            free(up); free(low); free(up_up); free(low_low);
            return 0;
        }
    } else {
        // Apply DSRS backbone logic
        long long dsrs_start = (mu % 4 == 0) ? ((mu + 2) / 2 - 1) : (mu - 1);

        if (dsrs_start >= l - 1) {
            printf("DSRS start index (%lld) is too large for the given limit. Exiting.\n", dsrs_start);
            free(up); free(low); free(up_up); free(low_low);
            return 0;
        }

        start_index_up = start_index_low = dsrs_start;
        printf("(DSRS Mode) Since μ = %lld, starting from ΔL(n) and ΔU(n) at n = %lld (index = %lld)\n", mu, dsrs_start + 1, dsrs_start);
    }

    // Determine how many terms can be multiplied
    long long remaining_up = (l - 1) - start_index_up;
    long long remaining_low = (l - 1) - start_index_low;
    long long max_steps = (remaining_up < remaining_low) ? remaining_up : remaining_low;

    if (max_steps <= 0) {
        printf("No terms to multiply after applying start indices.\n");
        free(up); free(low); free(up_up); free(low_low);
        return 0;
    }

    // Compute product
    long double product = 1.0L;

    for (long long i = 0; i < max_steps; i++) {
        long long index_up = start_index_up + i;
        long long index_low = start_index_low + i;
        if (up_up[index_up] == 0) {
            printf("Warning: Division by zero at term %lld. Skipping.\n", i + 1);
            continue;
        }
        product *= (long double)low_low[index_low] / up_up[index_up];
    }

    printf("Initial product = %.15Lf\n", product);

    // Apply final adjustment
    if (product > 1.0L && product < 2.0L) {
        product *= 2.0L;
        printf("Product >1 and <2, multiplied by 2.\n");
    } else {
        printf("Product not in (1,2), left unchanged.\n");
    }

    printf("Final product = %.15Lf\n", product);

    // Clean up
    free(up);
    free(low);
    free(up_up);
    free(low_low);

    return 0;
}
