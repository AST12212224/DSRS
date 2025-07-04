#include <stdio.h>

int main() {
    long long mu, L;
    printf("Enter mu: ");
    scanf("%lld", &mu);

    printf("Enter limit L (number of terms): ");
    scanf("%lld", &L);

    long long lower[L+1];
    long long upper[L+1];

    // Compute lower and upper arrays
    for (long long n = 1; n <= L; n++) {
        long long n2 = n * n;
        lower[n] = n2 / mu;
        upper[n] = (n2 + mu - 1) / mu;
    }

    // Find first nonzero index in lower
    long long start_lower = 1;
    while (start_lower <= L && lower[start_lower] == 0) {
        start_lower++;
    }

    if (start_lower > L) {
        printf("All lower terms are zero. No product to compute.\n");
        return 0;
    }

    // Ask user to specify k (start index in upper)
    long long k;
    printf("Enter k (starting index in upper): ");
    scanf("%lld", &k);

    // Validate
    if (k < 1 || k + (L - start_lower) > L + 1) {
        printf("Error: k is out of bounds for the available terms.\n");
        return 1;
    }

    // Compute product
    double product = 1.0;
    for (long long i = 0; (start_lower + i) <= L; i++) {
        long long idx_lower = start_lower + i;
        long long idx_upper = k + i;

        double frac = (double)lower[idx_lower] / (double)upper[idx_upper];
        product *= frac;
    }

    printf("%.10e\n", product);

    return 0;
}
