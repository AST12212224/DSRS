#include <stdio.h>

int main() {
    long long L;
    printf("Enter limit L (number of terms in product): ");
    scanf("%lld", &L);

    double product = 1.0;

    for (long long n = 1; n <= L; n++) {
        long long numerator_floor = (n + 1) / 2;
        long long denominator_floor = n / 2;

        double numerator = numerator_floor * 2.0;
        double denominator = (denominator_floor * 2.0) + 1.0;

        product *= (numerator / denominator);

        // Check for overflow
        if (product == 0.0 || product == 1.0/0.0) {
            printf("Warning: product overflow or underflow at n = %lld\n", n);
            break;
        }
    }

    double result = 2.0 * product;

    printf("Result: %.10e\n", result);

    return 0;
}
