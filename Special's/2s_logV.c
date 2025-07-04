#include <stdio.h>
#include <math.h>

int main() {
    long long L;
    printf("Enter limit L (number of terms in product): ");
    scanf("%lld", &L);

    double log_sum = log(2.0);

    for (long long n = 1; n <= L; n++) {
        long long numerator_floor = (n + 1) / 2;
        long long denominator_floor = n / 2;

        double numerator = numerator_floor * 2.0;
        double denominator = (denominator_floor * 2.0) + 1.0;

        double ratio = numerator / denominator;
        log_sum += log(ratio);
    }

    double result = exp(log_sum);

    printf("Result: %.10e\n", result);

    return 0;
}
