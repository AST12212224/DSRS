#include <stdio.h>
#include <math.h>

int main() {
    long long l;
    printf("Enter value of l: ");
    scanf("%lld", &l);

    long double logSum = 0.0L;

    for (long long n = 1; n <= l; n++) {
        long long numerator = (n + 2) / 2;
        long long ceil_n_div_2 = (n + 1) / 2;
        long long floor_n_div_2 = n / 2;
        long long denominator = 2 * ceil_n_div_2 - floor_n_div_2;

        logSum += logl((long double)numerator) - logl((long double)denominator);
    }

    long double product = expl(logSum);

    printf("Final Product for l = %lld is: %.15Le\n", l, product);
    return 0;
}
