#include <stdio.h>

// Compute ceil(x / y)
long long ceil_div(long long x, long long y) {
    // If x >= 0, standard formula
    if (x >= 0)
        return (x + y - 1) / y;
    else
        // For negative x, need to ensure rounding up
        return 0;
}

int main() {
    long long l;
    printf("Enter value of l: ");
    scanf("%lld", &l);

    long double product = 1.0L;

    for (long long n = 1; n <= l; n++) {
        long long ceil_n = ceil_div(n, 5);
        long long ceil_n_minus_1 = ceil_div(n - 1, 5);
        long long ceil_n_minus_2 = ceil_div(n - 2, 5);
        long long ceil_n_minus_3 = ceil_div(n - 3, 5);
        long long floor_n_minus_4 = ceil_div(n - 4,5);

        long long numerator = ceil_n_minus_1 + ceil_n;
        long long denominator = ceil_n
                              + ceil_n_minus_1
                              - ceil_n_minus_2
                              + 2 * ceil_n_minus_3
                              - floor_n_minus_4;

        product *= (long double)numerator / denominator;
    }

    printf("Final Product for l = %lld is: %.15Lf\n", l, 2*product);
    return 0;
}
