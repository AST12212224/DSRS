#include <stdio.h>

// Function to compute ceiling of integer division
int ceil_div(int numerator, int denominator) {
    if (numerator >= 0)
        return (numerator + denominator - 1) / denominator;
    else
        return numerator / denominator; // Safe for negative values
}

int main() {
    int limit;
    printf("Enter the limit: ");
    scanf("%d", &limit);

    for (int n = 1; n <= limit; n++) {
        int term = ceil_div(n - 1, 5)
                 + ceil_div(n - 2, 5)
                 - ceil_div(n - 3, 5)
                 + 2 * ceil_div(n - 4, 5)
                 - ceil_div(n - 5, 5);

        if (n < limit)
            printf("%d,", term);
        else
            printf("%d", term);  // No trailing comma on last value
    }

    printf("\n");
    return 0;
}
