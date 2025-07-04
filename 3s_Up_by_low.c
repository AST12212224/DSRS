#include <stdio.h>

int main() {
    int l;
    printf("Enter value of l: ");
    scanf("%d", &l);

    double product = 1.0;

    for (int n = 1; n <= l; n++) {
        int numerator = 2 * (n / 3) + 1;
        int denominator = (2 * (n + 1)) / 3;
        product *= (double)numerator / denominator;
    }

    printf("Final Product for l = %d is: %.10f\n", l, product);
    return 0;
}
