#include <stdio.h>
#include <math.h>

int U(int n, int mu) {
    return (int)ceil((double)(n * n) / mu);
}

int L(int n, int mu) {
    return (int)floor((double)(n * n) / mu);
}

int main() {
    int mu_limit, term_limit;
    printf("Enter how many mu values: ");
    scanf("%d", &mu_limit);
    printf("Enter how many up-up and low-low terms: ");
    scanf("%d", &term_limit);

    for (int mu = 2; mu < 2 + mu_limit; mu++) {
        printf("\nmu = %d\n", mu);

        // Print up-up
        printf("%d up up:   ", mu);
        int prevU = U(1, mu);
        for (int n = 2; n <= term_limit + 1; n++) {
            int currU = U(n, mu);
            int up_up = currU - prevU;
            printf("%d ", up_up);
            prevU = currU;
        }
        printf("\n");

        // Print low-low
        printf("%d low low: ", mu);
        int prevL = L(1, mu);
        for (int n = 2; n <= term_limit + 1; n++) {
            int currL = L(n, mu);
            int low_low = currL - prevL;
            printf("%d ", low_low);
            prevL = currL;
        }
        printf("\n");
    }

    return 0;
}
