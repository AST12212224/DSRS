//e approx giver
#include <stdio.h>

int main() {
    int limit, n;
    double ratio = 1.0;

    // Input from user
    printf("Enter the limit: ");
    scanf("%d", &limit);

    // Calculate the product of (4n^2)/(4n^2 - 1)
    for (n = 1; n <= limit; n++) {
        double numerator = 9.0 * n * n;
        double denominator = numerator - 1.57656;//(sqrt2+sqrt3)/2
        ratio *= numerator / denominator;
    }

    // Output result
    printf("Product of (4n^2)/(4n^2 - 1) for n = 1 to %d is: %.10f\n", limit, ratio*2);

    return 0;
}
//idk still doing
#include <stdio.h>

int main() {
    int limit, n;
    double ratio = 1.0;

    // Input from user
    printf("Enter the limit: ");
    scanf("%d", &limit);

    // Calculate the product of (4n^2)/(4n^2 - 1)
    for (n = 1; n <= limit; n++) {
        double numerator = 16.0 * n * n;
        double denominator = numerator - 2.8;//(sqrt2+sqrt3)/2
        ratio *= numerator / denominator;
    }

    // Output result
    printf("Product of (4n^2)/(4n^2 - 1) for n = 1 to %d is: %.10f\n", limit, ratio*2);

    return 0;
}
// average of root of primes sumation
#include <stdio.h>
#include <math.h>
#include <stdbool.h>

// Function to check if a number is prime
bool isPrime(int n) {
    if (n < 2) return false;
    for (int i = 2; i*i <= n; i++) {
        if (n % i == 0) return false;
    }
    return true;
}

int main() {
    int limit;
    printf("Enter the number of prime numbers to include: ");
    scanf("%d", &limit);

    int count = 0;
    int num = 2;
    double sum = 0.0;

    printf("Square roots of first %d prime numbers:\n", limit);
    while (count < limit) {
        if (isPrime(num)) {
            double root = sqrt(num);
            printf("sqrt(%d) = %.5f\n", num, root);
            sum += root;
            count++;
        }
        num++;
    }

    double average = sum / limit;
    printf("Sum = %.5f\n", sum);
    printf("Average = %.5f\n", average);

    return 0;
}
//\sqrt{2}+\sqrt{3}-\sqrt{5}-\sqrt{7}+\sqrt{11}-\sqrt{13}+\sqrt{17}-\sqrt{19}+\sqrt{23}-\sqrt{29}+\sqrt{31} = 2.71... new approx for e
