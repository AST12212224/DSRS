#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main() {
    FILE *fp_pi = fopen("mu_pi.csv", "w");
    FILE *fp_1 = fopen("mu_1.csv", "w");
    if (!fp_pi || !fp_1) {
        printf("Failed to create output files.\n");
        return 1;
    }

    // Write headers
    fprintf(fp_pi, "mu,pi approximation\n");
    fprintf(fp_1, "mu,approximation of 1 or out of range\n");

    int mu_limit;
    printf("Enter upper mu limit: ");
    scanf("%d", &mu_limit);

    for (int mu = 2; mu <= mu_limit; mu++) {
        char command[512];

        // Send: l, mu, y, mu (for up_up), mu (for low_low)
        snprintf(command, sizeof(command),
            "echo \"1000000\n%d\ny\n%d\n%d\" | ./Llow_by_Uup_any_mu", mu, mu, mu);

        FILE *fp = popen(command, "r");
        if (!fp) {
            printf("Failed to run command for mu = %d\n", mu);
            continue;
        }

        char line[1024];
        double final_product = 0.0;
        while (fgets(line, sizeof(line), fp)) {
            if (strstr(line, "Final product =")) {
                sscanf(line, "Final product = %lf", &final_product);
                break;
            }
        }
        pclose(fp);

        if (final_product > 3.0 && final_product < 3.2)
            fprintf(fp_pi, "%d,%.15f\n", mu, final_product);
        else
            fprintf(fp_1, "%d,%.15f\n", mu, final_product/4);
    }

    fclose(fp_pi);
    fclose(fp_1);

    printf("Completed. Results saved to mu_pi.csv and mu_1.csv\n");
    return 0;
}
