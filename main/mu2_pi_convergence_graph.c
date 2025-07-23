#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main() {
    FILE *fp_csv = fopen("mu2_pi_convergence.csv", "w");
    if (!fp_csv) {
        printf("Failed to create output file.\n");
        return 1;
    }

    fprintf(fp_csv, "limit,pi_approximation\n");

    const int mu = 2;
    const int steps = 200;
    const long long start_limit = 100;
    const long long end_limit = 100000000;

    for (int i = 0; i < steps; i++) {
        long long limit = start_limit + (end_limit - start_limit) * i / (steps - 1);

        char command[512];
        snprintf(command, sizeof(command),
            "echo \"%lld\n%d\ny\n%d\n%d\" | ./Llow_by_Uup_any_mu",
            limit, mu, mu, mu);

        FILE *fp = popen(command, "r");
        if (!fp) {
            printf("Failed to run command for limit = %lld\n", limit);
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

        fprintf(fp_csv, "%lld,%.15f\n", limit, final_product);
        printf("Saved: limit = %lld -> %.15f\n", limit, final_product);
    }

    fclose(fp_csv);
    printf("Completed. Results saved to mu2_pi_convergence.csv\n");
    return 0;
}
