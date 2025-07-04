#include <stdio.h>
#include <stdlib.h>
#include <math.h>

int main() {
    int mu, l;
    printf("Enter mu: ");
    scanf("%d", &mu);
    printf("Enter limit l: ");
    scanf("%d", &l);

    // Build filename like "7.csv"
    char filename[25];
    snprintf(filename, sizeof(filename), "%dextra.csv", mu);


    FILE *fp = fopen(filename, "w");
    if (fp == NULL) {
        printf("Error opening file!\n");
        return 1;
    }

    int squares[l];
    int up[l];
    int low[l];
    int up_up[l - 1];
    int low_low[l - 1];

    // Compute n^2, up, low
    for (int n = 1; n <= l; n++) {
        int sq = n * n;
        squares[n - 1] = sq;
        up[n - 1] = (int)ceil((double)sq / mu);
        low[n - 1] = (int)floor((double)sq / mu);
    }

    // Compute up_up and low_low differences
    for (int n = 0; n < l - 1; n++) {
        up_up[n] = up[n + 1] - up[n];
        low_low[n] = low[n + 1] - low[n];
    }

    // --------------------
    // Row 1: n square
    fprintf(fp, "n square,");
    for (int i = 0; i < l; i++) {
        fprintf(fp, "%d", squares[i]);
        if (i != l - 1) fprintf(fp, ",");
    }
    fprintf(fp, "\n");

    // Row 2: blank
    fprintf(fp, "\n");

    // Row 3: up up
    fprintf(fp, "up up,");
    for (int i = 0; i < l * 2 - 1; i++) {
        if (i % 2 == 1 && (i / 2) < l - 1) {
            fprintf(fp, "%d", up_up[i / 2]);
        }
        if (i != l * 2 - 2) fprintf(fp, ",");
    }
    fprintf(fp, "\n");

    // Row 4: up
    fprintf(fp, "up,");
    for (int i = 0; i < l * 2 - 1; i++) {
        if (i % 2 == 0 && (i / 2) < l) {
            fprintf(fp, "%d", up[i / 2]);
        }
        if (i != l * 2 - 2) fprintf(fp, ",");
    }
    fprintf(fp, "\n");

    // Row 5: common terms
    fprintf(fp, "common terms,");
    for (int i = 0; i < l * 2 - 1; i++) {
        if (i % 2 == 0 && (i / 2) < l) {
            if (up[i / 2] == low[i / 2]) {
                fprintf(fp, "%d", up[i / 2]);
            }
        }
        // else leave blank
        if (i != l * 2 - 2) fprintf(fp, ",");
    }
    fprintf(fp, "\n");


    // Row 6: low
    fprintf(fp, "low,");
    for (int i = 0; i < l * 2 - 1; i++) {
        if (i % 2 == 0 && (i / 2) < l) {
            fprintf(fp, "%d", low[i / 2]);
        }
        if (i != l * 2 - 2) fprintf(fp, ",");
    }
    fprintf(fp, "\n");

    // Row 7: low low
    fprintf(fp, "low low,");
    for (int i = 0; i < l * 2 - 1; i++) {
        if (i % 2 == 1 && (i / 2) < l - 1) {
            fprintf(fp, "%d", low_low[i / 2]);
        }
        if (i != l * 2 - 2) fprintf(fp, ",");
    }
    fprintf(fp, "\n");


    fclose(fp);
    printf("CSV file saved as %s\n", filename);

    return 0;
}
