#include <stdio.h>
#include <stdlib.h>
#include <math.h>

int main() {
    int mu, limit;
    printf("Enter mu: ");
    scanf("%d", &mu);
    printf("Enter limit: ");
    scanf("%d", &limit);

    // Build the filename like "7.csv"
    char filename[20];
    snprintf(filename, sizeof(filename), "%d.csv", mu);

    FILE *fp = fopen(filename, "w");
    if (fp == NULL) {
        printf("Error opening file!\n");
        return 1;
    }

    int upper[limit], lower[limit], squares[limit];

    // Compute values
    for (int n = 1; n <= limit; n++) {
        int sq = n * n;
        squares[n-1] = sq;
        upper[n-1] = (int)ceil((double)sq / mu);
        lower[n-1] = (int)floor((double)sq / mu);
    }

    // Row 1: Squares
    for (int i = 0; i < limit; i++) {
        fprintf(fp, "%d", squares[i]);
        if (i != limit - 1) fprintf(fp, ",");
    }
    fprintf(fp, "\n");

    // Row 2: Upper Index (if different)
    for (int i = 0; i < limit; i++) {
        if (upper[i] != lower[i])
            fprintf(fp, "%d", upper[i]);
        if (upper[i] == lower[i])
            fprintf(fp, "");
        if (i != limit - 1) fprintf(fp, ",");
    }
    fprintf(fp, "\n");

    // Row 3: Common Index (if same)
    for (int i = 0; i < limit; i++) {
        if (upper[i] == lower[i])
            fprintf(fp, "%d", upper[i]);
        if (i != limit - 1) fprintf(fp, ",");
    }
    fprintf(fp, "\n");

    // Row 4: Lower Index (if different)
    for (int i = 0; i < limit; i++) {
        if (upper[i] != lower[i])
            fprintf(fp, "%d", lower[i]);
        if (upper[i] == lower[i])
            fprintf(fp, "");
        if (i != limit - 1) fprintf(fp, ",");
    }
    fprintf(fp, "\n");

    fclose(fp);
    printf("CSV file saved as %s\n", filename);

    return 0;
}
