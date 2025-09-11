# Discrete Square Residual Structure (DSRS)

[![DOI](https://zenodo.org/badge/1011134407.svg)](https://doi.org/10.5281/zenodo.17101635)

This is the first preprint of the DSRS framework. Later versions may include stronger proofs, extended results, and additional numerical experiments.
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17101750.svg)](https://doi.org/10.5281/zenodo.17101750)

The **Discrete Square Residual Structure (DSRS)** is an original mathematical framework that explores relationships between square residuals, discrete indexing, and special constants. This repository hosts C implementations of functions derived from DSRS, as well as examples, test cases, and documentation.

## Overview

DSRS examines how residuals of squares interact when structured under specific discrete rules. Notably, some results have deep connections to classical formulas such as the Wallis Product, as well as integer sequences (e.g., OEIS A052928, A063196). 

Through this repository, the intention is to:
- Provide clean, reproducible C code implementing the core DSRS formulas.
- Allow further exploration of how these structures generalize for different parameters (e.g., varying `mu`).
- Share examples illustrating the computational patterns that arise from DSRS.

## Features

- **C Functions:** Efficient, modular implementations of DSRS-related functions.
- **Example Programs:** Simple examples demonstrating how to use the functions.
- **Documentation:** Explanations of the formulas and their connections to known mathematical results.

## Repository Structure

This project is organized into two main directories:

1. **main/**  
   This directory contains generalized programs that can be run for **any** `mu` value you choose.  
   For example, `upUPandLowlow_display.c` will prompt you to enter `mu` and `limit` interactively, making it flexible for different analyses.

2. **specific_mu/**  
   This directory includes versions of the programs preconfigured for **specific `mu` values** (e.g., 2, 3, 4, 5).  
   These are useful for reproducible studies or quick generation of CSVs without re-entering parameters.

---
### main/
#### 📂 `up_low_csvMaker.c`

This C program generates a structured CSV file based on the **Discrete Square Residual Structure (DSRS)** model. It takes two inputs from the user:

1. `mu` — the divisor parameter for the DSRS formula.
2. `limit` — how many square numbers (from 1² up to n²) to compute.

The program computes the **Upper Index** and **Lower Index** for each square using the following formulas:
- **Upper Index**: `ceil(n² / mu)`
- **Lower Index**: `floor(n² / mu)`

It saves the output in a file named `<mu>.csv` (e.g., `7.csv` if `mu = 7`) with the following format:

- **Row 1**: All square numbers from 1² to n².
- **Row 2**: Upper Indices where they differ from Lower.
- **Row 3**: Common Index values (where Upper = Lower).
- **Row 4**: Lower Indices where they differ from Upper.

This structured CSV format helps visually distinguish between common and differing index values, supporting further analysis of the DSRS model and patterns.


#### 📂 `Llow_by_Uup_any_mu.c`
##### Inputs and Usage

This program computes a product of terms derived from **Discrete Square Residual Structures** (DSRS), where each term is the ratio of the incremental difference in the low sequence (*low_low*) to the incremental difference in the up sequence (*up_up*).
 
It takes the following inputs:

1. **Limit (l)**
   - The maximum value of *n* up to which sequences are generated.
   - Accepts very large values (millions or billions) thanks to `long long` integers and dynamic memory allocation.

2. **Mu (μ)**
   - The divisor parameter in the formulas:
     - up = ceil(n² / μ)
     - low = floor(n² / μ)
   - Controls the spacing and behavior of the sequences.

3. **Custom Start Indices**
   - The program asks if you want to provide your own starting indices for the *up_up* and *low_low* sequences.
   - If you enter `y` or `Y`:
     - The program prints the first *mu* elements of both sequences (including any initial zeros).
     - You specify 1-based indices to start from in each sequence.
   - If you enter `n`:
     - The program automatically finds the first index where both sequences have positive non-zero values.


**How it works:**
- For each *n*, it computes:
  - `up[n] = ceil(n² / μ)`
  - `low[n] = floor(n² / μ)`
- Then it calculates the incremental differences:
  - `up_up[n] = up[n+1] - up[n]`
  - `low_low[n] = low[n+1] - low[n]`
- From your chosen starting indices, it processes each term:
  - **term = (low_low) / (up_up)**
- These ratios are multiplied sequentially to build the cumulative product.
- After all terms are processed:
  - If the product is less than 2, it multiplies the final result by 2.
  - Otherwise, it leaves the product unchanged.


**Note:**
- The program automatically handles large datasets.
- Dynamic memory ensures you can safely run high limits without stack overflow.
- If any `up_up` term is zero, it skips that term to avoid division by zero.



---

#### 📂 `upUPandLowlow_display.c`

This program generates a CSV visualization of DSRS sequences for a given `mu` and limit.

**Functionality:**
- Computes:
  - `n^2` for `n = 1` to `limit`
  - `up = ceil(n^2 / mu)`
  - `low = floor(n^2 / mu)`
  - `up_up = up[n+1] - up[n]`
  - `low_low = low[n+1] - low[n]`
- Outputs a CSV named `<mu>extra.csv` with 7 rows:

  1. **n square**: List of squares
  2. *(blank spacer row)*
  3. **up up**: Differences between consecutive `up` values (positioned between columns)
  4. **up**: Ceiling values in alternating format
  5. **common terms**: Cells where `up` and `low` are equal
  6. **low**: Floor values in alternating format
  7. **low low**: Differences between consecutive `low` values (positioned between columns)

**Usage:**

1. **Compile:**
   ```bash
   gcc upUPandLowlow_display.c -o dsrs -lm

#### 📂 `low_by_up_ratio.c`

This program computes the product of ratios between entries of two integer sequences derived from squares of indices divided by a user-specified parameter `mu`.

**How it works:**
- **Input parameters:**
  - `mu`: Divisor used to calculate `lower` and `upper` arrays.
  - `L`: The number of terms (array length).
  - `k`: The starting index for the `upper` array when forming ratios.
- **Procedure:**
  1. For each `n = 1` to `L`, compute:
     - `lower[n] = floor(n² / mu)`
     - `upper[n] = ceil(n² / mu)`
  2. Skip initial entries of `lower` that are zero.
  3. Starting from `start_lower` and user-specified `k`, compute the product:
     \[
     \prod_i \frac{lower[start\_lower + i]}{upper[k + i]}
     \]
  4. Print the resulting product in scientific notation.

- **Usage:**
  Compile and run:
  ```bash
  gcc -o low_by_up_ratio low_by_up_ratio.c
  ./low_by_up_ratio


---
### specific_mu/ or **special's**
---

#### 📂 `2s_downD_by_upU_my_wallis.c`

This C program computes a product related to the Wallis formula using a custom representation inspired by the **Discrete Square Residual Structure** approach.  

**How it works:**
- Takes `L`, the number of terms in the product.
- For each term `n`, it computes:
  - Numerator: `2 * floor((n+1)/2)`
  - Denominator: `2 * floor(n/2) + 1`
- Multiplies all such fractions together.
- The final result is scaled by 2:

$$
\text{Result} = 2 \times \prod_{n=1}^{L} \frac{\text{Numerator}}{\text{Denominator}}
$$
- Includes a check for numeric overflow or underflow during computation.

This implementation numerically approximates the Wallis product representation of π in a discrete and factorized form.

#### 📂 `2s_logV.c`

This C program provides an alternative **logarithmic formulation** of the same product computed in `2s_downD_by_upU_my_wallis.c`.  

**How it works:**
- Takes `L`, the number of terms.
- Initializes the sum with `log(2)`.
- For each term `n`, computes:
  - Numerator: `2 * floor((n+1)/2)`
  - Denominator: `2 * floor(n/2) + 1`
  - Ratio: `numerator / denominator`
- Accumulates the logarithm of each ratio:

$$
\log(\text{Result}) = \log(2) + \sum_{n=1}^{L} \log\left(\frac{\text{Numerator}}{\text{Denominator}}\right)
$$


- Exponentiates the final sum to obtain the product.

This logarithmic approach improves numeric stability for large `L` by avoiding intermediate overflows.

---

#### 📂 `3s_low_by_up.c`

This program computes the following product for a given upper limit `l`:

$$
\prod_{n=1}^{l}\frac{
\left\lfloor \frac{2(n+1)}{3}\right\rfloor
}{
2\left\lfloor \frac{n}{3}\right\rfloor + 1
}
$$

**How it works:**
- Takes input `l` from the user.
- Iterates `n` from 1 to `l`.
- Computes numerator and denominator using integer division and rounding functions.
- Multiplies all terms sequentially to form the final product.
- Prints the final product with high precision.

This file is named `3s_low_by_up.c`.

---
#### 📂 `4s_low_by_up.c`

This program computes the following product for a given upper limit `l`:

$$
\prod_{n=1}^{l}\frac{
\left\lceil \frac{n+1}{2}\right\rceil
}{
2\left\lceil \frac{n}{2}\right\rceil - \left\lfloor \frac{n}{2}\right\rfloor
}
$$

**How it works:**
- Takes input `l` from the user.
- Iterates `n` from 1 to `l`.
- Calculates numerator and denominator using floor division.
- Multiplies all terms step by step to compute the cumulative product.
- Prints the final product with high precision.

This file is named `4s_low_by_up.c`.


---
#### 📂 `5s_lowLow_by_upUp.c`

This program computes the following product for a given upper limit `l`:

$$
\prod_{n=1}^{l}\frac{
\left\lceil \frac{n-1}{5} \right\rceil + \left\lceil \frac{n}{5} \right\rceil
}{
\left\lceil \frac{n}{5} \right\rceil + \left\lceil \frac{n-1}{5} \right\rceil - \left\lceil \frac{n-2}{5} \right\rceil + 2 \left\lceil \frac{n-3}{5} \right\rceil - \left\lceil \frac{n-4}{5} \right\rceil
}
$$


**How it works:**
- Takes input `l` from the user.
- Iterates `n` from 1 to `l`.
- Computes the numerator and denominator for each term using integer division.
- For negative arguments in the ceiling function, the program returns `0` to avoid negative counts.
- Multiplies all fractions in sequence to get the final product.
- Prints the final product with high precision.

This file is named `5s_lowLow_by_upUp.c`.


