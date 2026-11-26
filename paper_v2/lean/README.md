# Lean 4 formalization: floor–ceiling Wallis-type product

This folder machine-checks the algebraic core of the paper
*A floor–ceiling Wallis-type product for π and a mod 4 dichotomy*:
Lemmas A and B, the counting step, Proposition C (block product) and
Proposition E (structural reduction / multiset cancellation), for every μ ≥ 2.
See the header of `FloorCeilWallis/Basic.lean` for the list of theorems.

The limit statement (Lemma D and the passage N → ∞) is **not** formalized here.

## Run it

Requirements: [elan](https://github.com/leanprover/elan) (installed automatically by the
VS Code Lean 4 extension).

```bash
cd lean
lake exe cache get   # downloads prebuilt Mathlib (first time only, several GB)
lake build           # should end with "Build completed successfully"
```

In VS Code: *File → Open Folder…* and choose this `lean` folder (the one containing
`lakefile.toml`), then open `FloorCeilWallis/Basic.lean`. The infoview shows no errors.

To list the axioms used (only Lean's standard `propext`, `Classical.choice`, `Quot.sound`):

```lean
import FloorCeilWallis
#print axioms FloorCeilWallis.structural_reduction
#print axioms FloorCeilWallis.block_product
```

Toolchain: Lean `v4.37.0-rc1`, Mathlib pinned in `lake-manifest.json`.
