# CHANGES — revision of "Discrete Square Residual Structures" → "A floor–ceiling Wallis-type product for π and a mod 4 dichotomy"

Status: `main.tex` compiles with `pdflatex → bibtex → pdflatex ×2` with **0 errors, 0 warnings, 0 undefined references** (one harmless underfull box). The PDF is **8 pages** (amsart, 10pt). `python3 verify.py` prints **39/39 PASS** in about 25 s. `python3 verify.py --audit` also re-runs the checks of the *original* manuscript's claims summarised below.

Notation: L(n)=⌊n²/μ⌋, U(n)=⌈n²/μ⌉, Δ = forward difference, P_N(μ)=∏_{n=μ}^{N} Δ_L(n)/Δ_U(n).

---

## 1. Mathematical errors found and how they were fixed

| # | Original claim | What verify.py found | Fix |
|---|---|---|---|
| 1 | P(μ) → π/2 when 4∤μ; π ≈ 2·P_N(μ) | P_{10⁶}(μ) = 0.7853978 (μ=2), 0.7853976 (3), 0.7853972 (5), 0.7853970 (6), i.e. **π/4**. The original numerical tables were in fact 4·P_N; only the text said 2·P_N. | Limit is π/4 everywhere (abstract, theorem, tables). π ≈ 4·P_N(μ). |
| 2 | Start n₀ = (μ+2)/2 when 4∣μ gives limit 1 | **False: from n₀ = (μ+2)/2 the limit is 2** (exactly: ∏_{n=(μ+2)/2}^{μ−1} = 2 for all 4∣μ ≤ 300; proved in the paper). From n₀ = μ/2 it is 1. | Single start **n₀ = μ for all μ**. Remark 1 explains the excluded terms: Δ_L(0)=0 (μ≥2); Δ_U(1)=0, so the factor is undefined (μ≥4). n₀=1 works only for μ∈{1,2,3} and gives π/2 for μ=2,3. It also gives the constants for n₀ = μ/2 and (μ+2)/2. All are proved and checked. |
| 3 | Error O(1/√N); "Wallis converges at O(1/√N)" | N·(4P_N − π) is constant in N: **−πμ/4** (−1.571, −2.356, −3.927, −4.712 for μ=2,3,5,6). The sign flips to +πμ/4 when N ≡ −1 (mod M). For 4∣μ, N(P_N−1) → −μ/2, or 0 when N ≡ −1 (mod M). | O(1/N) stated, with the constants in **Observation 1** (numerical, not proved; checked for 2≤μ≤30, all residues of N). The Wallis O(1/√N) claim was deleted. |
| 4 | Lemma 2.1 says α>0; Table 1 lists α<0; App. A.3 says α=−1 but its example gives α=+1 | With α = μU(n) − n², α ≥ 0 always. Table 1 had used n² − μU(n). | Residuals α, β are not needed for the proof, so they were **removed entirely**. |
| 5 | P(μ) defined twice (infinite product and the γ-block product) | — | Block product renamed **B_γ(μ)**; P(μ) is only the infinite product. |
| 6a | μ=2 formula (eq. pi-mu2), stated with "≈" | Correct, and an exact identity: π = 2∏_{n≥1}. The factor 2 is c(2,1)=2 (Remark 1). | Kept (Remark 2) with "=" and a proof. |
| 6b | μ=3 formula | Correct for n≥1, exact identity. | Kept (Remark 2) with a proof. |
| 6c | μ=5 formula (eq. pi-mu5) | Factors **do not** equal Δ_L(n)/Δ_U(n) (mismatch at n=1,3,4,5,8,9,10,…; at n=1 the true ratio is 0/0). Its partial product 2∏_{n≤10⁵} = 3.1415534 suggests it may still tend to π, but there is no proof. | **Deleted.** |
| 6d | μ=4 formula (eq. 10), ∏_{n≥1} = 1 | True, but it is the μ=4 product started at n=2 with the index shifted by one. | Deleted as redundant; covered by Remark 1 (start μ/2 gives 1). |
| 7 | Gap parameter g(μ) table; Theorem 5.2 (bidirectional crossing) | With the natural definition (minimal offset k_n ≥ 1, starting at μ/2), g(8)=2 (paper 3), g(20)=4 (9), g(24)=4 (13), g(16)=3 ✓, g(64)=7 ✓, g(4)=1 ✓. For **μ=12, 28, 32 the backward crossing does not exist**: e.g. μ=12, n=9, Δ_U(9)=2, but no m<9 has Δ_L(m)=2. In the μ=8 example, n=13 has offset 1 (Δ_L(12)=3), not 3. | **Theorem 5.2 is false as stated; section removed.** No definition of g gave all the table values. |
| 8 | Lemma 5.8 rewrote 2γ(2γ+2)/(2γ+1)² = (2γ/(2γ−1))(2γ/(2γ+1)) term by term | That identity is false (checked). Marco's original identity R_G = W_G·(G+1)/(2G+1) is correct. | Lemma D uses Marco's identity, with a factorial proof. Exact check for G ≤ 500. |
| 9 | Lemma 5.6 case "δ = (μ−1)/2 ⇒ factor 1" | Cannot occur for μ ≥ 2: if μ∣δ² or μ∣(δ+1)², then 2δ+1 ≠ μ (proved; Lemma B(5)). | Explained in a one-line remark after Lemma B. |
| 10 | Prop 5.7 counts a, b and "a−b=0 iff 4∣μ" were asserted without proof | Both are correct. | Full proofs (Prop C, Steps 1–4). |
| 11 | Lemma 5.8 number 0.7853971816527053 (μ=5, N=10⁶) | The 60-digit value is 0.785397181652812…: a floating-point error in the 13th digit. | Number removed (Table 1 has the correct values). |
| 12 | Table "P_N(4) = 0.98000 at N=100" | 0.98039 (from n₀=2 or 4); from the paper's own start n₀=3 it is **1.96078**. | Table replaced (Table 2). |
| 13 | Random-μ table: μ=999, N=10⁷ → 3.14154 | 4P_N(999) = 3.1415140 (other rows agree to the printed digits: 1009, 8888, 9999, 65537). μ=1147 (N=10⁶) and μ=11111 (N=10⁸) were not recomputed. | Table replaced by Table 2 (N=10⁷, recomputed, both residue classes). |
| 14 | "A052928 and A063196 encode the Wallis product" | A052928 = even numbers repeated. A063196 is a modular-forms dimension sequence that *coincides* with Δ_U for μ=2 (from index 2). Verified: Δ_L(n)=A052928(n+1), n≥0; Δ_U(n)=A063196(n+1), n≥1. | Stated as coincidence of terms with exact offsets. OEIS table entries for μ=3,4 were not verified and were dropped. |
| 15 | "μ ≢ 0 (mod 4) ⇒ π/2" also covered μ=1 | μ=1 gives 1. | Theorem now says "μ ≥ 2 and 4∤μ". |

**§6.1 ("Structural Reduction via Residual Cancellation"), as you asked.** The vague "≈" statement (Prop. 6.6) turned out to have an exact form, now **proved as Proposition E**. Over complete blocks n = μ,…,μ(G+1)−1:
- if 4∤μ, the cleaned multisets are exactly {3,3,5,5,…,2G+1,2G+1} and {2,4,4,…,2G,2G,2G+2}. This holds for *every* such μ and is the μ=2 picture.
- if 4∣μ, the two multisets are equal.

It was checked exactly for μ ≤ 300, G ≤ 10. The original examples, which started at n=1 with ragged N, had boundary effects; the exact statement needs complete blocks starting at n=μ.

## 2. Removed, and why

- **Coined names**: "Discrete Square Residual Structures", "DSRS" (kept once, in a footnote on the repository), "residual entropy", "cleaned sequences", "archetypal", "sharp", "robustness", "zero-entropy", "intrinsic structure, not numerical coincidence".
- **§6.1 multiset heuristics, Prop 6.6, Cor 6.7 (entropy)**: replaced by the proved Proposition E. The entropy corollary had no definition that could be checked.
- **"Primality is irrelevant" and "Role of μ=2" remarks**: redundant given the proof.
- **Proof sketches** of Thm 2.3 and Prop 5.1: replaced by the full proof.
- **Residuals α, β, Lemma 2.1, Table 1, observed "periodicity"**: not needed (see #4).
- **Gap parameter section, Theorem 5.2, Example 5.3, Remark 5.4**: false or ambiguous (see #7).
- **μ=4, μ=5 formulas**: see #6c, #6d.
- **Ramanujan/Viète comparison** and the Borwein, Borwein–Borwein and Beckmann references: no longer cited.
- **Appendix A**: the μ=2 closed forms moved into Remark 2; the rest removed. **Appendix B**: folded into Data availability.
- **All three figures**: not reproducible from verified data, and their captions relied on "entropy". The spikes in `pi-approx-graph.png` probably come from the sign flip in Observation 1, but I could not reproduce the plot, so it was dropped. Tables 1–2 carry the computational evidence instead.
- **Packages/macros**: interact class, natbib, subfig, epstopdf, multicol, multirow, float, tikz, lmodern, and every `\vspace`.

## 3. New material (all proved, or labelled)

- Lemma A: full proof (the original said "some calculations give"). Lemma B: complete case proofs, including exclusivity and 2δ+1 ≠ μ.
- Prop C: proofs of μ∣δ² ⇔ M∣δ, the counts a = ⌈T/2⌉ and b = ⌊T/2⌋, and "T even ⇔ 4∣μ" via v₂.
- Lemma D: Marco's identity R_G = W_G (G+1)/(2G+1), proved with factorials.
- Proof of Theorem 1, including **incomplete blocks**: x_G^{2μ} ≤ Q_{G,r} ≤ x_G^{−2μ}, so the limit exists along all N.
- Remark 3 (immediate from Prop C): P_{μG−1}(μ) = 1 exactly if 4∣μ, and = R_{G−1} (independent of μ) if 4∤μ.
- **Observation 1** (the 1/N constant): numerical only, clearly labelled.

## 4. Could not verify / not included

- **Lean 4 formalization** (update): the earlier Lean claims could not be checked, since no `.lean` files were found. A **new** formalization is now in `lean/` and builds with no errors and no `sorry`. It proves, for every μ ≥ 2: Lemma A, Lemma B, the counting step, Proposition C (block product) and Proposition E (structural reduction). It uses only Lean's standard axioms. The paper (§4 and Data availability) says exactly this, and states that the limit (Lemma D, incomplete blocks) is **not** formalized. The old pasted claims ("general case remains a conjecture", "μ=2 → π/2", "Lemma 2.1") are not used.
- **"Verified for μ ≤ 70,000"**: not reproduced. It is no longer needed, since the result is proved. I removed it rather than repeat it unchecked.
- **Observation 1**: not proved. A proof via Wallis asymptotics looks feasible, but it would be a new result, so I did not add one.
- Original rows for μ=1147 (N=10⁶) and μ=11111 (N=10⁸) were not recomputed.

## 5. Questions / actions for you

1. **AI declaration.** Resolved: no GPT-4 declaration needed; the statement names only Claude, as you specified.
2. **Marco's answer.** The paper credits Marco for the decomposition, the case analysis, the M/a/b counting and the reduction to Wallis. That matches his answer (math.stackexchange.com/a/5095888, 13 Sep 2025), which I read through the Stack Exchange API. Please confirm you're happy with that wording (Introduction, "Contributions").
3. **Upload `verify.py` to the GitHub repo.** The paper says it is there.
4. **Zenodo**: the cited preprint (10.5281/zenodo.17519713) still states π/2 and the (μ+2)/2 start. Consider uploading this version as a new Zenodo version. Its title contains "DSRS" in the reference list. Do you want to keep that citation (journals usually want preprints disclosed) or mention it only in the cover letter?
5. **Acknowledgments**: kept verbatim. Journals usually expect a full name for "Mukharji Uncle". Do you want to change it?
6. **Title**: kept as you proposed; I don't suggest a different one.
7. **Target journal**: if it is the *Journal of Integer Sequences*, they want a final "Concerned with sequences" line (A052928, A063196) and their own template. I can add this when you switch templates.
8. Unused files left in the folder: `interact.cls`, `tfq.bst`, the three PNGs, the old PDF. Delete them if you don't need them.
