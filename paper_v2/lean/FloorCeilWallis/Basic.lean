import Mathlib

/-!
# A floor–ceiling Wallis-type product: block cancellation (Lean 4 + Mathlib)

Companion formalization of the paper
"A floor–ceiling Wallis-type product for π and a mod 4 dichotomy" (A. Tikhe).

Fix a modulus `μ` and put `L n = ⌊n²/μ⌋`, `U n = ⌈n²/μ⌉`,
`dL n = L (n+1) - L n`, `dU n = U (n+1) - U n`.

Main results, for **every** `μ ≥ 2` (no computer search, no `sorry`):

* `L_eq_floor`, `U_eq_ceil`: the definitions are the floor and ceiling of `n²/μ`.
* `dL_block`, `dU_block` (Lemma A): `dL (μγ+δ) = 2γ + dL δ`, `dU (μγ+δ) = 2γ + dU δ`.
* `local_values_neither`, `local_values_zero`, `local_values_one` (Lemma B).
* `signed_count`: `∑_{δ<μ} [μ ∣ δ²]·([2δ+1<μ] - [2δ+1>μ]) = 1 - [4 ∣ μ]`,
  proved by the reflection `δ ↦ μ - δ`.
* `block_multiset`: on a block `n = μγ, …, μγ+μ-1`,
  `𝒰 + e•{2γ, 2γ+2} = ℒ + e•{2γ+1, 2γ+1}` with `e = [4 ∤ μ]`.
* `structural_reduction` (Proposition E): over `n = μ, …, μ(G+1)-1`, after cancelling
  common values, `𝒰 - ℒ = {3,3,5,5,…,2G+1,2G+1}` and `ℒ - 𝒰 = {2,4,4,…,2G,2G,2G+2}`
  if `4 ∤ μ`, and `𝒰 = ℒ` if `4 ∣ μ`.
* `block_product` (Proposition C): `∏_{block γ} dL/dU = 1` if `4 ∣ μ` and
  `4γ(γ+1)/(2γ+1)²` if `4 ∤ μ` (for `γ ≥ 1`).

Not formalized here: the passage to the limit (Lemma D, Wallis's product, and the
incomplete-block estimate in the proof of Theorem 1).
-/

namespace FloorCeilWallis

open Finset

variable (μ : ℕ)

/-- `L n = ⌊n²/μ⌋`. -/
def L (n : ℕ) : ℕ := n ^ 2 / μ

/-- `U n = ⌈n²/μ⌉` (for `μ > 0`). -/
def U (n : ℕ) : ℕ := (n ^ 2 + (μ - 1)) / μ

/-- Forward difference of `L`. -/
def dL (n : ℕ) : ℕ := L μ (n + 1) - L μ n

/-- Forward difference of `U`. -/
def dU (n : ℕ) : ℕ := U μ (n + 1) - U μ n

/-- The multiset of values `f n`, `n ∈ I`, counted with multiplicity. -/
def vals (f : ℕ → ℕ) (I : Finset ℕ) : Multiset ℕ := ∑ n ∈ I, ({f n} : Multiset ℕ)

variable {μ}

theorem L_eq_floor (n : ℕ) : L μ n = ⌊((n ^ 2 : ℕ) : ℚ) / μ⌋₊ :=
  (Nat.floor_div_eq_div _ _).symm

theorem L_mono (n : ℕ) : L μ n ≤ L μ (n + 1) :=
  Nat.div_le_div_right (Nat.pow_le_pow_left (Nat.le_succ n) 2)

theorem U_eq (hμ : 0 < μ) (n : ℕ) :
    U μ n = L μ n + (if μ ∣ n ^ 2 then 0 else 1) := by
  have hdm := Nat.div_add_mod (n ^ 2) μ
  have hlt := Nat.mod_lt (n ^ 2) hμ
  have key : n ^ 2 + (μ - 1) = (n ^ 2 % μ + (μ - 1)) + μ * (n ^ 2 / μ) := by omega
  rw [U, L, key, Nat.add_mul_div_left _ _ hμ]
  split_ifs with h
  · rw [Nat.mod_eq_zero_of_dvd h, zero_add, Nat.div_eq_of_lt (by omega)]
    ring
  · have hr : n ^ 2 % μ ≠ 0 := fun h' => h (Nat.dvd_of_mod_eq_zero h')
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    ring


theorem U_eq_ceil (hμ : 0 < μ) (n : ℕ) : U μ n = ⌈((n ^ 2 : ℕ) : ℚ) / μ⌉₊ := by
  have hμq : (0 : ℚ) < μ := by exact_mod_cast hμ
  have hdm : n ^ 2 / μ * μ + n ^ 2 % μ = n ^ 2 := by rw [mul_comm]; exact Nat.div_add_mod _ _
  have hlt := Nat.mod_lt (n ^ 2) hμ
  rw [U_eq hμ]
  split_ifs with h
  · have hr : n ^ 2 % μ = 0 := Nat.mod_eq_zero_of_dvd h
    have e : ((n ^ 2 : ℕ) : ℚ) / μ = ((n ^ 2 / μ : ℕ) : ℚ) := by
      rw [div_eq_iff hμq.ne']; exact_mod_cast (by omega : n ^ 2 = n ^ 2 / μ * μ)
    rw [e, Nat.ceil_natCast, L, add_zero]
  · have hr : n ^ 2 % μ ≠ 0 := fun h' => h (Nat.dvd_of_mod_eq_zero h')
    symm
    rw [Nat.ceil_eq_iff (by omega), Nat.add_sub_cancel, L]
    constructor
    · rw [lt_div_iff₀ hμq]; exact_mod_cast (by omega : n ^ 2 / μ * μ < n ^ 2)
    · rw [div_le_iff₀ hμq]
      exact_mod_cast (by rw [add_mul, one_mul]; omega : n ^ 2 ≤ (n ^ 2 / μ + 1) * μ)

theorem U_mono (n : ℕ) : U μ n ≤ U μ (n + 1) := by
  rw [U, U]
  exact Nat.div_le_div_right (by gcongr; omega)

/-! ### Lemma A -/

theorem L_block (hμ : 0 < μ) (γ δ : ℕ) :
    L μ (μ * γ + δ) = μ * γ ^ 2 + 2 * γ * δ + L μ δ := by
  have : (μ * γ + δ) ^ 2 = δ ^ 2 + μ * (μ * γ ^ 2 + 2 * γ * δ) := by ring
  rw [L, this, Nat.add_mul_div_left _ _ hμ, L]
  ring

theorem U_block (hμ : 0 < μ) (γ δ : ℕ) :
    U μ (μ * γ + δ) = μ * γ ^ 2 + 2 * γ * δ + U μ δ := by
  have : (μ * γ + δ) ^ 2 + (μ - 1) = (δ ^ 2 + (μ - 1)) + μ * (μ * γ ^ 2 + 2 * γ * δ) := by
    ring
  rw [U, this, Nat.add_mul_div_left _ _ hμ, U]
  ring

theorem dL_block (hμ : 0 < μ) (γ δ : ℕ) : dL μ (μ * γ + δ) = 2 * γ + dL μ δ := by
  have h1 := L_block hμ γ (δ + 1)
  have h2 := L_block hμ γ δ
  have hm := L_mono (μ := μ) δ
  have e : 2 * γ * (δ + 1) = 2 * γ * δ + 2 * γ := by ring
  rw [dL, dL, show μ * γ + δ + 1 = μ * γ + (δ + 1) by ring, h1, h2, e]
  omega

theorem dU_block (hμ : 0 < μ) (γ δ : ℕ) : dU μ (μ * γ + δ) = 2 * γ + dU μ δ := by
  have h1 := U_block hμ γ (δ + 1)
  have h2 := U_block hμ γ δ
  have hm := U_mono (μ := μ) δ
  have e : 2 * γ * (δ + 1) = 2 * γ * δ + 2 * γ := by ring
  rw [dU, dU, show μ * γ + δ + 1 = μ * γ + (δ + 1) by ring, h1, h2, e]
  omega

/-! ### Lemma B -/

theorem not_dvd_sq_of_mid (hμ : 2 ≤ μ) {δ : ℕ} (h : 2 * δ + 1 = μ) : ¬ μ ∣ δ ^ 2 := by
  intro hd
  obtain ⟨d, rfl⟩ : ∃ d, δ = d + 1 := ⟨δ - 1, by omega⟩
  have e : 4 * (d + 1) ^ 2 = μ * (2 * d + 1) + 1 := by rw [← h]; ring
  have h4 : μ ∣ μ * (2 * d + 1) + 1 := e ▸ Dvd.dvd.mul_left hd 4
  have h1 := (Nat.dvd_add_right (Dvd.intro _ rfl)).mp h4
  have := Nat.le_of_dvd one_pos h1
  omega

theorem not_dvd_succ_sq_of_mid (hμ : 2 ≤ μ) {δ : ℕ} (h : 2 * δ + 1 = μ) :
    ¬ μ ∣ (δ + 1) ^ 2 := by
  intro hd
  have e : 4 * (δ + 1) ^ 2 = μ * (2 * δ + 3) + 1 := by rw [← h]; ring
  have h4 : μ ∣ μ * (2 * δ + 3) + 1 := e ▸ Dvd.dvd.mul_left hd 4
  have h1 := (Nat.dvd_add_right (Dvd.intro _ rfl)).mp h4
  have := Nat.le_of_dvd one_pos h1
  omega

theorem not_both (hμ : 2 ≤ μ) {δ : ℕ} (h0 : μ ∣ δ ^ 2) : ¬ μ ∣ (δ + 1) ^ 2 := by
  intro h1
  obtain ⟨p, hp, hpμ⟩ := Nat.exists_prime_and_dvd (show μ ≠ 1 by omega)
  have a := hp.dvd_of_dvd_pow (hpμ.trans h0)
  have b := hp.dvd_of_dvd_pow (hpμ.trans h1)
  have := (Nat.dvd_add_right a).mp b
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem local_values_neither (hμ : 2 ≤ μ) {δ : ℕ}
    (h0 : ¬ μ ∣ δ ^ 2) (h1 : ¬ μ ∣ (δ + 1) ^ 2) : dU μ δ = dL μ δ := by
  have u0 := U_eq (by omega : 0 < μ) δ
  have u1 := U_eq (by omega : 0 < μ) (δ + 1)
  have hm := L_mono (μ := μ) δ
  simp only [h0, ↓reduceIte] at u0
  simp only [h1, ↓reduceIte] at u1
  rw [dU, dL, u0, u1]
  omega

theorem local_values_zero (hμ : 2 ≤ μ) {δ : ℕ} (hδ : δ < μ) (h0 : μ ∣ δ ^ 2) :
    dL μ δ = (if 2 * δ + 1 < μ then 0 else 1) ∧ dU μ δ = dL μ δ + 1 := by
  have h1 := not_both hμ h0
  have hne : 2 * δ + 1 ≠ μ := fun h => not_dvd_sq_of_mid hμ h h0
  have u0 := U_eq (by omega : 0 < μ) δ
  have u1 := U_eq (by omega : 0 < μ) (δ + 1)
  have hm := L_mono (μ := μ) δ
  simp only [h0, ↓reduceIte] at u0
  simp only [h1, ↓reduceIte] at u1
  obtain ⟨k, hk⟩ := h0
  have hL0 : L μ δ = k := by rw [L, hk, Nat.mul_div_cancel_left _ (by omega)]
  have hsq : (δ + 1) ^ 2 = (2 * δ + 1) + μ * k := by rw [← hk]; ring
  have hL1 : L μ (δ + 1) = (2 * δ + 1) / μ + k := by
    rw [L, hsq, Nat.add_mul_div_left _ _ (by omega)]
  refine ⟨?_, ?_⟩
  · rw [dL, hL1, hL0]
    split_ifs with hlt
    · rw [Nat.div_eq_of_lt hlt]; simp
    · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]; omega
  · rw [dU, dL, u0, u1]; omega

theorem local_values_one (hμ : 2 ≤ μ) {δ : ℕ} (hδ : δ < μ) (h1 : μ ∣ (δ + 1) ^ 2) :
    dU μ δ = (if 2 * δ + 1 < μ then 0 else 1) ∧ dL μ δ = dU μ δ + 1 := by
  have h0 : ¬ μ ∣ δ ^ 2 := fun h => not_both hμ h h1
  have hne : 2 * δ + 1 ≠ μ := fun h => not_dvd_succ_sq_of_mid hμ h h1
  have u0 := U_eq (by omega : 0 < μ) δ
  have u1 := U_eq (by omega : 0 < μ) (δ + 1)
  have hm := L_mono (μ := μ) δ
  simp only [h0, ↓reduceIte] at u0
  simp only [h1, ↓reduceIte] at u1
  obtain ⟨k, hk⟩ := h1
  have hL1 : L μ (δ + 1) = k := by rw [L, hk, Nat.mul_div_cancel_left _ (by omega)]
  have hsq : δ ^ 2 + (2 * δ + 1) = μ * k := by rw [← hk]; ring
  -- write c = 1 or 2 for the number of multiples of μ "lost"
  have hL0 : L μ δ + (if 2 * δ + 1 < μ then 1 else 2) = k := by
    rw [L]
    split_ifs with hlt
    · have hk1 : 1 ≤ k := by
        rcases k with _ | k
        · simp at hsq
        · omega
      have : δ ^ 2 / μ = k - 1 := by
        apply Nat.div_eq_of_lt_le
        · have : (k - 1) * μ + μ = k * μ := by
            rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hk1]
          nlinarith
        · have : (k - 1 + 1) * μ = k * μ := by rw [Nat.sub_add_cancel hk1]
          nlinarith
      omega
    · have hk2 : 2 ≤ k := by
        by_contra hk2
        have : k ≤ 1 := by omega
        interval_cases k <;> nlinarith
      have hgt : μ + 1 ≤ 2 * δ + 1 := by omega
      have : δ ^ 2 / μ = k - 2 := by
        apply Nat.div_eq_of_lt_le
        · have : (k - 2) * μ + 2 * μ = k * μ := by
            rw [← add_mul, Nat.sub_add_cancel hk2]
          nlinarith
        · have : (k - 2 + 1) * μ + μ = k * μ := by
            rw [← Nat.succ_mul, Nat.succ_eq_add_one]
            congr 1; omega
          nlinarith
      omega
  refine ⟨?_, ?_⟩
  · rw [dU, u0, u1, hL1]
    split_ifs at hL0 ⊢ <;> omega
  · rw [dU, dL, u0, u1, hL1]
    split_ifs at hL0 ⊢ <;> omega


/-! ### The counting step: a reflection argument -/

/-- `μ ∣ (μ - δ)² ↔ μ ∣ δ²` for `δ ≤ μ`. -/
theorem dvd_sq_reflect {δ : ℕ} (hδ : δ ≤ μ) : μ ∣ (μ - δ) ^ 2 ↔ μ ∣ δ ^ 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, μ = δ + e := ⟨μ - δ, by omega⟩
  have key : (δ + e) * (2 * δ) + (δ + e - δ) ^ 2 = (δ + e) * (δ + e) + δ ^ 2 := by
    rw [show δ + e - δ = e by omega]; ring
  rw [← Nat.dvd_add_right (Dvd.intro _ rfl), key, Nat.dvd_add_right (Dvd.intro _ rfl)]

/-- Indicator of a proposition, as an integer. -/
def ind (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

/-- `F δ = [μ ∣ δ²] · ([2δ+1 < μ] - [2δ+1 > μ])`. -/
def F (μ δ : ℕ) : ℤ := ind (μ ∣ δ ^ 2) * (ind (2 * δ + 1 < μ) - ind (μ < 2 * δ + 1))

theorem F_pair (hμ : 2 ≤ μ) {δ : ℕ} (h2 : δ < μ) :
    F μ δ + F μ (μ - δ) = -2 * ind (2 * δ = μ ∧ μ ∣ δ ^ 2) := by
  have hr := dvd_sq_reflect (μ := μ) (δ := δ) h2.le
  unfold F ind
  by_cases hd : μ ∣ δ ^ 2
  · have hm1 : 2 * δ + 1 ≠ μ := fun h => not_dvd_sq_of_mid hμ h hd
    have hm2 : 2 * (μ - δ) + 1 ≠ μ := fun h => not_dvd_sq_of_mid hμ h (hr.mpr hd)
    simp only [hd, hr.mpr hd, and_true, ↓reduceIte]
    split_ifs <;> omega
  · have hd' : ¬ μ ∣ (μ - δ) ^ 2 := fun h => hd (hr.mp h)
    simp only [hd, hd', and_false, ↓reduceIte]
    ring

theorem sum_mid (hμ : 2 ≤ μ) :
    ∑ j ∈ range (μ - 1), ind (2 * (j + 1) = μ ∧ μ ∣ (j + 1) ^ 2) = ind (4 ∣ μ) := by
  rcases Nat.even_or_odd μ with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk1 : 1 ≤ k := by omega
    rw [Finset.sum_eq_single (k - 1)]
    · unfold ind
      have e1 : 2 * (k - 1 + 1) = μ := by omega
      have e2 : μ ∣ (k - 1 + 1) ^ 2 ↔ 4 ∣ μ := by
        rw [show k - 1 + 1 = k by omega, hk, ← two_mul, sq,
          show (4 : ℕ) = 2 * 2 by rfl, Nat.mul_dvd_mul_iff_right (by omega : 0 < k),
          Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)]
      simp only [e1, e2, true_and]
    · intro j _ hj
      simp only [ind, ite_eq_right_iff]
      rintro ⟨h, -⟩; omega
    · intro h; simp at h; omega
  · have h4 : ¬ 4 ∣ μ := by rintro ⟨c, hc⟩; omega
    rw [show ind (4 ∣ μ) = 0 by simp [ind, h4]]
    apply Finset.sum_eq_zero
    intro j _
    simp only [ind, ite_eq_right_iff]
    rintro ⟨h, -⟩; omega

/-- **Counting step.** `∑_{δ<μ} [μ ∣ δ²]([2δ+1<μ] - [2δ+1>μ]) = 1 - [4 ∣ μ]`. -/
theorem signed_count (hμ : 2 ≤ μ) :
    ∑ δ ∈ range μ, F μ δ = 1 - ind (4 ∣ μ) := by
  obtain ⟨m, rfl⟩ : ∃ m, μ = m + 1 := ⟨μ - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hF0 : F (m + 1) 0 = 1 := by
    unfold F ind; simp; omega
  have hrefl : ∑ j ∈ range m, F (m + 1) (j + 1) =
      ∑ j ∈ range m, F (m + 1) (m + 1 - (j + 1)) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    congr 1; omega
  have hsum : ∑ j ∈ range m, (F (m + 1) (j + 1) + F (m + 1) (m + 1 - (j + 1))) =
      ∑ j ∈ range m, -2 * ind (2 * (j + 1) = m + 1 ∧ (m + 1) ∣ (j + 1) ^ 2) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    exact F_pair hμ (by omega)
  rw [Finset.sum_add_distrib, ← hrefl, ← Finset.mul_sum] at hsum
  have hmid := sum_mid hμ
  simp only [Nat.add_sub_cancel] at hmid
  rw [hmid] at hsum
  rw [hF0]
  linarith


theorem sum_z1_lo :
    ∑ δ ∈ range μ, ind (μ ∣ (δ + 1) ^ 2) * ind (2 * δ + 1 < μ) =
      ∑ δ ∈ range μ, ind (μ ∣ δ ^ 2) * ind (μ < 2 * δ + 1) := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro δ hδ
  simp only [Finset.mem_range] at hδ
  simp only [ind, show μ - 1 - δ + 1 = μ - δ by omega, dvd_sq_reflect hδ.le,
    show 2 * (μ - 1 - δ) + 1 < μ ↔ μ < 2 * δ + 1 by omega]

theorem sum_z1_hi :
    ∑ δ ∈ range μ, ind (μ ∣ (δ + 1) ^ 2) * ind (μ < 2 * δ + 1) =
      ∑ δ ∈ range μ, ind (μ ∣ δ ^ 2) * ind (2 * δ + 1 < μ) := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro δ hδ
  simp only [Finset.mem_range] at hδ
  simp only [ind, show μ - 1 - δ + 1 = μ - δ by omega, dvd_sq_reflect hδ.le,
    show μ < 2 * (μ - 1 - δ) + 1 ↔ 2 * δ + 1 < μ by omega]

/-! ### Signed counts of values -/

/-- `[a = v]` as an integer. -/
def eqv (a v : ℕ) : ℤ := if v = a then 1 else 0

/-- `e μ = [4 ∤ μ]`. -/
def e (μ : ℕ) : ℕ := if 4 ∣ μ then 0 else 1

theorem e_eq (μ : ℕ) : ((e μ : ℕ) : ℤ) = 1 - ind (4 ∣ μ) := by
  unfold e ind; split_ifs <;> simp

theorem local_signed (hμ : 2 ≤ μ) {δ : ℕ} (hδ : δ < μ) (v : ℕ) :
    eqv (dU μ δ) v - eqv (dL μ δ) v =
      (ind (μ ∣ δ ^ 2) - ind (μ ∣ (δ + 1) ^ 2)) *
        (ind (2 * δ + 1 < μ) * (eqv 1 v - eqv 0 v)
          + ind (μ < 2 * δ + 1) * (eqv 2 v - eqv 1 v)) := by
  by_cases h0 : μ ∣ δ ^ 2
  · have h1 := not_both hμ h0
    have hne : 2 * δ + 1 ≠ μ := fun h => not_dvd_sq_of_mid hμ h h0
    obtain ⟨a, b⟩ := local_values_zero hμ hδ h0
    rw [b, a]
    simp only [ind, eqv, h0, h1, ↓reduceIte]
    split_ifs <;> omega
  · by_cases h1 : μ ∣ (δ + 1) ^ 2
    · have hne : 2 * δ + 1 ≠ μ := fun h => not_dvd_succ_sq_of_mid hμ h h1
      obtain ⟨a, b⟩ := local_values_one hμ hδ h1
      rw [b, a]
      simp only [ind, eqv, h0, h1, ↓reduceIte]
      split_ifs <;> omega
    · rw [local_values_neither hμ h0 h1]
      simp [ind, h0, h1]

/-- Signed count of each value `v` among the local values `δ = 0, …, μ-1`. -/
theorem local_count (hμ : 2 ≤ μ) (v : ℕ) :
    ∑ δ ∈ range μ, (eqv (dU μ δ) v - eqv (dL μ δ) v) =
      (e μ : ℤ) * (2 * eqv 1 v - eqv 0 v - eqv 2 v) := by
  rw [Finset.sum_congr rfl (fun δ hδ => local_signed hμ (Finset.mem_range.mp hδ) v)]
  have hS := signed_count hμ
  unfold F at hS
  rw [e_eq, ← hS]
  have expand : ∀ δ, (ind (μ ∣ δ ^ 2) - ind (μ ∣ (δ + 1) ^ 2)) *
        (ind (2 * δ + 1 < μ) * (eqv 1 v - eqv 0 v)
          + ind (μ < 2 * δ + 1) * (eqv 2 v - eqv 1 v)) =
      ind (μ ∣ δ ^ 2) * ind (2 * δ + 1 < μ) * (eqv 1 v - eqv 0 v)
      - ind (μ ∣ (δ + 1) ^ 2) * ind (2 * δ + 1 < μ) * (eqv 1 v - eqv 0 v)
      + ind (μ ∣ δ ^ 2) * ind (μ < 2 * δ + 1) * (eqv 2 v - eqv 1 v)
      - ind (μ ∣ (δ + 1) ^ 2) * ind (μ < 2 * δ + 1) * (eqv 2 v - eqv 1 v) := by
    intro δ; ring
  have rhs : ∀ δ, ind (μ ∣ δ ^ 2) * (ind (2 * δ + 1 < μ) - ind (μ < 2 * δ + 1)) =
      ind (μ ∣ δ ^ 2) * ind (2 * δ + 1 < μ) - ind (μ ∣ δ ^ 2) * ind (μ < 2 * δ + 1) := by
    intro δ; ring
  simp only [expand, rhs, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_z1_lo, sum_z1_hi]
  ring

/-! ### Multisets of values -/

theorem vals_eq_map (f : ℕ → ℕ) (I : Finset ℕ) : vals f I = I.val.map f := by
  unfold vals
  rw [Finset.sum_eq_multiset_sum,
    show (fun n => ({f n} : Multiset ℕ)) = (fun x => ({x} : Multiset ℕ)) ∘ f from rfl,
    ← Multiset.map_map, Multiset.sum_map_singleton]

theorem count_vals (f : ℕ → ℕ) (I : Finset ℕ) (v : ℕ) :
    ((vals f I).count v : ℤ) = ∑ n ∈ I, eqv (f n) v := by
  unfold vals eqv
  rw [Multiset.count_sum']
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  rw [Multiset.count_singleton]
  split_ifs <;> simp

/-- Local multiset identity: `𝒰 + e•{0,2} = ℒ + e•{1,1}` over `δ = 0, …, μ-1`. -/
theorem local_multiset (hμ : 2 ≤ μ) :
    vals (dU μ) (range μ) + e μ • ({0, 2} : Multiset ℕ) =
      vals (dL μ) (range μ) + e μ • ({1, 1} : Multiset ℕ) := by
  ext v
  have h := local_count hμ v
  rw [Finset.sum_sub_distrib, ← count_vals, ← count_vals] at h
  simp only [Multiset.count_add, Multiset.count_nsmul]
  have c02 : (((({0, 2} : Multiset ℕ).count v : ℕ)) : ℤ) = eqv 0 v + eqv 2 v := by
    simp only [eqv, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    split_ifs <;> simp_all
  have c11 : (((({1, 1} : Multiset ℕ).count v : ℕ)) : ℤ) = 2 * eqv 1 v := by
    simp only [eqv, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    split_ifs <;> simp_all
  have : ((Multiset.count v (vals (dU μ) (range μ)) + e μ * Multiset.count v {0, 2} : ℕ) : ℤ) =
      ((Multiset.count v (vals (dL μ) (range μ)) + e μ * Multiset.count v {1, 1} : ℕ) : ℤ) := by
    push_cast
    rw [c02, c11]
    linarith
  exact_mod_cast this

/-- The block `n = μγ, …, μγ+μ-1`. -/
def block (μ γ : ℕ) : Finset ℕ := Ico (μ * γ) (μ * γ + μ)

theorem vals_block (f g : ℕ → ℕ) (hf : ∀ γ δ, f (μ * γ + δ) = 2 * γ + g δ) (γ : ℕ) :
    vals f (block μ γ) = (vals g (range μ)).map (fun x => 2 * γ + x) := by
  rw [vals_eq_map, vals_eq_map, block, Multiset.map_map]
  have : (Ico (μ * γ) (μ * γ + μ)).val = (range μ).val.map (fun δ => μ * γ + δ) := by
    have h : Ico (μ * γ) (μ * γ + μ) = (range μ).map (addLeftEmbedding (μ * γ)) := by
      rw [Finset.range_eq_Ico, Finset.map_add_left_Ico, add_zero]
    rw [h, Finset.map_val]
    rfl
  rw [this, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro δ _
  simp [hf]

/-- **Block identity.** On block `γ`: `𝒰_γ + e•{2γ, 2γ+2} = ℒ_γ + e•{2γ+1, 2γ+1}`. -/
theorem block_multiset (hμ : 2 ≤ μ) (γ : ℕ) :
    vals (dU μ) (block μ γ) + e μ • ({2 * γ, 2 * γ + 2} : Multiset ℕ) =
      vals (dL μ) (block μ γ) + e μ • ({2 * γ + 1, 2 * γ + 1} : Multiset ℕ) := by
  rw [vals_block _ _ (dU_block (by omega)) γ, vals_block _ _ (dL_block (by omega)) γ]
  have h := congrArg (Multiset.map (fun x => 2 * γ + x)) (local_multiset hμ)
  simpa [Multiset.map_add, Multiset.map_nsmul] using h


/-! ### Proposition E: structural reduction -/

/-- `{3,3,5,5,…,2G+1,2G+1}`. -/
def oddsDoubled (G : ℕ) : Multiset ℕ := ∑ γ ∈ Ico 1 (G + 1), {2 * γ + 1, 2 * γ + 1}

/-- `{2,4,4,6,6,…,2G,2G,2G+2}`. -/
def evensEnds (G : ℕ) : Multiset ℕ := ∑ γ ∈ Ico 1 (G + 1), {2 * γ, 2 * γ + 2}

theorem vals_blocks (f : ℕ → ℕ) (G : ℕ) :
    vals f (Ico μ (μ * (G + 1))) = ∑ γ ∈ Ico 1 (G + 1), vals f (block μ γ) := by
  induction G with
  | zero => simp [vals]
  | succ G ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ← ih, block, vals, vals, vals,
      show μ * (G + 1 + 1) = μ * (G + 1) + μ by ring,
      Finset.sum_Ico_consecutive _ (by nlinarith) (by omega)]

theorem summed_identity (hμ : 2 ≤ μ) (G : ℕ) :
    vals (dU μ) (Ico μ (μ * (G + 1))) + e μ • evensEnds G =
      vals (dL μ) (Ico μ (μ * (G + 1))) + e μ • oddsDoubled G := by
  rw [vals_blocks, vals_blocks, evensEnds, oddsDoubled, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun γ _ => block_multiset hμ γ)

theorem even_of_mem_evensEnds {G v : ℕ} (h : v ∈ evensEnds G) : Even v := by
  unfold evensEnds at h
  rw [Multiset.mem_sum] at h
  obtain ⟨γ, _, hγ⟩ := h
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hγ
  rcases hγ with rfl | rfl
  · exact ⟨γ, by ring⟩
  · exact ⟨γ + 1, by ring⟩

theorem odd_of_mem_oddsDoubled {G v : ℕ} (h : v ∈ oddsDoubled G) : Odd v := by
  unfold oddsDoubled at h
  rw [Multiset.mem_sum] at h
  obtain ⟨γ, _, hγ⟩ := h
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
    or_self] at hγ
  exact hγ ▸ ⟨γ, rfl⟩

/-- **Proposition E (structural reduction).** Let `μ ≥ 2` and let `𝒰`, `ℒ` be the
multisets of values of `dU`, `dL` over `n = μ, …, μ(G+1)-1`. After removing the
common part (multiset difference):
* if `4 ∣ μ`, nothing remains: `𝒰 = ℒ`;
* if `4 ∤ μ`, `𝒰 - ℒ = {3,3,5,5,…,2G+1,2G+1}` and `ℒ - 𝒰 = {2,4,4,…,2G,2G,2G+2}`,
  whatever the value of `μ` (the multisets of the case `μ = 2`). -/
theorem structural_reduction (hμ : 2 ≤ μ) (G : ℕ) :
    (4 ∣ μ → vals (dU μ) (Ico μ (μ * (G + 1))) = vals (dL μ) (Ico μ (μ * (G + 1)))) ∧
    (¬ 4 ∣ μ →
      vals (dU μ) (Ico μ (μ * (G + 1))) - vals (dL μ) (Ico μ (μ * (G + 1))) = oddsDoubled G ∧
      vals (dL μ) (Ico μ (μ * (G + 1))) - vals (dU μ) (Ico μ (μ * (G + 1))) = evensEnds G) := by
  have h := summed_identity hμ G
  set 𝒰 := vals (dU μ) (Ico μ (μ * (G + 1)))
  set ℒ := vals (dL μ) (Ico μ (μ * (G + 1)))
  refine ⟨fun h4 => ?_, fun h4 => ?_⟩
  · simpa [e, h4] using h
  · simp only [e, h4, ↓reduceIte, one_smul] at h
    have disj : ∀ v, (evensEnds G).count v = 0 ∨ (oddsDoubled G).count v = 0 := by
      intro v
      rcases Nat.even_or_odd v with hv | hv
      · right; rw [Multiset.count_eq_zero]
        exact fun hm => (Nat.not_even_iff_odd.mpr (odd_of_mem_oddsDoubled hm)) hv
      · left; rw [Multiset.count_eq_zero]
        exact fun hm => (Nat.not_even_iff_odd.mpr hv) (even_of_mem_evensEnds hm)
    have hc : ∀ v, 𝒰.count v + (evensEnds G).count v =
        ℒ.count v + (oddsDoubled G).count v := fun v => by
      simpa using congrArg (Multiset.count v) h
    constructor
    · ext v
      rw [Multiset.count_sub]
      have := hc v; rcases disj v with h0 | h0 <;> omega
    · ext v
      rw [Multiset.count_sub]
      have := hc v; rcases disj v with h0 | h0 <;> omega

/-! ### Proposition C: the block product -/

theorem dU_pos_block (hμ : 2 ≤ μ) {γ : ℕ} (hγ : 1 ≤ γ) {n : ℕ} (hn : n ∈ block μ γ) :
    0 < dU μ n := by
  simp only [block, Finset.mem_Ico] at hn
  obtain ⟨δ, rfl⟩ : ∃ δ, n = μ * γ + δ := ⟨n - μ * γ, by omega⟩
  rw [dU_block (by omega)]
  omega

/-- **Proposition C.** For `γ ≥ 1`, the product of `dL n / dU n` over the block
`n = μγ, …, μγ+μ-1` is `1` if `4 ∣ μ` and `4γ(γ+1)/(2γ+1)²` if `4 ∤ μ`. -/
theorem block_product (hμ : 2 ≤ μ) {γ : ℕ} (hγ : 1 ≤ γ) :
    ∏ n ∈ block μ γ, ((dL μ n : ℚ) / dU μ n) =
      if 4 ∣ μ then 1 else 4 * (γ : ℚ) * (γ + 1) / (2 * γ + 1) ^ 2 := by
  have h := congrArg (fun s : Multiset ℕ => (s.map (fun n : ℕ => (n : ℚ))).prod)
    (block_multiset hμ γ)
  simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_nsmul, Multiset.prod_nsmul,
    vals_eq_map, Multiset.map_map, Function.comp_def] at h
  rw [Finset.prod_div_distrib]
  have hU : (∏ n ∈ block μ γ, (dU μ n : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun n hn => by exact_mod_cast (dU_pos_block hμ hγ hn).ne'
  rw [Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
  rw [Finset.prod_eq_multiset_prod] at hU
  have hγ' : (0 : ℚ) < γ := by exact_mod_cast hγ
  split_ifs with h4
  · simp only [e, h4, ↓reduceIte, pow_zero, mul_one] at h
    rw [← h, div_self hU]
  · simp only [e, h4, ↓reduceIte, pow_one] at h
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton] at h
    rw [div_eq_div_iff hU (by positivity)]
    push_cast at h ⊢
    linear_combination -h

end FloorCeilWallis
