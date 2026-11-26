import Mathlib.Algebra.Order.BigOperators.Expect
import SketchOrientation.Dct

/-!
# Row energies of the first signed cosine pass

The uniform finite average over all Boolean sign configurations implements
independent fair signs. The manuscript bound is at `spectrum.tex:42–49`
and `cosine.tex:121–126` in commit `68dd06e`.
-/

open scoped BigOperators
open Finset

namespace SketchOrientation.Cosine

private noncomputable def sign (b : Bool) : ℝ := if b then 1 else -1

private noncomputable def signSum {n : ℕ} (x : Fin n → ℝ) (ε : Fin n → Bool) : ℝ :=
  ∑ i, sign (ε i) * x i

private theorem expect_signCons {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (𝔼 ε, f ε) = 𝔼 e : Fin n → Bool, (f (Fin.cons false e) + f (Fin.cons true e)) / 2 := by
  let g : Bool × (Fin n → Bool) → ℝ := fun (b, e) ↦ f (Fin.cons b e)
  calc
    _ = 𝔼 z, g z := (Fintype.expect_equiv (Fin.consEquiv (fun _ ↦ Bool)) g f (by
        rintro ⟨b, e⟩
        rfl)).symm
    _ = 𝔼 b : Bool, 𝔼 e : Fin n → Bool, f (Fin.cons b e) := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = _ := by
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro e _
      rw [Fintype.expect_eq_sum_div_card]
      simp [add_comm]

private theorem scalar_signMoments {n : ℕ} (x : Fin n → ℝ) :
    (𝔼 ε, signSum x ε ^ 2) = ∑ i, x i ^ 2 ∧
    (𝔼 ε, signSum x ε ^ 4) ≤ 3 * (∑ i, x i ^ 2) ^ 2 := by
  induction n with
  | zero => simp [signSum]
  | succ n ih =>
    let y : Fin n → ℝ := fun i ↦ x i.succ
    have h₂ (e : Fin n → Bool) :
        (signSum x (Fin.cons false e) ^ 2 + signSum x (Fin.cons true e) ^ 2) / 2 =
        x 0 ^ 2 + signSum y e ^ 2 := by
      simp only [signSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sign, Bool.false_eq_true,
        if_false, if_true, y]
      ring
    have h₄ (e : Fin n → Bool) :
        (signSum x (Fin.cons false e) ^ 4 + signSum x (Fin.cons true e) ^ 4) / 2 =
        x 0 ^ 4 + 6 * x 0 ^ 2 * signSum y e ^ 2 + signSum y e ^ 4 := by
      simp only [signSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sign, Bool.false_eq_true,
        if_false, if_true, y]
      ring
    obtain ⟨hy₂, hy₄⟩ := ih y
    constructor
    · rw [expect_signCons, Fin.sum_univ_succ]
      simp_rw [h₂, Finset.expect_add_distrib, Fintype.expect_const, hy₂]
      rfl
    · rw [expect_signCons, Fin.sum_univ_succ]
      simp_rw [h₄, Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect, hy₂]
      change _ ≤ 3 * (x 0 ^ 2 + ∑ i, y i ^ 2) ^ 2
      nlinarith [sq_nonneg (x 0 ^ 2)]

/-- Fourth moment of a signed vector sum, as used at `spectrum.tex:42–49`. -/
theorem signedVector_fourthMoment {n k : ℕ} (x : Matrix (Fin n) (Fin k) ℝ) :
    (𝔼 ε : Fin n → Bool, (∑ j, (∑ i, sign (ε i) * x i j) ^ 2) ^ 2) ≤
      3 * (∑ i, ∑ j, (x i j) ^ 2) ^ 2 := by
  let f (j : Fin k) (ε : Fin n → Bool) := signSum (fun i ↦ x i j) ε
  let s (j : Fin k) : ℝ := ∑ i, (x i j) ^ 2
  have hs (j : Fin k) : 0 ≤ s j := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have h (j l : Fin k) :
      (𝔼 ε, f j ε ^ 2 * f l ε ^ 2) ≤ 3 * s j * s l := by
    have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
      (fun ε ↦ f j ε ^ 2) (fun ε ↦ f l ε ^ 2)
    simp only [← pow_mul] at hcs
    have hm (a : Fin k) : (𝔼 ε, f a ε ^ 4) ≤ 3 * s a ^ 2 :=
      (scalar_signMoments (fun i ↦ x i a)).2
    have hprod :
        (𝔼 ε, f j ε ^ 4) * (𝔼 ε, f l ε ^ 4) ≤ (3 * s j * s l) ^ 2 := by
      calc
        _ ≤ (3 * s j ^ 2) * (3 * s l ^ 2) :=
          mul_le_mul (hm j) (hm l) (Finset.expect_nonneg fun _ _ ↦ by positivity) (by positivity)
        _ = _ := by ring
    exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (by exact mul_nonneg (mul_nonneg (by norm_num) (hs j)) (hs l)) (hcs.trans hprod)
  change (𝔼 ε, (∑ j, f j ε ^ 2) ^ 2) ≤ _
  rw [Finset.sum_comm (f := fun (i : Fin n) (j : Fin k) ↦ (x i j) ^ 2)]
  change _ ≤ 3 * (∑ j, s j) ^ 2
  simp_rw [pow_two (∑ j, f j _ ^ 2), Finset.sum_mul, Finset.mul_sum,
    Finset.expect_sum_comm]
  calc
    _ ≤ ∑ j, ∑ l, 3 * s j * s l :=
      Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun l _ ↦ h j l
    _ = _ := by
      simp_rw [mul_assoc (3 : ℝ), ← Finset.mul_sum]
      rw [← Finset.sum_mul, ← pow_two]

open Matrix in
/-- Frequency rows of the real DCT-II, in the orientation of `spectrum.tex:5–10`. -/
noncomputable def dctII (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (SketchOrientation.cosineCore n)ᵀ

open Matrix in
/-- The transform has orthonormal columns. -/
theorem dctII_transpose_mul (n : ℕ) : (dctII n)ᵀ * dctII n = 1 := by
  simpa [dctII] using SketchOrientation.cosineCore_mul_transpose n

/-- Uniform coefficient bound squared, including the constant row. -/
theorem dctII_apply_sq_le {n : ℕ} (r i : Fin n) : dctII n r i ^ 2 ≤ 2 / (n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast r.pos
  let c : ℝ := if r.val = 0 then 1 else Real.sqrt 2
  have hc : c ^ 2 ≤ 2 := by
    dsimp [c]
    split
    · norm_num
    · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [dctII, Matrix.transpose_apply, SketchOrientation.cosineCore]
  change ((c / Real.sqrt (n : ℝ)) * Real.cos _) ^ 2 ≤ _
  rw [mul_pow, div_pow, Real.sq_sqrt hn.le]
  apply (mul_le_of_le_one_right (div_nonneg (sq_nonneg _) hn.le) (Real.cos_sq_le_one _)).trans
  exact div_le_div_of_nonneg_right hc hn.le

/-- The squared row norm of a frame, `introduction.tex:99`. -/
noncomputable def leverage {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ) (i : Fin n) : ℝ :=
  ∑ j, (V i j) ^ 2

/-- The sum of squared leverage scores, `cosine.tex:29–33`. -/
noncomputable def rowEnergy {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ∑ i, (leverage V i) ^ 2

open Matrix in
theorem leverage_sum {n k : ℕ} {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    ∑ i, leverage V i = (k : ℝ) := by
  have hcolumn (j : Fin k) : ∑ i, (V i j) ^ 2 = 1 := by
    have hj := congrArg (fun W : Matrix (Fin k) (Fin k) ℝ ↦ W j j) hV
    simpa only [Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply_eq, pow_two] using hj
  simp only [leverage]
  rw [Finset.sum_comm]
  simp [hcolumn]

open Matrix in
/-- The leverage lower bound used at `cosine.tex:293–296`. -/
theorem rowEnergy_lower {n k : ℕ} (hn : 0 < n) {V : Matrix (Fin n) (Fin k) ℝ}
    (hV : Vᵀ * V = 1) : (k : ℝ) ^ 2 / n ≤ rowEnergy V := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ (fun _ : Fin n ↦ 1) (leverage V)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, leverage_sum hV] at hc
  exact (div_le_iff₀ hn').mpr (by simpa [rowEnergy, mul_comm] using hc)

open Matrix in
/-- Actual first signed pass `F D₂ V`. A Boolean configuration encodes its signs. -/
noncomputable def signedDCT {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (ε : Fin n → Bool) : Matrix (Fin n) (Fin k) ℝ :=
  dctII n * (diagonal (fun i ↦ sign (ε i)) * V)

open Matrix in
theorem signedDCT_transpose_mul {n k : ℕ} {V : Matrix (Fin n) (Fin k) ℝ}
    (hV : Vᵀ * V = 1) (ε : Fin n → Bool) : (signedDCT V ε)ᵀ * signedDCT V ε = 1 := by
  have hd : diagonal (fun i ↦ sign (ε i)) * diagonal (fun i ↦ sign (ε i)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one using 2
    funext i
    cases ε i <;> simp [sign]
  unfold signedDCT
  simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dctII n)ᵀ, dctII_transpose_mul]
  simp only [Matrix.one_mul]
  rw [← Matrix.mul_assoc (diagonal (fun i ↦ sign (ε i))), hd]
  simpa only [Matrix.one_mul] using hV

open Matrix in
/-- Exact first-pass spread bound for a deterministic orthonormal frame.
The proof discharges orthogonality and coefficient bounds for the real DCT-II. -/
theorem dctII_signedSpread {n k : ℕ}
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    (𝔼 ε : Fin n → Bool, rowEnergy (signedDCT V ε)) ≤ 6 * (k : ℝ) ^ 2 / n := by
  let b (r : Fin n) : ℝ := ∑ i, (dctII n r i) ^ 2 * leverage V i
  have hlev (i : Fin n) : 0 ≤ leverage V i := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hb (r : Fin n) : 0 ≤ b r := Finset.sum_nonneg fun i _ ↦ mul_nonneg (sq_nonneg _) (hlev i)
  have hcol (i : Fin n) : ∑ r, (dctII n r i) ^ 2 = 1 := by
    have hc := congrArg (fun W : Matrix (Fin n) (Fin n) ℝ ↦ W i i) (dctII_transpose_mul n)
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, pow_two] using hc
  have hsum : ∑ r, b r = (k : ℝ) := by
    dsimp only [b]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol, one_mul]
    exact leverage_sum hV
  have hmax (r : Fin n) : b r ≤ 2 * (k : ℝ) / n := by
    calc
      _ ≤ ∑ i : Fin n, (2 / (n : ℝ)) * leverage V i :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (dctII_apply_sq_le r i) (hlev i)
      _ = _ := by rw [← Finset.mul_sum, leverage_sum hV]; ring
  have hfourth (r : Fin n) :
      (𝔼 ε : Fin n → Bool, (leverage (signedDCT V ε) r) ^ 2) ≤ 3 * b r ^ 2 := by
    have hentry (ε : Fin n → Bool) (j : Fin k) :
        signedDCT V ε r j = ∑ i, sign (ε i) * (dctII n r i * V i j) := by
      unfold signedDCT
      rw [Matrix.mul_apply]
      simp_rw [Matrix.diagonal_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hb' : (∑ i : Fin n, ∑ j : Fin k, (dctII n r i * V i j)^2) = b r := by
      simp_rw [mul_pow, ← Finset.mul_sum]
      rfl
    simp only [leverage, hentry, ← hb']
    exact signedVector_fourthMoment (fun i j ↦ dctII n r i * V i j)
  unfold rowEnergy
  rw [Finset.expect_sum_comm]
  calc
    _ ≤ ∑ r, 3 * b r ^ 2 := Finset.sum_le_sum fun r _ ↦ hfourth r
    _ ≤ ∑ r, (3 * (2 * (k : ℝ) / n)) * b r := by
      apply Finset.sum_le_sum
      intro r _
      nlinarith [mul_nonneg (hb r) (sub_nonneg.mpr (hmax r))]
    _ = _ := by rw [← Finset.mul_sum, hsum]; ring

open Matrix in
/-- Each first-pass output is an orthonormal frame, so the lower bound
holds after averaging too. The expectation is the same as in the spread bound. -/
theorem dctII_signedSpread_lower {n k : ℕ} (hn : 0 < n)
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    (k : ℝ) ^ 2 / n ≤ 𝔼 ε : Fin n → Bool, rowEnergy (signedDCT V ε) := by
  rw [← Fintype.expect_const (ι := Fin n → Bool) ((k : ℝ)^2 / n)]
  exact Finset.expect_le_expect fun ε _ ↦ rowEnergy_lower hn (signedDCT_transpose_mul hV ε)

/-- Bound on every sampled coefficient vector, `cosine.tex:68–73`.
The selector models distinct rows through a finite embedding. -/
theorem dctII_sampledCoefficient_normSq {n ℓ : ℕ} (J : Fin ℓ ↪ Fin n) (i : Fin n) :
    ∑ r, (Real.sqrt n * dctII n (J r) i) ^ 2 ≤ 2 * (ℓ : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  calc
    _ ≤ ∑ _r : Fin ℓ, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      rw [mul_pow, Real.sq_sqrt hn.le]
      have h := mul_le_mul_of_nonneg_left (dctII_apply_sq_le (J r) i) hn.le
      convert h using 1
      field_simp
    _ = _ := by simp [mul_comm]

end SketchOrientation.Cosine
