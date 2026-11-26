import SketchOrientation.GaussianChaosSchur
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace SketchOrientation

open Matrix
open scoped Matrix

/-- The entire scalar series with coefficients `1/(q+1)!`. -/
noncomputable def expm1Div (x : ℝ) : ℝ := if x = 0 then 1 else (Real.exp x - 1) / x

private theorem hasSum_exp_sub_one (x : ℝ) :
    HasSum (fun q : ℕ => x ^ (q + 1) / ((q + 1).factorial : ℝ)) (Real.exp x - 1) := by
  have h := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Real.exp_eq_exp_ℝ] at h
  simpa using (hasSum_nat_add_iff' 1).mpr h

private theorem hasSum_expm1Div (x : ℝ) :
    HasSum (fun q : ℕ => x ^ q / ((q + 1).factorial : ℝ)) (expm1Div x) := by
  by_cases hx : x = 0
  · subst x
    have hs : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) ^ n / ((n + 1).factorial : ℝ) = 0 := by
      intro n hn
      simp [zero_pow hn]
    simpa [expm1Div] using hasSum_single 0 hs
  · unfold expm1Div
    rw [if_neg hx]
    have he : (fun q : ℕ => x ^ q / ((q + 1).factorial : ℝ)) =
      fun q : ℕ => (x ^ (q + 1) / ((q + 1).factorial : ℝ)) / x := by
      funext n
      rw [pow_succ, mul_div_right_comm, mul_div_cancel_right₀ _ hx]
    rw [he]
    exact (hasSum_exp_sub_one x).div_const x

variable {ι : Type*} [Fintype ι]

private theorem posSemidef_of_entrywise_hasSum
    {F : ℕ → Matrix ι ι ℝ} {G : Matrix ι ι ℝ} (hF : ∀ n, (F n).PosSemidef)
    (hG : ∀ i j, HasSum (fun n => F n i j) (G i j)) : G.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    rw [← (hG i j).tsum_eq, ← (hG j i).tsum_eq]
    exact tsum_congr fun n => by
      simpa using ((hF n).isHermitian.apply i j)
  · intro x
    have hsum : HasSum (fun n => x ⬝ᵥ (F n *ᵥ x)) (x ⬝ᵥ (G *ᵥ x)) := by
      simp only [dotProduct, Matrix.mulVec]
      apply hasSum_sum
      intro i _
      apply HasSum.mul_left
      apply hasSum_sum
      intro j _
      apply HasSum.mul_right
      exact hG i j
    rw [star_trivial, ← hsum.tsum_eq]
    apply tsum_nonneg
    intro n
    simpa using (hF n).dotProduct_mulVec_nonneg x

/-- Applying the exponential first divided difference entrywise to a positive
semidefinite Gram kernel preserves positive semidefiniteness. -/
theorem posSemidef_expm1Div_gram {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (Matrix.of fun i j => expm1Div (A i j)).PosSemidef := by
  apply posSemidef_of_entrywise_hasSum
    (F := fun q => (((q + 1).factorial : ℝ)⁻¹) • schurPower A q)
  · intro q
    exact (posSemidef_schurPower hA q).smul (by positivity)
  · intro i j
    simpa only [Matrix.smul_apply, schurPower_apply, Matrix.of_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hasSum_expm1Div (A i j)

/-- Summed version of the first-factor bound. It keeps one compressed factor
and sums the remaining powers of the uncompressed Gram kernel. -/
theorem posSemidef_exponential_compress_first {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : (A - B).PosSemidef) :
    (((Matrix.of fun i j => expm1Div (A i j)) ⊙ B) -
      Matrix.of (fun i j => Real.exp (B i j) - 1)).PosSemidef := by
  apply posSemidef_of_entrywise_hasSum (F := fun q => (((q + 1).factorial : ℝ)⁻¹) •
    ((schurPower A q ⊙ B) - schurPower B (q + 1)))
  · intro q
    exact (posSemidef_schurPower_compress_first hA hB hAB q).smul (by positivity)
  · intro i j
    have h := ((hasSum_expm1Div (A i j)).mul_right (B i j)).sub (hasSum_exp_sub_one (B i j))
    simp only [Matrix.smul_apply, Matrix.sub_apply, schurPower_apply, Matrix.of_apply,
      hadamard_apply, smul_eq_mul, mul_sub]
    have h1 (n : ℕ) :
        ((↑(n + 1).factorial : ℝ)⁻¹) * ((A i j) ^ n * B i j) =
          ((A i j) ^ n / ((n + 1).factorial : ℝ)) * B i j := by ring
    have h2 (n : ℕ) :
        ((↑(n + 1).factorial : ℝ)⁻¹) * (B i j) ^ (n + 1) =
          (B i j) ^ (n + 1) / ((n + 1).factorial : ℝ) := by ring
    simp only [h1, h2]
    exact h

omit [Fintype ι] in
/-- The centered exponential Gram kernel factors exactly into its first
factor and the series for the remaining degrees. -/
theorem expm1Div_hadamard_self (A : Matrix ι ι ℝ) :
    (Matrix.of fun i j => expm1Div (A i j)) ⊙ A =
      Matrix.of (fun i j => Real.exp (A i j) - 1) := by
  ext i j
  simp only [hadamard_apply, Matrix.of_apply]
  by_cases h : A i j = 0
  · simp [h]
  · rw [expm1Div, if_neg h, div_mul_cancel₀ _ h]

end SketchOrientation
