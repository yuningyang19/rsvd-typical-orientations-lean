import SketchOrientation.TwoLevelTail

namespace SketchOrientation

open Matrix

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq l]

/-- Matrix-trace form of the two-level residual calculation. There is
no assumption on the rank of the compressed target block. -/
theorem twoLevel_squaredResidual (A : Matrix m n ℝ) (U : Matrix n l ℝ) (V : Matrix n k ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {Γ : ℝ} (hΓ : 1 ≤ Γ)
    (hGram : Aᵀ * A = 1 + (Γ - 1) • (V * Vᵀ)) :
    squaredResidual A U =
      (Fintype.card n : ℝ) - Fintype.card k - Fintype.card l +
        Γ * ((1 + (Γ - 1) • (Vᵀ * (U * Uᵀ) * V))⁻¹).trace := by
  let C : Matrix l k ℝ := Uᵀ * V
  have hLeft : (A * U)ᵀ * (A * U) = 1 + (Γ - 1) • (C * Cᵀ) := calc
    _ = Uᵀ * (Aᵀ * A) * U := by simp only [transpose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hGram]; exact twoLevel_gram_compress U hU V _
  have hRight :
      Uᵀ * (Aᵀ * A) * (Aᵀ * A) * U = 1 + (Γ ^ 2 - 1) • (C * Cᵀ) := calc
    _ = Uᵀ * ((Aᵀ * A) * (Aᵀ * A)) * U := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hGram, twoLevel_gram_square _ hV]
      exact twoLevel_gram_compress U hU V _
  have hDet : IsUnit (((A * U)ᵀ * (A * U)).det) := by
    rw [hLeft]
    apply isUnit_iff_ne_zero.mpr
    simpa only [transpose_transpose] using (affineGram_posDef Cᵀ (sub_nonneg.mpr hΓ)).det_pos.ne'
  have hTotal : squaredFrobenius A =
      (Fintype.card n : ℝ) + (Γ - 1) * Fintype.card k := by
    unfold squaredFrobenius
    rw [hGram, trace_add, trace_one, trace_smul, smul_eq_mul,
      trace_mul_comm V Vᵀ, hV, trace_one]
  have hT : Cᵀ * C = Vᵀ * (U * Uᵀ) * V := by
    simp only [C, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [squaredResidual_gram_inv _ _ hDet, hLeft, hRight, twoLevel_captured_trace _ hΓ,
    hTotal, hT]
  ring

/-- The paper's centered loss before the sketch average. -/
noncomputable def centeredRankLoss (k : ℕ) (A : Matrix m n ℝ) (Ω : Matrix n l ℝ) : ℝ :=
  (tailRelativeError k A Ω - 1) / (k : ℝ)

/-- Equation (2.3) in its compressed, regularized inverse-trace
representation. All normalization factors refer to the actual best-rank
error and actual sampled range. -/
theorem twoLevel_centeredRankLoss (A : Matrix m n ℝ) (U : Matrix n l ℝ) (V : Matrix n k ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {Γ : ℝ} (hΓ : 1 ≤ Γ)
    (hGram : Aᵀ * A = 1 + (Γ - 1) • (V * Vᵀ))
    (hk : 0 < Fintype.card k) (hkn : Fintype.card k < Fintype.card n) :
    centeredRankLoss (Fintype.card k) A U =
      (Γ * ((1 + (Γ - 1) • (Vᵀ * (U * Uᵀ) * V))⁻¹).trace - Fintype.card l) /
        ((Fintype.card k : ℝ) * ((Fintype.card n : ℝ) - Fintype.card k)) := by
  unfold centeredRankLoss tailRelativeError
  rw [twoLevel_squaredResidual _ _ _ hU hV hΓ hGram, twoLevel_optimalTail _ _ hV hΓ hGram]
  have hkR : (0 : ℝ) < Fintype.card k := by exact_mod_cast hk
  have hknR : (Fintype.card k : ℝ) < Fintype.card n := by exact_mod_cast hkn
  field_simp [hkR.ne', (sub_pos.mpr hknR).ne']
  ring

end SketchOrientation
