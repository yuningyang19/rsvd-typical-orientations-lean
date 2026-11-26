import SketchOrientation.TwoLevelTail

namespace SketchOrientation

open Matrix
open scoped Matrix.Norms.Frobenius

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq l]

/-- The energy fractions in Section 2. -/
noncomputable def residualFraction (A : Matrix m n ℝ) (Ω : Matrix n l ℝ) : ℝ :=
  squaredResidual A Ω / squaredFrobenius A

noncomputable def normalizedGram (A : Matrix m n ℝ) : Matrix n n ℝ :=
  (squaredFrobenius A)⁻¹ • (Aᵀ * A)

omit [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq l] in
theorem normalizedGram_compressed_isHermitian (A : Matrix m n ℝ) (Ω : Matrix n l ℝ) :
    (Ωᵀ * normalizedGram A * Ω).IsHermitian := by
  change (Ωᵀ * normalizedGram A * Ω)ᴴ = _
  simp only [conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_transpose,
    normalizedGram, transpose_smul, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The normalized Gram correspondence for D(A, Ω), including the
paper's Moore–Penrose branch at deficient sampled range. -/
theorem residualFraction_eq_normalizedGram (A : Matrix m n ℝ) (Ω : Matrix n l ℝ)
    (hA : A ≠ 0) :
    residualFraction A Ω = 1 -
      (symmetricPseudoInverse (Ωᵀ * normalizedGram A * Ω)
        (normalizedGram_compressed_isHermitian A Ω) *
        (Ωᵀ * normalizedGram A * normalizedGram A * Ω)).trace := by
  let e := squaredFrobenius A
  let s := e⁻¹
  let T := (A * Ω)ᵀ * (A * Ω)
  let N := Ωᵀ * (Aᵀ * A) * (Aᵀ * A) * Ω
  let K := normalizedGram A
  let S := Ωᵀ * K * Ω
  let Q := symmetricPseudoInverse S (normalizedGram_compressed_isHermitian A Ω)
  have hE : e ≠ 0 := by
    dsimp [e]
    rw [squaredFrobenius_eq_norm_sq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hA)
  have hR : S = s • T := by
    simp only [S, K, normalizedGram, s, e, T, transpose_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  have hN : Ωᵀ * K * K * Ω = (s * s) • N := by
    simp only [K, normalizedGram, s, e, N, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      Matrix.mul_assoc]
  have hTriple : (s • T) * Q * (s • T) = s • T := by
    calc
      _ = S * Q * S := congrArg₂ (fun X Y => X * Q * Y) hR.symm hR.symm
      _ = S := symmetricPseudoInverse_penrose S _
      _ = _ := hR
  have hScaled : s • (T * (s • Q) * T) = s • T := by
    simpa only [Matrix.smul_mul, Matrix.mul_smul] using hTriple
  have hPen : T * (s • Q) * T = T := by
    have h := congrArg (fun M : Matrix l l ℝ => e • M) hScaled
    simpa only [smul_smul, show e * s = 1 from mul_inv_cancel₀ hE, one_smul] using h
  unfold residualFraction
  rw [squaredResidual_gram_of_inner_inverse _ _ (s • Q) hPen]
  change (e - ((s • Q) * N).trace) / e = 1 - (Q * (Ωᵀ * K * K * Ω)).trace
  rw [hN, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul,
    sub_div, div_self hE, div_eq_mul_inv]
  ring

omit [DecidableEq n] [DecidableEq m] in
theorem squaredFrobenius_transpose (A : Matrix m n ℝ) :
    squaredFrobenius Aᵀ = squaredFrobenius A := by
  simp only [squaredFrobenius, transpose_transpose, trace_mul_comm A Aᵀ]

omit [DecidableEq n] in
/-- Projecting into the sampled range minimizes the residual among all
matrices whose columns are formed from the sampled columns. -/
theorem squaredResidual_le_sampled_approximation
    (A : Matrix m n ℝ) (Ω : Matrix n l ℝ) (R : Matrix l n ℝ) :
    squaredResidual A Ω ≤ squaredFrobenius (A - (A * Ω) * R) := by
  let Y := A * Ω
  let P := rangeProjector Y
  have hp : Pᵀ = P := rangeProjector_transpose Y
  have hi : P * P = P := rangeProjector_mul_self Y
  have hy : (1 - P) * Y = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul_sample Y, sub_self]
  have hEq : (1 - P) * (A - Y * R) = (1 - P) * A := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc (1 - P), hy, Matrix.zero_mul, sub_zero]
  have h := squaredFrobenius_mul_projector_right_le (A - Y * R)ᵀ P hp hi
  change squaredFrobenius ((1 - P) * A) ≤ squaredFrobenius (A - Y * R)
  have hc : (1 - P)ᵀ = 1 - P := by rw [transpose_sub, transpose_one, hp]
  rw [← hEq, ← squaredFrobenius_transpose ((1 - P) * (A - Y * R)), transpose_mul, hc]
  exact h.trans_eq (squaredFrobenius_transpose (A - Y * R))

omit [DecidableEq n] in
theorem residualFraction_mem_unitInterval (A : Matrix m n ℝ) (Ω : Matrix n l ℝ) :
    residualFraction A Ω ∈ Set.Icc (0 : ℝ) 1 := by
  have h := squaredResidual_le_sampled_approximation A Ω (0 : Matrix l n ℝ)
  rw [Matrix.mul_zero, sub_zero] at h
  have he := squaredFrobenius_nonneg A
  change 0 ≤ squaredResidual A Ω / squaredFrobenius A ∧
    squaredResidual A Ω / squaredFrobenius A ≤ 1
  refine ⟨div_nonneg (squaredFrobenius_nonneg _) he, ?_⟩
  rcases he.eq_or_lt with hzero | hpos
  · rw [← hzero, div_zero]
    exact zero_le_one
  · exact (div_le_one hpos).2 h

end SketchOrientation
