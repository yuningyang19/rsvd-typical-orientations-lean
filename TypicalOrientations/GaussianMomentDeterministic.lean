import SketchOrientation.SpectrumSingular
import SketchOrientation.GaussianGramAlgebra

namespace TypicalOrientations

open Matrix SketchOrientation

noncomputable section

variable {k m ℓ : ℕ}

/-- The right inverse of the leading Gaussian row block, when it has full row rank. -/
def leadingRightInverse (B : Matrix (Fin k) (Fin ℓ) ℝ) : Matrix (Fin ℓ) (Fin k) ℝ :=
  Bᵀ * (gaussianGram Bᵀ)⁻¹

theorem leading_mul_rightInverse (B : Matrix (Fin k) (Fin ℓ) ℝ)
    (hB : Function.Injective Bᵀ.mulVec) : B * leadingRightInverse B = 1 := by
  have hi : IsUnit (gaussianGram Bᵀ).det := (isUnit_iff_isUnit_det _).mp (gaussianGram_posDef Bᵀ hB).isUnit
  calc
    B * leadingRightInverse B = (gaussianGram Bᵀ) * (gaussianGram Bᵀ)⁻¹ := by
      simp only [leadingRightInverse, gaussianGram, transpose_transpose, Matrix.mul_assoc]
    _ = 1 := Matrix.mul_nonsing_inv _ hi

/-- The covariance of the transformed tail row is the inverse leading
Gram matrix as in the proof of Lemma 3.2. -/
theorem leadingRightInverse_gram (B : Matrix (Fin k) (Fin ℓ) ℝ)
    (hB : Function.Injective Bᵀ.mulVec) :
    (leadingRightInverse B)ᵀ * leadingRightInverse B = (gaussianGram Bᵀ)⁻¹ := by
  let W := gaussianGram Bᵀ
  change (Bᵀ * W⁻¹)ᵀ * (Bᵀ * W⁻¹) = W⁻¹
  have hSym : W.IsSymm := (isHermitian_iff_isSymm.mp (gaussianGram_posDef Bᵀ hB).isHermitian)
  have hu : IsUnit W.det := (isUnit_iff_isUnit_det _).mp (gaussianGram_posDef Bᵀ hB).isUnit
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hSym.eq, transpose_transpose]
  calc
    _ = W⁻¹ * (W * W⁻¹) := by simp only [W, gaussianGram, transpose_transpose, Matrix.mul_assoc]
    _ = W⁻¹ := by rw [Matrix.mul_nonsing_inv W hu, Matrix.mul_one]

theorem leadingRightInverse_sum_column_sq (B : Matrix (Fin k) (Fin ℓ) ℝ)
    (hB : Function.Injective Bᵀ.mulVec) :
    (∑ j, ∑ i, leadingRightInverse B i j ^ 2) = (gaussianGram Bᵀ)⁻¹.trace := by
  rw [← leadingRightInverse_gram B hB]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

/-- Rowwise deterministic estimate in equation (3.4): fit the leading
columns exactly, then sum the actual squared errors in the remaining rows. -/
theorem diagonal_residual_le_tail_rows (s : Fin k → ℝ) (t : Fin m → ℝ)
    (B : Matrix (Fin k) (Fin ℓ) ℝ) (Z : Matrix (Fin m) (Fin ℓ) ℝ)
    (R : Matrix (Fin ℓ) (Fin k) ℝ) (hR : B * R = 1) :
    squaredResidual (fromBlocks (diagonal s) 0 0 (diagonal t)) (fromRows B Z) ≤
      (∑ i, t i ^ 2) + ∑ i, t i ^ 2 * (∑ j, (Z * R) i j ^ 2) := by
  let A := fromBlocks (diagonal s) (0 : Matrix (Fin k) (Fin m) ℝ)
    (0 : Matrix (Fin m) (Fin k) ℝ) (diagonal t)
  let G := fromRows B Z
  let U := fromCols R (0 : Matrix (Fin ℓ) (Fin m) ℝ)
  have hZ : A * G = fromRows (diagonal s * B) (diagonal t * Z) := by
    simp only [A, G, fromBlocks_mul_fromRows, Matrix.zero_mul, add_zero, zero_add]
  have hfit : (A * G) * U =
      fromBlocks (diagonal s) (0 : Matrix (Fin k) (Fin m) ℝ) (diagonal t * Z * R) 0 := by
    simp only [hZ, U, fromRows_mul_fromCols, Matrix.mul_zero, Matrix.mul_assoc (diagonal s),
      hR, Matrix.mul_one]
  have herr : A - (A * G) * U =
      fromBlocks 0 0 (-(diagonal t * Z * R)) (diagonal t) := by
    rw [hfit]
    ext i j
    cases i <;> cases j <;> simp only [A, Matrix.sub_apply, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply,
      sub_self, zero_sub, sub_zero, Matrix.neg_apply]
  refine (squaredResidual_le_sampled_approximation A G U).trans_eq ?_
  rw [herr]
  simp only [Cosine.squaredFrobenius_eq_sum_entries, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply,
    zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, zero_add, neg_sq,
    Finset.sum_add_distrib, Matrix.mul_assoc (diagonal t), Matrix.diagonal_mul, mul_pow,
    Finset.mul_sum]
  have hdiag (i : Fin m) : (∑ j, diagonal t i j ^ 2) = t i ^ 2 := by
    classical
    simp [Matrix.diagonal_apply, apply_ite (fun x : ℝ => x ^ (2 : ℕ))]
  rw [show (∑ i, ∑ j, diagonal t i j ^ 2) = ∑ i, t i ^ 2 from Finset.sum_congr rfl fun i _ => hdiag i]
  rw [add_comm]

/-- Equation (3.4), with the optimal diagonal tail appearing in both
the normalization and the weights. -/
theorem diagonal_relative_residual_le_weighted_rows (s : Fin k → ℝ) (t : Fin m → ℝ)
    (ht : 0 < ∑ i, (t i)^2)
    (B : Matrix (Fin k) (Fin ℓ) ℝ) (Z : Matrix (Fin m) (Fin ℓ) ℝ)
    (hB : Function.Injective Bᵀ.mulVec) :
    squaredResidual (fromBlocks (diagonal s) 0 0 (diagonal t)) (fromRows B Z) /
      (∑ i, t i ^ 2) ≤
      1 + ∑ i, (t i ^ 2 / (∑ j, t j ^ 2)) *
        (∑ j, (Z * leadingRightInverse B) i j ^ 2) := by
  have h := (div_le_div_of_nonneg_right
    (diagonal_residual_le_tail_rows s t B Z _ (leading_mul_rightInverse B hB)) ht.le)
  rw [add_div, div_self ht.ne', Finset.sum_div] at h
  refine h.trans_eq (congrArg (1 + ·) ?_)
  apply Finset.sum_congr rfl
  intro i _
  ring

end

end TypicalOrientations
