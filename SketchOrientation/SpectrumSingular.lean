import SketchOrientation.SpectrumResidual
import SketchOrientation.DctSampleCovariance
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace SketchOrientation

open Matrix
open scoped Matrix.Norms.Frobenius

variable {r t l : Type*} [Fintype r] [Fintype t] [Fintype l]
  [DecidableEq r] [DecidableEq t] [DecidableEq l]

/-- The singular limiting branch fits the leading columns exactly by a
right inverse of the observed leading block, and leaves only a tail error. -/
theorem singularSpectrum_residual_le
    (C₁ : Matrix r r ℝ) (C₂ : Matrix t t ℝ)
    (Z₁ : Matrix r l ℝ) (Z₂ : Matrix t l ℝ) (R : Matrix l r ℝ) (hR : Z₁ * R = 1) :
    squaredResidual (fromBlocks C₁ 0 0 C₂) (fromRows Z₁ Z₂) ≤
      squaredFrobenius C₂ + squaredFrobenius (C₂ * Z₂) * squaredFrobenius R := by
  let A := fromBlocks C₁ (0 : Matrix r t ℝ) (0 : Matrix t r ℝ) C₂
  let Ω := fromRows Z₁ Z₂
  let U := fromCols R (0 : Matrix l t ℝ)
  have hZ : A * Ω = fromRows (C₁ * Z₁) (C₂ * Z₂) := by
    simp only [A, Ω, fromBlocks_mul_fromRows, Matrix.zero_mul, add_zero, zero_add]
  have hFit : (A * Ω) * U = fromBlocks C₁ (0 : Matrix r t ℝ) (C₂ * Z₂ * R) 0 := by
    simp only [hZ, U, fromRows_mul_fromCols, Matrix.mul_zero, Matrix.mul_assoc C₁, hR, Matrix.mul_one]
  have hErr : A - (A * Ω) * U =
      fromBlocks (0 : Matrix r r ℝ) (0 : Matrix r t ℝ) (-(C₂ * Z₂ * R)) C₂ := by
    rw [hFit]
    ext i j
    cases i <;> cases j <;> simp [A]
  have hM : squaredFrobenius (A - (A * Ω) * U) =
      squaredFrobenius C₂ + squaredFrobenius ((C₂ * Z₂) * R) := by
    rw [hErr]
    simp only [Cosine.squaredFrobenius_eq_sum_entries, Fintype.sum_sum_type, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply,
      zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, zero_add, add_comm,
      neg_sq, Finset.sum_add_distrib]
  rw [← show A = fromBlocks C₁ 0 0 C₂ from rfl, ← show Ω = fromRows Z₁ Z₂ from rfl]
  refine (squaredResidual_le_sampled_approximation A Ω U).trans ?_
  rw [hM]
  refine add_le_add (le_refl _) ?_
  simp only [squaredFrobenius_eq_norm_sq]
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (Matrix.frobenius_norm_mul (C₂ * Z₂) R) _

end SketchOrientation
