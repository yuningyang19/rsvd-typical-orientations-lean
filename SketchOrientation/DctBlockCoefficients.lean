import SketchOrientation.DctSketchLaw
import SketchOrientation.DctSampleCovariance
import SketchOrientation.BlockLoss
import SketchOrientation.RandomSignBlockLimit

namespace SketchOrientation

open Matrix Edge.Walsh
open scoped RealInnerProductSpace

/-- The random frame entering the final signed transform. -/
noncomputable def DctPasses.intermediateFrame {n k : ℕ} (mode : DctPasses)
    (V : Matrix (Fin n) (Fin k) ℝ) (ε : Fin n → Bool) :
    Matrix (Fin n) (Fin k) ℝ :=
  match mode with
  | .one => V
  | .two => Cosine.signedDCT V ε

namespace Cosine

theorem intermediateFrame_orthonormal {n k : ℕ} (mode : DctPasses)
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) (ε : Fin n → Bool) :
    (mode.intermediateFrame V ε)ᵀ * mode.intermediateFrame V ε = 1 := by
  cases mode
  · exact hV
  · exact signedDCT_transpose_mul hV ε

/-- Coefficients of the final sign sum in sampled-row/target-column order. -/
noncomputable def dctBlockCoefficient {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (J : Fin l ↪ Fin n) (i : Fin n) : EuclideanSpace ℝ (Fin l × Fin k) :=
  WithLp.toLp 2 fun p => Real.sqrt (n : ℝ) * dctII n (J p.1) i * V i p.2

/-- The exact conditional sign expansion of the actual projected sketch. -/
theorem dctSketch_projected_eq_signedSum {n k l : ℕ} (mode : DctPasses)
    (V : Matrix (Fin n) (Fin k) ℝ) (d : DctDraw n l) :
    (WithLp.toLp 2 (fun p : Fin l × Fin k => scaledTargetBlock V (mode.sketch d) p.2 p.1) :
      EuclideanSpace ℝ (Fin l × Fin k)) =
      signedCoefficientSum (dctBlockCoefficient (mode.intermediateFrame V d.2.2) d.1) d.2.1 := by
  classical
  have hJ (r : Fin l) (i : Fin n) : (rowSelector d.1 * pairedDctII n) r i =
      pairedDctII n (d.1 r) i := by
    simp only [Matrix.mul_apply, rowSelector, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hA : (mode.sketch d)ᵀ * V =
      (rowSelector d.1 * pairedDctII n) *
      (diagonal (rademacherValue ∘ d.2.1) * mode.intermediateFrame V d.2.2) := by
    cases mode <;> simp only [DctPasses.sketch, onePassDct, twoPassDct, transpose_transpose,
      DctPasses.intermediateFrame, signedDCT, Matrix.mul_assoc]
    all_goals rfl
  ext p
  simp only [scaledTargetBlock, Matrix.smul_apply, smul_eq_mul, PiLp.toLp_apply,
    signedCoefficientSum, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, dctBlockCoefficient]
  rw [show (Vᵀ * mode.sketch d) p.2 p.1 = ((mode.sketch d)ᵀ * V) p.1 p.2 by
    rw [← transpose_transpose V, ← transpose_mul]; rfl, hA]
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hJ, Matrix.diagonal_mul]
  change _ = (if d.2.1 i then (1 : ℝ) else -1) * _
  change Real.sqrt (n : ℝ) * (dctII n (d.1 p.1) i *
    (rademacherValue (d.2.1 i) * mode.intermediateFrame V d.2.2 i p.2)) = _
  simp only [rademacherValue]
  ring

/-- The conditional covariance is the sum of the outer products of the
actual sign coefficients. -/
theorem sampledCovariance_eq_coefficients {n k l : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (J : Fin l ↪ Fin n) (p q : Fin l × Fin k) :
    sampledCovariance V J p q = ∑ i, dctBlockCoefficient V J i p * dctBlockCoefficient V J i q := by
  simp only [sampledCovariance, covarianceBlock, dctBlockCoefficient, PiLp.toLp_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n := by
    rw [← pow_two, Real.sq_sqrt (by positivity)]
  linear_combination
    (dctII n (J p.1) i * dctII n (J q.1) i * (V i p.2 * V i q.2)) * (-h)

private theorem dct_coefficient_inner {n k l : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (J : Fin l ↪ Fin n) (i : Fin n)
    (T : EuclideanSpace ℝ (Fin l × Fin k)) :
    ⟪dctBlockCoefficient V J i, T⟫ = ∑ p, T p * dctBlockCoefficient V J i p := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

/-- The variance discrepancy of every scalar test is its quadratic form
against the native sampled covariance defect. -/
theorem dctCoefficient_variance_defect_eq {n k l : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (J : Fin l ↪ Fin n)
    (T : EuclideanSpace ℝ (Fin l × Fin k)) :
    (∑ i, ⟪dctBlockCoefficient V J i, T⟫ ^ 2) - ‖T‖ ^ 2 =
      ∑ p, ∑ q, (T p * T q) * (sampledCovariance V J - 1) p q := by
  classical
  have hCov : (∑ i, ⟪dctBlockCoefficient V J i, T⟫ ^ 2) =
      ∑ p, ∑ q, (T p * T q) * sampledCovariance V J p q := by
    simp_rw [dct_coefficient_inner, pow_two, Finset.sum_mul_sum,
      sampledCovariance_eq_coefficients, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hId : (∑ p, ∑ q, (T p * T q) * (1 : Matrix (Fin l × Fin k) (Fin l × Fin k) ℝ) p q) =
      ‖T‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Matrix.one_apply, pow_two]
  simp_rw [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hCov, hId]

end Cosine
end SketchOrientation
