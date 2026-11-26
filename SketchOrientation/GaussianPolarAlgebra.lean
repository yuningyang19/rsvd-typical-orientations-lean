import SketchOrientation.GaussianGramLaw
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.Algebra.Group.Matrix

namespace SketchOrientation

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {n k : ℕ}

/-- Positive square root of the Gram in the Gaussian polar decomposition. -/
noncomputable def gaussianPolarRadial (G : Matrix (Fin n) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt (gaussianGram G)

/-- Orthogonal factor of the Gaussian polar decomposition on the full-rank locus. -/
noncomputable def gaussianPolarFrame (G : Matrix (Fin n) (Fin k) ℝ) : Matrix (Fin n) (Fin k) ℝ :=
  G * (gaussianPolarRadial G)⁻¹

theorem gaussianGram_posSemidef (G : Matrix (Fin n) (Fin k) ℝ) :
    (gaussianGram G).PosSemidef := by
  simpa [gaussianGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self G

private theorem continuous_gaussianGram : Continuous (@gaussianGram n k) :=
  (continuous_id.matrix_transpose).matrix_mul continuous_id

theorem continuous_gaussianPolarRadial : Continuous (@gaussianPolarRadial n k) := by
  exact CFC.continuousOn_sqrt.comp_continuous continuous_gaussianGram
    (fun G => (gaussianGram_posSemidef G).nonneg)

theorem measurable_matrix_nonsing_inv :
    Measurable (fun G : Matrix (Fin k) (Fin k) ℝ => G⁻¹) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, Matrix.adjugate_apply]
  have h : Continuous (fun G : Matrix (Fin k) (Fin k) ℝ => G.updateRow j (Pi.single i 1)) :=
    Continuous.matrix_updateRow j continuous_id continuous_const
  have hd : Continuous (fun G : Matrix (Fin k) (Fin k) ℝ => G.det) := continuous_id.matrix_det
  exact hd.measurable.inv.mul (hd.comp h).measurable

theorem measurable_gaussianPolarFrame :
    Measurable (@gaussianPolarFrame n k) := by
  have hMul : Measurable (fun p : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ => p.1 * p.2) :=
    (continuous_fst.matrix_mul continuous_snd).measurable
  exact hMul.comp (measurable_id.prodMk
    (measurable_matrix_nonsing_inv.comp continuous_gaussianPolarRadial.measurable))

theorem gaussianPolarRadial_sq (G : Matrix (Fin n) (Fin k) ℝ) :
    gaussianPolarRadial G * gaussianPolarRadial G = gaussianGram G :=
  CFC.sqrt_mul_sqrt_self _ (gaussianGram_posSemidef G).nonneg

theorem gaussianPolarRadial_transpose (G : Matrix (Fin n) (Fin k) ℝ) :
    (gaussianPolarRadial G)ᵀ = gaussianPolarRadial G := by
  have h : 0 ≤ gaussianPolarRadial G := CFC.sqrt_nonneg _
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h.posSemidef.isHermitian.eq

theorem gaussianPolarRadial_det_isUnit (G : Matrix (Fin n) (Fin k) ℝ)
    (hG : Function.Injective G.mulVec) : IsUnit (gaussianPolarRadial G).det := by
  have h := (gaussianGram G).isUnit_iff_isUnit_det.mp (gaussianGram_posDef G hG).isUnit
  rw [← gaussianPolarRadial_sq, Matrix.det_mul] at h
  exact isUnit_iff_ne_zero.mpr fun hz => h.ne_zero (by simp [hz])

/-- Full-rank polar factors satisfy the Stiefel constraint. -/
theorem gaussianPolarFrame_transpose_mul_self (G : Matrix (Fin n) (Fin k) ℝ)
    (hG : Function.Injective G.mulVec) :
    (gaussianPolarFrame G)ᵀ * gaussianPolarFrame G = 1 := by
  have hH := gaussianPolarRadial_det_isUnit G hG
  unfold gaussianPolarFrame
  rw [transpose_mul, transpose_nonsing_inv, gaussianPolarRadial_transpose, ← Matrix.mul_assoc,
    Matrix.mul_assoc (gaussianPolarRadial G)⁻¹ Gᵀ G]
  change (gaussianPolarRadial G)⁻¹ * gaussianGram G * (gaussianPolarRadial G)⁻¹ = 1
  rw [← gaussianPolarRadial_sq,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hH, Matrix.one_mul, Matrix.mul_nonsing_inv _ hH]

theorem gaussianPolarFrame_mul_radial (G : Matrix (Fin n) (Fin k) ℝ)
    (hG : Function.Injective G.mulVec) :
    gaussianPolarFrame G * gaussianPolarRadial G = G := by
  rw [gaussianPolarFrame, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gaussianPolarRadial_det_isUnit G hG),
    Matrix.mul_one]

theorem gaussianGram_mul_orthogonal_left (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) (G : Matrix (Fin n) (Fin k) ℝ) :
    gaussianGram (Q * G) = gaussianGram G := by
  unfold gaussianGram
  rw [transpose_mul, Matrix.mul_assoc Gᵀ, ← Matrix.mul_assoc Qᵀ Q, hQ, Matrix.one_mul]

theorem gaussianPolarRadial_mul_orthogonal_left (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) (G : Matrix (Fin n) (Fin k) ℝ) :
    gaussianPolarRadial (Q * G) = gaussianPolarRadial G := by
  simp [gaussianPolarRadial, gaussianGram_mul_orthogonal_left Q hQ]

theorem gaussianPolarFrame_mul_orthogonal_left (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) (G : Matrix (Fin n) (Fin k) ℝ) :
    gaussianPolarFrame (Q * G) = Q * gaussianPolarFrame G := by
  simp [gaussianPolarFrame, gaussianPolarRadial_mul_orthogonal_left Q hQ, Matrix.mul_assoc]

end SketchOrientation
