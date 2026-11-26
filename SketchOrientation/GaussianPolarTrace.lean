import SketchOrientation.GaussianGramMean
import SketchOrientation.GaussianPolarLaw

namespace SketchOrientation

open MeasureTheory Matrix

variable {n k : ℕ}

private theorem gaussianGram_inv_weighted_trace_mean (hn : k + 1 < n)
    (A : Matrix (Fin k) (Fin k) ℝ) :
    Integrable (fun G => (A * (gaussianGram G)⁻¹).trace) (gaussianMatrixLaw n k) ∧
      (∫ G, (A * (gaussianGram G)⁻¹).trace ∂gaussianMatrixLaw n k) =
        A.trace / ((n : ℝ) - k - 1) := by
  have hi (i j : Fin k) :
      Integrable (fun G => A i j * (gaussianGram G)⁻¹ j i) (gaussianMatrixLaw n k) :=
    ((gaussianGram_inv_mean hn j i).1).const_mul _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul, fun i j =>
    (gaussianGram_inv_mean hn j i).2]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [div_eq_mul_inv]
  · intro j _ hj
    rw [Matrix.one_apply_ne hj, zero_div, mul_zero]
  · simp

/-- Exact average over the radial law, with any fixed matrix weight. -/
theorem gaussianPolarRadial_weightedInverse_mean (hn : k + 1 < n)
    (A : Matrix (Fin k) (Fin k) ℝ) :
    Integrable (fun H => (A * (H * H)⁻¹).trace) (gaussianRadialFactorLaw n k) ∧
      (∫ H, (A * (H * H)⁻¹).trace ∂gaussianRadialFactorLaw n k) =
        A.trace / ((n : ℝ) - k - 1) := by
  let F := fun H : Matrix (Fin k) (Fin k) ℝ => (A * (H * H)⁻¹).trace
  have hM : Measurable (fun H : Matrix (Fin k) (Fin k) ℝ => A * (H * H)⁻¹) :=
    (continuous_const.matrix_mul continuous_id).measurable.comp
      (measurable_matrix_nonsing_inv.comp (continuous_id.matrix_mul continuous_id).measurable)
  have hTr : Continuous (fun M : Matrix (Fin k) (Fin k) ℝ => M.trace) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i
  have hF : Measurable F := hTr.measurable.comp hM
  have h := gaussianGram_inv_weighted_trace_mean hn A
  have hR := continuous_gaussianPolarRadial (n := n) (k := k)
  unfold gaussianRadialFactorLaw
  change Integrable F ((gaussianMatrixLaw n k).map gaussianPolarRadial) ∧
      (∫ H, F H ∂(gaussianMatrixLaw n k).map gaussianPolarRadial) = _
  rw [integrable_map_measure hF.aestronglyMeasurable hR.measurable.aemeasurable,
    integral_map hR.measurable.aemeasurable hF.aestronglyMeasurable]
  have he : F ∘ gaussianPolarRadial = fun G : Matrix (Fin n) (Fin k) ℝ =>
      (A * (gaussianGram G)⁻¹).trace := by
    funext G
    simp [F, gaussianPolarRadial_sq]
  rw [he]
  simpa only [F, gaussianPolarRadial_sq] using h

/-- Trace cycling puts both radial inverse factors beside each other.
The identity also holds for the total nonsingular-inverse convention when
the compressed Gram is singular. -/
theorem gaussianPolar_inv_projectedGram_trace (G : Matrix (Fin n) (Fin k) ℝ)
    (hG : Function.Injective G.mulVec) (P : Matrix (Fin n) (Fin n) ℝ) :
    (Gᵀ * P * G)⁻¹.trace =
      (((gaussianPolarFrame G)ᵀ * P * gaussianPolarFrame G)⁻¹ *
        (gaussianPolarRadial G * gaussianPolarRadial G)⁻¹).trace := by
  let V := gaussianPolarFrame G
  let H := gaussianPolarRadial G
  let T := Vᵀ * P * V
  have hW : Gᵀ * P * G = H * T * H := by
    conv_lhs => rw [← gaussianPolarFrame_mul_radial G hG]
    simp [V, H, T, transpose_mul, gaussianPolarRadial_transpose, Matrix.mul_assoc]
  change (Gᵀ * P * G)⁻¹.trace = (T⁻¹ * (H * H)⁻¹).trace
  rw [hW, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.trace_mul_comm H⁻¹, Matrix.mul_assoc]

end SketchOrientation
