import SketchOrientation.GaussianGramLaw

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

variable {d k : ℕ}

theorem ae_gaussianGram_inv_diag_nonneg (hdk : k ≤ d) (j : Fin k) :
    ∀ᵐ Z ∂gaussianMatrixLaw d k, 0 ≤ (gaussianGram Z)⁻¹ j j := by
  filter_upwards [ae_gaussianMatrix_injective hdk] with Z hZ
  exact ((gaussianGram_posDef Z hZ).inv.diag_pos).le

/-- Each inverse diagonal is integrable and has mean `1/(d-k-1)`. -/
theorem gaussianGram_inv_diag_mean (hdk : k + 1 < d) (j : Fin k) :
    Integrable (fun Z => (gaussianGram Z)⁻¹ j j) (gaussianMatrixLaw d k) ∧
      (∫ Z, (gaussianGram Z)⁻¹ j j ∂gaussianMatrixLaw d k) =
        1 / ((d : ℝ) - k - 1) := by
  cases k with
  | zero => exact j.elim0
  | succ k =>
    have hν : 2 < d - k := by omega
    have hm := measurable_gaussianGram_inv_entry (d := d) j j
    have ha : 0 ≤ᵐ[gaussianMatrixLaw d (k + 1)] (fun Z => (gaussianGram Z)⁻¹ j j) :=
      ae_gaussianGram_inv_diag_nonneg (by omega) j
    have hc : ((d - k : ℕ) : ℝ) - 2 = (d : ℝ) - (k + 1 : ℕ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      ring
    have he : (∫⁻ Z, ENNReal.ofReal ((gaussianGram Z)⁻¹ j j)
        ∂gaussianMatrixLaw d (k + 1)) = ENNReal.ofReal (1 / (((d - k : ℕ) : ℝ) - 2)) := by
      calc
        _ = ∫⁻ s, ENNReal.ofReal s⁻¹ ∂(gaussianMatrixLaw d (k + 1)).map
            (fun Z => ((gaussianGram Z)⁻¹ j j)⁻¹) := by
          have hφ : Measurable (fun s : ℝ => ENNReal.ofReal s⁻¹) :=
            measurable_id.inv.ennreal_ofReal
          have hm' : Measurable (fun Z => ((gaussianGram Z)⁻¹ j j)⁻¹) := hm.inv
          rw [lintegral_map hφ hm']
          simp only [inv_inv]
        _ = _ := by
          rw [gaussianGram_inv_diag_reciprocal_law (by omega), chiSquare_inverse_moment hν]
    refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
    · rw [hasFiniteIntegral_iff_ofReal ha, he]
      exact ENNReal.ofReal_lt_top
    · have hν' : (2 : ℝ) < ((d - k : ℕ) : ℝ) := by exact_mod_cast hν
      rw [integral_eq_lintegral_of_nonneg_ae ha hm.aestronglyMeasurable, he,
        ENNReal.toReal_ofReal (one_div_nonneg.mpr (sub_nonneg.mpr hν'.le)), hc]

/-- First inverse-trace moment under the primitive iid Gaussian matrix law. -/
theorem gaussianGram_inv_trace_mean (hdk : k + 1 < d) :
    Integrable (fun Z => (gaussianGram Z)⁻¹.trace) (gaussianMatrixLaw d k) ∧
      (∫ Z, (gaussianGram Z)⁻¹.trace ∂gaussianMatrixLaw d k) =
        (k : ℝ) / ((d : ℝ) - k - 1) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  have hi : ∀ j : Fin k,
      Integrable (fun Z => (gaussianGram Z)⁻¹ j j) (gaussianMatrixLaw d k) :=
    fun j => (gaussianGram_inv_diag_mean hdk j).1
  refine ⟨integrable_finsetSum _ (fun j _ => hi j), ?_⟩
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp [fun j => (gaussianGram_inv_diag_mean hdk j).2, div_eq_mul_inv]

end SketchOrientation
