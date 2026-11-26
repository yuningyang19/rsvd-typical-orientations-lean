import SketchOrientation.GammaMoments

namespace SketchOrientation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A positive-dimensional chi-square draw is almost surely positive. -/
theorem ae_chiSquare_pos (ν : ℕ) :
    ∀ᵐ x ∂chiSquareLaw ν, 0 < x := by
  rw [ae_iff]
  unfold chiSquareLaw gammaMeasure
  rw [show {x : ℝ | ¬ 0 < x} = Set.Iic 0 by ext x; simp, withDensity_apply _ measurableSet_Iic]
  rw [← restrict_Iio_eq_restrict_Iic]
  exact lintegral_gammaPDF_of_nonpos le_rfl

private theorem chiSquare_mean_ofReal {ν : ℕ} (hν : 0 < ν) :
    (∫⁻ x, ENNReal.ofReal x ∂chiSquareLaw ν) = ENNReal.ofReal ν := by
  have hν' : (0 : ℝ) < ν := Nat.cast_pos.mpr hν
  let a := (ν : ℝ) / 2
  have ha : 0 < a := by positivity
  have hg : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have h := gamma_negative_moment (a := a) (rate := (1 : ℝ) / 2) (q := -1)
    ha (by norm_num) (by linarith)
  unfold chiSquareLaw
  have h1 : (-(-1 : ℝ)) = 1 := by norm_num
  have h2 : a - -1 = a + 1 := by ring
  rw [h1, h2, Real.Gamma_add_one ha.ne', Real.rpow_neg_one] at h
  simp_rw [Real.rpow_one] at h
  rw [h]
  congr 1
  field_simp [hg]
  dsimp [a]
  ring

/-- The first chi-square moment equals its degrees of freedom. -/
theorem chiSquare_mean {ν : ℕ} (hν : 0 < ν) :
    Integrable (fun x : ℝ => x) (chiSquareLaw ν) ∧ (∫ x, x ∂chiSquareLaw ν) = (ν : ℝ) := by
  have hp : 0 ≤ᵐ[chiSquareLaw ν] (fun x : ℝ => x) := (ae_chiSquare_pos ν).mono fun x hx => hx.le
  have hm : AEStronglyMeasurable (fun x : ℝ => x) (chiSquareLaw ν) :=
    measurable_id.aestronglyMeasurable
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hp, chiSquare_mean_ofReal hν]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hp hm, chiSquare_mean_ofReal hν,
      ENNReal.toReal_ofReal (Nat.cast_nonneg _)]

/-- Exact real reciprocal expectation of a chi-square variable. -/
theorem chiSquare_inverse_mean {ν : ℕ} (hν : 2 < ν) :
    Integrable (fun x : ℝ => x⁻¹) (chiSquareLaw ν) ∧
      (∫ x, x⁻¹ ∂chiSquareLaw ν) = 1 / ((ν : ℝ) - 2) := by
  have hp : 0 ≤ᵐ[chiSquareLaw ν] (fun x : ℝ => x⁻¹) :=
    (ae_chiSquare_pos ν).mono fun x hx => inv_nonneg.mpr hx.le
  have hm : AEStronglyMeasurable (fun x : ℝ => x⁻¹) (chiSquareLaw ν) :=
    measurable_id.inv.aestronglyMeasurable
  have hd : (2 : ℝ) < ν := by exact_mod_cast hν
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hp, chiSquare_inverse_moment hν]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hp hm, chiSquare_inverse_moment hν,
      ENNReal.toReal_ofReal (by positivity)]

end SketchOrientation
