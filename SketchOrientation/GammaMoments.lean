import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic

namespace SketchOrientation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Multiplication by a negative power changes the Gamma shape.
The integrand identity holds away from the single point zero. -/
private theorem gammaPDF_mul_rpow_neg {a rate q x : ℝ}
    (hrate : 0 < rate) (ha : 0 < a) (hq : q < a) (hx : x ≠ 0) :
    gammaPDF a rate x * ENNReal.ofReal (x ^ (-q)) =
      ENNReal.ofReal (rate ^ q * Real.Gamma (a - q) / Real.Gamma a) *
        gammaPDF (a - q) rate x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · simp [gammaPDF_of_neg hneg]
  have haq : 0 < a - q := sub_pos.mpr hq
  have hcoeff : 0 ≤ rate ^ q * Real.Gamma (a - q) / Real.Gamma a := by
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hrate.le _)
      (Real.Gamma_pos_of_pos haq).le) (Real.Gamma_pos_of_pos ha).le
  rw [gammaPDF_of_nonneg hpos.le, gammaPDF_of_nonneg hpos.le, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_mul hcoeff]
  swap
  · positivity
  congr 1
  calc
    _ = rate ^ a / Real.Gamma a * (x ^ (a - 1) * x ^ (-q)) * Real.exp (-(rate * x)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hpos, show a - 1 + -q = a - q - 1 by ring]
      rw [show a = q + (a - q) by ring, Real.rpow_add hrate]
      have hg : Real.Gamma (a - q) ≠ 0 := (Real.Gamma_pos_of_pos haq).ne'
      field_simp [hg]
      ring_nf

/-- The density integration used for the negative chi-square moments in
Section 2.3, in shape/rate coordinates. -/
theorem gamma_negative_moment {a rate q : ℝ} (ha : 0 < a)
    (hrate : 0 < rate) (hq : q < a) :
    (∫⁻ x, ENNReal.ofReal (x ^ (-q)) ∂gammaMeasure a rate) =
      ENNReal.ofReal (rate ^ q * Real.Gamma (a - q) / Real.Gamma a) := by
  unfold gammaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ (by
    exact (measurable_gammaPDFReal a rate).ennreal_ofReal) (by fun_prop)]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (rate ^ q * Real.Gamma (a - q) / Real.Gamma a) *
        gammaPDF (a - q) rate x := by
      apply lintegral_congr_ae
      have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
        rw [ae_iff]
        simp
      filter_upwards [hne] with x hx using gammaPDF_mul_rpow_neg hrate ha hq hx
    _ = _ := by
      have hmeas : Measurable (gammaPDF (a - q) rate) :=
        (measurable_gammaPDFReal (a - q) rate).ennreal_ofReal
      rw [lintegral_const_mul _ hmeas,
        lintegral_gammaPDF_eq_one (sub_pos.mpr hq) hrate, mul_one]

/-- Chi-square as the Gamma law with shape ν/2 and rate 1/2. -/
noncomputable def chiSquareLaw (ν : ℕ) : Measure ℝ := gammaMeasure ((ν : ℝ) / 2) (1 / 2)

/-- The negative-power moment of the chi-square density in the manuscript. -/
theorem chiSquare_negative_moment {ν : ℕ} {q : ℝ} (hq : 0 < q)
    (hq' : q < (ν : ℝ) / 2) :
    (∫⁻ x, ENNReal.ofReal (x ^ (-q)) ∂chiSquareLaw ν) =
      ENNReal.ofReal (2 ^ (-q) * Real.Gamma ((ν : ℝ) / 2 - q) / Real.Gamma ((ν : ℝ) / 2)) := by
  unfold chiSquareLaw
  rw [gamma_negative_moment (hq.trans hq') (by norm_num) hq']
  congr 2
  rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

/-- In particular the inverse moment at ν > 2 is 1/(ν-2). -/
theorem chiSquare_inverse_moment {ν : ℕ} (hν : 2 < ν) :
    (∫⁻ x, ENNReal.ofReal x⁻¹ ∂chiSquareLaw ν) = ENNReal.ofReal (1 / ((ν : ℝ) - 2)) := by
  have hν' : (2 : ℝ) < ν := by exact_mod_cast hν
  have hx : (ν : ℝ) / 2 - 1 ≠ 0 := by linarith
  have hg : Real.Gamma ((ν : ℝ) / 2 - 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have h := chiSquare_negative_moment (ν := ν) (q := 1) (by norm_num) (by linarith)
  simp_rw [Real.rpow_neg_one] at h
  rw [h]
  congr 1
  have hGamma : Real.Gamma ((ν : ℝ) / 2) =
      ((ν : ℝ) / 2 - 1) * Real.Gamma ((ν : ℝ) / 2 - 1) := calc
    _ = Real.Gamma (((ν : ℝ) / 2 - 1) + 1) := congrArg Real.Gamma (by ring)
    _ = _ := Real.Gamma_add_one hx
  rw [hGamma]
  have hν₂ : (ν : ℝ) - 2 ≠ 0 := by linarith
  generalize Real.Gamma ((ν : ℝ) / 2 - 1) = g at hg ⊢
  field_simp [hg, hx, hν₂]

end SketchOrientation
