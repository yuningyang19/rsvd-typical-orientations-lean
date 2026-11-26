import SketchOrientation.GaussianChiSquareMeans
import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

private theorem gamma_restrict_pos (a rate : ℝ) :
    (gammaMeasure a rate).restrict (Ioi 0) = gammaMeasure a rate := by
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  change gammaMeasure a rate {x : ℝ | ¬ 0 < x} = 0
  unfold gammaMeasure
  rw [show {x : ℝ | ¬ 0 < x} = Set.Iic 0 by ext x; simp, withDensity_apply _ measurableSet_Iic]
  rw [← restrict_Iio_eq_restrict_Iic]
  exact lintegral_gammaPDF_of_nonpos le_rfl

private theorem measurable_gamma_density (a rate : ℝ) : Measurable (gammaPDF a rate) :=
  (measurable_gammaPDFReal a rate).ennreal_ofReal

private theorem measurable_beta_density (a b : ℝ) : Measurable (betaPDF a b) :=
  (measurable_betaPDFReal a b).ennreal_ofReal

private theorem gamma_density_ratio_change {a b rate q t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < rate) (hq : 0 < q) (ht : 0 < t) (ht' : t < 1) :
    ENNReal.ofReal q * (gammaPDF a rate (q * t) * gammaPDF b rate (q - q * t)) =
      gammaPDF (a + b) rate q * betaPDF a b t := by
  have hu : 0 < 1 - t := sub_pos.mpr ht'
  have hy : q - q * t = q * (1 - t) := by ring
  have he : Real.exp (-(rate * (q * t))) * Real.exp (-(rate * (q * (1 - t)))) =
      Real.exp (-(rate * q)) := by rw [← Real.exp_add]; congr 1; ring
  have hqShape : q ^ (a + b - 1) = q * (q ^ (a - 1) * q ^ (b - 1)) := by
    rw [show a + b - 1 = 1 + ((a - 1) + (b - 1)) by ring,
      Real.rpow_add hq, Real.rpow_add hq, Real.rpow_one]
  rw [hy, gammaPDF_of_nonneg (mul_nonneg hq.le ht.le),
    gammaPDF_of_nonneg (mul_nonneg hq.le hu.le), gammaPDF_of_nonneg hq.le,
    betaPDF_of_pos_lt_one ht ht', ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul hq.le,
    ← ENNReal.ofReal_mul]
  rotate_left
  · have hγ := Real.Gamma_pos_of_pos ha
    positivity
  · have hγ := Real.Gamma_pos_of_pos (add_pos ha hb)
    positivity
  congr 1
  rw [Real.mul_rpow hq.le ht.le, Real.mul_rpow hq.le hu.le, Real.rpow_add hr, hqShape]
  unfold beta
  have hga := (Real.Gamma_pos_of_pos ha).ne'
  have hgb := (Real.Gamma_pos_of_pos hb).ne'
  have hgab := (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  calc
    _ = (rate ^ a * rate ^ b / (Real.Gamma a * Real.Gamma b)) *
        (q * (q ^ (a - 1) * q ^ (b - 1))) *
        (t ^ (a - 1) * (1 - t) ^ (b - 1)) *
        (Real.exp (-(rate * (q * t))) * Real.exp (-(rate * (q * (1 - t))))) := by ring
    _ = _ := by rw [he]; field_simp [hga, hgb, hgab]

private theorem lintegral_pos_sum_ratio (F : ℝ → ℝ → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ x in Ioi 0, ∫⁻ y in Ioi 0, F x y) =
      ∫⁻ q in Ioi 0, ∫⁻ t in Ioo 0 1, ENNReal.ofReal q * F (q * t) (q - q * t) := by
  have htranslate (x : ℝ) :
      (∫⁻ y in Ioi (0 : ℝ), F x y) = ∫⁻ q in Ioi x, F x (q - x) := by
    have hImage : (fun q : ℝ => q - x) '' Ioi x = Ioi 0 := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact sub_pos.mpr (show x < q from hq)
      · intro hy
        exact ⟨y + x, by exact lt_add_of_pos_left x hy, add_sub_cancel_right _ _⟩
    rw [← hImage]
    simpa only [abs_one, ENNReal.ofReal_one, one_mul] using
      lintegral_image_eq_lintegral_abs_deriv_mul (f := fun q : ℝ => q - x) (f' := fun _ => 1)
        measurableSet_Ioi (fun q _ => ((hasDerivAt_id q).sub_const x).hasDerivWithinAt)
        (fun q _ r _ h => by change q - x = r - x at h; linarith) (F x)
  let H := fun x q : ℝ => if 0 < x ∧ x < q then F x (q - x) else 0
  have hH : Measurable (Function.uncurry H) := by
    change Measurable (fun p : ℝ × ℝ => if 0 < p.1 ∧ p.1 < p.2 then F p.1 (p.2 - p.1) else 0)
    have hm := hF.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst))
    exact Measurable.piecewise ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)) hm measurable_const
  have h1 :
      (∫⁻ x in Ioi 0, ∫⁻ q in Ioi x, F x (q - x)) = ∫⁻ x, ∫⁻ q, H x q := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), ← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro q
      by_cases hq : x < q
      · rw [indicator_of_mem (show q ∈ Ioi x from hq)]
        simp [H, hx, hq]
      · rw [indicator_of_notMem (show q ∉ Ioi x from hq)]
        simp [H, hx, hq]
    · rw [indicator_of_notMem (show x ∉ Ioi 0 from hx)]
      simp [H, hx]
  have h2 : (∫⁻ q, ∫⁻ x, H x q) = ∫⁻ q in Ioi 0, ∫⁻ x in Ioo 0 q, F x (q - x) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro q
    by_cases hq : 0 < q
    · rw [indicator_of_mem (show q ∈ Ioi (0 : ℝ) from hq), ← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro x
      by_cases hx : 0 < x ∧ x < q
      · rw [indicator_of_mem (show x ∈ Ioo (0 : ℝ) q from hx), show H x q = _ from if_pos hx]
      · rw [indicator_of_notMem (show x ∉ Ioo 0 q from hx), show H x q = _ from if_neg hx]
    · rw [indicator_of_notMem (show q ∉ Ioi 0 from hq)]
      have hzero (x : ℝ) : ¬(0 < x ∧ x < q) := fun hx => hq (hx.1.trans hx.2)
      simp [H, hzero]
  have hscale (q : ℝ) (hq : 0 < q) :
      (∫⁻ x in Ioo 0 q, F x (q - x)) =
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal q * F (q * t) (q - q * t) := by
    have hImage : (fun t : ℝ => q * t) '' Ioo 0 1 = Ioo 0 q := by
      ext x
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨mul_pos hq ht.1, by simpa using mul_lt_mul_of_pos_left ht.2 hq⟩
      · intro hx
        exact ⟨x / q, ⟨div_pos hx.1 hq, (div_lt_one hq).2 hx.2⟩, mul_div_cancel₀ _ hq.ne'⟩
    rw [← hImage]
    simpa only [abs_of_pos hq] using
      lintegral_image_eq_lintegral_abs_deriv_mul (f := fun t : ℝ => q * t) (f' := fun _ => q)
        measurableSet_Ioo (fun t _ => by simpa using ((hasDerivAt_id t).const_mul q).hasDerivWithinAt)
        (fun t _ u _ e => mul_left_cancel₀ hq.ne' e) (fun x => F x (q - x))
  calc
    _ = ∫⁻ x in Ioi 0, ∫⁻ q in Ioi x, F x (q - x) := by simp_rw [htranslate]
    _ = ∫⁻ x, ∫⁻ q, H x q := h1
    _ = ∫⁻ q, ∫⁻ x, H x q := lintegral_lintegral_swap hH.aemeasurable
    _ = ∫⁻ q in Ioi 0, ∫⁻ x in Ioo 0 q, F x (q - x) := h2
    _ = _ := lintegral_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono fun q hq => hscale q hq)

/-- The first proportion of independent equal-rate Gamma draws is Beta. -/
theorem gamma_ratio_law {a b rate : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < rate) :
    ((gammaMeasure a rate).prod (gammaMeasure b rate)).map (fun p => p.1 / (p.1 + p.2)) =
      betaMeasure a b := by
  let G := fun p : ℝ × ℝ => p.1 / (p.1 + p.2)
  have hG : Measurable G := measurable_fst.div (measurable_fst.add measurable_snd)
  apply Measure.ext_of_lintegral
  intro φ hφ
  let F := fun x y : ℝ => gammaPDF a rate x * gammaPDF b rate y * φ (G (x, y))
  have hFa := measurable_gamma_density a rate
  have hFb := measurable_gamma_density b rate
  have hFs := measurable_gamma_density (a + b) rate
  have hβ := measurable_beta_density a b
  have hF : Measurable (Function.uncurry F) :=
    ((hFa.comp measurable_fst).mul (hFb.comp measurable_snd)).mul (hφ.comp hG)
  have hγ (s : ℝ) :
      gammaMeasure s rate = (volume.restrict (Ioi 0)).withDensity (gammaPDF s rate) := by
    rw [← gamma_restrict_pos s rate, gammaMeasure, restrict_withDensity measurableSet_Ioi]
  have hD : Measurable (fun z : ℝ × ℝ => gammaPDF a rate z.1 * gammaPDF b rate z.2) :=
    (hFa.comp measurable_fst).mul (hFb.comp measurable_snd)
  have hφG : Measurable (fun z => φ (G z)) := hφ.comp hG
  rw [lintegral_map hφ hG, hγ a, hγ b, prod_withDensity hFa hFb,
    lintegral_withDensity_eq_lintegral_mul _ hD hφG]
  change (∫⁻ z : ℝ × ℝ, Function.uncurry F z
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) = _
  rw [lintegral_prod _ hF.aemeasurable]
  change (∫⁻ x in Ioi 0, ∫⁻ y in Ioi 0, F x y) = _
  rw [lintegral_pos_sum_ratio F hF]
  have hT :
      (∫⁻ q in Ioi 0, ∫⁻ t in Ioo 0 1, ENNReal.ofReal q * F (q * t) (q - q * t)) =
        ∫⁻ q in Ioi 0, ∫⁻ t in Ioo 0 1, gammaPDF (a + b) rate q * (betaPDF a b t * φ t) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hq' : 0 < q := hq
    have he : G (q * t, q - q * t) = t := by
      change q * t / (q * t + (q - q * t)) = t
      rw [show q * t + (q - q * t) = q by ring, mul_comm, mul_div_cancel_right₀ _ hq'.ne']
    dsimp only [F]
    rw [he, ← mul_assoc, gamma_density_ratio_change ha hb hr hq' ht.1 ht.2, mul_assoc]
  rw [hT]
  have hM : Measurable (fun t => betaPDF a b t * φ t) := hβ.mul hφ
  have hQ (q : ℝ) :
      (∫⁻ t in Ioo 0 1, gammaPDF (a + b) rate q * (betaPDF a b t * φ t)) =
        gammaPDF (a + b) rate q * ∫⁻ t in Ioo 0 1, betaPDF a b t * φ t :=
    lintegral_const_mul _ hM
  simp_rw [hQ]
  rw [lintegral_mul_const _ hFs]
  have hmass : (∫⁻ q in Ioi 0, gammaPDF (a + b) rate q) = 1 := by
    rw [← withDensity_apply _ measurableSet_Ioi, ← gammaMeasure]
    have h := congrArg (fun μ : Measure ℝ => μ univ) (gamma_restrict_pos (a + b) rate)
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at h
    rw [h]
    simp [gammaMeasure, lintegral_gammaPDF_eq_one (add_pos ha hb) hr]
  rw [hmass, one_mul, betaMeasure, lintegral_withDensity_eq_lintegral_mul _ hβ hφ,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro t
  rw [Pi.mul_apply]
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem ht]
  · rw [indicator_of_notMem ht, betaPDF_eq, if_neg (show ¬ (0 < t ∧ t < 1) from ht),
      ENNReal.ofReal_zero, zero_mul]

end SketchOrientation
