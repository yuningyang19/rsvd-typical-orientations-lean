import SketchOrientation.GaussianBetaRatio

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A beta random variable takes values strictly between zero and one. -/
theorem ae_beta_mem_Ioo (a b : ℝ) : ∀ᵐ x ∂betaMeasure a b, x ∈ Ioo (0 : ℝ) 1 := by
  rw [ae_iff, betaMeasure]
  change (volume.withDensity (betaPDF a b)) (Ioo (0 : ℝ) 1)ᶜ = 0
  rw [withDensity_apply _ measurableSet_Ioo.compl]
  apply setLIntegral_eq_zero measurableSet_Ioo.compl
  intro x hx
  rw [betaPDF_eq, if_neg (show ¬ (0 < x ∧ x < 1) from hx), ENNReal.ofReal_zero]
  rfl

theorem beta_mul_density_rpow {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haq : 0 < a + q) (x : ℝ) :
    betaPDF a b x * ENNReal.ofReal (x ^ q) =
      ENNReal.ofReal (beta (a + q) b / beta a b) * betaPDF (a + q) b x := by
  by_cases hx : 0 < x ∧ x < 1
  · have hB := beta_pos ha hb
    have hB' := beta_pos haq hb
    have hx' : 0 < 1 - x := sub_pos.mpr hx.2
    have hPos : 0 ≤ (1 / beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1) :=
      mul_nonneg (mul_nonneg (one_div_nonneg.mpr hB.le) (Real.rpow_nonneg hx.1.le _))
        (Real.rpow_nonneg hx'.le _)
    have hPos' : 0 ≤ beta (a + q) b / beta a b := by positivity
    rw [betaPDF_of_pos_lt_one hx.1 hx.2, betaPDF_of_pos_lt_one hx.1 hx.2,
      ← ENNReal.ofReal_mul hPos, ← ENNReal.ofReal_mul hPos']
    congr 1
    rw [show a + q - 1 = (a - 1) + q by ring, Real.rpow_add hx.1]
    field_simp
  · simp [betaPDF_eq, if_neg hx]

/-- Exact positive and negative real beta moments whenever the shifted
shape remains positive. -/
theorem beta_rpow_mean {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haq : 0 < a + q) :
    Integrable (fun x : ℝ => x ^ q) (betaMeasure a b) ∧
      (∫ x, x ^ q ∂betaMeasure a b) = beta (a + q) b / beta a b := by
  have hβ : ∀ a' : ℝ, Measurable (betaPDF a' b) :=
    fun a' => (measurable_betaPDFReal a' b).ennreal_ofReal
  have hm : Measurable (fun x : ℝ => x ^ q) := measurable_id.pow_const _
  have h0 : 0 ≤ᵐ[betaMeasure a b] (fun x : ℝ => x ^ q) :=
    (ae_beta_mem_Ioo a b).mono fun x hx => Real.rpow_nonneg hx.1.le q
  have hL :
      (∫⁻ x, ENNReal.ofReal (x ^ q) ∂betaMeasure a b) =
        ENNReal.ofReal (beta (a + q) b / beta a b) := by
    rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ (hβ a) hm.ennreal_ofReal]
    simp only [Pi.mul_apply]
    simp_rw [beta_mul_density_rpow ha hb haq]
    rw [lintegral_const_mul _ (hβ _), lintegral_betaPDF_eq_one haq hb, mul_one]
  refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal h0, hL]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae h0 hm.aestronglyMeasurable, hL,
      ENNReal.toReal_ofReal (div_nonneg (beta_pos haq hb).le (beta_pos ha hb).le)]

private theorem beta_add_one_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    beta (a + 1) b / beta a b = a / (a + b) := by
  unfold beta
  rw [show a + 1 + b = (a + b) + 1 by ring, Real.Gamma_add_one (add_pos ha hb).ne',
    Real.Gamma_add_one ha.ne']
  have hga := (Real.Gamma_pos_of_pos ha).ne'
  have hgb := (Real.Gamma_pos_of_pos hb).ne'
  have hg := (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  field_simp [hga, hgb, hg]

/-- The first beta moment. -/
theorem beta_mean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun x : ℝ => x) (betaMeasure a b) ∧ (∫ x, x ∂betaMeasure a b) = a / (a + b) := by
  have h := beta_rpow_mean (q := 1) ha hb (by linarith)
  simpa only [Real.rpow_one, beta_add_one_ratio ha hb] using h

/-- The exact inverse beta moment used for the conditioned Schur diagonal. -/
theorem beta_inverse_mean {a b : ℝ} (ha : 1 < a) (hb : 0 < b) :
    Integrable (fun x : ℝ => x⁻¹) (betaMeasure a b) ∧
      (∫ x, x⁻¹ ∂betaMeasure a b) = (a + b - 1) / (a - 1) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := sub_pos.mpr ha
  have h := beta_rpow_mean (q := -1) ha0 hb (by linarith)
  have hRatio := beta_add_one_ratio ha1 hb
  rw [show a - 1 + 1 = a by ring] at hRatio
  have hI : beta (a + -1) b / beta a b = (a + b - 1) / (a - 1) := by
    rw [← inv_div, ← sub_eq_add_neg, hRatio, inv_div]
    ring
  simpa only [Real.rpow_neg_one, hI] using h

/-- All nonnegative integer moments of a Beta variable. -/
theorem beta_nat_moment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m) (betaMeasure a b) ∧
      (∫ x, x ^ m ∂betaMeasure a b) =
        ∏ j ∈ Finset.range m, (a + j) / (a + b + j) := by
  have h : 0 < a + (m : ℝ) := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)
  have hR := beta_rpow_mean (q := (m : ℝ)) ha hb h
  simp_rw [Real.rpow_natCast] at hR
  refine ⟨hR.1, hR.2.trans ?_⟩
  clear hR h
  induction m with
  | zero => simp [(beta_pos ha hb).ne']
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih, Nat.cast_succ]
    have hA : 0 < a + (m : ℝ) := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)
    have hR := beta_add_one_ratio hA hb
    rw [← add_assoc, show a + b + (m : ℝ) = a + (m : ℝ) + b by ring]
    calc
      _ = (beta (a + m + 1) b / beta (a + m) b) * (beta (a + m) b / beta a b) := by
        field_simp [(beta_pos hA hb).ne']
      _ = _ := by rw [hR, mul_comm]

/-- Uniform moment control for ambient-scaled Haar projected lengths at
fixed rank, expressed on their exact beta law. -/
theorem beta_scaled_rank_moment {n k : ℕ} (hk : 0 < k) (hkn : k < n) (m : ℕ) :
    let β := betaMeasure ((k : ℝ) / 2) (((n - k : ℕ) : ℝ) / 2)
    Integrable (fun x : ℝ => ((n : ℝ) * x) ^ m) β ∧
      (∫ x, ((n : ℝ) * x) ^ m ∂β) ≤ ∏ j ∈ Finset.range m, ((k : ℝ) + 2 * j) := by
  intro β
  let a := (k : ℝ) / 2
  let b := ((n - k : ℕ) : ℝ) / 2
  have ha : 0 < a := half_pos (Nat.cast_pos.mpr hk)
  have hb : 0 < b := half_pos (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hkn))
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (hk.trans hkn)
  have he : a + b = (n : ℝ) / 2 := by
    dsimp [a, b]
    rw [Nat.cast_sub hkn.le]
    ring
  have hm := beta_nat_moment ha hb m
  simp_rw [mul_pow]
  refine ⟨hm.1.const_mul _, ?_⟩
  have hp : (∏ _ ∈ Finset.range m, (n : ℝ)) = (n : ℝ) ^ m := by simp
  rw [integral_const_mul, hm.2, he, ← hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hd : 0 < (n : ℝ) / 2 + i := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    dsimp [a]
    nlinarith

end SketchOrientation
