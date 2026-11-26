import SketchOrientation.GaussianOrientationScore
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

namespace SketchOrientation

open MeasureTheory Matrix

variable {n k ℓ : ℕ}

/-- The infinite-gap conditional mean, expressed by the inverse trace on
the Haar frame. -/
noncomputable def haarOrientationEndpoint (ν : Measure (OrthogonalProjector n ℓ))
    (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ((∫ P, gaussianOrientationScore P V ∂ν) - (ℓ : ℝ) / k) / ((n : ℝ) - k)

/-- The Haar benchmark in the normalization of Theorem 1.1. -/
noncomputable def haarOrientationBenchmark (n k ℓ : ℕ) : ℝ :=
  (((n : ℝ) - k - 1) * (1 / ((ℓ : ℝ) - k - 1)) - (ℓ : ℝ) / k) / ((n : ℝ) - k)

/-- The benchmark agrees with `(m_H - 1) / k` in Equation (1.1). -/
theorem haarOrientationBenchmark_eq_paper {p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (hn : k + p ≤ n) :
    haarOrientationBenchmark n k (k + p) =
      ((((n : ℝ) - (k + p : ℕ)) / ((n : ℝ) - k)) *
        (1 + (k : ℝ) / ((p : ℝ) - 1)) - 1) / (k : ℝ) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hp' : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr
    (by exact_mod_cast (show p ≠ 1 by omega))
  have hn' : (n : ℝ) - k ≠ 0 := sub_ne_zero.mpr
    (by exact_mod_cast (show n ≠ k by omega))
  unfold haarOrientationBenchmark
  push_cast
  rw [add_sub_cancel_left]
  field_simp [hk', hp', hn']; ring

theorem measurable_haarOrientationEndpoint (ν : Measure (OrthogonalProjector n ℓ))
    [IsProbabilityMeasure ν] : Measurable (haarOrientationEndpoint (k := k) ν) := by
  exact (measurable_gaussianOrientationScore.stronglyMeasurable.integral_prod_left.measurable.sub
    measurable_const).div_const _

theorem integrable_gaussianOrientationScore_prod (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] :
    Integrable (Function.uncurry (@gaussianOrientationScore n k ℓ)) (ν.prod (gaussianMatrixLaw n k)) :=
  (integrable_gaussianProjectedInverseTrace_comp hℓn hkℓ ν Subtype.val measurable_subtype_coe
    (ae_of_all _ fun P => P.property)).div_const _

set_option maxHeartbeats 1000000 in
/-- Radial conditioning commutes with the mean over the independent sketch. -/
theorem gaussianOrientationMean_condExp (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] :
    let μ := gaussianMatrixLaw n k
    μ[(fun G => ∫ P, gaussianOrientationScore P G ∂ν) |
      MeasurableSpace.comap gaussianPolarFrame inferInstance] =ᵐ[μ]
      (fun G =>
        (∫ P, gaussianOrientationScore P (gaussianPolarFrame G) ∂ν) / ((n : ℝ) - k - 1)) := by
  let μ := gaussianMatrixLaw n k
  let X := @gaussianPolarFrame n k
  let f := gaussianProjectedInverseTrace ∘ (Prod.map (@Subtype.val _ _) id :
    OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ → _)
  let g := fun z : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ =>
    gaussianProjectedInverseTrace (z.1.val, z.2) / ((n : ℝ) - k - 1)
  have hg : Measurable g := (measurable_gaussianProjectedInverseTrace.comp
    (measurable_subtype_coe.prodMap measurable_id)).div_const _
  have hf : Integrable f (ν.prod μ) :=
    integrable_gaussianProjectedInverseTrace_comp hℓn hkℓ ν Subtype.val measurable_subtype_coe
      (ae_of_all _ fun P => P.property)
  have hj := gaussianPolar_projectedInverseTrace_condExp_comp hℓn hkℓ ν Subtype.val
    measurable_subtype_coe (ae_of_all _ fun P => P.property)
  have h := condExp_integral_prod_left ν μ X measurable_gaussianPolarFrame f g hg hf hj
  let F := fun G => ∫ P, f (P, G) ∂ν
  have he : (fun G => ∫ P, gaussianOrientationScore P G ∂ν) = (k : ℝ)⁻¹ • F := by
    funext G
    change (∫ P, f (P, G) / (k : ℝ) ∂ν) = (k : ℝ)⁻¹ * F G
    rw [integral_div]
    dsimp [F]
    ring
  change μ[(fun G => ∫ P, gaussianOrientationScore P G ∂ν) | MeasurableSpace.comap X inferInstance] =ᵐ[μ] _
  rw [he]
  refine (condExp_smul (m := MeasurableSpace.comap X inferInstance) ((k : ℝ)⁻¹) F).trans ?_
  filter_upwards [h] with G hG
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hG]
  change (k : ℝ)⁻¹ * (∫ P, f (P, X G) / ((n : ℝ) - k - 1) ∂ν) =
    (∫ P, f (P, X G) / (k : ℝ) ∂ν) / ((n : ℝ) - k - 1)
  rw [integral_div, integral_div]
  ring

set_option maxHeartbeats 1000000 in
/-- The finite-dimensional endpoint estimate in Theorem 1.1. -/
theorem haarOrientationEndpoint_centered_bound (hℓn : ℓ ≤ n) (hk : 0 < k)
    (hkℓ : k + 1 < ℓ) (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 1 < r) (hr₂ : r ≤ 2) (hr' : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2) :
    (∫ V, |haarOrientationEndpoint ν V - haarOrientationBenchmark n k ℓ|
      ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤
      (((n : ℝ) - k - 1) / ((n : ℝ) - k)) *
        (3 * gaussianOrientationMomentConstant (ℓ - k) r *
          meanProjectedEnergy ν orientationRowSpace ^ (1 - 1 / r)) := by
  let μ := gaussianMatrixLaw n k
  let X := @gaussianPolarFrame n k
  let A := fun G : Matrix (Fin n) (Fin k) ℝ => ∫ P, gaussianOrientationScore P G ∂ν
  let a := (1 : ℝ) / ((ℓ : ℝ) - k - 1)
  let A₀ := fun G => A G - a
  let b := (n : ℝ) - k - 1
  let c := (n : ℝ) - k
  have hb : 0 < b := by
    have hn : (k : ℝ) + 1 < n := by exact_mod_cast (show k + 1 < n by omega)
    dsimp [b]
    linarith
  have hc : 0 < c := by dsimp [b, c] at *; linarith
  have hInt : Integrable A μ := (integrable_gaussianOrientationScore_prod hℓn hkℓ ν).integral_prod_right
  have h := gaussianOrientationMean_condExp (k := k) hℓn hkℓ ν
  have hHaar : Measurable (fun V : Matrix (Fin n) (Fin k) ℝ =>
      |haarOrientationEndpoint ν V - haarOrientationBenchmark n k ℓ|) :=
    (measurable_haarOrientationEndpoint ν |>.sub measurable_const).abs
  have hsub := condExp_sub hInt (integrable_const (μ := μ) a) (MeasurableSpace.comap X inferInstance)
  have hconst : μ[(fun _ => a) | MeasurableSpace.comap X inferInstance] = fun _ => a :=
    condExp_const measurable_gaussianPolarFrame.comap_le _
  have hAA : A - (fun _ => a) = A₀ := rfl
  rw [hconst, hAA] at hsub
  have hPoint : (fun G => |haarOrientationEndpoint ν (X G) - haarOrientationBenchmark n k ℓ|)
      =ᵐ[μ] fun G => (b / c) * ‖μ[A₀ | MeasurableSpace.comap X inferInstance] G‖ := by
    filter_upwards [h, hsub] with G hG hg
    rw [hg]
    change |(A (X G) - (ℓ : ℝ) / k) / c -
      (b * a - (ℓ : ℝ) / k) / c| = (b / c) * |μ[A | MeasurableSpace.comap X inferInstance] G - a|
    change μ[A | MeasurableSpace.comap X inferInstance] G = A (X G) / b at hG
    rw [hG, ← abs_of_pos (div_pos hb hc), ← abs_mul]
    congr 1
    field_simp [hb.ne', hc.ne']; ring
  rw [← gaussianPolarFrameLaw_eq_haar (show k ≤ n by omega),
    integral_map measurable_gaussianPolarFrame.aemeasurable hHaar.aestronglyMeasurable,
    integral_congr_ae hPoint, integral_const_mul]
  calc
    _ ≤ (b / c) * (∫ G, ‖A₀ G‖ ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_norm_condExp_le (m := MeasurableSpace.comap X inferInstance) _) (div_nonneg hb.le hc.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (gaussianOrientationScore_centered_bound hℓn hk hkℓ ν hr hr₂ hr')
        (div_nonneg hb.le hc.le)

set_option maxHeartbeats 800000 in
/-- For every sketch law, the exact mean of the endpoint is the Haar benchmark. -/
theorem haarOrientationEndpoint_mean (hℓn : ℓ ≤ n) (hk : 0 < k) (hkℓ : k + 1 < ℓ)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] :
    Integrable (haarOrientationEndpoint (k := k) ν) (gaussianHaarFrameLaw (show k ≤ n by omega)) ∧
      (∫ V, haarOrientationEndpoint ν V ∂gaussianHaarFrameLaw (show k ≤ n by omega)) =
        haarOrientationBenchmark n k ℓ := by
  let μ := gaussianMatrixLaw n k
  let η := gaussianHaarFrameLaw (show k ≤ n by omega)
  let X := @gaussianPolarFrame n k
  let A := fun G : Matrix (Fin n) (Fin k) ℝ => ∫ P, gaussianOrientationScore P G ∂ν
  let b := (n : ℝ) - k - 1
  let c := (n : ℝ) - k
  let a := (1 : ℝ) / ((ℓ : ℝ) - k - 1)
  have hb : 0 < b := by
    have hn : (k : ℝ) + 1 < n := by exact_mod_cast (show k + 1 < n by omega)
    dsimp [b]
    linarith
  have hX : Measurable X := measurable_gaussianPolarFrame
  have hXm : μ.map X = η := gaussianPolarFrameLaw_eq_haar _
  have hA : Measurable A :=
    (@measurable_gaussianOrientationScore n k ℓ).stronglyMeasurable.integral_prod_left.measurable
  have hInt := integrable_gaussianOrientationScore_prod (k := k) hℓn hkℓ ν
  have hMean : (∫ G, A G ∂μ) = a := by
    change (∫ G, ∫ P, gaussianOrientationScore P G ∂ν ∂μ) = _
    rw [← integral_integral_swap hInt]
    simp_rw [fun P => (gaussianOrientationScore_mean (k := k) hℓn hk hkℓ P).2, integral_const]
    simp [a]
  have hCond := gaussianOrientationMean_condExp (k := k) hℓn hkℓ ν
  have hV : A ∘ X =ᵐ[μ] fun G =>
      b * μ[A | MeasurableSpace.comap X inferInstance] G := by
    filter_upwards [hCond] with G hG
    change μ[A | MeasurableSpace.comap X inferInstance] G = A (X G) / b at hG
    rw [Function.comp_apply, hG]
    field_simp
  have hI : Integrable A η := by
    rw [← hXm, integrable_map_measure hA.aestronglyMeasurable hX.aemeasurable]
    exact (integrable_condExp.const_mul b).congr hV.symm
  have he : (∫ G, A G ∂η) = b * a := by
    rw [← hXm, integral_map hX.aemeasurable hA.aestronglyMeasurable]
    change (∫ G, (A ∘ X) G ∂μ) = _
    rw [integral_congr_ae hV, integral_const_mul, integral_condExp hX.comap_le, hMean]
  change Integrable (fun V => (A V - (ℓ : ℝ) / k) / c) η ∧
    (∫ V, (A V - (ℓ : ℝ) / k) / c ∂η) = (b * a - (ℓ : ℝ) / k) / c
  refine ⟨(hI.sub (integrable_const _)).div_const _, ?_⟩
  rw [integral_div, integral_sub hI (integrable_const _), he, integral_const, probReal_univ, one_smul]

end SketchOrientation
