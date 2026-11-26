import SketchOrientation.GaussianOrientationGapAlgebra
import SketchOrientation.GaussianOrientationHaarMoments

namespace SketchOrientation

open MeasureTheory Matrix Filter
open scoped Topology

variable {n k ℓ : ℕ}

/-- A measurable spectral extension of the actual finite two-level loss. -/
noncomputable def orientationFiniteLoss (Γ : ℝ) (P : OrthogonalProjector n ℓ)
    (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  (Γ * ((1 + (Γ - 1) • (Vᵀ * P.val * V))⁻¹).trace - (ℓ : ℝ)) /
    ((k : ℝ) * ((n : ℝ) - k))

theorem orientationFiniteLoss_eq_actual (hk : 0 < k) (hkn : k < n)
    (Γ : ℝ) (hΓ : 1 ≤ Γ) (P : OrthogonalProjector n ℓ)
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    orientationFiniteLoss Γ P V = projectorTwoLevelLoss V P Γ := by
  rw [orientationFiniteLoss, projectorTwoLevelLoss_eq_angles V hV P hΓ hk hkn,
    trace_inverse_one_add_smul_of_posSemidef (targetCompression_posSemidef V P)
      _ (sub_nonneg.mpr hΓ), Finset.mul_sum]
  simp only [div_eq_mul_inv]

theorem measurable_orientationFiniteLoss (Γ : ℝ) :
    Measurable (Function.uncurry (@orientationFiniteLoss n k ℓ Γ)) := by
  let C := fun z : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ =>
    z.2ᵀ * z.1.val * z.2
  have hC : Measurable C := measurable_matrix_product
    (measurable_matrix_product (measurable_matrix_transpose measurable_snd)
      (measurable_subtype_coe.comp measurable_fst)) measurable_snd
  have hTm : Continuous (fun A : Matrix (Fin k) (Fin k) ℝ =>
      (1 : Matrix (Fin k) (Fin k) ℝ) + (Γ - 1) • A) := by
    apply continuous_matrix
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact continuous_const.add (continuous_const.mul (continuous_id.matrix_elem i j))
  have hT := hTm.measurable.comp hC
  have hI := measurable_matrix_trace.comp (measurable_matrix_nonsing_inv.comp hT)
  exact (hI.const_mul Γ |>.sub measurable_const).div_const _

private theorem orientationFiniteLoss_abs_le (Γ : ℝ) (hΓ : 1 ≤ Γ)
    (P : OrthogonalProjector n ℓ) (V : Matrix (Fin n) (Fin k) ℝ) :
    |orientationFiniteLoss Γ P V| ≤ (Γ * k + ℓ) / |(k : ℝ) * ((n : ℝ) - k)| := by
  let d := (k : ℝ) * ((n : ℝ) - k)
  let t := orientationPrincipalCosines V P
  have ht (i : Fin k) : 1 ≤ 1 + (Γ - 1) * t i :=
    le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hΓ)
      (orientationPrincipalCosines_nonneg V P i))
  have h0 (i : Fin k) : 0 ≤ Γ / (1 + (Γ - 1) * t i) :=
    div_nonneg (zero_le_one.trans hΓ) (zero_le_one.trans (ht i))
  have h1 (i : Fin k) : Γ / (1 + (Γ - 1) * t i) ≤ Γ := by
    exact div_le_self (zero_le_one.trans hΓ) (ht i)
  rw [orientationFiniteLoss,
    trace_inverse_one_add_smul_of_posSemidef (targetCompression_posSemidef V P)
      _ (sub_nonneg.mpr hΓ), Finset.mul_sum, abs_div]
  change |(∑ i, Γ / (1 + (Γ - 1) * t i)) - ℓ| / |d| ≤ (Γ * k + ℓ) / |d|
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  have hleft : 0 ≤ ∑ i, Γ / (1 + (Γ - 1) * t i) :=
    Finset.sum_nonneg fun i _ => h0 i
  have hright : (∑ i, Γ / (1 + (Γ - 1) * t i)) ≤ Γ * k := by
    calc
      _ ≤ ∑ _ : Fin k, Γ := Finset.sum_le_sum fun i _ => h1 i
      _ = _ := by simp [mul_comm]
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) ℓ]

private theorem integrable_orientationFiniteLoss {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Γ : ℝ) (hΓ : 1 ≤ Γ)
    (X : Ω → OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ) (hX : Measurable X) :
    Integrable (Function.uncurry (orientationFiniteLoss Γ) ∘ X) μ := by
  refine (integrable_const ((Γ * k + ℓ) / |(k : ℝ) * ((n : ℝ) - k)|)).mono'
    (((@measurable_orientationFiniteLoss n k ℓ Γ).comp hX).aestronglyMeasurable) ?_
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, Function.comp_apply, Function.uncurry_def] using
    (orientationFiniteLoss_abs_le Γ hΓ (X x).1 (X x).2)

/-- The conditional mean of the actual RSVD loss at a finite gap. -/
noncomputable def haarOrientationFiniteMean (ν : Measure (OrthogonalProjector n ℓ))
    (Γ : ℝ) (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ∫ P, projectorTwoLevelLoss V P Γ ∂ν

private noncomputable def haarOrientationFiniteMeanExtension
    (ν : Measure (OrthogonalProjector n ℓ)) (Γ : ℝ) (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ∫ P, orientationFiniteLoss Γ P V ∂ν

private theorem haarOrientationFiniteMean_eq_extension (ν : Measure (OrthogonalProjector n ℓ))
    (hk : 0 < k) (hkn : k < n)
    (Γ : ℝ) (hΓ : 1 ≤ Γ) (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    haarOrientationFiniteMean ν Γ V = haarOrientationFiniteMeanExtension ν Γ V := by
  simp_rw [haarOrientationFiniteMean, haarOrientationFiniteMeanExtension,
    orientationFiniteLoss_eq_actual hk hkn Γ hΓ _ V hV]

private theorem integrable_orientationFiniteLoss_sect (ν : Measure (OrthogonalProjector n ℓ))
    [IsProbabilityMeasure ν] (Γ : ℝ) (hΓ : 1 ≤ Γ) (V : Matrix (Fin n) (Fin k) ℝ) :
    Integrable (fun P => orientationFiniteLoss Γ P V) ν := by
  exact integrable_orientationFiniteLoss ν Γ hΓ (fun P => (P, V))
    (measurable_id.prodMk measurable_const)

private theorem integrable_projectorTwoLevelLoss_sect (ν : Measure (OrthogonalProjector n ℓ))
    [IsProbabilityMeasure ν] (hk : 0 < k) (hkn : k < n)
    (Γ : ℝ) (hΓ : 1 ≤ Γ) (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    Integrable (fun P => projectorTwoLevelLoss V P Γ) ν := by
  simpa only [orientationFiniteLoss_eq_actual hk hkn Γ hΓ _ V hV] using
    integrable_orientationFiniteLoss_sect ν Γ hΓ V

theorem haarOrientationFiniteMean_monotone (ν : Measure (OrthogonalProjector n ℓ))
    [IsProbabilityMeasure ν] (hk : 0 < k) (hkn : k < n)
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    MonotoneOn (fun Γ => haarOrientationFiniteMean ν Γ V) (Set.Ici 1) := by
  intro Γ₀ h₀ Γ₁ h₁ hΓ
  apply integral_mono (integrable_projectorTwoLevelLoss_sect ν hk hkn Γ₀ h₀ V hV)
    (integrable_projectorTwoLevelLoss_sect ν hk hkn Γ₁ h₁ V hV)
  exact fun P => projectorTwoLevelLoss_monotone hk hkn V hV P h₀ h₁ hΓ

theorem integrable_projectorOrientationEndpoint_prod (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (hk : 0 < k) (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] :
    Integrable (fun z => projectorOrientationEndpoint z.2 z.1)
      (ν.prod (gaussianHaarFrameLaw (show k ≤ n by omega))) := by
  let c := (n : ℝ) - k
  have hi : Integrable (Function.uncurry (@gaussianOrientationScore n k ℓ))
      (ν.prod (gaussianHaarFrameLaw (show k ≤ n by omega))) := by
    have hr' : (1 : ℝ) < ((ℓ - k + 1 : ℕ) : ℝ) / 2 := by
      have hm : 2 < ℓ - k + 1 := by omega
      have hm' : (2 : ℝ) < ((ℓ - k + 1 : ℕ) : ℝ) := by exact_mod_cast hm
      linarith
    have h := (haarOrientationScore_moment_prod hℓn hk hkℓ ν le_rfl hr').1
    simpa only [Function.uncurry_def, Real.rpow_one] using h
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : (fun z : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ =>
      projectorOrientationEndpoint z.2 z.1) =
      (fun z => (gaussianOrientationScore z.1 z.2 - (ℓ : ℝ) / k) / c) := by
    funext z
    unfold projectorOrientationEndpoint gaussianOrientationScore gaussianProjectedInverseTrace c
    rw [← sub_div, div_div]
  rw [he]
  exact (hi.sub (integrable_const _)).div_const _

theorem ae_haarOrientationEndpoint_eq_mean (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ) (hk : 0 < k)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] :
    haarOrientationEndpoint ν =ᵐ[gaussianHaarFrameLaw (show k ≤ n by omega)]
      (fun V => ∫ P, projectorOrientationEndpoint V P ∂ν) := by
  have hEnd := (integrable_projectorOrientationEndpoint_prod hℓn hkℓ hk ν).prod_left_ae
  have hc : (n : ℝ) - k ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast (show n ≠ k by omega))
  have he (P : OrthogonalProjector n ℓ) (V : Matrix (Fin n) (Fin k) ℝ) :
      projectorOrientationEndpoint V P =
        (gaussianOrientationScore P V - (ℓ : ℝ) / k) / ((n : ℝ) - k) := by
    unfold projectorOrientationEndpoint gaussianOrientationScore gaussianProjectedInverseTrace
    rw [← sub_div, div_div]
  filter_upwards [hEnd] with V hV
  simp_rw [he] at hV
  have hI : Integrable (fun P => gaussianOrientationScore P V - (ℓ : ℝ) / k) ν := by
    have hP := hV.const_mul ((n : ℝ) - k)
    apply hP.congr
    filter_upwards [] with P
    field_simp
  have hY := hI.add (integrable_const ((ℓ : ℝ) / k) (μ := ν))
  have hY' : Integrable (fun P => gaussianOrientationScore P V) ν := by
    simpa only [Pi.add_def, sub_add_cancel] using hY
  simp_rw [haarOrientationEndpoint, he, integral_div, integral_sub hY' (integrable_const _),
    integral_const, probReal_univ, one_smul]

private theorem ae_haarOrientation_good (hℓn : ℓ ≤ n) (hkℓ : k ≤ ℓ)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] :
    ∀ᵐ V ∂gaussianHaarFrameLaw (hkℓ.trans hℓn),
      Vᵀ * V = 1 ∧ ∀ᵐ P ∂ν, (Vᵀ * P.val * V).det ≠ 0 := by
  let η := gaussianHaarFrameLaw (hkℓ.trans hℓn)
  have hC : Measurable (fun z : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ =>
        z.2ᵀ * z.1.val * z.2) :=
    measurable_matrix_product (measurable_matrix_product (measurable_matrix_transpose measurable_snd)
      (measurable_subtype_coe.comp measurable_fst)) measurable_snd
  have hd : MeasurableSet {z : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ |
      (z.2ᵀ * z.1.val * z.2).det ≠ 0} :=
    (isOpen_ne (x := (0 : ℝ))).measurableSet.preimage (continuous_id.matrix_det.measurable.comp hC)
  have h : ∀ᵐ z ∂ν.prod η, (z.2ᵀ * z.1.val * z.2).det ≠ 0 :=
    (Measure.ae_prod_iff_ae_ae hd).2 (ae_of_all _ fun P => ae_gaussianHaarFrame_projectedGram_invertible hℓn hkℓ P)
  filter_upwards [ae_gaussianHaarFrame_orthonormal (hkℓ.trans hℓn),
    (Measure.ae_ae_comm hd).1 ((Measure.ae_prod_iff_ae_ae hd).1 h)] with V hV hD
  exact ⟨hV, hD⟩

set_option maxHeartbeats 900000 in
/-- A common full-measure set supports the gap estimate for every real
finite gap, under any probability law on the sketch projectors. -/
theorem ae_haarOrientationGap_bound (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ) (hk : 0 < k)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 1 < r) (hr₂ : r ≤ 2) (hr' : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2) :
    ∀ᵐ V ∂gaussianHaarFrameLaw (show k ≤ n by omega),
      ∀ Γ : ℝ, 1 < Γ →
        0 ≤ haarOrientationEndpoint ν V - haarOrientationFiniteMean ν Γ V ∧
        haarOrientationEndpoint ν V - haarOrientationFiniteMean ν Γ V ≤
          ((Γ - 1) ^ (1 - r) * (k : ℝ) ^ r / ((k : ℝ) * ((n : ℝ) - k))) *
            ∫ P, gaussianOrientationScore P V ^ r ∂ν := by
  have hkℓ' : k ≤ ℓ := by omega
  have hkn : k < n := by omega
  have hEnd := integrable_projectorOrientationEndpoint_prod hℓn hkℓ hk ν
  have hM := (haarOrientationScore_moment_prod hℓn hk hkℓ ν hr.le hr').1
  filter_upwards [ae_haarOrientation_good hℓn hkℓ' ν, hEnd.prod_left_ae,
    hM.prod_left_ae, ae_haarOrientationEndpoint_eq_mean hℓn hkℓ hk ν] with V hV hE hM hEQ
  intro Γ hΓ
  have hF := integrable_projectorTwoLevelLoss_sect ν hk hkn Γ hΓ.le V hV.1
  let C := (Γ - 1) ^ (1 - r) * (k : ℝ) ^ r / ((k : ℝ) * ((n : ℝ) - k))
  have h0 : ∀ᵐ P ∂ν, 0 ≤ projectorOrientationEndpoint V P - projectorTwoLevelLoss V P Γ := by
    filter_upwards [hV.2] with P hP
    exact (projectorOrientationGap_bound hk hkn V hV.1 P hP hΓ hr hr₂).1
  have hle : ∀ᵐ P ∂ν, projectorOrientationEndpoint V P - projectorTwoLevelLoss V P Γ ≤
      C * gaussianOrientationScore P V ^ r := by
    filter_upwards [hV.2] with P hP
    have h := (projectorOrientationGap_bound hk hkn V hV.1 P hP hΓ hr hr₂).2
    refine h.trans_eq ?_
    have hTr : (Vᵀ * P.val * V)⁻¹.trace = (k : ℝ) * gaussianOrientationScore P V := by
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      unfold gaussianOrientationScore gaussianProjectedInverseTrace
      change _ = (k : ℝ) * ((Vᵀ * P.val * V)⁻¹.trace / k)
      field_simp
    rw [hTr, Real.mul_rpow (Nat.cast_nonneg _) (gaussianOrientationScore_nonneg _ _)]
    unfold C
    ring
  rw [hEQ, haarOrientationFiniteMean, ← integral_sub hE hF, ← integral_const_mul]
  exact ⟨integral_nonneg_of_ae h0, integral_mono_ae (hE.sub hF) (hM.const_mul C) hle⟩

theorem integrable_haarOrientationFiniteMean (hk : 0 < k) (hkn : k < n)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] {Γ : ℝ} (hΓ : 1 ≤ Γ) :
    Integrable (haarOrientationFiniteMean ν Γ) (gaussianHaarFrameLaw hkn.le) := by
  let η := gaussianHaarFrameLaw hkn.le
  have hI : Integrable (haarOrientationFiniteMeanExtension ν Γ) η :=
    (integrable_orientationFiniteLoss (ν.prod η) Γ hΓ id measurable_id).integral_prod_right
  refine hI.congr ?_
  filter_upwards [ae_gaussianHaarFrame_orthonormal hkn.le] with V hV
  exact (haarOrientationFiniteMean_eq_extension ν hk hkn Γ hΓ V hV).symm

/-- The computed endpoint is the almost-sure limit of the true finite-gap means. -/
theorem ae_haarOrientationFiniteMean_tendsto_endpoint (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (hk : 0 < k) (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] :
    ∀ᵐ V ∂gaussianHaarFrameLaw (show k ≤ n by omega),
      Tendsto (fun Γ => haarOrientationFiniteMean ν Γ V) atTop (𝓝 (haarOrientationEndpoint ν V)) := by
  let r : ℝ := 5 / 4
  have hr : 1 < r := by norm_num [r]
  have hr₂ : r ≤ 2 := by norm_num [r]
  have hr' : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2 := by
    have h : 3 ≤ ℓ - k + 1 := by omega
    have h' : (3 : ℝ) ≤ ((ℓ - k + 1 : ℕ) : ℝ) := by exact_mod_cast h
    dsimp [r]
    linarith
  filter_upwards [ae_haarOrientationGap_bound hℓn hkℓ hk ν hr hr₂ hr'] with V hV
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hΓ : ∀ᶠ Γ : ℝ in atTop, 1 < Γ := eventually_gt_atTop 1
  have ht : Tendsto (fun Γ : ℝ => Γ - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
  have ht' : Tendsto (fun Γ : ℝ => (Γ - 1) ^ (1 - r)) atTop (𝓝 0) := by
    rw [show 1 - r = -(r - 1) by ring]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).comp ht
  let D := (k : ℝ) ^ r / ((k : ℝ) * ((n : ℝ) - k)) *
    ∫ P, gaussianOrientationScore P V ^ r ∂ν
  have hlim : Tendsto (fun Γ : ℝ => (Γ - 1) ^ (1 - r) * D) atTop (𝓝 0) := by
    simpa only [zero_mul] using ht'.mul_const D
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hlim
  filter_upwards [hΓ] with Γ hΓ'
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (hV Γ hΓ').1]
  convert (hV Γ hΓ').2 using 1
  unfold D
  ring

/-- The deviation supremum across all finite gaps at least `Γ₀` and the
infinite endpoint. -/
noncomputable def haarOrientationUniformDeviation (ν : Measure (OrthogonalProjector n ℓ))
    (Γ₀ : ℝ) (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  sSup (Set.range (fun Γ : {Γ : ℝ // Γ₀ ≤ Γ} =>
    |haarOrientationFiniteMean ν Γ V - haarOrientationBenchmark n k ℓ|) ∪
    {|haarOrientationEndpoint ν V - haarOrientationBenchmark n k ℓ|})

theorem ae_haarOrientationUniformDeviation_eq_max (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (hk : 0 < k) (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν]
    {Γ₀ r : ℝ} (hΓ₀ : 1 < Γ₀) (hr : 1 < r) (hr₂ : r ≤ 2)
    (hr' : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2) :
    haarOrientationUniformDeviation ν Γ₀ =ᵐ[gaussianHaarFrameLaw (show k ≤ n by omega)]
      (fun V => max |haarOrientationFiniteMean ν Γ₀ V - haarOrientationBenchmark n k ℓ|
        |haarOrientationEndpoint ν V - haarOrientationBenchmark n k ℓ|) := by
  have hkn : k < n := by omega
  filter_upwards [ae_gaussianHaarFrame_orthonormal hkn.le,
    ae_haarOrientationGap_bound hℓn hkℓ hk ν hr hr₂ hr'] with V hV hgap
  let f := fun Γ => haarOrientationFiniteMean ν Γ V
  let E := haarOrientationEndpoint ν V
  let h := haarOrientationBenchmark n k ℓ
  let s := Set.range (fun Γ : {Γ : ℝ // Γ₀ ≤ Γ} => |f Γ - h|) ∪ {|E - h|}
  have hL : |f Γ₀ - h| ∈ s := Or.inl ⟨⟨Γ₀, le_rfl⟩, rfl⟩
  have hR : |E - h| ∈ s := Or.inr (Set.mem_singleton _)
  have hb (v : ℝ) (hv : v ∈ s) : v ≤ max |f Γ₀ - h| |E - h| := by
    rcases hv with ⟨Γ, rfl⟩ | hv
    · have hΓ : 1 < (Γ : ℝ) := hΓ₀.trans_le Γ.property
      have h₀ : f Γ₀ ≤ f Γ :=
        haarOrientationFiniteMean_monotone ν hk hkn V hV hΓ₀.le hΓ.le Γ.property
      have h₁ : f Γ ≤ E := sub_nonneg.mp (hgap Γ hΓ).1
      exact abs_le_max_abs_abs (sub_le_sub_right h₀ h) (sub_le_sub_right h₁ h)
    · rw [Set.mem_singleton_iff.mp hv]
      exact le_max_right _ _
  have hB : BddAbove s := ⟨_, hb⟩
  exact le_antisymm (csSup_le ⟨_, hR⟩ hb)
    (max_le (le_csSup hB hL) (le_csSup hB hR))

end SketchOrientation
