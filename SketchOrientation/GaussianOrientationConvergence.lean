import SketchOrientation.GaussianOrientationNorm
import Mathlib.Topology.Order.WithTop

namespace SketchOrientation

open MeasureTheory Filter Matrix
open scoped Topology

variable {n k ℓ : ℕ}

/-- The sketch conditional mean at a finite gap or its infinite endpoint. -/
noncomputable def haarOrientationMeanAt (ν : Measure (OrthogonalProjector n ℓ))
    (Γ : WithTop ℝ) (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  WithTop.recTopCoe (haarOrientationEndpoint ν V) (fun g => haarOrientationFiniteMean ν g V) Γ

/-- The gap-to-ambient-scale ratio, with the infinite endpoint retained. -/
noncomputable def orientationGapScale (n k : ℕ) (Γ : WithTop ℝ) : WithTop ℝ :=
  WithTop.recTopCoe ⊤ (fun g => ((g / ((n : ℝ) * k) : ℝ) : WithTop ℝ)) Γ

noncomputable def orientationGapInverse (n k : ℕ) (Γ : WithTop ℝ) : ℝ :=
  WithTop.recTopCoe (0 : ℝ) (fun g => (n : ℝ) * k / (g - 1)) Γ

theorem orientationGapInverse_tendsto {D : ℕ → ℕ} {Γ : ℕ → WithTop ℝ}
    (hk : 0 < k) (hD : ∀ i, 0 < D i)
    (hΓ : Tendsto (fun i => orientationGapScale (D i) k (Γ i)) atTop (𝓝 ⊤)) :
    Tendsto (fun i => orientationGapInverse (D i) k (Γ i)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := (WithTop.tendsto_nhds_top_iff _).1 hΓ (1 + ε⁻¹)
  filter_upwards [h] with i hi
  generalize hgi : Γ i = γ at hi ⊢
  induction γ using WithTop.recTopCoe with
  | top => simpa [orientationGapInverse] using hε
  | coe g =>
    let b := (D i : ℝ) * (k : ℝ)
    have hb : 0 < b := mul_pos (Nat.cast_pos.mpr (hD i)) (Nat.cast_pos.mpr hk)
    have hb₁ : 1 ≤ b := by
      dsimp [b]
      exact_mod_cast (show 1 ≤ D i * k from Nat.mul_pos (hD i) hk)
    have hlarge : 1 + ε⁻¹ < g / b := WithTop.coe_lt_coe.mp hi
    have hmul : (1 + ε⁻¹) * b < g := (lt_div_iff₀ hb).1 hlarge
    have hdiff : b / ε < g - 1 := by
      rw [div_eq_mul_inv]
      linarith
    have hpos : 0 < g - 1 := (div_pos hb hε).trans hdiff
    change dist (b / (g - 1)) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hb.le hpos.le)]
    exact (div_lt_iff₀ hpos).2 (by
      have h' := (div_lt_iff₀ hε).1 hdiff
      rwa [mul_comm] at h')

theorem eventually_orientationGap_gt_one {D : ℕ → ℕ} {Γ : ℕ → WithTop ℝ}
    (hk : 0 < k) (hD : ∀ i, 0 < D i)
    (hΓ : Tendsto (fun i => orientationGapScale (D i) k (Γ i)) atTop (𝓝 ⊤)) :
    ∀ᶠ i : ℕ in atTop, (1 : ℝ) < Γ i := by
  have h := (WithTop.tendsto_nhds_top_iff _).1 hΓ 1
  filter_upwards [h] with i hi
  generalize hgi : Γ i = γ at hi ⊢
  induction γ using WithTop.recTopCoe with
  | top => exact WithTop.coe_lt_top 1
  | coe g =>
    have hb₁ : (1 : ℝ) ≤ (D i : ℝ) * k := by
      exact_mod_cast (show 1 ≤ D i * k from Nat.mul_pos (hD i) hk)
    have hb : (0 : ℝ) < (D i : ℝ) * k := zero_lt_one.trans_le hb₁
    have hg : (1 : ℝ) < g / ((D i : ℝ) * k) := WithTop.coe_lt_coe.mp hi
    exact WithTop.coe_lt_coe.mpr (hb₁.trans_lt (by simpa using (lt_div_iff₀ hb).1 hg))

theorem integrable_haarOrientationMeanAt (hk : 0 < k) (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] {Γ : WithTop ℝ}
    (hΓ : (1 : ℝ) < Γ) : Integrable (haarOrientationMeanAt (k := k) ν Γ)
      (gaussianHaarFrameLaw (show k ≤ n by omega)) := by
  induction Γ using WithTop.recTopCoe with
  | top => exact (haarOrientationEndpoint_mean hℓn hk hkℓ ν).1
  | coe g =>
    have hg : 1 < g := WithTop.coe_lt_coe.mp hΓ
    exact integrable_haarOrientationFiniteMean hk (by omega) ν hg.le

theorem haarOrientationMeanAt_L1_bound {p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (hn : k + p ≤ n) (ν : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure ν]
    {Γ : WithTop ℝ} (hΓ : (1 : ℝ) < Γ) {r : ℝ}
    (hr : 1 < r) (hr₂ : r ≤ 2) (hr' : 2 * r < (p : ℝ) + 1) :
    (∫ V, |haarOrientationMeanAt (k := k) ν Γ V - haarOrientationBenchmark n k (k + p)|
       ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤
      orientationRateConstant p r *
        (meanProjectedEnergy ν orientationRowSpace ^ (1 - 1 / r) +
         orientationGapInverse n k Γ ^ (r - 1)) := by
  have hkp : k + 1 < k + p := by omega
  have hr'' : r < ((k + p - k + 1 : ℕ) : ℝ) / 2 := by
    rw [Nat.add_sub_cancel_left]
    push_cast
    linarith
  have hkn : k < n := by omega
  induction Γ using WithTop.recTopCoe with
  | top =>
    have h := haarOrientationEndpoint_centered_bound hn hk hkp ν hr hr₂ hr''
    rw [Nat.add_sub_cancel_left] at h
    change (∫ V, |haarOrientationEndpoint ν V - haarOrientationBenchmark n k (k + p)|
       ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤ _
    change _ ≤ orientationRateConstant p r *
        (meanProjectedEnergy ν orientationRowSpace ^ (1 - 1 / r) + (0 : ℝ) ^ (r - 1))
    rw [Real.zero_rpow (sub_pos.mpr hr).ne', add_zero]
    let b := (n : ℝ) - k - 1
    let c := (n : ℝ) - k
    have hc : 0 < c := sub_pos.mpr (by exact_mod_cast hkn)
    have hbc : b / c ≤ 1 := (div_le_one hc).2 (by dsimp [b, c]; linarith)
    have hK : 0 ≤ gaussianOrientationMomentConstant p r := by
      unfold gaussianOrientationMomentConstant chiSquareNegativeMoment
      push_cast
      have ha := Real.Gamma_pos_of_pos (show 0 < ((p : ℝ) + 1) / 2 - r by linarith)
      have hb := Real.Gamma_pos_of_pos (show 0 < ((p : ℝ) + 1) / 2 by linarith)
      positivity
    have hρ : 0 ≤ meanProjectedEnergy ν orientationRowSpace := by
      rw [meanProjectedEnergy_eq_meanSketchProjector_norm (by omega) ν]
      exact norm_nonneg _
    have hp' := Real.rpow_nonneg hρ (1 - 1 / r)
    refine h.trans ((mul_le_of_le_one_left (by positivity) hbc).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hp'
  | coe g =>
    have hg : 1 < g := WithTop.coe_lt_coe.mp hΓ
    refine le_trans ?_ (haarOrientationUniformDeviation_bound_paper hk hp hn ν hg hr hr₂ hr')
    let f := haarOrientationFiniteMean (k := k) ν g
    let e := haarOrientationEndpoint (k := k) ν
    let h := haarOrientationBenchmark n k (k + p)
    have hE := (haarOrientationEndpoint_mean hn hk hkp ν).1
    have hF := integrable_haarOrientationFiniteMean hk hkn ν hg.le
    have heI : Integrable (fun V => |e V - h|) _ := (hE.sub (integrable_const h)).abs
    have hfI : Integrable (fun V => |f V - h|) _ := (hF.sub (integrable_const h)).abs
    rw [integral_congr_ae (ae_haarOrientationUniformDeviation_eq_max hn hkp hk ν hg hr hr₂ hr'')]
    exact integral_mono hfI (hfI.sup heI) (fun _ => le_max_left _ _)

set_option maxHeartbeats 1000000 in
/-- Diffuseness implies convergence in mean absolute deviation for every
allowed sequence of finite and infinite gaps. -/
theorem haarOrientationL1_of_diffuse {p : ℕ} (hk : 0 < k) (hp : 2 ≤ p) (D : ℕ → ℕ)
    (hD : ∀ i, k + p ≤ D i)
    (ν : ∀ i, Measure (OrthogonalProjector (D i) (k + p)))
    [∀ i, IsProbabilityMeasure (ν i)] (Γ : ℕ → WithTop ℝ)
    (hΓ : Tendsto (fun i => orientationGapScale (D i) k (Γ i)) atTop (𝓝 ⊤))
    (hρ : Tendsto (fun i => ‖(meanSketchProjector (ν i)).toEuclideanLin.toContinuousLinearMap‖)
      atTop (𝓝 0)) :
    Tendsto (fun i =>
      ∫ V, |haarOrientationMeanAt (k := k) (ν i) (Γ i) V -
        haarOrientationBenchmark (D i) k (k + p)|
        ∂gaussianHaarFrameLaw (show k ≤ D i from le_trans (Nat.le_add_right _ _) (hD i)))
      atTop (𝓝 0) := by
  let r : ℝ := 5 / 4
  have hr : 1 < r := by norm_num [r]
  have hr₂ : r ≤ 2 := by norm_num [r]
  have hr' : 2 * r < (p : ℝ) + 1 := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    dsimp [r]
    linarith
  have hn (i : ℕ) : 0 < D i := by have := hD i; omega
  have hGeom : Tendsto (fun i => meanProjectedEnergy (ν i) orientationRowSpace) atTop (𝓝 0) := by
    simpa only [fun i => meanProjectedEnergy_eq_meanSketchProjector_norm (hn i) (ν i)] using hρ
  have ha : 0 < 1 - 1 / r := by
    apply sub_pos.mpr
    exact (div_lt_one (zero_lt_one.trans hr)).2 hr
  have hP : Tendsto (fun i => meanProjectedEnergy (ν i) orientationRowSpace ^ (1 - 1 / r))
      atTop (𝓝 0) := by
    have h := (Real.continuous_rpow_const ha.le).continuousAt (x := 0) |>.tendsto.comp hGeom
    simpa only [Function.comp_def, Real.zero_rpow ha.ne'] using h
  have hG : Tendsto (fun i => orientationGapInverse (D i) k (Γ i) ^ (r - 1))
      atTop (𝓝 0) := by
    have h := (Real.continuous_rpow_const (sub_nonneg.mpr hr.le)).continuousAt (x := 0)
      |>.tendsto.comp (orientationGapInverse_tendsto hk hn hΓ)
    simpa only [Function.comp_def, Real.zero_rpow (sub_pos.mpr hr).ne'] using h
  have hBound := (hP.add hG).const_mul (orientationRateConstant p r)
  simp only [add_zero, mul_zero] at hBound
  refine squeeze_zero' (Eventually.of_forall fun i => integral_nonneg fun _ => abs_nonneg _) ?_ hBound
  filter_upwards [eventually_orientationGap_gt_one hk hn hΓ] with i hi
  exact haarOrientationMeanAt_L1_bound hk hp (hD i) (ν i) hi hr hr₂ hr'

/-- Mean absolute convergence implies convergence in probability for
these varying Haar frame laws. -/
theorem haarOrientationProbability_of_L1 {p : ℕ} (hk : 0 < k) (hp : 2 ≤ p) (D : ℕ → ℕ)
    (hD : ∀ i, k + p ≤ D i)
    (ν : ∀ i, Measure (OrthogonalProjector (D i) (k + p)))
    [∀ i, IsProbabilityMeasure (ν i)] (Γ : ℕ → WithTop ℝ)
    (hΓ : Tendsto (fun i => orientationGapScale (D i) k (Γ i)) atTop (𝓝 ⊤))
    (hL1 : Tendsto (fun i =>
      ∫ V, |haarOrientationMeanAt (k := k) (ν i) (Γ i) V -
        haarOrientationBenchmark (D i) k (k + p)|
        ∂gaussianHaarFrameLaw (show k ≤ D i from le_trans (Nat.le_add_right _ _) (hD i)))
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun i =>
      (gaussianHaarFrameLaw (show k ≤ D i from le_trans (Nat.le_add_right _ _) (hD i))).real
        {V | ε ≤ |haarOrientationMeanAt (k := k) (ν i) (Γ i) V -
          haarOrientationBenchmark (D i) k (k + p)|}) atTop (𝓝 0) := by
  intro ε hε
  have hn (i : ℕ) : 0 < D i := by have := hD i; omega
  have hkp : k + 1 < k + p := by omega
  have hM := hL1.div_const ε
  simp only [zero_div] at hM
  refine squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_ hM
  filter_upwards [eventually_orientationGap_gt_one hk hn hΓ] with i hi
  have hI : Integrable (fun V => |haarOrientationMeanAt (k := k) (ν i) (Γ i) V -
      haarOrientationBenchmark (D i) k (k + p)|) _ :=
    ((integrable_haarOrientationMeanAt hk (hD i) hkp (ν i) hi).sub (integrable_const _)).abs
  apply (le_div_iff₀ hε).2
  rw [mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hI ε

end SketchOrientation
