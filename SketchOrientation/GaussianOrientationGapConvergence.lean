import SketchOrientation.GaussianOrientationConvergence

namespace SketchOrientation

open MeasureTheory Filter Matrix Set
open scoped Topology

variable {n k p : ℕ}

private theorem haarOrientationGapAt_L1_bound (hk : 0 < k) (hp : 2 ≤ p)
    (hn : k + p ≤ n) (ν : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure ν]
    {Γ : WithTop ℝ} (hΓ : (1 : ℝ) < Γ) :
    (∫ V, |haarOrientationEndpoint (k := k) ν V - haarOrientationMeanAt ν Γ V|
       ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤
      chiSquareNegativeMoment (p + 1) ((5 : ℝ) / 4) *
        orientationGapInverse n k Γ ^ (((5 : ℝ) / 4) - 1) := by
  let r : ℝ := 5 / 4
  let ℓ := k + p
  let b := (n : ℝ) - k - 1
  let c := (n : ℝ) - k
  let M := chiSquareNegativeMoment (p + 1) r
  have hkp : k + 1 < ℓ := by dsimp [ℓ]; omega
  have hr : 1 < r := by norm_num [r]
  have hr₂ : r ≤ 2 := by norm_num [r]
  have har : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2 := by
    dsimp [ℓ, r]
    rw [Nat.add_sub_cancel_left, Nat.cast_add]
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hM : 0 ≤ M := by
    unfold M chiSquareNegativeMoment
    have hR : r < ((p + 1 : ℕ) : ℝ) / 2 := by
      simpa [ℓ] using har
    have h₁ := Real.Gamma_pos_of_pos (sub_pos.mpr hR)
    have h₂ := Real.Gamma_pos_of_pos ((zero_lt_one.trans hr).trans hR)
    positivity
  induction Γ using WithTop.recTopCoe with
  | top =>
    change (∫ V, |haarOrientationEndpoint ν V - haarOrientationEndpoint ν V|
       ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤ M * (0 : ℝ) ^ (r - 1)
    rw [Real.zero_rpow (sub_pos.mpr hr).ne']
    simp
  | coe g =>
    have hg : 1 < g := WithTop.coe_lt_coe.mp hΓ
    let η := gaussianHaarFrameLaw (show k ≤ n by omega)
    have h' : (fun V => |haarOrientationEndpoint (k := k) ν V - haarOrientationFiniteMean ν g V|)
          =ᵐ[η] fun V => haarOrientationEndpoint ν V - haarOrientationFiniteMean ν g V := by
      filter_upwards [ae_haarOrientationGap_bound hn hkp hk ν hr hr₂ har] with V hV
      rw [abs_of_nonneg (hV g hg).1]
    change (∫ V, |haarOrientationEndpoint ν V - haarOrientationFiniteMean ν g V| ∂η) ≤
      M * ((n : ℝ) * k / (g - 1)) ^ (r - 1)
    rw [integral_congr_ae h']
    have h := haarOrientationGap_integral_bound hn hkp hk ν hg hr hr₂ har
    simp only [Nat.add_sub_cancel_left] at h
    refine h.trans ?_
    have ht : (k : ℝ) + 1 < n := by exact_mod_cast (show k + 1 < n by omega)
    have hb : 0 < b := by dsimp [b]; linarith
    have hc : 0 < c := by dsimp [c]; linarith
    have hbc : b / c ≤ 1 := (div_le_one hc).2 (by dsimp [b,c]; linarith)
    have hbn : b ≤ n := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hL : 0 ≤ (k : ℝ) * b / (g - 1) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) hb.le) (sub_nonneg.mpr hg.le)
    have hp' : (k : ℝ) * b / (g - 1) ≤ (n : ℝ) * k / (g - 1) := by
      rw [mul_comm (n : ℝ)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbn (Nat.cast_nonneg _))
        (sub_nonneg.mpr hg.le)
    change b / c * (M * ((k : ℝ) * b / (g - 1)) ^ (r - 1)) ≤ _
    refine (mul_le_of_le_one_left (mul_nonneg hM (Real.rpow_nonneg hL _)) hbc).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL hp' (sub_nonneg.mpr hr.le)) hM

/-- The unconditional finite-to-infinite gap tends to zero in mean for
all allowed gap sequences, including mixed finite and infinite values. -/
theorem haarOrientationGapL1_tendsto_zero (hk : 0 < k) (hp : 2 ≤ p) (D : ℕ → ℕ)
    (hD : ∀ i, k + p ≤ D i)
    (ν : ∀ i, Measure (OrthogonalProjector (D i) (k + p)))
    [∀ i, IsProbabilityMeasure (ν i)] (Γ : ℕ → WithTop ℝ)
    (hΓ : Tendsto (fun i => orientationGapScale (D i) k (Γ i)) atTop (𝓝 ⊤)) :
    Tendsto (fun i =>
      ∫ V, |haarOrientationEndpoint (k := k) (ν i) V - haarOrientationMeanAt (ν i) (Γ i) V|
        ∂gaussianHaarFrameLaw (show k ≤ D i from le_trans (Nat.le_add_right _ _) (hD i)))
      atTop (𝓝 0) := by
  have hn (i : ℕ) : 0 < D i := by have := hD i; omega
  have h := orientationGapInverse_tendsto hk hn hΓ
  have hr : 0 < ((5 : ℝ) / 4) - 1 := by norm_num
  have hR := (Real.continuous_rpow_const hr.le).continuousAt (x := 0) |>.tendsto.comp h
  simp only [Function.comp_def, Real.zero_rpow hr.ne'] at hR
  have hM := hR.const_mul (chiSquareNegativeMoment (p + 1) ((5 : ℝ) / 4))
  simp only [mul_zero] at hM
  refine squeeze_zero' (Eventually.of_forall fun i => integral_nonneg fun _ => abs_nonneg _) ?_ hM
  filter_upwards [eventually_orientationGap_gt_one hk hn hΓ] with i hi
  exact haarOrientationGapAt_L1_bound hk hp (hD i) (ν i) hi

set_option maxHeartbeats 1200000 in
/-- Convergence in probability for the observed finite or infinite gaps
implies the same convergence for the inverse endpoint. -/
theorem haarOrientationEndpointProbability_of_observed (hk : 0 < k) (hp : 2 ≤ p)
    (D : ℕ → ℕ) (hD : ∀ i, k + p ≤ D i)
    (ν : ∀ i, Measure (OrthogonalProjector (D i) (k + p)))
    [∀ i, IsProbabilityMeasure (ν i)] (Γ : ℕ → WithTop ℝ)
    (hΓ : Tendsto (fun i => orientationGapScale (D i) k (Γ i)) atTop (𝓝 ⊤))
    (hP : ∀ ε : ℝ, 0 < ε → Tendsto (fun i =>
      (gaussianHaarFrameLaw (show k ≤ D i from le_trans (Nat.le_add_right _ _) (hD i))).real
        {V | ε ≤ |haarOrientationMeanAt (k := k) (ν i) (Γ i) V -
          haarOrientationBenchmark (D i) k (k + p)|}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun i =>
      (gaussianHaarFrameLaw (show k ≤ D i from le_trans (Nat.le_add_right _ _) (hD i))).real
        {V | ε ≤ |haarOrientationEndpoint (k := k) (ν i) V -
          haarOrientationBenchmark (D i) k (k + p)|}) atTop (𝓝 0) := by
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  let η (i : ℕ) := gaussianHaarFrameLaw (show k ≤ D i from le_trans (Nat.le_add_right _ _) (hD i))
  let e (i : ℕ) := haarOrientationEndpoint (k := k) (ν i)
  let f (i : ℕ) := haarOrientationMeanAt (k := k) (ν i) (Γ i)
  let h (i : ℕ) := haarOrientationBenchmark (D i) k (k + p)
  let A (i : ℕ) := {V | δ ≤ |f i V - h i|}
  let B (i : ℕ) := {V | δ ≤ |e i V - f i V|}
  let C (i : ℕ) := {V | ε ≤ |e i V - h i|}
  have hA : Tendsto (fun i => (η i).real (A i)) atTop (𝓝 0) := hP δ hδ
  have hL := haarOrientationGapL1_tendsto_zero hk hp D hD ν Γ hΓ
  have hn (i : ℕ) : 0 < D i := by have := hD i; omega
  have hkp : k + 1 < k + p := by omega
  have hB : Tendsto (fun i => (η i).real (B i)) atTop (𝓝 0) := by
    have hb := hL.div_const δ
    simp only [zero_div] at hb
    refine squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_ hb
    filter_upwards [eventually_orientationGap_gt_one hk hn hΓ] with i hi
    have hE := (haarOrientationEndpoint_mean (hD i) hk hkp (ν i)).1
    have hF := integrable_haarOrientationMeanAt hk (hD i) hkp (ν i) hi
    have hInt : Integrable (fun V => |e i V - f i V|) (η i) := (hE.sub hF).abs
    apply (le_div_iff₀ hδ).2
    rw [mul_comm]
    exact mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hInt δ
  have hle (i : ℕ) : C i ⊆ A i ∪ B i := by
    intro V hV
    by_contra! hh
    have ha : |f i V - h i| < δ := lt_of_not_ge (fun hv => hh (Or.inl hv))
    have hb : |e i V - f i V| < δ := lt_of_not_ge (fun hv => hh (Or.inr hv))
    have hT : |e i V - h i| ≤ |f i V - h i| + |e i V - f i V| := by
      rw [show e i V - h i = (f i V - h i) + (e i V - f i V) by ring]
      exact abs_add_le _ _
    have hv : ε ≤ |e i V - h i| := hV
    dsimp [δ] at ha hb
    linarith
  have hS := hA.add hB
  simp only [add_zero] at hS
  refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_ hS
  intro i
  exact (measureReal_mono (hle i)).trans (measureReal_union_le _ _)

end SketchOrientation
