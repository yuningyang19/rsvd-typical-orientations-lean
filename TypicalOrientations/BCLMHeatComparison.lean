import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TypicalOrientations

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

variable {ι A : Type*} [Fintype ι]

/-- The positive weighted product transported by the heat equation. -/
def weightedPowerProduct (c v : ι → ℝ) : ℝ := ∏ i, (v i) ^ (c i)

private theorem weightedPowerProduct_eq_exp (c v : ι → ℝ) (h : ∀ i, 0 < v i) :
    weightedPowerProduct c v = Real.exp (∑ i, c i * Real.log (v i)) := by
  unfold weightedPowerProduct
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [Real.rpow_def_of_pos (h i), mul_comm]

/-- Weighted derivative of the logarithm of the product. -/
def weightedLogSlope (c v d : ι → ℝ) : ℝ := ∑ i, c i * (d i / v i)

theorem hasDerivAt_weightedPowerProduct (c : ι → ℝ) (f : ι → ℝ → ℝ)
    (d : ι → ℝ) {t : ℝ} (hPos : ∀ i, 0 < f i t)
    (hf : ∀ i, HasDerivAt (f i) (d i) t) :
    HasDerivAt (fun s => weightedPowerProduct c (fun i => f i s))
      (weightedPowerProduct c (fun i => f i t) * weightedLogSlope c (fun i => f i t) d) t := by
  have hLog : HasDerivAt (fun s => ∑ i, c i * Real.log (f i s))
      (weightedLogSlope c (fun i => f i t) d) t := by
    exact HasDerivAt.fun_sum fun i _ => ((hf i).log (hPos i).ne').const_mul (c i)
  have hP : ∀ᶠ s in 𝓝 t, ∀ i, 0 < f i s := by
    refine eventually_all.mpr fun i => ?_
    exact (hf i).continuousAt.eventually (Ioi_mem_nhds (hPos i))
  have hE : (fun s => weightedPowerProduct c (fun i => f i s)) =ᶠ[𝓝 t]
      (fun s => Real.exp (∑ i, c i * Real.log (f i s))) :=
    hP.mono fun s hs => weightedPowerProduct_eq_exp c (fun i => f i s) hs
  rw [weightedPowerProduct_eq_exp c _ hPos]
  exact hLog.exp.congr_of_eventuallyEq hE

/-- The second derivative of the weighted product along a spatial curve. -/
def weightedProductSecond (c v d e : ι → ℝ) : ℝ :=
  weightedPowerProduct c v *
    (weightedLogSlope c v e - (∑ i, c i * (d i / v i) ^ 2) + weightedLogSlope c v d ^ 2)

theorem hasDerivAt_deriv_weightedPowerProduct (c : ι → ℝ)
    (f d : ι → ℝ → ℝ) (e : ι → ℝ) {t : ℝ}
    (hPos : ∀ i, 0 < f i t)
    (hDeriv : ∀ᶠ s in 𝓝 t, ∀ i, HasDerivAt (f i) (d i s) s)
    (hSecond : ∀ i, HasDerivAt (d i) (e i) t) :
    HasDerivAt (deriv fun s => weightedPowerProduct c (fun i => f i s))
      (weightedProductSecond c (fun i => f i t) (fun i => d i t) e) t := by
  let P (s : ℝ) := weightedPowerProduct c (fun i => f i s)
  let L (s : ℝ) := weightedLogSlope c (fun i => f i s) (fun i => d i s)
  let L' : ℝ := ∑ i, c i * (e i / f i t - (d i t / f i t) ^ 2)
  have hD := hDeriv.self_of_nhds
  have hP : HasDerivAt P (P t * L t) t :=
    hasDerivAt_weightedPowerProduct c f (fun i => d i t) hPos hD
  have hPPos : ∀ᶠ s in 𝓝 t, ∀ i, 0 < f i s := by
    refine eventually_all.mpr fun i => ?_
    exact (hD i).continuousAt.eventually (Ioi_mem_nhds (hPos i))
  have hLogDerivative (i : ι) :
      HasDerivAt (fun s => d i s / f i s)
        (e i / f i t - (d i t / f i t)^2) t := by
    have h := (hSecond i).div (hD i) (hPos i).ne'
    have he : (e i * f i t - d i t * d i t) / f i t ^ 2 =
        e i / f i t - (d i t / f i t)^2 := by
      field_simp [(hPos i).ne']
    rw [he] at h
    exact h
  have hL : HasDerivAt L L' t :=
    HasDerivAt.fun_sum fun i _ => (hLogDerivative i).const_mul (c i)
  have hFirst : deriv P =ᶠ[𝓝 t] (fun s => P s * L s) := by
    filter_upwards [hDeriv, hPPos] with s hs hpos
    exact (hasDerivAt_weightedPowerProduct c f (fun i => d i s) hpos hs).deriv
  have hProd := (hP.mul hL).congr_of_eventuallyEq hFirst
  change HasDerivAt (deriv P) _ t
  have hE : L' = weightedLogSlope c (fun i => f i t) e -
      ∑ i, c i * (d i t / f i t) ^ 2 := by
    unfold L' weightedLogSlope
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hR : weightedProductSecond c (fun i => f i t) (fun i => d i t) e =
      P t * L t * L t + P t * L' := by
    rw [hE]
    unfold weightedProductSecond L P
    ring
  rw [hR]
  exact hProd

section DirectionSum

variable [Fintype A]

/-- Exact pointwise heat identity for the weighted product. Its defect
contains the difference of the two squared logarithmic gradients. -/
theorem weightedPowerProduct_heat_defect (c v : ι → ℝ)
    (d₁ d₂ : A → ι → ℝ) :
    weightedPowerProduct c v * weightedLogSlope c v (fun i => ∑ a, d₂ a i) -
      (∑ a, weightedProductSecond c v (d₁ a) (d₂ a)) =
        weightedPowerProduct c v *
          ((∑ a, ∑ i, c i * (d₁ a i / v i) ^ 2) -
            ∑ a, weightedLogSlope c v (d₁ a) ^ 2) := by
  have hL : weightedLogSlope c v (fun i => ∑ a, d₂ a i) =
      ∑ a, weightedLogSlope c v (d₂ a) := by
    unfold weightedLogSlope
    simp only [Finset.sum_div, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hL]
  simp only [weightedProductSecond, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

/-- The gradient inequality turns the exact heat identity into the
pointwise supersolution bound for the weighted product. -/
theorem weightedPowerProduct_heat_le (c v : ι → ℝ)
    (d₁ d₂ : A → ι → ℝ) (hPos : ∀ i, 0 < v i)
    (hGrad : (∑ a, weightedLogSlope c v (d₁ a) ^ 2) ≤
      ∑ a, ∑ i, c i * (d₁ a i / v i) ^ 2) :
    (∑ a, weightedProductSecond c v (d₁ a) (d₂ a)) ≤
      weightedPowerProduct c v * weightedLogSlope c v (fun i => ∑ a, d₂ a i) := by
  apply sub_nonneg.mp
  rw [weightedPowerProduct_heat_defect]
  exact mul_nonneg (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hPos i).le _)
    (sub_nonneg.mpr hGrad)

end DirectionSum

section CompactIntegration

variable {U : Type*} [TopologicalSpace U] [CompactSpace U]
  [MeasurableSpace U] [OpensMeasurableSpace U]

omit [CompactSpace U] [MeasurableSpace U] [OpensMeasurableSpace U] in
private theorem compactTimeSlice_continuous {F : ℝ → U → ℝ} {s : Set ℝ}
    (hF : ContinuousOn (fun p : ℝ × U => F p.1 p.2) (s ×ˢ univ))
    {t : ℝ} (ht : t ∈ s) : Continuous (F t) :=
  hF.comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨ht, Set.mem_univ _⟩)

/-- Joint continuity of a derivative on a compact space and a closed time
interval supplies the local bound needed to differentiate its integral. -/
theorem hasDerivAt_integral_compact_Icc (μ : Measure U) [IsFiniteMeasure μ]
    (F F' : ℝ → U → ℝ) {a b t : ℝ} (ha : a < t) (hb : t < b)
    (hF : ContinuousOn (fun p : ℝ × U => F p.1 p.2) (Icc a b ×ˢ univ))
    (hF' : ContinuousOn (fun p : ℝ × U => F' p.1 p.2) (Icc a b ×ˢ univ))
    (hD : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => F r x) (F' s x) s) :
    HasDerivAt (fun r => ∫ x, F r x ∂μ) (∫ x, F' t x ∂μ) t := by
  have hK : IsCompact (Icc a b ×ˢ (univ : Set U)) := isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF
  have ht : t ∈ Ioo a b := ⟨ha, hb⟩
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hIcc : ∀ᶠ s in 𝓝 t, s ∈ Icc a b := Icc_mem_nhds ha hb
  have hEv : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) μ :=
    hIcc.mono fun s hs =>
      (compactTimeSlice_continuous hF hs).measurable.aestronglyMeasurable
  have hInt : Integrable (F t) μ :=
    Integrable.of_bound (compactTimeSlice_continuous hF ht').measurable.aestronglyMeasurable
      B (ae_of_all _ fun x => hB (t, x) ⟨ht', Set.mem_univ x⟩)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (isOpen_Ioo.mem_nhds ht)
    hEv hInt (compactTimeSlice_continuous hF' ht').measurable.aestronglyMeasurable
    (ae_of_all _ fun x s hs => hC (s, x) ⟨Ioo_subset_Icc_self hs, Set.mem_univ x⟩)
    (integrable_const C) (ae_of_all _ fun x s hs => hD s hs x)).2

theorem hasDerivAt_integral_compact (μ : Measure U) [IsFiniteMeasure μ]
    (F F' : ℝ → U → ℝ) (t : ℝ)
    (hF : Continuous (fun p : ℝ × U => F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × U => F' p.1 p.2))
    (hD : ∀ s x, HasDerivAt (fun r => F r x) (F' s x) s) :
    HasDerivAt (fun r => ∫ x, F r x ∂μ) (∫ x, F' t x ∂μ) t :=
  hasDerivAt_integral_compact_Icc μ F F' (show t - 1 < t by linarith)
    (show t < t + 1 by linarith) hF.continuousOn hF'.continuousOn
    (fun s _ x => hD s x)

/-- Integrating the second derivative along a measure-preserving flow gives
zero. Both interchanges between derivatives and integrals use compactness. -/
theorem integral_secondDerivative_eq_zero_of_invariant_flow
    (μ : Measure U) [IsFiniteMeasure μ] (φ : ℝ → U → U)
    (hφ : Continuous (fun p : ℝ × U => φ p.1 p.2))
    (hPres : ∀ s, MeasurePreserving (φ s) μ μ)
    (f : U → ℝ) (hf : Continuous f)
    (d₁ d₂ : ℝ → U → ℝ)
    (hd₁ : Continuous (fun p : ℝ × U => d₁ p.1 p.2))
    (hd₂ : Continuous (fun p : ℝ × U => d₂ p.1 p.2))
    (h₁ : ∀ s x, HasDerivAt (fun t => f (φ t x)) (d₁ s x) s)
    (h₂ : ∀ s x, HasDerivAt (fun t => d₁ t x) (d₂ s x) s)
    (s : ℝ) :
    (∫ x, d₂ s x ∂μ) = 0 := by
  let F : ℝ → U → ℝ := fun t x => f (φ t x)
  have hF : Continuous (fun p : ℝ × U => F p.1 p.2) := hf.comp hφ
  have hConst : (fun t => ∫ x, F t x ∂μ) = fun _ => ∫ x, f x ∂μ := by
    funext t
    have ht := hPres t
    change (∫ x, f (φ t x) ∂μ) = _
    rw [← integral_map ht.measurable.aemeasurable hf.measurable.aestronglyMeasurable, ht.map_eq]
  have hZero₁ (t : ℝ) : (∫ x, d₁ t x ∂μ) = 0 := by
    have H := hasDerivAt_integral_compact μ F d₁ t hF hd₁ h₁
    rw [hConst] at H
    exact H.unique (hasDerivAt_const t _)
  have H := hasDerivAt_integral_compact μ d₁ d₂ s hd₁ hd₂ h₂
  rw [funext hZero₁] at H
  exact H.unique (hasDerivAt_const s _)

end CompactIntegration


section HeatEvolution

variable {U : Type*} [TopologicalSpace U] [CompactSpace U]
  [MeasurableSpace U] [OpensMeasurableSpace U] [Fintype A]

private theorem continuousOn_weightedPowerProduct {X : Type*} [TopologicalSpace X]
    {s : Set X} (c : ι → ℝ) (v : ι → X → ℝ)
    (hv : ∀ i, ContinuousOn (v i) s) (h : ∀ i x, x ∈ s → 0 < v i x) :
    ContinuousOn (fun x => weightedPowerProduct c (fun i => v i x)) s := by
  unfold weightedPowerProduct
  apply continuousOn_finsetProd
  intro i _ x hx
  exact (Real.continuousAt_rpow_const (v i x) (c i) (Or.inl (h i x hx).ne')).comp_continuousWithinAt
    (hv i x hx)

private theorem continuousOn_weightedLogSlope {X : Type*} [TopologicalSpace X]
    {s : Set X} (c : ι → ℝ) (v d : ι → X → ℝ)
    (hv : ∀ i, ContinuousOn (v i) s) (hd : ∀ i, ContinuousOn (d i) s)
    (h : ∀ i x, x ∈ s → 0 < v i x) :
    ContinuousOn (fun x => weightedLogSlope c (fun i => v i x) (fun i => d i x)) s := by
  unfold weightedLogSlope
  apply continuousOn_finsetSum
  intro i _
  exact continuousOn_const.mul ((hd i).div (hv i) (fun x hx => (h i x hx).ne'))

private theorem continuousOn_weightedProductSecond {X : Type*} [TopologicalSpace X]
    {s : Set X} (c : ι → ℝ) (v d e : ι → X → ℝ)
    (hv : ∀ i, ContinuousOn (v i) s) (hd : ∀ i, ContinuousOn (d i) s)
    (he : ∀ i, ContinuousOn (e i) s) (h : ∀ i x, x ∈ s → 0 < v i x) :
    ContinuousOn (fun x => weightedProductSecond c (fun i => v i x)
      (fun i => d i x) (fun i => e i x)) s := by
  have hsq : ContinuousOn (fun x => ∑ i, c i * (d i x / v i x)^2) s := by
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.mul (((hd i).div (hv i) (fun x hx => (h i x hx).ne')).pow 2)
  exact (continuousOn_weightedPowerProduct c v hv h).mul
    (((continuousOn_weightedLogSlope c v e hv he h).sub hsq).add
      ((continuousOn_weightedLogSlope c v d hv hd h).pow 2))

private theorem continuousOn_integral_compact_Ici (μ : Measure U) [IsFiniteMeasure μ]
    {F : ℝ → U → ℝ}
    (hF : ContinuousOn (fun p : ℝ × U => F p.1 p.2) (Ici 0 ×ˢ univ)) :
    ContinuousOn (fun t => ∫ x, F t x ∂μ) (Ici 0) := by
  intro t ht
  let S := Icc 0 (t + 1)
  have hKS : IsCompact (S ×ˢ (univ : Set U)) := isCompact_Icc.prod isCompact_univ
  have hS : S ×ˢ (univ : Set U) ⊆ Ici 0 ×ˢ univ :=
    fun _ hy => ⟨hy.1.1, hy.2⟩
  obtain ⟨C, hC⟩ := hKS.exists_bound_of_continuousOn (hF.mono hS)
  have hLt : ∀ᶠ u in 𝓝[Ici 0] t, u < t + 1 := by
    have h : ∀ᶠ u in 𝓝 t, u < t + 1 :=
      Iio_mem_nhds (show t < t + 1 by linarith)
    exact h.filter_mono nhdsWithin_le_nhds
  have hMem : ∀ᶠ u in 𝓝[Ici 0] t, u ∈ S := by
    filter_upwards [eventually_mem_nhdsWithin, hLt] with u hu hu'
    exact ⟨hu, hu'.le⟩
  have hMeas : ∀ᶠ u in 𝓝[Ici 0] t, AEStronglyMeasurable (F u) μ :=
    hMem.mono (fun _ hu => (compactTimeSlice_continuous hF hu.1).measurable.aestronglyMeasurable)
  have hBound : ∀ᶠ u in 𝓝[Ici 0] t, ∀ᵐ x ∂μ, ‖F u x‖ ≤ C :=
    hMem.mono (fun u hu => ae_of_all _ fun x => hC (u, x) ⟨hu, Set.mem_univ _⟩)
  have hLim : ∀ᵐ x ∂μ, Tendsto (fun u => F u x) (𝓝[Ici 0] t) (𝓝 (F t x)) :=
    ae_of_all _ fun x => by
      have h := hF.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => ⟨hu, Set.mem_univ x⟩)
      exact h t ht
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    hMeas hBound (integrable_const _) hLim

/-- A time-zero directional derivative of a one-parameter flow determines
the derivative at any point along its orbit. -/
theorem hasDerivAt_orbit_of_zero {V : Type*} (φ : ℝ → V → V)
    (hAdd : ∀ s t x, φ (s + t) x = φ s (φ t x))
    (f d : V → ℝ) (h : ∀ x, HasDerivAt (fun t => f (φ t x)) (d x) 0)
    (s : ℝ) (x : V) :
    HasDerivAt (fun t => f (φ t x)) (d (φ s x)) s := by
  have h₀ : HasDerivAt (fun t => f (φ t (φ s x))) (d (φ s x)) (s-s) := by
    simpa only [sub_self] using h (φ s x)
  have h₁ := HasDerivAt.comp_sub_const s s h₀
  have he : (fun t => f (φ (t-s) (φ s x))) = fun t => f (φ t x) := by
    funext t
    rw [← hAdd, sub_add_cancel]
  rwa [he] at h₁

private theorem integrable_continuous_compact (μ : Measure U) [IsFiniteMeasure μ]
    {f : U → ℝ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable C
    (ae_of_all _ fun x => hC x (Set.mem_univ _))

/-- Heat evolution increases the integral of the weighted product. The
inputs specify the heat equation and the logarithmic-gradient inequality.
The two differentiations under the Haar integral follow from compactness
and the measure-preserving one-parameter flows. -/
theorem weightedHeatIntegral_mono (μ : Measure U) [IsFiniteMeasure μ]
    (c : ι → ℝ) (h : ι → ℝ → U → ℝ) (φ : A → ℝ → U → U)
    (d₁ d₂ : A → ι → ℝ → U → ℝ)
    (hPos : ∀ i t, 0 ≤ t → ∀ x, 0 < h i t x)
    (hFlowZero : ∀ a x, φ a 0 x = x)
    (hFlowAdd : ∀ a s t x, φ a (s+t) x = φ a s (φ a t x))
    (hFlowCont : ∀ a, Continuous (fun p : ℝ × U => φ a p.1 p.2))
    (hPres : ∀ a s, MeasurePreserving (φ a s) μ μ)
    (hJoint : ∀ i, ContinuousOn (fun p : ℝ × U => h i p.1 p.2) (Ici 0 ×ˢ univ))
    (hJoint₁ : ∀ a i, ContinuousOn (fun p : ℝ × U => d₁ a i p.1 p.2) (Ici 0 ×ˢ univ))
    (hJoint₂ : ∀ a i, ContinuousOn (fun p : ℝ × U => d₂ a i p.1 p.2) (Ici 0 ×ˢ univ))
    (hTime : ∀ i t, 0 < t → ∀ x,
      HasDerivAt (fun r => h i r x) (∑ a, d₂ a i t x) t)
    (hSpace₁ : ∀ a i t, 0 < t → ∀ x,
      HasDerivAt (fun r => h i t (φ a r x)) (d₁ a i t x) 0)
    (hSpace₂ : ∀ a i t, 0 < t → ∀ x,
      HasDerivAt (fun r => d₁ a i t (φ a r x)) (d₂ a i t x) 0)
    (hGradient : ∀ t, 0 < t → ∀ x,
      (∑ a, weightedLogSlope c (fun i => h i t x) (fun i => d₁ a i t x) ^ 2) ≤
        ∑ a, ∑ i, c i * (d₁ a i t x / h i t x) ^ 2) :
    MonotoneOn (fun t => ∫ x, weightedPowerProduct c (fun i => h i t x) ∂μ) (Ici 0) := by
  let V := fun (i : ι) (p : ℝ × U) => h i p.1 p.2
  let D₁ := fun (a : A) (i : ι) (p : ℝ × U) => d₁ a i p.1 p.2
  let D₂ := fun (a : A) (i : ι) (p : ℝ × U) => d₂ a i p.1 p.2
  let P := fun (t : ℝ) (x : U) => weightedPowerProduct c (fun i => h i t x)
  let DP := fun (t : ℝ) (x : U) => P t x *
    weightedLogSlope c (fun i => h i t x) (fun i => ∑ a, d₂ a i t x)
  let EP := fun (a : A) (t : ℝ) (x : U) => P t x *
    weightedLogSlope c (fun i => h i t x) (fun i => d₁ a i t x)
  let KP := fun (a : A) (t : ℝ) (x : U) =>
    weightedProductSecond c (fun i => h i t x) (fun i => d₁ a i t x) (fun i => d₂ a i t x)
  have hVPos (i : ι) (p : ℝ × U) (hp : p ∈ Ici 0 ×ˢ (univ : Set U)) : 0 < V i p :=
    hPos i p.1 hp.1 p.2
  have hP : ContinuousOn (fun p : ℝ × U => P p.1 p.2) (Ici 0 ×ˢ univ) :=
    continuousOn_weightedPowerProduct c V hJoint hVPos
  have hDP : ContinuousOn (fun p : ℝ × U => DP p.1 p.2) (Ici 0 ×ˢ univ) :=
    hP.mul (continuousOn_weightedLogSlope c V (fun i p => ∑ a, D₂ a i p) hJoint
      (fun i => continuousOn_finsetSum _ (fun a _ => hJoint₂ a i)) hVPos)
  have hEP (a : A) : ContinuousOn (fun p : ℝ × U => EP a p.1 p.2) (Ici 0 ×ˢ univ) :=
    hP.mul (continuousOn_weightedLogSlope c V (D₁ a) hJoint (hJoint₁ a) hVPos)
  have hKP (a : A) : ContinuousOn (fun p : ℝ × U => KP a p.1 p.2) (Ici 0 ×ˢ univ) :=
    continuousOn_weightedProductSecond c V (D₁ a) (D₂ a) hJoint
      (hJoint₁ a) (hJoint₂ a) hVPos
  have hf : ContinuousOn (fun t => ∫ x, P t x ∂μ) (Ici 0) :=
    continuousOn_integral_compact_Ici μ hP
  have hTimeP (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun r => ∫ x, P r x ∂μ) (∫ x, DP t x ∂μ) t := by
    have hS : Icc 0 (t+1) ×ˢ (univ : Set U) ⊆ Ici 0 ×ˢ univ :=
      fun _ hp => ⟨hp.1.1, hp.2⟩
    refine hasDerivAt_integral_compact_Icc μ P DP ht (show t < t+1 by linarith)
      (hP.mono hS) (hDP.mono hS) (fun s hs x => ?_)
    exact hasDerivAt_weightedPowerProduct c (fun i r => h i r x)
      (fun i => ∑ a, d₂ a i s x) (fun i => hPos i s hs.1.le x)
      (fun i => hTime i s hs.1 x)
  have hZero (t : ℝ) (ht : 0 < t) (a : A) : (∫ x, KP a t x ∂μ) = 0 := by
    have h₀ := compactTimeSlice_continuous hP ht.le
    have h₁ := compactTimeSlice_continuous (hEP a) ht.le
    have h₂ := compactTimeSlice_continuous (hKP a) ht.le
    have hS₁ (i : ι) (s : ℝ) (x : U) :
        HasDerivAt (fun r => h i t (φ a r x)) (d₁ a i t (φ a s x)) s :=
      hasDerivAt_orbit_of_zero (φ a) (hFlowAdd a) (h i t) (d₁ a i t)
        (hSpace₁ a i t ht) s x
    have hS₂ (i : ι) (s : ℝ) (x : U) :
        HasDerivAt (fun r => d₁ a i t (φ a r x)) (d₂ a i t (φ a s x)) s :=
      hasDerivAt_orbit_of_zero (φ a) (hFlowAdd a) (d₁ a i t) (d₂ a i t)
        (hSpace₂ a i t ht) s x
    have hEp (s : ℝ) (x : U) :
        HasDerivAt (fun r => P t (φ a r x)) (EP a t (φ a s x)) s :=
      hasDerivAt_weightedPowerProduct c (fun i r => h i t (φ a r x))
        (fun i => d₁ a i t (φ a s x))
        (fun i => hPos i t ht.le (φ a s x)) (fun i => hS₁ i s x)
    have hKp (s : ℝ) (x : U) :
        HasDerivAt (fun r => EP a t (φ a r x)) (KP a t (φ a s x)) s := by
      have H := hasDerivAt_deriv_weightedPowerProduct c
        (fun i r => h i t (φ a r x)) (fun i r => d₁ a i t (φ a r x))
        (fun i => d₂ a i t (φ a s x)) (fun i => hPos i t ht.le (φ a s x))
        (Eventually.of_forall fun r i => hS₁ i r x) (fun i => hS₂ i s x)
      change HasDerivAt (deriv fun r => P t (φ a r x)) (KP a t (φ a s x)) s at H
      rwa [funext (fun r => (hEp r x).deriv)] at H
    have H := integral_secondDerivative_eq_zero_of_invariant_flow μ
      (φ a) (hFlowCont a) (hPres a) (P t) h₀
      (fun s x => EP a t (φ a s x)) (fun s x => KP a t (φ a s x))
      (h₁.comp (hFlowCont a)) (h₂.comp (hFlowCont a)) hEp hKp 0
    simpa only [hFlowZero a] using H
  have hDeriv0 (t : ℝ) (ht : 0 < t) : 0 ≤ ∫ x, DP t x ∂μ := by
    have hI (a : A) : Integrable (KP a t) μ :=
      integrable_continuous_compact μ (compactTimeSlice_continuous (hKP a) ht.le)
    have hD : Integrable (DP t) μ :=
      integrable_continuous_compact μ (compactTimeSlice_continuous hDP ht.le)
    have hM := integral_mono (integrable_finsetSum _ (fun a _ => hI a)) hD
      (fun x => weightedPowerProduct_heat_le c (fun i => h i t x)
        (fun a i => d₁ a i t x) (fun a i => d₂ a i t x)
        (fun i => hPos i t ht.le x) (hGradient t ht x))
    rw [integral_finsetSum _ (fun a _ => hI a)] at hM
    simpa only [hZero t ht, Finset.sum_const_zero] using hM
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hf
  · intro t ht
    rw [interior_Ici] at ht
    exact (hTimeP t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    rw [(hTimeP t ht).deriv]
    exact hDeriv0 t ht

end HeatEvolution


section HeatLimit

variable {U : Type*} [MeasurableSpace U]

/-- The weighted integral tends to the product of the limiting constants.
The bound on each function follows from the heat maximum principle when
these functions are heat trajectories. -/
theorem weightedHeatIntegral_tendsto (μ : Measure U) [IsProbabilityMeasure μ]
    (c : ι → ℝ) (h : ι → ℝ → U → ℝ) (B m : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hmeas : ∀ i t, 0 ≤ t → Measurable (h i t))
    (hBound : ∀ i t, 0 ≤ t → ∀ x, 0 ≤ h i t x ∧ h i t x ≤ B i)
    (hLim : ∀ i x, Tendsto (fun t => h i t x) atTop (𝓝 (m i))) :
    Tendsto (fun t => ∫ x, weightedPowerProduct c (fun i => h i t x) ∂μ) atTop
      (𝓝 (weightedPowerProduct c m)) := by
  let P := fun t (x : U) => weightedPowerProduct c (fun i => h i t x)
  let C := weightedPowerProduct c B
  have ht : ∀ᶠ t : ℝ in atTop, 0 ≤ t := eventually_ge_atTop 0
  have hM : ∀ᶠ t in atTop, AEStronglyMeasurable (P t) μ := by
    filter_upwards [ht] with t ht'
    have hm : Measurable (P t) :=
      Finset.measurable_prod _ (fun i _ => (hmeas i t ht').pow_const (c i))
    exact hm.aestronglyMeasurable
  have hPBound : ∀ᶠ t in atTop, ∀ᵐ x ∂μ, ‖P t x‖ ≤ C := by
    filter_upwards [ht] with t ht'
    apply ae_of_all
    intro x
    have hPos : 0 ≤ P t x := Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg (hBound i t ht' x).1 _
    rw [Real.norm_of_nonneg hPos]
    exact Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hBound i t ht' x).1 _) fun i _ =>
      Real.rpow_le_rpow (hBound i t ht' x).1 (hBound i t ht' x).2 (hc i)
  have hPoint : ∀ᵐ x ∂μ, Tendsto (fun t => P t x) atTop (𝓝 (weightedPowerProduct c m)) := by
    apply ae_of_all
    intro x
    refine tendsto_finsetProd _ fun i _ => ?_
    exact (Real.continuousAt_rpow_const (m i) (c i) (Or.inr (hc i))).tendsto.comp (hLim i x)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    hM hPBound (integrable_const C) hPoint
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- Monotonicity on nonnegative times and the heat limit imply the desired
comparison at time zero. -/
theorem weightedHeatIntegral_le_of_mono_limit (μ : Measure U)
    (c : ι → ℝ) (h : ι → ℝ → U → ℝ) (m : ι → ℝ)
    (hMono : MonotoneOn (fun t => ∫ x, weightedPowerProduct c (fun i => h i t x) ∂μ) (Ici 0))
    (hLim : Tendsto (fun t => ∫ x, weightedPowerProduct c (fun i => h i t x) ∂μ) atTop
      (𝓝 (weightedPowerProduct c m))) :
    (∫ x, weightedPowerProduct c (fun i => h i 0 x) ∂μ) ≤ weightedPowerProduct c m := by
  apply ge_of_tendsto hLim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hMono (by simp) ht ht

end HeatLimit


end

end TypicalOrientations
