import SketchOrientation.WalshGaussian
import SketchOrientation.WalshSmallBall
import SketchOrientation.EdgeCap
import SketchOrientation.GaussianRadial

/-!
# Removing exact misses from the mean Walsh loss
The atom is temporarily assigned energy one. This preserves weak convergence,
and on small balls it leaves only the positive energies.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal BoundedContinuousFunction

noncomputable section
namespace SketchOrientation.Edge.Walsh

def repairedEnergy (y : ℝ) : ℝ := if y = 0 then 1 else y

private theorem measurable_repairedEnergy : Measurable repairedEnergy := by
  unfold repairedEnergy
  exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_id

private theorem measurable_repairedNormSq {ell : ℕ} :
    Measurable (fun x : Block ell => repairedEnergy (‖x‖^2)) :=
  measurable_repairedEnergy.comp (by fun_prop)

def repairedEnergyLaw (m s ell : ℕ) : ProbabilityMeasure ℝ :=
  (sampledBlockLaw m s ell).map (f := fun x => repairedEnergy (‖x‖^2))
    (measurable_repairedNormSq.aemeasurable)

private theorem tableBlock_energy {s ell : ℕ} (T : Fin s → Fin ell → Bool) :
    ‖tableBlock T‖^2 = walshTableEnergy T := by
  rw [EuclideanSpace.real_norm_sq_eq, walshTableEnergy_eq_normSq]
  rfl

private theorem integral_repairedEnergyLaw {m s ell : ℕ}
    [Nonempty (Fin s ↪ Label m)] [Nonempty (Fin ell ↪ Label m)]
    {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ x, g x ∂(repairedEnergyLaw m s ell : Measure ℝ)) =
      uniformMean (fun d : Draw m s ell => g (repairedEnergy (walshTableEnergy (table d)))) := by
  rw [repairedEnergyLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_repairedNormSq.aemeasurable) hg.aestronglyMeasurable,
    sampledBlockLaw_of_nonempty]
  change (∫ x, g (repairedEnergy (‖x‖^2)) ∂finiteLaw
    (tableBlock ∘ table : Draw m s ell → Block ell)) = _
  rw [integral_finiteLaw_eq_uniformMean]
  simp only [Function.comp_apply, tableBlock_energy]

private theorem measureReal_repairedEnergyLaw {m s ell : ℕ}
    [Nonempty (Fin s ↪ Label m)] [Nonempty (Fin ell ↪ Label m)]
    {S : Set ℝ} (hS : MeasurableSet S) :
    (repairedEnergyLaw m s ell : Measure ℝ).real S =
      uniformProbability (fun d : Draw m s ell => repairedEnergy (walshTableEnergy (table d)) ∈ S) := by
  have h := integral_repairedEnergyLaw (m := m) (s := s) (ell := ell)
    ((measurable_const (a := (1 : ℝ))).indicator hS)
  rw [integral_indicator hS, integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ, ← measureReal_def] at h
  rw [h]
  rfl

private theorem repairedEnergy_nonneg {m s ell : ℕ} :
    ∀ᵐ y ∂(repairedEnergyLaw m s ell : Measure ℝ), 0 ≤ y := by
  rw [repairedEnergyLaw, ProbabilityMeasure.toMeasure_map]
  exact (ae_map_iff measurable_repairedNormSq.aemeasurable
    (measurableSet_le measurable_const (measurable_id : Measurable (id : ℝ → ℝ)))).2 (by
    filter_upwards with x
    change 0 ≤ repairedEnergy (‖x‖^2)
    unfold repairedEnergy
    split <;> positivity)

private theorem tendsto_missProbability_zero {m s : ℕ → ℕ} {ell : ℕ} {he : 0 < ell}
    (hs : Tendsto s atTop atTop) (heven : ∀ᶠ i in atTop, Even (s i))
    (hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i)
    (hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i)
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0)) :
    Tendsto (fun i => missProbability (m i) (s i) ell) atTop (𝓝 0) := by
  have hscaled := tendsto_scaled_missProbability hs heven hr hc hgrowth
  have hx : Tendsto (fun i => (s i : ℝ) ^ ((ell : ℝ) / 2)) atTop atTop := by
    exact (tendsto_rpow_atTop (by positivity : 0 < (ell : ℝ) / 2)).comp
      (tendsto_natCast_atTop_atTop.comp hs)
  refine (hscaled.div_atTop hx).congr' ?_
  filter_upwards [hs.eventually_ge_atTop 1] with i hi
  have hi' : (0 : ℝ) < s i := by exact_mod_cast (show 0 < s i by omega)
  simp [mul_div_cancel_right₀, (Real.rpow_pos_of_pos hi' ((ell : ℝ) / 2)).ne']

def chiSquareProbability (ell : ℕ) (hell : 0 < ell) : ProbabilityMeasure ℝ :=
  ⟨chiSquareLaw ell, isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)⟩

private theorem tendsto_repairedEnergyLaw {m s : ℕ → ℕ} {ell : ℕ} (hell : 0 < ell)
    (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i)
    (hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i)
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0))
    (hBlock : Tendsto (fun i => sampledBlockLaw (m i) (s i) ell) atTop (𝓝 (gaussianBlockLaw ell))) :
    Tendsto (fun i => repairedEnergyLaw (m i) (s i) ell) atTop
      (𝓝 (chiSquareProbability ell hell)) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun g => ?_
  let k : Block ell →ᵇ ℝ := g.compContinuous ⟨fun x => ‖x‖^2, by fun_prop⟩
  let a (i : ℕ) := ∫ y, g y ∂(repairedEnergyLaw (m i) (s i) ell : Measure ℝ)
  let b (i : ℕ) := ∫ x, k x ∂(sampledBlockLaw (m i) (s i) ell : Measure (Block ell))
  have hb := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    hBlock k
  have hlim : (∫ x, k x ∂(gaussianBlockLaw ell : Measure (Block ell))) =
      ∫ y, g y ∂(chiSquareProbability ell hell : Measure ℝ) := by
    change (∫ x : Block ell, g (‖x‖^2) ∂stdGaussian (Block ell)) =
      ∫ y, g y ∂chiSquareLaw ell
    rw [← stdGaussian_norm_sq_map hell, integral_map (by fun_prop) g.continuous.aestronglyMeasurable]
  rw [hlim] at hb
  have hp := tendsto_missProbability_zero (he := hell) hs he hr hc hgrowth
  have hbound : ∀ᶠ i in atTop, ‖a i - b i‖ ≤ |g 1 - g 0| * missProbability (m i) (s i) ell := by
    filter_upwards [hr, hc] with i hri hci
    letI := label_embedding_nonempty (m := m i) hri
    letI := label_embedding_nonempty (m := m i) hci
    dsimp only [a,b]
    rw [integral_repairedEnergyLaw g.continuous.measurable, sampledBlockLaw_of_nonempty]
    change ‖uniformMean (fun d : Draw (m i) (s i) ell =>
      g (repairedEnergy (walshTableEnergy (table d)))) -
      (∫ x, k x ∂finiteLaw (tableBlock ∘ table : Draw (m i) (s i) ell → Block ell))‖ ≤ _
    rw [integral_finiteLaw_eq_uniformMean, Real.norm_eq_abs]
    have hpoint (d : Draw (m i) (s i) ell) :
        |g (repairedEnergy (walshTableEnergy (table d))) - k (tableBlock (table d))| ≤
        |g 1 - g 0| * indicator (walshTableEnergy (table d) = 0) := by
      change |g (repairedEnergy _) - g (‖tableBlock (table d)‖^2)| ≤ _
      rw [tableBlock_energy]
      by_cases h : walshTableEnergy (table d) = 0 <;> simp [repairedEnergy, indicator, h]
    refine (abs_uniformMean_sub_le hpoint).trans_eq ?_
    simp only [missProbability, uniformProbability, uniformMean, ← Finset.mul_sum, mul_div_assoc]
  have hd : Tendsto (fun i => a i - b i) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound (by simpa only [mul_zero] using (hp.const_mul |g 1 - g 0|))
  simpa only [zero_add, sub_add_cancel, a, b] using hd.add hb

private theorem chiSquare_ae_positive {ell : ℕ} :
    ∀ᵐ x ∂chiSquareLaw ell, (0 : ℝ) < x := by
  unfold chiSquareLaw gammaMeasure gammaPDF
  rw [ae_withDensity_iff ((measurable_gammaPDFReal _ _).ennreal_ofReal)]
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [hne] with x hx hpdf
  by_contra! h
  exact hpdf (gammaPDF_of_neg (lt_of_le_of_ne h hx))

private theorem chiSquare_integral_inverse {ell : ℕ} (hell : 2 < ell) :
    Integrable (fun x : ℝ => x⁻¹) (chiSquareLaw ell) ∧
    (∫ x, x⁻¹ ∂chiSquareLaw ell) = 1 / ((ell : ℝ) - 2) := by
  have hn := (chiSquare_ae_positive (ell := ell)).mono (fun x hx => inv_nonneg.2 hx.le)
  have hm : Measurable (fun x : ℝ => x⁻¹) := measurable_inv
  have hell' : (2 : ℝ) < ell := by exact_mod_cast hell
  refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hn, chiSquare_inverse_moment hell]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable,
      chiSquare_inverse_moment hell, ENNReal.toReal_ofReal (by positivity)]


private theorem integral_power_tail {r δ : ℝ} (hr : -1 < r) (hδ : 0 < δ) :
    (∫⁻ t in Ioc 0 δ, ENNReal.ofReal (t ^ r)) =
      ENNReal.ofReal (δ ^ (r + 1) / (r + 1)) := by
  have hi := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := δ) hr
  have hnonneg : ∀ᵐ t ∂(volume.restrict (Ioc 0 δ)), 0 ≤ t ^ r := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := δ))]
      with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1 hnonneg,
    ← intervalIntegral.integral_of_le hδ.le, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]

private theorem repairedEnergyLaw_vanishingCap {m s : ℕ → ℕ} {ell : ℕ} (hell : 2 < ell)
    (hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i)
    (hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i)
    (hSmall : ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in atTop, ∀ t : ℝ, 0 < t →
      uniformProbability (fun d : Draw (m i) (s i) ell =>
        0 < walshTableEnergy (table d) ∧ walshTableEnergy (table d) ≤ t) ≤
        C * t ^ ((ell : ℝ) / 2)) :
    VanishingCap (fun i => (repairedEnergyLaw (m i) (s i) ell : Measure ℝ)) id (fun _ => 0) := by
  obtain ⟨C, hC, hb⟩ := hSmall
  let r : ℝ := (ell : ℝ) / 2 - 2
  have hell' : (2 : ℝ) < ell := by exact_mod_cast hell
  have hRp : 0 < r + 1 := by dsimp [r]; linarith
  have hR : -1 < r := by linarith
  intro ε hε
  have ht : Tendsto (fun δ : ℝ => ENNReal.ofReal (C * (δ ^ (r + 1) / (r + 1))))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hbase : Tendsto (fun δ : ℝ => δ ^ (r + 1)) (𝓝 (0 : ℝ)) (𝓝 (0 ^ (r + 1))) :=
      (continuousAt_id.rpow_const (x := (0 : ℝ)) (Or.inr hRp.le)).tendsto
    have h' := (hbase.div_const (r + 1)).const_mul C
    simpa [Real.zero_rpow hRp.ne'] using ENNReal.tendsto_ofReal h'
  obtain ⟨δ, hδ, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ENNReal.ofReal (C * (δ ^ (r + 1) / (r + 1))) < ε := by
    have h₁ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (C * (δ ^ (r + 1) / (r + 1))) < ε :=
      (ht.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hε)
    have h₂ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 :=
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ)) (Iio_mem_nhds zero_lt_one)
    letI : NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_neBot _
    have h₃ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    obtain ⟨δ, ⟨hδε, hδ1⟩, hδ⟩ := (h₁.and h₂ |>.and h₃).exists
    exact ⟨δ, hδ, hδ1, hδε⟩
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hb, hr, hc] with i hi hri hci
  letI := label_embedding_nonempty (m := m i) hri
  letI := label_embedding_nonempty (m := m i) hci
  let μ := (repairedEnergyLaw (m i) (s i) ell : Measure ℝ)
  have hμ (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
      μ {y | id y ≤ t} ≤ ENNReal.ofReal (C * t ^ ((ell : ℝ) / 2)) := by
    have heq : μ {y | id y ≤ t} = ENNReal.ofReal (uniformProbability
        (fun d : Draw (m i) (s i) ell => repairedEnergy (walshTableEnergy (table d)) ∈ Iic t)) := by
      have hm := measureReal_repairedEnergyLaw (m := m i) (s := s i) (ell := ell)
        (S := Iic t) measurableSet_Iic
      rw [← hm, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rfl
    rw [heq]
    apply ENNReal.ofReal_le_ofReal
    have h := hi t ht
    refine le_trans (uniformProbability_mono ?_) h
    intro d hd
    let y := walshTableEnergy (table d)
    change repairedEnergy y ≤ t at hd
    change 0 < y ∧ y ≤ t
    have hy : 0 ≤ y := div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    by_cases hz : y = 0
    · simp only [repairedEnergy, hz, if_true] at hd
      linarith
    · exact ⟨lt_of_le_of_ne hy (Ne.symm hz), by simpa only [repairedEnergy, hz, if_false] using hd⟩
  have hle : capTail μ id 0 δ ≤ ENNReal.ofReal (C * (δ ^ (r + 1) / (r + 1))) := by
    calc
      _ ≤ ∫⁻ t in Ioc 0 δ, ENNReal.ofReal C * ENNReal.ofReal (t ^ r) := by
        unfold capTail
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := δ))]
          with t ht
        calc
          _ ≤ ENNReal.ofReal (1 / (t + 0)^2) * ENNReal.ofReal (C * t ^ ((ell : ℝ) / 2)) :=
            mul_le_mul' le_rfl (hμ t ht.1 (ht.2.trans_lt hδ1))
          _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC.le]
            congr 1
            rw [add_zero, show (1 : ℝ) / t^2 = t ^ (-(2 : ℝ)) by
              rw [Real.rpow_neg ht.1.le, Real.rpow_two, one_div]]
            rw [mul_left_comm, ← Real.rpow_add ht.1]
            congr 2
            dsimp [r]
            ring
      _ = _ := by
        rw [lintegral_const_mul _ (by fun_prop), integral_power_tail hR hδ,
          ← ENNReal.ofReal_mul hC.le]
  exact hle.trans_lt hδε


private theorem rankOneLoss_repairedEnergy (n L : ℝ) (ell : ℕ) (y : ℝ)
    (h : 0 < L - n⁻¹) :
    rankOneLoss n L ell y =
      n / (n - 1) * (L * indicator (y = 0) + L * gapRegularizer n 1 L *
        ((repairedEnergy y + gapRegularizer n 1 L)⁻¹ -
          (1 + gapRegularizer n 1 L)⁻¹ * indicator (y = 0))) - (ell : ℝ) / (n - 1) := by
  classical
  let b := gapRegularizer n 1 L
  have hb : b = (L - n⁻¹)⁻¹ := by simp [b, gapRegularizer]
  have hker : 1 + (L - n⁻¹) * y = (L - n⁻¹) * (y + b) := by
    rw [mul_add, hb, mul_inv_cancel₀ h.ne']
    ring
  by_cases hy : y = 0
  · simp [rankOneLoss, hy, indicator, repairedEnergy]
  · simp only [rankOneLoss, indicator, hy, if_false, repairedEnergy, mul_zero, zero_add,
      sub_zero, one_div]
    change n / (n - 1) * (L / (1 + (L - n⁻¹) * y)) - (ell : ℝ) / (n - 1) =
      n / (n - 1) * (L * b * (y + b)⁻¹) - (ell : ℝ) / (n - 1)
    rw [hker]
    simp only [div_eq_mul_inv, mul_inv, ← hb]
    ring

private theorem uniformMean_add' {A : Type*} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

private theorem uniformMean_mul' {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

private theorem meanLoss_sub_miss_eq {m s ell : ℕ}
    [Nonempty (Fin s ↪ Label m)] [Nonempty (Fin ell ↪ Label m)] (L : ℝ)
    (hnL : 0 < L - ((2 : ℝ)^m)⁻¹) :
    let n : ℝ := 2^m
    let b := gapRegularizer n 1 L
    meanLoss m s ell L - n / (n - 1) * L * missProbability m s ell =
      (n / (n - 1) * (L * b)) *
        ((∫ y, (y + b)⁻¹ ∂(repairedEnergyLaw m s ell : Measure ℝ)) -
          (1 + b)⁻¹ * missProbability m s ell) - (ell : ℝ) / (n - 1) := by
  dsimp only
  unfold meanLoss
  simp only [rankOneLoss_repairedEnergy _ _ _ _ hnL, uniformMean_sub, uniformMean_add',
    uniformMean_mul', uniformMean_const]
  rw [integral_repairedEnergyLaw (by fun_prop)]
  unfold missProbability uniformProbability
  ring

/-- Proposition 6.4, the remaining contribution after subtraction of the
exact zero atom, for every diverging gap. -/
theorem tendsto_meanLoss_sub_miss_of_block_tail {m s : ℕ → ℕ} {ell : ℕ} (hell : 2 < ell)
    (hm : Tendsto m atTop atTop) (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i)
    (hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i)
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0))
    (hBlock : Tendsto (fun i => sampledBlockLaw (m i) (s i) ell) atTop (𝓝 (gaussianBlockLaw ell)))
    (hSmall : ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in atTop, ∀ t : ℝ, 0 < t →
      uniformProbability (fun d : Draw (m i) (s i) ell =>
        0 < walshTableEnergy (table d) ∧ walshTableEnergy (table d) ≤ t) ≤
        C * t ^ ((ell : ℝ) / 2)) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto (fun i => meanLoss (m i) (s i) ell (L i) -
        (2 : ℝ)^m i / ((2 : ℝ)^m i - 1) * L i * missProbability (m i) (s i) ell)
      atTop (𝓝 (1 / ((ell : ℝ) - 2))) := by
  let n (i : ℕ) : ℝ := 2^m i
  let μ (i : ℕ) := repairedEnergyLaw (m i) (s i) ell
  let ν := chiSquareProbability ell (by omega)
  let b (i : ℕ) := if 0 < L i - (n i)⁻¹ then gapRegularizer (n i) 1 (L i) else 1
  have hn : Tendsto n atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hm
  have hbn : ∀ᶠ i in atTop, 0 < L i - (n i)⁻¹ := by
    filter_upwards [hn.eventually_ge_atTop 2, hL.eventually_ge_atTop 1] with i hi hLi
    have hni : 0 < n i := by linarith
    have hlt : (n i)⁻¹ < 1 := (inv_lt_one₀ hni).2 (by linarith)
    linarith
  have hb_eq : ∀ᶠ i in atTop, b i = gapRegularizer (n i) 1 (L i) :=
    hbn.mono fun i hi => if_pos hi
  have hbpos (i : ℕ) : 0 < b i := by
    dsimp only [b]
    split_ifs with h
    · simpa only [gapRegularizer, one_mul, inv_pos] using h
    · norm_num
  have hb0 : Tendsto b atTop (𝓝 0) :=
    (tendsto_gapRegularizer (show (0 : ℝ) < 1 by norm_num) hn hL).congr' (hb_eq.mono fun _ hi => hi.symm)
  have hell₀ : 0 < ell := by omega
  have hlu := tendsto_repairedEnergyLaw hell₀ hs he hr hc hgrowth hBlock
  have hTail := repairedEnergyLaw_vanishingCap hell hr hc hSmall
  obtain ⟨hint, hinv⟩ := chiSquare_integral_inverse hell
  let X (y : ℝ) := max y 0
  have hXpos : ∀ᵐ y ∂chiSquareLaw ell, 0 < X y :=
    chiSquare_ae_positive.mono (fun y hy => hy.trans_le (le_max_left _ _))
  have hinvEq : (fun y => (X y)⁻¹) =ᵐ[chiSquareLaw ell] (fun y => y⁻¹) :=
    chiSquare_ae_positive.mono (fun y hy => by simp [X, max_eq_left hy.le])
  have hTail' : VanishingCap (fun i => (μ i : Measure ℝ)) X (fun _ => 0) := by
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hTail ε hε
    refine ⟨δ, hδ, hbound.mono (fun i hi => ?_)⟩
    have heq : capTail (μ i : Measure ℝ) X 0 δ = capTail (μ i : Measure ℝ) id 0 δ := by
      unfold capTail
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := δ))]
        with t ht
      have ht₀ : 0 ≤ t := ht.1.le
      have heq : {y | X y ≤ t} = {y | id y ≤ t} := by ext y; simp [X, max_le_iff, ht₀]
      rw [heq]
    exact heq.symm ▸ hi
  have hlim :=
    (tendsto_inverseMean_for_all_iff (ι := Unit) hlu (X := fun _ => X)
      (fun _ => continuous_id.max continuous_const) (fun _ _ => le_max_right _ _)
      (fun _ => hXpos) (fun _ => hint.congr hinvEq.symm) () (fun _ _ => le_rfl)).2 hTail' b hbpos hb0
  have hμInv (i : ℕ) : inverseMean (μ i) (fun _ : Unit => X) (b i) =
      ∫ y, (y + b i)⁻¹ ∂(μ i : Measure ℝ) := by
    simp only [inverseMean, Fintype.sum_unique]
    apply integral_congr_ae
    filter_upwards [repairedEnergy_nonneg (m := m i) (s := s i) (ell := ell)] with y hy
    simp [X, max_eq_left hy]
  have hνInv : inverseMean ν (fun _ : Unit => X) 0 = 1 / ((ell : ℝ) - 2) := by
    simp only [inverseMean, Fintype.sum_unique, add_zero]
    exact (integral_congr_ae hinvEq).trans hinv
  have hmean : Tendsto (fun i => ∫ y, (y + b i)⁻¹ ∂(μ i : Measure ℝ))
      atTop (𝓝 (1 / ((ell : ℝ) - 2))) := by
    change Tendsto (fun i => inverseMean (μ i) (fun _ : Unit => X) (b i)) atTop
      (𝓝 (inverseMean ν (fun _ : Unit => X) 0)) at hlim
    simpa only [hμInv, hνInv] using hlim
  have hp := tendsto_missProbability_zero (he := hell₀) hs he hr hc hgrowth
  have hconst : Tendsto (fun i => (1 + b i)⁻¹ * missProbability (m i) (s i) ell) atTop (𝓝 0) := by
    have h := ((hb0.const_add 1).inv₀ (by norm_num)).mul hp
    simpa using h
  have hLb : Tendsto (fun i => L i * b i) atTop (𝓝 1) := by
    have h := (hn.inv_tendsto_atTop.mul hb0).const_add 1
    simp only [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [hb_eq, hbn] with i hi hni
    have heq : (L i - (n i)⁻¹) * b i = 1 := by
      rw [hi, gapRegularizer, one_mul, mul_inv_cancel₀ hni.ne']
    change 1 + (n i)⁻¹ * b i = L i * b i
    rw [sub_mul] at heq
    linarith only [heq]
  have hnratio : Tendsto (fun i => n i / (n i - 1)) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hn.inv_tendsto_atTop).inv₀ (by norm_num)
    simp only [sub_zero, inv_one] at h
    refine h.congr' ?_
    filter_upwards [hn.eventually_ge_atTop 2] with i hi
    have hni : n i ≠ 0 := by linarith
    have heq : 1 - (n i)⁻¹ = (n i - 1) / n i := by field_simp
    change (1 - (n i)⁻¹)⁻¹ = _
    rw [heq, inv_div]
  have hsub : Tendsto (fun i => (ell : ℝ) / (n i - 1)) atTop (𝓝 0) := by
    have hh : Tendsto (fun i => n i - 1) atTop atTop := by
      simpa only [sub_eq_add_neg] using hn.atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      hh.inv_tendsto_atTop.const_mul (ell : ℝ)
  have h := ((hnratio.mul hLb).mul (hmean.sub hconst)).sub hsub
  simp only [one_mul, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hb_eq, hbn, hr, hc] with i hi hbi hri hci
  letI := label_embedding_nonempty (m := m i) hri
  letI := label_embedding_nonempty (m := m i) hci
  dsimp only [μ]
  rw [hi]
  exact (meanLoss_sub_miss_eq (s := s i) (ell := ell) (L i) hbi).symm

/-- The same inverse-mean conclusion using the Walsh-specific coupling. -/
theorem tendsto_meanLoss_sub_miss {m s : ℕ → ℕ} {ell : ℕ} (hell : 2 < ell)
    (hm : Tendsto m atTop atTop) (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i)
    (hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i)
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0)) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto (fun i => meanLoss (m i) (s i) ell (L i) -
        (2 : ℝ)^m i / ((2 : ℝ)^m i - 1) * L i * missProbability (m i) (s i) ell)
      atTop (𝓝 (1 / ((ell : ℝ) - 2))) :=
  tendsto_meanLoss_sub_miss_of_block_tail hell hm hs he hr hc hgrowth
    (tendsto_sampledBlockLaw hs hr hc hgrowth)
    (eventually_positive_energy_smallBall hs he hr hc hgrowth) hL

end SketchOrientation.Edge.Walsh
