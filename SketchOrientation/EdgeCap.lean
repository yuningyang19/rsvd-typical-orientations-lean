import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Lower tails and the removal of the cap

The integral argument in `edge.tex`, lines 21–45. The lower-tail integral takes
values in `ℝ≥0∞` so that the unregularized integral can be infinite.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
namespace SketchOrientation.Edge

section CapIntegral
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The loss of one regularized reciprocal when its argument is capped from below. -/
def capDifference (b δ x : ℝ) : ℝ := (x + b)⁻¹ - (max x δ + b)⁻¹

/-- The integral of the lower tail up to the cap. The interval can omit either
endpoint because Lebesgue measure has no atoms. -/
def capTail (μ : Measure Ω) (X : Ω → ℝ) (b δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 δ, ENNReal.ofReal ((1 : ℝ) / (t + b) ^ 2) * μ {x | X x ≤ t}

theorem capDifference_nonneg {b δ x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    0 ≤ capDifference b δ x := by
  apply sub_nonneg.mpr
  have hp : 0 < x + b := by linarith
  exact inv_anti₀ hp (add_le_add_left (le_max_left _ _) _)

private theorem measurable_capDensity (b : ℝ) :
    Measurable (fun t : ℝ => ENNReal.ofReal ((1 : ℝ) / (t + b) ^ 2)) := by
  fun_prop

private theorem lintegral_reciprocal_sq {b x δ : ℝ} (hb : 0 < b) (hx : 0 ≤ x)
    (hxd : x ≤ δ) :
    (∫⁻ t in Ioc x δ, ENNReal.ofReal ((1 : ℝ) / (t + b) ^ 2)) =
      ENNReal.ofReal ((x + b)⁻¹ - (δ + b)⁻¹) := by
  have hcont : ContinuousOn (fun t : ℝ => 1 / (t + b) ^ 2) (Icc x δ) := by
    refine continuousOn_const.div ((continuous_id.add continuous_const).pow _).continuousOn ?_
    intro t ht
    exact pow_ne_zero _ (show t + b ≠ 0 by have := ht.1; linarith)
  have hi := hcont.intervalIntegrable_of_Icc (μ := volume) hxd
  have hderiv : ∀ t ∈ uIcc x δ,
      HasDerivAt (fun v : ℝ => (v + b)⁻¹) (-1 / (t + b) ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hxd] at ht
    have htb : t + b ≠ 0 := by have := ht.1; linarith
    exact ((hasDerivAt_id t).add_const b).inv htb
  have hi' : IntervalIntegrable (fun t : ℝ => -1 / (t + b) ^ 2) volume x δ := by
    convert hi.neg using 1
    funext t
    simp [Pi.neg_apply, neg_div]
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi'
  simp_rw [neg_div] at heq
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le hxd] at heq
  have ha : ∀ᵐ t : ℝ ∂volume.restrict (Ioc x δ), 0 ≤ (1 : ℝ) / (t + b) ^ 2 :=
    ae_of_all _ (fun _ => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1 ha]
  congr 1
  linarith

private theorem capDifference_indicator {b δ x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    (∫⁻ t in Ioc 0 δ, (Ici x).indicator
      (fun v => ENNReal.ofReal ((1 : ℝ) / (v + b) ^ 2)) t) =
      ENNReal.ofReal (capDifference b δ x) := by
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have heq : (Ici x ∩ Ioc 0 δ : Set ℝ) =ᵐ[(volume : Measure ℝ)] Ioc x δ := by
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ x := ae_iff.mpr (by simp)
    filter_upwards [hne] with t ht
    apply propext
    change (x ≤ t ∧ 0 < t ∧ t ≤ δ) ↔ (x < t ∧ t ≤ δ)
    constructor
    · rintro ⟨h, _, hd⟩
      exact ⟨lt_of_le_of_ne h (Ne.symm ht), hd⟩
    · rintro ⟨h, hd⟩
      exact ⟨h.le, hx.trans_lt h, hd⟩
  rw [Measure.restrict_congr_set heq]
  by_cases hxd : x ≤ δ
  · rw [lintegral_reciprocal_sq hb hx hxd, capDifference, max_eq_right hxd]
  · rw [Ioc_eq_empty (by linarith), capDifference, max_eq_left (by linarith)]
    simp

/-- The paper's identity (lines 26–30) after taking expectations. -/
theorem capTail_eq_lintegral_capDifference (μ : Measure Ω) [SFinite μ] {X : Ω → ℝ}
    (hX : Measurable X) (hX₀ : ∀ᵐ x ∂μ, 0 ≤ X x) {b δ : ℝ} (hb : 0 < b) :
    capTail μ X b δ = ∫⁻ x, ENNReal.ofReal (capDifference b δ (X x)) ∂μ := by
  let density := fun t : ℝ => ENNReal.ofReal ((1 : ℝ) / (t + b) ^ 2)
  let f := fun (x : Ω) (t : ℝ) => (Ici (X x)).indicator density t
  have hm : Measurable (Function.uncurry f) := by
    have hs : MeasurableSet {p : Ω × ℝ | X p.1 ≤ p.2} :=
      measurableSet_le (hX.comp measurable_fst) measurable_snd
    convert ((measurable_capDensity b).comp measurable_snd).indicator hs using 1
    ext ⟨x, t⟩
    by_cases ht : X x ≤ t <;> simp [f, density, Function.uncurry, ht]
  have hinner (t : ℝ) : (∫⁻ x, f x t ∂μ) = density t * μ {x | X x ≤ t} := by
    have heq : (fun x => f x t) = ({x | X x ≤ t} : Set Ω).indicator (fun _ => density t) := by
      ext x
      by_cases ht : X x ≤ t <;> simp [f, ht]
    rw [heq, lintegral_indicator_const (measurableSet_le hX measurable_const)]
  change (∫⁻ t in Ioc 0 δ, density t * μ {x | X x ≤ t}) = _
  simp_rw [← hinner]
  rw [← lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hX₀] with x hx
  exact capDifference_indicator hb hx

/-- Raising the lower cap increases the integral. -/
theorem capTail_mono_cutoff (μ : Measure Ω) (X : Ω → ℝ) (b : ℝ) :
    Monotone (capTail μ X b) := by
  intro a c hac
  exact lintegral_mono' (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right hac)) le_rfl

/-- A larger nonnegative regularizer decreases the lower-tail integral. -/
theorem capTail_anti_regularizer (μ : Measure Ω) (X : Ω → ℝ)
    {a b δ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    capTail μ X b δ ≤ capTail μ X a δ := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := δ))]
    with t ht
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 < t + a := lt_add_of_pos_of_le ht.1 ha
  apply one_div_le_one_div_of_le (sq_pos_of_pos hp)
  gcongr

/-- A positive decreasing sequence cofinal at zero. -/
def inverseIndex (j : ℕ) : ℝ := ((j : ℝ) + 1)⁻¹

private theorem inverseIndex_pos (j : ℕ) : 0 < inverseIndex j := by
  unfold inverseIndex
  positivity

private theorem inverseIndex_anti : Antitone inverseIndex := by
  intro i j hij
  unfold inverseIndex
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)

private theorem inverseIndex_tendsto : Tendsto inverseIndex atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ))
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Monotone convergence for the regularizer as it decreases to zero. -/
theorem capTail_eq_iSup_regularizer (μ : Measure Ω) (X : Ω → ℝ) (δ : ℝ) :
    capTail μ X 0 δ = ⨆ j : ℕ, capTail μ X (inverseIndex j) δ := by
  let F := fun (b t : ℝ) => ENNReal.ofReal ((1 : ℝ) / (t + b) ^ 2) * μ {x | X x ≤ t}
  have hanti {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t) :
      F b t ≤ F a t := by
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le (sq_pos_of_pos (by linarith : 0 < t + a))
    gcongr
  have hF (b : ℝ) : Measurable (F b) := by
    refine (measurable_capDensity b).mul (?_ : Measurable (fun t => μ {x | X x ≤ t}))
    apply Monotone.measurable
    intro x y hxy
    exact measure_mono (fun _ hx => le_trans hx hxy)
  change (∫⁻ t in Ioc 0 δ, F 0 t) = ⨆ j : ℕ, ∫⁻ t in Ioc 0 δ, F (inverseIndex j) t
  rw [← lintegral_iSup_ae (fun j => hF (inverseIndex j))]
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := δ))]
      with t ht
    have hlim : Tendsto (fun j => F (inverseIndex j) t) atTop (𝓝 (F 0 t)) := by
      have hzero : t + (0 : ℝ) ≠ 0 := by simpa using ht.1.ne'
      have hbase : Tendsto (fun j => t + inverseIndex j) atTop (𝓝 (t + 0)) :=
        tendsto_const_nhds.add inverseIndex_tendsto
      apply ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (1 : ℝ))).div
          (hbase.pow 2) (pow_ne_zero _ hzero)))
      exact Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos one_pos (sq_pos_of_ne_zero hzero))))
    have hmono : Monotone (fun j => F (inverseIndex j) t) :=
      fun i j hij => hanti (inverseIndex_pos j).le (inverseIndex_anti hij) ht.1
    exact tendsto_nhds_unique hlim (tendsto_atTop_iSup hmono)
  · intro j
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := δ))]
      with t ht
    exact hanti (inverseIndex_pos _).le (inverseIndex_anti (Nat.le_succ _)) ht.1

/-- Quantifier form of the nonnegative nested lower-tail limit. -/
def VanishingCap (μ : ℕ → Measure Ω) (X : Ω → ℝ) (b : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ n in atTop, capTail (μ n) X (b n) δ < ε

theorem vanishingCap_iff_iInf_limsup (μ : ℕ → Measure Ω) (X : Ω → ℝ) (b : ℕ → ℝ) :
    VanishingCap μ X b ↔
      (⨅ δ : {δ : ℝ // 0 < δ}, limsup (fun n => capTail (μ n) X (b n) δ) atTop) = 0 := by
  let U := fun δ : {δ : ℝ // 0 < δ} => limsup (fun n => capTail (μ n) X (b n) δ) atTop
  change VanishingCap μ X b ↔ (⨅ δ, U δ) = 0
  constructor
  · intro h
    apply bot_unique
    by_contra! hpos
    obtain ⟨ε, hε, hlt⟩ := exists_between hpos
    obtain ⟨δ, hδ, hn⟩ := h ε hε
    exact (not_lt_of_ge ((iInf_le U ⟨δ, hδ⟩).trans
      (limsup_le_of_le (by isBoundedDefault) (hn.mono fun _ h => h.le)))) hlt
  · intro h ε hε
    obtain ⟨δ, hd⟩ : ∃ δ, U δ < ε := by
      by_contra! hf
      exact (not_le_of_gt hε) (h ▸ le_iInf hf)
    exact ⟨δ, δ.2, eventually_lt_of_limsup_lt hd (by isBoundedDefault)⟩

/-- The condition at zero is equivalent to the condition along all positive
regularizers converging to zero. The converse chooses a regularizer that
preserves the bad tail at each of an increasing collection of cutoffs. -/
theorem vanishingCap_all_iff (μ : ℕ → Measure Ω) (X : Ω → ℝ) :
    (∀ b : ℕ → ℝ, (∀ n, 0 < b n) → Tendsto b atTop (𝓝 0) → VanishingCap μ X b) ↔
      VanishingCap μ X (fun _ => 0) := by
  constructor
  · intro hall
    by_contra hzero
    obtain ⟨ε, hε, hbad⟩ : ∃ ε : ℝ≥0∞, 0 < ε ∧
        ∀ δ : ℝ, 0 < δ → ∃ᶠ n in atTop, ε ≤ capTail (μ n) X 0 δ := by
      unfold VanishingCap at hzero
      push Not at hzero
      obtain ⟨ε, hε, hbad⟩ := hzero
      exact ⟨ε, hε, hbad⟩
    obtain ⟨a, ha, haε⟩ := exists_between hε
    have hchoose (n N : ℕ) : ∃ b : ℝ, 0 < b ∧ b ≤ inverseIndex n ∧
        ∀ j < N, a < capTail (μ n) X 0 (inverseIndex j) →
          a < capTail (μ n) X b (inverseIndex j) := by
      induction N with
      | zero => exact ⟨inverseIndex n, inverseIndex_pos n, le_rfl, by simp⟩
      | succ N ih =>
        obtain ⟨b, hb, hbn, hbprop⟩ := ih
        by_cases hbadN : a < capTail (μ n) X 0 (inverseIndex N)
        · rw [capTail_eq_iSup_regularizer] at hbadN
          obtain ⟨j, hj⟩ := lt_iSup_iff.mp hbadN
          refine ⟨min b (inverseIndex j), lt_min hb (inverseIndex_pos j),
            (min_le_left _ _).trans hbn, ?_⟩
          intro i hi hbadI
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact (hbprop i hi' hbadI).trans_le
              (capTail_anti_regularizer _ _ (le_min hb.le (inverseIndex_pos j).le) (min_le_left _ _))
          · exact hj.trans_le
              (capTail_anti_regularizer _ _ (le_min hb.le (inverseIndex_pos j).le) (min_le_right _ _))
        · exact ⟨b, hb, hbn, fun i hi hbadI => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
            · exact hbprop i hi' hbadI
            · exact (hbadN hbadI).elim⟩
    choose b hb hb_le hbprop using fun n => hchoose n n
    have hbt : Tendsto b atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds inverseIndex_tendsto
        (fun n => (hb n).le) hb_le
    obtain ⟨δ, hδ, hgood⟩ := hall b hb hbt a ha
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    have hj' : inverseIndex j ≤ δ := by simpa [inverseIndex, one_div] using hj.le
    have hfreq := (hbad (inverseIndex j) (inverseIndex_pos j)).and_eventually (eventually_gt_atTop j)
    exact hfreq <| hgood.mono fun n hn hh =>
      (not_lt_of_gt hn) <| (hbprop n j hh.2 (haε.trans_le hh.1)).trans_le
        (capTail_mono_cutoff (μ n) X (b n) hj')
  · intro hz b hb _ ε hε
    obtain ⟨δ, hδ, hn⟩ := hz ε hε
    exact ⟨δ, hδ, hn.mono fun n h =>
      (capTail_anti_regularizer (μ n) X le_rfl (hb n).le).trans_lt h⟩

end CapIntegral
section SpectrumCap

variable {Ω ι : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [Fintype ι]

/-- The mean of the sum of regularized reciprocals. -/
def inverseMean (μ : ProbabilityMeasure Ω) (X : ι → Ω → ℝ) (b : ℝ) : ℝ :=
  ∑ i, ∫ ω, (X i ω + b)⁻¹ ∂(μ : Measure Ω)

/-- The corresponding mean after capping each spectral coordinate from below. -/
def cappedInverseMean (μ : ProbabilityMeasure Ω) (X : ι → Ω → ℝ) (b δ : ℝ) : ℝ :=
  ∑ i, ∫ ω, (max (X i ω) δ + b)⁻¹ ∂(μ : Measure Ω)

omit [TopologicalSpace Ω] [BorelSpace Ω] in
private theorem integrable_inv_of_lower_bound (μ : ProbabilityMeasure Ω) {f : Ω → ℝ}
    (hf : Measurable f) {c : ℝ} (hc : 0 < c) (hfc : ∀ ω, c ≤ f ω) :
    Integrable (fun ω => (f ω)⁻¹) (μ : Measure Ω) :=
  Integrable.of_bound (hf.inv.aestronglyMeasurable) c⁻¹ <| ae_of_all _ fun ω => by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (hc.le.trans (hfc ω)))]
    exact inv_anti₀ hc (hfc ω)

private theorem capDifference_antitoneOn {b δ x y : ℝ} (hb : 0 < b) (hx : 0 ≤ x)
    (hxy : x ≤ y) : capDifference b δ y ≤ capDifference b δ x := by
  by_cases hyδ : y ≤ δ
  · simp only [capDifference, max_eq_right hyδ, max_eq_right (hxy.trans hyδ)]
    exact sub_le_sub_right (inv_anti₀ (by linarith) (by linarith)) _
  · rw [capDifference, max_eq_left (le_of_not_ge hyδ), sub_self]
    exact capDifference_nonneg hb hx

omit [TopologicalSpace Ω] [BorelSpace Ω] in
private theorem capTail_eq_ofReal_integral (μ : ProbabilityMeasure Ω) {X : Ω → ℝ}
    (hX : Measurable X) (hX₀ : ∀ ω, 0 ≤ X ω) {b δ : ℝ} (hb : 0 < b) :
    capTail (μ : Measure Ω) X b δ =
      ENNReal.ofReal (∫ ω, capDifference b δ (X ω) ∂(μ : Measure Ω)) := by
  rw [capTail_eq_lintegral_capDifference _ hX (ae_of_all _ hX₀) hb]
  symm
  have h1 := integrable_inv_of_lower_bound μ (hX.add_const b) hb (fun ω => by linarith [hX₀ ω])
  have h2 := integrable_inv_of_lower_bound μ ((hX.max measurable_const).add_const b) hb
    (fun ω => by linarith [hX₀ ω, le_max_left (X ω) δ])
  exact ofReal_integral_eq_lintegral_ofReal (h1.sub h2)
    (ae_of_all _ (fun ω => capDifference_nonneg hb (hX₀ ω)))

/-- Bound the exact error from removing the cap by the tail of the smallest
coordinate, with the factor equal to the number of coordinates. -/
theorem inverseMean_sub_capped_bounds (μ : ProbabilityMeasure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Continuous (X i)) (hX₀ : ∀ i ω, 0 ≤ X i ω)
    (i₀ : ι) (hmin : ∀ i ω, X i₀ ω ≤ X i ω) {b δ : ℝ} (hb : 0 < b) :
    let T := (capTail (μ : Measure Ω) (X i₀) b δ).toReal
    T ≤ inverseMean μ X b - cappedInverseMean μ X b δ ∧
      inverseMean μ X b - cappedInverseMean μ X b δ ≤ (Fintype.card ι : ℝ) * T := by
  classical
  have hd (i : ι) : Integrable (fun ω => capDifference b δ (X i ω)) (μ : Measure Ω) := by
    have h1 := integrable_inv_of_lower_bound μ ((hX i).measurable.add_const b) hb
      (fun ω => by linarith [hX₀ i ω])
    have h2 := integrable_inv_of_lower_bound μ (((hX i).measurable.max measurable_const).add_const b) hb
      (fun ω => by linarith [hX₀ i ω, le_max_left (X i ω) δ])
    exact h1.sub h2
  have hnonneg (i : ι) : 0 ≤ ∫ ω, capDifference b δ (X i ω) ∂(μ : Measure Ω) :=
    integral_nonneg (fun ω => capDifference_nonneg hb (hX₀ i ω))
  have heq : inverseMean μ X b - cappedInverseMean μ X b δ =
      ∑ i, ∫ ω, capDifference b δ (X i ω) ∂(μ : Measure Ω) := by
    unfold inverseMean cappedInverseMean
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    symm
    exact integral_sub
      (integrable_inv_of_lower_bound μ ((hX i).measurable.add_const b) hb
        (fun ω => by linarith [hX₀ i ω]))
      (integrable_inv_of_lower_bound μ (((hX i).measurable.max measurable_const).add_const b) hb
        (fun ω => by linarith [hX₀ i ω, le_max_left (X i ω) δ]))
  dsimp
  rw [heq, capTail_eq_ofReal_integral μ (hX i₀).measurable (hX₀ i₀) hb,
    ENNReal.toReal_ofReal (hnonneg i₀)]
  constructor
  · exact Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ i₀)
  · calc
      _ ≤ ∑ _:ι, ∫ ω, capDifference b δ (X i₀ ω) ∂(μ : Measure Ω) :=
        Finset.sum_le_sum fun i _ => integral_mono_ae (hd i) (hd i₀) <|
          ae_of_all _ fun ω => capDifference_antitoneOn hb (hX₀ i₀ ω) (hmin i ω)
      _ = _ := by simp [nsmul_eq_mul]

private theorem capped_shift_bounds {x b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ) :
    0 ≤ (max x δ)⁻¹ - (max x δ + b)⁻¹ ∧
      (max x δ)⁻¹ - (max x δ + b)⁻¹ ≤ b / δ ^ 2 := by
  have hm : 0 < max x δ := hδ.trans_le (le_max_right _ _)
  have hmb : 0 < max x δ + b := by linarith
  have heq : (max x δ)⁻¹ - (max x δ + b)⁻¹ = b / (max x δ * (max x δ + b)) := by
    field_simp
    ring
  rw [heq]
  exact ⟨by positivity, div_le_div_of_nonneg_left hb (sq_pos_of_pos hδ) (by
    rw [pow_two]
    exact mul_le_mul (le_max_right _ _) (by linarith [le_max_right x δ]) hδ.le hm.le)⟩

private theorem tendsto_capped_coordinate {μ : ℕ → ProbabilityMeasure Ω}
    {ν : ProbabilityMeasure Ω} (hμ : Tendsto μ atTop (𝓝 ν)) {X : Ω → ℝ}
    (hX : Continuous X) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (hbt : Tendsto b atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => ∫ ω, (max (X ω) δ + b n)⁻¹ ∂(μ n : Measure Ω)) atTop
      (𝓝 (∫ ω, (max (X ω) δ)⁻¹ ∂(ν : Measure Ω))) := by
  let f : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun ω => (max (X ω) δ)⁻¹, (hX.max continuous_const).inv₀
      (fun ω => (hδ.trans_le (le_max_right _ _)).ne')⟩ δ⁻¹ (fun x y => by
      rw [Real.dist_eq]
      change |(max (X x) δ)⁻¹ - (max (X y) δ)⁻¹| ≤ δ⁻¹
      have hx : 0 ≤ (max (X x) δ)⁻¹ := by positivity
      have hy : 0 ≤ (max (X y) δ)⁻¹ := by positivity
      have hx' : (max (X x) δ)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (le_max_right _ _)
      have hy' : (max (X y) δ)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (le_max_right _ _)
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
  have hweak := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
  change Tendsto (fun n => ∫ ω, (max (X ω) δ)⁻¹ ∂(μ n : Measure Ω)) atTop
    (𝓝 (∫ ω, (max (X ω) δ)⁻¹ ∂(ν : Measure Ω))) at hweak
  have hbound (n : ℕ) :
      (∫ ω, (max (X ω) δ)⁻¹ ∂(μ n : Measure Ω)) - b n / δ ^ 2 ≤
        ∫ ω, (max (X ω) δ + b n)⁻¹ ∂(μ n : Measure Ω) := by
    have h1 := integrable_inv_of_lower_bound (μ n) (hX.measurable.max measurable_const)
      hδ (fun ω => le_max_right _ _)
    have h2 := integrable_inv_of_lower_bound (μ n)
      ((hX.measurable.max measurable_const).add_const (b n)) hδ
      (fun ω => by linarith [le_max_right (X ω) δ, hb n])
    have hc : Integrable (fun _ : Ω => b n / δ ^ 2) (μ n : Measure Ω) :=
      integrable_const _
    have heq : (∫ _ : Ω, b n / δ ^ 2 ∂(μ n : Measure Ω)) = b n / δ ^ 2 := by simp
    rw [← heq, ← integral_sub h1 hc]
    exact integral_mono_ae (h1.sub hc) h2 <|
      ae_of_all _ fun ω => by linarith [(capped_shift_bounds (x := X ω) (hb n) hδ).2]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ hweak hbound ?_
  · simpa using hweak.sub (hbt.div_const (δ ^ 2))
  · intro n
    have h1 := integrable_inv_of_lower_bound (μ n) (hX.measurable.max measurable_const)
      hδ (fun ω => le_max_right _ _)
    have h2 := integrable_inv_of_lower_bound (μ n)
      ((hX.measurable.max measurable_const).add_const (b n)) hδ
      (fun ω => by linarith [le_max_right (X ω) δ, hb n])
    exact integral_mono_ae h2 h1 <|
      ae_of_all _ fun ω => sub_nonneg.mp (capped_shift_bounds (x := X ω) (hb n) hδ).1

theorem tendsto_cappedInverseMean {μ : ℕ → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    (hμ : Tendsto μ atTop (𝓝 ν)) {X : ι → Ω → ℝ} (hX : ∀ i, Continuous (X i))
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (hbt : Tendsto b atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => cappedInverseMean (μ n) X (b n) δ) atTop (𝓝 (cappedInverseMean ν X 0 δ)) := by
  simpa [cappedInverseMean] using
    tendsto_finsetSum Finset.univ (fun i _ => tendsto_capped_coordinate hμ (hX i) hb hbt hδ)

private theorem tendsto_limit_cappedInverseMean (ν : ProbabilityMeasure Ω) {X : ι → Ω → ℝ}
    (hX : ∀ i, Continuous (X i))
    (hpos : ∀ i, ∀ᵐ ω ∂(ν : Measure Ω), 0 < X i ω)
    (hint : ∀ i, Integrable (fun ω => (X i ω)⁻¹) (ν : Measure Ω)) :
    Tendsto (fun j => cappedInverseMean ν X 0 (inverseIndex j)) atTop (𝓝 (inverseMean ν X 0)) := by
  simp only [cappedInverseMean, inverseMean, add_zero]
  apply tendsto_finsetSum
  intro i _
  refine tendsto_integral_of_dominated_convergence (fun ω => (X i ω)⁻¹) ?_ (hint i) ?_ ?_
  · intro j
    exact (((hX i).measurable.max measurable_const).inv).aestronglyMeasurable
  · intro j
    filter_upwards [hpos i] with ω hω
    have hm : 0 < max (X i ω) (inverseIndex j) := hω.trans_le (le_max_left _ _)
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hm.le)]
    exact inv_anti₀ hω (le_max_left _ _)
  · filter_upwards [hpos i] with ω hω
    have h := (tendsto_const_nhds (x := X i ω)).max inverseIndex_tendsto
    rw [max_eq_left hω.le] at h
    exact h.inv₀ hω.ne'

/-- The cap criterion under weak convergence, with a general limiting law having
integrable unregularized reciprocals. The Gaussian moment and the continuity
of the ordered matrix spectrum are separate representation obligations. -/
theorem tendsto_inverseMean_iff_vanishingCap {μ : ℕ → ProbabilityMeasure Ω}
    {ν : ProbabilityMeasure Ω} (hμ : Tendsto μ atTop (𝓝 ν)) {X : ι → Ω → ℝ}
    (hX : ∀ i, Continuous (X i)) (hX₀ : ∀ i ω, 0 ≤ X i ω)
    (hpos : ∀ i, ∀ᵐ ω ∂(ν : Measure Ω), 0 < X i ω)
    (hint : ∀ i, Integrable (fun ω => (X i ω)⁻¹) (ν : Measure Ω))
    (i₀ : ι) (hmin : ∀ i ω, X i₀ ω ≤ X i ω)
    {b : ℕ → ℝ} (hb : ∀ n, 0 < b n) (hbt : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => inverseMean (μ n) X (b n)) atTop (𝓝 (inverseMean ν X 0)) ↔
      VanishingCap (fun n => (μ n : Measure Ω)) (X i₀) b := by
  let T := fun n δ => capTail (μ n : Measure Ω) (X i₀) (b n) δ
  have hfin (n : ℕ) (δ : ℝ) : T n δ ≠ ∞ := by
    dsimp [T]
    rw [capTail_eq_ofReal_integral (μ n) (hX i₀).measurable (hX₀ i₀) (hb n)]
    exact ENNReal.ofReal_ne_top
  have hreal :
      VanishingCap (fun n => (μ n : Measure Ω)) (X i₀) b ↔
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, (T n δ).toReal < ε := by
    constructor
    · intro h ε hε
      obtain ⟨δ, hδ, he⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
      exact ⟨δ, hδ, he.mono fun n hn => by
        simpa [ENNReal.toReal_ofReal hε.le] using
          (ENNReal.toReal_lt_toReal (hfin n δ) ENNReal.ofReal_ne_top).mpr hn⟩
    · intro h ε hε
      obtain ⟨a, hapos, haε⟩ := exists_between hε
      have hafin := (haε.trans_le le_top).ne
      obtain ⟨δ, hδ, he⟩ := h a.toReal (ENNReal.toReal_pos hapos.ne' hafin)
      exact ⟨δ, hδ, he.mono fun n hn =>
        ((ENNReal.toReal_lt_toReal (hfin n δ) hafin).mp hn).trans haε⟩
  let m := inverseMean ν X 0
  let c := fun δ => cappedInverseMean ν X 0 δ
  have hlim := tendsto_limit_cappedInverseMean ν hX hpos hint
  have hcap (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => cappedInverseMean (μ n) X (b n) δ) atTop (𝓝 (c δ)) :=
    tendsto_cappedInverseMean hμ hX (fun n => (hb n).le) hbt hδ
  have hrem (n : ℕ) (δ : ℝ) :=
    inverseMean_sub_capped_bounds (μ n) X hX hX₀ i₀ hmin (δ := δ) (hb n)
  rw [hreal]
  constructor
  · intro h ε hε
    obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.mp hlim (ε / 3) (by positivity)).exists
    refine ⟨inverseIndex j, inverseIndex_pos j, ?_⟩
    have he1 := Metric.tendsto_nhds.mp h (ε / 3) (by positivity)
    have he2 := Metric.tendsto_nhds.mp (hcap (inverseIndex j) (inverseIndex_pos j))
      (ε / 3) (by positivity)
    filter_upwards [he1, he2] with n hn1 hn2
    rw [Real.dist_eq, abs_lt] at hn1 hn2 hj
    have hT := (hrem n (inverseIndex j)).1
    dsimp [T, c, m] at *
    linarith [hn1.2, hn2.1, hj.1]
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let q : ℝ := Fintype.card ι
    let η := ε / (3 * (q + 1))
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hη : 0 < η := by dsimp [η]; positivity
    have hconst : q * η ≤ ε / 3 := by
      calc
        _ ≤ (q + 1) * η := mul_le_mul_of_nonneg_right (by linarith) hη.le
        _ = _ := by
          dsimp [η]
          have : q + 1 ≠ 0 := by linarith
          field_simp
    obtain ⟨δ, hδ, htail⟩ := h η hη
    obtain ⟨j, hj, hjdist⟩ := ((tendsto_order.mp inverseIndex_tendsto).2 δ hδ).and
      (Metric.tendsto_nhds.mp hlim (ε / 3) (by positivity)) |>.exists
    have he2 := Metric.tendsto_nhds.mp (hcap (inverseIndex j) (inverseIndex_pos j))
      (ε / 3) (by positivity)
    filter_upwards [he2, htail] with n hn2 hnT
    rw [Real.dist_eq, abs_lt] at hn2 hjdist ⊢
    have hT₀ : 0 ≤ (T n (inverseIndex j)).toReal := ENNReal.toReal_nonneg
    have hTη : (T n (inverseIndex j)).toReal ≤ η :=
      (ENNReal.toReal_mono (hfin n δ) (capTail_mono_cutoff (μ n : Measure Ω)
        (X i₀) (b n) hj.le)).trans hnT.le
    have hupper := (mul_le_mul_of_nonneg_left hTη hq).trans hconst
    have hr := hrem n (inverseIndex j)
    dsimp [T, c, m, q] at *
    exact ⟨by linarith [hr.1, hn2.1, hjdist.1], by linarith [hr.2, hn2.2, hjdist.2]⟩

/-- Both directions of the all-regularizers version for weakly convergent laws. -/
theorem tendsto_inverseMean_for_all_iff {μ : ℕ → ProbabilityMeasure Ω}
    {ν : ProbabilityMeasure Ω} (hμ : Tendsto μ atTop (𝓝 ν)) {X : ι → Ω → ℝ}
    (hX : ∀ i, Continuous (X i)) (hX₀ : ∀ i ω, 0 ≤ X i ω)
    (hpos : ∀ i, ∀ᵐ ω ∂(ν : Measure Ω), 0 < X i ω)
    (hint : ∀ i, Integrable (fun ω => (X i ω)⁻¹) (ν : Measure Ω))
    (i₀ : ι) (hmin : ∀ i ω, X i₀ ω ≤ X i ω) :
    (∀ b : ℕ → ℝ, (∀ n, 0 < b n) → Tendsto b atTop (𝓝 0) →
      Tendsto (fun n => inverseMean (μ n) X (b n)) atTop (𝓝 (inverseMean ν X 0))) ↔
      VanishingCap (fun n => (μ n : Measure Ω)) (X i₀) (fun _ => 0) := by
  rw [← vanishingCap_all_iff]
  constructor
  · intro h b hb hbt
    exact (tendsto_inverseMean_iff_vanishingCap hμ hX hX₀ hpos hint i₀ hmin hb hbt).mp
      (h b hb hbt)
  · intro h b hb hbt
    exact (tendsto_inverseMean_iff_vanishingCap hμ hX hX₀ hpos hint i₀ hmin hb hbt).mpr
      (h b hb hbt)

end SpectrumCap
section GapNormalization

/-- The inverse regularizer for the paper's gap parameter `L = Γ/(nk)`. -/
def gapRegularizer (n k L : ℝ) : ℝ := (k * L - n⁻¹)⁻¹

/-- The gap with a specified positive inverse regularizer. -/
def gapOfRegularizer (n k b : ℝ) : ℝ := (b⁻¹ + n⁻¹) / k

theorem gapRegularizer_gapOfRegularizer (n : ℝ) {k b : ℝ} (hk : 0 < k) :
    gapRegularizer n k (gapOfRegularizer n k b) = b := by
  simp [gapRegularizer, gapOfRegularizer, mul_div_cancel₀ _ hk.ne']

theorem tendsto_gapRegularizer {n L : ℕ → ℝ} {k : ℝ} (hk : 0 < k)
    (hn : Tendsto n atTop atTop) (hL : Tendsto L atTop atTop) :
    Tendsto (fun j => gapRegularizer (n j) k (L j)) atTop (𝓝 0) := by
  have h : Tendsto (fun j => k * L j - (n j)⁻¹) atTop atTop := by
    simpa only [sub_eq_add_neg, Pi.inv_apply] using
      (hL.const_mul_atTop hk).atTop_add hn.inv_tendsto_atTop.neg
  exact h.inv_tendsto_atTop

theorem tendsto_gapOfRegularizer {n b : ℕ → ℝ} {k : ℝ} (hk : 0 < k)
    (hn : Tendsto n atTop atTop) (hb : ∀ j, 0 < b j) (hbt : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun j => gapOfRegularizer (n j) k (b j)) atTop atTop := by
  have hbt' : Tendsto b atTop (𝓝[Set.Ioi 0] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hbt, Eventually.of_forall hb⟩
  exact (hbt'.inv_tendsto_nhdsGT_zero.atTop_add hn.inv_tendsto_atTop).atTop_div_const hk

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- Expected normalized finite-gap loss from `preliminaries.tex`, Eq. (edge:loss). -/
def scaledGapMean (μ : ProbabilityMeasure Ω) (X : ι → Ω → ℝ) (n k ell L : ℝ) : ℝ :=
  n / (n - k) * (∑ i, ∫ ω, L / (1 + (k * L - n⁻¹) * X i ω) ∂(μ : Measure Ω)) -
    ell / (k * (n - k))

/-- The multiplier of the regularized reciprocal sum. -/
def gapCoefficient (n k L : ℝ) : ℝ :=
  n / (n - k) * (L * gapRegularizer n k L)

/-- Exact conversion of the loss to the regularized reciprocal sum. -/
theorem scaledGapMean_eq (μ : ProbabilityMeasure Ω) (X : ι → Ω → ℝ)
    {n k ell L : ℝ} (h : 0 < k * L - n⁻¹) :
    scaledGapMean μ X n k ell L =
      gapCoefficient n k L * inverseMean μ X (gapRegularizer n k L) -
        ell / (k * (n - k)) := by
  let d := k * L - n⁻¹
  have hd : d ≠ 0 := h.ne'
  have hker (x : ℝ) : L / (1 + d * x) = (L * d⁻¹) * (x + d⁻¹)⁻¹ := by
    have he : 1 + d * x = d * (x + d⁻¹) := by
      rw [mul_add, mul_inv_cancel₀ hd]; ring
    rw [he, div_eq_mul_inv, mul_inv_rev]
    ring
  change n / (n - k) * (∑ i, ∫ ω, L / (1 + d * X i ω) ∂(μ : Measure Ω)) -
    ell / (k * (n - k)) = _
  simp_rw [hker, integral_const_mul, ← Finset.mul_sum]
  simp [gapCoefficient, gapRegularizer, inverseMean, d, mul_assoc]

private theorem tendsto_gapCoefficient {n L : ℕ → ℝ} {k : ℝ} (hk : 0 < k)
    (hn : Tendsto n atTop atTop) (hL : Tendsto L atTop atTop)
    (hnk : ∀ j, k < n j) (hd : ∀ j, 0 < k * L j - (n j)⁻¹) :
    Tendsto (fun j => gapCoefficient (n j) k (L j)) atTop (𝓝 (1 / k)) := by
  have hratio : Tendsto (fun j => n j / (n j - k)) atTop (𝓝 1) := by
    have hbase : Tendsto (fun j => 1 - k * (n j)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
        (hn.inv_tendsto_atTop.const_mul k)
    convert hbase.inv₀ one_ne_zero using 1
    · funext j
      have hn₀ := (hk.trans (hnk j)).ne'
      have hdiff := (sub_pos.mpr (hnk j)).ne'
      have he : 1 - k * (n j)⁻¹ = (n j - k) / n j := by
        field_simp
      rw [he, inv_div]
    · norm_num
  have hreg := tendsto_gapRegularizer hk hn hL
  have hlb : Tendsto (fun j => L j * gapRegularizer (n j) k (L j)) atTop (𝓝 (1 / k)) := by
    have hbase : Tendsto (fun j => (1 + (n j)⁻¹ * gapRegularizer (n j) k (L j)) / k)
        atTop (𝓝 (1 / k)) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add
        (hn.inv_tendsto_atTop.mul hreg)).div_const k
    convert hbase using 1
    funext j
    apply (eq_div_iff hk.ne').mpr
    have he := mul_inv_cancel₀ (hd j).ne'
    change (k * L j - (n j)⁻¹) * gapRegularizer (n j) k (L j) = 1 at he
    linear_combination he
  simpa [gapCoefficient] using hratio.mul hlb

/-- Normalizing by the finite-gap loss changes the target by precisely `1 / k`. -/
theorem tendsto_scaledGapMean_iff {μ : ℕ → ProbabilityMeasure Ω} {X : ι → Ω → ℝ}
    {n L : ℕ → ℝ} {k ell m : ℝ} (hk : 0 < k) (hn : Tendsto n atTop atTop)
    (hL : Tendsto L atTop atTop) (hnk : ∀ j, k < n j)
    (hd : ∀ j, 0 < k * L j - (n j)⁻¹) :
    Tendsto (fun j => scaledGapMean (μ j) X (n j) k ell (L j)) atTop (𝓝 (m / k)) ↔
      Tendsto (fun j => inverseMean (μ j) X (gapRegularizer (n j) k (L j))) atTop (𝓝 m) := by
  have hc := tendsto_gapCoefficient hk hn hL hnk hd
  have hs : Tendsto (fun j => ell / (k * (n j - k))) atTop (𝓝 0) := by
    have hn' : Tendsto (fun j => n j - k) atTop atTop := by
      simpa only [sub_eq_add_neg] using hn.atTop_add (tendsto_const_nhds (x := -k))
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      (hn'.const_mul_atTop hk).inv_tendsto_atTop.const_mul ell
  constructor
  · intro h
    have h' := (h.add hs).div hc (show (1 : ℝ) / k ≠ 0 by positivity)
    convert h' using 1
    · funext j
      change _ = (scaledGapMean (μ j) X (n j) k ell (L j) + ell / (k * (n j - k))) /
        gapCoefficient (n j) k (L j)
      rw [scaledGapMean_eq (μ j) X (hd j), sub_add_cancel]
      have hcoeff : gapCoefficient (n j) k (L j) ≠ 0 := by
        have hn₀ := hk.trans (hnk j)
        have h₁ := sub_pos.mpr (hnk j)
        have hL₀ : 0 < L j :=
          pos_of_mul_pos_right ((inv_pos.mpr hn₀).trans (sub_pos.mp (hd j))) hk.le
        exact (mul_pos (div_pos hn₀ h₁) (mul_pos hL₀ (inv_pos.mpr (hd j)))).ne'
      exact (mul_div_cancel_left₀ _ hcoeff).symm
    · congr 1
      field_simp
      ring
  · intro h
    have h' := (hc.mul h).sub hs
    convert h' using 1
    · funext j
      exact scaledGapMean_eq (μ j) X (hd j)
    · congr 1
      ring

end GapNormalization

end SketchOrientation.Edge
