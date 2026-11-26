import SketchOrientation.GaussianChaosExponential

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem measures_eq_of_mgf_along_lines {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmgf : ∀ u : E, mgf (innerSL ℝ u) μ = mgf (innerSL ℝ u) ν)
    (hexp : ∀ u : E, integrableExpSet (innerSL ℝ u) μ = univ) :
    μ = ν := by
  have hmass : μ.real univ = ν.real univ := by
    simpa only [mgf_zero'] using congrFun (hmgf 0) 0
  have hzero : μ = 0 ↔ ν = 0 := by
    rw [← Measure.measure_univ_eq_zero, ← Measure.measure_univ_eq_zero,
      ← measureReal_eq_zero_iff, ← measureReal_eq_zero_iff, hmass]
  apply Measure.ext_of_charFun
  funext u
  have he := eqOn_complexMGF_of_mgf' (hmgf u) hzero
  have h := he (show Complex.I ∈ {z : ℂ |
      z.re ∈ interior (integrableExpSet (innerSL ℝ u) μ)} from by
      change Complex.I.re ∈ interior (integrableExpSet (innerSL ℝ u) μ)
      rw [hexp u, interior_univ]
      exact Set.mem_univ _)
  simpa only [complexMGF, charFun_apply, innerSL_apply_apply, real_inner_comm u, mul_comm Complex.I] using h

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem integrable_with_nonnegative_density {μ : Measure E} {f : E → ℝ≥0}
    (hf : Integrable (fun x => (f x : ℝ)) μ) :
    IsFiniteMeasure (μ.withDensity (fun x => (f x : ℝ≥0∞))) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hasFiniteIntegral_iff_ofNNReal.mp hf.2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem exp_line_eq_const_mul_wick (u : E) (t : ℝ) :
    (fun x => Real.exp (t * innerSL ℝ u x)) =
      fun x => Real.exp (‖t • u‖ ^ 2 / 2) * gaussianWickExponential (t • u) x := by
  funext x
  unfold gaussianWickExponential
  rw [← Real.exp_add, real_inner_smul_left]
  congr 1
  change t * inner ℝ u x = _
  ring

omit [BorelSpace E] in
private theorem memLp_posPart_of_memLp {f : E → ℝ} (hf : MemLp f 2 (stdGaussian E))
    (hm : Measurable f) :
    MemLp (fun x => (Real.toNNReal (f x) : ℝ)) 2 (stdGaussian E) := by
  have hm' : Measurable (fun x => (Real.toNNReal (f x) : ℝ)) := by fun_prop
  apply hf.mono hm'.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (NNReal.coe_nonneg _), Real.coe_toNNReal', Real.norm_eq_abs]
  exact max_le (le_abs_self _) (abs_nonneg _)

private theorem wickSeparates_of_measurable (f : E → ℝ) (hm : Measurable f)
    (hf : MemLp f 2 (stdGaussian E))
    (hf0 : ∀ u : E, (∫ x, f x * gaussianWickExponential u x ∂stdGaussian E) = 0) :
    f =ᵐ[stdGaussian E] 0 := by
  let μ := stdGaussian E
  let p : E → ℝ≥0 := fun x => (f x).toNNReal
  let q : E → ℝ≥0 := fun x => (-f x).toNNReal
  let μp := μ.withDensity (fun x => (p x : ℝ≥0∞))
  let μq := μ.withDensity (fun x => (q x : ℝ≥0∞))
  have hp : Measurable p := hm.real_toNNReal
  have hq : Measurable q := hm.neg.real_toNNReal
  have hpLp : MemLp (fun x => (p x : ℝ)) 2 μ := memLp_posPart_of_memLp hf hm
  have hqLp : MemLp (fun x => (q x : ℝ)) 2 μ := memLp_posPart_of_memLp hf.neg hm.neg
  have : IsFiniteMeasure μp := integrable_with_nonnegative_density (hpLp.integrable (by norm_num))
  have : IsFiniteMeasure μq := integrable_with_nonnegative_density (hqLp.integrable (by norm_num))
  have hpq (x : E) : (p x : ℝ) - q x = f x := by
    have hfx := le_total 0 (f x)
    rcases hfx with hfx | hfx
    · simp [p, q, Real.coe_toNNReal', max_eq_left hfx, max_eq_right (neg_nonpos.mpr hfx)]
    · simp [p, q, Real.coe_toNNReal', max_eq_right hfx, max_eq_left (neg_nonneg.mpr hfx)]
  have hmgf (u : E) : mgf (innerSL ℝ u) μp = mgf (innerSL ℝ u) μq := by
    funext t
    let G := gaussianWickExponential (t • u)
    let c := Real.exp (‖t • u‖ ^ 2 / 2)
    have hg : MemLp G 2 μ := memLp_gaussianWickExponential _
    have hpG : Integrable (fun x => (p x : ℝ) * G x) μ := hpLp.integrable_mul hg
    have hqG : Integrable (fun x => (q x : ℝ) * G x) μ := hqLp.integrable_mul hg
    have hdifference :
        (∫ x, (p x : ℝ) * G x ∂μ) = ∫ x, (q x : ℝ) * G x ∂μ := by
      apply sub_eq_zero.mp
      rw [← integral_sub hpG hqG]
      simpa only [← sub_mul, hpq] using hf0 (t • u)
    unfold mgf μp μq
    rw [integral_withDensity_eq_integral_smul hp, integral_withDensity_eq_integral_smul hq]
    have hline := congrFun (exp_line_eq_const_mul_wick u t)
    simp only [hline, NNReal.smul_def]
    change (∫ x, (p x : ℝ) * (c * G x) ∂μ) = ∫ x, (q x : ℝ) * (c * G x) ∂μ
    have hp' (x : E) : (p x : ℝ) * (c * G x) = c * ((p x : ℝ) * G x) := by ring
    have hq' (x : E) : (q x : ℝ) * (c * G x) = c * ((q x : ℝ) * G x) := by ring
    simp only [hp', hq', integral_const_mul, hdifference]
  have hexp (u : E) : integrableExpSet (innerSL ℝ u) μp = univ := by
    apply Set.eq_univ_of_forall
    intro t
    change Integrable (fun x => Real.exp (t * innerSL ℝ u x)) μp
    unfold μp
    rw [integrable_withDensity_iff_integrable_smul hp]
    simp only [congrFun (exp_line_eq_const_mul_wick u t)]
    have hg := (memLp_gaussianWickExponential (t • u)).const_mul (Real.exp (‖t • u‖ ^ 2 / 2))
    exact hpLp.integrable_mul hg
  have heq := measures_eq_of_mgf_along_lines hmgf hexp
  have ha : (fun x => (p x : ℝ≥0∞)) =ᵐ[μ] (fun x => (q x : ℝ≥0∞)) :=
    (withDensity_eq_iff_of_sigmaFinite hp.coe_nnreal_ennreal.aemeasurable
      hq.coe_nnreal_ennreal.aemeasurable).mp heq
  filter_upwards [ha] with x hx
  have hx' : p x = q x := ENNReal.coe_injective hx
  simp [← hpq x, hx']

/-- A Gaussian L² function orthogonal to all Gaussian generating functions
vanishes almost everywhere. The proof uses the moment-generating functions
of its positive and negative densities. -/
theorem gaussianWickExponential_totality (f : E → ℝ) (hf : MemLp f 2 (stdGaussian E))
    (hf0 : ∀ u : E, (∫ x, f x * gaussianWickExponential u x ∂stdGaussian E) = 0) :
    f =ᵐ[stdGaussian E] 0 := by
  let F := hf.aestronglyMeasurable.mk f
  have hF : f =ᵐ[stdGaussian E] F := hf.aestronglyMeasurable.ae_eq_mk
  refine hF.trans (wickSeparates_of_measurable F hf.aestronglyMeasurable.measurable_mk
    (MemLp.ae_eq hF hf) fun u => ?_)
  exact (integral_congr_ae (hF.mono fun x hx => congrArg
    (fun y => y * gaussianWickExponential u x) hx.symm)).trans (hf0 u)


/-- The L² element represented by a Gaussian generating function. -/
noncomputable def gaussianWickLp (u : E) : Lp ℝ 2 (stdGaussian E) :=
  (memLp_gaussianWickExponential u).toLp _

/-- The Gaussian generating family has dense linear span in Gaussian L². -/
theorem dense_span_gaussianWickLp :
    Dense (Submodule.span ℝ (Set.range (gaussianWickLp (E := E))) :
      Set (Lp ℝ 2 (stdGaussian E))) := by
  let K := Submodule.span ℝ (Set.range (gaussianWickLp (E := E)))
  change Dense (K : Set (Lp ℝ 2 (stdGaussian E)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, ← K.orthogonal_orthogonal_eq_closure]
  have hbot : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro f hf
    apply Lp.ext
    refine (gaussianWickExponential_totality f (Lp.memLp f) fun u => ?_).trans
      ((Lp.coeFn_zero (μ := stdGaussian E) (p := 2) (E := ℝ)).symm)
    have h := hf (gaussianWickLp u) (Submodule.subset_span ⟨u, rfl⟩)
    rw [L2.inner_def] at h
    refine (integral_congr_ae ?_).trans h
    filter_upwards [(memLp_gaussianWickExponential u).coeFn_toLp] with x hx
    change f x * gaussianWickExponential u x = inner ℝ (gaussianWickLp u x) (f x)
    rw [show gaussianWickLp u x = gaussianWickExponential u x from hx]
    rw [RCLike.inner_apply]
    simp only [conj_trivial]
  rw [hbot, Submodule.bot_orthogonal_eq_top]

end SketchOrientation
