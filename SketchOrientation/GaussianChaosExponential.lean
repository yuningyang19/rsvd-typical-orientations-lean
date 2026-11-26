import SketchOrientation.GaussianChaosSplit

namespace SketchOrientation

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The real Gaussian generating function at parameter `u`. -/
noncomputable def gaussianWickExponential (u x : E) : ℝ :=
  Real.exp (inner ℝ u x - ‖u‖ ^ 2 / 2)

omit [FiniteDimensional ℝ E] in
@[fun_prop] theorem measurable_gaussianWickExponential (u : E) :
    Measurable (gaussianWickExponential u) := by
  unfold gaussianWickExponential
  fun_prop

private theorem stdGaussian_inner_map (u : E) :
    (stdGaussian E).map (innerSL ℝ u) =
      gaussianReal 0 (Real.toNNReal (‖u‖ ^ 2)) := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm]

private theorem integrable_stdGaussian_exp_inner (u : E) :
    Integrable (fun x => Real.exp (inner ℝ u x)) (stdGaussian E) := by
  have h : Integrable (fun t : ℝ => Real.exp t)
      ((stdGaussian E).map (innerSL ℝ u)) := by
    rw [stdGaussian_inner_map]
    simpa using integrable_exp_mul_gaussianReal
      (μ := 0) (v := Real.toNNReal (‖u‖ ^ 2)) 1
  exact h.comp_measurable (innerSL ℝ u).continuous.measurable

/-- Every Gaussian generating function is integrable. -/
theorem integrable_gaussianWickExponential (u : E) :
    Integrable (gaussianWickExponential u) (stdGaussian E) := by
  unfold gaussianWickExponential
  simp_rw [Real.exp_sub]
  exact (integrable_stdGaussian_exp_inner u).div_const _

/-- The Gaussian generating function has mean one. -/
theorem integral_gaussianWickExponential (u : E) :
    (∫ x, gaussianWickExponential u x ∂stdGaussian E) = 1 := by
  have h := mgf_gaussianReal (stdGaussian_inner_map u) 1
  simp only [mgf, one_mul, zero_add, one_pow, mul_one,
    Real.coe_toNNReal _ (sq_nonneg _)] at h
  unfold gaussianWickExponential
  simp_rw [Real.exp_sub]
  rw [integral_div]
  change (∫ x, Real.exp (innerSL ℝ u x) ∂stdGaussian E) / _ = 1
  rw [h]
  exact div_self (Real.exp_ne_zero _)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem gaussianWickExponential_split (S : Submodule ℝ E) (u x : E) :
    gaussianWickExponential u x =
      gaussianWickExponential (S.orthogonalProjectionOnto u) (S.orthogonalProjectionOnto x) *
      gaussianWickExponential (Sᗮ.orthogonalProjectionOnto u) (Sᗮ.orthogonalProjectionOnto x) := by
  have h := S.orthogonalDecomposition.inner_map_map u x
  rw [WithLp.prod_inner_apply] at h
  simp only [S.orthogonalDecomposition_apply, WithLp.ofLp_toLp] at h
  unfold gaussianWickExponential
  rw [← Real.exp_add, S.norm_sq_eq_add_norm_sq_projection, ← h]
  congr 1
  ring

set_option maxHeartbeats 500000 in
/-- Conditioning the generating function on the orthogonal observation
projects its parameter. This is the generating-function identity used in
the proof of Lemma 3.2. -/
theorem gaussianWickExponential_condExp (S : Submodule ℝ E) (u : E) :
    (stdGaussian E)[gaussianWickExponential u |
      MeasurableSpace.comap S.orthogonalProjectionOnto inferInstance] =ᵐ[stdGaussian E]
      gaussianWickExponential (S.starProjection u) := by
  let μ := stdGaussian E
  let p := S.orthogonalProjectionOnto
  let q := Sᗮ.orthogonalProjectionOnto
  let f := gaussianWickExponential (p u) ∘ p
  let g := gaussianWickExponential (q u) ∘ q
  have hp : Measurable p := p.continuous.measurable
  have hq : Measurable q := q.continuous.measurable
  have hmp : MeasurableSpace.comap p inferInstance ≤ (inferInstance : MeasurableSpace E) := hp.comap_le
  have hmq : MeasurableSpace.comap q inferInstance ≤ (inferInstance : MeasurableSpace E) := hq.comap_le
  have hf : StronglyMeasurable[MeasurableSpace.comap p inferInstance] f :=
    ((measurable_gaussianWickExponential (p u)).comp (comap_measurable p)).stronglyMeasurable
  have hg : StronglyMeasurable[MeasurableSpace.comap q inferInstance] g :=
    ((measurable_gaussianWickExponential (q u)).comp (comap_measurable q)).stronglyMeasurable
  have hsplit : gaussianWickExponential u = f * g :=
    funext (gaussianWickExponential_split S u)
  have hfg : Integrable (f * g) μ := by
    rw [← hsplit]
    exact integrable_gaussianWickExponential u
  have hgInt : Integrable g μ := by
    have h : Integrable (gaussianWickExponential (q u)) (μ.map q) := by
      change Integrable _ ((stdGaussian E).map Sᗮ.orthogonalProjectionOnto)
      rw [stdGaussian_map_projection]
      exact integrable_gaussianWickExponential _
    exact h.comp_measurable hq
  have hi : Indep (MeasurableSpace.comap q inferInstance)
      (MeasurableSpace.comap p inferInstance) μ :=
    (IndepFun_iff_Indep q p μ).mp (stdGaussian_orthogonal_split_indep S).symm
  have hce := condExp_indep_eq hmq hmp hg hi
  have hgi : (∫ x, g x ∂μ) = 1 := by
    change (∫ x, gaussianWickExponential (q u) (q x) ∂μ) = 1
    rw [← integral_map hq.aemeasurable
      (measurable_gaussianWickExponential (q u)).aestronglyMeasurable]
    change (∫ x, gaussianWickExponential (q u) x ∂(stdGaussian E).map Sᗮ.orthogonalProjectionOnto) = _
    rw [stdGaussian_map_projection, integral_gaussianWickExponential]
  rw [hgi] at hce
  change μ[gaussianWickExponential u | MeasurableSpace.comap p inferInstance] =ᵐ[μ] gaussianWickExponential (S.starProjection u)
  rw [hsplit]
  refine (condExp_mul_of_stronglyMeasurable_left hf hfg hgInt).trans ?_
  filter_upwards [hce] with x hx
  change f x * μ[g | MeasurableSpace.comap p inferInstance] x = _
  rw [hx, mul_one]
  change gaussianWickExponential (p u) (p x) = gaussianWickExponential (S.starProjection u) x
  unfold gaussianWickExponential
  change Real.exp (inner ℝ (p u) (p x) - ‖p u‖ ^ 2 / 2) =
    Real.exp (inner ℝ (↑(p u) : E) x - ‖p u‖ ^ 2 / 2)
  rw [S.inner_orthogonalProjectionOnto_eq_of_mem_left]


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem gaussianWickExponential_mul (u v x : E) :
    gaussianWickExponential u x * gaussianWickExponential v x =
      Real.exp (inner ℝ u v) * gaussianWickExponential (u + v) x := by
  unfold gaussianWickExponential
  rw [← Real.exp_add, ← Real.exp_add, inner_add_left, norm_add_sq_real]
  congr 1
  ring

/-- The pairing of generating functions yields the exponential Gram kernel. -/
theorem integral_gaussianWickExponential_mul (u v : E) :
    (∫ x, gaussianWickExponential u x * gaussianWickExponential v x ∂stdGaussian E) =
      Real.exp (inner ℝ u v) := by
  simp_rw [gaussianWickExponential_mul]
  rw [integral_const_mul, integral_gaussianWickExponential, mul_one]

/-- The centered Gaussian generating functions pair by the centered
exponential Gram kernel. -/
theorem integral_gaussianWickExponential_centered_mul (u v : E) :
    (∫ x, (gaussianWickExponential u x - 1) * (gaussianWickExponential v x - 1)
      ∂stdGaussian E) = Real.exp (inner ℝ u v) - 1 := by
  have hprod : Integrable (fun x => gaussianWickExponential u x * gaussianWickExponential v x)
      (stdGaussian E) := by
    simp_rw [gaussianWickExponential_mul]
    exact (integrable_gaussianWickExponential (u + v)).const_mul _
  have hu := integrable_gaussianWickExponential u
  have hv := integrable_gaussianWickExponential v
  simp_rw [sub_mul, mul_sub, mul_one, one_mul]
  have h₁ : Integrable (fun x => gaussianWickExponential u x * gaussianWickExponential v x -
      gaussianWickExponential u x) (stdGaussian E) := hprod.sub hu
  have h₂ : Integrable (fun x => gaussianWickExponential v x - 1) (stdGaussian E) :=
    hv.sub (integrable_const _)
  rw [integral_sub h₁ h₂,
    integral_sub hprod hu, integral_sub hv (integrable_const _),
    integral_gaussianWickExponential_mul, integral_gaussianWickExponential,
    integral_gaussianWickExponential]
  simp


/-- The Gaussian generating functions belong to the Gaussian L² space. -/
theorem memLp_gaussianWickExponential (u : E) :
    MemLp (gaussianWickExponential u) 2 (stdGaussian E) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_gaussianWickExponential u).aestronglyMeasurable).2
  simp_rw [pow_two, gaussianWickExponential_mul]
  exact (integrable_gaussianWickExponential (u + u)).const_mul _

end SketchOrientation
