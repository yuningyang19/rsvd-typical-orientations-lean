import SketchOrientation.GaussianChaosDensity
import SketchOrientation.GaussianChaosAverage

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

variable {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] [Fintype ι]

noncomputable abbrev GaussianL2 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] :=
  Lp ℝ 2 (stdGaussian E)

/-- Conditional expectation on the observed orthogonal projection, as a map of Gaussian L². -/
noncomputable def gaussianConditionalProjection (S : Submodule ℝ E) :
    GaussianL2 E →L[ℝ] GaussianL2 E :=
  (lpMeas ℝ ℝ (MeasurableSpace.comap S.orthogonalProjectionOnto inferInstance) 2
    (stdGaussian E)).subtypeL.comp
    (condExpL2 ℝ ℝ S.orthogonalProjectionOnto.continuous.measurable.comap_le)

theorem norm_gaussianConditionalProjection_le (S : Submodule ℝ E) (f : GaussianL2 E) :
    ‖gaussianConditionalProjection S f‖ ≤ ‖f‖ :=
  norm_condExpL2_coe_le S.orthogonalProjectionOnto.continuous.measurable.comap_le f

theorem gaussianConditionalProjection_wickLp (S : Submodule ℝ E) (u : E) :
    gaussianConditionalProjection S (gaussianWickLp u) = gaussianWickLp (S.starProjection u) := by
  apply Lp.ext
  exact ((memLp_gaussianWickExponential u).condExpL2_ae_eq_condExp
    S.orthogonalProjectionOnto.continuous.measurable.comap_le).trans
    ((gaussianWickExponential_condExp S u).trans
      (memLp_gaussianWickExponential (S.starProjection u)).coeFn_toLp.symm)

noncomputable def gaussianCenteredWickLp (u : E) : GaussianL2 E :=
  gaussianWickLp u - gaussianWickLp 0

theorem gaussianConditionalProjection_centeredWickLp (S : Submodule ℝ E) (u : E) :
    gaussianConditionalProjection S (gaussianCenteredWickLp u) =
      gaussianCenteredWickLp (S.starProjection u) := by
  simp [gaussianCenteredWickLp, gaussianConditionalProjection_wickLp]

private theorem inner_gaussianCenteredWickLp (u v : E) :
    inner ℝ (gaussianCenteredWickLp u) (gaussianCenteredWickLp v) =
      Real.exp (inner ℝ u v) - 1 := by
  rw [L2.inner_def, ← integral_gaussianWickExponential_centered_mul]
  apply integral_congr_ae
  have ha (w : E) : gaussianCenteredWickLp w =ᵐ[stdGaussian E]
      fun x => gaussianWickExponential w x - 1 := by
    unfold gaussianCenteredWickLp
    filter_upwards [Lp.coeFn_sub (gaussianWickLp w) (gaussianWickLp 0),
      (memLp_gaussianWickExponential w).coeFn_toLp,
      (memLp_gaussianWickExponential (0 : E)).coeFn_toLp] with x hsub hw hzero
    change ((gaussianWickLp w - gaussianWickLp 0 : GaussianL2 E) : E → ℝ) x = _
    rw [hsub]
    change gaussianWickLp w x - gaussianWickLp 0 x = _
    change gaussianWickLp w x = _ at hw
    change gaussianWickLp 0 x = _ at hzero
    rw [hw, hzero]
    simp [gaussianWickExponential]
  filter_upwards [ha u, ha v] with x hu hv
  rw [hu, hv, RCLike.inner_apply, conj_trivial, mul_comm]

/-- On finite linear combinations, the squared L² norm is the centered
exponential kernel quadratic form. -/
theorem norm_sq_gaussianCenteredWickLp_sum (u : ι → E) (a : ι → ℝ) :
    ‖∑ i, a i • gaussianCenteredWickLp (u i)‖ ^ 2 =
      kernelQuadratic (Matrix.of fun i j => Real.exp (inner ℝ (u i) (u j)) - 1) a := by
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    inner_gaussianCenteredWickLp, kernelQuadratic, Matrix.of_apply, mul_comm (a _) (Real.exp _ - 1)]

/-- Lemma 3.2's L² contraction on the finite span of centered generating
functions. Measurability and integrability concern the actual conditional
expectation as a function of the projector draw. -/
theorem gaussianProjection_finiteWick_average (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ E)
    (hS : ∀ u : E, Measurable (fun ω => (S ω).starProjection u))
    (ρ : ℝ) (hρ : ∀ u : E, (∫ ω, ‖(S ω).starProjection u‖ ^ 2 ∂μ) ≤ ρ * ‖u‖ ^ 2)
    (u : ι → E) (a : ι → ℝ) :
    let f := ∑ i, a i • gaussianCenteredWickLp (u i)
    Measurable (fun ω => ‖gaussianConditionalProjection (S ω) f‖ ^ 2) ∧
      (∫ ω, ‖gaussianConditionalProjection (S ω) f‖ ^ 2 ∂μ) ≤ ρ * ‖f‖ ^ 2 := by
  dsimp only
  simp_rw [map_sum, map_smul, gaussianConditionalProjection_centeredWickLp,
    norm_sq_gaussianCenteredWickLp_sum]
  constructor
  · unfold kernelQuadratic
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    have hinner := (continuous_inner (𝕜 := ℝ) (E := E)).measurable.comp
      ((hS (u i)).prodMk (hS (u j)))
    exact ((hinner.exp.sub_const _).mul_const _).const_mul _
  · exact gaussianProjection_expKernel_average μ S hS ρ hρ u a

end SketchOrientation
