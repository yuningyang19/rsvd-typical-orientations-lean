import SketchOrientation.GaussianChaosProjection
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal InnerProductSpace Topology

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]

/-- Pairing against the constant generating function gives the Gaussian mean. -/
theorem gaussianWickLp_zero_inner (f : GaussianL2 E) :
    inner ℝ (gaussianWickLp 0) f = ∫ x, f x ∂stdGaussian E := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_gaussianWickExponential (0 : E)).coeFn_toLp] with x hx
  change gaussianWickLp 0 x = gaussianWickExponential (0 : E) x at hx
  rw [hx, RCLike.inner_apply]
  simp [gaussianWickExponential]

private noncomputable def gaussianL2Centering :
    GaussianL2 E →L[ℝ] GaussianL2 E :=
  ContinuousLinearMap.id ℝ _ -
    (innerSL ℝ (gaussianWickLp (0 : E))).smulRight (gaussianWickLp 0)

private theorem gaussianL2Centering_apply (f : GaussianL2 E) :
    gaussianL2Centering f = f - (∫ x, f x ∂stdGaussian E) • gaussianWickLp 0 := by
  change f - (inner ℝ (gaussianWickLp 0) f) • gaussianWickLp 0 = _
  rw [gaussianWickLp_zero_inner]

private theorem gaussianL2Centering_wickLp (u : E) :
    gaussianL2Centering (gaussianWickLp u) = gaussianCenteredWickLp u := by
  rw [gaussianL2Centering_apply]
  have h : (∫ x, gaussianWickLp u x ∂stdGaussian E) = 1 := by
    rw [← integral_gaussianWickExponential u]
    exact integral_congr_ae (memLp_gaussianWickExponential u).coeFn_toLp
  rw [h, one_smul]
  rfl

private theorem gaussianCenteredWickLp_sequence (f : GaussianL2 E)
    (hf : (∫ x, f x ∂stdGaussian E) = 0) :
    ∃ g : ℕ → GaussianL2 E,
      (∀ n, g n ∈ Submodule.span ℝ (Set.range (gaussianCenteredWickLp (E := E)))) ∧
        Tendsto g atTop (𝓝 f) := by
  let K := Submodule.span ℝ (Set.range (gaussianWickLp (E := E)))
  let K₀ := Submodule.span ℝ (Set.range (gaussianCenteredWickLp (E := E)))
  let C := gaussianL2Centering (E := E)
  obtain ⟨g, hg, hglim⟩ := mem_closure_iff_seq_limit.mp (dense_span_gaussianWickLp f)
  have himage : K.map C.toLinearMap = K₀ := by
    unfold K K₀
    rw [Submodule.map_span]
    have hh : C.toLinearMap '' Set.range (gaussianWickLp (E := E)) =
        Set.range (gaussianCenteredWickLp (E := E)) := by
      ext w
      constructor
      · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
        exact ⟨u, (gaussianL2Centering_wickLp u).symm⟩
      · rintro ⟨u, rfl⟩
        exact ⟨gaussianWickLp u, ⟨u, rfl⟩, gaussianL2Centering_wickLp u⟩
    rw [hh]
  refine ⟨C ∘ g, fun n => ?_, ?_⟩
  · change C (g n) ∈ K₀
    rw [← himage]
    exact Submodule.mem_map.2 ⟨g n, hg n, rfl⟩
  · have he : C f = f := by rw [gaussianL2Centering_apply, hf, zero_smul, sub_zero]
    simpa only [he] using C.continuous.continuousAt.tendsto.comp hglim

private theorem gaussianProjection_spanWick_average (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ E)
    (hS : ∀ u : E, Measurable (fun ω => (S ω).starProjection u))
    (ρ : ℝ) (hρ : ∀ u : E, (∫ ω, ‖(S ω).starProjection u‖ ^ 2 ∂μ) ≤ ρ * ‖u‖ ^ 2)
    (f : GaussianL2 E) (hf : f ∈ Submodule.span ℝ (Set.range (gaussianCenteredWickLp (E := E)))) :
    Measurable (fun ω => ‖gaussianConditionalProjection (S ω) f‖ ^ 2) ∧
      (∫ ω, ‖gaussianConditionalProjection (S ω) f‖ ^ 2 ∂μ) ≤ ρ * ‖f‖ ^ 2 := by
  classical
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
  rw [← hl]
  have he :
      (l.sum fun i a => a • gaussianCenteredWickLp i) =
        ∑ i : l.support, l (i : E) • gaussianCenteredWickLp (i : E) := by
    rw [Finsupp.sum, ← Finset.sum_attach]
    rfl
  rw [he]
  exact gaussianProjection_finiteWick_average μ S hS ρ hρ
    (fun i : l.support => (i : E)) (fun i => l i)

/-- The Gaussian L² contraction for an arbitrary law of orthogonal observations.
The constant is the mean projected-energy bound. -/
theorem gaussianProjection_L2_contraction (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ E)
    (hS : ∀ u : E, Measurable (fun ω => (S ω).starProjection u))
    (ρ : ℝ) (hρ : ∀ u : E, (∫ ω, ‖(S ω).starProjection u‖ ^ 2 ∂μ) ≤ ρ * ‖u‖ ^ 2)
    (f : GaussianL2 E) (hf : (∫ x, f x ∂stdGaussian E) = 0) :
    Measurable (fun ω => ‖gaussianConditionalProjection (S ω) f‖ ^ 2) ∧
      (∫ ω, ‖gaussianConditionalProjection (S ω) f‖ ^ 2 ∂μ) ≤ ρ * ‖f‖ ^ 2 := by
  obtain ⟨g, hg, hglim⟩ := gaussianCenteredWickLp_sequence f hf
  let P := fun ω : Ω => gaussianConditionalProjection (S ω)
  let A := fun n ω => ‖P ω (g n)‖ ^ 2
  let B := fun ω => ‖P ω f‖ ^ 2
  have hA (n : ℕ) := gaussianProjection_spanWick_average μ S hS ρ hρ (g n) (hg n)
  have hlim (ω : Ω) : Tendsto (fun n => A n ω) atTop (𝓝 (B ω)) :=
    (((P ω).continuous.continuousAt.tendsto.comp hglim).norm).pow 2
  have hBm : Measurable B :=
    measurable_of_tendsto_metrizable (fun n => (hA n).1) (tendsto_pi_nhds.2 hlim)
  refine ⟨hBm, ?_⟩
  obtain ⟨C, hC⟩ := (hglim.norm.bddAbove_range)
  have hBnd (n : ℕ) : ∀ᵐ ω ∂μ, ‖A n ω‖ ≤ C ^ 2 := by
    filter_upwards [] with ω
    change ‖‖P ω (g n)‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_gaussianConditionalProjection_le _ _).trans
      (hC ⟨n, rfl⟩)) _
  have hInt := tendsto_integral_of_dominated_convergence (fun _ => C ^ 2)
    (fun n => (hA n).1.aestronglyMeasurable) (integrable_const _) hBnd (ae_of_all _ hlim)
  exact le_of_tendsto_of_tendsto' hInt
    ((hglim.norm.pow 2).const_mul ρ) (fun n => (hA n).2)

end SketchOrientation
