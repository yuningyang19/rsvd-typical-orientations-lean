import TypicalOrientations.ConditionalCriterion
import TypicalOrientations.GeneralRotationVariance
import TypicalOrientations.RotationMarginal
import TypicalOrientations.RootRate
import TypicalOrientations.CommonMean
import TypicalOrientations.SamplingGeometry

namespace TypicalOrientations

open Filter Matrix MeasureTheory ProbabilityTheory Set SketchOrientation
open scoped ProbabilityTheory Topology

/-- Lemma 3.1 with its external rotation-group theorem as an explicit premise. -/
theorem lemma_3_1_of_brascampLieb (hBL : RotationBrascampLieb)
    {n l : ℕ} (hl' : 0 < l) (hl : l ≤ n)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    SharedRotationVariance hl μ := by
  rintro f hf ⟨B, hB⟩
  apply variance_rotation_of_brascampLieb hBL hl' hl μ f hf B hB
  intro P
  simpa only [Function.comp_def, id_eq] using
    (rotateProjector_specialOrientation_identDistrib (hl'.trans_le hl) hl P).comp hf

/-- The equivalence in Theorem 1.1, retaining the precise external
Brascamp–Lieb interface in the theorem type. -/
theorem criterion_of_brascampLieb (hBL : RotationBrascampLieb)
    {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hℓn : ∀ i, k + p ≤ n i)
    (μ : ∀ i, Measure (OrthogonalProjector (n i) (k+p))) [∀ i, IsProbabilityMeasure (μ i)] :
    Tendsto (fun i => meanProjectorNorm (μ i)) atTop (𝓝 0) ↔
      Tendsto (fun i => meanDiscrepancy k (μ i)) atTop (𝓝 0) :=
  criterion_of_sharedRotationVariance hk hp n hn hℓn μ
    (fun i => lemma_3_1_of_brascampLieb hBL (by omega) (hℓn i) (μ i))

theorem meanDiscrepancy_rate_of_brascampLieb (hBL : RotationBrascampLieb)
    {n k p : ℕ} (hk : 0 < k) (hl : k + p ≤ n)
    (μ : Measure (OrthogonalProjector n (k+p))) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 1 < r) (hr₂ : r ≤ 2) (hp : 2 * r < (p : ℝ) + 1) :
    meanDiscrepancy k μ ≤
      3 * gaussianTailMomentConstant k p r * (2 * meanProjectorNorm μ) ^ (1 - 1 / r) :=
  meanDiscrepancy_paper_rate_of_variance hk hl μ
    (lemma_3_1_of_brascampLieb hBL (by omega) hl μ) hr hr₂ hp

theorem meanDiscrepancy_rootRate_of_brascampLieb (hBL : RotationBrascampLieb)
    {n k p : ℕ} (hk : 0 < k) (hp : 4 ≤ p) (hl : k + p ≤ n)
    (μ : Measure (OrthogonalProjector n (k+p))) [IsProbabilityMeasure μ] :
    meanDiscrepancy k μ ≤
      gaussianTailMomentConstant k p 2 * Real.sqrt (2 * meanProjectorNorm μ) :=
  meanDiscrepancy_rootRate_of_variance hk hp hl μ fun σ =>
    lemma_3_1_of_brascampLieb hBL (by omega) hl μ _ (measurable_subspaceLoss k σ.val) <|
      ⟨_, fun P => by
        rw [subspaceLoss, abs_of_nonneg (residual_div_tail_nonneg k σ.val σ.property.2.2 P.val)]
        exact residual_div_tail_le k σ.val σ.property.2.2 P.val⟩

/-- The common rate part of Corollaries 4.1 and 4.2 once their respective
geometric proofs give the scalar mean projector. -/
theorem isotropic_meanDiscrepancy_rate_of_brascampLieb (hBL : RotationBrascampLieb)
    {n k p : ℕ} (hk : 0 < k) (hp : 4 ≤ p) (hl : k + p ≤ n)
    (μ : Measure (OrthogonalProjector n (k+p))) [IsProbabilityMeasure μ]
    (hIso : meanSketchProjector μ = (((k+p : ℕ) : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    meanDiscrepancy k μ ≤
      gaussianTailMomentConstant k p 2 * Real.sqrt (2 * (((k+p : ℕ) : ℝ) / n)) := by
  have hr := meanDiscrepancy_rootRate_of_brascampLieb hBL hk hp hl μ
  have hρ : meanProjectorNorm μ = ((k+p : ℕ) : ℝ) / n :=
    meanSketchProjector_norm_of_isotropic (by omega) μ hIso
  rwa [hρ] at hr

/-- Corollary 4.3 with the same explicit premise as Theorem 1.1. -/
theorem commonMean_of_brascampLieb (hBL : RotationBrascampLieb)
    {ι : Type*} [Fintype ι] [Nonempty ι] {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hℓn : ∀ t, k+p ≤ n t)
    (μ : ∀ t, ι → Measure (OrthogonalProjector (n t) (k+p))) [∀ t j, IsProbabilityMeasure (μ t j)]
    (hρ : ∀ j, Tendsto (fun t => meanProjectorNorm (μ t j)) atTop (𝓝 0)) :
    Tendsto (fun t => commonMeanDiscrepancy k (μ t)) atTop (𝓝 0) ∧
      ∀ i j, Tendsto (fun t => pairwiseMeanDiscrepancy k (μ t i) (μ t j)) atTop (𝓝 0) := by
  refine commonMean_of_individual_limits n (fun t => ?_) μ
    (fun t j => meanDiscrepancy_bddAbove hk hp (hℓn t) (μ t j)) fun j => ?_
  · have := hℓn t
    omega
  · exact (criterion_of_brascampLieb hBL hk hp n hn hℓn (fun t => μ t j)).mp (hρ j)

end TypicalOrientations
