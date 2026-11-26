import TypicalOrientations.BCLMTheorem
import TypicalOrientations.CriterionPort

namespace TypicalOrientations

open Filter Matrix MeasureTheory ProbabilityTheory Set SketchOrientation
open scoped Topology

noncomputable section

theorem lemma_3_1 {n l : ℕ} (hl' : 0 < l) (hl : l ≤ n)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    SharedRotationVariance hl μ :=
  lemma_3_1_of_brascampLieb rotationBrascampLieb hl' hl μ

theorem paper_explicit_rate {n k p : ℕ} (hk : 0 < k) (hn : k+p ≤ n)
    (μ : Measure (OrthogonalProjector n (k+p))) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 1 < r) (hr₂ : r ≤ 2) (hp : 2*r < (p : ℝ)+1) :
    meanDiscrepancy k μ ≤
      3 * gaussianTailMomentConstant k p r * (2 * meanProjectorNorm μ) ^ (1 - 1 / r) :=
  meanDiscrepancy_rate_of_brascampLieb rotationBrascampLieb hk hn μ hr hr₂ hp

theorem paper_root_rate {n k p : ℕ} (hk : 0 < k) (hp : 4 ≤ p) (hn : k+p ≤ n)
    (μ : Measure (OrthogonalProjector n (k+p))) [IsProbabilityMeasure μ] :
    meanDiscrepancy k μ ≤
      gaussianTailMomentConstant k p 2 * Real.sqrt (2 * meanProjectorNorm μ) :=
  meanDiscrepancy_rootRate_of_brascampLieb rotationBrascampLieb hk hp hn μ

/-- Theorem 1.1. The quantitative conclusions retain the explicit
constants of equations (3.6) and (3.7). -/
theorem theorem_1_1 {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hℓn : ∀ i, k+p ≤ n i)
    (μ : ∀ i, Measure (OrthogonalProjector (n i) (k+p))) [∀ i, IsProbabilityMeasure (μ i)] :
    (Tendsto (fun i => meanProjectorNorm (μ i)) atTop (𝓝 0) ↔
      Tendsto (fun i => meanDiscrepancy k (μ i)) atTop (𝓝 0)) ∧
    (∀ i r, 1 < r → r ≤ 2 → 2*r < (p : ℝ)+1 →
      meanDiscrepancy k (μ i) ≤
        3 * gaussianTailMomentConstant k p r * (2 * meanProjectorNorm (μ i)) ^ (1 - 1 / r)) ∧
    (4 ≤ p → ∀ i, meanDiscrepancy k (μ i) ≤
      gaussianTailMomentConstant k p 2 * Real.sqrt (2 * meanProjectorNorm (μ i))) := by
  refine ⟨criterion_of_brascampLieb rotationBrascampLieb hk hp n hn hℓn μ, ?_, ?_⟩
  · intro i r hr hr₂ hrp
    exact paper_explicit_rate hk (hℓn i) (μ i) hr hr₂ hrp
  · intro hp₄ i
    exact paper_root_rate hk hp₄ (hℓn i) (μ i)

private theorem isotropic_comparison {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hd : ∀ i, k+p ≤ n i)
    (μ : ∀ i, Measure (OrthogonalProjector (n i) (k+p))) [∀ i, IsProbabilityMeasure (μ i)]
    (hIso : ∀ i, meanSketchProjector (μ i) =
      (((k+p : ℕ) : ℝ) / n i) • (1 : Matrix (Fin (n i)) (Fin (n i)) ℝ)) :
    Tendsto (fun i => meanDiscrepancy k (μ i)) atTop (𝓝 0) ∧
      (4 ≤ p → ∀ i, meanDiscrepancy k (μ i) ≤
        gaussianTailMomentConstant k p 2 * Real.sqrt (2 * (((k+p : ℕ) : ℝ) / n i))) := by
  have hRho (i) : meanProjectorNorm (μ i) = ((k+p : ℕ) : ℝ) / n i :=
    meanSketchProjector_norm_of_isotropic (by have := hd i; omega) _ (hIso i)
  have hLim : Tendsto (fun i => ((k+p : ℕ) : ℝ) / (n i : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hn)
  refine ⟨(theorem_1_1 hk hp n hn hd μ).1.mp (hLim.congr (fun i => (hRho i).symm)), ?_⟩
  intro hp₄ i
  rw [← hRho i]
  exact paper_root_rate hk hp₄ (hd i) (μ i)

def rowSketchLaw {n l : ℕ} (joint : Measure (OrthogonalTransform n × CoordinateSubset n l)) :
    Measure (OrthogonalProjector n l) :=
  joint.map (fun z => orthogonalRowProjector z.1 z.2)

instance {n l : ℕ} (joint : Measure (OrthogonalTransform n × CoordinateSubset n l))
    [IsProbabilityMeasure joint] : IsProbabilityMeasure (rowSketchLaw joint) :=
  Measure.isProbabilityMeasure_map measurable_orthogonalRowProjector.aemeasurable

def equalConditionalRowInclusion {n l : ℕ} (hl : l ≤ n)
    (joint : Measure (OrthogonalTransform n × CoordinateSubset n l))
    [IsProbabilityMeasure joint] : Prop :=
  let _ : Nonempty (CoordinateSubset n l) := ⟨⟨Finset.univ.map (Fin.castLEEmb hl), by simp⟩⟩
  ∀ᵐ O ∂joint.fst, ∀ i : Fin n,
    (joint.condKernel O).real {J | i ∈ J.val} = (l : ℝ) / n

/-- Corollary 4.1 for arbitrary joint laws of a transform and its sampled rows. -/
theorem corollary_4_1 {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hd : ∀ i, k+p ≤ n i)
    (J : ∀ i, Measure (OrthogonalTransform (n i) × CoordinateSubset (n i) (k+p)))
    [∀ i, IsProbabilityMeasure (J i)] (hIncl : ∀ i, equalConditionalRowInclusion (hd i) (J i)) :
    (∀ i, meanSketchProjector (rowSketchLaw (J i)) =
      (((k+p : ℕ) : ℝ) / n i) • (1 : Matrix (Fin (n i)) (Fin (n i)) ℝ)) ∧
    Tendsto (fun i => meanDiscrepancy k (rowSketchLaw (J i))) atTop (𝓝 0) ∧
    (4 ≤ p → ∀ i, meanDiscrepancy k (rowSketchLaw (J i)) ≤
      gaussianTailMomentConstant k p 2 * Real.sqrt (2 * (((k+p : ℕ) : ℝ) / n i))) := by
  have hM (i : ℕ) := meanSketchProjector_orthogonalRows_joint (hd i) (J i) (hIncl i)
  exact ⟨hM, isotropic_comparison hk hp n hn hd (fun i => rowSketchLaw (J i)) hM⟩

def fullRankSketchLaw {n l : ℕ} (hl : l ≤ n) (ν : Measure (Matrix (Fin n) (Fin l) ℝ)) :
    Measure (OrthogonalProjector n l) :=
  ν.map (fullRankColumnProjector hl)

instance {n l : ℕ} (hl : l ≤ n) (ν : Measure (Matrix (Fin n) (Fin l) ℝ))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (fullRankSketchLaw hl ν) :=
  Measure.isProbabilityMeasure_map (measurable_fullRankColumnProjector hl).aemeasurable

/-- Corollary 4.2 on the matrix law with full column rank almost surely. -/
theorem corollary_4_2 {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hd : ∀ i, k+p ≤ n i)
    (ν : ∀ i, Measure (Matrix (Fin (n i)) (Fin (k+p)) ℝ))
    [∀ i, IsProbabilityMeasure (ν i)]
    (hRank : ∀ i, ∀ᵐ Y ∂ν i, Function.Injective Y.mulVec)
    (hSign : ∀ i (s : Fin (n i) → ℝ), (∀ j, s j = 1 ∨ s j = -1) →
      ((ν i).map fun Y => rangeProjector (diagonal s * Y)) = (ν i).map rangeProjector)
    (hPerm : ∀ i (π : Equiv.Perm (Fin (n i))),
      ((ν i).map fun Y => rangeProjector (π.permMatrix ℝ * Y)) = (ν i).map rangeProjector) :
    (∀ i, meanSketchProjector (fullRankSketchLaw (hd i) (ν i)) =
      (((k+p : ℕ) : ℝ) / n i) • (1 : Matrix (Fin (n i)) (Fin (n i)) ℝ)) ∧
    Tendsto (fun i => meanDiscrepancy k (fullRankSketchLaw (hd i) (ν i))) atTop (𝓝 0) ∧
    (4 ≤ p → ∀ i, meanDiscrepancy k (fullRankSketchLaw (hd i) (ν i)) ≤
      gaussianTailMomentConstant k p 2 * Real.sqrt (2 * (((k+p : ℕ) : ℝ) / n i))) := by
  have hM (i) :=
    meanSketchProjector_of_fullRankColumnSpace_symmetry (by have := hd i; omega)
      (hd i) (ν i) (hRank i) (hSign i) (hPerm i)
  exact ⟨hM, isotropic_comparison hk hp n hn hd (fun i => fullRankSketchLaw (hd i) (ν i)) hM⟩

/-- Corollary 4.3, including both joint and pairwise comparison. -/
theorem corollary_4_3
    {ι : Type*} [Fintype ι] [Nonempty ι] {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hd : ∀ t, k+p ≤ n t)
    (μ : ∀ t, ι → Measure (OrthogonalProjector (n t) (k+p))) [∀ t j, IsProbabilityMeasure (μ t j)]
    (hρ : ∀ j, Tendsto (fun t => meanProjectorNorm (μ t j)) atTop (𝓝 0)) :
    Tendsto (fun t => commonMeanDiscrepancy k (μ t)) atTop (𝓝 0) ∧
      ∀ i j, Tendsto (fun t => pairwiseMeanDiscrepancy k (μ t i) (μ t j)) atTop (𝓝 0) :=
  commonMean_of_brascampLieb rotationBrascampLieb hk hp n hn hd μ hρ

end

end TypicalOrientations
