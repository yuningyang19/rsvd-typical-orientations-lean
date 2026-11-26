import TypicalOrientations

open Filter MeasureTheory SketchOrientation TypicalOrientations
open scoped Topology

noncomputable section

/-- The exact fixed-width equivalence and both quantitative conclusions. -/
private def criterionConclusion {k p : ℕ} (n : ℕ → ℕ)
    (μ : (i : ℕ) → Measure (OrthogonalProjector (n i) (k + p))) : Prop :=
  (Tendsto (fun i => meanProjectorNorm (μ i)) atTop (𝓝 0) ↔
    Tendsto (fun i => meanDiscrepancy k (μ i)) atTop (𝓝 0)) ∧
  (∀ i (r : ℝ), 1 < r → r ≤ 2 → 2 * r < (p : ℝ) + 1 →
    meanDiscrepancy k (μ i) ≤
      3 * gaussianTailMomentConstant k p r * (2 * meanProjectorNorm (μ i)) ^ (1 - 1 / r)) ∧
  (4 ≤ p → ∀ i, meanDiscrepancy k (μ i) ≤
    gaussianTailMomentConstant k p 2 * Real.sqrt (2 * meanProjectorNorm (μ i)))

example {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hw : ∀ i, k + p ≤ n i)
    (μ : (i : ℕ) → Measure (OrthogonalProjector (n i) (k + p)))
    [∀ i, IsProbabilityMeasure (μ i)] : criterionConclusion n μ :=
  theorem_1_1 hk hp n hn hw μ

-- The fixed-width equivalence requires the manuscript's oversampling range.
example : True := by
  fail_if_success
    have invalid : ∀ {k p : ℕ}, 0 < k →
        ∀ (n : ℕ → ℕ), Tendsto n atTop atTop → (∀ i, k + p ≤ n i) →
        ∀ (μ : (i : ℕ) → Measure (OrthogonalProjector (n i) (k + p))),
          (∀ i, IsProbabilityMeasure (μ i)) → criterionConclusion n μ := by
      exact @theorem_1_1
  trivial

-- The explicit second-moment rate cannot be applied at p = 3.
example {n k : ℕ} (_hk : 0 < k) (_hw : k + 3 ≤ n)
    (μ : Measure (OrthogonalProjector n (k + 3))) [IsProbabilityMeasure μ] : True := by
  fail_if_success
    have invalid : meanDiscrepancy k μ ≤
        gaussianTailMomentConstant k 3 2 * Real.sqrt (2 * meanProjectorNorm μ) := by
      exact paper_root_rate _hk (by decide : 4 ≤ 3) _hw μ
  trivial

end
