import SketchOrientation.GaussianOrientationConverse

namespace SketchOrientation

open MeasureTheory Filter Matrix
open scoped Topology

/-- Typical target orientations (Theorem 1.1). The dimensions may be
indexed by any sequence tending to infinity. The gap sequence may take
both finite values and the infinite endpoint. -/
theorem theorem_1_1 {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (D : ℕ → ℕ) (hD : ∀ i, k + p ≤ D i) (hDt : Tendsto D atTop atTop)
    (ν : ∀ i, Measure (OrthogonalProjector (D i) (k + p)))
    [∀ i, IsProbabilityMeasure (ν i)] (Γ : ℕ → WithTop ℝ)
    (hΓ : Tendsto (fun i => orientationGapScale (D i) k (Γ i)) atTop (𝓝 ⊤)) :
    let η (i : ℕ) := gaussianHaarFrameLaw (show k ≤ D i from le_trans (Nat.le_add_right _ _) (hD i))
    let X (i : ℕ) := fun V : Matrix (Fin (D i)) (Fin k) ℝ =>
      haarOrientationMeanAt (ν i) (Γ i) V - haarOrientationBenchmark (D i) k (k + p)
    let Diffuse := Tendsto (fun i => ‖(meanSketchProjector (ν i)).toEuclideanLin.toContinuousLinearMap‖)
      atTop (𝓝 0)
    let InProbability := ∀ ε : ℝ, 0 < ε → Tendsto (fun i => (η i).real {V | ε ≤ |X i V|}) atTop (𝓝 0)
    let InMean := Tendsto (fun i => ∫ V, |X i V| ∂η i) atTop (𝓝 0)
    (Diffuse ↔ InProbability) ∧ (Diffuse ↔ InMean) := by
  intro η X Diffuse InProbability InMean
  have h₁ : Diffuse → InMean := haarOrientationL1_of_diffuse hk hp D hD ν Γ hΓ
  have h₂ : InMean → InProbability := haarOrientationProbability_of_L1 hk hp D hD ν Γ hΓ
  have h₃ : InProbability → Diffuse := haarOrientationDiffuse_of_probability hk hp D hD hDt ν Γ hΓ
  exact ⟨⟨h₂ ∘ h₁, h₃⟩, ⟨h₁, h₃ ∘ h₂⟩⟩

/-- Theorem 1.1's uniform rate for the actual Euclidean operator norm of
the mean projector and all finite or infinite gaps above a finite threshold. -/
theorem theorem_1_1_uniform_rate {n k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (hn : k + p ≤ n) (ν : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure ν]
    {Γ₀ r : ℝ} (hΓ₀ : 1 < Γ₀) (hr : 1 < r) (hr₂ : r ≤ 2) (hr' : 2 * r < (p : ℝ) + 1) :
    (∫ V, haarOrientationUniformDeviation ν Γ₀ V ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤
      orientationRateConstant p r *
        (‖(meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap‖ ^ (1 - 1 / r) +
          ((n : ℝ) * k / (Γ₀ - 1)) ^ (r - 1)) := by
  rw [← meanProjectedEnergy_eq_meanSketchProjector_norm (by omega) ν]
  exact haarOrientationUniformDeviation_bound_paper hk hp hn ν hΓ₀ hr hr₂ hr'

/-- The endpoint specialization of Theorem 1.1 has only the orientation term. -/
theorem theorem_1_1_endpoint_rate {n k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (hn : k + p ≤ n) (ν : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 1 < r) (hr₂ : r ≤ 2) (hr' : 2 * r < (p : ℝ) + 1) :
    (∫ V, |haarOrientationEndpoint ν V - haarOrientationBenchmark n k (k + p)|
      ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤
      orientationRateConstant p r *
        ‖(meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap‖ ^ (1 - 1 / r) := by
  have h := haarOrientationMeanAt_L1_bound hk hp hn ν
    (Γ := (⊤ : WithTop ℝ)) (WithTop.coe_lt_top _) hr hr₂ hr'
  change (∫ V, |haarOrientationEndpoint ν V - haarOrientationBenchmark n k (k + p)|
    ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤
    orientationRateConstant p r * (meanProjectedEnergy ν orientationRowSpace ^ (1 - 1 / r) +
      (0 : ℝ) ^ (r - 1)) at h
  rw [Real.zero_rpow (sub_pos.mpr hr).ne', add_zero,
    meanProjectedEnergy_eq_meanSketchProjector_norm (by omega) ν] at h
  exact h

/-- From oversampling four onward the infinite-gap rate is a square-root rate. -/
theorem theorem_1_1_endpoint_sqrt {n k p : ℕ} (hk : 0 < k) (hp : 4 ≤ p)
    (hn : k + p ≤ n) (ν : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure ν] :
    (∫ V, |haarOrientationEndpoint ν V - haarOrientationBenchmark n k (k + p)|
      ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤
      orientationRateConstant p 2 * Real.sqrt ‖(meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap‖ := by
  have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have h := theorem_1_1_endpoint_rate hk (by omega) hn ν
    (r := (2 : ℝ)) (by norm_num) le_rfl (by linarith)
  have he : (1 : ℝ) - 1 / 2 = (1 : ℝ) / 2 := by norm_num
  rw [he, ← Real.sqrt_eq_rpow] at h
  exact h

end SketchOrientation
