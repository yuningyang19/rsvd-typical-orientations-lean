import TypicalOrientations.ConditionalUpperBound
import TypicalOrientations.BenchmarkBound
import TypicalOrientations.SpikeQuantitative

namespace TypicalOrientations

open Filter Matrix MeasureTheory Set SketchOrientation
open scoped ENNReal Topology

noncomputable section

theorem subspaceLoss_rpow_integral_le {n k p : ℕ} (hk : 0 < k) (hl : k + p ≤ n)
    (σ : Spectra n k) {r : ℝ} (hr : 1 < r) (hr₂ : r ≤ 2) (hp : 2 * r < (p : ℝ) + 1) :
    (∫ P, subspaceLoss k σ.val P ^ r ∂haarSketchProjectorLaw hl) ≤
      (gaussianTailMomentConstant k p r) ^ r := by
  let H := subspaceLoss (l := k + p) k σ.val
  let ν := haarSketchProjectorLaw hl
  let K := gaussianTailMomentConstant k p r
  have hr0 : 0 < r := by linarith
  have hLp := (lemma_3_2 hk hl σ hr hr₂ hp).2
  have he := lpNorm_eq_integral_norm_rpow_toReal (f := H) (μ := ν)
    (p := ENNReal.ofReal r) (by positivity) (by simp)
    (measurable_subspaceLoss k σ.val).aestronglyMeasurable
  rw [ENNReal.toReal_ofReal hr0.le] at he
  have h0 (P : OrthogonalProjector n (k + p)) : 0 ≤ H P :=
    residual_div_tail_nonneg k σ.val σ.property.2.2 P.val
  simp_rw [Real.norm_of_nonneg (h0 _)] at he
  have hInt : 0 ≤ (∫ P, H P ^ r ∂ν) :=
    integral_nonneg fun P => Real.rpow_nonneg (h0 P) _
  have hK := gaussianTailMomentConstant_pos hr0 hp (k := k)
  have hle : (∫ P, H P ^ r ∂ν) ^ r⁻¹ ≤ K := he ▸ hLp
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hInt r⁻¹) hle hr0.le
  rw [← Real.rpow_mul hInt, inv_mul_cancel₀ hr0.ne', Real.rpow_one] at hpow
  exact hpow

/-- The explicit rate (3.6) from the shared-rotation variance estimate. -/
theorem meanDiscrepancy_paper_rate_of_variance {n k p : ℕ}
    (hk : 0 < k) (hl : k + p ≤ n)
    (μ : Measure (OrthogonalProjector n (k+p))) [IsProbabilityMeasure μ]
    (hVar : SharedRotationVariance hl μ)
    {r : ℝ} (hr : 1 < r) (hr₂ : r ≤ 2) (hp : 2 * r < (p : ℝ) + 1) :
    meanDiscrepancy k μ ≤
      3 * gaussianTailMomentConstant k p r * (2 * meanProjectorNorm μ) ^ (1 - 1 / r) :=
  meanDiscrepancy_le_of_variance hl (by omega) μ hVar hr hr₂
    (gaussianTailMomentConstant_pos (by linarith) hp) fun σ =>
      subspaceLoss_rpow_integral_le hk hl σ hr hr₂ hp

/-- The paper's limit equivalence conditional on the Haar variance estimate.
The necessary implication invokes the independently proved one-spike chain. -/
theorem criterion_of_sharedRotationVariance {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hℓn : ∀ i, k + p ≤ n i)
    (μ : ∀ i, Measure (OrthogonalProjector (n i) (k+p))) [∀ i, IsProbabilityMeasure (μ i)]
    (hVar : ∀ i, SharedRotationVariance (hℓn i) (μ i)) :
    Tendsto (fun i => meanProjectorNorm (μ i)) atTop (𝓝 0) ↔
      Tendsto (fun i => meanDiscrepancy k (μ i)) atTop (𝓝 0) := by
  refine ⟨?_, meanProjectorNorm_tendsto_zero_of_discrepancy hk hp n hn μ⟩
  intro hρ
  let C := 3 * gaussianTailMomentConstant k p (5 / 4)
  have hRate (i : ℕ) : meanDiscrepancy k (μ i) ≤
      C * (2 * meanProjectorNorm (μ i)) ^ (1 - 1 / (5 / 4 : ℝ)) :=
    meanDiscrepancy_paper_rate_of_variance hk (hℓn i) (μ i) (hVar i)
      (by norm_num) (by norm_num) (by have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
                                      linarith)
  have hD₀ (i : ℕ) : 0 ≤ meanDiscrepancy k (μ i) := by
    have hSpec := oneSpikeSpectra hk (show k < n i by have := hℓn i; omega)
    apply (integral_nonneg fun _ => abs_nonneg _).trans
      (le_csSup (meanDiscrepancy_bddAbove hk hp (hℓn i) (μ i)) (Set.mem_range_self hSpec))
  have hρ' : Tendsto (fun i => 2 * meanProjectorNorm (μ i)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hρ.const_mul 2
  have hLim := (hρ'.rpow_const_nhds_zero (p := 1 - 1 / (5 / 4 : ℝ)) (by norm_num)).const_mul C
  rw [mul_zero] at hLim
  exact squeeze_zero' (Eventually.of_forall hD₀) (Eventually.of_forall hRate) hLim

end

end TypicalOrientations
