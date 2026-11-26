import TypicalOrientations.PaperTheorems
import Mathlib.Probability.Moments.Covariance

namespace TypicalOrientations

open Filter Matrix MeasureTheory ProbabilityTheory SketchOrientation
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

variable {n k p l : ℕ}

/-- The introduction's orientation probability bound, for the paper's strict event. -/
theorem orientationGap_probability_le (hk : 0 < k) (hp : 2 ≤ p) (hn : k + p ≤ n)
    (μ : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure μ]
    (σ : Spectra n k) {ε : ℝ} (hε : 0 < ε) :
    (gaussianRightOrthogonalLaw n).real {U | ε < orientationGap k μ σ U} ≤
      meanDiscrepancy k μ / ε := by
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun U => abs_nonneg (conditionalMean k σ.val μ U - gaussianMean k (k+p) σ.val))
    (integrable_orientationGap σ μ) ε
  have hmono := measureReal_mono (μ := gaussianRightOrthogonalLaw n)
    (s₁ := {U | ε < orientationGap k μ σ U}) (s₂ := {U | ε ≤ orientationGap k μ σ U})
    (fun _ h => Set.mem_ofPred_eq.mpr (le_of_lt (Set.mem_ofPred_eq.mp h)))
  have hD := le_csSup (meanDiscrepancy_bddAbove hk hp hn μ)
    (Set.mem_range_self σ)
  apply (le_div_iff₀ hε).2
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono hε.le).trans (hMarkov.trans hD)

/-- The dimensional lower bound and unit upper bound of §2.1. -/
theorem meanProjectorNorm_mem_interval (hn : 0 < n)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    meanProjectorNorm μ ∈ Set.Icc ((l : ℝ) / n) 1 := by
  have he : meanProjectedEnergy μ orientationRowSpace = meanProjectorNorm μ :=
    meanProjectedEnergy_eq_meanSketchProjector_norm hn μ
  constructor
  · apply (div_le_iff₀ (Nat.cast_pos.mpr hn : (0 : ℝ) < n)).2
    rw [mul_comm, ← he]
    exact sketchRank_le_dim_mul_meanProjectedEnergy μ
  · rw [← he]
    unfold meanProjectedEnergy
    apply csSup_le
    · let i : Fin n := ⟨0, hn⟩
      have hu : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
        simp [EuclideanSpace.single, PiLp.norm_single]
      exact Set.range_nonempty_iff_nonempty.mpr ⟨⟨_, hu⟩⟩
    · rintro _ ⟨u, rfl⟩
      have h (P : OrthogonalProjector n l) :
          ‖(orientationRowSpace P).starProjection u‖ ^ 2 ≤ 1 := by
        calc
          _ ≤ ‖(u : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) ((orientationRowSpace P).norm_starProjection_apply_le _) _
          _ = 1 := by rw [u.property, one_pow]
      simpa using
        integral_mono (integrable_projected_energy μ orientationRowSpace u
          (measurable_orientationRowSpace_projection _)) (integrable_const (1 : ℝ)) h

/-- Standard deviation of the conditional mean for the numerical illustration. -/
theorem conditionalMean_standardDeviation_eq (hn : l ≤ n)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] (σ : Spectra n k) :
    Real.sqrt (Var[conditionalMean k σ.val μ; gaussianRightOrthogonalLaw n]) =
      Real.sqrt (∫ U, |conditionalMean k σ.val μ U - gaussianMean k l σ.val| ^ 2
        ∂gaussianRightOrthogonalLaw n) := by
  rw [variance_eq_integral (measurable_conditionalMean k σ.val μ).aemeasurable,
    conditionalMean_integral_eq_gaussianMean hn k σ.val σ.property.2.2 μ]
  simp only [sq_abs]

/-- The numerical illustration's uniform bound on standard deviation. -/
theorem conditionalMean_standardDeviation_le (hk : 0 < k) (hp : 4 ≤ p) (hn : k + p ≤ n)
    (μ : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure μ] (σ : Spectra n k) :
    Real.sqrt (Var[conditionalMean k σ.val μ; gaussianRightOrthogonalLaw n]) ≤
      gaussianTailMomentConstant k p 2 * Real.sqrt (2 * meanProjectorNorm μ) := by
  let f := subspaceLoss (l := k+p) k σ.val
  let ν := haarSketchProjectorLaw hn
  have hf (P : OrthogonalProjector n (k+p)) :
      0 ≤ f P ∧ |f P| ≤ squaredFrobenius (diagonal σ.val) / optimalSquaredTail k σ.val := by
    have h := residual_div_tail_nonneg k σ.val σ.property.2.2 P.val
    have h' : 0 ≤ f P := h
    exact ⟨h', by rw [abs_of_nonneg h']; exact residual_div_tail_le k σ.val σ.property.2.2 P.val⟩
  have hV := lemma_3_1 (by omega : 0 < k+p) hn μ f (measurable_subspaceLoss k σ.val)
    ⟨_, fun P => (hf P).2⟩
  have hLaw := averaged_foldedLoss_identDistrib k σ.val μ id measurable_id
  have hRot : Var[conditionalMean k σ.val μ; gaussianRightOrthogonalLaw n] ≤
      2 * meanProjectorNorm μ * Var[f; ν] := hLaw.variance_eq.trans_le hV
  have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hM := lemma_3_2 hk hn σ (r := 2) (by norm_num) le_rfl (by linarith)
  have hNorm : Real.sqrt (∫ P, f P ^ 2 ∂ν) = lpNorm f (ENNReal.ofReal (2 : ℝ)) ν := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofReal_ne_top
      hM.1.aestronglyMeasurable, Real.sqrt_eq_rpow, ENNReal.toReal_ofReal (by norm_num)]
    change (∫ P, f P ^ 2 ∂ν) ^ (1/2 : ℝ) = (∫ P, ‖f P‖ ^ (2 : ℝ) ∂ν) ^ (2 : ℝ)⁻¹
    simp_rw [one_div, show ∀ P, ‖f P‖ = f P from fun P => Real.norm_of_nonneg (hf P).1,
      Real.rpow_two]
  have hNonneg : 0 ≤ 2 * meanProjectorNorm μ := by unfold meanProjectorNorm; positivity
  calc
    _ ≤ Real.sqrt (2 * meanProjectorNorm μ * Var[f; ν]) := Real.sqrt_le_sqrt hRot
    _ = Real.sqrt (2 * meanProjectorNorm μ) * Real.sqrt (Var[f; ν]) :=
      Real.sqrt_mul hNonneg _
    _ ≤ Real.sqrt (2 * meanProjectorNorm μ) * lpNorm f (ENNReal.ofReal (2 : ℝ)) ν := by
      rw [← hNorm]
      gcongr
      exact variance_le_expectation_sq hM.1.aestronglyMeasurable
    _ ≤ _ := (mul_le_mul_of_nonneg_left hM.2 (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _)

/-- The growing-width consequence following Corollary 4.2. -/
theorem paper_growingWidth_meanDiscrepancy_tendsto {d p : ℕ → ℕ} {k : ℕ} (hk : 0 < k)
    (hl : ∀ j, k + p j ≤ d j)
    (μ : ∀ j, Measure (OrthogonalProjector (d j) (k + p j)))
    [∀ j, IsProbabilityMeasure (μ j)]
    (hp : ∀ᶠ j in atTop, 4 ≤ p j)
    (hIso : ∀ᶠ j in atTop, meanProjectorNorm (μ j) = ((k + p j : ℕ) : ℝ) / d j)
    (hsmall : Tendsto (fun j => ((k + p j : ℕ) : ℝ) / d j) atTop (𝓝 0)) :
    Tendsto (fun j => meanDiscrepancy k (μ j)) atTop (𝓝 0) := by
  apply growingWidth_meanDiscrepancy_tendsto hk hl μ hp hIso _ hsmall
  filter_upwards [hp] with j hj σ
  apply lemma_3_1 (by omega : 0 < k + p j) (hl j) (μ j)
  · exact measurable_subspaceLoss k σ.val
  · refine ⟨squaredFrobenius (diagonal σ.val) / optimalSquaredTail k σ.val, fun P => ?_⟩
    have h : 0 ≤ subspaceLoss k σ.val P :=
      residual_div_tail_nonneg k σ.val σ.property.2.2 P.val
    rw [abs_of_nonneg h]
    exact residual_div_tail_le k σ.val σ.property.2.2 P.val

end
end TypicalOrientations
