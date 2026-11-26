import TypicalOrientations.BenchmarkBound
import TypicalOrientations.ReflectionTransfer
import TypicalOrientations.Truncation

namespace TypicalOrientations

open Filter Matrix MeasureTheory ProbabilityTheory SketchOrientation
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

variable {n k p : ℕ}

/-- Equation (3.7) at one spectrum. The rotation variance input is stated
on the original, unclipped residual as in the paper's (r=2) argument. -/
theorem residualMean_rootRate_of_variance (hk : 0 < k) (hp : 4 ≤ p) (hl : k + p ≤ n)
    (μ : Measure (OrthogonalProjector n (k+p))) [IsProbabilityMeasure μ]
    (σ : Spectra n k)
    (hRotation :
      Var[fun U => ∫ P, subspaceLoss k σ.val (rotateProjector U P) ∂μ;
        specialOrientationLaw n] ≤
        2 * meanProjectorNorm μ * Var[subspaceLoss k σ.val; haarSketchProjectorLaw hl]) :
    (∫ U, |conditionalMean k σ.val μ U - gaussianMean k (k+p) σ.val|
      ∂gaussianRightOrthogonalLaw n) ≤
      gaussianTailMomentConstant k p 2 * Real.sqrt (2 * meanProjectorNorm μ) := by
  let ν := haarSketchProjectorLaw hl
  let η := gaussianRightOrthogonalLaw n
  let f := subspaceLoss (l := k+p) k σ.val
  let F := conditionalMean k σ.val μ
  let C := squaredFrobenius (diagonal σ.val) / optimalSquaredTail k σ.val
  let ρ := meanProjectorNorm μ
  have htail := σ.property.2.2
  have hF0 (U : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ F U :=
    integral_nonneg fun P => residual_div_tail_nonneg k σ.val htail (U * P.val)
  have hFBound (U : Matrix (Fin n) (Fin n) ℝ) : F U ≤ C := by
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun P => squaredResidual (diagonal σ.val) (U * P.val) / optimalSquaredTail k σ.val)
      (C := C) (ae_of_all _ fun P => by
        rw [Real.norm_of_nonneg (residual_div_tail_nonneg k σ.val htail _)]
        exact residual_div_tail_le k σ.val htail _)
    have h' : ‖F U‖ ≤ C := by simpa only [F, conditionalMean, probReal_univ, mul_one] using h
    rwa [Real.norm_of_nonneg (hF0 U)] at h'
  have hF₂ : MemLp F 2 η := memLp_two_of_nonneg_bound η
    (measurable_conditionalMean k σ.val μ) hF0 hFBound
  have hcenter := conditionalMean_integral_eq_gaussianMean hl k σ.val htail μ
  have hFLaw := averaged_foldedLoss_identDistrib k σ.val μ id measurable_id
  have hFV : Var[F; η] ≤ 2 * ρ * Var[f; ν] :=
    hFLaw.variance_eq.trans_le hRotation
  have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hM := lemma_3_2 hk hl σ (r := 2) (by norm_num) le_rfl (by linarith)
  have hEq : Real.sqrt (∫ P, f P ^ 2 ∂ν) =
      lpNorm f (ENNReal.ofReal (2 : ℝ)) ν := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofReal_ne_top
      hM.1.aestronglyMeasurable, Real.sqrt_eq_rpow,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
    change (∫ P, f P ^ 2 ∂ν) ^ (1/2 : ℝ) = (∫ P, ‖f P‖ ^ (2 : ℝ) ∂ν) ^ (2 : ℝ)⁻¹
    simp_rw [one_div, show ∀ P, ‖f P‖ = f P from fun P =>
      Real.norm_of_nonneg (residual_div_tail_nonneg k σ.val htail P.val), Real.rpow_two]
  have hVarf : Var[f; ν] ≤ ∫ P, f P ^ 2 ∂ν :=
    variance_le_expectation_sq hM.1.aestronglyMeasurable
  have hρ : 0 ≤ 2 * ρ := by unfold ρ meanProjectorNorm; positivity
  calc
    _ ≤ Real.sqrt (Var[F; η]) := by
      have h := absolute_centered_mean_le_sqrt_variance η hF₂
      rw [show (∫ U, F U ∂η) = gaussianMean k (k+p) σ.val from hcenter] at h
      exact h
    _ ≤ Real.sqrt (2 * ρ * Var[f; ν]) := Real.sqrt_le_sqrt hFV
    _ = Real.sqrt (2 * ρ) * Real.sqrt (Var[f; ν]) := Real.sqrt_mul hρ _
    _ ≤ Real.sqrt (2 * ρ) * lpNorm f (ENNReal.ofReal (2 : ℝ)) ν := by
      rw [← hEq]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hVarf) (Real.sqrt_nonneg _)
    _ ≤ gaussianTailMomentConstant k p 2 * Real.sqrt (2 * ρ) :=
      (mul_le_mul_of_nonneg_left hM.2 (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _)

/-- Equation (3.7) after taking the supremum over all prescribed spectra. -/
theorem meanDiscrepancy_rootRate_of_variance (hk : 0 < k) (hp : 4 ≤ p) (hl : k + p ≤ n)
    (μ : Measure (OrthogonalProjector n (k+p))) [IsProbabilityMeasure μ]
    (hRotation : ∀ σ : Spectra n k,
      Var[fun U => ∫ P, subspaceLoss k σ.val (rotateProjector U P) ∂μ;
        specialOrientationLaw n] ≤
        2 * meanProjectorNorm μ * Var[subspaceLoss k σ.val; haarSketchProjectorLaw hl]) :
    meanDiscrepancy k μ ≤
      gaussianTailMomentConstant k p 2 * Real.sqrt (2 * meanProjectorNorm μ) := by
  unfold meanDiscrepancy
  by_cases h : (Set.range fun σ : Spectra n k =>
    ∫ U, |conditionalMean k σ.val μ U - gaussianMean k (k+p) σ.val|
      ∂gaussianRightOrthogonalLaw n).Nonempty
  · refine csSup_le h ?_
    rintro _ ⟨σ, rfl⟩
    exact residualMean_rootRate_of_variance hk hp hl μ σ (hRotation σ)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty]
    have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
    exact mul_nonneg (gaussianTailMomentConstant_pos (by norm_num) (by linarith)).le
      (Real.sqrt_nonneg _)

/-- For every oversampling level at least four, the exact (r=2) factor
is at most (1+k). -/
theorem gaussianTailMomentConstant_two_le (hp : 4 ≤ p) :
    gaussianTailMomentConstant k p 2 ≤ 1 + (k : ℝ) := by
  rw [gaussianTailMomentConstant_two hp]
  apply add_le_add le_rfl
  apply mul_le_of_le_one_right (Nat.cast_nonneg k)
  have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₁ : (3 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hp₃ : (1 : ℝ) ≤ (p : ℝ) - 3 := by linarith
  have h3 : (3 : ℝ) ≤ ((p : ℝ) - 1) * ((p : ℝ) - 3) := by
    simpa only [mul_one] using mul_le_mul hp₁ hp₃ (by norm_num) (by linarith)
  have hden : 0 < ((p : ℝ) - 1) * ((p : ℝ) - 3) :=
    (show (0 : ℝ) < 3 by norm_num).trans_le h3
  have hfrac : 3 / (((p : ℝ) - 1) * ((p : ℝ) - 3)) ≤ 1 := (div_le_one₀ hden).2 h3
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hfrac

/-- Convergence in the growing-width remark. The finite-dimension laws
are isotropic with mean projector norm (ell/n). -/
theorem growingWidth_meanDiscrepancy_tendsto {n p : ℕ → ℕ} {k : ℕ} (hk : 0 < k)
    (hl : ∀ j, k + p j ≤ n j)
    (μ : ∀ j, Measure (OrthogonalProjector (n j) (k + p j)))
    [∀ j, IsProbabilityMeasure (μ j)]
    (hp : ∀ᶠ j in atTop, 4 ≤ p j)
    (hIso : ∀ᶠ j in atTop, meanProjectorNorm (μ j) = ((k + p j : ℕ) : ℝ) / n j)
    (hVar : ∀ᶠ j in atTop, ∀ σ : Spectra (n j) k,
      Var[fun U => ∫ P, subspaceLoss k σ.val (rotateProjector U P) ∂μ j;
        specialOrientationLaw (n j)] ≤
        2 * meanProjectorNorm (μ j) * Var[subspaceLoss k σ.val; haarSketchProjectorLaw (hl j)])
    (hsmall : Tendsto (fun j => ((k + p j : ℕ) : ℝ) / n j) atTop (𝓝 0)) :
    Tendsto (fun j => meanDiscrepancy k (μ j)) atTop (𝓝 0) := by
  let q (j : ℕ) := ((k + p j : ℕ) : ℝ) / n j
  have hq : Tendsto q atTop (𝓝 0) := hsmall
  have h2q : Tendsto (fun j => 2 * q j) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := (2 : ℝ))).mul hq
  have hB : Tendsto (fun j => (1 + (k : ℝ)) * Real.sqrt (2 * q j)) atTop (𝓝 0) := by
    have hSq : Tendsto (fun j => Real.sqrt (2 * q j)) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp h2q
    simpa only [Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds (x := 1 + (k : ℝ))).mul hSq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB ?_ ?_
  · filter_upwards [hp] with j hjp
    let d := fun σ : Spectra (n j) k =>
      ∫ U, |conditionalMean k σ.val (μ j) U - gaussianMean k (k + p j) σ.val|
        ∂gaussianRightOrthogonalLaw (n j)
    change 0 ≤ sSup (Set.range d)
    by_cases hn : (Set.range d).Nonempty
    · rcases hn with ⟨_, ⟨σ, rfl⟩⟩
      exact (integral_nonneg fun _ => abs_nonneg _).trans
        (le_csSup (meanDiscrepancy_bddAbove hk (by omega) (hl j) (μ j)) ⟨σ, rfl⟩)
    · rw [Set.not_nonempty_iff_eq_empty.mp hn, Real.sSup_empty]
  · filter_upwards [hp, hIso, hVar] with j hjp hjiso hjvar
    have h := meanDiscrepancy_rootRate_of_variance hk hjp (hl j) (μ j) hjvar
    rw [hjiso] at h
    exact h.trans (mul_le_mul_of_nonneg_right (gaussianTailMomentConstant_two_le hjp)
      (Real.sqrt_nonneg _))


end

end TypicalOrientations
