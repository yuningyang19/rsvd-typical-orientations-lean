import TypicalOrientations.GaussianMoment
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace TypicalOrientations

open Matrix MeasureTheory SketchOrientation
open scoped ENNReal

noncomputable section

variable {n k p : ℕ}

/-- Lemma 3.2 indexed by the paper's allowed spectra. -/
theorem lemma_3_2 (hk : 0 < k) (hl : k + p ≤ n) (σ : Spectra n k)
    {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) (hp : 2 * r < (p : ℝ) + 1) :
    MemLp (subspaceLoss k σ.val) (ENNReal.ofReal r) (haarSketchProjectorLaw hl) ∧
    lpNorm (subspaceLoss k σ.val) (ENNReal.ofReal r) (haarSketchProjectorLaw hl) ≤
      gaussianTailMomentConstant k p r :=
  haarSubspaceLoss_moment hk hl σ.val σ.property.2.2 hr hr2 hp

/-- The boundedness of the Gaussian comparison is independent of the
singular values because Lemma 3.2 controls the loss at the scale of the tail. -/
theorem gaussianMean_le_momentConstant (hk : 0 < k) (hp : 2 ≤ p) (hl : k + p ≤ n)
    (σ : Spectra n k) :
    gaussianMean k (k + p) σ.val ≤ gaussianTailMomentConstant k p (5 / 4) := by
  let r : ℝ := 5 / 4
  let q := ENNReal.ofReal r
  let ν := haarSketchProjectorLaw hl
  let f := subspaceLoss (l := k+p) k σ.val
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hM := lemma_3_2 hk hl σ (r := r)
    (by norm_num [r]) (by norm_num [r]) (by dsimp [r]; linarith)
  have hf : MemLp f q ν := hM.1
  have hq : 1 ≤ q := ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal (by norm_num [r])
  have he : gaussianMean k (k + p) σ.val = lpNorm f 1 ν := by
    rw [gaussianMean_eq_haarProjector hl, lpNorm_one_eq_integral_norm hf.aestronglyMeasurable]
    apply integral_congr_ae
    exact ae_of_all _ fun P => (Real.norm_of_nonneg
      (residual_div_tail_nonneg k σ.val σ.property.2.2 P.val)).symm
  calc
    _ = lpNorm f 1 ν := he
    _ ≤ lpNorm f q ν := by
      rw [← toReal_eLpNorm hf.aestronglyMeasurable, ← toReal_eLpNorm hf.aestronglyMeasurable]
      exact ENNReal.toReal_mono hf.eLpNorm_ne_top
        (eLpNorm_le_eLpNorm_of_exponent_le hq hf.aestronglyMeasurable)
    _ ≤ _ := hM.2

/-- The family whose supremum defines (D_n) is bounded before applying
any rotation-concentration estimate. -/
theorem meanDiscrepancy_bddAbove (hk : 0 < k) (hp : 2 ≤ p) (hl : k + p ≤ n)
    (μ : Measure (OrthogonalProjector n (k+p))) [IsProbabilityMeasure μ] :
    BddAbove (Set.range fun σ : Spectra n k =>
      ∫ U, |conditionalMean k σ.val μ U - gaussianMean k (k+p) σ.val|
        ∂gaussianRightOrthogonalLaw n) := by
  refine ⟨2 * gaussianTailMomentConstant k p (5 / 4), ?_⟩
  rintro _ ⟨σ, rfl⟩
  let ν := gaussianRightOrthogonalLaw n
  let F := conditionalMean k σ.val μ
  let g := gaussianMean k (k+p) σ.val
  let C := squaredFrobenius (diagonal σ.val) / optimalSquaredTail k σ.val
  have hF0 (U : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ F U :=
    integral_nonneg fun P => residual_div_tail_nonneg k σ.val σ.property.2.2 (U * P.val)
  have hg0 : 0 ≤ g :=
    integral_nonneg fun G => residual_div_tail_nonneg k σ.val σ.property.2.2 G
  have hFB (U : Matrix (Fin n) (Fin n) ℝ) : ‖F U‖ ≤ C := by
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun P => squaredResidual (diagonal σ.val) (U * P.val) / optimalSquaredTail k σ.val)
      (C := C) (ae_of_all _ fun P => by
        rw [Real.norm_of_nonneg (residual_div_tail_nonneg k σ.val σ.property.2.2 _)]
        exact residual_div_tail_le k σ.val σ.property.2.2 _)
    simpa only [F, conditionalMean, probReal_univ, mul_one] using h
  have hmeas : Measurable F := measurable_conditionalMean k σ.val μ
  have hI : Integrable F ν := Integrable.of_bound hmeas.aestronglyMeasurable C (ae_of_all _ hFB)
  have hG : Integrable (fun U => F U + g) ν := hI.add (integrable_const g)
  have hpoint (U : Matrix (Fin n) (Fin n) ℝ) : |F U - g| ≤ F U + g := by
    rw [abs_le]
    constructor <;> linarith [hF0 U, hg0]
  have hgap : Integrable (fun U => |F U - g|) ν :=
    hG.mono' (hmeas.sub_const g).abs.aestronglyMeasurable
      (ae_of_all _ fun U => by rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hpoint U)
  calc
    _ ≤ ∫ U, (F U + g) ∂ν := integral_mono hgap hG hpoint
    _ = 2 * g := by
      rw [integral_add hI (integrable_const g)]
      change (∫ U, conditionalMean k σ.val μ U ∂ν) + (∫ _ : Matrix (Fin n) (Fin n) ℝ, g ∂ν) = _
      rw [conditionalMean_integral_eq_gaussianMean hl k σ.val σ.property.2.2 μ]
      simp only [integral_const, probReal_univ, one_smul, g, two_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussianMean_le_momentConstant hk hp hl σ) (by norm_num)

end

end TypicalOrientations
