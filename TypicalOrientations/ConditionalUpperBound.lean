import TypicalOrientations.ReflectionTransfer
import TypicalOrientations.Truncation

namespace TypicalOrientations

open Filter Matrix MeasureTheory ProbabilityTheory Set SketchOrientation
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

variable {n k l : ℕ}

/-- The exact variance statement retained as an unresolved premise for
the development of its consequences. -/
def SharedRotationVariance (hl : l ≤ n) (μ : Measure (OrthogonalProjector n l)) : Prop :=
  ∀ (f : OrthogonalProjector n l → ℝ), Measurable f → (∃ B, ∀ S, |f S| ≤ B) →
    Var[fun U => ∫ P, f (rotateProjector U P) ∂μ; specialOrientationLaw n] ≤
      2 * meanProjectorNorm μ * Var[f; haarSketchProjectorLaw hl]

theorem meanProjectorNorm_pos (hn : 0 < n) (hl : 0 < l)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    0 < meanProjectorNorm μ := by
  have h := sketchRank_le_dim_mul_meanProjectedEnergy μ
  rw [meanProjectedEnergy_eq_meanSketchProjector_norm hn μ] at h
  change (l : ℝ) ≤ (n : ℝ) * meanProjectorNorm μ at h
  exact pos_of_mul_pos_right ((Nat.cast_pos.mpr hl).trans_le h) (Nat.cast_nonneg _)

private theorem spectrumLossBound (k : ℕ) (σ : Fin n → ℝ)
    (htail : 0 < optimalSquaredTail k σ) :
    ∀ P : OrthogonalProjector n l,
      |subspaceLoss k σ P| ≤ squaredFrobenius (diagonal σ) / optimalSquaredTail k σ := fun P => by
  rw [subspaceLoss, abs_of_nonneg (residual_div_tail_nonneg k σ htail P.val)]
  exact residual_div_tail_le k σ htail P.val

set_option maxHeartbeats 650000 in
/-- The rate in (3.6), before taking the supremum in (1.4). -/
theorem residualMeanRate_of_variance (hl : l ≤ n) (hl' : 0 < l)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ]
    (hVar : SharedRotationVariance hl μ) (σ : Spectra n k)
    {r K : ℝ} (hr : 1 < r) (hr₂ : r ≤ 2) (hK : 0 < K)
    (hM : (∫ P, subspaceLoss k σ.val P ^ r ∂haarSketchProjectorLaw hl) ≤ K ^ r) :
    (∫ U, |conditionalMean k σ.val μ U - gaussianMean k l σ.val|
      ∂gaussianRightOrthogonalLaw n) ≤ 3 * K * (2 * meanProjectorNorm μ) ^ (1 - 1 / r) := by
  let ν := haarSketchProjectorLaw hl
  let g := subspaceLoss (l := l) k σ.val
  let Y := fun (P : OrthogonalProjector n l) (U : Matrix (Fin n) (Fin n) ℝ) =>
    squaredResidual (diagonal σ.val) (U * P.val) / optimalSquaredTail k σ.val
  let η := gaussianRightOrthogonalLaw n
  let ρ := meanProjectorNorm μ
  let a := K * (2 * ρ) ^ (-1 / r)
  have hTail := σ.property.2.2
  have hρ : 0 < ρ := meanProjectorNorm_pos (hl'.trans_le hl) hl' μ
  have ha : 0 < a := mul_pos hK (Real.rpow_pos_of_pos (by positivity) _)
  have hY : Measurable (Function.uncurry Y) := by
    have hP : Measurable (fun z : OrthogonalProjector n l × Matrix (Fin n) (Fin n) ℝ => z.1.val) :=
      measurable_subtype_coe.comp measurable_fst
    have hP' : Measurable (fun z : OrthogonalProjector n l × Matrix (Fin n) (Fin n) ℝ => z.2 * z.1.val) :=
      measurable_matrix_product measurable_snd hP
    exact (measurable_rawResidual (A := fun _ => diagonal σ.val) measurable_const hP').div_const _
  have hg := measurable_subspaceLoss (l := l) k σ.val
  have hgn (P : OrthogonalProjector n l) : 0 ≤ g P := residual_div_tail_nonneg k σ.val hTail P.val
  have hgB := spectrumLossBound (l := l) k σ.val hTail
  have hgLp : MemLp g 2 ν :=
    memLp_two_of_nonneg_bound ν hg hgn (fun P => (le_abs_self _).trans (hgB P))
  have hGM : Integrable (fun P => g P ^ r) ν := by
    apply Integrable.of_bound (hg.pow_const r).aestronglyMeasurable
      ((squaredFrobenius (diagonal σ.val) / optimalSquaredTail k σ.val) ^ r)
    apply ae_of_all
    intro P
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hgn P) _)]
    exact Real.rpow_le_rpow (hgn P) ((le_abs_self _).trans (hgB P)) (by linarith)
  have hLaw (P : OrthogonalProjector n l) : IdentDistrib (Y P) g η ν := by
    have hG := rotatedLoss_identDistrib_gaussian hl k σ.val P
    exact ⟨hG.aemeasurable_fst, hg.aemeasurable, hG.map_eq.trans
      (gaussianLossLaw_eq_haarProjector hl k σ.val)⟩
  let f := fun P => min (g P) a
  have hf : Measurable f := hg.min measurable_const
  have hfB : ∃ B, ∀ S, |f S| ≤ B := ⟨a, fun S => by
    rw [abs_of_nonneg (le_min (hgn S) ha.le)]
    exact min_le_right _ _⟩
  have hVar' : Var[fun U => ∫ P, min (Y P U) a ∂μ; η] ≤ 2 * ρ * Var[f; ν] := by
    rw [(averaged_foldedLoss_identDistrib k σ.val μ (fun x => min x a)
      (measurable_id.min measurable_const)).variance_eq]
    exact hVar f hf hfB
  have hEstimate := l1_mean_le_of_truncated_variance μ η ν Y hY
    (fun P U => residual_div_tail_nonneg k σ.val hTail (U * P.val)) g
    (hgLp.integrable (by norm_num)) hgn hLaw ha hr hr₂ (by positivity : 0 ≤ 2 * ρ) hGM hM hVar'
  rw [paper_cutoff_bound_eq hρ hK hr] at hEstimate
  rw [gaussianMean_eq_haarProjector hl k σ.val]
  exact hEstimate

/-- Taking the outer supremum preserves the estimate because the cutoff
and moment bound are independent of the spectrum. -/
theorem meanDiscrepancy_le_of_variance (hl : l ≤ n) (hl' : 0 < l)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ]
    (hVar : SharedRotationVariance hl μ)
    {r K : ℝ} (hr : 1 < r) (hr₂ : r ≤ 2) (hK : 0 < K)
    (hM : ∀ σ : Spectra n k, (∫ P, subspaceLoss k σ.val P ^ r ∂haarSketchProjectorLaw hl) ≤ K ^ r) :
    meanDiscrepancy k μ ≤ 3 * K * (2 * meanProjectorNorm μ) ^ (1 - 1 / r) := by
  unfold meanDiscrepancy
  by_cases h : (Set.range fun σ : Spectra n k =>
    ∫ U, |conditionalMean k σ.val μ U - gaussianMean k l σ.val|
      ∂gaussianRightOrthogonalLaw n).Nonempty
  · apply csSup_le h
    rintro _ ⟨σ, rfl⟩
    exact residualMeanRate_of_variance hl hl' μ hVar σ hr hr₂ hK (hM σ)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by unfold meanProjectorNorm; positivity) _)

end

end TypicalOrientations
