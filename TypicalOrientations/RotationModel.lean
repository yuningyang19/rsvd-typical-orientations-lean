import SketchOrientation.CosineWindowHaar
import SketchOrientation.ProjectorOverlap
import SketchOrientation.UnequalSpikesHaar

namespace TypicalOrientations

open Matrix MeasureTheory SketchOrientation

noncomputable section

variable {n k l : ℕ}

/-- The squared singular values strictly after the first k positions. -/
def optimalSquaredTail (k : ℕ) (σ : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), σ i ^ 2

/-- Spectra are sorted in decreasing order. Zero singular values are allowed. -/
def Spectra (n k : ℕ) :=
  {σ : Fin n → ℝ // Antitone σ ∧ (∀ i, 0 ≤ σ i) ∧ 0 < optimalSquaredTail k σ}

set_option maxHeartbeats 800000 in
theorem measurable_rawResidual {m : ℕ} {X : Type*} [MeasurableSpace X]
    {A : X → Matrix (Fin m) (Fin n) ℝ} {Ω : X → Matrix (Fin n) (Fin l) ℝ}
    (hA : Measurable A) (hΩ : Measurable Ω) :
    Measurable (fun x => squaredResidual (A x) (Ω x)) := by
  let f (R : Matrix (Fin l) (Fin n) ℚ) : Matrix (Fin l) (Fin n) ℝ := R.map Rat.cast
  let obj (x : X) (R : Matrix (Fin l) (Fin n) ℝ) :=
    squaredFrobenius (A x - (A x * Ω x) * R)
  have hDense : DenseRange f :=
    DenseRange.piMap (f := fun _ : Fin l => Pi.map (fun _ : Fin n => Rat.cast))
      (fun _ => DenseRange.piMap (fun _ => Rat.denseRange_cast))
  have hFrob : Continuous (squaredFrobenius : Matrix (Fin m) (Fin n) ℝ → ℝ) := by
    change Continuous (fun Q : Matrix (Fin m) (Fin n) ℝ => squaredFrobenius Q)
    simp only [Cosine.squaredFrobenius_eq_sum_entries]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_id.matrix_elem i j).pow 2
  have hEq (x : X) : squaredResidual (A x) (Ω x) = ⨅ R, obj x (f R) := by
    let t := ⨅ R, obj x (f R)
    have hb : BddBelow (Set.range fun R => obj x (f R)) :=
      ⟨0, by rintro _ ⟨R, rfl⟩; exact squaredFrobenius_nonneg _⟩
    refine le_antisymm (le_ciInf fun R => squaredResidual_le_sampled_approximation _ _ _) ?_
    have hc : Continuous (obj x) := by
      change Continuous (fun R : Matrix (Fin l) (Fin n) ℝ =>
        squaredFrobenius (A x - (A x * Ω x) * R))
      exact hFrob.comp (continuous_const.sub (continuous_const.matrix_mul continuous_id))
    have hLE : ∀ R, t ≤ obj x R := by
      intro R
      refine hDense.induction_on (p := fun R => t ≤ obj x R) R (isClosed_le continuous_const hc) ?_
      exact fun T => ciInf_le hb T
    let Y := A x * Ω x
    have hG : (Yᵀ * Y).IsHermitian := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_self Y
    let R := symmetricPseudoInverse (Yᵀ * Y) hG * Yᵀ * A x
    have hOpt : Y * R = rangeProjector Y * A x := by
      rw [rangeProjector_eq_gram_pseudoInverse]
      simp only [R, Matrix.mul_assoc]
    have hVal : obj x R = squaredResidual (A x) (Ω x) := by
      change squaredFrobenius (A x - Y * R) = squaredFrobenius ((1 - rangeProjector Y) * A x)
      rw [hOpt, Matrix.sub_mul, Matrix.one_mul]
    exact (hLE R).trans_eq hVal
  simp_rw [hEq]
  have : Countable (Matrix (Fin l) (Fin n) ℚ) :=
    inferInstanceAs (Countable (Fin l → Fin n → ℚ))
  apply Measurable.iInf
  intro R
  apply hFrob.measurable.comp
  have hMul : Measurable (fun x => (A x * Ω x) * f R) :=
    measurable_matrix_product (measurable_matrix_product hA hΩ) measurable_const
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact (((continuous_id.matrix_elem i j).measurable.comp hA).sub
    ((continuous_id.matrix_elem i j).measurable.comp hMul))

private def frameProjector (U : Matrix (Fin n) (Fin l) ℝ) (hU : Uᵀ * U = 1) :
    OrthogonalProjector n l :=
  ⟨U * Uᵀ, by simp, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul],
    by rw [Matrix.rank_self_mul_transpose, ← Matrix.rank_transpose_mul_self, hU,
      Matrix.rank_one, Fintype.card_fin]⟩

def haarFrameProjector (hl : l ≤ n) (U : Matrix (Fin n) (Fin l) ℝ) :
    OrthogonalProjector n l :=
  if hU : Uᵀ * U = 1 then frameProjector U hU
  else frameProjector (exists_stiefel_frame hl).choose (exists_stiefel_frame hl).choose_spec

theorem haarFrameProjector_val (hl : l ≤ n) {U : Matrix (Fin n) (Fin l) ℝ}
    (hU : Uᵀ * U = 1) : (haarFrameProjector hl U).val = U * Uᵀ := by
  rw [haarFrameProjector, dif_pos hU]
  rfl

theorem measurable_haarFrameProjector (hl : l ≤ n) :
    Measurable (haarFrameProjector hl) := by
  apply Measurable.subtype_mk
  change Measurable (fun U : Matrix (Fin n) (Fin l) ℝ =>
    (haarFrameProjector hl U).val)
  have hs : MeasurableSet {U : Matrix (Fin n) (Fin l) ℝ | Uᵀ * U = 1} :=
    (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const).measurableSet
  let P₀ := frameProjector (exists_stiefel_frame hl).choose (exists_stiefel_frame hl).choose_spec
  have he : (fun U => (haarFrameProjector hl U).val) =
      {U : Matrix (Fin n) (Fin l) ℝ | Uᵀ * U = 1}.piecewise
        (fun U => U * Uᵀ) (fun _ => P₀.val) := by
    funext U
    by_cases hU : Uᵀ * U = 1
    · simp [Set.piecewise, hU, haarFrameProjector_val]
    · simp [Set.piecewise, hU, haarFrameProjector, P₀]
  rw [he]
  exact (continuous_id.matrix_mul continuous_id.matrix_transpose).measurable.piecewise hs
    measurable_const

/-- The Haar sketch law on rank-l projectors, obtained from the Haar
orthonormal frame by taking its range projection. -/
def haarSketchProjectorLaw (hl : l ≤ n) : Measure (OrthogonalProjector n l) :=
  (gaussianHaarFrameLaw hl).map (haarFrameProjector hl)

instance (hl : l ≤ n) : IsProbabilityMeasure (haarSketchProjectorLaw hl) :=
  Measure.isProbabilityMeasure_map (measurable_haarFrameProjector hl).aemeasurable

/-- The normalized full-range residual h_Σ from (2.2). -/
def subspaceLoss (k : ℕ) (σ : Fin n → ℝ) (P : OrthogonalProjector n l) : ℝ :=
  squaredResidual (diagonal σ) P.val / optimalSquaredTail k σ

/-- The orientation law is represented by U = Qᵀ. The sample columns U P
span the rotated sketch space when U is orthogonal. -/
def conditionalMean (k : ℕ) (σ : Fin n → ℝ)
    (μ : Measure (OrthogonalProjector n l)) (U : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∫ P, squaredResidual (diagonal σ) (U * P.val) / optimalSquaredTail k σ ∂μ

/-- The Gaussian reference for the same spectrum and width. -/
def gaussianMean (k l : ℕ) (σ : Fin n → ℝ) : ℝ :=
  ∫ G, squaredResidual (diagonal σ) G / optimalSquaredTail k σ ∂gaussianMatrixLaw n l

/-- Largest mean directional energy of one sketch draw. -/
def meanProjectorNorm (μ : Measure (OrthogonalProjector n l)) : ℝ :=
  ‖(meanSketchProjector μ).toEuclideanLin.toContinuousLinearMap‖

/-- Supremum over fixed spectra, taken outside the average over orientations. -/
def meanDiscrepancy (k : ℕ) (μ : Measure (OrthogonalProjector n l)) : ℝ :=
  sSup (Set.range fun σ : Spectra n k =>
    ∫ U, |conditionalMean k σ.val μ U - gaussianMean k l σ.val|
      ∂gaussianRightOrthogonalLaw n)

theorem measurable_subspaceLoss (k : ℕ) (σ : Fin n → ℝ) :
    Measurable (subspaceLoss (l := l) k σ) :=
  (measurable_rawResidual measurable_const measurable_subtype_coe).div_const _

theorem residual_div_tail_le (k : ℕ) (σ : Fin n → ℝ) (htail : 0 < optimalSquaredTail k σ)
    {d : ℕ} (Y : Matrix (Fin n) (Fin d) ℝ) :
    squaredResidual (diagonal σ) Y / optimalSquaredTail k σ ≤
      squaredFrobenius (diagonal σ) / optimalSquaredTail k σ := by
  apply div_le_div_of_nonneg_right _ htail.le
  simpa only [Matrix.mul_zero, sub_zero] using
    squaredResidual_le_sampled_approximation (diagonal σ) Y (0 : Matrix (Fin d) (Fin n) ℝ)

theorem residual_div_tail_nonneg (k : ℕ) (σ : Fin n → ℝ)
    (htail : 0 < optimalSquaredTail k σ) {d : ℕ} (Y : Matrix (Fin n) (Fin d) ℝ) :
    0 ≤ squaredResidual (diagonal σ) Y / optimalSquaredTail k σ :=
  div_nonneg (squaredFrobenius_nonneg _) htail.le


/-- Right multiplication by independently invertible column coordinates leaves
the actual range residual unchanged. -/
theorem squaredResidual_mul_right_of_det_isUnit {d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (Y : Matrix (Fin n) (Fin d) ℝ)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : IsUnit R.det) :
    squaredResidual A (Y * R) = squaredResidual A Y := by
  have hSurj : Function.Surjective R.toEuclideanLin := by
    intro x
    refine ⟨R⁻¹.toEuclideanLin x, ?_⟩
    exact congrArg (fun T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) => T x)
      (show R.toEuclideanLin.comp R⁻¹.toEuclideanLin = LinearMap.id by
        rw [← euclidean_mul, Matrix.mul_nonsing_inv _ hR]
        ext y : 1
        simp)
  rw [squaredResidual, squaredResidual, ← Matrix.mul_assoc A Y R,
    rangeProjector_eq_of_range_eq (A * Y * R) (A * Y) (by
      rw [euclidean_mul, LinearMap.range_comp, LinearMap.range_eq_top.mpr hSurj, Submodule.map_top])]

/-- Expression in the original coordinates, with the same target spectrum. -/
theorem residual_rotate_input (k : ℕ) (σ : Fin n → ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1)
    (P : OrthogonalProjector n l) :
    squaredResidual (diagonal σ * U) P.val / optimalSquaredTail k σ =
      squaredResidual (diagonal σ) (U * P.val) / optimalSquaredTail k σ := by
  unfold squaredResidual
  rw [Matrix.mul_assoc (diagonal σ) U P.val, ← Matrix.mul_assoc,
    squaredFrobenius_mul_orthogonal_right _ _ (mul_eq_one_comm.mp hU)]

/-- Replacing the columns of a frame by its range projector preserves the
residual even when the spectrum has zero entries. -/
theorem gaussianMean_eq_haarProjector (hl : l ≤ n) (k : ℕ) (σ : Fin n → ℝ) :
    gaussianMean k l σ = ∫ P, subspaceLoss k σ P ∂haarSketchProjectorLaw hl := by
  rw [haarSketchProjectorLaw, integral_map (measurable_haarFrameProjector hl).aemeasurable
    (measurable_subspaceLoss k σ).aestronglyMeasurable, ← gaussianPolarFrameLaw_eq_haar hl]
  change _ = ∫ V, (subspaceLoss k σ ∘ haarFrameProjector hl) V
    ∂(gaussianMatrixLaw n l).map gaussianPolarFrame
  rw [integral_map measurable_gaussianPolarFrame.aemeasurable
      ((measurable_subspaceLoss k σ).comp (measurable_haarFrameProjector hl)).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_gaussianMatrix_injective hl] with G hG
  have hU := gaussianPolarFrame_transpose_mul_self G hG
  change squaredResidual (diagonal σ) G / optimalSquaredTail k σ =
    subspaceLoss k σ (haarFrameProjector hl (gaussianPolarFrame G))
  rw [subspaceLoss, haarFrameProjector_val hl hU,
    squaredResidual_frame_projector _ _ hU]
  apply congrArg (fun x => x / optimalSquaredTail k σ)
  calc
    squaredResidual (diagonal σ) G =
        squaredResidual (diagonal σ) (gaussianPolarFrame G * gaussianPolarRadial G) := by
      rw [gaussianPolarFrame_mul_radial G hG]
    _ = _ := squaredResidual_mul_right_of_det_isUnit _ _ _ (gaussianPolarRadial_det_isUnit G hG)

theorem gaussianLossLaw_eq_haarProjector (hl : l ≤ n) (k : ℕ) (σ : Fin n → ℝ) :
    (gaussianMatrixLaw n l).map
      (fun G => squaredResidual (diagonal σ) G / optimalSquaredTail k σ) =
    (haarSketchProjectorLaw hl).map (subspaceLoss k σ) := by
  rw [haarSketchProjectorLaw,
    Measure.map_map (measurable_subspaceLoss k σ) (measurable_haarFrameProjector hl),
    ← gaussianPolarFrameLaw_eq_haar hl, Measure.map_map
      ((measurable_subspaceLoss k σ).comp (measurable_haarFrameProjector hl))
      measurable_gaussianPolarFrame]
  apply Measure.map_congr
  filter_upwards [ae_gaussianMatrix_injective hl] with G hG
  have hU := gaussianPolarFrame_transpose_mul_self G hG
  change squaredResidual (diagonal σ) G / optimalSquaredTail k σ =
    subspaceLoss k σ (haarFrameProjector hl (gaussianPolarFrame G))
  rw [subspaceLoss, haarFrameProjector_val hl hU,
    squaredResidual_frame_projector _ _ hU]
  apply congrArg (fun x => x / optimalSquaredTail k σ)
  calc
    squaredResidual (diagonal σ) G =
        squaredResidual (diagonal σ) (gaussianPolarFrame G * gaussianPolarRadial G) := by
      rw [gaussianPolarFrame_mul_radial G hG]
    _ = _ := squaredResidual_mul_right_of_det_isUnit _ _ _ (gaussianPolarRadial_det_isUnit G hG)

theorem measurable_rotatedLoss (k : ℕ) (σ : Fin n → ℝ) :
    Measurable (fun z : Matrix (Fin n) (Fin n) ℝ × OrthogonalProjector n l =>
      squaredResidual (diagonal σ) (z.1 * z.2.val) / optimalSquaredTail k σ) :=
  (measurable_rawResidual measurable_const
    (measurable_matrix_product measurable_fst (measurable_subtype_coe.comp measurable_snd))).div_const _

theorem measurable_conditionalMean (k : ℕ) (σ : Fin n → ℝ)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    Measurable (conditionalMean k σ μ) :=
  (measurable_rotatedLoss k σ).stronglyMeasurable.integral_prod_right.measurable

set_option maxHeartbeats 1200000 in
/-- For a fixed E, rotation gives the same residual law as a fresh Gaussian span. -/
theorem rotatedLoss_identDistrib_gaussian (hl : l ≤ n) (k : ℕ) (σ : Fin n → ℝ)
    (P : OrthogonalProjector n l) :
    ProbabilityTheory.IdentDistrib
      (fun U => squaredResidual (diagonal σ) (U * P.val) / optimalSquaredTail k σ)
      (fun G => squaredResidual (diagonal σ) G / optimalSquaredTail k σ)
      (gaussianRightOrthogonalLaw n) (gaussianMatrixLaw n l) := by
  obtain ⟨B, hB, hP⟩ := exists_frame_of_projector P.val P.property.1 P.property.2.1 P.property.2.2
  let A := diagonal σ
  let L := fun V : Matrix (Fin n) (Fin l) ℝ =>
    squaredResidual A V / optimalSquaredTail k σ
  have hL : Measurable L := (measurable_rawResidual measurable_const measurable_id).div_const _
  have hBMap : Measurable (fun U : Matrix (Fin n) (Fin n) ℝ => U * B) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hRange (U : Matrix (Fin n) (Fin n) ℝ) :
      squaredResidual A (U * P.val) = squaredResidual A (U * B) := by
    have hSurj : Function.Surjective Bᵀ.toEuclideanLin := by
      intro x
      refine ⟨B.toEuclideanLin x, ?_⟩
      exact congrArg
        (fun T : EuclideanSpace ℝ (Fin l) →ₗ[ℝ] EuclideanSpace ℝ (Fin l) => T x)
        (show Bᵀ.toEuclideanLin.comp B.toEuclideanLin = LinearMap.id by
          rw [← euclidean_mul, hB]
          ext y : 1
          simp)
    have he : A * (U * P.val) = (A * (U * B)) * Bᵀ := by
      rw [← hP]
      simp only [Matrix.mul_assoc]
    rw [squaredResidual, squaredResidual, he,
      rangeProjector_eq_of_range_eq ((A * (U * B)) * Bᵀ) (A * (U * B)) (by
        rw [euclidean_mul, LinearMap.range_comp, LinearMap.range_eq_top.mpr hSurj,
          Submodule.map_top])]
  let η := gaussianRightOrthogonalLaw n
  have hMul : Measurable (fun U : Matrix (Fin n) (Fin n) ℝ => U * P.val) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hLeft : Measurable (fun U => squaredResidual A (U * P.val) / optimalSquaredTail k σ) :=
    (measurable_rawResidual measurable_const hMul).div_const _
  change ProbabilityTheory.IdentDistrib
    (fun U => squaredResidual A (U * P.val) / optimalSquaredTail k σ) L η (gaussianMatrixLaw n l)
  refine ⟨hLeft.aemeasurable, hL.aemeasurable, ?_⟩
  calc
    _ = η.map (L ∘ fun U => U * B) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun U =>
        congrArg (fun x => x / optimalSquaredTail k σ) (hRange U)
    _ = (gaussianHaarFrameLaw hl).map L := by
      rw [← Measure.map_map hL hBMap, gaussianHaarFrameLaw_eq_orbit hl B hB]
    _ = _ := by
      rw [← gaussianPolarFrameLaw_eq_haar hl,
        Measure.map_map hL measurable_gaussianPolarFrame]
      apply Measure.map_congr
      filter_upwards [ae_gaussianMatrix_injective hl] with G hG
      change squaredResidual A (gaussianPolarFrame G) / optimalSquaredTail k σ = _
      apply congrArg (fun x => x / optimalSquaredTail k σ)
      calc
        squaredResidual A (gaussianPolarFrame G) =
            squaredResidual A (gaussianPolarFrame G * gaussianPolarRadial G) :=
          (squaredResidual_mul_right_of_det_isUnit _ _ _ (gaussianPolarRadial_det_isUnit G hG)).symm
        _ = squaredResidual A G := by rw [gaussianPolarFrame_mul_radial G hG]

theorem integral_rotatedLoss_fixed_eq (hl : l ≤ n) (k : ℕ) (σ : Fin n → ℝ)
    (P : OrthogonalProjector n l) :
    (∫ U, squaredResidual (diagonal σ) (U * P.val) / optimalSquaredTail k σ
      ∂gaussianRightOrthogonalLaw n) = gaussianMean k l σ :=
  (rotatedLoss_identDistrib_gaussian hl k σ P).integral_eq

/-- Centering at the Gaussian comparison for every fixed spectrum, equation (2.3). -/
theorem conditionalMean_integral_eq_gaussianMean (hl : l ≤ n) (k : ℕ) (σ : Fin n → ℝ)
    (htail : 0 < optimalSquaredTail k σ)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    (∫ U, conditionalMean k σ μ U ∂gaussianRightOrthogonalLaw n) = gaussianMean k l σ := by
  let L := fun z : Matrix (Fin n) (Fin n) ℝ × OrthogonalProjector n l =>
    squaredResidual (diagonal σ) (z.1 * z.2.val) / optimalSquaredTail k σ
  have hL : Integrable L ((gaussianRightOrthogonalLaw n).prod μ) := by
    apply Integrable.of_bound (measurable_rotatedLoss k σ).aestronglyMeasurable
      (squaredFrobenius (diagonal σ) / optimalSquaredTail k σ)
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_of_nonneg (residual_div_tail_nonneg k σ htail _)]
    exact residual_div_tail_le k σ htail _
  unfold conditionalMean
  rw [integral_integral_swap hL]
  simp_rw [integral_rotatedLoss_fixed_eq hl k σ]
  simp

end

end TypicalOrientations
