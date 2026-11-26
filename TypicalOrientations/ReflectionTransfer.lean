import TypicalOrientations.RotationProduct

namespace TypicalOrientations

open Filter Matrix MeasureTheory ProbabilityTheory SketchOrientation
open scoped ProbabilityTheory

noncomputable section

variable {n k l : ℕ}

/-- Left reflection changes neither the squared residual nor its sampled
range formula, up to conjugation of the projector. -/
theorem squaredResidual_reflect_input (A : Matrix (Fin n) (Fin n) ℝ)
    (Y : Matrix (Fin n) (Fin l) ℝ) :
    squaredResidual (diagonalReflection n * A) Y = squaredResidual A Y := by
  let J := diagonalReflection n
  let R := rangeProjector (A * Y)
  have hJt : Jᵀ = J := diagonalReflection_transpose n
  have hJ : J * J = 1 := diagonalReflection_sq n
  have hSplit : (1 - J * R * J) * (J * A) = J * ((1 - R) * A) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]
    congr 1
    calc
      _ = J * R * (J * J) * A := by simp only [Matrix.mul_assoc]
      _ = J * (R * A) := by rw [hJ, Matrix.mul_one, Matrix.mul_assoc]
  unfold squaredResidual
  rw [Matrix.mul_assoc J A Y, rangeProjector_sign_mul _ _ hJt hJ]
  change squaredFrobenius ((1 - J * R * J) * (J * A)) = _
  rw [hSplit, squaredFrobenius_mul_orthogonal_left _ _ (hJt.symm ▸ hJ)]

theorem subspaceLoss_rotated_eq (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1)
    (P : OrthogonalProjector n l) (k : ℕ) (σ : Fin n → ℝ) :
    subspaceLoss k σ (rotateProjector U P) =
      squaredResidual (diagonal σ) (U * P.val) / optimalSquaredTail k σ := by
  rw [subspaceLoss, rotateProjector_val U hU]
  have hDet : IsUnit Uᵀ.det := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h)
  rw [squaredResidual_mul_right_of_det_isUnit _ _ _ hDet]

/-- The spectrum's diagonal commutation identifies the residual integrands
in both orthogonal components as in the proof after Lemma 3.1. -/
theorem folded_loss_eq (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1)
    (P : OrthogonalProjector n l) (k : ℕ) (σ : Fin n → ℝ) :
    subspaceLoss k σ (rotateProjector (foldOrientation U) P) =
      squaredResidual (diagonal σ) (U * P.val) / optimalSquaredTail k σ := by
  by_cases hd : U.det = 1
  · rw [foldOrientation, if_pos hd]
    exact subspaceLoss_rotated_eq U hU P k σ
  let J := diagonalReflection n
  have hJt : Jᵀ = J := diagonalReflection_transpose n
  have hJ : J * J = 1 := diagonalReflection_sq n
  have hJU : (J * U)ᵀ * (J * U) = 1 := by
    rw [transpose_mul, hJt, Matrix.mul_assoc Uᵀ, ← Matrix.mul_assoc J, hJ, Matrix.one_mul, hU]
  have hComm : diagonal σ * J = J * diagonal σ := by
    simp only [J, diagonalReflection, diagonal_mul_diagonal, mul_comm]
  rw [foldOrientation, if_neg hd, subspaceLoss_rotated_eq _ hJU,
    ← residual_rotate_input k σ _ hJU, ← residual_rotate_input k σ _ hU,
    ← Matrix.mul_assoc, hComm, Matrix.mul_assoc,
    squaredResidual_reflect_input]

theorem subspaceLoss_specialOrientation_identDistrib (hl : l ≤ n)
    (P : OrthogonalProjector n l) (k : ℕ) (σ : Fin n → ℝ) :
    IdentDistrib (fun U => subspaceLoss k σ (rotateProjector U P)) (subspaceLoss k σ)
      (specialOrientationLaw n) (haarSketchProjectorLaw hl) := by
  let f := fun U => subspaceLoss k σ (rotateProjector U P)
  have hf : Measurable f := (measurable_subspaceLoss k σ).comp
    (measurable_rotateProjector.comp (measurable_id.prodMk measurable_const))
  refine ⟨hf.aemeasurable, (measurable_subspaceLoss k σ).aemeasurable, ?_⟩
  change ((gaussianRightOrthogonalLaw n).map foldOrientation).map f = _
  rw [Measure.map_map hf measurable_foldOrientation, ← gaussianLossLaw_eq_haarProjector]
  refine Eq.trans (Measure.map_congr ?_) (rotatedLoss_identDistrib_gaussian hl k σ P).map_eq
  filter_upwards [ae_gaussianRightOrthogonal n] with U hU
  exact folded_loss_eq U hU P k σ

/-- The folded SO(n) average and the O(n) average have the same law for
any Borel function of the residual, including the clipping function. -/
theorem averaged_foldedLoss_identDistrib (k : ℕ) (σ : Fin n → ℝ)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ]
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    IdentDistrib
      (fun U => ∫ P, φ (squaredResidual (diagonal σ) (U * P.val) / optimalSquaredTail k σ) ∂μ)
      (fun U => ∫ P, φ (subspaceLoss k σ (rotateProjector U P)) ∂μ)
      (gaussianRightOrthogonalLaw n) (specialOrientationLaw n) := by
  let A := fun U => ∫ P, φ (squaredResidual (diagonal σ) (U * P.val) / optimalSquaredTail k σ) ∂μ
  let B := fun U => ∫ P, φ (subspaceLoss k σ (rotateProjector U P)) ∂μ
  have hX : Measurable (Function.uncurry
      (fun (U : Matrix (Fin n) (Fin n) ℝ) (P : OrthogonalProjector n l) =>
        φ (squaredResidual (diagonal σ) (U * P.val) / optimalSquaredTail k σ))) :=
    hφ.comp (measurable_rotatedLoss k σ)
  have hY : Measurable (Function.uncurry
      (fun (U : Matrix (Fin n) (Fin n) ℝ) (P : OrthogonalProjector n l) =>
        φ (subspaceLoss k σ (rotateProjector U P)))) :=
    hφ.comp ((measurable_subspaceLoss k σ).comp measurable_rotateProjector)
  have hA : Measurable A := hX.stronglyMeasurable.integral_prod_right.measurable
  have hB : Measurable B := hY.stronglyMeasurable.integral_prod_right.measurable
  refine ⟨hA.aemeasurable, hB.aemeasurable, ?_⟩
  change (gaussianRightOrthogonalLaw n).map A =
    ((gaussianRightOrthogonalLaw n).map foldOrientation).map B
  rw [Measure.map_map hB measurable_foldOrientation]
  apply Measure.map_congr
  filter_upwards [ae_gaussianRightOrthogonal n] with U hU
  exact integral_congr_ae (ae_of_all _ fun P => congrArg φ (folded_loss_eq U hU P k σ).symm)

end

end TypicalOrientations
