import TypicalOrientations.RotationModel

namespace TypicalOrientations

open Matrix MeasureTheory SketchOrientation Set Filter

noncomputable section

variable {n l : ℕ}

private theorem rank_conjugation (U P : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
    (U * P * Uᵀ).rank = P.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have h : Uᵀ * (U * P * Uᵀ) * U = P := by
      calc
        _ = ((Uᵀ * U) * P) * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
        _ = _ := by simp [hU]
    calc
      P.rank = (Uᵀ * (U * P * Uᵀ) * U).rank := congrArg Matrix.rank h.symm
      _ ≤ (Uᵀ * (U * P * Uᵀ)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (U * P * Uᵀ).rank := Matrix.rank_mul_le_right _ _

private def rotateProjectorOfOrthogonal (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) (P : OrthogonalProjector n l) : OrthogonalProjector n l :=
  ⟨U * P.val * Uᵀ, by simp [transpose_mul, P.property.1, Matrix.mul_assoc], by
    calc
      _ = U * (P.val * (Uᵀ * U) * P.val) * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, P.property.2.1, Matrix.mul_assoc],
    (rank_conjugation U P.val hU).trans P.property.2.2⟩

/-- Conjugation is the action on orthogonal projectors. The values at
nonorthogonal ambient matrices play no role under the rotation laws. -/
def rotateProjector (U : Matrix (Fin n) (Fin n) ℝ) (P : OrthogonalProjector n l) :
    OrthogonalProjector n l :=
  if hU : Uᵀ * U = 1 then rotateProjectorOfOrthogonal U hU P else P

theorem rotateProjector_val (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1)
    (P : OrthogonalProjector n l) :
    (rotateProjector U P).val = U * P.val * Uᵀ := by
  simp [rotateProjector, hU, rotateProjectorOfOrthogonal]

theorem measurable_rotateProjector :
    Measurable (fun z : Matrix (Fin n) (Fin n) ℝ × OrthogonalProjector n l =>
      rotateProjector z.1 z.2) := by
  classical
  apply Measurable.subtype_mk
  change Measurable (fun z : Matrix (Fin n) (Fin n) ℝ × OrthogonalProjector n l =>
    (rotateProjector z.1 z.2).val)
  have hU : MeasurableSet {U : Matrix (Fin n) (Fin n) ℝ | Uᵀ * U = 1} :=
    (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const).measurableSet
  have hForm : (fun z : Matrix (Fin n) (Fin n) ℝ × OrthogonalProjector n l =>
      (rotateProjector z.1 z.2).val) =
      ({z : Matrix (Fin n) (Fin n) ℝ × OrthogonalProjector n l |
        z.1ᵀ * z.1 = 1}).piecewise
        (fun z => z.1 * z.2.val * z.1ᵀ) (fun z => z.2.val) := by
    funext z
    by_cases hz : z.1ᵀ * z.1 = 1
    · simpa only [Set.piecewise, Set.mem_ofPred_eq, if_pos hz] using rotateProjector_val _ hz z.2
    · simp [Set.piecewise, hz, rotateProjector]
  rw [hForm]
  exact (measurable_matrix_product
    (measurable_matrix_product measurable_fst (measurable_subtype_coe.comp measurable_snd))
    (continuous_id.matrix_transpose.measurable.comp measurable_fst)).piecewise
    (measurable_fst hU) (measurable_subtype_coe.comp measurable_snd)

/-- The diagonal reflection used to identify the two orthogonal components. -/
def diagonalReflection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => if i.val = 0 then -1 else 1

theorem diagonalReflection_transpose (n : ℕ) :
    (diagonalReflection n)ᵀ = diagonalReflection n := by simp [diagonalReflection]

theorem diagonalReflection_sq (n : ℕ) :
    diagonalReflection n * diagonalReflection n = 1 := by
  rw [diagonalReflection, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  by_cases hi : i.val = 0 <;> simp [hi]

theorem diagonalReflection_det (hn : 0 < n) : (diagonalReflection n).det = -1 := by
  rw [diagonalReflection, det_diagonal, Finset.prod_eq_single (⟨0, hn⟩ : Fin n)]
  · simp
  · intro i _ hi
    have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [hi']
  · simp

/-- Fold the determinant-minus-one component by the same left reflection as
in the manuscript. -/
def foldOrientation (U : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if U.det = 1 then U else diagonalReflection n * U

theorem measurable_foldOrientation : Measurable (@foldOrientation n) := by
  change Measurable ({U | U.det = 1}.piecewise id fun U => diagonalReflection n * U)
  exact measurable_id.piecewise
    (continuous_id.matrix_det.measurable (measurableSet_singleton 1))
    (continuous_const.matrix_mul continuous_id).measurable

private theorem det_orthogonal (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
    U.det = 1 ∨ U.det = -1 := by
  have h := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact (mul_eq_zero.mp (show (U.det - 1) * (U.det + 1) = 0 by nlinarith)).imp
    (fun h => by linarith) (fun h => by linarith)

/-- An ambient-matrix realization of Haar SO(n). It is the pushforward of
the orthogonal law by folding the determinant-minus-one component. -/
def specialOrientationLaw (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  (gaussianRightOrthogonalLaw n).map foldOrientation

instance : IsProbabilityMeasure (specialOrientationLaw n) :=
  Measure.isProbabilityMeasure_map measurable_foldOrientation.aemeasurable

theorem ae_specialOrientation (hn : 0 < n) :
    ∀ᵐ U ∂specialOrientationLaw n, Uᵀ * U = 1 ∧ U.det = 1 := by
  have hs : MeasurableSet {U : Matrix (Fin n) (Fin n) ℝ | Uᵀ * U = 1 ∧ U.det = 1} :=
    (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const).measurableSet.inter
      (isClosed_eq continuous_id.matrix_det continuous_const).measurableSet
  apply (ae_map_iff measurable_foldOrientation.aemeasurable hs).2
  filter_upwards [ae_gaussianRightOrthogonal n] with U hU
  rcases det_orthogonal U hU with h | h
  · simp [foldOrientation, h, hU]
  · rw [show foldOrientation U = diagonalReflection n * U by simp [foldOrientation, h, show (-1 : ℝ) ≠ 1 by norm_num]]
    constructor
    · rw [transpose_mul, diagonalReflection_transpose, Matrix.mul_assoc Uᵀ,
        ← Matrix.mul_assoc (diagonalReflection n), diagonalReflection_sq, Matrix.one_mul, hU]
    · rw [Matrix.det_mul, diagonalReflection_det hn, h]
      norm_num

theorem specialOrientationLaw_map_right (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : Rᵀ * R = 1) (hd : R.det = 1) :
    (specialOrientationLaw n).map (fun U => U * R) = specialOrientationLaw n := by
  have hm : Measurable (fun U : Matrix (Fin n) (Fin n) ℝ => U * R) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have he : (fun U : Matrix (Fin n) (Fin n) ℝ => U * R) ∘ foldOrientation =
      foldOrientation ∘ fun U => U * R := by
    funext U
    simp only [Function.comp_apply, foldOrientation, Matrix.det_mul, hd, mul_one]
    split <;> simp [Matrix.mul_assoc]
  unfold specialOrientationLaw
  rw [Measure.map_map hm measurable_foldOrientation, he,
    ← Measure.map_map measurable_foldOrientation hm, gaussianRightOrthogonalLaw_map_right R hR]

/-- The fixed-rank rotation-group Brascamp–Lieb inequality in (2.6).
Its proof is `rotationBrascampLieb` in `BCLMTheorem`. -/
def RotationBrascampLieb : Prop :=
  ∀ (n l m : ℕ), 0 < n → l ≤ n →
    ∀ (P : Fin m → OrthogonalProjector n l) (c : Fin m → ℝ)
      (H : Fin m → OrthogonalProjector n l → ℝ),
      (∀ i, 0 < c i) →
      (∀ x : EuclideanSpace ℝ (Fin n), ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2) →
      (∀ i, Measurable (H i)) →
      (∀ i S, 0 ≤ H i S) →
      (∀ i, ∃ B, ∀ S, H i S ≤ B) →
      (∫ U, ∏ i, (H i (rotateProjector U (P i))) ^ (c i / 2) ∂specialOrientationLaw n) ≤
        ∏ i, (∫ U, H i (rotateProjector U (P i)) ∂specialOrientationLaw n) ^ (c i / 2)

end

end TypicalOrientations
