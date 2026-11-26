import TypicalOrientations.RotationProduct
import SketchOrientation.DctSketchLaw

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation
open scoped ProbabilityTheory

noncomputable section

variable {n l : ℕ}

private theorem orthogonal_product (U V : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) : (U * V)ᵀ * (U * V) = 1 := by
  rw [transpose_mul, Matrix.mul_assoc Vᵀ, ← Matrix.mul_assoc Uᵀ U,
    hU, Matrix.one_mul, hV]

private theorem reflection_orthogonal (n : ℕ) :
    (diagonalReflection n)ᵀ * diagonalReflection n = 1 := by
  rw [diagonalReflection_transpose, diagonalReflection_sq]

private theorem orthogonalLaw_map_left (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : Rᵀ * R = 1) :
    (gaussianRightOrthogonalLaw n).map (fun U => R * U) = gaussianRightOrthogonalLaw n := by
  have h := gaussianHaarFrameLaw_eq_orbit (le_refl n)
    (1 : Matrix (Fin n) (Fin n) ℝ) (by simp)
  have he : gaussianRightOrthogonalLaw n = gaussianHaarFrameLaw (le_refl n) := by
    simpa only [Matrix.mul_one, Measure.map_id'] using h
  rw [he, gaussianHaarFrameLaw_map_left (le_refl n) R hR]

/-- Every subspace in positive dimension has an orientation-reversing
orthogonal transformation that fixes it as an unoriented subspace. -/
theorem exists_orthogonalReflection_fix_projector (hn : 0 < n) (hl : l ≤ n)
    (P : OrthogonalProjector n l) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, Rᵀ * R = 1 ∧ R.det = -1 ∧
      R * P.val * Rᵀ = P.val := by
  classical
  obtain ⟨B, hB, hP⟩ :=
    exists_frame_of_projector P.val P.property.1 P.property.2.1 P.property.2.2
  let e := Fin.castLEEmb hl
  let C : Matrix (Fin n) (Fin l) ℝ := (rowSelector e)ᵀ
  have hC : Cᵀ * C = 1 := by
    simpa only [C, transpose_transpose] using rowSelector_orthonormal e
  obtain ⟨Q, hQ, hQB⟩ := exists_orthogonal_mul_frame_eq hl hC hB
  let J := diagonalReflection n
  let D := C * Cᵀ
  have hOff (i j : Fin n) (hij : i ≠ j) : D i j = 0 := by
    change (∑ a, (if e a = i then (1 : ℝ) else 0) * (if e a = j then 1 else 0)) = 0
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : e a = i <;> simp [ha, hij]
  have hComm : J * D = D * J := by
    ext i j
    simp only [J, diagonalReflection, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst j
      exact mul_comm _ _
    · rw [hOff i j hij, mul_zero, zero_mul]
  have hFix : J * D * Jᵀ = D := by
    rw [hComm, Matrix.mul_assoc D, show J * Jᵀ = 1 by
      rw [show Jᵀ = J from diagonalReflection_transpose n, diagonalReflection_sq], Matrix.mul_one]
  have hPD : P.val = Q * D * Qᵀ := by
    rw [← hP, ← hQB, transpose_mul]
    simp only [D, Matrix.mul_assoc]
  let R := Q * J * Qᵀ
  have hR : Rᵀ * R = 1 := orthogonal_product _ _
    (orthogonal_product _ _ hQ (reflection_orthogonal n))
    (by rw [transpose_transpose]; exact mul_eq_one_comm.mp hQ)
  have hDet : R.det = -1 := by
    have hd : Q.det * Q.det = 1 := by
      simpa only [det_mul, det_transpose, det_one] using congrArg Matrix.det hQ
    simp only [R, J, det_mul, det_transpose, diagonalReflection_det hn]
    linarith [show Q.det * -1 * Q.det = -(Q.det * Q.det) by ring]
  refine ⟨R, hR, hDet, ?_⟩
  calc
    R * P.val * Rᵀ =
        Q * (J * (Qᵀ * Q) * D * (Qᵀ * Q) * Jᵀ) * Qᵀ := by
      rw [hPD]
      simp only [R, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    _ = P.val := by rw [hQ, Matrix.mul_one, Matrix.mul_one, hFix, ← hPD]

private theorem piecewise_map_eq_self {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {A : Set X} [DecidablePred (· ∈ A)] (hA : MeasurableSet A)
    (f : X → X) (hf : Measurable f) (hLaw : μ.map f = μ)
    (hA' : f ⁻¹' Aᶜ = Aᶜ) :
    μ.map (A.piecewise id f) = μ := by
  classical
  let F := A.piecewise id f
  have hF : Measurable F := measurable_id.piecewise hA hf
  have hPlus : F =ᵐ[μ.restrict A] id := by
    filter_upwards [ae_restrict_mem hA] with x hx
    exact Set.piecewise_eq_of_mem A id f hx
  have hMinus : F =ᵐ[μ.restrict Aᶜ] f := by
    filter_upwards [ae_restrict_mem hA.compl] with x hx
    exact Set.piecewise_eq_of_notMem A id f hx
  have hSecond : (μ.restrict Aᶜ).map f = μ.restrict Aᶜ := by
    calc
      _ = (μ.restrict (f ⁻¹' Aᶜ)).map f := by rw [hA']
      _ = (μ.map f).restrict Aᶜ := (Measure.restrict_map hf hA.compl).symm
      _ = _ := by rw [hLaw]
  calc
    μ.map F = (μ.restrict A + μ.restrict Aᶜ).map F := by
      rw [Measure.restrict_add_restrict_compl hA]
    _ = (μ.restrict A).map F + (μ.restrict Aᶜ).map F := Measure.map_add _ _ hF
    _ = μ := by
      rw [Measure.map_congr hPlus, Measure.map_id, Measure.map_congr hMinus,
        hSecond, Measure.restrict_add_restrict_compl hA]

/-- On each fixed subspace, the folded special-orthogonal action has the
same pushforward as the orthogonal action. -/
theorem rotateProjector_specialOrientation_map_eq_orthogonal
    (hn : 0 < n) (hl : l ≤ n) (P : OrthogonalProjector n l) :
    (specialOrientationLaw n).map (fun U => rotateProjector U P) =
      (gaussianRightOrthogonalLaw n).map (fun U => rotateProjector U P) := by
  classical
  let μ := gaussianRightOrthogonalLaw n
  let A : Set (Matrix (Fin n) (Fin n) ℝ) := {U | U.det = 1}
  let J := diagonalReflection n
  obtain ⟨R, hR, hDetR, hRP⟩ := exists_orthogonalReflection_fix_projector hn hl P
  let K := fun U : Matrix (Fin n) (Fin n) ℝ => J * U * R
  let L := A.piecewise id K
  let F := fun U => rotateProjector U P
  have hF : Measurable F :=
    measurable_rotateProjector.comp (measurable_id.prodMk measurable_const)
  have hA : MeasurableSet A :=
    continuous_id.matrix_det.measurable (measurableSet_singleton 1)
  have hK : Measurable K :=
    (continuous_const.matrix_mul continuous_id |>.matrix_mul continuous_const).measurable
  have hL : Measurable L := measurable_id.piecewise hA hK
  have hLawK : μ.map K = μ := by
    let f := fun U : Matrix (Fin n) (Fin n) ℝ => J * U
    let g := fun U : Matrix (Fin n) (Fin n) ℝ => U * R
    have hf : Measurable f := (continuous_const.matrix_mul continuous_id).measurable
    have hg : Measurable g := (continuous_id.matrix_mul continuous_const).measurable
    change μ.map (g ∘ f) = μ
    rw [← Measure.map_map hg hf, orthogonalLaw_map_left J (reflection_orthogonal n),
      gaussianRightOrthogonalLaw_map_right R hR]
  have hdet (U : Matrix (Fin n) (Fin n) ℝ) : (K U).det = U.det := by
    simp only [K, J, det_mul, diagonalReflection_det hn, hDetR]
    ring
  have hLawL : μ.map L = μ :=
    piecewise_map_eq_self μ hA K hK hLawK (by ext U; show _ ↔ _; simp [A, hdet])
  change (μ.map foldOrientation).map F = μ.map F
  rw [Measure.map_map hF measurable_foldOrientation]
  calc
    μ.map (F ∘ foldOrientation) = μ.map (F ∘ L) := by
      apply Measure.map_congr
      filter_upwards [ae_gaussianRightOrthogonal n] with U hU
      by_cases hUdet : U.det = 1
      · simp [foldOrientation, L, A, hUdet]
      · have hJU := orthogonal_product J U (reflection_orthogonal n) hU
        have hKorth := orthogonal_product (J * U) R hJU hR
        change F (foldOrientation U) = F (L U)
        rw [show foldOrientation U = J * U by simp [foldOrientation, J, hUdet],
          show L U = K U from Set.piecewise_eq_of_notMem A id K hUdet]
        apply Subtype.ext
        rw [rotateProjector_val _ hJU, rotateProjector_val _ hKorth]
        rw [show (J * U * R) * P.val * (J * U * R)ᵀ =
            (J * U) * (R * P.val * Rᵀ) * (J * U)ᵀ by
          simp only [transpose_mul, Matrix.mul_assoc], hRP]
    _ = _ := by rw [← Measure.map_map hF hL, hLawL]

/-- The orthogonal orbit of any fixed rank-l projector is precisely the
Gaussian-induced uniform Grassmannian law. -/
theorem rotateProjector_orthogonal_identDistrib (hl : l ≤ n)
    (P : OrthogonalProjector n l) :
    IdentDistrib (fun U => rotateProjector U P) id
      (gaussianRightOrthogonalLaw n) (haarSketchProjectorLaw hl) := by
  obtain ⟨B, hB, hP⟩ :=
    exists_frame_of_projector P.val P.property.1 P.property.2.1 P.property.2.2
  have hf : Measurable (fun U : Matrix (Fin n) (Fin n) ℝ => rotateProjector U P) :=
    measurable_rotateProjector.comp (measurable_id.prodMk measurable_const)
  have hm : Measurable (fun U : Matrix (Fin n) (Fin n) ℝ => U * B) :=
    (continuous_id.matrix_mul continuous_const).measurable
  refine ⟨hf.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id, haarSketchProjectorLaw, ← gaussianHaarFrameLaw_eq_orbit hl B hB,
    Measure.map_map (measurable_haarFrameProjector hl) hm]
  apply Measure.map_congr
  filter_upwards [ae_gaussianRightOrthogonal n] with U hU
  have hUB : (U * B)ᵀ * (U * B) = 1 := by
    rw [transpose_mul, Matrix.mul_assoc Bᵀ, ← Matrix.mul_assoc Uᵀ U,
      hU, Matrix.one_mul, hB]
  apply Subtype.ext
  rw [Function.comp_apply, rotateProjector_val U hU P, haarFrameProjector_val hl hUB,
    ← hP, transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Every fixed subspace rotated by the same Haar SO(n) orientation has
the uniform Grassmannian marginal used in Lemma 3.1. -/
theorem rotateProjector_specialOrientation_identDistrib (hn : 0 < n) (hl : l ≤ n)
    (P : OrthogonalProjector n l) :
    IdentDistrib (fun U => rotateProjector U P) id
      (specialOrientationLaw n) (haarSketchProjectorLaw hl) := by
  have hm : Measurable (fun U : Matrix (Fin n) (Fin n) ℝ => rotateProjector U P) :=
    measurable_rotateProjector.comp (measurable_id.prodMk measurable_const)
  refine ⟨hm.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [rotateProjector_specialOrientation_map_eq_orthogonal hn hl P]
  exact (rotateProjector_orthogonal_identDistrib hl P).map_eq

end

end TypicalOrientations
