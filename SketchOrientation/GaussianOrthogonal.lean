import SketchOrientation.GaussianGramLaw

namespace SketchOrientation

open Matrix MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {n k : ℕ}

private theorem toEuclideanLin_adjoint_mul (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) :
    Q.toEuclideanLin.adjoint ∘ₗ Q.toEuclideanLin = LinearMap.id := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  change toLpLin 2 2 Qᵀ ∘ₗ toLpLin 2 2 Q = _
  rw [← Matrix.toLpLin_mul_same, hQ, Matrix.toLpLin_one]

noncomputable def orthogonalMatrixIsometry (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := by
  let L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { Q.toEuclideanLin with
      norm_map' := fun x => by
        have h := LinearMap.congr_fun (toEuclideanLin_adjoint_mul Q hQ) x
        change Q.toEuclideanLin.adjoint (Q.toEuclideanLin x) = x at h
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
          ← LinearMap.adjoint_inner_right, h] }
  exact LinearIsometryEquiv.ofSurjective L (LinearMap.injective_iff_surjective.mp L.injective)

theorem orthogonalMatrixIsometry_apply (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) (u : EuclideanSpace ℝ (Fin n)) :
    orthogonalMatrixIsometry Q hQ u = Q.toEuclideanLin u := by
  simp [orthogonalMatrixIsometry]

/-- Left orthogonal multiplication preserves the iid standard Gaussian matrix law. -/
theorem gaussianMatrixLaw_map_left_orthogonal (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) :
    (gaussianMatrixLaw n k).map (fun G => Q * G) = gaussianMatrixLaw n k := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := orthogonalMatrixIsometry Q hQ
  let F := fun (X : Fin k → E) j => e (X j)
  have he : MeasurePreserving e (stdGaussian E) (stdGaussian E) :=
    ⟨e.continuous.measurable, stdGaussian_map e⟩
  have hF : MeasurePreserving F (gaussianColumnLaw n k) (gaussianColumnLaw n k) :=
    measurePreserving_pi _ _ (fun _ => he)
  have hM : Measurable (fun G : Matrix (Fin n) (Fin k) ℝ => Q * G) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hh : (fun G : Matrix (Fin n) (Fin k) ℝ => Q * G) ∘ matrixOfGaussianColumns =
      matrixOfGaussianColumns ∘ F := by
    funext X
    ext i j
    change (Q * matrixOfGaussianColumns X) i j = (e (X j)) i
    rw [orthogonalMatrixIsometry_apply]
    change (Q * matrixOfGaussianColumns X) i j = (toLpLin 2 2 Q (X j)) i
    rw [Matrix.toLpLin_apply]
    rfl
  unfold gaussianMatrixLaw
  rw [Measure.map_map hM measurable_matrixOfGaussianColumns, hh,
    ← Measure.map_map measurable_matrixOfGaussianColumns hF.measurable, hF.map_eq]


theorem orthonormal_frame_columns {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    Orthonormal ℝ (fun j => WithLp.toLp 2 (V.col j) : Fin k → EuclideanSpace ℝ (Fin n)) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M i j) hV
  simpa [Matrix.mul_apply, Matrix.one_apply, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.col_apply, mul_comm] using h

/-- Complete an orthonormal frame by filling in an orthonormal complement. -/
theorem exists_orthogonal_extension (hkn : k ≤ n) (V : Matrix (Fin n) (Fin k) ℝ)
    (hV : Vᵀ * V = 1) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 ∧
      U.submatrix id (Fin.castLE hkn) = V := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e := Fin.castLEEmb hkn
  let a : Fin k ≃ Set.range e := Equiv.ofInjective e e.injective
  let v : Fin k → E := fun j => WithLp.toLp 2 (V.col j)
  let f : Fin n → E := fun i =>
    if hi : i ∈ Set.range e then v (a.symm ⟨i, hi⟩) else 0
  have hf : Orthonormal ℝ ((Set.range e).domRestrict f) := by
    have hEq : (Set.range e).domRestrict f = v ∘ a.symm := by
      funext i
      change (if hi : (i : Fin n) ∈ Set.range e then v (a.symm ⟨i, hi⟩) else 0) = v (a.symm i)
      rw [dif_pos i.property]
    rw [hEq]
    exact (orthonormal_frame_columns hV).comp _ a.symm.injective
  obtain ⟨b, hb⟩ := hf.exists_orthonormalBasis_extension_of_card_eq
    (by simp [E])
  let U : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => b j i
  refine ⟨U, ?_, ?_⟩
  · ext i j
    have h : inner ℝ (b i : EuclideanSpace ℝ (Fin n)) (b j : EuclideanSpace ℝ (Fin n)) =
        if i = j then 1 else 0 := orthonormal_iff_ite.mp b.orthonormal i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [Matrix.one_apply]
    change (∑ a, (b i : EuclideanSpace ℝ (Fin n)) a * (b j : EuclideanSpace ℝ (Fin n)) a) = _
    simpa only [dotProduct, star_trivial, mul_comm] using h
  · ext i j
    change b (e j) i = V i j
    have hj : e j ∈ Set.range e := ⟨j, rfl⟩
    have h := hb (e j) hj
    have ha : (⟨e j, hj⟩ : Set.range e) = a j := rfl
    rw [h]
    simp [f, ha, v, Matrix.col_apply]

/-- The orthogonal left action is transitive on frames of the same width. -/
theorem exists_orthogonal_mul_frame_eq (hkn : k ≤ n)
    {U V : Matrix (Fin n) (Fin k) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ, Qᵀ * Q = 1 ∧ Q * U = V := by
  classical
  obtain ⟨R, hR, hRU⟩ := exists_orthogonal_extension hkn U hU
  obtain ⟨T, hT, hTV⟩ := exists_orthogonal_extension hkn V hV
  refine ⟨T * Rᵀ, ?_, ?_⟩
  · rw [transpose_mul, transpose_transpose, Matrix.mul_assoc R, ← Matrix.mul_assoc Tᵀ T,
      hT, Matrix.one_mul]
    exact mul_eq_one_comm.mp hR
  · have hh : T * Rᵀ * R = T := by rw [Matrix.mul_assoc, hR, Matrix.mul_one]
    rw [← hRU, ← hTV]
    calc
      _ = (T * Rᵀ * R).submatrix id (Fin.castLE hkn) := by
        ext i j
        simp [Matrix.mul_apply, Matrix.submatrix_apply]
      _ = _ := by rw [hh]

end SketchOrientation
