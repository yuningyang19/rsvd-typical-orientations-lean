import SketchOrientation.GramResidual

namespace SketchOrientation

open Matrix

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq l]

theorem rangeProjector_eq_of_range_eq (Y : Matrix m n ℝ) (Z : Matrix m l ℝ)
    (h : Y.toEuclideanLin.range = Z.toEuclideanLin.range) :
    rangeProjector Y = rangeProjector Z := by
  apply Matrix.toEuclideanLin.injective
  rw [euclidean_projector, euclidean_projector]
  exact congrArg (fun S : Submodule ℝ (EuclideanSpace ℝ m) =>
    S.starProjection.toLinearMap) h

/-- A symmetric idempotent matrix is the orthogonal projector onto its range. -/
theorem rangeProjector_of_projector (P : Matrix n n ℝ)
    (hs : Pᵀ = P) (hi : P * P = P) :
    rangeProjector P = P := by
  let p := P.toEuclideanLin
  have hIdem : IsIdempotentElem p := by
    change p.comp p = p
    rw [← euclidean_mul, hi]
  have hSymm : p.IsSymmetric := by
    have hAdj : p.adjoint = p := by
      rw [← euclidean_transpose, hs]
    intro x y
    rw [← LinearMap.adjoint_inner_left, hAdj]
  apply Matrix.toEuclideanLin.injective
  rw [euclidean_projector]
  exact (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
    ⟨hIdem, hSymm⟩).choose_spec.symm

/-- When the columns are orthonormal, the projector is their outer product. -/
theorem rangeProjector_of_frame (U : Matrix n l ℝ) (hU : Uᵀ * U = 1) :
    rangeProjector U = U * Uᵀ := by
  rw [rangeProjector_eq_gram_pseudoInverse,
    symmetricPseudoInverse_eq_inv_of_isUnit _ _ (by rw [hU, det_one]; exact isUnit_one),
    hU, inv_one, Matrix.mul_one]

set_option maxHeartbeats 800000 in
/-- Choose an orthonormal basis of the range of an actual rank-ℓ
orthogonal projector. -/
theorem exists_frame_of_projector {n l : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hs : Pᵀ = P) (hi : P * P = P) (hrank : P.rank = l) :
    ∃ U : Matrix (Fin n) (Fin l) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = P := by
  classical
  let S := P.toEuclideanLin.range
  have hdim : Module.finrank ℝ S = l := (rank_eq_finrank_euclidean P).symm.trans hrank
  let b : OrthonormalBasis (Fin l) ℝ S := (stdOrthonormalBasis ℝ S).reindex (finCongr hdim)
  let f : EuclideanSpace ℝ (Fin l) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    S.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let U := Matrix.toEuclideanLin.symm f.toLinearMap
  have hU : U.toEuclideanLin = f.toLinearMap := LinearEquiv.apply_symm_apply _ _
  have hGram : Uᵀ * U = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [euclidean_mul, euclidean_transpose, hU, f.adjoint_comp_self']
    ext x : 1
    simp
  have hRange : U.toEuclideanLin.range = S := by
    rw [hU]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (b.repr.symm y).property
    · intro hx
      refine ⟨b.repr ⟨x, hx⟩, ?_⟩
      change (b.repr.symm (b.repr ⟨x, hx⟩)).val = x
      rw [LinearIsometryEquiv.symm_apply_apply]
  exact ⟨U, hGram, (rangeProjector_of_frame U hGram).symm.trans
    ((rangeProjector_eq_of_range_eq U P hRange).trans (rangeProjector_of_projector P hs hi))⟩

/-- Sketching with U and with UUᵀ produces the same actual sampled range. -/
theorem squaredResidual_frame_projector (A : Matrix m n ℝ) (U : Matrix n l ℝ)
    (hU : Uᵀ * U = 1) :
    squaredResidual A (U * Uᵀ) = squaredResidual A U := by
  have hSurj : Function.Surjective Uᵀ.toEuclideanLin := by
    intro x
    refine ⟨U.toEuclideanLin x, ?_⟩
    have h := LinearMap.congr_fun
      (show Uᵀ.toEuclideanLin.comp U.toEuclideanLin = LinearMap.id by
        rw [← euclidean_mul, hU]
        ext y : 1
        simp) x
    exact h
  have hRange :
      (A * (U * Uᵀ)).toEuclideanLin.range = (A * U).toEuclideanLin.range := by
    rw [← Matrix.mul_assoc, euclidean_mul, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hSurj, Submodule.map_top]
  rw [squaredResidual, squaredResidual, rangeProjector_eq_of_range_eq _ _ hRange]

end SketchOrientation
