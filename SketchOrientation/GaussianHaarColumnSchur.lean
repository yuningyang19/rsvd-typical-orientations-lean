import SketchOrientation.GaussianHaarColumn
import SketchOrientation.AtomTheorem

namespace SketchOrientation

open Matrix
open scoped InnerProductSpace

variable {n k ℓ : ℕ}

/-- Within the sketch space retain only the directions orthogonal to the
other sampled frame columns. -/
noncomputable def schurSketchProjector (P : OrthogonalProjector n ℓ) (W : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  P.val - rangeProjector (P.val * W)

theorem sketch_mul_sample_projector (P : OrthogonalProjector n ℓ) (W : Matrix (Fin n) (Fin k) ℝ) :
    P.val * rangeProjector (P.val * W) = rangeProjector (P.val * W) := by
  have hLe : (P.val * W).toEuclideanLin.range ≤ P.val.toEuclideanLin.range := by
    rintro _ ⟨z, rfl⟩
    exact ⟨W.toEuclideanLin z, (LinearMap.congr_fun (euclidean_mul P.val W) z).symm⟩
  have hP := congrArg Matrix.toEuclideanLin (rangeProjector_of_projector P.val P.property.1 P.property.2.1)
  rw [euclidean_projector] at hP
  apply Matrix.toEuclideanLin.injective
  rw [euclidean_mul, euclidean_projector, ← hP]
  ext x : 1
  change P.val.toEuclideanLin.range.starProjection ((P.val * W).toEuclideanLin.range.starProjection x) =
    (P.val * W).toEuclideanLin.range.starProjection x
  exact Submodule.starProjection_eq_self_iff.mpr
    (hLe ((P.val * W).toEuclideanLin.range.orthogonalProjectionOnto x).property)

theorem sample_projector_mul_sketch (P : OrthogonalProjector n ℓ) (W : Matrix (Fin n) (Fin k) ℝ) :
    rangeProjector (P.val * W) * P.val = rangeProjector (P.val * W) := by
  have h := congrArg Matrix.transpose (sketch_mul_sample_projector P W)
  rwa [transpose_mul, rangeProjector_transpose, P.property.1] at h

theorem schurSketchProjector_transpose (P : OrthogonalProjector n ℓ) (W : Matrix (Fin n) (Fin k) ℝ) :
    (schurSketchProjector P W)ᵀ = schurSketchProjector P W := by
  rw [schurSketchProjector, transpose_sub, P.property.1, rangeProjector_transpose]

theorem schurSketchProjector_sq (P : OrthogonalProjector n ℓ) (W : Matrix (Fin n) (Fin k) ℝ) :
    schurSketchProjector P W * schurSketchProjector P W = schurSketchProjector P W := by
  rw [schurSketchProjector, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    P.property.2.1, sketch_mul_sample_projector, sample_projector_mul_sketch,
    rangeProjector_mul_self, sub_self, sub_zero]

theorem transpose_mul_schurSketchProjector (P : OrthogonalProjector n ℓ)
    (W : Matrix (Fin n) (Fin k) ℝ) :
    Wᵀ * schurSketchProjector P W = 0 := by
  have h := congrArg Matrix.transpose (rangeProjector_mul_sample (P.val * W))
  rw [transpose_mul, rangeProjector_transpose, transpose_mul, P.property.1, Matrix.mul_assoc,
    sketch_mul_sample_projector] at h
  rw [schurSketchProjector, Matrix.mul_sub, h, sub_self]

/-- The Schur projector is contained in the perpendicular space of the
other target columns. -/
theorem schurSketchProjector_range_le_orthogonal
    (P : OrthogonalProjector n ℓ) (W : Matrix (Fin n) (Fin k) ℝ) :
    (schurSketchProjector P W).toEuclideanLin.range ≤ W.toEuclideanLin.rangeᗮ := by
  rintro _ ⟨u, rfl⟩ v ⟨x, rfl⟩
  rw [← LinearMap.adjoint_inner_right (A := W.toEuclideanLin), ← euclidean_transpose, ← LinearMap.comp_apply,
    ← euclidean_mul, transpose_mul_schurSketchProjector, map_zero, LinearMap.zero_apply,
    inner_zero_right]

theorem schurSketchProjector_rank (P : OrthogonalProjector n ℓ) (W : Matrix (Fin n) (Fin k) ℝ)
    (hW : Function.Injective (P.val * W).mulVec) :
    (schurSketchProjector P W).rank = ℓ - k := by
  have hTrace (A : Matrix (Fin n) (Fin n) ℝ) (hs : Aᵀ = A) (hi : A * A = A) :
      (A.rank : ℝ) = A.trace := by
    rw [← trace_rangeProjector, rangeProjector_of_projector A hs hi]
  have hW' : Function.Injective (P.val * W).toEuclideanLin := by
    intro x y h
    have h' := congrArg WithLp.ofLp h
    exact WithLp.ofLp_injective 2 (hW h')
  have hA : (P.val * W).rank = k := by
    rw [rank_eq_finrank_euclidean, LinearMap.finrank_range_of_inj hW', finrank_euclideanSpace,
      Fintype.card_fin]
  have h := hTrace (schurSketchProjector P W) (schurSketchProjector_transpose P W)
    (schurSketchProjector_sq P W)
  rw [schurSketchProjector, Matrix.trace_sub, trace_rangeProjector, hA,
    ← hTrace P.val P.property.1 P.property.2.1, P.property.2.2] at h
  have hkℓ : k ≤ ℓ := by
    have hr : 0 ≤ ((schurSketchProjector P W).rank : ℝ) := Nat.cast_nonneg _
    exact_mod_cast (sub_nonneg.mp (h ▸ hr))
  exact_mod_cast (h.trans (Nat.cast_sub hkℓ).symm)

theorem orthonormalFrame_toEuclideanLin_injective (W : Matrix (Fin n) (Fin k) ℝ)
    (hW : Wᵀ * W = 1) : Function.Injective W.toEuclideanLin := by
  have hL : Function.LeftInverse (Wᵀ.toEuclideanLin) W.toEuclideanLin := by
    have h := euclidean_mul Wᵀ W
    rw [hW] at h
    intro x
    have hx := LinearMap.congr_fun h x
    change toLpLin 2 2 1 x = _ at hx
    rw [Matrix.toLpLin_one] at hx
    exact hx.symm
  exact hL.injective

theorem finrank_orthonormalFrame_complement (W : Matrix (Fin n) (Fin k) ℝ)
    (hW : Wᵀ * W = 1) : Module.finrank ℝ W.toEuclideanLin.rangeᗮ = n - k := by
  have h := W.toEuclideanLin.range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj (orthonormalFrame_toEuclideanLin_injective W hW),
    finrank_euclideanSpace, Fintype.card_fin, finrank_euclideanSpace, Fintype.card_fin] at h
  omega

theorem schurSketchProjector_eq_projection (P : OrthogonalProjector n ℓ)
    (W : Matrix (Fin n) (Fin k) ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    (schurSketchProjector P W).toEuclideanLin z =
      (schurSketchProjector P W).toEuclideanLin.range.starProjection z := by
  have h := congrArg Matrix.toEuclideanLin
    (rangeProjector_of_projector _ (schurSketchProjector_transpose P W)
      (schurSketchProjector_sq P W))
  rw [euclidean_projector] at h
  exact LinearMap.congr_fun h.symm z

theorem schurSketchProjector_range_le_sketch (P : OrthogonalProjector n ℓ)
    (W : Matrix (Fin n) (Fin k) ℝ) :
    (schurSketchProjector P W).toEuclideanLin.range ≤ P.val.toEuclideanLin.range := by
  have h : P.val * schurSketchProjector P W = schurSketchProjector P W := by
    rw [schurSketchProjector, Matrix.mul_sub, P.property.2.1, sketch_mul_sample_projector]
  rintro _ ⟨x, rfl⟩
  refine ⟨(schurSketchProjector P W).toEuclideanLin x, ?_⟩
  rw [← LinearMap.comp_apply, ← euclidean_mul, h]

theorem dropGramColumn_mul_insertFrameColumn (P : OrthogonalProjector n ℓ)
    (j : Fin (k + 1)) (W : Matrix (Fin n) (Fin k) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    dropGramColumn (P.val * insertFrameColumn j W v) j = P.val * W := by
  ext i l
  simp only [dropGramColumn, Matrix.submatrix_apply, id_eq, Matrix.mul_apply,
    insertFrameColumn_succAbove]

/-- The Schur reciprocal for the appended direction in the manuscript's
conditioning proof. -/
theorem schurSketchProjector_inv_diag (P : OrthogonalProjector n ℓ)
    (j : Fin (k + 1)) (W : Matrix (Fin n) (Fin k) ℝ) (v : EuclideanSpace ℝ (Fin n))
    (hV : Function.Injective (P.val * insertFrameColumn j W v).mulVec) :
    let V := insertFrameColumn j W v
    (Vᵀ * P.val * V)⁻¹ j j = (‖(schurSketchProjector P W).toEuclideanLin v‖ ^ 2)⁻¹ := by
  intro V
  let A := P.val * V
  have hGram : gaussianGram A = Vᵀ * P.val * V := by
    unfold gaussianGram A
    rw [transpose_mul, P.property.1]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P.val P.val, P.property.2.1]
  have hcol : WithLp.toLp 2 (A.col j) = P.val.toEuclideanLin v := by
    ext i
    change A i j = ∑ a, P.val i a * v a
    simp [A, V, Matrix.mul_apply]
  rw [← hGram, gaussianGram_inv_diag A hV, dropGramColumn_mul_insertFrameColumn,
    hcol, columnResidualSq, schurSketchProjector, map_sub, LinearMap.sub_apply,
    euclidean_projector]
  congr 3
  apply congrArg (fun z => P.val.toEuclideanLin v - z)
  have hp (z : EuclideanSpace ℝ (Fin n)) :
      (rangeProjector (P.val * W)).toEuclideanLin z =
        (P.val * W).toEuclideanLin.range.starProjection z :=
    LinearMap.congr_fun (euclidean_projector _) z
  rw [← hp (P.val.toEuclideanLin v), ← LinearMap.comp_apply, ← euclidean_mul,
    sample_projector_mul_sketch]
  exact hp v

end SketchOrientation
