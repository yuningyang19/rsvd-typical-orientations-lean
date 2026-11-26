import SketchOrientation.SpectralContinuity
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-! Singular values and the inverse trace for the row Gram matrix. -/

namespace SketchOrientation

open Matrix Unitary

variable {k ℓ : ℕ}

private theorem orderedEigenvaluesFin_eq_linearMap {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.IsHermitian) (j : Fin k) :
    orderedEigenvaluesFin hA j =
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin j := by
  unfold orderedEigenvaluesFin Matrix.IsHermitian.eigenvalues₀
  let T := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have heq {d d' : ℕ} (h : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = d)
      (h' : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = d') (e : d' = d) (j' : Fin d') :
      T.eigenvalues h (Fin.cast e j') = T.eigenvalues h' j' := by
    subst d
    subst d'
    rfl
  exact heq _ _ _ _

private theorem toLpLin_transpose_eq_adjoint {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) :
    Bᵀ.toLpLin 2 2 = (B.toLpLin 2 2).adjoint := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, EuclideanSpace.basisFun_toBasis,
      ← Matrix.toLpLin_eq_toLin] using
    Matrix.toLin_conjTranspose (EuclideanSpace.basisFun (Fin n) ℝ)
      (EuclideanSpace.basisFun (Fin m) ℝ) B

/-- Squaring the `j`th singular value of the map `Bᵀ : ℝ^k → ℝ^ℓ` gives the `j`th ordered
row Gram eigenvalue. The `k` entries include zero singular values in deficient rank. -/
theorem sq_singularValues_transpose_eq_gramEigenvalues (B : Matrix (Fin k) (Fin ℓ) ℝ)
    (j : Fin k) : (Bᵀ.toLpLin 2 2).singularValues j ^ 2 = gramEigenvalues B j := by
  have hmap : (B * Bᵀ).toLpLin 2 2 = (Bᵀ.toLpLin 2 2).adjoint ∘ₗ Bᵀ.toLpLin 2 2 := by
    rw [Matrix.toLpLin_mul_same, ← toLpLin_transpose_eq_adjoint, Matrix.transpose_transpose]
  let T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ) := Bᵀ.toLpLin 2 2
  change T.singularValues j ^ 2 = _
  rw [T.sq_singularValues_fin finrank_euclideanSpace_fin j, gramEigenvalues,
    orderedEigenvaluesFin_eq_linearMap]
  have haux {U V : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
      (hU : U.IsSymmetric) (hV : V.IsSymmetric) (h : U = V) :
      hU.eigenvalues finrank_euclideanSpace_fin j =
        hV.eigenvalues finrank_euclideanSpace_fin j := by
    subst V
    rfl
  exact haux T.isSymmetric_adjoint_comp_self _ hmap.symm

/-- The paper's smallest singular value for `0 < k ≤ ℓ`, using the last of the `k` singular
values of `Bᵀ`. This definition is also available for a block with fewer columns. -/
noncomputable def minSingularValue (B : Matrix (Fin k) (Fin ℓ) ℝ) (_hk : 0 < k) : ℝ :=
  (Bᵀ.toLpLin 2 2).singularValues (k - 1)

theorem minSingularValue_nonneg (B : Matrix (Fin k) (Fin ℓ) ℝ) (hk : 0 < k) :
    0 ≤ minSingularValue B hk :=
  (Bᵀ.toLpLin 2 2).singularValues_nonneg _

theorem sq_minSingularValue_eq_gramMinEigenvalue (B : Matrix (Fin k) (Fin ℓ) ℝ) (hk : 0 < k) :
    minSingularValue B hk ^ 2 = gramMinEigenvalue B hk :=
  sq_singularValues_transpose_eq_gramEigenvalues B ⟨k - 1, by omega⟩

theorem continuous_minSingularValue (hk : 0 < k) :
    Continuous (fun B : Matrix (Fin k) (Fin ℓ) ℝ ↦ minSingularValue B hk) := by
  convert (Real.continuous_sqrt.comp (continuous_gramMinEigenvalue (ℓ := ℓ) hk)) using 1
  ext B
  rw [Function.comp_apply, ← sq_minSingularValue_eq_gramMinEigenvalue, Real.sqrt_sq
    (minSingularValue_nonneg B hk)]

/-- Every unit vector has image norm at least the least singular value of the transposed block. -/
theorem minSingularValue_le_norm_transpose (B : Matrix (Fin k) (Fin ℓ) ℝ) (hk : 0 < k)
    (x : EuclideanSpace ℝ (Fin k)) (hx : ‖x‖ = 1) :
    minSingularValue B hk ≤ ‖Bᵀ.toLpLin 2 2 x‖ := by
  let T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ) := Bᵀ.toLpLin 2 2
  let U := T.adjoint ∘ₗ T
  let hU := T.isSymmetric_adjoint_comp_self
  let v := hU.eigenvectorBasis finrank_euclideanSpace_fin
  have hcoords (j : Fin k) : v.repr (U x) j = T.singularValues j ^ 2 * v.repr x j := by
    rw [T.sq_singularValues_fin finrank_euclideanSpace_fin j]
    exact hU.eigenvectorBasis_apply_self_apply finrank_euclideanSpace_fin x j
  have hnorm : ‖T x‖ ^ 2 = ∑ j : Fin k, T.singularValues j ^ 2 * (v.repr x j) ^ 2 := by
    calc
      ‖T x‖ ^ 2 = inner ℝ x (U x) := by
        rw [← real_inner_self_eq_norm_sq, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
      _ = inner ℝ (v.repr x) (v.repr (U x)) := (v.repr.inner_map_map x (U x)).symm
      _ = ∑ j : Fin k, T.singularValues j ^ 2 * (v.repr x j) ^ 2 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Pi.star_apply, star_trivial]
        change v.repr (U x) j * v.repr x j = _
        rw [hcoords]
        ring
  have hx' : ∑ j : Fin k, (v.repr x j) ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, v.repr.norm_map, hx, one_pow]
  have hj (j : Fin k) : minSingularValue B hk ^ 2 ≤ T.singularValues j ^ 2 := by
    rw [sq_minSingularValue_eq_gramMinEigenvalue,
      sq_singularValues_transpose_eq_gramEigenvalues B j]
    exact gramMinEigenvalue_le B hk j
  change minSingularValue B hk ≤ ‖T x‖
  apply (sq_le_sq₀ (minSingularValue_nonneg B hk) (norm_nonneg _)).mp
  calc
    minSingularValue B hk ^ 2 =
        ∑ j : Fin k, minSingularValue B hk ^ 2 * (v.repr x j) ^ 2 := by
      rw [← Finset.mul_sum, hx', mul_one]
    _ ≤ ∑ j : Fin k, T.singularValues j ^ 2 * (v.repr x j) ^ 2 :=
      Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (hj j) (sq_nonneg _)
    _ = ‖T x‖ ^ 2 := hnorm.symm

/-- The least singular value is attained by some unit vector, including when it is zero. -/
theorem exists_unit_norm_transpose_eq_minSingularValue (B : Matrix (Fin k) (Fin ℓ) ℝ)
    (hk : 0 < k) : ∃ x : EuclideanSpace ℝ (Fin k),
      ‖x‖ = 1 ∧ ‖Bᵀ.toLpLin 2 2 x‖ = minSingularValue B hk := by
  let T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ) := Bᵀ.toLpLin 2 2
  let i : Fin k := ⟨k - 1, by omega⟩
  let hT := T.isSymmetric_adjoint_comp_self
  let v := hT.eigenvectorBasis finrank_euclideanSpace_fin
  have hunit : ‖v i‖ = 1 := v.orthonormal.1 i
  refine ⟨v i, hunit, ?_⟩
  change ‖T (v i)‖ = _
  have heig : (T.adjoint ∘ₗ T) (v i) = minSingularValue B hk ^ 2 • v i := by
    change (T.adjoint ∘ₗ T) (v i) = T.singularValues i ^ 2 • v i
    rw [T.sq_singularValues_fin finrank_euclideanSpace_fin i]
    exact hT.apply_eigenvectorBasis finrank_euclideanSpace_fin i
  have hs : ‖T (v i)‖ ^ 2 = minSingularValue B hk ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← T.adjoint_inner_right, ← LinearMap.comp_apply, heig,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hunit]
    simp
  exact (sq_eq_sq₀ (norm_nonneg _) (minSingularValue_nonneg B hk)).mp hs

private theorem trace_inverse_affine_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (a b : ℝ)
    (hb : ∀ j, b + a * hA.eigenvalues j ≠ 0) :
    ((b • 1 + a • A)⁻¹).trace = ∑ j, (b + a * hA.eigenvalues j)⁻¹ := by
  let U := hA.eigenvectorUnitary
  let C := conjStarAlgAut ℝ _ U
  let d : ι → ℝ := fun j ↦ b + a * hA.eigenvalues j
  have hA₀ : A = C (diagonal hA.eigenvalues) := by
    exact hA.spectral_theorem
  have hdiag : b • 1 + a • diagonal hA.eigenvalues = diagonal d := by
    ext i j
    by_cases h : i = j <;> simp [h, d, smul_eq_mul]
  have hA' : b • 1 + a • A = C (diagonal d) := by
    rw [← hdiag, map_add, map_smul, map_smul, map_one, ← hA₀]
  have hdiagInv : diagonal d * diagonal (fun j ↦ (d j)⁻¹) = (1 : Matrix ι ι ℝ) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext j
    exact mul_inv_cancel₀ (hb j)
  rw [hA', Matrix.inv_eq_right_inv (B := C (diagonal fun j ↦ (d j)⁻¹)) (by
    rw [← map_mul, hdiagInv, map_one])]
  change (conjStarAlgAut ℝ _ U (diagonal fun j ↦ (d j)⁻¹)).trace = _
  rw [conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul, trace_diagonal]

/-- Affine transforms of a symmetric matrix can be inverted term by term in its spectrum when
all transformed eigenvalues are nonzero. -/
theorem trace_inverse_affine_orderedEigenvaluesFin {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.IsHermitian) (a b : ℝ) (hb : ∀ j, b + a * orderedEigenvaluesFin hA j ≠ 0) :
    ((b • 1 + a • A)⁻¹).trace = ∑ j, (b + a * orderedEigenvaluesFin hA j)⁻¹ := by
  let e : Fin k ≃ Fin k := (finCongr (Fintype.card_fin k).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin k))))
  have he (j : Fin k) : hA.eigenvalues (e j) = orderedEigenvaluesFin hA j := by
    simp [e, Matrix.IsHermitian.eigenvalues, orderedEigenvaluesFin]
  have hb' (j : Fin k) : b + a * hA.eigenvalues j ≠ 0 := by
    have hj := hb (e.symm j)
    rwa [← he, e.apply_symm_apply] at hj
  rw [trace_inverse_affine_eq_sum hA a b hb', ← Equiv.sum_comp e]
  simp_rw [he]

/-- The trace of the inverse of a shifted Gram matrix is the sum of the shifted reciprocals.
At `b = 0` the hypothesis is exactly positivity of the full row Gram spectrum. -/
theorem trace_inverse_shifted_rowGram (B : Matrix (Fin k) (Fin ℓ) ℝ) (b : ℝ)
    (hb : ∀ j, gramEigenvalues B j + b ≠ 0) :
    ((B * Bᵀ + b • 1)⁻¹).trace = ∑ j, (gramEigenvalues B j + b)⁻¹ := by
  have hb' : ∀ j, b + (1 : ℝ) * orderedEigenvaluesFin (rowGram_isHermitian B) j ≠ 0 := by
    simpa only [one_mul, gramEigenvalues, add_comm] using hb
  simpa only [one_smul, one_mul, gramEigenvalues, add_comm] using
    trace_inverse_affine_orderedEigenvaluesFin (rowGram_isHermitian B) 1 b hb'

/-- The inverse trace of a Gram matrix whose ordered eigenvalues are all positive. -/
theorem trace_inverse_rowGram_eq_sum (B : Matrix (Fin k) (Fin ℓ) ℝ)
    (hB : ∀ j, 0 < gramEigenvalues B j) :
    ((B * Bᵀ)⁻¹).trace = ∑ j, (gramEigenvalues B j)⁻¹ := by
  simpa only [zero_smul, add_zero] using
    trace_inverse_shifted_rowGram B 0 (fun j ↦ by simpa using (hB j).ne')

/-- The inverse trace of `I + a A` for positive semidefinite `A` and `a ≥ 0`. -/
theorem trace_inverse_one_add_smul_of_posSemidef {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosSemidef) (a : ℝ) (ha : 0 ≤ a) :
    ((1 + a • A)⁻¹).trace = ∑ j, (1 + a * orderedEigenvaluesFin hA.isHermitian j)⁻¹ := by
  have hb : ∀ j, 1 + a * orderedEigenvaluesFin hA.isHermitian j ≠ 0 := by
    intro j
    exact (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg ha (orderedEigenvaluesFin_nonneg hA j))).ne'
  simpa only [one_smul] using trace_inverse_affine_orderedEigenvaluesFin hA.isHermitian a 1 hb

end SketchOrientation
