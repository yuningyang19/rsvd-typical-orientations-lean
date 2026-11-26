import SketchOrientation.Residual
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Trace

namespace SketchOrientation

open Matrix Unitary

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq l]

theorem euclidean_mul {i j k : Type*} [Fintype j] [Fintype k]
    [DecidableEq j] [DecidableEq k] (A : Matrix i j ℝ) (B : Matrix j k ℝ) :
    (A * B).toEuclideanLin = A.toEuclideanLin.comp B.toEuclideanLin := by
  ext x : 1
  change WithLp.toLp 2 ((A * B) *ᵥ WithLp.ofLp x) =
    WithLp.toLp 2 (A *ᵥ (B *ᵥ WithLp.ofLp x))
  rw [mulVec_mulVec]

theorem euclidean_transpose {i j : Type*} [Fintype i] [Fintype j]
    [DecidableEq i] [DecidableEq j] (Y : Matrix i j ℝ) :
    Yᵀ.toEuclideanLin = Y.toEuclideanLin.adjoint := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint Y

theorem euclidean_projector (Y : Matrix m l ℝ) :
    (rangeProjector Y).toEuclideanLin =
      (LinearMap.range Y.toEuclideanLin).starProjection.toLinearMap :=
  LinearEquiv.apply_symm_apply _ _

/-- Reciprocal on the nonzero eigenspaces of a real symmetric matrix, and
zero on its kernel. This is the Moore–Penrose inverse on symmetric matrices. -/
noncomputable def symmetricPseudoInverse (S : Matrix l l ℝ) (hS : S.IsHermitian) :
    Matrix l l ℝ := hS.cfc Inv.inv

theorem symmetricPseudoInverse_penrose (S : Matrix l l ℝ) (hS : S.IsHermitian) :
    S * symmetricPseudoInverse S hS * S = S := by
  let C := conjStarAlgAut ℝ (Matrix l l ℝ) hS.eigenvectorUnitary
  have hD : S = C (diagonal hS.eigenvalues) := by
    simpa [C] using hS.spectral_theorem
  have hInv : symmetricPseudoInverse S hS = C (diagonal fun i => (hS.eigenvalues i)⁻¹) := by
    simp [symmetricPseudoInverse, Matrix.IsHermitian.cfc, C, Function.comp_def]
  calc
    _ = C (diagonal hS.eigenvalues) * symmetricPseudoInverse S hS * S :=
      congrArg (fun A => A * symmetricPseudoInverse S hS * S) hD
    _ = C (diagonal hS.eigenvalues) * C (diagonal fun i => (hS.eigenvalues i)⁻¹) *
          C (diagonal hS.eigenvalues) :=
      congrArg₂ (fun B D => C (diagonal hS.eigenvalues) * B * D) hInv hD
    _ = C (diagonal hS.eigenvalues) := by
      rw [← map_mul, ← map_mul]
      apply congrArg C
      simp only [diagonal_mul_diagonal]
      congr
      funext i
      by_cases h : hS.eigenvalues i = 0
      · simp [h]
      · rw [mul_inv_cancel₀ h, one_mul]
    _ = S := hD.symm

/-- An inner inverse of the Gram matrix gives the sampled range projection. -/
theorem rangeProjector_of_inner_inverse (Y : Matrix m l ℝ) (Q : Matrix l l ℝ)
    (hQ : (Yᵀ * Y) * Q * (Yᵀ * Y) = Yᵀ * Y) :
    rangeProjector Y = Y * Q * Yᵀ := by
  let S := Yᵀ * Y
  apply Matrix.toEuclideanLin.injective
  rw [euclidean_projector, euclidean_mul (Y * Q) Yᵀ, euclidean_mul Y Q, euclidean_transpose]
  ext x : 1
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact LinearMap.mem_range_self _ _
  · rw [LinearMap.orthogonal_range]
    apply LinearMap.mem_ker.mpr
    let y := Y.toEuclideanLin
    let q := Q.toEuclideanLin
    let s := S.toEuclideanLin
    have hs : s = y.adjoint.comp y := by
      dsimp [s, S, y]
      rw [euclidean_mul, euclidean_transpose]
    have hr : s.range = y.adjoint.range := by
      rw [hs, LinearMap.range_adjoint_comp_self]
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp
      (hr.symm ▸ LinearMap.mem_range_self y.adjoint x)
    have hPen : (s.comp q).comp s = s := by
      dsimp [s, q]
      rw [← euclidean_mul, ← euclidean_mul, hQ]
    have hZ : s (q (s z)) = s z := LinearMap.congr_fun hPen z
    change y.adjoint (x - y (q (y.adjoint x))) = 0
    rw [LinearMap.map_sub, ← show s (q (y.adjoint x)) = y.adjoint (y (q (y.adjoint x))) from
      LinearMap.congr_fun hs _, ← hz, hZ, sub_self]

/-- Formula for the projection onto the sampled range, including singular
Gram matrices. -/
theorem rangeProjector_eq_gram_pseudoInverse (Y : Matrix m l ℝ) :
    rangeProjector Y =
      Y * symmetricPseudoInverse (Yᵀ * Y)
        (by simpa only [conjTranspose_eq_transpose_of_trivial] using
          isHermitian_conjTranspose_mul_self Y) * Yᵀ := by
  apply rangeProjector_of_inner_inverse
  exact symmetricPseudoInverse_penrose _ _

/-- The sampled projector is represented by a symmetric matrix. -/
theorem rangeProjector_transpose (Y : Matrix m l ℝ) :
    (rangeProjector Y)ᵀ = rangeProjector Y := by
  apply Matrix.toEuclideanLin.injective
  rw [euclidean_transpose, euclidean_projector]
  apply LinearMap.IsSymmetric.adjoint_eq
  exact (LinearMap.range Y.toEuclideanLin).starProjection_isSymmetric

/-- The sampled projector is idempotent. -/
theorem rangeProjector_mul_self (Y : Matrix m l ℝ) :
    rangeProjector Y * rangeProjector Y = rangeProjector Y := by
  apply Matrix.toEuclideanLin.injective
  rw [euclidean_mul, euclidean_projector]
  exact congrArg ContinuousLinearMap.toLinearMap
    (LinearMap.range Y.toEuclideanLin).isIdempotentElem_starProjection.eq

/-- Projecting the sampled columns onto their range fixes them. -/
theorem rangeProjector_mul_sample (Y : Matrix m l ℝ) :
    rangeProjector Y * Y = Y := by
  apply Matrix.toEuclideanLin.injective
  rw [euclidean_mul, euclidean_projector]
  ext x : 1
  exact Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self _ _)

omit [DecidableEq m] in
/-- Matrix rank in orthonormal Euclidean coordinates. -/
theorem rank_eq_finrank_euclidean (Y : Matrix m l ℝ) :
    Y.rank = Module.finrank ℝ (LinearMap.range Y.toEuclideanLin) := by
  let bₘ := PiLp.basisFun 2 ℝ m
  let bₗ := PiLp.basisFun 2 ℝ l
  have hY : Y.toEuclideanLin = Matrix.toLin bₗ bₘ Y :=
    DFunLike.congr_fun (Matrix.toLpLin_eq_toLin 2 2) Y
  have hr := congrArg LinearMap.range hY
  exact (Y.rank_eq_finrank_range_toLin bₘ bₗ).trans
    (congrArg (fun W : Submodule ℝ (EuclideanSpace ℝ m) => Module.finrank ℝ W) hr).symm

set_option maxHeartbeats 650000 in
/-- A sampled projector has trace equal to the dimension of the sampled range. -/
theorem trace_rangeProjector (Y : Matrix m l ℝ) :
    (rangeProjector Y).trace = (Y.rank : ℝ) := by
  let S := LinearMap.range Y.toEuclideanLin
  let p := S.starProjection.toLinearMap
  have hProj : LinearMap.IsProj S p := by
    exact ⟨fun x => (S.orthogonalProjectionOnto x).property,
      fun _ hx => Submodule.starProjection_eq_self_iff.mpr hx⟩
  have hMat : LinearMap.trace ℝ _ (rangeProjector Y).toEuclideanLin = (rangeProjector Y).trace := by
    change LinearMap.trace ℝ _ (Matrix.toLpLin 2 2 (rangeProjector Y)) = _
    rw [Matrix.toLpLin_eq_toLin, Matrix.trace_toLin_eq]
  rw [← hMat, euclidean_projector]
  change LinearMap.trace ℝ _ p = (Y.rank : ℝ)
  rw [hProj.trace, rank_eq_finrank_euclidean]

omit [DecidableEq n] in
/-- Orthogonal residual energy as total energy minus captured trace. -/
theorem squaredResidual_sub_trace (A : Matrix m n ℝ) (Ω : Matrix n l ℝ) :
    squaredResidual A Ω =
      squaredFrobenius A - (Aᵀ * rangeProjector (A * Ω) * A).trace := by
  let P := rangeProjector (A * Ω)
  have hs : Pᵀ = P := rangeProjector_transpose _
  have hi : P * P = P := rangeProjector_mul_self _
  have he : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hi, sub_self, sub_zero]
  unfold squaredResidual squaredFrobenius
  change (((1 - P) * A)ᵀ * ((1 - P) * A)).trace = _
  rw [transpose_mul, transpose_sub, transpose_one, hs,
    Matrix.mul_assoc Aᵀ, ← Matrix.mul_assoc (1 - P), he,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, trace_sub]
  simp only [Matrix.mul_assoc, P]

/-- The spectral pseudoinverse agrees with the ordinary inverse when the
Gram matrix is nonsingular. -/
theorem symmetricPseudoInverse_eq_inv_of_isUnit (S : Matrix l l ℝ)
    (hS : S.IsHermitian) (hDet : IsUnit S.det) :
    symmetricPseudoInverse S hS = S⁻¹ := by
  have hPen := congrArg (fun M => S⁻¹ * M * S⁻¹) (symmetricPseudoInverse_penrose S hS)
  simpa only [← Matrix.mul_assoc, nonsing_inv_mul S hDet, Matrix.one_mul,
    mul_nonsing_inv S hDet, Matrix.mul_one, Matrix.mul_assoc _ S S⁻¹] using hPen

omit [DecidableEq n] in
/-- The captured trace expressed with any inner inverse of the sampled Gram. -/
theorem squaredResidual_gram_of_inner_inverse (A : Matrix m n ℝ) (Ω : Matrix n l ℝ)
    (Q : Matrix l l ℝ)
    (hQ : ((A * Ω)ᵀ * (A * Ω)) * Q * ((A * Ω)ᵀ * (A * Ω)) =
      (A * Ω)ᵀ * (A * Ω)) :
    squaredResidual A Ω = squaredFrobenius A -
      (Q * (Ωᵀ * (Aᵀ * A) * (Aᵀ * A) * Ω)).trace := by
  rw [squaredResidual_sub_trace, rangeProjector_of_inner_inverse _ Q hQ]
  congr 1
  let Y := A * Ω
  have hc : Aᵀ * (Y * Q * Yᵀ) * A = (Aᵀ * Y) * (Q * (Yᵀ * A)) := by
    simp only [Matrix.mul_assoc]
  change (Aᵀ * (Y * Q * Yᵀ) * A).trace = (Q *
    (Ωᵀ * (Aᵀ * A) * (Aᵀ * A) * Ω)).trace
  rw [hc, trace_mul_comm]
  simp only [Y, transpose_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Gram form of the captured trace, with no restriction on the rank of the
sampled columns. K here is the unnormalized Gram matrix Aᵀ A. -/
theorem squaredResidual_gram_pseudoInverse (A : Matrix m n ℝ) (Ω : Matrix n l ℝ) :
    squaredResidual A Ω = squaredFrobenius A -
      (symmetricPseudoInverse ((A * Ω)ᵀ * (A * Ω))
        (by simpa only [conjTranspose_eq_transpose_of_trivial] using
          isHermitian_conjTranspose_mul_self (A * Ω)) *
        (Ωᵀ * (Aᵀ * A) * (Aᵀ * A) * Ω)).trace := by
  apply squaredResidual_gram_of_inner_inverse
  exact symmetricPseudoInverse_penrose _ _

omit [DecidableEq n] in
/-- Ordinary inverse form when the sampled Gram has full rank. -/
theorem squaredResidual_gram_inv (A : Matrix m n ℝ) (Ω : Matrix n l ℝ)
    (h : IsUnit (((A * Ω)ᵀ * (A * Ω)).det)) :
    squaredResidual A Ω = squaredFrobenius A -
      ((((A * Ω)ᵀ * (A * Ω))⁻¹) *
        (Ωᵀ * (Aᵀ * A) * (Aᵀ * A) * Ω)).trace := by
  rw [squaredResidual_gram_pseudoInverse, symmetricPseudoInverse_eq_inv_of_isUnit _ _ h]

end SketchOrientation
