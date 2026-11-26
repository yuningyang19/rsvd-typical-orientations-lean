import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace SketchOrientation

open Matrix
open scoped Matrix.Norms.Frobenius

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq l]

/-- Squared Frobenius norm in the trace representation. -/
def squaredFrobenius (A : Matrix m n ℝ) : ℝ :=
  (Aᵀ * A).trace

omit [DecidableEq m] [DecidableEq n] in
theorem squaredFrobenius_eq_norm_sq (A : Matrix m n ℝ) :
    squaredFrobenius A = ‖A‖ ^ 2 := by
  have h : 0 ≤ ∑ i, ∑ j, (A i j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt h]
  unfold squaredFrobenius Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, ← pow_two]
  exact Finset.sum_comm

/-- Orthogonal projection onto the actual image of the sampled matrix. -/
noncomputable def rangeProjector (Y : Matrix m l ℝ) : Matrix m m ℝ :=
  Matrix.toEuclideanLin.symm
    (LinearMap.range Y.toEuclideanLin).starProjection.toLinearMap

/-- The optimal squared error over all matrices of rank at most k. -/
noncomputable def optimalTail (k : ℕ) (A : Matrix m n ℝ) : ℝ :=
  sInf {x | ∃ Z : Matrix m n ℝ, Z.rank ≤ k ∧ x = squaredFrobenius (A - Z)}

/-- Squared range-finder residual from the paper. -/
noncomputable def squaredResidual (A : Matrix m n ℝ) (Ω : Matrix n l ℝ) : ℝ :=
  squaredFrobenius ((1 - rangeProjector (A * Ω)) * A)

/-- Equation (2.1) after cancelling the common total-energy factor. -/
noncomputable def tailRelativeError (k : ℕ) (A : Matrix m n ℝ) (Ω : Matrix n l ℝ) : ℝ :=
  squaredResidual A Ω / optimalTail k A

omit [DecidableEq m] [DecidableEq n] in
/-- If Aₖ is a best rank-k approximation, the infimum defining the tail is
exactly its attained error. This relates the definitions on both sides of C.1. -/
theorem optimalTail_eq_of_best_approximation (k : ℕ) (A Aₖ : Matrix m n ℝ)
    (h_rank : Aₖ.rank ≤ k)
    (h_min : ∀ Z : Matrix m n ℝ, Z.rank ≤ k → ‖A - Aₖ‖ ^ 2 ≤ ‖A - Z‖ ^ 2) :
    optimalTail k A = ‖A - Aₖ‖ ^ 2 := by
  have hMem : ‖A - Aₖ‖ ^ 2 ∈
      {x | ∃ Z : Matrix m n ℝ, Z.rank ≤ k ∧ x = squaredFrobenius (A - Z)} :=
    ⟨Aₖ, h_rank, (squaredFrobenius_eq_norm_sq _).symm⟩
  unfold optimalTail
  refine le_antisymm (csInf_le ?_ hMem) (le_csInf ⟨_, hMem⟩ ?_)
  · refine ⟨0, ?_⟩
    rintro _ ⟨Z, _, rfl⟩
    rw [squaredFrobenius_eq_norm_sq]
    exact sq_nonneg _
  · rintro _ ⟨Z, hZ, rfl⟩
    rw [squaredFrobenius_eq_norm_sq]
    exact h_min Z hZ

omit [DecidableEq n] in
/-- The paper's two ratios have a common total-energy normalization. -/
theorem tailRelativeError_eq_normalized_ratio (k : ℕ) (A : Matrix m n ℝ)
    (Ω : Matrix n l ℝ) (h_energy : squaredFrobenius A ≠ 0) :
    tailRelativeError k A Ω =
      (squaredResidual A Ω / squaredFrobenius A) /
      (optimalTail k A / squaredFrobenius A) := by
  rw [tailRelativeError, div_div_div_cancel_right₀ h_energy]

private theorem toEuclideanLin_mul {i j k : Type*} [Fintype j] [Fintype k]
    [DecidableEq j] [DecidableEq k]
    (A : Matrix i j ℝ) (B : Matrix j k ℝ) :
    (A * B).toEuclideanLin = A.toEuclideanLin.comp B.toEuclideanLin := by
  ext x : 1
  change WithLp.toLp 2 ((A * B) *ᵥ WithLp.ofLp x) =
    WithLp.toLp 2 (A *ᵥ (B *ᵥ WithLp.ofLp x))
  rw [mulVec_mulVec]

private theorem toEuclideanLin_one :
    (1 : Matrix m m ℝ).toEuclideanLin = LinearMap.id := by
  ext x : 1
  simp

private theorem rangeProjector_apply (Y : Matrix m l ℝ) :
    (rangeProjector Y).toEuclideanLin =
      (LinearMap.range Y.toEuclideanLin).starProjection.toLinearMap :=
  LinearEquiv.apply_symm_apply _ _

/-- The sampled orthogonal projector conjugates by a symmetric sign matrix.
The use of the actual range includes rank-deficient draws. -/
theorem rangeProjector_sign_mul (Y : Matrix m l ℝ) (D : Matrix m m ℝ)
    (hDt : Dᵀ = D) (hDD : D * D = 1) :
    rangeProjector (D * Y) = D * rangeProjector Y * D := by
  apply Matrix.toEuclideanLin.injective
  rw [rangeProjector_apply, toEuclideanLin_mul (D * rangeProjector Y) D,
    toEuclideanLin_mul D (rangeProjector Y), rangeProjector_apply]
  let S := LinearMap.range Y.toEuclideanLin
  let d := D.toEuclideanLin
  have hd : d.comp d = LinearMap.id := by
    rw [← toEuclideanLin_mul, hDD, toEuclideanLin_one]
  have hdx (x : EuclideanSpace ℝ m) : d (d x) = x := LinearMap.congr_fun hd x
  have hds : d.IsSymmetric := by
    have hadj : d.adjoint = d := by
      simpa only [conjTranspose_eq_transpose_of_trivial, hDt, d] using
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint D).symm
    intro x y
    rw [← LinearMap.adjoint_inner_left, hadj]
  rw [toEuclideanLin_mul D Y]
  ext x : 1
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · have hp : S.starProjection (d x) ∈ S := (S.orthogonalProjectionOnto (d x)).property
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hp
    exact LinearMap.mem_range.mpr ⟨u, congrArg d hu⟩
  · intro w hw
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hw
    have hz : Y.toEuclideanLin u ∈ S := LinearMap.mem_range_self _ _
    rw [← hu]
    change inner ℝ (d (Y.toEuclideanLin u)) (x - d (S.starProjection (d x))) = 0
    rw [hds (Y.toEuclideanLin u) (x - d (S.starProjection (d x))), LinearMap.map_sub, hdx]
    exact S.sub_starProjection_mem_orthogonal (d x) _ hz

omit [DecidableEq m] in
theorem squaredFrobenius_mul_orthogonal_right (A : Matrix m n ℝ) (Q : Matrix n n ℝ)
    (hQ : Q * Qᵀ = 1) :
    squaredFrobenius (A * Q) = squaredFrobenius A := by
  unfold squaredFrobenius
  rw [transpose_mul, trace_mul_comm (Qᵀ * Aᵀ), Matrix.mul_assoc A Q,
    ← Matrix.mul_assoc Q Qᵀ Aᵀ, hQ, Matrix.one_mul, trace_mul_comm]

omit [DecidableEq n] in
theorem squaredFrobenius_mul_orthogonal_left (A : Matrix m n ℝ) (Q : Matrix m m ℝ)
    (hQ : Qᵀ * Q = 1) :
    squaredFrobenius (Q * A) = squaredFrobenius A := by
  unfold squaredFrobenius
  rw [transpose_mul, Matrix.mul_assoc Aᵀ, ← Matrix.mul_assoc Qᵀ Q, hQ, Matrix.one_mul]

omit [DecidableEq m] in
/-- The set of attainable squared rank-k approximation errors is invariant
under an orthogonal change of the right coordinates. -/
theorem optimalTail_mul_orthogonal_right (k : ℕ) (A : Matrix m n ℝ) (Q : Matrix n n ℝ)
    (hq : Q * Qᵀ = 1) (hqt : Qᵀ * Q = 1) :
    optimalTail k (A * Q) = optimalTail k A := by
  unfold optimalTail
  congr 1
  ext x
  constructor
  · rintro ⟨Z, hZ, hx⟩
    refine ⟨Z * Qᵀ, (rank_mul_le_left _ _).trans hZ, hx.trans ?_⟩
    rw [← squaredFrobenius_mul_orthogonal_right (A * Q - Z) Qᵀ (by simpa using hqt),
      Matrix.sub_mul, Matrix.mul_assoc, hq, Matrix.mul_one]
  · rintro ⟨Z, hZ, hx⟩
    refine ⟨Z * Q, (rank_mul_le_left _ _).trans hZ, hx.trans ?_⟩
    rw [← Matrix.sub_mul, squaredFrobenius_mul_orthogonal_right _ _ hq]

set_option maxHeartbeats 800000 in
/-- The draw-wise argument of Proposition C.1 for any orthogonal core.
The prescribed pairing is built into the two arguments of the conclusion. -/
theorem pairedDraw_orthogonal (k : ℕ) (σ signs : n → ℝ) (F : Matrix n n ℝ)
    (hF : Fᵀ * F = 1) (hFt : F * Fᵀ = 1) (Ω₁ : Matrix n l ℝ)
    (hsigns : ∀ i, signs i = -1 ∨ signs i = 1)
    (_htail : 0 < optimalTail k (diagonal σ)) :
    tailRelativeError k (diagonal σ) (diagonal signs * Fᵀ * Ω₁) =
      tailRelativeError k (diagonal σ * Fᵀ) Ω₁ := by
  let D := diagonal signs
  let spectrumDiagonal := diagonal σ
  let A := spectrumDiagonal * Fᵀ
  have hDt : Dᵀ = D := diagonal_transpose _
  have hDD : D * D = 1 := by
    have hself : ∀ i, signs i * signs i = 1 := fun i => by
      rcases hsigns i with h | h <;> rw [h] <;> norm_num
    simp [D, diagonal_mul_diagonal, hself]
  have hcomm : spectrumDiagonal * D = D * spectrumDiagonal := by
    simp [spectrumDiagonal, D, diagonal_mul_diagonal, mul_comm]
  change squaredResidual spectrumDiagonal (D * Fᵀ * Ω₁) / optimalTail k spectrumDiagonal =
    squaredResidual A Ω₁ / optimalTail k A
  have hsample : spectrumDiagonal * (D * Fᵀ * Ω₁) = D * (A * Ω₁) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcomm]
    simp [A, Matrix.mul_assoc]
  have hrotate : D * A * (F * D) = spectrumDiagonal := by
    calc
      D * A * (F * D) = D * (spectrumDiagonal * (Fᵀ * F)) * D := by
        simp only [A, Matrix.mul_assoc]
      _ = spectrumDiagonal := by
        rw [hF, Matrix.mul_one, ← hcomm, Matrix.mul_assoc, hDD, Matrix.mul_one]
  have hright : (F * D) * (F * D)ᵀ = 1 := by
    rw [transpose_mul, hDt, Matrix.mul_assoc, ← Matrix.mul_assoc D D Fᵀ, hDD, Matrix.one_mul, hFt]
  have htailEq : optimalTail k A = optimalTail k spectrumDiagonal := by
    apply optimalTail_mul_orthogonal_right
    · simpa using hF
    · simpa using hFt
  rw [htailEq]
  congr 1
  unfold squaredResidual
  rw [hsample, rangeProjector_sign_mul _ _ hDt hDD]
  let P := rangeProjector (A * Ω₁)
  have hfactor : (1 - D * P * D) * D = D * (1 - P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc (D * P), hDD, Matrix.mul_one]
  have hres :
      (1 - D * P * D) * spectrumDiagonal = D * ((1 - P) * A) * (F * D) := by
    calc
      _ = (1 - D * P * D) * (D * A * (F * D)) := by rw [hrotate]
      _ = ((1 - D * P * D) * D) * A * (F * D) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hfactor, Matrix.mul_assoc D (1 - P) A]
  change squaredFrobenius ((1 - D * P * D) * spectrumDiagonal) =
    squaredFrobenius ((1 - P) * A)
  rw [hres, squaredFrobenius_mul_orthogonal_right _ _ hright,
    squaredFrobenius_mul_orthogonal_left _ _ (hDt.symm ▸ hDD)]

end SketchOrientation
