import SketchOrientation.GramResidual
import SketchOrientation.TwoLevelAlgebra

namespace SketchOrientation

open Matrix
open scoped Matrix.Norms.Frobenius

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

omit [DecidableEq m] [DecidableEq n] in
theorem squaredFrobenius_nonneg (M : Matrix m n ℝ) : 0 ≤ squaredFrobenius M := by
  rw [squaredFrobenius_eq_norm_sq]
  exact sq_nonneg _

omit [DecidableEq m] [DecidableEq n] in
/-- Frobenius energy after right projection. -/
theorem squaredFrobenius_mul_projector_right (M : Matrix m n ℝ) (P : Matrix n n ℝ)
    (hs : Pᵀ = P) (hP : P * P = P) :
    squaredFrobenius (M * P) = (Mᵀ * M * P).trace := by
  unfold squaredFrobenius
  rw [transpose_mul, hs, Matrix.mul_assoc P, trace_mul_comm P]
  simp only [Matrix.mul_assoc, hP]

omit [DecidableEq m] in
theorem projector_complement (P : Matrix n n ℝ) (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hP, sub_self, sub_zero]

omit [DecidableEq m] in
theorem squaredFrobenius_mul_projector_right_le (M : Matrix m n ℝ) (P : Matrix n n ℝ)
    (hs : Pᵀ = P) (hP : P * P = P) :
    squaredFrobenius (M * (1 - P)) ≤ squaredFrobenius M := by
  have h1 := squaredFrobenius_mul_projector_right M P hs hP
  have h2 := squaredFrobenius_mul_projector_right M (1 - P)
    (by rw [transpose_sub, transpose_one, hs]) (projector_complement P hP)
  rw [h2, Matrix.mul_sub, Matrix.mul_one, trace_sub]
  exact sub_le_self _ (h1 ▸ squaredFrobenius_nonneg _)

/-- For the two-level input, the best rank-k squared tail is n-k, in the
unnormalized Gram units of the manuscript. -/
theorem twoLevel_optimalTail (A : Matrix m n ℝ) (V : Matrix n k ℝ)
    (hV : Vᵀ * V = 1) {Γ : ℝ} (hΓ : 1 ≤ Γ)
    (hGram : Aᵀ * A = 1 + (Γ - 1) • (V * Vᵀ)) :
    optimalTail (Fintype.card k) A = (Fintype.card n : ℝ) - Fintype.card k := by
  classical
  let P := V * Vᵀ
  have hPs : Pᵀ = P := by simp [P, transpose_mul]
  have hPi : P * P = P := by
    dsimp [P]
    rw [Matrix.mul_assoc V Vᵀ, ← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul]
  have hpTrace : P.trace = (Fintype.card k : ℝ) := by
    dsimp [P]
    rw [trace_mul_comm, hV, trace_one]
  have hPc : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPi, sub_self]
  have hZrank : (A * P).rank ≤ Fintype.card k := by
    rw [show A * P = (A * V) * Vᵀ by simp [P, Matrix.mul_assoc]]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  have hZerror : squaredFrobenius (A - A * P) =
      (Fintype.card n : ℝ) - Fintype.card k := by
    rw [show A - A * P = A * (1 - P) by rw [Matrix.mul_sub, Matrix.mul_one],
      squaredFrobenius_mul_projector_right _ _ (by rw [transpose_sub, transpose_one, hPs])
        (projector_complement _ hPi)]
    rw [hGram, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    change ((1 - P) + (Γ - 1) • (P * (1 - P))).trace = _
    rw [hPc, smul_zero, add_zero, trace_sub, trace_one, hpTrace]
  let s := {x : ℝ | ∃ Z : Matrix m n ℝ, Z.rank ≤ Fintype.card k ∧
    x = squaredFrobenius (A - Z)}
  have hmem : (Fintype.card n : ℝ) - Fintype.card k ∈ s := ⟨_, hZrank, hZerror.symm⟩
  change sInf s = _
  refine le_antisymm (csInf_le ?_ hmem) (le_csInf ⟨_, hmem⟩ ?_)
  · refine ⟨0, ?_⟩
    rintro _ ⟨Z, _, rfl⟩
    exact squaredFrobenius_nonneg _
  rintro _ ⟨Z, hZ, rfl⟩
  let S := rangeProjector Zᵀ
  let Q := (1 : Matrix n n ℝ) - S
  have hSs : Sᵀ = S := rangeProjector_transpose Zᵀ
  have hSi : S * S = S := rangeProjector_mul_self Zᵀ
  have hQs : Qᵀ = Q := by simp only [Q, transpose_sub, transpose_one, hSs]
  have hQi : Q * Q = Q := projector_complement _ hSi
  have hZS : Z * S = Z := by
    have h := congrArg Matrix.transpose (rangeProjector_mul_sample Zᵀ)
    change (S * Zᵀ)ᵀ = Zᵀᵀ at h
    simpa only [transpose_mul, transpose_transpose, hSs] using h
  have hZQ : Z * Q = 0 := by
    dsimp [Q]
    rw [Matrix.mul_sub, Matrix.mul_one, hZS, sub_self]
  have hQtrace : Q.trace = (Fintype.card n : ℝ) - Z.rank := by
    dsimp [Q, S]
    rw [trace_sub, trace_one, trace_rangeProjector, rank_transpose]
  have hVQ : 0 ≤ (P * Q).trace := by
    have h := squaredFrobenius_mul_projector_right Vᵀ Q hQs hQi
    rw [transpose_transpose] at h
    exact h ▸ squaredFrobenius_nonneg _
  calc
    _ ≤ Q.trace := by rw [hQtrace]; exact sub_le_sub_left (by exact_mod_cast hZ) _
    _ ≤ squaredFrobenius (A * Q) := by
      rw [squaredFrobenius_mul_projector_right A Q hQs hQi, hGram]
      change Q.trace ≤ ((1 + (Γ - 1) • P) * Q).trace
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, trace_add, trace_smul, smul_eq_mul]
      exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hΓ) hVQ)
    _ = squaredFrobenius ((A - Z) * Q) := by rw [Matrix.sub_mul, hZQ, sub_zero]
    _ ≤ _ := squaredFrobenius_mul_projector_right_le _ _ hSs hSi

/-- A square input realizing the two-level Gram, with positive square root
of the leading squared singular value. -/
noncomputable def twoLevelInput (V : Matrix n k ℝ) (Γ : ℝ) : Matrix n n ℝ :=
  1 + (Real.sqrt Γ - 1) • (V * Vᵀ)

theorem twoLevelInput_gram (V : Matrix n k ℝ) (hV : Vᵀ * V = 1) {Γ : ℝ} (hΓ : 0 ≤ Γ) :
    (twoLevelInput V Γ)ᵀ * twoLevelInput V Γ = 1 + (Γ - 1) • (V * Vᵀ) := by
  unfold twoLevelInput
  rw [transpose_add, transpose_smul, transpose_one, transpose_mul, transpose_transpose,
    twoLevel_gram_square _ hV, Real.sq_sqrt hΓ]

end SketchOrientation
