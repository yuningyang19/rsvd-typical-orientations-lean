import SketchOrientation.SpectrumResidual
import SketchOrientation.TwoLevelResidual
import Mathlib.Analysis.Matrix.Order

namespace SketchOrientation

open Matrix
open scoped MatrixOrder

variable {m n l k : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq l] [DecidableEq k]

private theorem trace_conjugation_mono {A B : Matrix n n ℝ} (h : A ≤ B)
    (Q : Matrix n l ℝ) : (Qᵀ * A * Q).trace ≤ (Qᵀ * B * Q).trace := by
  have hP := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same Q
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul] at hP
  exact sub_nonneg.mp (by simpa only [trace_sub] using hP.trace_nonneg)

omit [Fintype l] [Fintype k] [DecidableEq l] [DecidableEq k] in
private theorem squaredFrobenius_mul_eq_conjugate (T : Matrix m n ℝ) (Q : Matrix n n ℝ) :
    squaredFrobenius (T * Q) = (Qᵀ * (Tᵀ * T) * Q).trace := by
  simp only [squaredFrobenius, transpose_mul, Matrix.mul_assoc]

omit [Fintype k] [DecidableEq k] in
/-- The projected range-finder residual is increasing in the Gram matrix.
A least-squares coefficient is provided by the Moore–Penrose formula. -/
theorem squaredResidual_mono_gram {m' : Type*} [Fintype m'] [DecidableEq m']
    (A : Matrix m n ℝ) (B : Matrix m' n ℝ) (Ω : Matrix n l ℝ)
    (hAB : Aᵀ * A ≤ Bᵀ * B) :
    squaredResidual A Ω ≤ squaredResidual B Ω := by
  let Y := B * Ω
  have hS : (Yᵀ * Y).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_self Y
  let R := symmetricPseudoInverse (Yᵀ * Y) hS * Yᵀ * B
  let Q : Matrix n n ℝ := 1 - Ω * R
  have hYR : Y * R = rangeProjector Y * B := by
    rw [rangeProjector_eq_gram_pseudoInverse]
    simp only [R, Matrix.mul_assoc]
  have hLeft : A * Q = A - (A * Ω) * R := by
    simp only [Q, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have hRight : B * Q = (1 - rangeProjector Y) * B := by
    rw [show Q = 1 - Ω * R from rfl, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, show B * Ω = Y from rfl, hYR,
      Matrix.sub_mul, Matrix.one_mul]
  calc
    _ ≤ squaredFrobenius (A * Q) := hLeft ▸ squaredResidual_le_sampled_approximation A Ω R
    _ ≤ squaredFrobenius (B * Q) := by
      rw [squaredFrobenius_mul_eq_conjugate A Q, squaredFrobenius_mul_eq_conjugate B Q]
      exact trace_conjugation_mono hAB Q
    _ = _ := by rw [hRight]; rfl

/-- With a positive perturbation supported on the prescribed leading
frame, the best rank-k tail has exactly n−k energy. -/
theorem flatTail_optimalTail (A : Matrix m n ℝ) (V : Matrix n k ℝ)
    (hV : Vᵀ * V = 1) (H : Matrix k k ℝ) (hH : H.PosSemidef)
    (hGram : Aᵀ * A = 1 + V * H * Vᵀ) :
    optimalTail (Fintype.card k) A = (Fintype.card n : ℝ) - Fintype.card k := by
  let P := V * Vᵀ
  have hPs : Pᵀ = P := by simp [P, transpose_mul]
  have hPi : P * P = P := by
    simp only [P, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul]
  have hpTrace : P.trace = (Fintype.card k : ℝ) := by
    dsimp [P]
    rw [trace_mul_comm, hV, trace_one]
  have hOrth : Vᵀ * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, show Vᵀ * P = Vᵀ by
      rw [show P = V * Vᵀ from rfl, ← Matrix.mul_assoc, hV, Matrix.one_mul], sub_self]
  have hZrank : (A * P).rank ≤ Fintype.card k := by
    rw [show A * P = (A * V) * Vᵀ by simp [P, Matrix.mul_assoc]]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  have hZerror : squaredFrobenius (A - A * P) =
      (Fintype.card n : ℝ) - Fintype.card k := by
    rw [show A - A * P = A * (1 - P) by rw [Matrix.mul_sub, Matrix.mul_one],
      squaredFrobenius_mul_projector_right _ _ (by rw [transpose_sub, transpose_one, hPs])
        (projector_complement _ hPi), hGram, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_assoc (V * H), hOrth, Matrix.mul_zero, add_zero, trace_sub, trace_one, hpTrace]
  apply optimalTail_eq_of_best_approximation _ _ (A * P) hZrank
    (fun Z hZ => ?_) |>.trans
  · exact (squaredFrobenius_eq_norm_sq _).symm.trans hZerror
  · rw [← squaredFrobenius_eq_norm_sq, ← squaredFrobenius_eq_norm_sq, hZerror]
    let S := rangeProjector Zᵀ
    let Q := (1 : Matrix n n ℝ) - S
    have hSs : Sᵀ = S := rangeProjector_transpose Zᵀ
    have hSi : S * S = S := rangeProjector_mul_self Zᵀ
    have hQs : Qᵀ = Q := by simp only [Q, transpose_sub, transpose_one, hSs]
    have hQi : Q * Q = Q := projector_complement _ hSi
    have hZS : Z * S = Z := by
      have hz := congrArg Matrix.transpose (rangeProjector_mul_sample Zᵀ)
      change (S * Zᵀ)ᵀ = Zᵀᵀ at hz
      simpa only [transpose_mul, transpose_transpose, hSs] using hz
    have hZQ : Z * Q = 0 := by
      rw [show Q = 1 - S from rfl, Matrix.mul_sub, Matrix.mul_one, hZS, sub_self]
    have hQTrace : Q.trace = (Fintype.card n : ℝ) - Z.rank := by
      dsimp [Q, S]
      rw [trace_sub, trace_one, trace_rangeProjector, rank_transpose]
    have hOne : (1 : Matrix n n ℝ) ≤ Aᵀ * A := by
      rw [Matrix.le_iff, hGram, add_sub_cancel_left]
      simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
        hH.conjTranspose_mul_mul_same Vᵀ
    calc
      _ ≤ Q.trace := by rw [hQTrace]; exact sub_le_sub_left (by exact_mod_cast hZ) _
      _ ≤ squaredFrobenius (A * Q) := by
        have hh := trace_conjugation_mono hOne Q
        rw [hQs, Matrix.mul_one, hQi] at hh
        simpa only [squaredFrobenius, transpose_mul, Matrix.mul_assoc, hQs] using hh
      _ = squaredFrobenius ((A - Z) * Q) := by rw [Matrix.sub_mul, hZQ, sub_zero]
      _ ≤ _ := squaredFrobenius_mul_projector_right_le _ _ hSs hSi

/-- Unequal leading squared singular values in the interval
`[Γ₋, Γ₊]` are bounded by the two equal-spike losses on every draw. -/
theorem unequalSpikes_centeredRankLoss_bounds (A : Matrix m n ℝ) (V : Matrix n k ℝ)
    (hV : Vᵀ * V = 1) (H : Matrix k k ℝ) (hH : H.PosSemidef)
    (hGram : Aᵀ * A = 1 + V * H * Vᵀ) {lo hi : ℝ} (hlo : 1 ≤ lo) (hhi : 1 ≤ hi)
    (hLow : (lo - 1) • (1 : Matrix k k ℝ) ≤ H)
    (hHigh : H ≤ (hi - 1) • (1 : Matrix k k ℝ))
    (hkn : Fintype.card k < Fintype.card n) (Ω : Matrix n l ℝ) :
    centeredRankLoss (Fintype.card k) (twoLevelInput V lo) Ω ≤
      centeredRankLoss (Fintype.card k) A Ω ∧
    centeredRankLoss (Fintype.card k) A Ω ≤
      centeredRankLoss (Fintype.card k) (twoLevelInput V hi) Ω := by
  have hConj {X Y : Matrix k k ℝ} (h : X ≤ Y) :
      (1 + V * X * Vᵀ) ≤ 1 + V * Y * Vᵀ := by
    rw [Matrix.le_iff, add_sub_add_left_eq_sub]
    have hP := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same Vᵀ
    simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose, Matrix.mul_sub,
      Matrix.sub_mul] using hP
  have hL := hConj hLow
  have hU := hConj hHigh
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hL hU
  have hGL := twoLevelInput_gram V hV (zero_le_one.trans hlo)
  have hGU := twoLevelInput_gram V hV (zero_le_one.trans hhi)
  rw [← hGram, ← hGL] at hL
  rw [← hGram, ← hGU] at hU
  have he := flatTail_optimalTail A V hV H hH hGram
  have hPos : 0 ≤ (Fintype.card n : ℝ) - Fintype.card k :=
    sub_nonneg.mpr (by exact_mod_cast hkn.le)
  have hK : 0 ≤ (Fintype.card k : ℝ) := Nat.cast_nonneg _
  unfold centeredRankLoss tailRelativeError
  rw [he, twoLevel_optimalTail _ _ hV hlo hGL, twoLevel_optimalTail _ _ hV hhi hGU]
  exact ⟨div_le_div_of_nonneg_right
    (sub_le_sub_right (div_le_div_of_nonneg_right (squaredResidual_mono_gram _ _ Ω hL) hPos) 1) hK,
    div_le_div_of_nonneg_right
      (sub_le_sub_right (div_le_div_of_nonneg_right (squaredResidual_mono_gram _ _ Ω hU) hPos) 1) hK⟩

end SketchOrientation
