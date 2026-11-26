import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

namespace SketchOrientation

open Matrix

variable {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
  [DecidableEq n] [DecidableEq k] [DecidableEq l]

omit [DecidableEq k] [DecidableEq l] in
private theorem positive_transpose_mul (C : Matrix l k ℝ) : (Cᵀ * C).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self C

omit [DecidableEq l] in
/-- The regularized Gram is positive definite for every nonnegative ridge
coefficient, regardless of the rank of the rectangular block. -/
theorem affineGram_posDef (C : Matrix l k ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (1 + a • (Cᵀ * C)).PosDef :=
  Matrix.PosDef.one.add_posSemidef ((positive_transpose_mul C).smul ha)

/-- Squaring the two-level Gram squares the upper eigenvalue and retains
the same leading subspace. -/
theorem twoLevel_gram_square (V : Matrix n k ℝ) (hV : Vᵀ * V = 1) (Γ : ℝ) :
    (1 + (Γ - 1) • (V * Vᵀ)) * (1 + (Γ - 1) • (V * Vᵀ)) =
      1 + (Γ ^ 2 - 1) • (V * Vᵀ) := by
  classical
  have hP : (V * Vᵀ) * (V * Vᵀ) = V * Vᵀ := by
    rw [Matrix.mul_assoc V Vᵀ, ← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul]
  simp only [add_assoc, ← add_smul]
  ring_nf

omit [Fintype l] [DecidableEq k] in
/-- Compressing a two-level Gram to the sketch width. -/
theorem twoLevel_gram_compress (U : Matrix n l ℝ) (hU : Uᵀ * U = 1)
    (V : Matrix n k ℝ) (a : ℝ) :
    Uᵀ * (1 + a • (V * Vᵀ)) * U =
      1 + a • ((Uᵀ * V : Matrix l k ℝ) * (Uᵀ * V)ᵀ) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU,
    Matrix.mul_smul, Matrix.smul_mul, transpose_mul, transpose_transpose]
  simp only [Matrix.mul_assoc]

private theorem affineGram_commute (C : Matrix l k ℝ) (a : ℝ) :
    (1 + a • (C * Cᵀ)) * C = C * (1 + a • (Cᵀ * C)) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

private theorem affineGram_inv_commute (C : Matrix l k ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (1 + a • (C * Cᵀ))⁻¹ * C = C * (1 + a • (Cᵀ * C))⁻¹ := by
  let L := 1 + a • (C * Cᵀ)
  let R := 1 + a • (Cᵀ * C)
  have hL : IsUnit L.det := isUnit_iff_ne_zero.mpr (by
    simpa [L] using (affineGram_posDef Cᵀ ha).det_pos.ne')
  have hR : IsUnit R.det := isUnit_iff_ne_zero.mpr (affineGram_posDef C ha).det_pos.ne'
  have h := congrArg (fun N => L⁻¹ * N * R⁻¹) (affineGram_commute C a)
  change L⁻¹ * (L * C) * R⁻¹ = L⁻¹ * (C * R) * R⁻¹ at h
  rw [← Matrix.mul_assoc L⁻¹ L, nonsing_inv_mul L hL, Matrix.one_mul,
    ← Matrix.mul_assoc L⁻¹ C, mul_nonsing_inv_cancel_right R _ hR] at h
  exact h.symm

/-- The trace captured by the two compressed Grams from the manuscript's
two-level calculation. The k-by-k inverse retains all zero singular values. -/
theorem twoLevel_captured_trace (C : Matrix l k ℝ) {Γ : ℝ} (hΓ : 1 ≤ Γ) :
    ((1 + (Γ - 1) • (C * Cᵀ))⁻¹ * (1 + (Γ ^ 2 - 1) • (C * Cᵀ))).trace =
      (Fintype.card l : ℝ) + Γ *
        ((Fintype.card k : ℝ) - ((1 + (Γ - 1) • (Cᵀ * C))⁻¹).trace) := by
  let L := 1 + (Γ - 1) • (C * Cᵀ)
  let R := 1 + (Γ - 1) • (Cᵀ * C)
  have ha := sub_nonneg.mpr hΓ
  have hL : IsUnit L.det := isUnit_iff_ne_zero.mpr (by
    simpa [L] using (affineGram_posDef Cᵀ ha).det_pos.ne')
  have hR : IsUnit R.det := isUnit_iff_ne_zero.mpr (affineGram_posDef C ha).det_pos.ne'
  have hsplit : (1 + (Γ ^ 2 - 1) • (C * Cᵀ)) =
      L + (Γ * (Γ - 1)) • (C * Cᵀ) := by
    dsimp [L]
    rw [add_assoc, ← add_smul]
    congr 2
    ring
  have hC : L⁻¹ * C = C * R⁻¹ := affineGram_inv_commute C ha
  have hTrace : (L⁻¹ * (C * Cᵀ)).trace = (R⁻¹ * (Cᵀ * C)).trace := by
    rw [← Matrix.mul_assoc L⁻¹, hC, Matrix.mul_assoc C, trace_mul_comm, Matrix.mul_assoc]
  have hPop : (Γ - 1) • (R⁻¹ * (Cᵀ * C)) = (1 : Matrix k k ℝ) - R⁻¹ := by
    have hSum : R⁻¹ + (Γ - 1) • (R⁻¹ * (Cᵀ * C)) = 1 := calc
      _ = R⁻¹ * R := by
        dsimp [R]
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
      _ = 1 := nonsing_inv_mul R hR
    exact eq_sub_of_add_eq (by simpa only [add_comm] using hSum)
  have hTrace' := congrArg Matrix.trace hPop
  rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, smul_eq_mul] at hTrace'
  rw [hsplit]
  change (L⁻¹ * (L + (Γ * (Γ - 1)) • (C * Cᵀ))).trace = _
  rw [Matrix.mul_add, nonsing_inv_mul L hL, Matrix.mul_smul, trace_add, trace_one,
    trace_smul, smul_eq_mul, hTrace, mul_assoc, hTrace']

end SketchOrientation
