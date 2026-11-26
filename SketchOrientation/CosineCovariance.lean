import SketchOrientation.CosineSpread
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Covariance before sampling

The block trace and Frobenius identities in `cosine.tex:83–99` and
`spectrum.tex:51–55` at manuscript commit `68dd06e`.
-/

open Matrix
open scoped BigOperators

namespace SketchOrientation.Cosine

/-- Covariance between coordinates in transform rows `r,s`, before sampling. -/
noncomputable def covarianceBlock {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (r s : Fin n) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b ↦ (n : ℝ) * ∑ i, dctII n r i * dctII n s i * (V i a * V i b)

/-- The diagonal covariance blocks sum to `n I_k`. -/
theorem covarianceBlock_diag_sum {n k : ℕ} {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    ∑ r, covarianceBlock V r r = (n : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  ext a b
  have hcol (i : Fin n) : ∑ r, dctII n r i ^ 2 = 1 := by
    have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i i) (dctII_transpose_mul n)
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, pow_two] using hi
  simp only [Matrix.sum_apply, covarianceBlock, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  congr 1
  simp_rw [← pow_two]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcol, one_mul]
  have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ ↦ M a b) hV
  simpa only [Matrix.mul_apply, Matrix.transpose_apply] using h

private theorem conjugation_sumSq {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : Fᵀ * F = 1) (v : Fin n → ℝ) :
    ∑ r, ∑ s, ((F * diagonal v * Fᵀ) r s)^2 = ∑ i, (v i)^2 := by
  let D := diagonal v
  let M := F * D * Fᵀ
  have hMt : Mᵀ = M := by
    simp [M, D, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  change ∑ r, ∑ s, (M r s)^2 = _
  calc
    _ = trace (Mᵀ * M) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
      exact Finset.sum_comm
    _ = trace (F * (D * D) * Fᵀ) := by
      rw [hMt]
      dsimp only [M]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Fᵀ, hF, one_mul]
    _ = trace (D * D) := by
      rw [Matrix.trace_mul_cycle, hF, one_mul]
    _ = _ := by
      simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]

/-- The squared Frobenius norms of all covariance blocks sum to
`n² η(V)`. Orthonormality of the target frame is unnecessary for this identity. -/
theorem covarianceBlock_frobenius_sum {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ) :
    (∑ r, ∑ s, ∑ a, ∑ b, (covarianceBlock V r s a b)^2) =
      (n : ℝ)^2 * rowEnergy V := by
  have hentry (r s : Fin n) (a b : Fin k) :
      covarianceBlock V r s a b =
        (n : ℝ) * (dctII n * diagonal (fun i ↦ V i a * V i b) * (dctII n)ᵀ) r s := by
    unfold covarianceBlock
    rw [Matrix.mul_apply]
    simp_rw [Matrix.transpose_apply, Matrix.mul_diagonal]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hentry, mul_pow, ← Finset.mul_sum]
  congr 1
  let f (r s : Fin n) (a b : Fin k) :=
    ((dctII n * diagonal (fun i ↦ V i a * V i b) * (dctII n)ᵀ) r s)^2
  change (∑ r, ∑ s, ∑ a, ∑ b, f r s a b) = rowEnergy V
  calc
    _ = ∑ r, ∑ a, ∑ s, ∑ b, f r s a b := by
      exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_comm
    _ = ∑ a, ∑ r, ∑ s, ∑ b, f r s a b := Finset.sum_comm
    _ = ∑ a, ∑ r, ∑ b, ∑ s, f r s a b := by
      exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun r _ ↦ Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ r, ∑ s, f r s a b := by
      exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i : Fin n, (V i a * V i b)^2 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact conjugation_sumSq (dctII_transpose_mul n) (fun i ↦ V i a * V i b)
    _ = ∑ a, ∑ i : Fin n, ∑ b, (V i a * V i b)^2 := by
      exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
    _ = ∑ i : Fin n, ∑ a, ∑ b, (V i a * V i b)^2 := Finset.sum_comm
    _ = _ := by
      unfold rowEnergy leverage
      simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, ← pow_two]

end SketchOrientation.Cosine
