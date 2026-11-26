import SketchOrientation.AtomTheorem
import SketchOrientation.DctSketchLaw
import SketchOrientation.GaussianOrthogonal
import SketchOrientation.UnequalSpikes

namespace TypicalOrientations

open Matrix SketchOrientation

/-- Squared projection of the single spike direction onto the sketch space. -/
def spikeProjectionEnergy {n : ℕ} (V : Matrix (Fin n) (Fin 1) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (Vᵀ * P * V) 0 0

private theorem mul_rowSelector_transpose {a b c : ℕ}
    (J : Fin b ↪ Fin c) (Q : Matrix (Fin a) (Fin c) ℝ) :
    Q * (rowSelector J)ᵀ = Q.submatrix id J := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, rowSelector, submatrix_apply, id_eq, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- For a single spike and a flat unit tail, any target rank between 1 and n
removes the spike and k-1 unit singular values. -/
theorem spike_optimalTail {m n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin 1) ℝ)
    (hV : Vᵀ * V = 1) :
    Aᵀ * A = 1 + (n : ℝ) • (V * Vᵀ) →
      optimalTail k A = (n : ℝ) - k := by
  intro hGram
  obtain ⟨Q, hQ, hQV⟩ := exists_orthogonal_extension (show 1 ≤ n by omega) V hV
  let W := Q * (rowSelector (Fin.castLEEmb hkn))ᵀ
  let S := (rowSelector (Fin.castLEEmb (show 1 ≤ k by omega)))ᵀ
  have hW : Wᵀ * W = 1 := by
    dsimp only [W]
    rw [transpose_mul, transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul, rowSelector_orthonormal]
  have hWS : W * S = V := by
    unfold W S
    rw [mul_rowSelector_transpose, mul_rowSelector_transpose, Matrix.submatrix_submatrix, ← hQV]
    rfl
  let H := (n : ℝ) • (S * Sᵀ)
  have hH : H.PosSemidef := by
    have hPSD : (S * Sᵀ).PosSemidef := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose S
    exact hPSD.smul (Nat.cast_nonneg _)
  have hWH : W * H * Wᵀ = (n : ℝ) • (V * Vᵀ) := by
    simp only [H, Matrix.mul_smul, Matrix.smul_mul, ← hWS, transpose_mul,
      Matrix.mul_assoc]
  simpa only [Fintype.card_fin] using
    flatTail_optimalTail A W hW H hH (hGram.trans (congrArg (fun M => 1 + M) hWH.symm))

private theorem trace_inv_finOne (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A⁻¹.trace = (A 0 0)⁻¹ := by
  simp [Matrix.inv_subsingleton, Matrix.trace_diagonal, Fin.default_eq_zero]

/-- Equation (spike-loss) at an actual rank-width orthogonal projector.
The trace step is the one-column specialization of the compressed Gram calculation. -/
theorem spike_tailRelativeError {m n k ℓ : ℕ} (hk : 0 < k) (hkn : k < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin 1) ℝ)
    (hV : Vᵀ * V = 1) (P : OrthogonalProjector n ℓ)
    (hGram : Aᵀ * A = 1 + (n : ℝ) • (V * Vᵀ)) :
    tailRelativeError k A P.val = ((n : ℝ) - ℓ - 1) / ((n : ℝ) - k) +
      ((n : ℝ) + 1) / ((n : ℝ) - k) *
        (1 + (n : ℝ) * spikeProjectionEnergy V P.val)⁻¹ := by
  obtain ⟨B, hB, hP⟩ := exists_frame_of_projector P.val P.property.1
    P.property.2.1 P.property.2.2
  have hΓ : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hΓsub : (n : ℝ) + 1 - 1 = n := add_sub_cancel_right _ _
  have h := twoLevel_squaredResidual A B V hB hV hΓ (by rwa [hΓsub])
  rw [← squaredResidual_frame_projector A B hB, hP, hΓsub, trace_inv_finOne] at h
  simp only [Fintype.card_fin, Nat.cast_one, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply,
    smul_eq_mul] at h
  rw [tailRelativeError, spike_optimalTail hk hkn.le A V hV hGram, h, spikeProjectionEnergy]
  ring

end TypicalOrientations
