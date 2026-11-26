import TypicalOrientations.RotationProduct
import Mathlib.Analysis.InnerProductSpace.Positive

namespace TypicalOrientations

open Matrix SketchOrientation
open scoped InnerProductSpace

noncomputable section

variable {n l : ℕ}

private theorem frobenius_left_project (A P : Matrix (Fin n) (Fin n) ℝ)
    (hPt : Pᵀ = P) (hP : P * P = P) :
    squaredFrobenius (P * A) = (Aᵀ * P * A).trace := by
  rw [squaredFrobenius, transpose_mul, hPt, Matrix.mul_assoc Aᵀ P,
    ← Matrix.mul_assoc P P, hP, ← Matrix.mul_assoc]

private theorem frobenius_right_project (A P : Matrix (Fin n) (Fin n) ℝ)
    (hPt : Pᵀ = P) (hP : P * P = P) :
    squaredFrobenius (A * P) = (Aᵀ * A * P).trace := by
  rw [squaredFrobenius, transpose_mul, hPt]
  calc
    _ = (P * (Aᵀ * A) * P).trace := by simp only [Matrix.mul_assoc]
    _ = (P * (P * (Aᵀ * A))).trace := trace_mul_comm _ P
    _ = _ := by rw [← Matrix.mul_assoc, hP, trace_mul_comm]

/-- The Frobenius identity for the projection of skew matrices off the
pointwise stabilizer, from §2.3. -/
theorem stabilizerComplement_frobenius (L : Matrix (Fin n) (Fin n) ℝ)
    (hL : Lᵀ = -L) (P : OrthogonalProjector n l) :
    squaredFrobenius (L - (1 - P.val) * L * (1 - P.val)) =
      2 * squaredFrobenius (P.val * L) - squaredFrobenius (P.val * L * P.val) := by
  let p := P.val
  let r := 1 - p
  let C := r * L * r
  have hpt : pᵀ = p := P.property.1
  have hp : p * p = p := P.property.2.1
  have hrt : rᵀ = r := by simp [r, hpt]
  have hr : r * r = r := by
    simp [r, Matrix.sub_mul, Matrix.mul_sub, hp]
  have hC : squaredFrobenius C = (Lᵀ * r * L * r).trace := by
    unfold C
    rw [frobenius_right_project (r * L) r hrt hr, transpose_mul, hrt]
    congr 1
    calc
      _ = Lᵀ * (r * r) * L * r := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hr]
  have hCross : (Cᵀ * L).trace = (Lᵀ * r * L * r).trace := by
    rw [← trace_transpose, transpose_mul, transpose_transpose]
    congr 1
    simp only [C, Matrix.mul_assoc]
  have hF : squaredFrobenius (L - C) =
      (Lᵀ * L).trace - (Lᵀ * r * L * r).trace := by
    have hLC : (Lᵀ * C).trace = (Lᵀ * r * L * r).trace := by
      congr 1
      simp only [C, Matrix.mul_assoc]
    have hCC : (Cᵀ * C).trace = (Lᵀ * r * L * r).trace := hC
    rw [squaredFrobenius, transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      trace_sub, trace_sub, trace_sub, hCross, hLC, hCC]
    ring
  have hMixed : (Lᵀ * p * L * p).trace = squaredFrobenius (p * L * p) := by
    rw [frobenius_right_project (p * L) p hpt hp, transpose_mul, hpt]
    congr 1
    calc
      _ = Lᵀ * (p * p) * L * p := by rw [hp]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hRight : (Lᵀ * L * p).trace = squaredFrobenius (p * L) := by
    rw [← frobenius_right_project L p hpt hp, ← squaredFrobenius_transpose (L * p),
      transpose_mul, hpt, hL, Matrix.mul_neg]
    simp [squaredFrobenius]
  have hExpand :
      Lᵀ * r * L * r = (Lᵀ * L - Lᵀ * p * L) - (Lᵀ * L * p - Lᵀ * p * L * p) := by
    unfold r
    noncomm_ring
  change squaredFrobenius (L - C) = _
  rw [hF, hExpand, trace_sub, trace_sub, trace_sub, hMixed, hRight,
    ← frobenius_left_project L p hpt hp]
  ring

private theorem frobenius_eq_columns (A : Matrix (Fin n) (Fin n) ℝ) :
    squaredFrobenius A = ∑ j, ‖(WithLp.toLp 2 (fun i => A i j) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  have hcol (j : Fin n) :
      ‖(WithLp.toLp 2 (fun i => A i j) : EuclideanSpace ℝ (Fin n))‖ ^ 2 =
        ∑ i, (A i j) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [hcol]
  rw [Cosine.squaredFrobenius_eq_sum_entries]
  exact Finset.sum_comm

private theorem column_left_mul (P A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    (WithLp.toLp 2 (fun i => (P * A) i j) : EuclideanSpace ℝ (Fin n)) =
      P.toEuclideanLin (WithLp.toLp 2 (fun i => A i j)) := by
  ext i
  simp [Matrix.mul_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- The exact sufficient Lie-algebra condition at coefficients c_i/2
for a family of projectors whose ranks may differ. -/
theorem stabilizerComplement_weighted_le_mixedRanks {m : ℕ} {rank : Fin m → ℕ}
    (P : (i : Fin m) → OrthogonalProjector n (rank i)) (c : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hEnergy : ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) :
    (∑ i, (c i / 2) * squaredFrobenius
      (L - (1 - (P i).val) * L * (1 - (P i).val))) ≤ squaredFrobenius L := by
  calc
    _ ≤ ∑ i, c i * squaredFrobenius ((P i).val * L) := by
      apply Finset.sum_le_sum
      intro i _
      rw [stabilizerComplement_frobenius _ hL]
      have hpos := squaredFrobenius_nonneg ((P i).val * L * (P i).val)
      nlinarith [mul_nonneg (hc i) hpos]
    _ = ∑ j : Fin n, ∑ i,
        c i * ‖(P i).val.toEuclideanLin (WithLp.toLp 2 (fun k => L k j))‖ ^ 2 := by
      simp_rw [frobenius_eq_columns, column_left_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ _ := by
      rw [frobenius_eq_columns]
      exact Finset.sum_le_sum fun j _ => hEnergy (WithLp.toLp 2 (fun k => L k j))

/-- The Lie-algebra projection bound for a family of common rank. -/
theorem stabilizerComplement_weighted_le {m : ℕ}
    (P : Fin m → OrthogonalProjector n l) (c : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hEnergy : ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) :
    (∑ i, (c i / 2) * squaredFrobenius
      (L - (1 - (P i).val) * L * (1 - (P i).val))) ≤ squaredFrobenius L :=
  stabilizerComplement_weighted_le_mixedRanks (rank := fun _ => l) P c hc hEnergy L hL

/-- The directional energy condition in (2.5) is the Löwner bound
`∑ i, c i • P i ≤ 1`, expressed by a positive semidefinite difference. -/
theorem projector_weighted_energy_iff_posSemidef {n m : ℕ} {rank : Fin m → ℕ}
    (P : (i : Fin m) → OrthogonalProjector n (rank i)) (c : Fin m → ℝ) :
    (∀ x : EuclideanSpace ℝ (Fin n), ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2) ↔
      (1 - ∑ i, c i • (P i).val).PosSemidef := by
  let A : Matrix (Fin n) (Fin n) ℝ := 1 - ∑ i, c i • (P i).val
  have hA : A.IsHermitian := by
    unfold A IsHermitian
    simp_rw [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_one,
      transpose_sum, transpose_smul, fun i => (P i).property.1]
  have hE (i : Fin m) (x : EuclideanSpace ℝ (Fin n)) :
      ‖(P i).val.toEuclideanLin x‖ ^ 2 = inner ℝ ((P i).val.toEuclideanLin x) x := by
    rw [← orientationRowSpace_starProjection]
    exact ((orientationRowSpace (P i)).re_inner_starProjection_eq_normSq x).symm
  have hOne (x : EuclideanSpace ℝ (Fin n)) :
      (1 : Matrix (Fin n) (Fin n) ℝ).toEuclideanLin x = x := by
    exact LinearMap.congr_fun (Matrix.toLpLin_one 2) x
  have hQ (x : EuclideanSpace ℝ (Fin n)) :
      inner ℝ (A.toEuclideanLin x) x = ‖x‖ ^ 2 - ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 := by
    simp only [A, map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, inner_sub_left, sum_inner, real_inner_smul_left, hOne,
      real_inner_self_eq_norm_sq, hE]
  change _ ↔ A.PosSemidef
  rw [← Matrix.isPositive_toEuclideanLin_iff, LinearMap.IsPositive,
    Matrix.isSymmetric_toEuclideanLin_iff, and_iff_right hA]
  simp only [RCLike.re_to_real, hQ, sub_nonneg]


end

end TypicalOrientations
