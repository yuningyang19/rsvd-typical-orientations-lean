import TypicalOrientations.LieProjection
import TypicalOrientations.BCLMGradientGeometry

namespace TypicalOrientations

open Matrix SketchOrientation
open scoped InnerProductSpace

noncomputable section

private abbrev FrobeniusCoordinates (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

private def coordinateMatrix (n : ℕ) : FrobeniusCoordinates n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun v := Matrix.of (fun i j => v (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem coordinateMatrix_injective (n : ℕ) : Function.Injective (coordinateMatrix n) := by
  intro x y h
  ext ij
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A ij.1 ij.2) h

/-- The real Lie algebra of the orthogonal group, with the Frobenius
inner product inherited from its Euclidean entry coordinates. -/
def skewFrobeniusSubmodule (n : ℕ) : Submodule ℝ (FrobeniusCoordinates n) where
  carrier := {x | (coordinateMatrix n x)ᵀ = -(coordinateMatrix n x)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (coordinateMatrix n x)ᵀ = -(coordinateMatrix n x) at hx
    change (coordinateMatrix n y)ᵀ = -(coordinateMatrix n y) at hy
    change (coordinateMatrix n (x + y))ᵀ = -(coordinateMatrix n (x + y))
    rw [map_add, transpose_add, hx, hy, neg_add]
  smul_mem' := by
    intro c x hx
    change (coordinateMatrix n x)ᵀ = -(coordinateMatrix n x) at hx
    change (coordinateMatrix n (c • x))ᵀ = -(coordinateMatrix n (c • x))
    rw [map_smul, transpose_smul, hx, smul_neg]

abbrev SkewFrobenius (n : ℕ) := ↥(skewFrobeniusSubmodule n)

variable {n l : ℕ}

/-- Matrix realization of the skew Frobenius space. -/
def skewMatrix : SkewFrobenius n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (coordinateMatrix n).comp (skewFrobeniusSubmodule n).subtype

theorem skewMatrix_injective : Function.Injective (skewMatrix (n := n)) := by
  intro L M h
  exact Subtype.ext (coordinateMatrix_injective n h)

@[simp] theorem skewMatrix_transpose (L : SkewFrobenius n) :
    (skewMatrix L)ᵀ = -(skewMatrix L) := L.property

/-- Inverse coordinate map, restricted to skew matrices. -/
def skewOfMatrix (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) : SkewFrobenius n :=
  ⟨WithLp.toLp 2 (fun ij : Fin n × Fin n => L ij.1 ij.2), hL⟩

@[simp] theorem skewMatrix_skewOfMatrix (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) :
    skewMatrix (skewOfMatrix L hL) = L := rfl

/-- Frobenius normalization agrees with the inner product used by the
orthonormal basis and the projection API. -/
theorem skewMatrix_norm_sq (L : SkewFrobenius n) :
    ‖L‖ ^ 2 = squaredFrobenius (skewMatrix L) := by
  change ‖L.val‖ ^ 2 = _
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Cosine.squaredFrobenius_eq_sum_entries]
  rfl

theorem skewMatrix_inner (L M : SkewFrobenius n) :
    inner ℝ L M = ((skewMatrix L)ᵀ * skewMatrix M).trace := by
  change inner ℝ L.val M.val = _
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type]
  simp only [star_trivial, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change M.val (j, i) * L.val (j, i) = L.val (j, i) * M.val (j, i)
  ring

private theorem isSkew_conjugate (R : Matrix (Fin n) (Fin n) ℝ) (L : SkewFrobenius n) :
    (Rᵀ * skewMatrix L * R)ᵀ = -(Rᵀ * skewMatrix L * R) := by
  simp only [transpose_mul, transpose_transpose, skewMatrix_transpose, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc]

private def skewConjugateValue (R : Matrix (Fin n) (Fin n) ℝ) (L : SkewFrobenius n) :
    SkewFrobenius n :=
  skewOfMatrix (Rᵀ * skewMatrix L * R) (isSkew_conjugate R L)

private theorem skewConjugateValue_inverse (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R * Rᵀ = 1) (L : SkewFrobenius n) :
    skewConjugateValue Rᵀ (skewConjugateValue R L) = L := by
  apply skewMatrix_injective
  change Rᵀᵀ * (Rᵀ * skewMatrix L * R) * Rᵀ = skewMatrix L
  rw [transpose_transpose]
  calc
    _ = (R * Rᵀ) * skewMatrix L * (R * Rᵀ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hR, Matrix.one_mul, Matrix.mul_one]

/-- Orthogonal conjugation in Frobenius coordinates. -/
def skewConjugate (R : Matrix (Fin n) (Fin n) ℝ) (hR : Rᵀ * R = 1) :
    SkewFrobenius n ≃ₗᵢ[ℝ] SkewFrobenius n where
  toLinearEquiv :=
    { toFun := skewConjugateValue R
      invFun := skewConjugateValue Rᵀ
      left_inv := skewConjugateValue_inverse R (mul_eq_one_comm.mp hR)
      right_inv := by
        intro L
        have hRt : Rᵀ * Rᵀᵀ = 1 := by rwa [transpose_transpose]
        simpa only [transpose_transpose] using skewConjugateValue_inverse Rᵀ hRt L
      map_add' := by
        intro L M
        apply skewMatrix_injective
        simp only [skewConjugateValue, skewMatrix_skewOfMatrix, map_add, Matrix.mul_add,
          Matrix.add_mul]
      map_smul' := by
        intro a L
        apply skewMatrix_injective
        simp only [skewConjugateValue, skewMatrix_skewOfMatrix, map_smul, RingHom.id_apply,
          Matrix.mul_smul, Matrix.smul_mul] }
  norm_map' := by
    intro L
    change ‖skewConjugateValue R L‖ = ‖L‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [skewMatrix_norm_sq, skewMatrix_norm_sq, skewConjugateValue, skewMatrix_skewOfMatrix]
    have hRR : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
    rw [squaredFrobenius_mul_orthogonal_right _ _ hRR,
      squaredFrobenius_mul_orthogonal_left _ _ (by rwa [transpose_transpose])]

@[simp] theorem skewMatrix_skewConjugate (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : Rᵀ * R = 1) (L : SkewFrobenius n) :
    skewMatrix (skewConjugate R hR L) = Rᵀ * skewMatrix L * R := rfl

/-- Infinitesimal rotations that vanish on the projected sketch space. -/
def skewStabilizer (P : OrthogonalProjector n l) : Submodule ℝ (SkewFrobenius n) where
  carrier := {L | skewMatrix L * P.val = 0}
  zero_mem' := by simp
  add_mem' := by
    intro L M hL hM
    change skewMatrix L * P.val = 0 at hL
    change skewMatrix M * P.val = 0 at hM
    change skewMatrix (L + M) * P.val = 0
    rw [map_add, Matrix.add_mul, hL, hM, add_zero]
  smul_mem' := by
    intro a L hL
    change skewMatrix L * P.val = 0 at hL
    change skewMatrix (a • L) * P.val = 0
    rw [map_smul, Matrix.smul_mul, hL, smul_zero]

@[simp] theorem mem_skewStabilizer (P : OrthogonalProjector n l) (L : SkewFrobenius n) :
    L ∈ skewStabilizer P ↔ skewMatrix L * P.val = 0 := Iff.rfl

private theorem skewMatrix_starProjection_stabilizer (P : OrthogonalProjector n l)
    (L : SkewFrobenius n) :
    skewMatrix ((skewStabilizer P).starProjection L) =
      (1 - P.val) * skewMatrix L * (1 - P.val) := by
  let Q := 1 - P.val
  have hQt : Qᵀ = Q := by simp only [Q, transpose_sub, transpose_one, P.property.1]
  have hQP : Q * P.val = 0 := by
    simp only [Q, Matrix.sub_mul, Matrix.one_mul, P.property.2.1, sub_self]
  have hSkew : (Q * skewMatrix L * Q)ᵀ = -(Q * skewMatrix L * Q) := by
    simp only [transpose_mul, hQt, skewMatrix_transpose, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc]
  let C := skewOfMatrix (Q * skewMatrix L * Q) hSkew
  have hC : C ∈ skewStabilizer P := by
    rw [mem_skewStabilizer, skewMatrix_skewOfMatrix, Matrix.mul_assoc _ Q P.val, hQP, Matrix.mul_zero]
  have hOrth : L - C ∈ (skewStabilizer P)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro U hU
    have hUP := (mem_skewStabilizer P U).mp hU
    have hPUt : P.val * (skewMatrix U)ᵀ = 0 := by
      simpa only [transpose_mul, P.property.1, transpose_zero] using congrArg Matrix.transpose hUP
    have hUtP : (skewMatrix U)ᵀ * P.val = 0 := by rw [skewMatrix_transpose, Matrix.neg_mul, hUP, neg_zero]
    have hQUt : Q * (skewMatrix U)ᵀ = (skewMatrix U)ᵀ := by
      rw [show Q = 1 - P.val from rfl, Matrix.sub_mul, Matrix.one_mul, hPUt, sub_zero]
    have hUtQ : (skewMatrix U)ᵀ * Q = (skewMatrix U)ᵀ := by
      rw [show Q = 1 - P.val from rfl, Matrix.mul_sub, Matrix.mul_one, hUtP, sub_zero]
    rw [skewMatrix_inner, map_sub, Matrix.mul_sub, Matrix.trace_sub,
      show skewMatrix C = Q * skewMatrix L * Q from rfl]
    have hTrace : ((skewMatrix U)ᵀ * (Q * skewMatrix L * Q)).trace =
        ((skewMatrix U)ᵀ * skewMatrix L).trace := by
      calc
        _ = ((((skewMatrix U)ᵀ * Q) * skewMatrix L) * Q).trace := by simp only [Matrix.mul_assoc]
        _ = ((Q * ((skewMatrix U)ᵀ * Q)) * skewMatrix L).trace := by
          rw [trace_mul_comm, ← Matrix.mul_assoc]
        _ = _ := by rw [hUtQ, hQUt]
    rw [hTrace, sub_self]
  rw [Submodule.eq_starProjection_of_mem_orthogonal hC hOrth]
  rfl

/-- The projected gradient direction is obtained by removing the skew
block supported in the orthogonal complement of the sketch. -/
theorem skewMatrix_starProjection_complement (P : OrthogonalProjector n l) (L : SkewFrobenius n) :
    skewMatrix ((skewStabilizer P)ᗮ.starProjection L) =
      skewMatrix L - (1 - P.val) * skewMatrix L * (1 - P.val) := by
  rw [Submodule.starProjection_orthogonal_val, map_sub, skewMatrix_starProjection_stabilizer]

/-- The exact admissibility inequality in the Frobenius inner product,
now expressed through actual orthogonal projections onto Lie subspaces. -/
theorem skewStabilizerComplement_weighted_le_mixedRanks {m : ℕ} {rank : Fin m → ℕ}
    (P : (i : Fin m) → OrthogonalProjector n (rank i)) (c : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hEnergy : ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (L : SkewFrobenius n) :
    (∑ i, (c i / 2) * ‖((skewStabilizer (P i))ᗮ.starProjection L)‖ ^ 2) ≤ ‖L‖ ^ 2 := by
  simp_rw [skewMatrix_norm_sq, skewMatrix_starProjection_complement]
  exact stabilizerComplement_weighted_le_mixedRanks P c hc hEnergy
    (skewMatrix L) (skewMatrix_transpose L)

/-- The Frobenius projection bound for a family of common rank. -/
theorem skewStabilizerComplement_weighted_le {m : ℕ}
    (P : Fin m → OrthogonalProjector n l) (c : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hEnergy : ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (L : SkewFrobenius n) :
    (∑ i, (c i / 2) * ‖((skewStabilizer (P i))ᗮ.starProjection L)‖ ^ 2) ≤ ‖L‖ ^ 2 :=
  skewStabilizerComplement_weighted_le_mixedRanks (rank := fun _ => l) P c hc hEnergy L

/-- The gradient inequality in the heat calculation requires only the
directional linear functionals. Each vanishes on its pointwise stabilizer,
so its Frobenius Riesz vector lies in the complementary projection space. -/
theorem skewDirectionalResponses_weighted_square_le_mixedRanks {m : ℕ}
    {rank : Fin m → ℕ} {J : Type*} [Fintype J]
    (P : (i : Fin m) → OrthogonalProjector n (rank i)) (c : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hEnergy : ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (b : OrthonormalBasis J ℝ (SkewFrobenius n))
    (D : Fin m → SkewFrobenius n →ₗ[ℝ] ℝ)
    (hD : ∀ i L, skewMatrix L * (P i).val = 0 → D i L = 0) :
    (∑ j, (∑ i, (c i / 2) * D i (b j)) ^ 2) ≤
      ∑ j, ∑ i, (c i / 2) * (D i (b j)) ^ 2 := by
  let g (i : Fin m) : SkewFrobenius n := ∑ j, D i (b j) • b j
  have hRep (i : Fin m) (L : SkewFrobenius n) : inner ℝ L (g i) = D i L := by
    calc
      _ = ∑ j, D i (b j) * inner ℝ L (b j) := by
        simp only [g, inner_sum]
        exact Finset.sum_congr rfl (fun j _ => real_inner_smul_right L (b j) (D i (b j)))
      _ = D i (∑ j, inner ℝ (b j) L • b j) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul, smul_eq_mul, mul_comm (D i (b j)), real_inner_comm]
      _ = _ := by rw [b.sum_repr']
  have hV (i : Fin m) : g i ∈ (skewStabilizer (P i))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro L hL
    exact (hRep i L).trans (hD i L ((mem_skewStabilizer (P i) L).mp hL))
  have h := sum_squared_weighted_coordinates_le (fun i => (skewStabilizer (P i))ᗮ)
    (fun i => c i / 2) g b
    (fun i => div_nonneg (hc i) (by norm_num)) hV
    (skewStabilizerComplement_weighted_le_mixedRanks P c hc hEnergy)
  simp_rw [hRep] at h
  exact h

/-- The weighted directional inequality for a family of common rank. -/
theorem skewDirectionalResponses_weighted_square_le {m : ℕ} {J : Type*} [Fintype J]
    (P : Fin m → OrthogonalProjector n l) (c : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hEnergy : ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (b : OrthonormalBasis J ℝ (SkewFrobenius n))
    (D : Fin m → SkewFrobenius n →ₗ[ℝ] ℝ)
    (hD : ∀ i L, skewMatrix L * (P i).val = 0 → D i L = 0) :
    (∑ j, (∑ i, (c i / 2) * D i (b j)) ^ 2) ≤
      ∑ j, ∑ i, (c i / 2) * (D i (b j)) ^ 2 :=
  skewDirectionalResponses_weighted_square_le_mixedRanks (rank := fun _ => l)
    P c hc hEnergy b D hD

end

end TypicalOrientations
