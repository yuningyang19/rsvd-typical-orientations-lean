import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace TypicalOrientations

open scoped InnerProductSpace

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The weighted projection inequality says that the map sending x to
the weighted orthogonal projections is a contraction. Its adjoint,
which sums weighted vectors in their respective subspaces, is also a
contraction. The proof is the weighted Cauchy–Schwarz calculation. -/
theorem squaredNorm_weighted_sum_of_projected_vectors [FiniteDimensional ℝ E]
    (S : I → Submodule ℝ E) (d : I → ℝ) (g : I → E)
    (hd : ∀ i, 0 ≤ d i) (hg : ∀ i, g i ∈ S i)
    (hProjection : ∀ x : E, (∑ i, d i * ‖(S i).starProjection x‖ ^ 2) ≤ ‖x‖ ^ 2) :
    ‖∑ i, d i • g i‖ ^ 2 ≤ ∑ i, d i * ‖g i‖ ^ 2 := by
  let x := ∑ i, d i • g i
  let a (i : I) := Real.sqrt (d i) * ‖g i‖
  let b (i : I) := Real.sqrt (d i) * ‖(S i).starProjection x‖
  have hInner (i : I) :
      inner ℝ (g i) x = inner ℝ (g i) ((S i).starProjection x) := by
    have h := (S i).starProjection_inner_eq_zero x (g i) (hg i)
    rw [inner_sub_left, sub_eq_zero] at h
    calc
      _ = inner ℝ x (g i) := real_inner_comm _ _
      _ = inner ℝ ((S i).starProjection x) (g i) := h
      _ = _ := real_inner_comm _ _
  have hTerm (i : I) : a i * b i = d i * (‖g i‖ * ‖(S i).starProjection x‖) := by
    dsimp [a, b]
    rw [show Real.sqrt (d i) * ‖g i‖ * (Real.sqrt (d i) * ‖(S i).starProjection x‖) =
      (Real.sqrt (d i)) ^ 2 * (‖g i‖ * ‖(S i).starProjection x‖) by ring,
      Real.sq_sqrt (hd i)]
  have hA (i : I) : a i ^ 2 = d i * ‖g i‖ ^ 2 := by
    simp only [a, mul_pow, Real.sq_sqrt (hd i)]
  have hB (i : I) : b i ^ 2 = d i * ‖(S i).starProjection x‖ ^ 2 := by
    simp only [b, mul_pow, Real.sq_sqrt (hd i)]
  have hBound : ‖x‖ ^ 2 ≤ ∑ i, a i * b i := by
    calc
      _ = inner ℝ x x := (real_inner_self_eq_norm_sq _).symm
      _ = ∑ i, d i * inner ℝ (g i) x := by
        unfold x
        rw [sum_inner]
        simp only [real_inner_smul_left]
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
        rw [hInner i, hTerm i]
        exact mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (hd i)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simp_rw [hA, hB] at hCS
  let R := ∑ i, d i * ‖g i‖ ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sq_nonneg _)
  have hFinal : (‖x‖ ^ 2) ^ 2 ≤ R * ‖x‖ ^ 2 :=
    (pow_le_pow_left₀ (sq_nonneg _) hBound 2).trans
      (hCS.trans (mul_le_mul_of_nonneg_left (hProjection x) hR))
  change ‖x‖ ^ 2 ≤ R
  by_cases hx : ‖x‖ = 0
  · simpa only [hx, zero_pow (by decide : 2 ≠ 0)] using hR
  · exact le_of_mul_le_mul_right (by simpa only [pow_two] using hFinal)
      (sq_pos_of_ne_zero hx)

variable {J F : Type*} [Fintype J] [AddCommMonoid F] [Module ℝ F]

/-- The sum of diagonal values of a real bilinear map is invariant under
orthonormal change of basis, with no scalar restriction on its target. -/
theorem sum_bilinear_diagonal_orthonormalBasis (q : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (a : OrthonormalBasis I ℝ E) (b : OrthonormalBasis J ℝ E) :
    (∑ j, q (b j) (b j)) = ∑ i, q (a i) (a i) := by
  classical
  calc
    _ = ∑ j, ∑ i, a.repr (b j) i • q (a i) (b j) := by
      apply Finset.sum_congr rfl
      intro j _
      nth_rw 1 [← a.sum_repr (b j)]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
    _ = ∑ i, ∑ j, b.repr (a i) j • q (a i) (b j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [a.repr_apply_apply, b.repr_apply_apply, real_inner_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hTerm (j : J) : b.repr (a i) j • q (a i) (b j) =
          q (a i) (b.repr (a i) j • b j) := (map_smul (q (a i)) _ _).symm
      simp_rw [hTerm]
      rw [← map_sum, b.sum_repr]


/-- The weighted inequality in coordinates of an orthonormal basis. -/
theorem sum_squared_weighted_coordinates_le [FiniteDimensional ℝ E]
    (S : I → Submodule ℝ E) (d : I → ℝ) (g : I → E) (b : OrthonormalBasis J ℝ E)
    (hd : ∀ i, 0 ≤ d i) (hg : ∀ i, g i ∈ S i)
    (hProjection : ∀ x : E, (∑ i, d i * ‖(S i).starProjection x‖ ^ 2) ≤ ‖x‖ ^ 2) :
    (∑ j, (∑ i, d i * inner ℝ (b j) (g i))^2) ≤
      ∑ j, ∑ i, d i * (inner ℝ (b j) (g i))^2 := by
  have hL : (∑ j, (∑ i, d i * inner ℝ (b j) (g i))^2) = ‖∑ i, d i • g i‖ ^ 2 := by
    rw [← b.sum_sq_inner_right]
    apply Finset.sum_congr rfl
    intro j _
    simp only [inner_sum, real_inner_smul_right]
  have hR : (∑ j, ∑ i, d i * (inner ℝ (b j) (g i))^2) = ∑ i, d i * ‖g i‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, b.sum_sq_inner_right]
  rw [hL, hR]
  exact squaredNorm_weighted_sum_of_projected_vectors S d g hd hg hProjection

/-- The basis-invariance rewrite for an orthonormal basis transported by an
isometric linear automorphism. -/
theorem sum_bilinear_diagonal_linearIsometryEquiv
    (q : E →ₗ[ℝ] E →ₗ[ℝ] F) (a : OrthonormalBasis I ℝ E) (e : E ≃ₗᵢ[ℝ] E) :
    (∑ i, q (e (a i)) (e (a i))) = ∑ i, q (a i) (a i) := by
  simpa only [OrthonormalBasis.map_apply] using
    sum_bilinear_diagonal_orthonormalBasis q a (a.map e)

end TypicalOrientations
