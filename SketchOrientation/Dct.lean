import SketchOrientation.Arithmetic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace SketchOrientation

open Matrix BigOperators

private noncomputable def midpointCos (n : ℕ) (d : ℤ) (i : ℕ) : ℝ :=
  Real.cos ((d : ℝ) * Real.pi / (n : ℝ) * ((i : ℝ) + 1 / 2))

private theorem sum_midpointCos_zero {n : ℕ} (hn : 0 < n) {d : ℤ}
    (hd : d ≠ 0) (hlo : -(2 * (n : ℤ)) < d) (hhi : d < 2 * (n : ℤ)) :
    ∑ i : Fin n, midpointCos n d i.val = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hlo' : -(2 * (n : ℝ)) < (d : ℝ) := by exact_mod_cast hlo
  have hhi' : (d : ℝ) < 2 * (n : ℝ) := by exact_mod_cast hhi
  let a := (d : ℝ) * Real.pi / (n : ℝ)
  have hlo'' : -Real.pi < a / 2 := by
    dsimp [a]
    rw [div_div, lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hhi'' : a / 2 < Real.pi := by
    dsimp [a]
    rw [div_div, div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (a / 2) ≠ 0 := by
    rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt hlo'' hhi'']
    dsimp [a]
    exact div_ne_zero (div_ne_zero (mul_ne_zero hd' Real.pi_ne_zero) hn'.ne') two_ne_zero
  have hsum :
      (∑ i : Fin n, midpointCos n d i.val) =
        ∑ i ∈ Finset.range n, Real.cos (a * (i : ℝ) + a / 2) := by
    simp only [midpointCos, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    dsimp [a]
    ring
  apply (mul_eq_zero.mp ?_).resolve_left hsin
  rw [hsum, Real.sin_mul_sum_cos]
  have hphase : ((n : ℝ) - 1) * a / 2 + a / 2 = (n : ℝ) * a / 2 := by ring
  rw [hphase]
  have hphase' : 2 * ((n : ℝ) * a / 2) = (d : ℝ) * Real.pi := by
    dsimp [a]
    field_simp
  have hdouble := Real.sin_two_mul ((n : ℝ) * a / 2)
  rw [hphase', Real.sin_int_mul_pi] at hdouble
  linarith

private theorem sum_midpointCos (n : ℕ) (hn : 0 < n) (d : ℤ)
    (hlo : -(2 * (n : ℤ)) < d) (hhi : d < 2 * (n : ℤ)) :
    ∑ i : Fin n, midpointCos n d i.val = if d = 0 then (n : ℝ) else 0 := by
  split_ifs with hd
  · simp [hd, midpointCos]
  · exact sum_midpointCos_zero hn hd hlo hhi

private noncomputable def dctScale (n : ℕ) (j : Fin n) : ℝ :=
  (if j.val = 0 then 1 else Real.sqrt 2) / Real.sqrt (n : ℝ)

private theorem cosineCore_entry {n : ℕ} (i j : Fin n) :
    cosineCore n i j = dctScale n j * midpointCos n (j.val : ℤ) i.val := by
  unfold cosineCore midpointCos dctScale
  congr 2
  push_cast
  ring

/-- The normalized cosine columns of the paper form an orthonormal basis. -/
theorem cosineCore_transpose_mul (n : ℕ) : (cosineCore n)ᵀ * cosineCore n = 1 := by
  ext j k
  have hn : 0 < n := j.pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn').ne'
  have hroot_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
  have hdiff := sum_midpointCos n hn ((j.val : ℤ) - k.val) (by omega) (by omega)
  have hsum := sum_midpointCos n hn ((j.val : ℤ) + k.val) (by omega) (by omega)
  rw [Matrix.mul_apply]
  simp only [transpose_apply, cosineCore_entry]
  have hprod :
      (∑ i : Fin n, (dctScale n j * midpointCos n (j.val : ℤ) i.val) *
        (dctScale n k * midpointCos n (k.val : ℤ) i.val)) =
      (dctScale n j * dctScale n k / 2) *
        ((∑ i : Fin n, midpointCos n ((j.val : ℤ) - k.val) i.val) +
          ∑ i : Fin n, midpointCos n ((j.val : ℤ) + k.val) i.val) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [midpointCos, Int.cast_sub, Int.cast_add, Int.cast_natCast]
    rw [show (((j.val : ℝ) - (k.val : ℝ)) * Real.pi / (n : ℝ) * ((i.val : ℝ) + 1 / 2)) =
          (j.val : ℝ) * Real.pi / (n : ℝ) * ((i.val : ℝ) + 1 / 2) -
          (k.val : ℝ) * Real.pi / (n : ℝ) * ((i.val : ℝ) + 1 / 2) by ring,
      show (((j.val : ℝ) + (k.val : ℝ)) * Real.pi / (n : ℝ) * ((i.val : ℝ) + 1 / 2)) =
          (j.val : ℝ) * Real.pi / (n : ℝ) * ((i.val : ℝ) + 1 / 2) +
          (k.val : ℝ) * Real.pi / (n : ℝ) * ((i.val : ℝ) + 1 / 2) by ring,
      ← Real.two_mul_cos_mul_cos]
    ring
  rw [hprod, hdiff, hsum, Matrix.one_apply]
  by_cases hjk : j = k
  · subst k
    by_cases hj : j.val = 0
    · simp [dctScale, hj]
      field_simp
      nlinarith
    · have hpos : (j.val : ℤ) + j.val ≠ 0 := by omega
      simp only [sub_self, if_true, hpos, if_false, add_zero, dctScale, hj]
      have h2 := Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)
      field_simp
      nlinarith
  · have hne : (j.val : ℤ) - k.val ≠ 0 := by
      have := mt (Fin.val_eq_val j k).mp hjk
      omega
    have hne' : (j.val : ℤ) + k.val ≠ 0 := by omega
    simp [hne, hne', hjk]

/-- Orthogonality in the other order follows because the matrix is square. -/
theorem cosineCore_mul_transpose (n : ℕ) : cosineCore n * (cosineCore n)ᵀ = 1 :=
  mul_eq_one_comm.mp (cosineCore_transpose_mul n)

end SketchOrientation
