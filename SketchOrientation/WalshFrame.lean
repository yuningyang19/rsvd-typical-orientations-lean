import SketchOrientation.WalshSignedPerm
import Mathlib.Data.Matrix.Basic

/-!
# Orthonormal Walsh frames and equal-amplitude unit targets
-/

open Function Matrix
open scoped BigOperators

noncomputable section
namespace SketchOrientation.Edge.Walsh

@[simp] theorem signValue_zero : signValue 0 = 1 := by norm_num [signValue, signBit]
@[simp] theorem signValue_one : signValue 1 = -1 := by norm_num [signValue, signBit]

@[simp] theorem signValue_sq (b : ZMod 2) : signValue b ^ 2 = 1 := by
  have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h b with rfl | rfl <;> norm_num

private theorem parity_add_left {m : ℕ} (x y v : Label m) :
    parity (x + y) v = parity x v + parity y v := by
  simp [parity, add_mul, Finset.sum_add_distrib]

private theorem parity_add_right {m : ℕ} (x y v : Label m) :
    parity v (x + y) = parity v x + parity v y := by
  simp [parity, mul_add, Finset.sum_add_distrib]

private theorem sum_signValue_parity_of_ne_zero {m : ℕ} (v : Label m) (hv : v ≠ 0) :
    (∑ x : Label m, signValue (parity x v)) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hi' : v i = 1 := (h (v i)).resolve_left hi
  let e : Label m := Pi.single i 1
  have he : parity e v = 1 := by
    unfold parity
    rw [Finset.sum_eq_single i]
    · simp [e, hi']
    · intro j _ hj
      simp [e, Pi.single_eq_of_ne hj]
    · simp
  have hh := Equiv.sum_comp (Equiv.addRight e) (fun x => signValue (parity x v))
  change (∑ x, signValue (parity (x + e) v)) = _ at hh
  simp_rw [parity_add_left, he, signValue_add, signValue_one, mul_neg_one, Finset.sum_neg_distrib] at hh
  linarith

theorem sum_signValue_parity_mul {m : ℕ} (a b : Label m) :
    (∑ x : Label m, signValue (parity x a) * signValue (parity x b)) =
      if a = b then (2 : ℝ)^m else 0 := by
  classical
  simp_rw [← signValue_add, ← parity_add_right]
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  have hadd (x : Label m) : x + x = 0 := funext fun i => h (x i)
  by_cases hab : a = b
  · rw [hab, hadd]
    simp [parity]
  · rw [if_neg hab]
    apply sum_signValue_parity_of_ne_zero
    intro hz
    apply hab
    calc
      a = a + (b + b) := by rw [hadd, add_zero]
      _ = b := by rw [← add_assoc, hz, zero_add]

/-- The sampled columns of the signed Walsh transform are orthonormal. -/
theorem signedMatrix_orthonormal {m ell : ℕ} (cols : Fin ell ↪ Label m)
    (d : SignedPermDraw m) :
    (signedMatrix cols d)ᵀ * signedMatrix cols d = 1 := by
  classical
  ext i j
  let c := ((Real.sqrt ((2 : ℝ)^m))⁻¹)^2
  let bi := signValue (d.2.2.2 (cols i))
  let bj := signValue (d.2.2.2 (cols j))
  let v₁ := d.2.1 (cols i)
  let v₂ := d.2.1 (cols j)
  have hp (x : Label m) :
      signedMatrix cols d x i * signedMatrix cols d x j =
        c * (bi * bj) *
          (signValue (parity (d.1 x) v₁) * signValue (parity (d.1 x) v₂)) := by
    rw [signedMatrix_apply, signedMatrix_apply]
    dsimp [c, bi, bj, v₁, v₂]
    have hh := signValue_sq (d.2.2.1 x)
    linear_combination ((Real.sqrt ((2 : ℝ)^m))⁻¹)^2 * signValue (d.2.2.2 (cols i)) *
      signValue (d.2.2.2 (cols j)) * signValue (parity (d.1 x) (d.2.1 (cols i))) *
      signValue (parity (d.1 x) (d.2.1 (cols j))) * hh
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hp, ← Finset.mul_sum]
  rw [Equiv.sum_comp d.1 (fun x => signValue (parity x v₁) * signValue (parity x v₂)),
    sum_signValue_parity_mul]
  have hv : v₁ = v₂ ↔ i = j := ⟨fun h => cols.injective (d.2.1.injective h), fun h => congrArg (fun k => d.2.1 (cols k)) h⟩
  by_cases hij : i = j
  · simp only [Matrix.one_apply, hij, hv.mpr hij, if_true]
    have hbi : bi * bj = 1 := by
      dsimp [bi, bj]
      rw [← hij, ← sq, signValue_sq]
    have hc : c * (2 : ℝ)^m = 1 := by
      unfold c
      rw [inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
    rw [hbi, mul_one, hc]
  · simp [Matrix.one_apply, hij, mt hv.mp hij]

/-- The actual target vector is constant on the prescribed support and zero elsewhere. -/
def supportTarget {m s : ℕ} (rows : Fin s ↪ Label m) (x : Label m) : ℝ := by
  classical
  exact if x ∈ Set.range rows then (Real.sqrt (s : ℝ))⁻¹ else 0

private theorem sum_over_support {m s : ℕ} (rows : Fin s ↪ Label m) (f : Label m → ℝ) :
    (∑ x : Label m, if x ∈ (Finset.univ.map rows : Finset (Label m)) then f x else 0) =
      ∑ i : Fin s, f (rows i) := by
  classical
  rw [← Finset.sum_filter, show Finset.univ.filter (fun x => x ∈ Finset.univ.map rows) =
      Finset.univ.map rows by ext x; simp, Finset.sum_map]

private theorem mem_map_iff_range {m s : ℕ} (rows : Fin s ↪ Label m) (x : Label m) :
    x ∈ Finset.univ.map rows ↔ x ∈ Set.range rows := by simp [Set.mem_range]

theorem supportTarget_unit {m s : ℕ} (rows : Fin s ↪ Label m) (hs : 0 < s) :
    (∑ x, supportTarget rows x ^ 2) = 1 := by
  classical
  simp_rw [supportTarget, ← mem_map_iff_range, apply_ite (fun y : ℝ => y ^ 2),
    zero_pow (by decide : 2 ≠ 0)]
  rw [sum_over_support, inv_pow, Real.sq_sqrt (by positivity)]
  simpa using mul_inv_cancel₀ (show (s : ℝ) ≠ 0 by positivity)

theorem normalizedProjection_eq_supportTarget {m s ell : ℕ} (rows : Fin s ↪ Label m)
    (cols : Fin ell ↪ Label m) (d : SignedPermDraw m) (j : Fin ell) :
    normalizedProjection rows cols d j =
      Real.sqrt ((2 : ℝ)^m) * ∑ x : Label m, supportTarget rows x * signedMatrix cols d x j := by
  classical
  unfold normalizedProjection
  simp_rw [supportTarget, ← mem_map_iff_range, ite_mul, zero_mul]
  rw [sum_over_support]

end SketchOrientation.Edge.Walsh
