import SketchOrientation.WalshSampling
import Mathlib.Data.Matrix.Mul

/-!
# Signed permutations and the Walsh table
The full signed-permutation draw induces the law on sampled support rows,
output columns, and sign parities used in the finite table argument.
-/

open Function
open scoped BigOperators

noncomputable section
namespace SketchOrientation.Edge.Walsh

abbrev SignedPermDraw (m : ℕ) :=
  Equiv.Perm (Label m) × Equiv.Perm (Label m) × (Label m → ZMod 2) × (Label m → ZMod 2)

/-- The signs on the left are indexed by the target's coordinates and the signs
on the right are indexed by the prescribed output coordinates. -/
def restrictSignedPerm {m s ell : ℕ} (rows : Fin s ↪ Label m) (cols : Fin ell ↪ Label m)
    (d : SignedPermDraw m) : Draw m s ell :=
  (rows.trans d.1.toEmbedding, cols.trans d.2.1.toEmbedding,
    fun i => d.2.2.1 (rows i), fun j => d.2.2.2 (cols j))

private theorem uniformMean_sign_restrict {k m : ℕ} (e : Fin k ↪ Label m)
    (f : (Fin k → ZMod 2) → ℝ) :
    uniformMean (fun z : Label m → ZMod 2 => f (fun i => z (e i))) = uniformMean f := by
  let q : (Label m → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    LinearMap.pi (fun i => LinearMap.proj (e i))
  have hq : Surjective q := by
    intro w
    exact ⟨Function.extend e w 0, funext fun i => e.injective.extend_apply w 0 i⟩
  exact uniformMean_linear q hq f

/-- The law on restricted draws is obtained from independent uniform signed
permutations, for any fixed support and output coordinates. -/
theorem uniformMean_restrictSignedPerm {m s ell : ℕ}
    (rows : Fin s ↪ Label m) (cols : Fin ell ↪ Label m) (f : Draw m s ell → ℝ) :
    uniformMean (fun d => f (restrictSignedPerm rows cols d)) = uniformMean f := by
  simp only [SignedPermDraw, Draw, uniformMean_prod', restrictSignedPerm]
  have hb (r : Fin s ↪ Label m) (c : Fin ell ↪ Label m) (a : Fin s → ZMod 2) :=
    uniformMean_sign_restrict cols (fun b => f (r, c, a, b))
  have ha (r : Fin s ↪ Label m) (c : Fin ell ↪ Label m) :=
    uniformMean_sign_restrict rows (fun a => uniformMean (fun b => f (r, c, a, b)))
  have hc (r : Fin s ↪ Label m) :=
    uniformMean_perm_restrict cols (fun c => uniformMean (fun a =>
      uniformMean (fun b => f (r, c, a, b))))
  have hr := uniformMean_perm_restrict rows (fun r => uniformMean (fun c =>
    uniformMean (fun a => uniformMean (fun b => f (r, c, a, b)))))
  simp_rw [hb, ha, hc, hr]

def signValue (b : ZMod 2) : ℝ :=
  if signBit b then 1 else -1

theorem signValue_add (a b : ZMod 2) : signValue (a + b) = signValue a * signValue b := by
  have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases h a with h0 | h1 <;> rcases h b with h0' | h1' <;> subst a <;> subst b <;>
    norm_num [signValue, signBit, h11] <;> decide

/-- Normalized Walsh matrix indexed by binary vectors. -/
def core (m : ℕ) : Matrix (Label m) (Label m) ℝ :=
  fun r c => (Real.sqrt ((2 : ℝ)^m))⁻¹ * signValue (parity r c)

/-- The left signed permutation reads Walsh row σ(i) at target coordinate i. -/
def leftSignedMatrix {m : ℕ} (σ : Equiv.Perm (Label m)) (z : Label m → ZMod 2) :
    Matrix (Label m) (Label m) ℝ :=
  fun i r => if r = σ i then signValue (z i) else 0

/-- The right signed permutation sends output coordinate j to σ(j). -/
def rightSignedMatrix {m : ℕ} (σ : Equiv.Perm (Label m)) (z : Label m → ZMod 2) :
    Matrix (Label m) (Label m) ℝ :=
  fun c j => if c = σ j then signValue (z j) else 0

/-- The prescribed columns of the signed Walsh transform. -/
def signedMatrix {m ell : ℕ} (cols : Fin ell ↪ Label m) (d : SignedPermDraw m) :
    Matrix (Label m) (Fin ell) ℝ :=
  fun i j => (leftSignedMatrix d.1 d.2.2.1 * core m *
    rightSignedMatrix d.2.1 d.2.2.2) i (cols j)

theorem signedMatrix_entry {m s ell : ℕ} (rows : Fin s ↪ Label m)
    (cols : Fin ell ↪ Label m) (d : SignedPermDraw m) (i : Fin s) (j : Fin ell) :
    signedMatrix cols d (rows i) j =
      (Real.sqrt ((2 : ℝ)^m))⁻¹ * (if table (restrictSignedPerm rows cols d) i j then 1 else -1) := by
  classical
  unfold signedMatrix
  simp only [Matrix.mul_apply, leftSignedMatrix, rightSignedMatrix, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [core, table, signedTable, restrictSignedPerm, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply]
  rw [← mul_ite]
  change signValue (d.2.2.1 (rows i)) * ((Real.sqrt ((2 : ℝ)^m))⁻¹ *
    signValue (parity (d.1 (rows i)) (d.2.1 (cols j)))) * signValue (d.2.2.2 (cols j)) =
      (Real.sqrt ((2 : ℝ)^m))⁻¹ * signValue
        (parity (d.1 (rows i)) (d.2.1 (cols j)) + d.2.2.1 (rows i) + d.2.2.2 (cols j))
  simp only [signValue_add]
  ring

/-- Projection of the deterministic equal-amplitude target, evaluated in
support coordinates. -/
def normalizedProjection {m s ell : ℕ} (rows : Fin s ↪ Label m)
    (cols : Fin ell ↪ Label m) (d : SignedPermDraw m) (j : Fin ell) : ℝ :=
  Real.sqrt ((2 : ℝ)^m) * ∑ i : Fin s, (Real.sqrt (s : ℝ))⁻¹ * signedMatrix cols d (rows i) j

theorem normalizedProjection_eq_signSum {m s ell : ℕ} (rows : Fin s ↪ Label m)
    (cols : Fin ell ↪ Label m) (d : SignedPermDraw m) (j : Fin ell) :
    normalizedProjection rows cols d j =
      (walshSignSum (table (restrictSignedPerm rows cols d)) j : ℝ) / Real.sqrt s := by
  unfold normalizedProjection
  have hn : Real.sqrt ((2 : ℝ)^m) ≠ 0 := by positivity
  simp_rw [signedMatrix_entry rows]
  unfold walshSignSum
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : table (restrictSignedPerm rows cols d) i j <;>
    simp [h, field]

theorem projectionEnergy_eq_tableEnergy {m s ell : ℕ} (rows : Fin s ↪ Label m)
    (cols : Fin ell ↪ Label m) (d : SignedPermDraw m) :
    (∑ j, (normalizedProjection rows cols d j)^2) =
      walshTableEnergy (table (restrictSignedPerm rows cols d)) := by
  simp_rw [normalizedProjection_eq_signSum, walshTableEnergy_eq_normSq]


theorem signedMatrix_apply {m ell : ℕ} (cols : Fin ell ↪ Label m)
    (d : SignedPermDraw m) (x : Label m) (j : Fin ell) :
    signedMatrix cols d x j =
      (Real.sqrt ((2 : ℝ)^m))⁻¹ * signValue (d.2.2.1 x) *
        signValue (parity (d.1 x) (d.2.1 (cols j))) * signValue (d.2.2.2 (cols j)) := by
  classical
  unfold signedMatrix
  simp only [Matrix.mul_apply, leftSignedMatrix, rightSignedMatrix, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, core]
  ring

end SketchOrientation.Edge.Walsh
