import SketchOrientation.EdgeWalsh
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Logic.Equiv.Fintype

/-!
# Finite Walsh sampling
The two ordered samples in the signed-permutation model are the restrictions
of independent uniform permutations. We also use the uniform product law on
row and column tuples, in which repeats are permitted.
-/

open Function
open scoped BigOperators

noncomputable section
namespace SketchOrientation.Edge.Walsh

/-- Expectation on the uniform law on a finite sample space. -/
def uniformMean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

def indicator (P : Prop) : ℝ := by classical exact if P then 1 else 0

def uniformProbability {A : Type*} [Fintype A] (P : A → Prop) : ℝ :=
  uniformMean fun a => indicator (P a)

theorem indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  classical
  unfold indicator
  split <;> norm_num

theorem indicator_le_one (P : Prop) : indicator P ≤ 1 := by
  classical
  unfold indicator
  split <;> norm_num

theorem uniformMean_mono {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    uniformMean f ≤ uniformMean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

theorem uniformMean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniformMean, mul_div_cancel_left₀, hc]

theorem uniformMean_sub {A : Type*} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

theorem abs_uniformMean_le {A : Type*} [Fintype A] (f : A → ℝ) :
    |uniformMean f| ≤ uniformMean (fun a => |f a|) := by
  rw [uniformMean, abs_div, abs_of_nonneg (show 0 ≤ (Fintype.card A : ℝ) by positivity)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)

theorem uniformMean_sum {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    uniformMean (fun a => ∑ b, f a b) = ∑ b, uniformMean (fun a => f a b) := by
  simp only [uniformMean, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem uniformMean_prod {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    uniformMean (fun ab : A × B => f ab.1 ab.2) =
      uniformMean (fun a => uniformMean (f a)) := by
  simp [uniformMean, Fintype.sum_prod_type, ← Finset.sum_div, div_div, mul_comm]

theorem uniformMean_prod' {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a, b))) :=
  uniformMean_prod (fun a b => f (a,b))

/-- A map with equally sized nonempty fibers pushes the uniform law forward
to the uniform law. -/
theorem uniformMean_comp {A B : Type*} [Fintype A] [Fintype B]
    (q : A → B) (k : ℕ) (hk : k ≠ 0) (h : ∀ b, Nat.card {a // q a = b} = k)
    (f : B → ℝ) : uniformMean (f ∘ q) = uniformMean f := by
  classical
  let e := Equiv.sigmaFiberEquiv q
  have h' (b : B) : Fintype.card {a // q a = b} = k := by
    simpa only [Nat.card_eq_fintype_card] using h b
  have hcard : Fintype.card A = Fintype.card B * k := by
    rw [← Fintype.card_congr e, Fintype.card_sigma]
    simp [h', Nat.mul_comm]
  have hsum : (∑ a, f (q a)) = (k : ℝ) * ∑ b, f b := by
    rw [← e.sum_comp (fun a => f (q a)), Fintype.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    change (∑ a : {a // q a = b}, f (q a)) = _
    calc
      (∑ a : {a // q a = b}, f (q a)) = ∑ _a : {a // q a = b}, f b :=
        Finset.sum_congr rfl fun a _ => congrArg f a.property
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, h', nsmul_eq_mul]
  simp only [uniformMean, comp_apply, hcard, Nat.cast_mul, hsum]
  rw [mul_comm (Fintype.card B : ℝ), mul_div_mul_left _ _ (by exact_mod_cast hk)]

/-- Fiber sizes of a surjective linear map are equal by translation. -/
theorem uniformMean_linear {R A B : Type*} [Ring R] [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] [Fintype A] [Fintype B] (q : A →ₗ[R] B)
    (hq : Surjective q) (f : B → ℝ) : uniformMean (fun a => f (q a)) = uniformMean f := by
  classical
  apply uniformMean_comp q (Nat.card {a // q a = 0})
  · letI : Nonempty {a // q a = 0} := ⟨⟨0, by simp⟩⟩
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_ne_zero (α := {a // q a = 0})
  · intro b
    obtain ⟨z, hz⟩ := hq b
    apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.addRight (-z)) _)
    intro a
    change (q a = b) ↔ q (a + -z) = 0
    rw [map_add, map_neg, hz, ← sub_eq_add_neg, sub_eq_zero]

theorem uniformMean_equiv {A B : Type*} [Fintype A] [Fintype B] (q : A ≃ B)
    (f : B → ℝ) : uniformMean (fun a => f (q a)) = uniformMean f := by
  unfold uniformMean
  rw [q.sum_comp f, Fintype.card_congr q]

theorem uniformProbability_eq_card {A : Type*} [Fintype A] (P : A → Prop) :
    uniformProbability P = (Nat.card {a // P a} : ℝ) / Fintype.card A := by
  classical
  unfold uniformProbability uniformMean
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [indicator]

theorem uniformProbability_nonneg {A : Type*} [Fintype A] (P : A → Prop) :
    0 ≤ uniformProbability P := by rw [uniformProbability_eq_card]; positivity

theorem uniformProbability_mono {A : Type*} [Fintype A] {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : uniformProbability P ≤ uniformProbability Q := by
  apply uniformMean_mono
  intro a
  by_cases hp : P a
  · simp [indicator, hp, h a hp]
  · simpa [indicator, hp] using indicator_nonneg (Q a)

theorem uniformProbability_exists_le_sum {A I : Type*} [Fintype A] [Fintype I]
    (P : I → A → Prop) :
    uniformProbability (fun a => ∃ i, P i a) ≤ ∑ i, uniformProbability (P i) := by
  classical
  unfold uniformProbability
  rw [← uniformMean_sum]
  apply uniformMean_mono
  intro a
  by_cases h : ∃ i, P i a
  · obtain ⟨i, hi⟩ := h
    rw [show indicator (∃ i, P i a) = indicator (P i a) by simp [indicator, hi, show ∃ i, P i a from ⟨i, hi⟩]]
    exact Finset.single_le_sum (fun j _ => indicator_nonneg (P j a)) (Finset.mem_univ i)
  · simpa [indicator, h] using Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
      indicator_nonneg (P i a))

/-- Conditioning a uniform mean on a nonempty subset changes it by at
most the complementary probability, for observables in the unit interval. -/
theorem abs_uniformMean_sub_conditioned {A : Type*} [Fintype A] (P : A → Prop)
    [DecidablePred P] [Nonempty {a // P a}] (f : A → ℝ)
    (hf₀ : ∀ a, 0 ≤ f a) (hf₁ : ∀ a, f a ≤ 1) :
    |uniformMean (fun a : {a // P a} => f a) - uniformMean f| ≤
      uniformProbability (fun a => ¬P a) := by
  classical
  let G : Type _ := {a : A // P a}
  let H : Type _ := {a : A // ¬P a}
  have hnA : (Fintype.card A : ℝ) ≠ 0 := by
    have : Nonempty A := (inferInstance : Nonempty G).map Subtype.val
    exact_mod_cast Fintype.card_ne_zero
  have hnG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card G : ℝ) + (Fintype.card H : ℝ) = Fintype.card A := by
    simpa [G, H] using Fintype.sum_subtype_add_sum_subtype P (fun _ : A => (1 : ℝ))
  have hs : (∑ a : G, f a) + (∑ a : H, f a) = ∑ a : A, f a :=
    Fintype.sum_subtype_add_sum_subtype P f
  have h₀ : 0 ≤ uniformMean (fun a : G => f a) :=
    div_nonneg (Finset.sum_nonneg fun a _ => hf₀ a) (by positivity)
  have h₁ : uniformMean (fun a : G => f a) ≤ 1 := by
    simpa only [uniformMean_const] using uniformMean_mono (A := G)
      (f := fun a => f a) (g := fun _ => 1) (fun a => hf₁ a)
  have hx₀ : 0 ≤ ∑ a : H, f a := Finset.sum_nonneg fun a _ => hf₀ a
  have hx₁ : (∑ a : H, f a) ≤ Fintype.card H := by
    simpa using Finset.sum_le_sum (g := fun _ : H => (1 : ℝ))
      (fun a (_ : a ∈ Finset.univ) => hf₁ a)
  change |uniformMean (fun a : G => f a) - uniformMean f| ≤ _
  rw [uniformProbability_eq_card, Nat.card_eq_fintype_card]
  have heq : uniformMean (fun a : G => f a) - uniformMean f =
      ((Fintype.card H : ℝ) * uniformMean (fun a : G => f a) - (∑ a : H, f a)) /
        Fintype.card A := by
    unfold uniformMean
    field_simp [hnA, hnG]
    rw [← hc, ← hs]
    ring
  rw [heq, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card A by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  change |(Fintype.card H : ℝ) * uniformMean (fun a : G => f a) - ∑ a : H, f a| ≤
    Fintype.card H
  have hm₀ : 0 ≤ (Fintype.card H : ℝ) * uniformMean (fun a : G => f a) :=
    mul_nonneg (by positivity) h₀
  have hm₁ : (Fintype.card H : ℝ) * uniformMean (fun a : G => f a) ≤ Fintype.card H :=
    mul_le_of_le_one_right (by positivity) h₁
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Restricting a uniform permutation to any prescribed ordered set of
locations gives the uniform law on ordered samples without replacement. -/
theorem uniformMean_perm_restrict {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq A] (e : I ↪ A) (f : (I ↪ A) → ℝ) :
    uniformMean (fun σ : Equiv.Perm A => f (e.trans σ.toEmbedding)) = uniformMean f := by
  classical
  let q (σ : Equiv.Perm A) := e.trans σ.toEmbedding
  apply uniformMean_comp q (Nat.card {σ // q σ = e})
  · letI : Nonempty {σ // q σ = e} := ⟨⟨Equiv.refl A, by ext i; rfl⟩⟩
    simpa [Nat.card_eq_fintype_card] using Fintype.card_ne_zero (α := {σ // q σ = e})
  · intro b
    obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair b e b.injective e.injective
    let t : Equiv.Perm (Equiv.Perm A) :=
      ⟨fun σ => σ.trans τ, fun σ => σ.trans τ.symm, by intro σ; ext x; simp, by intro σ; ext x; simp⟩
    apply Nat.card_congr (Equiv.subtypeEquiv t _)
    intro σ
    constructor
    · intro h
      ext i
      change τ (σ (e i)) = e i
      have hi : σ (e i) = b i := congrArg (fun g : I ↪ A => g i) h
      rw [hi, hτ]
    · intro h
      ext i
      apply τ.injective
      simpa [t, q, hτ] using congrArg (fun g : I ↪ A => g i) h

def embeddingEquivInjective (I A : Type*) :
    (I ↪ A) ≃ {u : I → A // Injective u} where
  toFun f := ⟨f, f.injective⟩
  invFun u := ⟨u, u.2⟩
  left_inv f := by cases f; rfl
  right_inv u := by cases u; rfl

/-- Binary Walsh labels. -/
abbrev Label (m : ℕ) := Fin m → ZMod 2

@[simp] theorem card_label (m : ℕ) : Fintype.card (Label m) = 2 ^ m := by
  simp [Label, Fintype.card_pi]

def parity {m : ℕ} (r c : Label m) : ZMod 2 := ∑ i, r i * c i

/-- Parity zero encodes the sign +1, represented by true. -/
def signBit (b : ZMod 2) : Bool := decide (b = 0)

def signedTable {m s ell : ℕ} (r : Fin s → Label m) (c : Fin ell → Label m)
    (a : Fin s → ZMod 2) (b : Fin ell → ZMod 2) : Fin s → Fin ell → Bool :=
  fun i j => signBit (parity (r i) (c j) + a i + b j)

/-- The relevant ordered locations and fair sign parities in the two
independent uniform signed permutations. -/
abbrev Draw (m s ell : ℕ) :=
  (Fin s ↪ Label m) × (Fin ell ↪ Label m) × (Fin s → ZMod 2) × (Fin ell → ZMod 2)

/-- Uniform labels with replacement, with the same fair signs. -/
abbrev IndependentDraw (m s ell : ℕ) :=
  (Fin s → Label m) × (Fin ell → Label m) × (Fin s → ZMod 2) × (Fin ell → ZMod 2)

def table {m s ell : ℕ} (d : Draw m s ell) : Fin s → Fin ell → Bool :=
  signedTable d.1 d.2.1 d.2.2.1 d.2.2.2

def independentTable {m s ell : ℕ} (d : IndependentDraw m s ell) : Fin s → Fin ell → Bool :=
  signedTable d.1 d.2.1 d.2.2.1 d.2.2.2


theorem abs_uniformMean_sub_le {A : Type*} [Fintype A] {f g h : A → ℝ}
    (hle : ∀ a, |f a - g a| ≤ h a) :
    |uniformMean f - uniformMean g| ≤ uniformMean h := by
  rw [← uniformMean_sub]
  exact (abs_uniformMean_le _).trans (uniformMean_mono hle)

theorem uniformMean_comm {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    uniformMean (fun a => uniformMean (fun b => f a b)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) := by
  rw [← uniformMean_prod, ← uniformMean_prod]
  exact uniformMean_equiv (Equiv.prodComm _ _) (fun ba => f ba.2 ba.1)

theorem uniformMean_nonneg {A : Type*} [Fintype A] {f : A → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ uniformMean f :=
  div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

theorem uniformMean_le_one {A : Type*} [Fintype A] [Nonempty A] {f : A → ℝ}
    (h : ∀ a, f a ≤ 1) : uniformMean f ≤ 1 := by
  simpa only [uniformMean_const] using uniformMean_mono (g := fun _ => 1) h

theorem abs_uniformMean_embedding_sub {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    [Nonempty (I ↪ A)] (f : (I → A) → ℝ) (hf₀ : ∀ a, 0 ≤ f a) (hf₁ : ∀ a, f a ≤ 1) :
    |uniformMean (fun u : I ↪ A => f u) - uniformMean f| ≤
      uniformProbability (fun u : I → A => ¬Injective u) := by
  classical
  let e := embeddingEquivInjective I A
  letI : Nonempty {u : I → A // Injective u} := (inferInstance : Nonempty (I ↪ A)).map e
  change |uniformMean (fun u : I ↪ A => (fun t : {u : I → A // Injective u} => f t) (e u)) -
    uniformMean f| ≤ _
  rw [uniformMean_equiv e (fun t : {u : I → A // Injective u} => f t)]
  exact abs_uniformMean_sub_conditioned _ _ hf₀ hf₁

/-- A two-coordinate equality has probability one over the number of labels. -/
private theorem uniformProbability_eq_coords {m k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    uniformProbability (fun u : Fin k → Label m => u i = u j) = 1 / (2 : ℝ)^m := by
  let q : (Fin k → Label m) →ₗ[ZMod 2] Label m :=
    LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin k => Label m) i - LinearMap.proj j
  have hq : Surjective q := by
    intro y
    refine ⟨Pi.single i y, ?_⟩
    simp [q, Pi.single_eq_of_ne hij.symm]
  have hiff (u : Fin k → Label m) : (u i = u j) ↔ q u = 0 := by simp [q, sub_eq_zero]
  have heq : (fun u : Fin k → Label m => u i = u j) = (fun u => q u = 0) :=
    funext fun u => propext (hiff u)
  rw [heq]
  change uniformMean (fun u => (fun y : Label m => indicator (y = 0)) (q u)) = _
  rw [uniformMean_linear q hq (fun y : Label m => indicator (y = 0))]
  change uniformProbability (fun y : Label m => y = 0) = _
  rw [uniformProbability_eq_card]
  simp

/-- Collision probability for the sample with replacement. -/
theorem probability_collision_le (m k : ℕ) :
    uniformProbability (fun u : Fin k → Label m => ¬Injective u) ≤
      (k : ℝ)^2 / (2 : ℝ)^m := by
  classical
  let A := {ij : Fin k × Fin k // ij.1 ≠ ij.2}
  have hcover (u : Fin k → Label m) (hu : ¬Injective u) : ∃ ij : A, u ij.1.1 = u ij.1.2 := by
    rw [Injective] at hu
    push Not at hu
    obtain ⟨i, j, he, hn⟩ := hu
    exact ⟨⟨(i,j), hn⟩, he⟩
  calc
    _ ≤ uniformProbability (fun u : Fin k → Label m => ∃ ij : A, u ij.1.1 = u ij.1.2) :=
      uniformProbability_mono hcover
    _ ≤ ∑ ij : A, uniformProbability (fun u : Fin k → Label m => u ij.1.1 = u ij.1.2) :=
      uniformProbability_exists_le_sum _
    _ = (Fintype.card A : ℝ) / (2 : ℝ)^m := by
      simp_rw [fun ij : A => uniformProbability_eq_coords (m := m) ij.2]
      simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := Fintype.card_le_of_injective (Subtype.val : A → Fin k × Fin k) Subtype.val_injective
      have h' : Fintype.card A ≤ k^2 := by simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using h
      exact_mod_cast h'

end SketchOrientation.Edge.Walsh
