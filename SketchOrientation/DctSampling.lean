import SketchOrientation.WalshSampling
import Mathlib.Data.Fintype.CardEmbedding

namespace SketchOrientation

open Edge.Walsh

/-- Subsampling ordered positions of a uniform injection preserves the
uniform law on ordered injections of the smaller width. -/
theorem uniformMean_orderedSample_restrict {I A B : Type*}
    [Fintype I] [Fintype A] [Fintype B] [DecidableEq B]
    (e : A ↪ B) (r : I ↪ A) (f : (I ↪ B) → ℝ) :
    uniformMean (fun s : A ↪ B => f (r.trans s)) = uniformMean f := by
  calc
    _ = uniformMean (fun σ : Equiv.Perm B => f (r.trans (e.trans σ.toEmbedding))) :=
      (uniformMean_perm_restrict e (fun s => f (r.trans s))).symm
    _ = _ := uniformMean_perm_restrict (r.trans e) f

private def oneEmbeddingEquiv (A : Type*) : (Fin 1 ↪ A) ≃ A where
  toFun j := j 0
  invFun a := ⟨fun _ => a, fun {_ _} _ => Subsingleton.elim _ _⟩
  left_inv j := by ext a; fin_cases a; rfl
  right_inv _ := rfl

/-- A single position of the ordered sample is uniform. -/
theorem uniformMean_orderedSample_apply {n l : ℕ} (h : l ≤ n) (j : Fin l)
    (f : Fin n → ℝ) :
    uniformMean (fun s : Fin l ↪ Fin n => f (s j)) = uniformMean f := by
  let j₀ := (oneEmbeddingEquiv (Fin l)).symm j
  calc
    _ = uniformMean (fun s : Fin 1 ↪ Fin n => f (s 0)) :=
      uniformMean_orderedSample_restrict (Fin.castLEEmb h) j₀ (fun s => f (s 0))
    _ = _ := uniformMean_equiv (oneEmbeddingEquiv (Fin n)) f

private def twoEmbedding {A : Type*} (a b : A) (hab : a ≠ b) : Fin 2 ↪ A :=
  ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

private noncomputable def twoEmbeddingEquiv (A : Type*) [DecidableEq A] [Fintype A] :
    (Fin 2 ↪ A) ≃ {p : A × A // p ∈ (Finset.univ : Finset A).offDiag} where
  toFun j := ⟨(j 0, j 1), by simp [j.injective.ne (by decide : (0 : Fin 2) ≠ 1)]⟩
  invFun p := twoEmbedding p.val.1 p.val.2 ((Finset.mem_offDiag.mp p.property).2.2)
  left_inv j := by ext i; fin_cases i <;> rfl
  right_inv p := by apply Subtype.ext; rfl

set_option maxHeartbeats 650000 in
/-- Two distinct positions of the sample are uniform on ordered pairs of
distinct population elements. -/
theorem uniformMean_orderedSample_pair {n l : ℕ} (h : l ≤ n)
    (i j : Fin l) (hij : i ≠ j) (f : Fin n → Fin n → ℝ) :
    uniformMean (fun s : Fin l ↪ Fin n => f (s i) (s j)) =
      (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, f p.1 p.2) /
        ((n : ℝ) * (n - 1)) := by
  classical
  let r := twoEmbedding i j hij
  calc
    _ = uniformMean (fun s : Fin 2 ↪ Fin n => f (s 0) (s 1)) :=
      uniformMean_orderedSample_restrict (Fin.castLEEmb h) r (fun s => f (s 0) (s 1))
    _ = uniformMean (fun p : {p : Fin n × Fin n //
          p ∈ (Finset.univ : Finset (Fin n)).offDiag} => f p.val.1 p.val.2) :=
      uniformMean_equiv (twoEmbeddingEquiv (Fin n)) (fun p => f p.val.1 p.val.2)
    _ = _ := by
      have hn : 0 < n := i.pos.trans_le h
      unfold uniformMean
      rw [Finset.sum_coe_sort _ (fun p : Fin n × Fin n => f p.1 p.2)]
      simp only [Fintype.card_coe, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      congr 1
      have he : n * n - n = n * (n - 1) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [he, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]

theorem sum_offDiag_eq_sum_sub_diag {a : Type*} [Fintype a] [DecidableEq a]
    (f : a → a → ℝ) :
    (∑ p ∈ (Finset.univ : Finset a).offDiag, f p.1 p.2) =
      (∑ r, ∑ s, f r s) - ∑ r, f r r := by
  have hF : (Finset.univ : Finset a).offDiag =
      (Finset.univ : Finset (a × a)).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp
  rw [hF, Finset.sum_filter, Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have hEr : (Finset.univ : Finset a).filter (fun s => r ≠ s) = Finset.univ.erase r := by
    ext s
    simp [eq_comm]
  rw [← Finset.sum_filter, hEr]
  have h := Finset.add_sum_erase Finset.univ (fun s => f r s) (Finset.mem_univ r)
  linarith

end SketchOrientation
