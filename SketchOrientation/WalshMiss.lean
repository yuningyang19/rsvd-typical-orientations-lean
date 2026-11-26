import SketchOrientation.WalshCoupling
import SketchOrientation.WalshStirling
import Mathlib.Data.Fintype.Powerset

/-!
# Exact misses of the signed Walsh sketch
-/

open Filter Asymptotics Function
open scoped Topology BigOperators

noncomputable section
namespace SketchOrientation.Edge.Walsh

def trueSetEquiv (s : ℕ) : (Fin s → Bool) ≃ Finset (Fin s) where
  toFun u := Finset.univ.filter fun i => u i
  invFun S i := decide (i ∈ S)
  left_inv u := by ext i; cases h : u i <;> simp [h]
  right_inv S := by ext i; simp

/-- The signed Walsh miss probability for an equal-amplitude support. -/
def missProbability (m s ell : ℕ) : ℝ :=
  uniformProbability fun d : Draw m s ell => walshTableEnergy (table d) = 0

theorem tableEnergy_eq_zero_iff {s ell : ℕ} (hs : 0 < s)
    (T : Fin s → Fin ell → Bool) :
    walshTableEnergy T = 0 ↔ ∀ j, walshSignSum T j = 0 := by
  have hs' : (s : ℝ) ≠ 0 := by positivity
  simp only [walshTableEnergy, div_eq_zero_iff, hs', or_false]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (walshSignSum T j : ℝ))]
  simp

theorem iid_missProbability {s ell : ℕ} (hs : 0 < s) (he : Even s) :
    uniformProbability (fun T : Fin s → Fin ell → Bool => walshTableEnergy T = 0) =
      balancedProbability s ^ ell := by
  classical
  let flip : (Fin s → Fin ell → Bool) ≃ (Fin ell → Fin s → Bool) :=
    ⟨Function.swap, Function.swap, fun _ => rfl, fun _ => rfl⟩
  let trans := Equiv.subtypeEquiv flip
    (q := fun T => ∀ j, (Finset.univ.filter fun i => T j i).card = s / 2)
    (fun T => (tableEnergy_eq_zero_iff hs T).trans (forall_congr' (walshSignSum_zero_iff he T)))
  let e := trans.trans (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight
    fun _j : Fin ell => Equiv.subtypeEquiv (trueSetEquiv s)
      (q := fun S => S.card = s / 2) (fun _ => Iff.rfl)))
  rw [uniformProbability_eq_card, Nat.card_congr e, Nat.card_eq_fintype_card]
  simp only [Fintype.card_pi, Fintype.card_finset_len, Fintype.card_fin, Fintype.card_bool,
    Finset.prod_const, Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat, balancedProbability,
    div_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Finite error bound in the exact miss probability. -/
theorem abs_missProbability_sub {m s ell : ℕ}
    [Nonempty (Fin s ↪ Label m)] [Nonempty (Fin ell ↪ Label m)]
    (hs : 0 < s) (he : Even s) :
    |missProbability m s ell - balancedProbability s ^ ell| ≤
      ((s : ℝ)^2 + (ell : ℝ)^2 + (2 : ℝ)^ell) / (2 : ℝ)^m := by
  rw [← iid_missProbability hs he]
  exact abs_uniformMean_table_sub (m := m)
    (fun T : Fin s → Fin ell → Bool => indicator (walshTableEnergy T = 0))
    (fun _ => indicator_nonneg _) (fun _ => indicator_le_one _)

theorem label_embedding_nonempty {m k : ℕ} (hk : k ≤ 2^m) :
    Nonempty (Fin k ↪ Label m) := by
  let e := Fintype.equivFin (Label m)
  have hk' : k ≤ Fintype.card (Label m) := by rwa [card_label]
  exact ⟨(Fin.castLEEmb hk').trans e.symm.toEmbedding⟩

theorem sqrt_pow_eq_rpow (x : ℝ) (hx : 0 ≤ x) (ell : ℕ) :
    Real.sqrt x ^ ell = x ^ ((ell : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hx]
  congr 1
  ring

/-- The miss probability times the paper's normalization converges to the
positive constant determined by Stirling's formula. -/
theorem tendsto_scaled_missProbability {m s : ℕ → ℕ} {ell : ℕ}
    (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i)
    (hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i)
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0)) :
    Tendsto (fun i => missProbability (m i) (s i) ell * (s i : ℝ) ^ ((ell : ℝ) / 2))
      atTop (𝓝 ((2 / Real.pi : ℝ) ^ ((ell : ℝ) / 2))) := by
  let q (i : ℕ) := (s i : ℝ) ^ ((ell : ℝ) / 2)
  let a (i : ℕ) := missProbability (m i) (s i) ell * q i
  let b (i : ℕ) := balancedProbability (s i) ^ ell * q i
  let C : ℝ := 1 + (ell : ℝ)^2 + (2 : ℝ)^ell
  have hb : Tendsto b atTop (𝓝 ((2 / Real.pi : ℝ) ^ ((ell : ℝ) / 2))) := by
    have h := (tendsto_balancedProbability_scaled hs he).pow ell
    have hsqrt (i : ℕ) := sqrt_pow_eq_rpow (s i : ℝ) (by positivity) ell
    have hpi := sqrt_pow_eq_rpow (2 / Real.pi) (by positivity) ell
    simpa only [b, q, mul_pow, hsqrt, hpi] using h
  have hbound : ∀ᶠ i in atTop, |a i - b i| ≤
      C * ((s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i) := by
    filter_upwards [hs.eventually_ge_atTop 1, he, hr, hc] with i hsi hei hri hci
    letI := label_embedding_nonempty (m := m i) hri
    letI := label_embedding_nonempty (m := m i) hci
    have hs1 : (1 : ℝ) ≤ s i := by exact_mod_cast hsi
    have hs2 : (1 : ℝ) ≤ (s i : ℝ)^2 := by nlinarith
    have hq : 0 ≤ q i := by positivity
    have hC : (s i : ℝ)^2 + (ell : ℝ)^2 + (2 : ℝ)^ell ≤ C * (s i : ℝ)^2 := by
      have h₁ := mul_le_mul_of_nonneg_left hs2 (sq_nonneg (ell : ℝ))
      have h₂ := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ (2 : ℝ)^ell by positivity)
      dsimp [C]
      nlinarith
    calc
      |a i - b i| =
        |missProbability (m i) (s i) ell - balancedProbability (s i) ^ ell| * q i := by
          dsimp only [a, b]
          rw [← sub_mul, abs_mul, abs_of_nonneg hq]
      _ ≤ (((s i : ℝ)^2 + (ell : ℝ)^2 + (2 : ℝ)^ell) / (2 : ℝ)^m i) * q i :=
        mul_le_mul_of_nonneg_right (abs_missProbability_sub (by omega) hei) hq
      _ ≤ (C * (s i : ℝ)^2 / (2 : ℝ)^m i) * q i :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hC (by positivity)) hq
      _ = _ := by
        dsimp only [q]
        rw [Real.rpow_add (by positivity), Real.rpow_two]
        ring
  have hd : Tendsto (fun i => a i - b i) atTop (𝓝 0) := by
    have hu := hgrowth.const_mul C
    rw [mul_zero] at hu
    exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hbound) hu
  have h := hd.add hb
  simpa only [zero_add, sub_add_cancel] using h

/-- Exact miss equivalent in Proposition 6.4. -/
theorem missProbability_isEquivalent {m s : ℕ → ℕ} {ell : ℕ}
    (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i)
    (hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i)
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0)) :
    (fun i => missProbability (m i) (s i) ell) ~[atTop]
      (fun i => (2 / Real.pi : ℝ) ^ ((ell : ℝ) / 2) * (s i : ℝ) ^ (-(ell : ℝ) / 2)) := by
  have h := tendsto_scaled_missProbability hs he hr hc hgrowth
  have hK : 0 < (2 / Real.pi : ℝ) ^ ((ell : ℝ) / 2) :=
    Real.rpow_pos_of_pos (div_pos (by norm_num) Real.pi_pos) _
  have h' := h.div_const ((2 / Real.pi : ℝ) ^ ((ell : ℝ) / 2))
  rw [div_self hK.ne'] at h'
  apply isEquivalent_of_tendsto_one
  refine h'.congr' ?_
  filter_upwards [hs.eventually_ge_atTop 1] with i hi
  have hsi : (0 : ℝ) < s i := by exact_mod_cast (show 0 < s i by omega)
  change _ = missProbability (m i) (s i) ell /
    ((2 / Real.pi : ℝ) ^ ((ell : ℝ) / 2) * (s i : ℝ) ^ (-(ell : ℝ) / 2))
  rw [neg_div, Real.rpow_neg hsi.le]
  field_simp [hK.ne', (Real.rpow_pos_of_pos hsi ((ell : ℝ) / 2)).ne']

end SketchOrientation.Edge.Walsh
