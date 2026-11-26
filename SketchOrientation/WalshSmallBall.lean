import SketchOrientation.WalshMiss
import Mathlib.Data.Int.Interval

/-!
# Binomial small-ball estimates for the independent Walsh table
-/

open Filter Function
open scoped Topology BigOperators

noncomputable section
namespace SketchOrientation.Edge.Walsh

private def positiveCount {s : ℕ} (u : Fin s → Bool) : ℕ :=
  (Finset.univ.filter fun i => u i).card

private theorem uniformProbability_positiveCount {s k : ℕ} :
    uniformProbability (fun u : Fin s → Bool => positiveCount u = k) =
      (s.choose k : ℝ) / (2 : ℝ)^s := by
  classical
  let e : {u : Fin s → Bool // positiveCount u = k} ≃ {S : Finset (Fin s) // S.card = k} :=
    Equiv.subtypeEquiv (trueSetEquiv s)
    (q := fun S => S.card = k) (fun _ => Iff.rfl)
  rw [uniformProbability_eq_card, Nat.card_congr e, Nat.card_eq_fintype_card]
  simp [Fintype.card_pi]

/-- At even support size every count has probability at most that of the
central count. -/
private theorem uniformProbability_positiveCount_le {s : ℕ} (he : Even s) (a : ℤ) :
    uniformProbability (fun u : Fin s → Bool => (positiveCount u : ℤ) = a) ≤
      balancedProbability s := by
  by_cases ha : 0 ≤ a
  · have ha' (u : Fin s → Bool) : (positiveCount u : ℤ) = a ↔ positiveCount u = a.toNat := by
      omega
    simp_rw [ha']
    rw [uniformProbability_positiveCount]
    apply div_le_div_of_nonneg_right _ (by positivity)
    obtain ⟨r, hr⟩ := he
    rw [show s = 2 * r by omega, show 2 * r / 2 = r by omega]
    exact_mod_cast Nat.choose_le_centralBinom a.toNat r
  · have ha' (u : Fin s → Bool) : (positiveCount u : ℤ) ≠ a := by omega
    simp [uniformProbability, indicator, ha', uniformMean, balancedProbability, div_nonneg]

/-- Probability of a band around zero for one normalized column sum. -/
theorem uniformProbability_column_band {s : ℕ} (he : Even s) {R : ℝ} (hR : 0 ≤ R) :
    uniformProbability (fun u : Fin s → Bool =>
      |(2 : ℝ) * positiveCount u - (s : ℝ)| ≤ R) ≤
        (R + 1) * balancedProbability s := by
  classical
  let q := ⌊R / 2⌋
  let k : ℤ := s / 2
  let A := {a : ℤ // a ∈ Finset.Icc (-q) q}
  have hk : 2 * (k : ℝ) = s := by
    have hk' : 2 * k = (s : ℤ) := by obtain ⟨r, hr⟩ := he; dsimp [k]; omega
    exact_mod_cast hk'
  have hq : 0 ≤ q := Int.floor_nonneg.2 (by positivity)
  have hcover (u : Fin s → Bool)
      (hu : |(2 : ℝ) * positiveCount u - (s : ℝ)| ≤ R) :
      ∃ a : A, (positiveCount u : ℤ) = k + a := by
    let a : ℤ := (positiveCount u : ℤ) - k
    have h₀ : (a : ℝ) ≤ R / 2 := by
      push_cast [a]
      linarith [(abs_le.1 hu).2]
    have h₁ : (-(a : ℝ)) ≤ R / 2 := by
      push_cast [a]
      linarith [(abs_le.1 hu).1]
    have h₀' : a ≤ q := Int.le_floor.2 h₀
    have h₁' : -a ≤ q := Int.le_floor.2 (by simpa only [Int.cast_neg] using h₁)
    exact ⟨⟨a, Finset.mem_Icc.2 ⟨by omega, h₀'⟩⟩, by dsimp [a]; omega⟩
  have hcard : (Fintype.card A : ℝ) ≤ R + 1 := by
    have h' := Int.card_Icc_of_le (a := -q) (b := q) (by omega)
    have hf := Int.floor_le (R / 2)
    have hr : (Fintype.card A : ℝ) = 2 * (q : ℝ) + 1 := by
      have h'' : (Fintype.card A : ℤ) = q + 1 - -q := by
        simpa only [A, Fintype.card_coe] using h'
      have hr' : (Fintype.card A : ℤ) = 2 * q + 1 := by omega
      exact_mod_cast hr'
    linarith
  have hp : 0 ≤ balancedProbability s := by unfold balancedProbability; positivity
  calc
    _ ≤ uniformProbability (fun u : Fin s → Bool => ∃ a : A, (positiveCount u : ℤ) = k + a) :=
      uniformProbability_mono hcover
    _ ≤ ∑ a : A, uniformProbability (fun u : Fin s → Bool => (positiveCount u : ℤ) = k + a) :=
      uniformProbability_exists_le_sum _
    _ ≤ ∑ _ : A, balancedProbability s :=
      Finset.sum_le_sum fun a _ => uniformProbability_positiveCount_le he (k + a)
    _ = (Fintype.card A : ℝ) * balancedProbability s := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hp

private theorem uniformProbability_every_column {s ell : ℕ} (P : (Fin s → Bool) → Prop) :
    uniformProbability (fun T : Fin s → Fin ell → Bool => ∀ j, P (fun i => T i j)) =
      uniformProbability P ^ ell := by
  classical
  let flip : (Fin s → Fin ell → Bool) ≃ (Fin ell → Fin s → Bool) :=
    ⟨Function.swap, Function.swap, fun _ => rfl, fun _ => rfl⟩
  let e : {T : Fin s → Fin ell → Bool // ∀ j, P (fun i => T i j)} ≃
      (Fin ell → {u : Fin s → Bool // P u}) := (Equiv.subtypeEquiv flip (q := fun T => ∀ j, P (T j)) (fun _ => Iff.rfl)).trans
    Equiv.subtypePiEquivPi
  rw [uniformProbability_eq_card, uniformProbability_eq_card, Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_bool,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, div_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- An energy small ball implies all columns lie in the corresponding
one-dimensional bands, whose probabilities multiply under the iid law. -/
theorem uniformProbability_iid_energy_le {s ell : ℕ} (hs : 0 < s) (he : Even s)
    {t : ℝ} (ht : 0 ≤ t) :
    uniformProbability (fun T : Fin s → Fin ell → Bool => walshTableEnergy T ≤ t) ≤
    ((Real.sqrt (t * s) + 1) * balancedProbability s) ^ ell := by
  let R := Real.sqrt (t * s)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hcover (T : Fin s → Fin ell → Bool) (hT : walshTableEnergy T ≤ t) :
      ∀ j : Fin ell, |(2 : ℝ) * positiveCount (fun i => T i j) - (s : ℝ)| ≤ R := by
    intro j
    have hs' : (0 : ℝ) < s := by positivity
    have hsum : (∑ j, (walshSignSum T j : ℝ)^2) ≤ t * s := (div_le_iff₀ hs').1 hT
    have hterm : (walshSignSum T j : ℝ)^2 ≤ t * s :=
      (Finset.single_le_sum (fun i _ => sq_nonneg (walshSignSum T i : ℝ))
        (Finset.mem_univ j)).trans hsum
    have hab : |(walshSignSum T j : ℝ)| ≤ Real.sqrt (t * s) := by
      apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg ht hs'.le)).2
      rwa [sq_abs]
    have hsign := congrArg (fun z : ℤ => (z : ℝ)) (walshSignSum_eq_count T j)
    push_cast at hsign
    simpa only [hsign, positiveCount] using hab
  calc
    _ ≤ uniformProbability (fun T : Fin s → Fin ell → Bool => ∀ j : Fin ell,
        |(2 : ℝ) * positiveCount (fun i => T i j) - (s : ℝ)| ≤ R) :=
      uniformProbability_mono hcover
    _ = (uniformProbability (fun u : Fin s → Bool =>
        |(2 : ℝ) * positiveCount u - (s : ℝ)| ≤ R)) ^ ell :=
      uniformProbability_every_column (ell := ell)
        (fun u : Fin s → Bool => |(2 : ℝ) * positiveCount u - (s : ℝ)| ≤ R)
    _ ≤ _ := pow_le_pow_left₀ (uniformProbability_nonneg _) (uniformProbability_column_band he hR) _


/-- The bound on the small positive projections holds uniformly in the size
of the ball. Below the first positive lattice point the event is empty. -/
theorem eventually_positive_energy_smallBall {m s : ℕ → ℕ} {ell : ℕ}
    (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i)
    (hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i)
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in atTop, ∀ t : ℝ, 0 < t →
      uniformProbability (fun d : Draw (m i) (s i) ell =>
        0 < walshTableEnergy (table d) ∧ walshTableEnergy (table d) ≤ t) ≤
        C * t ^ ((ell : ℝ) / 2) := by
  let B : ℝ := Real.sqrt (2 / Real.pi) + 1
  let D : ℝ := 1 + (ell : ℝ)^2 + (2 : ℝ)^ell
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨(2*B)^ell + D, by positivity, ?_⟩
  have hg : ∀ᶠ i in atTop,
      (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ)^m i ≤ 1 :=
    hgrowth.eventually (ge_mem_nhds (by norm_num))
  have hbal : ∀ᶠ i in atTop, balancedProbability (s i) * Real.sqrt (s i) ≤ B :=
    (tendsto_balancedProbability_scaled hs he).eventually (ge_mem_nhds (by dsimp [B]; linarith))
  filter_upwards [hs.eventually_ge_atTop 1, he, hr, hc, hg, hbal] with i hsi hei hri hci hgi hbi
  letI := label_embedding_nonempty (m := m i) hri
  letI := label_embedding_nonempty (m := m i) hci
  have hspos : 0 < s i := by omega
  have hspos' : 0 < (s i : ℝ) := by exact_mod_cast hspos
  have hsr : 0 < Real.sqrt (s i : ℝ) := by positivity
  intro t ht
  by_cases ht' : t < 4 / (s i : ℝ)
  · have hzero (d : Draw (m i) (s i) ell) :
        ¬(0 < walshTableEnergy (table d) ∧ walshTableEnergy (table d) ≤ t) := by
      intro hd
      exact (not_le_of_gt ht') ((walshTableEnergy_pos_ge hspos hei _ hd.1).trans hd.2)
    simp [uniformProbability, indicator, uniformMean, hzero]
    positivity
  have ht' : 4 / (s i : ℝ) ≤ t := le_of_not_gt ht'
  have hts : 4 ≤ t * s i := (div_le_iff₀ hspos').1 ht'
  have hsqrt : 1 ≤ Real.sqrt t * Real.sqrt (s i : ℝ) := by
    have hh : 1 ≤ Real.sqrt (t * s i) := by
      apply (Real.le_sqrt zero_le_one (by positivity)).2
      norm_num
      linarith
    rwa [Real.sqrt_mul ht.le] at hh
  let P (T : Fin (s i) → Fin ell → Bool) :=
    0 < walshTableEnergy T ∧ walshTableEnergy T ≤ t
  have hcmp : |uniformProbability (fun d : Draw (m i) (s i) ell => P (table d)) -
      uniformProbability P| ≤
      ((s i : ℝ)^2 + (ell : ℝ)^2 + (2 : ℝ)^ell) / (2 : ℝ)^m i :=
    abs_uniformMean_table_sub (m := m i) (fun T => indicator (P T))
      (fun _ => indicator_nonneg _) (fun _ => indicator_le_one _)
  have hbin : uniformProbability P ≤ (2 * B)^ell * t ^ ((ell : ℝ) / 2) := by
    apply (uniformProbability_mono (P := P) (Q := fun T => walshTableEnergy T ≤ t)
      (fun _ h => h.2)).trans
    apply (uniformProbability_iid_energy_le hspos hei ht.le).trans
    have hpb : 0 ≤ balancedProbability (s i) := by unfold balancedProbability; positivity
    have hb : (Real.sqrt (t * (s i : ℝ)) + 1) * balancedProbability (s i)
        ≤ 2 * B * Real.sqrt t := by
      rw [Real.sqrt_mul ht.le]
      calc
        _ ≤ (2 * (Real.sqrt t * Real.sqrt (s i : ℝ))) * balancedProbability (s i) :=
          mul_le_mul_of_nonneg_right (by linarith) hpb
        _ = (2 * Real.sqrt t) * (balancedProbability (s i) * Real.sqrt (s i : ℝ)) := by ring
        _ ≤ (2 * Real.sqrt t) * B := mul_le_mul_of_nonneg_left hbi (by positivity)
        _ = _ := by ring
    rw [← sqrt_pow_eq_rpow t ht.le ell, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hb _
  have herr : ((s i : ℝ)^2 + (ell : ℝ)^2 + (2 : ℝ)^ell) / (2 : ℝ)^m i ≤
      D * t ^ ((ell : ℝ) / 2) := by
    have hsr1 : (1 : ℝ) ≤ s i := by exact_mod_cast hsi
    have hs2 : (1 : ℝ) ≤ (s i : ℝ)^2 := by nlinarith
    have hnum : (s i : ℝ)^2 + (ell : ℝ)^2 + (2 : ℝ)^ell ≤ D * (s i : ℝ)^2 := by
      have h₁ := mul_le_mul_of_nonneg_left hs2 (sq_nonneg (ell : ℝ))
      have h₂ := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ (2 : ℝ)^ell by positivity)
      dsimp [D]
      nlinarith
    have hs' : (1 : ℝ) / s i ≤ t := (div_le_iff₀ hspos').2 (by linarith)
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (1 : ℝ) / s i) hs' (by positivity :
      0 ≤ (ell : ℝ) / 2)
    rw [one_div, Real.inv_rpow hspos'.le] at hpow
    rw [Real.rpow_add hspos', Real.rpow_two] at hgi
    have hgi₀ : ((s i : ℝ)^2 / (2 : ℝ)^m i) * (s i : ℝ) ^ ((ell : ℝ) / 2) ≤ 1 := by
      rwa [div_mul_eq_mul_div]
    have hgi₁ := (le_div_iff₀ (Real.rpow_pos_of_pos hspos' ((ell : ℝ) / 2))).2 hgi₀
    calc
      _ ≤ D * ((s i : ℝ)^2 / (2 : ℝ)^m i) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ D * (1 / (s i : ℝ) ^ ((ell : ℝ) / 2)) := mul_le_mul_of_nonneg_left hgi₁ hD.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [one_div] using hpow) hD.le
  change uniformProbability (fun d : Draw (m i) (s i) ell => P (table d)) ≤ _
  have hu := (abs_le.1 hcmp).2.trans herr
  rw [add_mul]
  linarith only [hu, hbin]

end SketchOrientation.Edge.Walsh
