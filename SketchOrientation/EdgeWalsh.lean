import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic

/-!
# Walsh support and exact misses

Deterministic parts of the argument in `edge.tex`, lines 131–181.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section
namespace SketchOrientation.Edge

/-- The largest even natural number at most
`min (log n) (L ^ (1 / ell))` when that bound is nonnegative. -/
def walshSupport (ell : ℕ) (n L : ℝ) : ℕ :=
  2 * ⌊min (Real.log n) (L ^ (1 / (ell : ℝ))) / 2⌋₊

theorem walshSupport_even (ell : ℕ) (n L : ℝ) : Even (walshSupport ell n L) :=
  ⟨_, two_mul _⟩

theorem walshSupport_le_min {ell : ℕ} {n L : ℝ} (hn : 1 ≤ n) (hL : 0 ≤ L) :
    (walshSupport ell n L : ℝ) ≤ min (Real.log n) (L ^ (1 / (ell : ℝ))) := by
  have hb : 0 ≤ min (Real.log n) (L ^ (1 / (ell : ℝ))) :=
    le_min (Real.log_nonneg hn) (Real.rpow_nonneg hL _)
  unfold walshSupport
  push_cast
  linarith [Nat.floor_le (show 0 ≤ min (Real.log n) (L ^ (1 / (ell : ℝ))) / 2 by positivity)]

theorem tendsto_walshSupport {ell : ℕ} {n L : ℕ → ℝ} (hell : 0 < ell)
    (hn : Tendsto n atTop atTop) (hL : Tendsto L atTop atTop) :
    Tendsto (fun j => walshSupport ell (n j) (L j)) atTop atTop := by
  have hlog := Real.tendsto_log_atTop.comp hn
  have hpow := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / (ell : ℝ) by positivity)).comp hL
  refine tendsto_atTop.2 fun m => ?_
  filter_upwards [hlog.eventually_ge_atTop (2 * m), hpow.eventually_ge_atTop (2 * m)] with j hj hk
  change 2 * (m : ℝ) ≤ Real.log (n j) at hj
  change 2 * (m : ℝ) ≤ L j ^ (1 / (ell : ℝ)) at hk
  have hfloor : m ≤ ⌊min (Real.log (n j)) (L j ^ (1 / (ell : ℝ))) / 2⌋₊ :=
    Nat.le_floor (by linarith [le_min hj hk])
  unfold walshSupport
  omega

theorem walshSupport_le_dimension {ell n : ℕ} {L : ℝ} (hn : 1 ≤ n) (hL : 0 ≤ L) :
    walshSupport ell n L ≤ n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log n ≤ (n : ℝ) :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  exact_mod_cast (walshSupport_le_min (ell := ell) hn' hL).trans
    ((min_le_left _ _).trans hlog)

/-- The log bound in the prescribed-gap construction ensures the growth condition in the
exact-miss proposition. -/
theorem walshSupport_growth {ell : ℕ} {n L : ℕ → ℝ}
    (hn : Tendsto n atTop atTop) (hL : ∀ᶠ j in atTop, 0 ≤ L j) :
    Tendsto (fun j => (walshSupport ell (n j) (L j) : ℝ) ^ (2 + (ell : ℝ) / 2) / n j)
      atTop (𝓝 0) := by
  have hp : 0 < (2 : ℝ) + (ell : ℝ) / 2 := by positivity
  have hlog := ((isLittleO_log_rpow_rpow_atTop (s := 1) (2 + (ell : ℝ) / 2) (by norm_num)).tendsto_div_nhds_zero).comp hn
  simp only [Real.rpow_one] at hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog ?_ ?_
  · filter_upwards [hn.eventually_ge_atTop 1] with j hj
    exact div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith)
  · filter_upwards [hn.eventually_ge_atTop 1, hL] with j hj hLj
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact Real.rpow_le_rpow (by positivity)
      (le_trans (walshSupport_le_min hj hLj) (min_le_left _ _)) hp.le

/-- The upper bound from the prescribed gap gives the divergent atom scale. -/
theorem walshSupport_atomScale {ell : ℕ} {n L : ℕ → ℝ} (hell : 0 < ell)
    (hn : Tendsto n atTop atTop) (hL : Tendsto L atTop atTop) :
    Tendsto (fun j => L j * (walshSupport ell (n j) (L j) : ℝ) ^ (-(ell : ℝ) / 2))
      atTop atTop := by
  have hhalf : (0 : ℝ) < (ell : ℝ) / 2 := by positivity
  refine tendsto_atTop_mono' _ ?_ ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hL)
  filter_upwards [hn.eventually_ge_atTop 1, hL.eventually_ge_atTop 1,
    (tendsto_walshSupport hell hn hL).eventually_ge_atTop 1] with j hj hLj hsj
  have hs : 0 < (walshSupport ell (n j) (L j) : ℝ) := by exact_mod_cast hsj
  have hLpos : 0 < L j := by linarith
  have hpow := Real.rpow_le_rpow hs.le
    ((walshSupport_le_min (ell := ell) (L := L j) hj hLpos.le).trans (min_le_right _ _)) hhalf.le
  rw [← Real.rpow_mul hLpos.le] at hpow
  have heq : 1 / (ell : ℝ) * ((ell : ℝ) / 2) = 1 / 2 := by
    field_simp
  rw [heq] at hpow
  show L j ^ (1 / 2 : ℝ) ≤ L j * (walshSupport ell (n j) (L j) : ℝ) ^ (-(ell : ℝ) / 2)
  rw [neg_div, Real.rpow_neg hs.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hs _)]
  calc
    _ ≤ L j ^ (1 / 2 : ℝ) * L j ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hLpos.le _)
    _ = L j := by rw [← Real.rpow_add hLpos]; norm_num

/-- A prescribed target supported on the first `s` coordinates. -/
def equalSupportTarget (n s : ℕ) (i : Fin n) : ℝ :=
  if i.val < s then (Real.sqrt (s : ℝ))⁻¹ else 0

theorem equalSupportTarget_unit {n s : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    (∑ i : Fin n, equalSupportTarget n s i ^ 2) = 1 := by
  have hsq : ((Real.sqrt (s : ℝ))⁻¹)^2 = (s : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  simp only [equalSupportTarget, apply_ite (fun r : ℝ => r ^ 2), zero_pow (by decide : 2 ≠ 0),
    hsq, ← Finset.sum_filter, Finset.sum_const, Fin.card_filter_val_lt,
    min_eq_right hsn, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

theorem equalSupportTarget_entry_bound (n s : ℕ) (i : Fin n) :
    |equalSupportTarget n s i| ≤ (Real.sqrt (s : ℝ))⁻¹ := by
  unfold equalSupportTarget
  split <;> simp [abs_of_nonneg (show 0 ≤ (Real.sqrt (s : ℝ))⁻¹ by positivity)]

/-- A column sum of a Walsh sign table restricted to the support. -/
def walshSignSum {s ell : ℕ} (A : Fin s → Fin ell → Bool) (j : Fin ell) : ℤ :=
  ∑ i, if A i j then 1 else -1

theorem walshSignSum_eq_count {s ell : ℕ} (A : Fin s → Fin ell → Bool) (j : Fin ell) :
    walshSignSum A j = 2 * ((Finset.univ.filter fun i => A i j).card : ℤ) - (s : ℤ) := by
  rw [Finset.natCast_card_filter]
  unfold walshSignSum
  rw [Finset.mul_sum, ← (show (∑ _ : Fin s, (1 : ℤ)) = s by simp),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases A i j <;> norm_num

theorem walshSignSum_zero_iff {s ell : ℕ} (hs : Even s)
    (A : Fin s → Fin ell → Bool) (j : Fin ell) :
    walshSignSum A j = 0 ↔ (Finset.univ.filter fun i => A i j).card = s / 2 := by
  rw [walshSignSum_eq_count]
  rcases hs with ⟨r, hr⟩
  omega

/-- Squared Euclidean norm of the table's column sums scaled by `1 / √s`. -/
def walshTableEnergy {s ell : ℕ} (A : Fin s → Fin ell → Bool) : ℝ :=
  (∑ j, (walshSignSum A j : ℝ)^2) / s

theorem walshTableEnergy_eq_normSq {s ell : ℕ} (A : Fin s → Fin ell → Bool) :
    walshTableEnergy A = ∑ j, ((walshSignSum A j : ℝ) / Real.sqrt s)^2 := by
  unfold walshTableEnergy
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_pow, Real.sq_sqrt (by positivity)]

/-- On even support, the positive energy cannot be smaller than `4 / s`. -/
theorem walshTableEnergy_pos_ge {s ell : ℕ} (hs : 0 < s) (hse : Even s)
    (A : Fin s → Fin ell → Bool) (hA : 0 < walshTableEnergy A) :
    (4 : ℝ) / (s : ℝ) ≤ walshTableEnergy A := by
  have hnz : ∃ j, walshSignSum A j ≠ 0 := by
    by_contra! hz
    simp [walshTableEnergy, hz] at hA
  obtain ⟨j, hj⟩ := hnz
  have hsquare : (4 : ℝ) ≤ (walshSignSum A j : ℝ)^2 := by
    have hj' := walshSignSum_eq_count A j
    rcases hse with ⟨r, hr⟩
    have hsign : walshSignSum A j ≤ -2 ∨ 2 ≤ walshSignSum A j := by omega
    rcases hsign with h | h
    · have h' : (walshSignSum A j : ℝ) ≤ -2 := by exact_mod_cast h
      nlinarith [mul_nonneg (show 0 ≤ -(walshSignSum A j : ℝ) - 2 by linarith)
        (show 0 ≤ -(walshSignSum A j : ℝ) + 2 by linarith)]
    · have h' : (2 : ℝ) ≤ (walshSignSum A j : ℝ) := by exact_mod_cast h
      nlinarith [mul_nonneg (show 0 ≤ (walshSignSum A j : ℝ) - 2 by linarith)
        (show 0 ≤ (walshSignSum A j : ℝ) + 2 by linarith)]
  unfold walshTableEnergy
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact hsquare.trans (Finset.single_le_sum (f := fun u => (walshSignSum A u : ℝ)^2)
    (fun u _ => sq_nonneg (walshSignSum A u : ℝ)) (Finset.mem_univ j))

/-- The rank-one loss of a draw, as in `preliminaries.tex`, equation (edge:loss). -/
def rankOneLoss (n L : ℝ) (ell : ℕ) (y : ℝ) : ℝ :=
  n / (n - 1) * (L / (1 + (L - 1 / n) * y)) - (ell : ℝ) / (n - 1)

/-- For a finite law with weights summing to one, the exact zero contribution
has coefficient `n L / (n - 1)`. The positive part retains the entire regularizer.
This applies to Walsh draws by taking their squared overlaps as `Y`. -/
theorem rankOneLoss_exact_miss_split {D : Type*} [Fintype D] [DecidableEq D]
    (w Y : D → ℝ) (n L : ℝ) (ell : ℕ) (hw : ∑ d, w d = 1) :
    (∑ d, w d * rankOneLoss n L ell (Y d)) =
      n / (n - 1) * L * (∑ d with Y d = 0, w d) +
      n / (n - 1) * (∑ d with Y d ≠ 0, w d * (L / (1 + (L - 1 / n) * Y d))) -
      (ell : ℝ) / (n - 1) := by
  classical
  simp only [rankOneLoss, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
  have h (d : D) : w d * (n / (n - 1) * (L / (1 + (L - 1 / n) * Y d))) =
      n / (n - 1) * (w d * (L / (1 + (L - 1 / n) * Y d))) := by ring
  simp_rw [h]
  have hzero :
      (∑ d with Y d = 0, w d * (L / (1 + (L - 1 / n) * Y d))) =
        L * ∑ d with Y d = 0, w d := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [(Finset.mem_filter.mp hd).2]
    simp [mul_comm]
  rw [← Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun d => Y d = 0),
    hzero, mul_add, mul_assoc]

end SketchOrientation.Edge
