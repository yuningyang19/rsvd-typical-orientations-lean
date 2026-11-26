import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Scalar estimates for the growing-gap cosine comparison

The eigenvalue formulation allows every squared singular value to be zero.
Manuscript locations refer to commit `68dd06e`.
-/

open scoped BigOperators

namespace SketchOrientation.Cosine

/-- Ridge statistic in eigenvalue coordinates, `cosine.tex:46–50`. -/
noncomputable def ridge {k : ℕ} (L : ℝ) (θ : Fin k → ℝ) : ℝ :=
  ∑ j, L / (1 + L * k * θ j)

/-- Exact two-level loss in eigenvalue coordinates, `preliminaries.tex:130–133`. -/
noncomputable def twoLevelLoss {k : ℕ} (n ℓ : ℕ) (L : ℝ) (θ : Fin k → ℝ) : ℝ :=
  (n : ℝ) / (n - (k : ℝ)) *
    (∑ j, L / (1 + (L * k - 1 / (n : ℝ)) * θ j)) -
      (ℓ : ℝ) / ((k : ℝ) * (n - (k : ℝ)))

private theorem ridgeTerm_difference {n k L t : ℝ}
    (hn : 0 < n) (hk : 0 < k) (hL : 0 < L) (hgap : 1 / n ≤ L * k)
    (ht : 0 ≤ t) :
    0 ≤ L / (1 + (L * k - 1 / n) * t) - L / (1 + L * k * t) ∧
    L / (1 + (L * k - 1 / n) * t) - L / (1 + L * k * t) ≤ 1 / (n * k) := by
  let a := 1 + L * k * t
  let q := 1 + (L * k - 1 / n) * t
  have ha : 0 < a := by dsimp [a]; positivity
  have hq : 1 ≤ q := by dsimp [q]; nlinarith [mul_nonneg (sub_nonneg.mpr hgap) ht]
  have hqp : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hdiff : a - q = t / n := by dsimp [a, q]; ring
  have hrepr : L / q - L / a = (L * (t / n) / a) / q := by
    rw [← hdiff]
    field_simp
  have htop : L * (t / n) / a ≤ 1 / (n * k) := by
    apply (div_le_div_iff₀ ha (mul_pos hn hk)).mpr
    dsimp [a]
    field_simp
    nlinarith
  change 0 ≤ L / q - L / a ∧ L / q - L / a ≤ _
  rw [hrepr]
  constructor
  · positivity
  · exact (div_le_self (by positivity) hq).trans htop

/-- Finite-contrast transfer at `cosine.tex:282–291`. The gap assumption is
`Γ = nkL ≥ 1`, as in the two-level loss formula. -/
theorem finiteGap_transfer {n k ℓ : ℕ} {L : ℝ} {θ : Fin k → ℝ}
    (hk : 0 < k) (hkn : k < n) (hL : 0 < L)
    (hgap : 1 ≤ (n : ℝ) * k * L) (hθ : ∀ j, 0 ≤ θ j) :
    |twoLevelLoss n ℓ L θ - ridge L θ| ≤
      ((k : ℝ)^2 * L + 1 + (ℓ : ℝ) / k) / (n - (k : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast (hk.trans hkn)
  have hgap' : 1 / (n : ℝ) ≤ L * k := by
    apply (div_le_iff₀ hn').mpr
    nlinarith
  have hden : 0 < (n : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkn)
  let S := ∑ j : Fin k, L / (1 + (L * k - 1 / (n : ℝ)) * θ j)
  let R := ridge L θ
  have hterm (j : Fin k) := ridgeTerm_difference hn' hk' hL hgap' (hθ j)
  have hdiff : 0 ≤ S - R ∧ S - R ≤ 1 / (n : ℝ) := by
    dsimp [S, R, ridge]
    rw [← Finset.sum_sub_distrib]
    constructor
    · exact Finset.sum_nonneg (fun j _ ↦ (hterm j).1)
    · calc
        _ ≤ ∑ _j : Fin k, 1 / ((n : ℝ) * k) :=
          Finset.sum_le_sum (fun j _ ↦ (hterm j).2)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                    field_simp
  have hR : 0 ≤ R ∧ R ≤ k * L := by
    dsimp [R, ridge]
    constructor
    · apply Finset.sum_nonneg
      intro j hj
      have := hθ j
      positivity
    · calc
        _ ≤ ∑ _j : Fin k, L := by
          apply Finset.sum_le_sum
          intro j hj
          have := hθ j
          apply div_le_self hL.le
          linarith [mul_nonneg (mul_nonneg hL.le hk'.le) this]
        _ = _ := by simp
  change |(n : ℝ) / (n - (k : ℝ)) * S -
      (ℓ : ℝ) / ((k : ℝ) * (n - (k : ℝ))) - R| ≤ _
  have hrepr : (n : ℝ) / (n - (k : ℝ)) * S -
      (ℓ : ℝ) / ((k : ℝ) * (n - (k : ℝ))) - R =
      ((n : ℝ) * (S - R) + k * R - (ℓ : ℝ) / k) / (n - (k : ℝ)) := by
    field_simp
    ring
  rw [hrepr, abs_div, abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  have h₁ : 0 ≤ (n : ℝ) * (S - R) := mul_nonneg hn'.le hdiff.1
  have h₂ : (n : ℝ) * (S - R) ≤ 1 := by
    simpa [div_eq_mul_inv, mul_comm, hn'.ne'] using mul_le_mul_of_nonneg_left hdiff.2 hn'.le
  have h₃ : 0 ≤ (k : ℝ) * R := mul_nonneg hk'.le hR.1
  have h₄ : (k : ℝ) * R ≤ (k : ℝ)^2 * L := by
    simpa [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hR.2 hk'.le
  have h₅ : 0 ≤ (ℓ : ℝ) / k := by positivity
  have h₆ : 0 ≤ (k : ℝ)^2 * L := by positivity
  rw [abs_le]
  constructor <;> linarith

private theorem regularizationTerm_le {L x θ : ℝ} (hL : 0 < L) (hx : 0 ≤ x)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    x ^ 2 / (L + x) ≤ L ^ (-θ) * (x * x ^ θ) := by
  have hy : 0 ≤ x / L := div_nonneg hx hL.le
  have hden : 0 < 1 + x / L := by linarith
  have hratio : (x / L) / (1 + x / L) ≤ (x / L) ^ θ := by
    by_cases h : x / L ≤ 1
    · calc
        _ ≤ x / L := div_le_self hy (by linarith)
        _ ≤ _ := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hy h hθ₀ hθ₁
    · have h' : 1 ≤ x / L := le_of_lt (lt_of_not_ge h)
      calc
        _ ≤ 1 := (div_le_one hden).mpr (by linarith)
        _ ≤ _ := Real.one_le_rpow h' hθ₀
  rw [Real.div_rpow hx hL.le, div_eq_mul_inv (x ^ θ), ← Real.rpow_neg hL.le] at hratio
  calc
    _ = x * ((x * L⁻¹) / (1 + x / L)) := by
      field_simp
    _ ≤ x * (x ^ θ * L ^ (-θ)) :=
      mul_le_mul_of_nonneg_left (by simpa only [div_eq_mul_inv x L] using hratio) hx
    _ = _ := by ring

/-- Removing the ridge in positive spectral coordinates, `cosine.tex:265–272`.
Here `x j = (k * σ_j(W))⁻¹` in the Gaussian application. -/
theorem ridgeRemoval_bound {k : ℕ} {L θ : ℝ} {x : Fin k → ℝ}
    (hL : 0 < L) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hx : ∀ j, 0 ≤ x j) :
    0 ≤ (∑ j, x j) - (∑ j, L * x j / (L + x j)) ∧
    (∑ j, x j) - (∑ j, L * x j / (L + x j)) ≤
      L ^ (-θ) * (∑ j, x j) ^ (1 + θ) := by
  have hrepr (j : Fin k) : x j - L * x j / (L + x j) = x j ^ 2 / (L + x j) := by
    have hj : 0 < L + x j := by linarith [hx j]
    field_simp
    ring
  rw [← Finset.sum_sub_distrib]
  simp only [hrepr]
  have hsum : 0 ≤ ∑ j, x j := Finset.sum_nonneg fun j _ ↦ hx j
  constructor
  · exact Finset.sum_nonneg fun j _ ↦ div_nonneg (sq_nonneg _) (by linarith [hx j])
  · calc
      _ ≤ ∑ j, L ^ (-θ) * (x j * x j ^ θ) :=
        Finset.sum_le_sum fun j _ ↦ regularizationTerm_le hL (hx j) hθ₀ hθ₁
      _ ≤ ∑ j, L ^ (-θ) * (x j * (∑ l, x l) ^ θ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hx j) (Finset.single_le_sum (fun i _ ↦ hx i) hj) hθ₀) (hx j))
          (by positivity)
      _ = L ^ (-θ) * (∑ j, x j) ^ (1 + θ) := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, Real.rpow_add' hsum (by linarith : 1 + θ ≠ 0),
          Real.rpow_one]

/-- The key power (L^2 k^5/n) is controlled by the row-energy window,
as used at `cosine.tex:293–296`. The row-energy lower bound is proved from
orthonormality for actual signed DCT frames. -/
theorem window_controls_power {n k ℓ L η : ℝ} (hn : 0 < n) (hk : 0 ≤ k)
    (hkℓ : k ≤ ℓ) (hη : k ^ 2 / n ≤ η) :
    L ^ 2 * k ^ 5 / n ≤ L ^ 2 * k * ℓ ^ 2 * η := by
  have he : 0 ≤ k ^ 2 / n := by positivity
  calc
    _ = L ^ 2 * k * k ^ 2 * (k ^ 2 / n) := by ring
    _ ≤ L ^ 2 * k * ℓ ^ 2 * η := by gcongr

/-- The two-pass rank-only sufficient window follows from the first pass's
row-energy bound and the dimensional identity `ℓ = k + p`. -/
theorem twoPass_window_majorant {n k p L η : ℝ} (hn : 0 < n)
    (hk : 1 ≤ k) (hp : 0 ≤ p) (hη : η ≤ 6 * k ^ 2 / n) :
    L ^ 2 * k * (k + p) ^ 2 * η ≤ 6 * (p + 1) ^ 2 * (L ^ 2 * k ^ 5 / n) := by
  have hkk : 0 ≤ k := by linarith
  have hkp : 0 ≤ k + p := add_nonneg hkk hp
  have hℓ : k + p ≤ (p + 1) * k := by nlinarith [mul_nonneg hp (sub_nonneg.mpr hk)]
  calc
    _ ≤ L ^ 2 * k * (k + p) ^ 2 * (6 * k ^ 2 / n) :=
      mul_le_mul_of_nonneg_left hη (by positivity)
    _ ≤ L ^ 2 * k * ((p + 1) * k) ^ 2 * (6 * k ^ 2 / n) := by gcongr
    _ = _ := by ring

end SketchOrientation.Cosine
