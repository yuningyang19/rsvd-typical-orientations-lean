import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace SketchOrientation

open Matrix

/-- Finite-gap summand in (2.3). -/
noncomputable def angleSummand (Γ t : ℝ) : ℝ := Γ / (1 + (Γ - 1) * t)

/-- The summand's exact defect from the unregularized inverse. -/
theorem angleSummand_defect {Γ t : ℝ} (hΓ : 1 ≤ Γ) (ht : 0 < t) :
    t⁻¹ - angleSummand Γ t = (1 - t) / (t * (1 + (Γ - 1) * t)) := by
  have hden : 0 < 1 + (Γ - 1) * t := by positivity
  unfold angleSummand
  rw [← one_div, div_sub_div _ _ ht.ne' hden.ne']
  congr 1
  ring

/-- The pointwise estimate used to bound the entire finite-gap discrepancy
in the proof leading to (3.8), for the manuscript's range of r. -/
theorem angleSummand_defect_bounds {Γ t r : ℝ} (hΓ : 1 < Γ) (ht : 0 < t)
    (ht₁ : t ≤ 1) (hr : 1 < r) (hr₂ : r ≤ 2) :
    0 ≤ t⁻¹ - angleSummand Γ t ∧
      t⁻¹ - angleSummand Γ t ≤ (Γ - 1) ^ (1 - r) * t ^ (-r) := by
  let x := (Γ - 1) * t
  have hΓ' : 0 < Γ - 1 := sub_pos.mpr hΓ
  have hx : 0 < x := mul_pos hΓ' ht
  have hden : 0 < 1 + x := by positivity
  have hpow : x ^ (r - 1) ≤ 1 + x := by
    by_cases hx₁ : x ≤ 1
    · have h : x ^ (r - 1) ≤ 1 :=
        Real.rpow_le_one hx.le hx₁ (sub_nonneg.mpr hr.le)
      linarith
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx₁)
        (show r - 1 ≤ 1 by linarith)
      rw [Real.rpow_one] at h
      linarith
  rw [angleSummand_defect hΓ.le ht]
  change 0 ≤ (1 - t) / (t * (1 + x)) ∧
    (1 - t) / (t * (1 + x)) ≤ (Γ - 1) ^ (1 - r) * t ^ (-r)
  refine ⟨div_nonneg (sub_nonneg.mpr ht₁) (mul_nonneg ht.le hden.le), ?_⟩
  calc
    _ ≤ 1 / (t * (1 + x)) :=
      div_le_div_of_nonneg_right (by linarith) (mul_nonneg ht.le hden.le)
    _ ≤ 1 / (t * x ^ (r - 1)) :=
      one_div_le_one_div_of_le (mul_pos ht (Real.rpow_pos_of_pos hx _))
        (mul_le_mul_of_nonneg_left hpow ht.le)
    _ = _ := by
      rw [one_div, mul_inv, ← Real.rpow_neg hx.le, show -(r - 1) = 1 - r by ring]
      rw [show x = (Γ - 1) * t from rfl, Real.mul_rpow hΓ'.le ht.le]
      rw [← Real.rpow_neg_one, mul_left_comm, ← Real.rpow_add ht, show -1 + (1 - r) = -r by ring]

/-- Monotonicity across all finite gaps, with the zero-cosine case included. -/
theorem angleSummand_monotone {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    MonotoneOn (fun Γ => angleSummand Γ t) (Set.Ici 1) := by
  intro Γ₀ hΓ₀ Γ₁ hΓ₁ h
  have hden₀ : 0 < 1 + (Γ₀ - 1) * t := by
    have hΓ₀' : 0 ≤ Γ₀ - 1 := sub_nonneg.mpr hΓ₀
    positivity
  have hden₁ : 0 < 1 + (Γ₁ - 1) * t := by
    have hΓ₁' : 0 ≤ Γ₁ - 1 := sub_nonneg.mpr hΓ₁
    positivity
  unfold angleSummand
  apply (div_le_div_iff₀ hden₀ hden₁).mpr
  have hp := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr ht₁)
  nlinarith

/-- Algebra before taking the conditional expectation in (2.9).
The symmetric radial factor is already fixed in this deterministic identity. -/
theorem radial_trace_identity {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (P : Matrix n n ℝ) (V : Matrix n k ℝ) (H : Matrix k k ℝ)
    (hH : Hᵀ = H) :
    (((V * H)ᵀ * P * (V * H))⁻¹).trace =
      ((Vᵀ * P * V)⁻¹ * (H⁻¹ * H⁻¹)).trace := by
  rw [transpose_mul, hH]
  have hfactor : H * Vᵀ * P * (V * H) = H * (Vᵀ * P * V) * H := by
    simp only [Matrix.mul_assoc]
  rw [hfactor, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.trace_mul_comm H⁻¹, Matrix.mul_assoc]

end SketchOrientation
