import SketchOrientation.EdgeWalsh
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Central binomial normalization for Walsh misses
-/

open Filter
open scoped Topology

noncomputable section
namespace SketchOrientation.Edge.Walsh

/-- The exact probability of a balanced column of independent fair signs. -/
def balancedProbability (s : ℕ) : ℝ := (s.choose (s / 2) : ℝ) / (2 : ℝ)^s

theorem balancedProbability_two_mul (r : ℕ) :
    balancedProbability (2 * r) = (Nat.centralBinom r : ℝ) / (4 : ℝ)^r := by
  have hr : 2 * r / 2 = r := by omega
  simp only [balancedProbability, hr, Nat.centralBinom, pow_mul]
  norm_num

theorem centralBinom_sqrt_eq_stirling {r : ℕ} (hr : 0 < r) :
    (Nat.centralBinom r : ℝ) / (4 : ℝ)^r * Real.sqrt r =
      Stirling.stirlingSeq (2 * r) / (Stirling.stirlingSeq r)^2 := by
  have hfact : (Nat.centralBinom r : ℝ) * (r.factorial : ℝ)^2 = (2 * r).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * r) (k := r) (by omega)
    rw [show 2 * r - r = r by omega] at h
    rw [Nat.centralBinom, pow_two, ← mul_assoc]
    exact_mod_cast h
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hr'
  have he : 0 < (r : ℝ) / Real.exp 1 := by positivity
  have hf : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hs2 : Real.sqrt (2 * (2 * (r : ℝ))) = 2 * Real.sqrt r := by
    rw [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hp : (2 * (r : ℝ) / Real.exp 1) ^ (2 * r) =
      (4 : ℝ)^r * (((r : ℝ) / Real.exp 1) ^ r) ^ 2 := by
    rw [mul_div_assoc, mul_pow, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num,
      Nat.mul_comm 2 r, pow_mul]
  unfold Stirling.stirlingSeq
  push_cast
  rw [hs2, hp, ← hfact]
  let a : ℝ := ((r : ℝ) / Real.exp 1)^r
  change _ = ((Nat.centralBinom r : ℝ) * (r.factorial : ℝ)^2 /
    (2 * Real.sqrt r * ((4 : ℝ)^r * a^2))) /
      ((r.factorial : ℝ) / (Real.sqrt (2 * r) * a))^2
  have ha : 0 < a := pow_pos he _
  have hs' : 0 < Real.sqrt (2 * (r : ℝ)) := by positivity
  simp only [div_pow, mul_pow, Real.sq_sqrt (show 0 ≤ 2 * (r : ℝ) by positivity)]
  field_simp [hs.ne', ha.ne', hf.ne']
  nlinarith only [congrArg (fun x : ℝ => (Nat.centralBinom r : ℝ) * x) (Real.sq_sqrt hr'.le)]

theorem tendsto_balancedProbability_even_scaled :
    Tendsto (fun r : ℕ => balancedProbability (2 * r) * Real.sqrt (2 * (r : ℝ)))
      atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
  have h₁ := Stirling.tendsto_stirlingSeq_sqrt_pi
  have h₂ := h₁.comp (tendsto_id.const_mul_atTop' (show 0 < (2 : ℕ) by decide))
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have h := h₂.div (h₁.pow 2) (pow_ne_zero 2 hpi.ne')
  have h' := h.const_mul (Real.sqrt 2)
  have hlim : Real.sqrt 2 * (Real.sqrt Real.pi / (Real.sqrt Real.pi)^2) =
      Real.sqrt (2 / Real.pi) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), pow_two]
    field_simp [hpi.ne']
  rw [hlim] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with r hr
  rw [balancedProbability_two_mul, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  change Real.sqrt 2 * (Stirling.stirlingSeq (2*r) / (Stirling.stirlingSeq r)^2) = _
  rw [← centralBinom_sqrt_eq_stirling hr]
  ring

/-- Stirling's asymptotic along any sequence of even support sizes. -/
theorem tendsto_balancedProbability_scaled {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    (he : ∀ᶠ i in atTop, Even (s i)) :
    Tendsto (fun i => balancedProbability (s i) * Real.sqrt (s i : ℝ))
      atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
  have hsdiv : Tendsto (fun i => s i / 2) atTop atTop := by
    refine tendsto_atTop.2 fun k => ?_
    filter_upwards [hs.eventually_ge_atTop (k * 2)] with j hj
    exact Nat.le_div_iff_mul_le (by decide : 0 < 2) |>.mpr hj
  refine (tendsto_balancedProbability_even_scaled.comp hsdiv).congr' ?_
  filter_upwards [he] with j hj
  obtain ⟨r, hr⟩ := hj
  have h : 2 * (s j / 2) = s j := by omega
  change balancedProbability (2 * (s j / 2)) * Real.sqrt (2 * ((s j / 2 : ℕ) : ℝ)) = _
  rw [← Nat.cast_ofNat (R := ℝ) (n := 2), ← Nat.cast_mul, h]

end SketchOrientation.Edge.Walsh
