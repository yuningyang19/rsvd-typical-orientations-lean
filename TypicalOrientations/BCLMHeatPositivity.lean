import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace TypicalOrientations

open Filter Set
open scoped Topology

/-- The second derivative is nonnegative at the minimum of a smooth orbit. -/
theorem second_derivative_nonneg_of_curve_min {f f' : ℝ → ℝ} {d : ℝ}
    (h₁ : ∀ s, HasDerivAt f (f' s) s) (h₂ : HasDerivAt f' d 0)
    (hMin : ∀ s, f 0 ≤ f s) : 0 ≤ d := by
  have hF : Differentiable ℝ f := fun s => (h₁ s).differentiableAt
  have hLocal : IsLocalMin f 0 := Eventually.of_forall hMin
  have h0 : deriv f 0 = 0 := hLocal.deriv_eq_zero
  have hd : deriv (deriv f) 0 = d := by
    rw [funext (fun s => (h₁ s).deriv)]
    exact h₂.deriv
  by_contra! hneg
  rw [← hd] at hneg
  have hSign := eventually_nhdsWithin_sign_eq_of_deriv_neg hneg h0
  have hRight := deriv_neg_right_of_sign_deriv (nhdsWithin_le_nhds hSign)
  rw [eventually_nhdsWithin_iff] at hRight
  obtain ⟨δ, hδ, hNeg⟩ := Metric.eventually_nhds_iff.mp hRight
  have hδ' : 0 < δ / 2 := half_pos hδ
  obtain ⟨s, hs, hSlope⟩ :=
    exists_deriv_eq_slope (f := f) hδ' hF.continuous.continuousOn hF.differentiableOn
  have hsNear : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
    linarith [hs.2]
  have hD := hNeg hsNear hs.1
  rw [hSlope, sub_zero] at hD
  exact (not_lt_of_ge (div_nonneg (sub_nonneg.mpr (hMin _)) hδ'.le)) hD

section MaximumPrinciple

variable {U : Type*} [TopologicalSpace U] [CompactSpace U]

/-- A compact-space minimum principle. The time derivative is only
required to be nonnegative at spatial global minima. The strictly increasing
barrier settles the case when the minimizing time is the terminal time. -/
theorem heat_lower_bound_of_time_deriv_at_spatial_min
    (h d : ℝ → U → ℝ) (c : ℝ)
    (hCont : ContinuousOn (fun p : ℝ × U => h p.1 p.2) (Ici 0 ×ˢ univ))
    (hD : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => h s x) (d t x) t)
    (hMin : ∀ t, 0 < t → ∀ x, (∀ y, h t x ≤ h t y) → 0 ≤ d t x)
    (h0 : ∀ x, c ≤ h 0 x) :
    ∀ t, 0 ≤ t → ∀ x, c ≤ h t x := by
  intro T hT x
  by_contra! hBad
  let δ := (c - h T x) / (2 * (T+1))
  have hDen : 0 < T+1 := by linarith
  have hδ : 0 < δ := div_pos (sub_pos.mpr hBad) (mul_pos (by norm_num) hDen)
  let b (p : ℝ × U) := h p.1 p.2 + δ * (p.1 + 1)
  have hB : b (T, x) < c := by
    have he : δ * (T+1) = (c - h T x) / 2 := by
      unfold δ
      field_simp [hDen.ne']
    change h T x + δ * (T+1) < c
    rw [he]
    linarith
  let K := Icc 0 T ×ˢ (univ : Set U)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hxK : (T, x) ∈ K := ⟨⟨hT, le_rfl⟩, mem_univ _⟩
  have hC : ContinuousOn b K := by
    have hs : K ⊆ Ici 0 ×ˢ (univ : Set U) := fun _ hy => ⟨hy.1.1, hy.2⟩
    have ha : Continuous (fun p : ℝ × U => δ * (p.1+1)) :=
      continuous_const.mul (continuous_fst.add continuous_const)
    exact (hCont.mono hs).add ha.continuousOn
  obtain ⟨⟨s,y⟩, hs, hA⟩ := hK.exists_isMinOn ⟨(T,x), hxK⟩ hC
  have hUnder : b (s,y) < c := (hA hxK).trans_lt hB
  have hs0 : 0 < s := by
    have hs' : 0 ≤ s := hs.1.1
    by_contra! he
    have he' : s = 0 := le_antisymm he hs'
    rw [he'] at hUnder
    change h 0 y + δ * (0+1) < c at hUnder
    linarith [h0 y]
  have hSpatial (z : U) : h s y ≤ h s z := by
    have hZ : (s,z) ∈ K := ⟨hs.1, mem_univ _⟩
    have hh := hA hZ
    change h s y + δ * (s+1) ≤ h s z + δ * (s+1) at hh
    linarith
  have hP : 0 < d s y + δ := add_pos_of_nonneg_of_pos (hMin s hs0 y hSpatial) hδ
  have hDer : HasDerivAt (fun t => b (t,y)) (d s y + δ) s := by
    have hLinear : HasDerivAt (fun t : ℝ => δ * (t+1)) δ s := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id s).add_const 1).const_mul δ
    exact (hD s hs0 y).add hLinear
  have hTimeMin : IsMinOn (fun t => b (t,y)) (Icc 0 T) s := by
    intro t ht
    exact hA (show (t,y) ∈ K from ⟨ht, mem_univ _⟩)
  have hTan : (0 : ℝ) - s ∈ posTangentConeAt (Icc 0 T) s :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc 0 T).segment_subset hs.1 ⟨le_rfl, hT⟩)
  have hNonneg := hTimeMin.localize.hasFDerivWithinAt_nonneg
    hDer.hasFDerivAt.hasFDerivWithinAt hTan
  change 0 ≤ ((0 : ℝ) - s) * (d s y + δ) at hNonneg
  exact (not_lt_of_ge hNonneg) (mul_neg_of_neg_of_pos (sub_neg.mpr hs0) hP)

/-- Applying the minimum principle to the negative solution gives the
matching uniform upper bound. -/
theorem heat_upper_bound_of_time_deriv_at_spatial_max
    (h d : ℝ → U → ℝ) (c : ℝ)
    (hCont : ContinuousOn (fun p : ℝ × U => h p.1 p.2) (Ici 0 ×ˢ univ))
    (hD : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => h s x) (d t x) t)
    (hMax : ∀ t, 0 < t → ∀ x, (∀ y, h t y ≤ h t x) → d t x ≤ 0)
    (h0 : ∀ x, h 0 x ≤ c) :
    ∀ t, 0 ≤ t → ∀ x, h t x ≤ c := by
  have h := heat_lower_bound_of_time_deriv_at_spatial_min
    (fun t x => -(h t x)) (fun t x => -(d t x)) (-c) hCont.neg
    (fun t ht x => (hD t ht x).neg)
    (fun t ht x hspace => neg_nonneg.mpr (hMax t ht x fun y => neg_le_neg_iff.mp (hspace y)))
    (fun x => neg_le_neg (h0 x))
  intro t ht x
  exact neg_le_neg_iff.mp (h t ht x)

end MaximumPrinciple

end TypicalOrientations
