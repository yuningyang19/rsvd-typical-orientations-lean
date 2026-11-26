import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace SketchOrientation

open MeasureTheory Filter Set
open scoped Topology

private theorem mixed_term_rpow_le (x y : ℝ) :
    (|x * y| : ℝ) ^ ((10 : ℝ) / 9) ≤
      (|x| : ℝ) ^ ((5 : ℝ) / 4) + (|y| : ℝ) ^ (10 : ℝ) := by
  have hpq : ((9 : ℝ) / 8).HolderConjugate (9 : ℝ) := by
    apply Real.holderConjugate_iff.mpr
    norm_num
  rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have h := Real.young_inequality_of_nonneg (Real.rpow_nonneg (abs_nonneg x) ((10 : ℝ) / 9))
    (Real.rpow_nonneg (abs_nonneg y) ((10 : ℝ) / 9)) hpq
  rw [← Real.rpow_mul (abs_nonneg x), ← Real.rpow_mul (abs_nonneg y)] at h
  norm_num at h
  rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact h.trans (add_le_add (div_le_self (Real.rpow_nonneg (abs_nonneg x) ((5 : ℝ) / 4))
    (show (1 : ℝ) ≤ 9 / 8 by norm_num))
    (div_le_self (pow_nonneg (abs_nonneg y) (10 : ℕ)) (show (1 : ℝ) ≤ 9 by norm_num)))

private theorem abs_le_one_add_rpow_ten (y : ℝ) : |y| ≤ 1 + (|y| : ℝ) ^ (10 : ℝ) := by
  by_cases h : |y| ≤ 1
  · exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
  · have h₁ : 1 ≤ |y| := le_of_not_ge h
    have hp := Real.rpow_le_rpow_of_exponent_le h₁ (by norm_num : (1 : ℝ) ≤ 10)
    rw [Real.rpow_one] at hp
    exact hp.trans (le_add_of_nonneg_left zero_le_one)

set_option maxHeartbeats 1400000 in
private theorem mixed_expectation_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    {C D δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T)
    (hMX : Integrable (fun z => (|X z| : ℝ) ^ ((5 : ℝ) / 4)) μ)
    (hMY : Integrable (fun z => (|Y z| : ℝ) ^ (10 : ℝ)) μ)
    (hC : (∫ z, (|X z| : ℝ) ^ ((5 : ℝ) / 4) ∂μ) ≤ C)
    (hD : (∫ z, (|Y z| : ℝ) ^ (10 : ℝ) ∂μ) ≤ D) :
    (∫ z, |X z * Y z| ∂μ) ≤
      δ * (1 + D) + T * μ.real {z | δ ≤ |X z|} + T ^ (1 - (10 : ℝ) / 9) * (C + D) := by
  let A := {z | δ ≤ |X z|}
  let U := fun z => (|X z| : ℝ) ^ ((5 : ℝ) / 4)
  let V := fun z => (|Y z| : ℝ) ^ (10 : ℝ)
  let w := T ^ (1 - (10 : ℝ) / 9)
  let H := fun z => δ * (1 + V z) + A.indicator (fun _ => T) z + w * (U z + V z)
  have hXa : Measurable (fun z => |X z|) := by simpa only [Real.norm_eq_abs] using hX.norm
  have hA : MeasurableSet A := measurableSet_le measurable_const hXa
  have hw : 0 ≤ w := Real.rpow_nonneg hT.le _
  have h₁ : Integrable (fun z => δ * (1 + V z)) μ :=
    ((integrable_const 1).add hMY).const_mul _
  have h₂ : Integrable (A.indicator (fun _ => T)) μ := (integrable_const _).indicator hA
  have h₃ : Integrable (fun z => w * (U z + V z)) μ := (hMX.add hMY).const_mul _
  have hHI : Integrable H μ := (h₁.add h₂).add h₃
  have hH (z : Ω) : |X z * Y z| ≤ H z := by
    have hU : 0 ≤ U z := Real.rpow_nonneg (abs_nonneg _) _
    have hV : 0 ≤ V z := Real.rpow_nonneg (abs_nonneg _) _
    have hP : 0 ≤ δ * (1 + V z) := by positivity
    have hR : 0 ≤ w * (U z + V z) := by positivity
    have hInd : 0 ≤ A.indicator (fun _ => T) z :=
      Set.indicator_nonneg (fun _ _ => hT.le) _
    by_cases hsmall : |X z| ≤ δ
    · have h := mul_le_mul hsmall (abs_le_one_add_rpow_ten (Y z)) (abs_nonneg _) hδ.le
      rw [abs_mul]
      exact h.trans (by unfold H; linarith)
    · by_cases hz : |X z * Y z| ≤ T
      · have hzA : z ∈ A := le_of_not_ge hsmall
        unfold H
        rw [Set.indicator_of_mem hzA]
        linarith
      · have hb : T ≤ |X z * Y z| := le_of_not_ge hz
        have hPos : 0 < |X z * Y z| := hT.trans_le hb
        let q := (10 : ℝ) / 9
        have hq : 0 ≤ q - 1 := by norm_num [q]
        have hMono := Real.rpow_le_rpow hT.le hb hq
        have hRpow : |X z * Y z| ≤ w * (|X z * Y z| : ℝ) ^ q := by
          unfold w
          rw [show 1 - (10 : ℝ) / 9 = -(q - 1) by dsimp [q]; ring, Real.rpow_neg hT.le,
            ← div_eq_inv_mul]
          apply (le_div_iff₀ (Real.rpow_pos_of_pos hT _)).2
          refine (mul_le_mul_of_nonneg_left hMono (abs_nonneg _)).trans_eq ?_
          calc
            _ = (|X z * Y z| : ℝ) ^ (1 : ℝ) * (|X z * Y z| : ℝ) ^ (q - 1) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hPos, show 1 + (q - 1) = q by ring]
        have hR' := hRpow.trans (mul_le_mul_of_nonneg_left (mixed_term_rpow_le (X z) (Y z)) hw)
        exact hR'.trans (by unfold H; linarith)
  have hInt : Integrable (fun z => |X z * Y z|) μ := by
    have hm : Measurable (fun z => |X z * Y z|) := by
      simpa only [Real.norm_eq_abs, Pi.mul_apply] using (hX.mul hY).norm
    refine hHI.mono' hm.aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    exact hH z
  refine (integral_mono hInt hHI hH).trans ?_
  change (∫ z, (δ * (1 + V z) + A.indicator (fun _ => T) z) + w * (U z + V z) ∂μ) ≤ _
  have h₁₂ : Integrable (fun z => δ * (1 + V z) + A.indicator (fun _ => T) z) μ := h₁.add h₂
  rw [integral_add h₁₂ h₃]
  rw [integral_add h₁ h₂, integral_const_mul, integral_add (integrable_const 1) hMY,
    integral_const, probReal_univ, one_smul, integral_indicator_const _ hA, smul_eq_mul,
    integral_const_mul, integral_add hMX hMY]
  rw [mul_comm (μ.real A) T]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hD) hδ.le) le_rfl)
    (mul_le_mul_of_nonneg_left (add_le_add hC hD) hw)

/-- Probability convergence of the first factor and uniform moment bounds
on both factors force their mixed expectation to converge to zero. -/
theorem mixed_expectation_tendsto_zero {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X Y : ∀ i, Ω i → ℝ) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {C D : ℝ} (_hC₀ : 0 ≤ C) (hD₀ : 0 ≤ D)
    (hMX : ∀ i, Integrable (fun z => (|X i z| : ℝ) ^ ((5 : ℝ) / 4)) (μ i) ∧
      (∫ z, (|X i z| : ℝ) ^ ((5 : ℝ) / 4) ∂μ i) ≤ C)
    (hMY : ∀ i, Integrable (fun z => (|Y i z| : ℝ) ^ (10 : ℝ)) (μ i) ∧
      (∫ z, (|Y i z| : ℝ) ^ (10 : ℝ) ∂μ i) ≤ D)
    (hP : ∀ δ : ℝ, 0 < δ → Tendsto (fun i => (μ i).real {z | δ ≤ |X i z|}) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ z, X i z * Y i z ∂μ i) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (3 * (1 + D))
  have hδ : 0 < δ := by positivity
  have hδε : δ * (1 + D) = ε / 3 := by
    unfold δ
    field_simp
  have hlim : Tendsto (fun T : ℝ => T ^ (1 - (10 : ℝ) / 9) * (C + D)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 9)).mul_const (C + D)
    convert h using 2 <;> norm_num
  have ht : ∀ᶠ T : ℝ in atTop, 0 < T ∧ T ^ (1 - (10 : ℝ) / 9) * (C + D) < ε / 3 :=
    (eventually_gt_atTop 0).and (hlim.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨T, hT, htε⟩ := ht.exists
  have hP' := (hP δ hδ).const_mul T
  simp only [mul_zero] at hP'
  filter_upwards [hP'.eventually (gt_mem_nhds (by linarith : 0 < ε / 3))] with i hi
  rw [Real.dist_eq, sub_zero]
  have hI := mixed_expectation_abs_bound (μ i) (X i) (Y i) (hX i) (hY i) hδ hT
    (hMX i).1 (hMY i).1 (hMX i).2 (hMY i).2
  have h := (abs_integral_le_integral_abs (f := fun z => X i z * Y i z)).trans hI
  rw [hδε] at h
  linarith

end SketchOrientation
