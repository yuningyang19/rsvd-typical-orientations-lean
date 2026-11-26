import SketchOrientation.GaussianChaosVariance

namespace SketchOrientation

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

private theorem clip_sq_le_rpow {a x r : ℝ} (ha : 0 < a) (hx : 0 ≤ x)
    (hr : 0 < r) (hr₂ : r ≤ 2) : min x a ^ 2 ≤ a ^ (2 - r) * x ^ r := by
  let z := min x a
  have hz : 0 ≤ z := le_min hx ha.le
  change z ^ 2 ≤ _
  rcases eq_or_lt_of_le hz with hz₀ | hz₀
  · rw [← hz₀, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity
  · calc
      z ^ 2 = z ^ (2 - r) * z ^ r := by
        rw [← Real.rpow_add hz₀, sub_add_cancel, Real.rpow_two]
      _ ≤ a ^ (2 - r) * x ^ r := by
        exact mul_le_mul
          (Real.rpow_le_rpow hz (min_le_right _ _) (sub_nonneg.mpr hr₂))
          (Real.rpow_le_rpow hz (min_le_left _ _) hr.le)
          (Real.rpow_nonneg hz _) (Real.rpow_nonneg ha.le _)

private theorem truncation_defect_le_rpow {a x r : ℝ} (ha : 0 < a) (hx : 0 ≤ x)
    (hr : 1 < r) : x - min x a ≤ a ^ (1 - r) * x ^ r := by
  by_cases h : x ≤ a
  · simpa only [min_eq_left h, sub_self] using
      mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hx _)
  · have h' : a < x := lt_of_not_ge h
    calc
      _ ≤ x := sub_le_self _ (le_min hx ha.le)
      _ = x ^ (1 - r) * x ^ r := by
        rw [← Real.rpow_add (ha.trans h'), sub_add_cancel, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos ha h'.le (by linarith))
        (Real.rpow_nonneg hx _)

private theorem memLp_two_of_nonneg_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} {a : ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ a) :
    MemLp f 2 μ := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  refine (integrable_const (a ^ 2)).mono' (hf.pow_const _).aestronglyMeasurable ?_
  exact ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (h0 x) (h1 x) _

private theorem absolute_centered_mean_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x - ∫ t, f t ∂μ| ∂μ) ≤ Real.sqrt (Var[f; μ]) := by
  let c := ∫ t, f t ∂μ
  have h : MemLp (fun x => |f x - c|) 2 μ := (hf.sub (memLp_const c)).norm
  have hh := variance_nonneg (fun x => |f x - c|) μ
  rw [variance_eq_sub h] at hh
  apply Real.le_sqrt_of_sq_le
  rw [variance_eq_integral hf.aemeasurable]
  simpa [sq_abs, c] using sub_nonneg.mp hh

section

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]

set_option maxHeartbeats 1200000 in
/-- The cutoff inequality in the sufficiency proof of Theorem 1.1, before
choosing the cutoff. The variance estimate is for observations of the same
Gaussian draw, with an arbitrary measurable sketch law. -/
theorem gaussianProjection_truncation_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ E)
    (hS : ∀ u : E, Measurable (fun ω => (S ω).starProjection u))
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ)
    (hρ : ∀ u : E, (∫ ω, ‖(S ω).starProjection u‖ ^ 2 ∂μ) ≤ ρ * ‖u‖ ^ 2)
    (Y : Ω → E → ℝ) (hY : Measurable (Function.uncurry Y))
    (hYnonneg : ∀ ω z, 0 ≤ Y ω z)
    (hObs : ∀ ω, Measurable[MeasurableSpace.comap (S ω).orthogonalProjectionOnto inferInstance] (Y ω))
    (Y₀ : E → ℝ) (hY₀Int : Integrable Y₀ (stdGaussian E)) (hY₀nonneg : ∀ z, 0 ≤ Y₀ z)
    (hLaw : ∀ ω, IdentDistrib (Y ω) Y₀ (stdGaussian E) (stdGaussian E))
    {a r M : ℝ} (ha : 0 < a) (hr : 1 < r) (hr₂ : r ≤ 2)
    (hMomentInt : Integrable (fun z => Y₀ z ^ r) (stdGaussian E))
    (hMoment : (∫ z, Y₀ z ^ r ∂stdGaussian E) ≤ M) :
    (∫ z, |(∫ ω, Y ω z ∂μ) - ∫ u, Y₀ u ∂stdGaussian E| ∂stdGaussian E) ≤
       Real.sqrt (ρ * a ^ (2 - r) * M) + 2 * a ^ (1 - r) * M := by
  let γ := stdGaussian E
  let T := fun ω z => min (Y ω z) a
  let T₀ := fun z => min (Y₀ z) a
  let D := fun ω z => Y ω z - T ω z
  let D₀ := fun z => Y₀ z - T₀ z
  let y := fun z => ∫ ω, Y ω z ∂μ
  let t := fun z => ∫ ω, T ω z ∂μ
  let d := fun z => ∫ ω, D ω z ∂μ
  let m := ∫ z, Y₀ z ∂γ
  let mT := ∫ z, T₀ z ∂γ
  let mD := ∫ z, D₀ z ∂γ
  have hT : Measurable (Function.uncurry T) := hY.min measurable_const
  have hTObs (ω : Ω) :
      Measurable[MeasurableSpace.comap (S ω).orthogonalProjectionOnto inferInstance] (T ω) :=
    (hObs ω).min measurable_const
  have hcmeas : Measurable (fun x : ℝ => min x a) := measurable_id.min measurable_const
  have hTLaw (ω : Ω) : IdentDistrib (T ω) T₀ γ γ := (hLaw ω).comp hcmeas
  have hT₀Lp : MemLp T₀ 2 γ := by
    obtain ⟨ω, _⟩ := (ae_of_all μ fun _ => True.intro).exists
    have hm : Measurable (T ω) := hT.comp measurable_prodMk_left
    exact (hTLaw ω).memLp_snd
      (memLp_two_of_nonneg_bound γ hm (fun z => le_min (hYnonneg ω z) ha.le)
        (fun z => min_le_right _ _))
  have hTyLp : MemLp (Function.uncurry T) 2 (μ.prod γ) :=
    memLp_two_of_nonneg_bound (μ.prod γ) hT
      (fun p => le_min (hYnonneg p.1 p.2) ha.le) (fun _ => min_le_right _ _)
  have hjT := hTyLp.integrable (by norm_num)
  have hjY : Integrable (Function.uncurry Y) (μ.prod γ) := by
    apply (integrable_prod_iff hY.aestronglyMeasurable).2
    refine ⟨ae_of_all _ fun ω => (hLaw ω).symm.integrable_snd hY₀Int, ?_⟩
    have hh (ω : Ω) : (∫ z, ‖Y ω z‖ ∂γ) = m := by
      simp_rw [Real.norm_of_nonneg (hYnonneg _ _)]
      exact (hLaw ω).integral_eq
    change Integrable (fun ω => ∫ z, ‖Y ω z‖ ∂γ) μ
    simp only [hh]
    exact integrable_const _
  have hjD : Integrable (Function.uncurry D) (μ.prod γ) := hjY.sub hjT
  have hTLp : MemLp t 2 γ := by
    have hm : Measurable t := hT.stronglyMeasurable.integral_prod_left.measurable
    apply memLp_two_of_nonneg_bound γ hm
    · intro z
      exact integral_nonneg fun ω => le_min (hYnonneg ω z) ha.le
    · intro z
      have ht (ω : Ω) : T ω z ≤ a := min_le_right _ _
      have hLp : MemLp (fun ω => T ω z) 2 μ := memLp_two_of_nonneg_bound μ
        (hT.comp measurable_prodMk_right) (fun ω => le_min (hYnonneg ω z) ha.le) ht
      simpa using integral_mono (hLp.integrable (by norm_num)) (integrable_const a) ht
  have htMean : (∫ z, t z ∂γ) = mT := by
    change (∫ z, ∫ ω, T ω z ∂μ ∂γ) = mT
    rw [← integral_integral_swap hjT]
    have ht' (ω : Ω) : (∫ z, T ω z ∂γ) = mT := (hTLaw ω).integral_eq
    simp only [ht', integral_const, probReal_univ, one_smul]
  have hD₀Int : Integrable D₀ γ := hY₀Int.sub (hT₀Lp.integrable (by norm_num))
  have hmSplit : m = mT + mD := by
    unfold mD D₀
    rw [integral_sub hY₀Int (hT₀Lp.integrable (by norm_num))]
    change m = mT + (m - mT)
    ring
  have hdMean : (∫ z, d z ∂γ) = mD := by
    change (∫ z, ∫ ω, D ω z ∂μ ∂γ) = mD
    rw [← integral_integral_swap hjD]
    have hd' (ω : Ω) : (∫ z, D ω z ∂γ) = mD :=
      ((hLaw ω).comp (measurable_id.sub hcmeas)).integral_eq
    simp only [hd', integral_const, probReal_univ, one_smul]
  have hmDNonneg : 0 ≤ mD := integral_nonneg fun z => sub_nonneg.mpr (min_le_left _ _)
  have hdNonneg (z : E) : 0 ≤ d z := integral_nonneg fun ω => sub_nonneg.mpr (min_le_left _ _)
  have hSplit : y =ᵐ[γ] fun z => t z + d z := by
    filter_upwards [hjY.prod_left_ae, hjT.prod_left_ae] with z hz hz'
    change Integrable (fun ω => Y ω z) μ at hz
    change Integrable (fun ω => T ω z) μ at hz'
    change (∫ ω, Y ω z ∂μ) = (∫ ω, T ω z ∂μ) + ∫ ω, Y ω z - T ω z ∂μ
    rw [integral_sub hz hz']
    ring
  have hdInt : Integrable d γ := hjD.integral_prod_right
  have hyInt : Integrable y γ := hjY.integral_prod_right
  have hAbsInt : Integrable (fun z => |t z - mT|) γ :=
    ((hTLp.integrable (by norm_num)).sub (integrable_const mT)).norm
  have hTri :
      (∫ z, |y z - m| ∂γ) ≤ (∫ z, |t z - mT| ∂γ) + 2 * mD := by
    have hmaj : Integrable (fun z => |t z - mT| + d z + mD) γ :=
      (hAbsInt.add hdInt).add (integrable_const _)
    refine (integral_mono_ae ((hyInt.sub (integrable_const m)).norm) hmaj ?_).trans_eq ?_
    · filter_upwards [hSplit] with z hz
      change |y z - m| ≤ _
      rw [hz, hmSplit, show t z + d z - (mT + mD) = (t z - mT) + (d z - mD) by ring]
      have hbound : |d z - mD| ≤ d z + mD := by
        rw [abs_le]
        constructor <;> linarith [hdNonneg z, hmDNonneg]
      simpa only [add_assoc] using (abs_add_le _ _).trans (add_le_add le_rfl hbound)
    · have hi : Integrable (fun z => |t z - mT| + d z) γ := hAbsInt.add hdInt
      rw [integral_add hi (integrable_const _), integral_add hAbsInt hdInt, hdMean]
      simp only [integral_const, probReal_univ, one_smul]
      ring
  have hClip2 : (∫ z, (T₀ z) ^ 2 ∂γ) ≤ a ^ (2 - r) * M := by
    exact (integral_mono ((memLp_two_iff_integrable_sq hT₀Lp.aestronglyMeasurable).mp hT₀Lp)
      (hMomentInt.const_mul _) (fun z => clip_sq_le_rpow ha (hY₀nonneg z)
        (zero_lt_one.trans hr) hr₂)).trans (by rw [integral_const_mul]; gcongr)
  have hTail : mD ≤ a ^ (1 - r) * M := by
    exact (integral_mono hD₀Int (hMomentInt.const_mul _) (fun z => truncation_defect_le_rpow
      ha (hY₀nonneg z) hr)).trans (by rw [integral_const_mul]; gcongr)
  have hVar : Var[t; γ] ≤ ρ * a ^ (2 - r) * M := by
    have h0 := gaussianProjection_variance_contraction μ S hS ρ hρ₀ hρ
      T hT hTObs T₀ hT₀Lp hTLaw
    apply h0.trans
    rw [variance_eq_sub hT₀Lp, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((sub_le_self _ (sq_nonneg _)).trans hClip2) hρ₀
  have hAbs : (∫ z, |t z - mT| ∂γ) ≤ Real.sqrt (ρ * a ^ (2 - r) * M) := by
    have hh := absolute_centered_mean_le_sqrt_variance γ hTLp
    rw [htMean] at hh
    exact hh.trans (Real.sqrt_le_sqrt hVar)
  exact hTri.trans (by linarith)

end

/-- The cutoff used in Section 3.2 balances the truncated fluctuation and
discarded tail at the stated power of the mean projector. -/
theorem gaussianOrientation_cutoff_bound_eq {ρ K r : ℝ} (hρ : 0 < ρ)
    (hK : 0 < K) (hr : 1 < r) :
    let a := K * ρ ^ (-1 / r)
    Real.sqrt (ρ * a ^ (2 - r) * K ^ r) + 2 * a ^ (1 - r) * K ^ r =
      3 * K * ρ ^ (1 - 1 / r) := by
  let a := K * ρ ^ (-1 / r)
  have hρpow : 0 ≤ ρ ^ (-1 / r) := Real.rpow_nonneg hρ.le _
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  have ht : a ^ (1 - r) * K ^ r = K * ρ ^ (1 - 1 / r) := by
    unfold a
    rw [Real.mul_rpow hK.le hρpow, ← Real.rpow_mul hρ.le,
      show -1 / r * (1 - r) = 1 - 1 / r by field_simp [hr0]; ring]
    calc
      _ = (K ^ (1 - r) * K ^ r) * ρ ^ (1 - 1 / r) := by ring
      _ = _ := by rw [← Real.rpow_add hK, sub_add_cancel, Real.rpow_one]
  have hs : ρ * a ^ (2 - r) * K ^ r = (K * ρ ^ (1 - 1 / r)) ^ 2 := by
    unfold a
    rw [Real.mul_rpow hK.le hρpow, ← Real.rpow_mul hρ.le, mul_pow]
    calc
      _ = (K ^ (2 - r) * K ^ r) * (ρ ^ (1 : ℝ) * ρ ^ (-1 / r * (2 - r))) := by
        rw [Real.rpow_one]
        ring
      _ = K ^ 2 * ρ ^ ((1 - 1 / r) * 2) := by
        rw [← Real.rpow_add hK, ← Real.rpow_add hρ, sub_add_cancel, Real.rpow_two]
        congr 2
        field_simp [hr0]; ring
      _ = _ := by rw [Real.rpow_mul hρ.le, Real.rpow_two]
  change Real.sqrt (ρ * a ^ (2 - r) * K ^ r) + 2 * a ^ (1 - r) * K ^ r = _
  rw [hs, Real.sqrt_sq (mul_nonneg hK.le (Real.rpow_nonneg hρ.le _))]
  rw [mul_assoc, ht]
  ring

end SketchOrientation
