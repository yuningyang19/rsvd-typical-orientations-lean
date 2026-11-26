import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.Variance

namespace TypicalOrientations

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

variable {U E : Type*} [MeasurableSpace U] [MeasurableSpace E] {m : ℕ}

/-- The empirical average at one common orientation, based on m independent
sketch draws. -/
def empiricalScalarAverage (f : U × E → ℝ) (u : U) (sample : Fin m → E) : ℝ :=
  (∑ i, f (u, sample i)) / (m : ℝ)

theorem measurable_empiricalScalarAverage (f : U × E → ℝ) (hf : Measurable f) :
    Measurable (fun p : U × (Fin m → E) => empiricalScalarAverage f p.1 p.2) :=
  (Finset.measurable_sum _ fun i _ =>
    hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).div_const _

private theorem boundedIntegrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

private theorem centeredSquareIntegrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (a : ℝ) : Integrable (fun x => (f x - a) ^ 2) μ := by
  refine boundedIntegrable μ ((hf.sub_const _).pow_const (2 : ℕ))
    (C := (C + ‖a‖) ^ 2) fun x => ?_
  rw [norm_pow]
  have h := (norm_sub_le (f x) a).trans (add_le_add (hC x) le_rfl)
  exact pow_le_pow_left₀ (norm_nonneg _) h _

private theorem integral_empiricalScalarAverage_samples (μ : Measure E) [IsProbabilityMeasure μ]
    (f : U × E → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ p, ‖f p‖ ≤ C)
    (u : U) (hm : 0 < m) :
    (∫ z : Fin m → E, empiricalScalarAverage f u z ∂Measure.pi (fun _ => μ)) =
      ∫ x, f (u, x) ∂μ := by
  let g : E → ℝ := fun x => f (u, x)
  have hg : Measurable g := hf.comp (measurable_const.prodMk measurable_id)
  have hi (i : Fin m) : Integrable (fun z : Fin m → E => g (z i)) (Measure.pi fun _ => μ) :=
    (measurePreserving_eval (fun _ : Fin m => μ) i).integrable_comp_of_integrable
      (boundedIntegrable μ hg fun x => hC (u, x))
  have he (i : Fin m) :
      (∫ z : Fin m → E, g (z i) ∂Measure.pi (fun _ => μ)) = ∫ x, g x ∂μ :=
    integral_comp_eval hg.aestronglyMeasurable
  have hm' : (m : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr hm.ne')
  unfold empiricalScalarAverage
  change (∫ z : Fin m → E, (∑ i, g (z i)) / (m : ℝ) ∂Measure.pi (fun _ => μ)) =
    ∫ x, g x ∂μ
  rw [integral_div, integral_finsetSum _ fun i _ => hi i]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel_left₀ _ hm']

omit [MeasurableSpace U] [MeasurableSpace E] in
private theorem empiricalScalarAverage_bound (f : U × E → ℝ) (C : ℝ)
    (hC : ∀ p, ‖f p‖ ≤ C) (hm : 0 < m) (u : U) (z : Fin m → E) :
    ‖empiricalScalarAverage f u z‖ ≤ C := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  unfold empiricalScalarAverage
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hm']
  apply (div_le_iff₀ hm').2
  calc
    _ ≤ ∑ i, |f (u, z i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin m, C := Finset.sum_le_sum fun i _ => by
      simpa only [Real.norm_eq_abs] using hC (u, z i)
    _ = _ := by simp [mul_comm]

private theorem integral_empiricalScalarAverage_orientation (ρ : Measure U) [IsProbabilityMeasure ρ]
    (f : U × E → ℝ) (hf : Measurable f) (C a : ℝ) (hC : ∀ p, ‖f p‖ ≤ C)
    (hmean : ∀ x, (∫ u, f (u, x) ∂ρ) = a) (hm : 0 < m) (z : Fin m → E) :
    (∫ u, empiricalScalarAverage f u z ∂ρ) = a := by
  have hm' : (m : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr hm.ne')
  unfold empiricalScalarAverage
  have hI (i : Fin m) : Integrable (fun u => f (u, z i)) ρ :=
    boundedIntegrable ρ (hf.comp (measurable_id.prodMk measurable_const)) (fun u => hC (u, z i))
  rw [integral_div, integral_finsetSum _ fun i _ => hI i]
  simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel_left₀ _ hm']

/-- The Jensen and Fubini step of the general-law proof of Lemma 3.1.
Averaging first over independent sketch draws reduces the orientation
variance of their empirical average. -/
theorem variance_sketch_average_le_empirical (ρ : Measure U) [IsProbabilityMeasure ρ]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : U × E → ℝ) (hf : Measurable f)
    (C a : ℝ) (hC : ∀ p, ‖f p‖ ≤ C) (hmean : ∀ x, (∫ u, f (u, x) ∂ρ) = a)
    {m : ℕ} (hm : 0 < m) :
    Var[fun u => ∫ x, f (u, x) ∂μ; ρ] ≤
      ∫ z : Fin m → E, Var[fun u => empiricalScalarAverage f u z; ρ]
        ∂Measure.pi (fun _ => μ) := by
  let ν := Measure.pi (fun _ : Fin m => μ)
  let A (u : U) := ∫ x, f (u, x) ∂μ
  let B := fun p : U × (Fin m → E) => empiricalScalarAverage f p.1 p.2
  let R := fun p : U × (Fin m → E) => (B p - a) ^ 2
  have hF : StronglyMeasurable (Function.uncurry fun u x => f (u, x)) := hf.stronglyMeasurable
  have hA : Measurable A := hF.integral_prod_right.measurable
  have hB : Measurable B := measurable_empiricalScalarAverage f hf
  have hBl (u : U) (z : Fin m → E) : ‖B (u, z)‖ ≤ C :=
    empiricalScalarAverage_bound f C hC hm u z
  have hAl (u : U) : ‖A u‖ ≤ C := by
    exact (norm_integral_le_of_norm_le_const (ae_of_all _ fun x => hC (u, x))).trans
      (by simp)
  have hACenter : (∫ u, A u ∂ρ) = a := by
    unfold A
    rw [integral_integral_swap (f := fun u x => f (u, x))
      (boundedIntegrable (ρ.prod μ) hf hC)]
    simp only [hmean, integral_const, probReal_univ, one_smul]
  have hBCenter (z : Fin m → E) : (∫ u, B (u, z) ∂ρ) = a :=
    integral_empiricalScalarAverage_orientation ρ f hf C a hC hmean hm z
  have hBSampleCenter (u : U) : (∫ z, B (u, z) ∂ν) = A u :=
    integral_empiricalScalarAverage_samples μ f hf C hC u hm
  have hRi : Integrable R (ρ.prod ν) := centeredSquareIntegrable _ hB
    (fun p => hBl p.1 p.2) a
  have hJ (u : U) : (A u - a)^2 ≤ ∫ z, R (u, z) ∂ν := by
    have hm₁ : Measurable (fun z => B (u, z)) :=
      hB.comp (measurable_const.prodMk measurable_id)
    have hI₀ := boundedIntegrable ν hm₁ (hBl u)
    have hI := hI₀.sub (integrable_const a)
    have hI₂ := centeredSquareIntegrable ν hm₁ (hBl u) a
    have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 : ℕ)) :=
      (show Even (2 : ℕ) by decide).convexOn_pow
    have h := hconv.map_integral_le (by fun_prop) isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) hI hI₂
    change (∫ z, B (u, z) - a ∂ν) ^ 2 ≤ ∫ z, R (u, z) ∂ν at h
    simpa only [integral_sub hI₀ (integrable_const a), hBSampleCenter, integral_const,
      probReal_univ, one_smul] using h
  change Var[A; ρ] ≤ _
  rw [variance_eq_integral hA.aemeasurable, hACenter]
  calc
    _ ≤ ∫ u, ∫ z, R (u, z) ∂ν ∂ρ :=
      integral_mono (centeredSquareIntegrable ρ hA hAl a) hRi.integral_prod_left hJ
    _ = ∫ z, ∫ u, R (u, z) ∂ρ ∂ν := integral_integral_swap hRi
    _ = _ := by
      apply integral_congr_ae
      refine ae_of_all _ fun z => ?_
      change (∫ u, (B (u, z) - a) ^ 2 ∂ρ) = Var[fun u => B (u, z); ρ]
      have hBz : Measurable (fun u => B (u, z)) :=
        hB.comp (measurable_id.prodMk measurable_const)
      rw [variance_eq_integral hBz.aemeasurable, hBCenter]

end

end TypicalOrientations
