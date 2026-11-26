import TypicalOrientations.CumulantComparison
import TypicalOrientations.RotationProduct

namespace TypicalOrientations

open Filter Matrix MeasureTheory ProbabilityTheory Set SketchOrientation
open scoped ProbabilityTheory Topology

private theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x)

/-- The finite-sketch-law step of Lemma 3.1. The product inequality used by
the paper is supplied explicitly. The common marginal is that of each
individual rotated plane, and all summands use one rotation U. -/
theorem variance_finite_rotation_of_brascampLieb (hBL : RotationBrascampLieb)
    {n l m : ℕ} (hn : 0 < n) (hl : l ≤ n)
    (P : Fin m → OrthogonalProjector n l) (w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) (hwSum : ∑ i, w i = 1)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hDir : ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i, w i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ρ * ‖x‖ ^ 2)
    (f : OrthogonalProjector n l → ℝ) (hf : Measurable f)
    (B : ℝ) (hfB : ∀ S, |f S| ≤ B)
    (ν : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure ν]
    (hLaw : ∀ i, IdentDistrib (fun U => f (rotateProjector U (P i))) f
      (specialOrientationLaw n) ν) :
    Var[fun U => ∑ i, w i * f (rotateProjector U (P i)); specialOrientationLaw n] ≤
      2 * ρ * Var[f; ν] := by
  classical
  let μ := specialOrientationLaw n
  let R := fun (i : Fin m) (U : Matrix (Fin n) (Fin n) ℝ) => f (rotateProjector U (P i))
  let A := fun U => ∑ i, w i * R i U
  have hRm (i : Fin m) : Measurable (R i) :=
    hf.comp (measurable_rotateProjector.comp (measurable_id.prodMk measurable_const))
  have hAm : Measurable A :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (hRm i)
  have hAB (U) : |A U| ≤ B := by
    change |∑ i, w i * R i U| ≤ B
    calc
      _ ≤ ∑ i, |w i * R i U| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, w i * B := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_pos (hw i)]
        exact mul_le_mul_of_nonneg_left (hfB _) (hw i).le
      _ = B := by rw [← Finset.sum_mul, hwSum, one_mul]
  have hMean : (∫ U, A U ∂μ) = ∫ S, f S ∂ν := by
    change (∫ U, ∑ i, w i * R i U ∂μ) = _
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul]
      have hh (i) : (∫ U, R i U ∂μ) = ∫ S, f S ∂ν := (hLaw i).integral_eq
      simp_rw [hh]
      rw [← Finset.sum_mul, hwSum, one_mul]
    · intro i _
      exact (integrable_of_abs_le μ (hRm i) (fun U => hfB _)).const_mul _
  have hρ2 : 0 < 2 * ρ := by positivity
  apply variance_le_of_cgf_comparison hAm hf (2 * ρ) B B hρ2 hAB hfB hMean
  intro t
  let H := fun S => Real.exp (t * (2 * ρ * f S))
  have hH : Measurable H := ((measurable_const.mul (measurable_const.mul hf))).exp
  have hHbound : ∀ S, H S ≤ Real.exp (|t * (2 * ρ)| * B) := by
    intro S
    apply Real.exp_le_exp.mpr
    rw [← mul_assoc]
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hfB S) (abs_nonneg _))
  have hc (x : EuclideanSpace ℝ (Fin n)) :
      ∑ i, w i / ρ * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [div_mul_eq_mul_div, ← Finset.sum_div] using
      (div_le_iff₀ hρ).2 ((hDir x).trans_eq (mul_comm _ _))
  have hBL' := hBL n l m hn hl P (fun i => w i / ρ) (fun _ => H)
      (fun i => div_pos (hw i) hρ) hc (fun _ => hH)
      (fun _ _ => (Real.exp_pos _).le) (fun _ => ⟨_, hHbound⟩)
  have hMarg (i : Fin m) :
      (∫ U, H (rotateProjector U (P i)) ∂μ) =
      mgf (fun S => (2 * ρ) * f S) ν t :=
    ((hLaw i).comp (show Measurable (fun x : ℝ => Real.exp (t * (2 * ρ * x))) by fun_prop)).integral_eq
  have hProd (U : Matrix (Fin n) (Fin n) ℝ) :
      ∏ i, H (rotateProjector U (P i)) ^ (w i / ρ / 2) =
        Real.exp (t * A U) := by
    simp only [H, ← Real.exp_mul, ← Real.exp_sum, A, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    unfold R
    field_simp [hρ.ne']
  let b := mgf (fun S => (2 * ρ) * f S) ν t
  have hb : 0 < b := by
    apply mgf_pos
    exact integrable_of_abs_le ν hH (fun S => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact hHbound S)
  have ha : 0 < mgf A μ t := by
    apply mgf_pos
    have hm : Measurable (fun U => Real.exp (t * A U)) := (measurable_const.mul hAm).exp
    refine integrable_of_abs_le μ hm (B := Real.exp (|t| * B)) fun U => ?_
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hAB U) (abs_nonneg _))
  have hMgf : mgf A μ t ≤ b ^ (1 / (2 * ρ)) := by
    change (∫ U, ∏ i, H (rotateProjector U (P i)) ^ (w i / ρ / 2) ∂μ) ≤
      ∏ i, (∫ U, H (rotateProjector U (P i)) ∂μ) ^ (w i / ρ / 2) at hBL'
    simp_rw [hProd, hMarg] at hBL'
    change mgf A μ t ≤ ∏ i, b ^ (w i / ρ / 2) at hBL'
    rw [← Real.rpow_sum_of_pos hb] at hBL'
    simp_rw [← Finset.sum_div, hwSum] at hBL'
    convert hBL' using 2
    field_simp [hρ.ne']
  have hLog := Real.log_le_log ha hMgf
  rw [Real.log_rpow hb] at hLog
  change (2 * ρ) * Real.log (mgf A μ t) ≤ Real.log b
  rw [mul_comm (2 * ρ)]
  apply (le_div_iff₀ hρ2).1
  simpa [div_eq_mul_inv, mul_comm] using hLog

end TypicalOrientations
