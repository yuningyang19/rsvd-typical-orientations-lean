import TypicalOrientations.FiniteRotationVariance
import TypicalOrientations.EmpiricalJensen
import TypicalOrientations.EmpiricalProjector
import SketchOrientation.GaussianTailGram

namespace TypicalOrientations

open Filter Matrix MeasureTheory ProbabilityTheory Set SketchOrientation
open scoped ProbabilityTheory Topology

noncomputable section

variable {n l : ℕ}

set_option maxHeartbeats 900000 in
/-- General-law step of Lemma 3.1, conditional on the rotation-group
product inequality and with the common marginal of the rotations explicit. -/
theorem variance_rotation_of_brascampLieb (hBL : RotationBrascampLieb)
    (hl' : 0 < l) (hl : l ≤ n)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ]
    (f : OrthogonalProjector n l → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ S, |f S| ≤ B)
    (hLaw : ∀ P : OrthogonalProjector n l,
      IdentDistrib (fun U => f (rotateProjector U P)) f
        (specialOrientationLaw n) (haarSketchProjectorLaw hl)) :
    Var[fun U => ∫ P, f (rotateProjector U P) ∂μ; specialOrientationLaw n] ≤
      2 * meanProjectorNorm μ * Var[f; haarSketchProjectorLaw hl] := by
  let S := OrthogonalProjector n l
  let U := Matrix (Fin n) (Fin n) ℝ
  let η := specialOrientationLaw n
  let ν := haarSketchProjectorLaw hl
  let F := fun (z : U × S) => f (rotateProjector z.1 z.2)
  let v := Var[f; ν]
  let a := ∫ P, f P ∂ν
  let A := fun u : U => ∫ P, F (u, P) ∂μ
  have hF : Measurable F := hf.comp measurable_rotateProjector
  have hc (P : S) : (∫ u, F (u, P) ∂η) = a := (hLaw P).integral_eq
  have hFn (z : U × S) : ‖F z‖ ≤ B := by simpa only [Real.norm_eq_abs] using hB _
  have hLim := (integral_empiricalProjectorNorm_tendsto μ).const_mul (2 * v)
  have hV : ∀ m : ℕ, 0 < m → Var[A; η] ≤ (2 * v) *
      (∫ P, ‖(empiricalProjector m P).toEuclideanLin.toContinuousLinearMap‖ ∂projectorSampleLaw μ) := by
    intro m hm
    let τ : Measure (Fin m → S) := Measure.pi (fun _ => μ)
    let E := fun P : Fin m → S => ((m : ℝ)⁻¹) • ∑ i, (P i).val
    let r := fun P : Fin m → S => ‖projectorOperator (E P)‖
    let pref := fun (P : ℕ → S) (i : Fin m) => P i.val
    have hpref : Measurable pref := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
    have hpush : (projectorSampleLaw μ).map pref = τ :=
      infiniteProduct_map_embedding μ (Fin.valEmbedding (n := m))
    have he (P : ℕ → S) : E (pref P) = empiricalProjector m P :=
      (empiricalProjector_eq_fin_sum m P).symm
    have hNorm : Continuous (fun M : U => ‖projectorOperator M‖) :=
      (projectorOperator (n := n)).continuous_of_finiteDimensional.norm
    have hr : Measurable r := by
      apply hNorm.measurable.comp
      apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      simp only [E, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
      exact measurable_const.mul (Finset.measurable_sum _ fun r _ =>
        (continuous_id.matrix_elem i j).measurable.comp
          (measurable_subtype_coe.comp (measurable_pi_apply r)))
    let ext := fun (P : Fin m → S) (i : ℕ) => if hi : i < m then P ⟨i, hi⟩ else P ⟨0, hm⟩
    have hout (P : Fin m → S) : pref (ext P) = P := by
      funext i
      simp [pref, ext, i.isLt]
    have ht (P : Fin m → S) : empiricalProjector m (ext P) = E P := by
      rw [← he, hout]
    have hR (P : Fin m → S) : r P ≤ 1 := by
      unfold r
      rw [← ht]
      exact empiricalProjectorNorm_le_one m (ext P)
    have hRI : Integrable (fun P => (2 * v) * r P) τ :=
      (Integrable.of_bound hr.aestronglyMeasurable 1 (ae_of_all _ fun P => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hR P)).const_mul _
    have hPt (P : Fin m → S) :
        Var[fun u => empiricalScalarAverage F u P; η] ≤ (2 * v) * r P := by
      have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      have hInv : 0 < (m : ℝ)⁻¹ := inv_pos.mpr hm0
      have hSum : (∑ _ : Fin m, (m : ℝ)⁻¹) = 1 := by simp [hm.ne']
      have hDir (x : EuclideanSpace ℝ (Fin n)) :
          ∑ i, (m : ℝ)⁻¹ * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ r P * ‖x‖ ^ 2 := by
        have hcoord (i : Fin m) : ext P i.val = P i := congrFun (hout P) i
        simpa only [hcoord, ht, r] using empiricalProjector_direction_le m (ext P) x
      have hRpos : 0 < r P := by
        unfold r
        rw [← ht]
        exact empiricalProjectorNorm_pos hm hl' (ext P)
      have hb := variance_finite_rotation_of_brascampLieb hBL (hl'.trans_le hl) hl P
        (fun _ => (m : ℝ)⁻¹) (fun _ => hInv) hSum (r P) hRpos hDir f hf B hB ν
        (fun i => hLaw (P i))
      have hEq : (fun u => empiricalScalarAverage F u P) =
          fun u => ∑ i, (m : ℝ)⁻¹ * f (rotateProjector u (P i)) := by
        funext u
        simp [empiricalScalarAverage, F, ← Finset.mul_sum, div_eq_inv_mul]
      rw [hEq]
      exact hb.trans_eq (by unfold v; ring)
    calc
      _ ≤ ∫ P : Fin m → S, Var[fun u => empiricalScalarAverage F u P; η] ∂τ :=
        variance_sketch_average_le_empirical η μ F hF B a hFn hc hm
      _ ≤ ∫ P : Fin m → S, (2 * v) * r P ∂τ :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => variance_nonneg _ _)
          hRI (ae_of_all _ hPt)
      _ = _ := by
        rw [integral_const_mul, ← hpush, integral_map hpref.aemeasurable hr.aestronglyMeasurable]
        simp only [r, he]
        rfl
  have hV' : Var[A; η] ≤ (2 * v) * meanProjectorNorm μ := by
    apply ge_of_tendsto hLim
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact hV m hm
  exact hV'.trans_eq (by unfold v; ring)

end

end TypicalOrientations
