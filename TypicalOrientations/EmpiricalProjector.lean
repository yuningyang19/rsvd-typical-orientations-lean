import TypicalOrientations.RotationModel
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

namespace TypicalOrientations

open Filter Matrix MeasureTheory ProbabilityTheory SketchOrientation
open scoped Topology

noncomputable section

variable {n l : ℕ}

/-- An infinite coupling of the successive independent sketch draws. -/
def projectorSampleLaw (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    Measure (ℕ → OrthogonalProjector n l) :=
  Measure.infinitePi fun _ : ℕ => μ

instance (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (projectorSampleLaw μ) := by unfold projectorSampleLaw; infer_instance

def empiricalProjector (m : ℕ) (P : ℕ → OrthogonalProjector n l) : Matrix (Fin n) (Fin n) ℝ :=
  ((m : ℝ)⁻¹) • ∑ i ∈ Finset.range m, (P i).val

theorem empiricalProjector_tendsto (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    ∀ᵐ P ∂projectorSampleLaw μ,
      Tendsto (fun m => empiricalProjector m P) atTop (𝓝 (meanSketchProjector μ)) := by
  have hEntry (i j : Fin n) : ∀ᵐ P ∂projectorSampleLaw μ,
      Tendsto (fun m => empiricalProjector m P i j) atTop (𝓝 (meanSketchProjector μ i j)) := by
    let f := fun P : OrthogonalProjector n l => P.val i j
    let X := fun r (P : ℕ → OrthogonalProjector n l) => f (P r)
    have hf : Measurable f := (continuous_id.matrix_elem i j).measurable.comp measurable_subtype_coe
    have hEval (r : ℕ) : MeasurePreserving (fun P : ℕ → OrthogonalProjector n l => P r)
        (projectorSampleLaw μ) μ := measurePreserving_eval_infinitePi (fun _ : ℕ => μ) r
    have hX (r : ℕ) : Measurable (X r) := hf.comp (hEval r).measurable
    have hi : Integrable (X 0) (projectorSampleLaw μ) :=
      (hEval 0).integrable_comp_of_integrable (integrable_sketchProjector_entry μ i j)
    have hInd : iIndepFun X (projectorSampleLaw μ) :=
      iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ : ℕ => f) fun _ => hf
    have hMap (r : ℕ) : (projectorSampleLaw μ).map (X r) = μ.map f := by
      change (projectorSampleLaw μ).map (f ∘ fun P => P r) = _
      rw [← Measure.map_map hf (hEval r).measurable, (hEval r).map_eq]
    have hIdent (r : ℕ) : IdentDistrib (X r) (X 0) (projectorSampleLaw μ) (projectorSampleLaw μ) :=
      ⟨(hX r).aemeasurable, (hX 0).aemeasurable, (hMap r).trans (hMap 0).symm⟩
    have hm : (∫ P, X 0 P ∂projectorSampleLaw μ) = meanSketchProjector μ i j :=
      by
        change (∫ P, f (P 0) ∂projectorSampleLaw μ) = ∫ P, f P ∂μ
        calc
          _ = ∫ P, f P ∂(projectorSampleLaw μ).map (fun P => P 0) :=
            (integral_map (hEval 0).measurable.aemeasurable hf.aestronglyMeasurable).symm
          _ = _ := congrArg (fun ν => ∫ P, f P ∂ν) (hEval 0).map_eq
    have h := strong_law_ae_real X hi (fun a b hab => hInd.indepFun hab) hIdent
    rw [hm] at h
    filter_upwards [h] with P hP
    apply hP.congr
    intro m
    simp [empiricalProjector, X, f, smul_eq_mul, Matrix.sum_apply, div_eq_inv_mul]
  have hAll : ∀ᵐ P ∂projectorSampleLaw μ, ∀ i j : Fin n,
      Tendsto (fun m => empiricalProjector m P i j) atTop (𝓝 (meanSketchProjector μ i j)) := by
    simp only [ae_all_iff]
    exact hEntry
  filter_upwards [hAll] with P hP
  exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 (hP i)

def projectorOperator :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap

theorem empiricalProjectorNorm_tendsto (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    ∀ᵐ P ∂projectorSampleLaw μ,
      Tendsto (fun m => ‖(empiricalProjector m P).toEuclideanLin.toContinuousLinearMap‖)
        atTop (𝓝 (meanProjectorNorm μ)) := by
  have hNorm : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => ‖(projectorOperator (n := n)) A‖) :=
    ((projectorOperator (n := n)).continuous_of_finiteDimensional).norm
  filter_upwards [empiricalProjector_tendsto μ] with P hP
  exact (hNorm.tendsto _).comp hP

theorem empiricalProjectorNorm_le_one (m : ℕ) (P : ℕ → OrthogonalProjector n l) :
    ‖(empiricalProjector m P).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
  change ‖projectorOperator (empiricalProjector m P)‖ ≤ 1
  rw [empiricalProjector, map_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
  by_cases hm : m = 0
  · simp [hm]
  simp only [map_sum]
  have hP (i : ℕ) : ‖projectorOperator (P i).val‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    change ‖(P i).val.toEuclideanLin u‖ ≤ 1 * ‖u‖
    rw [← orientationRowSpace_starProjection, one_mul]
    exact (orientationRowSpace (P i)).norm_starProjection_apply_le _
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ i ∈ Finset.range m, ‖projectorOperator (P i).val‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (m : ℝ)⁻¹ * ∑ _i ∈ Finset.range m, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hP i) (by positivity)
    _ = 1 := by simp [hm]

theorem empiricalProjector_eq_fin_sum (m : ℕ) (P : ℕ → OrthogonalProjector n l) :
    empiricalProjector m P = ((m : ℝ)⁻¹) • ∑ i : Fin m, (P i.val).val := by
  rw [empiricalProjector, Fin.sum_univ_eq_sum_range (fun i : ℕ => (P i).val)]

theorem empiricalProjectorNorm_pos {m : ℕ} (hm : 0 < m) (hl : 0 < l)
    (P : ℕ → OrthogonalProjector n l) :
    0 < ‖projectorOperator (empiricalProjector m P)‖ := by
  apply lt_of_le_of_ne (norm_nonneg _)
  intro hz
  have hp : projectorOperator (empiricalProjector m P) = 0 := norm_eq_zero.mp hz.symm
  have hE : empiricalProjector m P = 0 := by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.toContinuousLinearMap.injective
    simpa only [projectorOperator, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero] using hp
  have hTrace (Q : OrthogonalProjector n l) : Q.val.trace = (l : ℝ) := by
    rw [← rangeProjector_of_projector Q.val Q.property.1 Q.property.2.1, trace_rangeProjector]
    rw [Q.property.2.2]
  have h := congrArg Matrix.trace hE
  rw [empiricalProjector, trace_smul, trace_sum] at h
  simp only [hTrace, Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_eq_mul, trace_zero] at h
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← mul_assoc, inv_mul_cancel₀ hm', one_mul] at h
  exact (Nat.cast_ne_zero.mpr hl.ne') h

theorem empiricalProjector_direction_le (m : ℕ) (P : ℕ → OrthogonalProjector n l)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i : Fin m, (m : ℝ)⁻¹ * ‖(P i.val).val.toEuclideanLin x‖ ^ 2 ≤
      ‖projectorOperator (empiricalProjector m P)‖ * ‖x‖ ^ 2 := by
  let M := projectorOperator (empiricalProjector m P)
  have hE (i : Fin m) :
      ‖(P i.val).val.toEuclideanLin x‖ ^ 2 = inner ℝ (projectorOperator (P i.val).val x) x := by
    change ‖(P i.val).val.toEuclideanLin x‖ ^ 2 = inner ℝ ((P i.val).val.toEuclideanLin x) x
    rw [← orientationRowSpace_starProjection]
    exact ((orientationRowSpace (P i.val)).re_inner_starProjection_eq_normSq x).symm
  calc
    _ = inner ℝ (M x) x := by
      simp only [M, empiricalProjector_eq_fin_sum, map_smul, map_sum, _root_.smul_apply,
        _root_.sum_apply, inner_smul_left, starRingEnd_apply, star_trivial, sum_inner, hE, Finset.mul_sum]
    _ ≤ ‖M x‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ _ := by
      simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right (M.le_opNorm x) (norm_nonneg x)

/-- The dominated-convergence limit of the random empirical projector norms. -/
theorem integral_empiricalProjectorNorm_tendsto (μ : Measure (OrthogonalProjector n l))
    [IsProbabilityMeasure μ] :
    Tendsto (fun m => ∫ P, ‖(empiricalProjector m P).toEuclideanLin.toContinuousLinearMap‖
      ∂projectorSampleLaw μ) atTop (𝓝 (meanProjectorNorm μ)) := by
  have hNorm : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => ‖(projectorOperator (n := n)) A‖) :=
    ((projectorOperator (n := n)).continuous_of_finiteDimensional).norm
  have hm (m : ℕ) : Measurable (fun P : ℕ → OrthogonalProjector n l => empiricalProjector m P) := by
    have hCoord (j : ℕ) : Measurable (fun P : ℕ → OrthogonalProjector n l => (P j).val) :=
      measurable_subtype_coe.comp
        (show Measurable (fun P : ℕ → OrthogonalProjector n l => P j) from measurable_pi_apply j)
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    simp only [empiricalProjector, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    exact measurable_const.mul (Finset.measurable_sum _ fun r _ =>
      (continuous_id.matrix_elem i j).measurable.comp (hCoord r))
  rw [← show (∫ _ : ℕ → OrthogonalProjector n l, meanProjectorNorm μ ∂projectorSampleLaw μ) =
    meanProjectorNorm μ by simp [projectorSampleLaw]]
  exact tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun m => (hNorm.measurable.comp (hm m)).aestronglyMeasurable)
    (integrable_const _) (fun m => ae_of_all _ fun P => by
      change ‖‖(empiricalProjector m P).toEuclideanLin.toContinuousLinearMap‖‖ ≤ 1
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact empiricalProjectorNorm_le_one m P)
    (empiricalProjectorNorm_tendsto μ)

end

end TypicalOrientations
