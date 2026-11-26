import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import SketchOrientation.GammaMoments

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace

/-- Orthogonal projection of a standard Gaussian has the standard Gaussian law
on the target subspace. -/
theorem stdGaussian_map_projection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (S : Submodule ℝ E) :
    (stdGaussian E).map S.orthogonalProjectionOnto = stdGaussian S := by
  have : IsProbabilityMeasure ((stdGaussian E).map S.orthogonalProjectionOnto) :=
    Measure.isProbabilityMeasure_map S.orthogonalProjectionOnto.continuous.measurable.aemeasurable
  apply Measure.ext_of_charFun (E := S)
  funext t
  rw [charFun_apply, integral_map S.orthogonalProjectionOnto.continuous.measurable.aemeasurable
    (Measurable.aestronglyMeasurable (by fun_prop))]
  simp_rw [S.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← charFun_apply (μ := stdGaussian E) (↑t : E), charFun_stdGaussian,
    charFun_stdGaussian]
  rfl

private theorem stdGaussian_pi_density {ι : Type*} [Fintype ι] :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi]
  have hi : ∀ i, Integrable (gaussianPDFReal 0 1) (volume.restrict (s i)) :=
    fun _ => (integrable_gaussianPDFReal _ _).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hi)
    (ae_of_all _ fun x => Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
  · simp_rw [gaussianReal_apply_eq_integral _ one_ne_zero]
  · exact fun i _ => integral_nonneg (gaussianPDFReal_nonneg _ _)

/-- The standard Euclidean Gaussian has radial density with respect to volume. -/
theorem stdGaussian_euclidean_density {ι : Type*} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity (fun x => ENNReal.ofReal
        (((Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι * Real.exp (-‖x‖ ^ 2 / 2))) := by
  classical
  rw [← map_pi_eq_stdGaussian, stdGaussian_pi_density]
  ext s hs
  set e := (MeasurableEquiv.toLp 2 (ι → ℝ))
  have hp : MeasurePreserving e := PiLp.volume_preserving_toLp ι
  have heq : (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) = e := rfl
  rw [heq, e.map_apply s, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs, ← hp.setLIntegral_comp_preimage_emb e.measurableEmbedding]
  apply lintegral_congr
  intro x
  congr 1
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ← Real.exp_sum, ← Finset.sum_div,
    ← Finset.sum_neg_distrib, EuclideanSpace.real_norm_sq_eq]
  rfl

private theorem integral_stdGaussian_radial {ν : ℕ} [NeZero ν] (f : ℝ → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin ν), f (‖x‖ ^ 2) ∂stdGaussian _) =
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ ν * ν *
        (volume : Measure (EuclideanSpace ℝ (Fin ν))).real (Metric.ball 0 1) / 2) *
        ∫ y in Ioi 0, y ^ ((ν : ℝ) / 2 - 1) * Real.exp (-(y / 2)) * f y := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ ν
  let ρ : ℝ → ℝ := fun y => y ^ ((ν : ℝ) / 2 - 1) * Real.exp (-(y / 2)) * f y
  have hv : (∫ x : EuclideanSpace ℝ (Fin ν), f (‖x‖ ^ 2) ∂stdGaussian _) =
      c * ∫ x : EuclideanSpace ℝ (Fin ν), Real.exp (-‖x‖ ^ 2 / 2) * f (‖x‖ ^ 2) := by
    rw [stdGaussian_euclidean_density, integral_withDensity_eq_integral_toReal_smul]
    · simp only [Fintype.card_fin]
      change (∫ x : EuclideanSpace ℝ (Fin ν),
        (ENNReal.ofReal (c * Real.exp (-‖x‖ ^ 2 / 2))).toReal • f (‖x‖ ^ 2)) = _
      have hc (x : EuclideanSpace ℝ (Fin ν)) : 0 ≤ c * Real.exp (-‖x‖ ^ 2 / 2) := by
        unfold c
        positivity
      simp_rw [ENNReal.toReal_ofReal (hc _), smul_eq_mul, mul_assoc, integral_const_mul]
    · fun_prop
    · exact ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hν : 1 ≤ ν := Nat.one_le_iff_ne_zero.mpr (NeZero.ne ν)
  have hsubst :
      (∫ y in Ioi (0 : ℝ), y ^ (ν - 1) * (Real.exp (-(y ^ 2) / 2) * f (y ^ 2))) =
        (∫ y in Ioi (0 : ℝ), ρ y) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    rw [mul_comm, ← integral_const_mul,
      ← integral_comp_rpow_Ioi_of_pos (g := ρ) (by norm_num : (0 : ℝ) < 2)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy' : 0 < y := hy
    dsimp only [ρ, smul_eq_mul]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      ← Real.rpow_mul hy'.le]
    simp only [Real.rpow_two, neg_div]
    rw [← Real.rpow_natCast, Nat.cast_sub hν, Nat.cast_one]
    rw [show (2 : ℝ) * ((ν : ℝ) / 2 - 1) = (ν : ℝ) - 1 - 1 by ring,
      Real.rpow_sub hy' ((ν : ℝ) - 1) 1, Real.rpow_one]
    field_simp
  rw [hv, integral_fun_norm_addHaar volume (fun y => Real.exp (-(y ^ 2) / 2) * f (y ^ 2))]
  simp only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  rw [hsubst]
  unfold c ρ
  ring

private theorem integral_chiSquare_radial {ν : ℕ} (hν : 0 < ν) (f : ℝ → ℝ) :
    (∫ y, f y ∂chiSquareLaw ν) =
      ((1 / 2 : ℝ) ^ ((ν : ℝ) / 2) / Real.Gamma ((ν : ℝ) / 2)) *
        ∫ y in Ioi 0, y ^ ((ν : ℝ) / 2 - 1) * Real.exp (-(y / 2)) * f y := by

  have hν' : (0 : ℝ) < ν := Nat.cast_pos.mpr hν
  have ha : 0 < (ν : ℝ) / 2 := by positivity
  have hp : Measurable (gammaPDF ((ν : ℝ) / 2) (1 / 2)) :=
    (measurable_gammaPDFReal _ _).ennreal_ofReal
  unfold chiSquareLaw gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hp (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha (by norm_num : (0 : ℝ) < 1 / 2) _), smul_eq_mul]
  let C := (1 / 2 : ℝ) ^ ((ν : ℝ) / 2) / Real.Gamma ((ν : ℝ) / 2)
  have heq : (fun y => gammaPDFReal ((ν : ℝ) / 2) (1 / 2) y * f y) =
      (Ici (0 : ℝ)).indicator
        (fun y => C * (y ^ ((ν : ℝ) / 2 - 1) * Real.exp (-(y / 2)) * f y)) := by
    funext y
    by_cases hy : 0 ≤ y
    · simp [gammaPDFReal, hy, C, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    · simp [gammaPDFReal, hy]
  rw [heq, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul]

/-- The squared norm of a `ν`-dimensional standard Gaussian has the
chi-square law with `ν` degrees of freedom. -/
theorem stdGaussian_norm_sq_map {ν : ℕ} (hν : 0 < ν) :
    (stdGaussian (EuclideanSpace ℝ (Fin ν))).map (fun x => ‖x‖ ^ 2) = chiSquareLaw ν := by
  let : NeZero ν := ⟨hν.ne'⟩
  let μ := stdGaussian (EuclideanSpace ℝ (Fin ν))
  let g : EuclideanSpace ℝ (Fin ν) → ℝ := fun x => ‖x‖ ^ 2
  have hg : Measurable g := by fun_prop
  have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have : IsProbabilityMeasure (chiSquareLaw ν) := by
    have hν' : (0 : ℝ) < ν := Nat.cast_pos.mpr hν
    exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  have hc := integral_stdGaussian_radial (ν := ν) (fun _ => 1)
  have hγ := integral_chiSquare_radial hν (fun _ => 1)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hc hγ
  have hne : (∫ y in Ioi 0, y ^ ((ν : ℝ) / 2 - 1) * Real.exp (-(y / 2))) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hγ
    exact one_ne_zero hγ
  have hcoefficient := mul_right_cancel₀ hne (hc.symm.trans hγ)
  ext s hs
  change (μ.map g) s = chiSquareLaw ν s
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [← measureReal_def, ← measureReal_def, ← integral_indicator_one hs, ← integral_indicator_one hs]
  have hf : Measurable (s.indicator (1 : ℝ → ℝ)) := measurable_const.indicator hs
  rw [integral_map hg.aemeasurable hf.aestronglyMeasurable]
  exact (integral_stdGaussian_radial (ν := ν) (s.indicator 1)).trans
    (by rw [hcoefficient, ← integral_chiSquare_radial hν])

end SketchOrientation
