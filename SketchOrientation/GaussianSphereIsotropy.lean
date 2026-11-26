import SketchOrientation.GaussianSphereBeta
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace SketchOrientation

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sphereNormalize_norm {x : E} (hx : x ≠ 0) : ‖sphereNormalize x‖ = 1 := by
  unfold sphereNormalize
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sphereNormalize_norm_le_one (x : E) : ‖sphereNormalize x‖ ≤ 1 := by
  by_cases h : x = 0
  · simp [h, sphereNormalize]
  · rw [sphereNormalize_norm h]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sphereNormalize_map_linearIsometry (e : E ≃ₗᵢ[ℝ] E) (x : E) :
    sphereNormalize (e x) = e (sphereNormalize x) := by
  simp [sphereNormalize]

theorem ae_stdGaussian_ne_zero_of_finrank (hE : 0 < Module.finrank ℝ E) :
    ∀ᵐ x ∂stdGaussian E, x ≠ 0 := by
  have h := ae_chiSquare_pos (Module.finrank ℝ E)
  have hm : Measurable (fun x : E => ‖x‖ ^ (2 : ℕ)) := measurable_id.norm.pow_const _
  rw [← stdGaussian_norm_sq_map_finrank hE, ae_map_iff hm.aemeasurable
      (measurableSet_Ioi (a := (0 : ℝ)))] at h
  filter_upwards [h] with x hx
  rintro rfl
  simp at hx

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sphere_inner_sq_le (u x : E) : (inner ℝ u (sphereNormalize x)) ^ 2 ≤ ‖u‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℝ) u (sphereNormalize x)
  rw [Real.norm_eq_abs] at h
  have h' := h.trans (mul_le_of_le_one_right (norm_nonneg u) (sphereNormalize_norm_le_one x))
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h' 2

theorem measurable_sphere_inner_sq (u : E) :
    Measurable (fun x : E => (inner ℝ u (sphereNormalize x)) ^ (2 : ℕ)) := by
  have h : Continuous (fun x : E => inner ℝ u x) := continuous_const.inner continuous_id
  exact (h.measurable.comp measurable_sphereNormalize).pow_const _

theorem integrable_radial_weighted_sphere_inner_sq (w : ℝ → ℝ)
    (hw : Measurable w) (hInt : Integrable (fun x : E => w (‖x‖ ^ 2)) (stdGaussian E))
    (u : E) :
    Integrable (fun x : E => w (‖x‖ ^ 2) * (inner ℝ u (sphereNormalize x)) ^ 2) (stdGaussian E) := by
  have hm := (hw.comp (measurable_id.norm.pow_const (2 : ℕ))).mul (measurable_sphere_inner_sq u)
  refine (hInt.norm.mul_const (‖u‖ ^ 2)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg (inner ℝ u (sphereNormalize x)))]
  exact mul_le_mul_of_nonneg_left (sphere_inner_sq_le u x) (norm_nonneg _)

set_option maxHeartbeats 1000000 in
/-- A radial weight leaves the normalized Gaussian's quadratic moment
isotropic. The trace of the weighted quadratic form fixes the coefficient. -/
theorem integral_radial_weighted_sphere_inner_sq (hE : 0 < Module.finrank ℝ E) (w : ℝ → ℝ)
    (hw : Measurable w) (hInt : Integrable (fun x : E => w (‖x‖ ^ 2)) (stdGaussian E))
    (u : E) :
    (∫ x, w (‖x‖ ^ 2) * (inner ℝ u (sphereNormalize x)) ^ 2 ∂stdGaussian E) =
      (‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ)) * ∫ x, w (‖x‖ ^ 2) ∂stdGaussian E := by
  let μ := stdGaussian E
  let F := fun u (x : E) => w (‖x‖ ^ 2) * (inner ℝ u (sphereNormalize x)) ^ 2
  let I := fun u => ∫ x, F u x ∂μ
  have hF (u : E) : Measurable (F u) :=
    (hw.comp (measurable_id.norm.pow_const (2 : ℕ))).mul (measurable_sphere_inner_sq u)
  have hIso (u v : E) (huv : ‖u‖ = ‖v‖) : I u = I v := by
    let e := (ℝ ∙ (u - v))ᗮ.reflection
    have he : e u = v := Submodule.reflection_sub huv
    have hμ : μ.map e = μ := stdGaussian_map e
    calc
      _ = ∫ x, F v (e x) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        change w (‖x‖ ^ 2) * (inner ℝ u (sphereNormalize x)) ^ 2 =
          w (‖e x‖ ^ 2) * (inner ℝ v (sphereNormalize (e x))) ^ 2
        rw [e.norm_map, sphereNormalize_map_linearIsometry, ← he, e.inner_map_map]
      _ = _ := by
        rw [← integral_map e.continuous.measurable.aemeasurable (hF v).aestronglyMeasurable, hμ]
  have hUnit (v : E) (hv : ‖v‖ = 1) :
      ((Module.finrank ℝ E : ℕ) : ℝ) * I v = ∫ x, w (‖x‖ ^ 2) ∂μ := by
    let b := stdOrthonormalBasis ℝ E
    have hI (j : Fin (Module.finrank ℝ E)) : Integrable (F (b j)) μ :=
      integrable_radial_weighted_sphere_inner_sq w hw hInt (b j)
    have hP (x : E) : (∑ j, F (b j) x) = w (‖x‖ ^ 2) * ‖sphereNormalize x‖ ^ 2 := by
      have hp := b.sum_sq_norm_inner_right (sphereNormalize x)
      simp_rw [Real.norm_eq_abs, sq_abs] at hp
      simp only [F, ← Finset.mul_sum, hp]
    calc
      _ = ∑ j : Fin (Module.finrank ℝ E), I v := by simp
      _ = ∑ j : Fin (Module.finrank ℝ E), I (b j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hIso _ _ (hv.trans (b.orthonormal.1 j).symm)
      _ = ∫ x, ∑ j : Fin (Module.finrank ℝ E), F (b j) x ∂μ :=
        (integral_finsetSum _ fun j _ => hI j).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_stdGaussian_ne_zero_of_finrank hE] with x hx
        rw [hP, sphereNormalize_norm hx, one_pow, mul_one]
  by_cases hu : u = 0
  · simp [hu]
  have hNu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  let v := ‖u‖⁻¹ • u
  have hv : ‖v‖ = 1 := sphereNormalize_norm hu
  have huv : u = ‖u‖ • v := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hNu, one_smul]
  have hScale : I u = ‖u‖ ^ 2 * I v := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [F]
    rw [congrArg (fun y => inner ℝ y (sphereNormalize x)) huv, real_inner_smul_left, mul_pow]
    ring
  have hN : ((Module.finrank ℝ E : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hE.ne'
  change I u = _
  rw [hScale, ← hUnit v hv]
  field_simp

end SketchOrientation
