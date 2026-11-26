import SketchOrientation.GaussianSphereWeighted

namespace SketchOrientation

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The squared normalized energy in the first orthogonal block. -/
noncomputable def sphereProjectionEnergy (R : Submodule ℝ E) (x : E) : ℝ :=
  ‖R.starProjection (sphereNormalize x)‖ ^ 2

theorem measurable_sphereProjectionEnergy (R : Submodule ℝ E) :
    Measurable (sphereProjectionEnergy R) :=
  (R.starProjection.continuous.measurable.comp measurable_sphereNormalize).norm.pow_const (2 : ℕ)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem sphereProjectionEnergy_le_one (R : Submodule ℝ E) (x : E) :
    sphereProjectionEnergy R x ≤ 1 := by
  have h := (R.norm_starProjection_apply_le (sphereNormalize x)).trans (sphereNormalize_norm_le_one x)
  simpa [sphereProjectionEnergy] using pow_le_pow_left₀
    (norm_nonneg (R.starProjection (sphereNormalize x))) h 2

omit [MeasurableSpace E] [BorelSpace E] in
private theorem sphereProjectionEnergy_nonneg (R : Submodule ℝ E) (x : E) :
    0 ≤ sphereProjectionEnergy R x := sq_nonneg _

set_option maxHeartbeats 1800000 in
/-- Weighted conditional quadratic moment of a normalized Gaussian split
into two orthogonal blocks. The test weight may be any integrable function
of the squared first-block length. -/
theorem integral_sphere_conditionalQuadratic (R : Submodule ℝ E)
    (hR : 0 < Module.finrank ℝ R) (hC : 0 < Module.finrank ℝ Rᗮ)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hInt : Integrable w
      (betaMeasure ((Module.finrank ℝ R : ℝ) / 2) ((Module.finrank ℝ Rᗮ : ℝ) / 2)))
    (u : E) :
    (∫ x, w (sphereProjectionEnergy R x) * (inner ℝ u (sphereNormalize x)) ^ 2 ∂stdGaussian E) =
      (‖R.orthogonalProjectionOnto u‖ ^ 2 / (Module.finrank ℝ R : ℝ)) *
        (∫ t, w t * t ∂betaMeasure ((Module.finrank ℝ R : ℝ) / 2) ((Module.finrank ℝ Rᗮ : ℝ) / 2)) +
      (‖Rᗮ.orthogonalProjectionOnto u‖ ^ 2 / (Module.finrank ℝ Rᗮ : ℝ)) *
        (∫ t, w t * (1 - t) ∂betaMeasure ((Module.finrank ℝ R : ℝ) / 2) ((Module.finrank ℝ Rᗮ : ℝ) / 2)) := by
  let μ := stdGaussian E
  let η := (stdGaussian R).prod (stdGaussian Rᗮ)
  let β := betaMeasure ((Module.finrank ℝ R : ℝ) / 2) ((Module.finrank ℝ Rᗮ : ℝ) / 2)
  let X := fun x : E => (R.orthogonalProjectionOnto x, Rᗮ.orthogonalProjectionOnto x)
  let Y := fun p : R × Rᗮ => (p.1 : E) + (p.2 : E)
  let t := sphereProjectionEnergy R
  let A := fun p : R × Rᗮ => ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2
  let q := fun p : R × Rᗮ => ‖p.1‖ ^ 2 / A p
  let u₁ := R.orthogonalProjectionOnto u
  let u₂ := Rᗮ.orthogonalProjectionOnto u
  let L := fun p : R × Rᗮ => inner ℝ u₁ p.1
  let D := fun p : R × Rᗮ => inner ℝ u₂ p.2
  let J := fun p => w (q p) / A p
  have hX : Measurable X := R.orthogonalProjectionOnto.continuous.measurable.prodMk
    Rᗮ.orthogonalProjectionOnto.continuous.measurable
  have hY : Measurable Y := by
    exact (measurable_subtype_coe.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd)
  have hX₀ : μ.map X = η := stdGaussian_orthogonal_split R
  have hY₀ : η.map Y = μ := by
    rw [← hX₀, Measure.map_map hY hX]
    have h : Y ∘ X = id := funext (R.starProjection_add_starProjection_orthogonal)
    rw [h, Measure.map_id]
  have ht : Measurable t := measurable_sphereProjectionEnergy R
  have ht₀ : μ.map t = β := stdGaussian_sphere_projected_sq_beta R hR hC
  have hA (p : R × Rᗮ) : ‖Y p‖ ^ 2 = A p := by
    change ‖(p.1 : E) + (p.2 : E)‖ ^ 2 = _
    simpa [A, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (p.2.property _ p.1.property)
  have hProj (p : R × Rᗮ) : R.starProjection (Y p) = p.1 := by
    change R.starProjection ((p.1 : E) + (p.2 : E)) = _
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr p.1.property,
      Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal p.2.property]
    simp
  have hQ (p : R × Rᗮ) : t (Y p) = q p := by
    change ‖R.starProjection (‖Y p‖⁻¹ • Y p)‖ ^ 2 = _
    rw [map_smul, hProj, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      mul_pow, inv_pow, hA, mul_comm]
    rfl
  have hQMap : η.map q = β := by
    have h : q = t ∘ Y := funext fun p => (hQ p).symm
    rw [h, ← Measure.map_map ht hY, hY₀, ht₀]
  have hqm : Measurable q := by
    exact (measurable_fst.norm.pow_const (2 : ℕ)).div
      ((measurable_fst.norm.pow_const (2 : ℕ)).add (measurable_snd.norm.pow_const (2 : ℕ)))
  have hqi (p : R × Rᗮ) : 0 ≤ q p ∧ q p ≤ 1 := by
    rw [← hQ]
    exact ⟨sphereProjectionEnergy_nonneg R _, sphereProjectionEnergy_le_one R _⟩
  have hwI : Integrable (fun p => w (q p)) η := by
    change Integrable (w ∘ q) η
    rw [← integrable_map_measure hw.aestronglyMeasurable hqm.aemeasurable, hQMap]
    exact hInt
  let q₀ := fun p : ℝ × ℝ => p.1 / (p.1 + p.2)
  let w₁ := fun p : ℝ × ℝ => w (q₀ p) * q₀ p
  let w₂ := fun p : ℝ × ℝ => w (q₀ p) * (1 - q₀ p)
  have hq₀ : Measurable q₀ := by fun_prop
  have hw₁ : Measurable w₁ := (hw.comp hq₀).mul hq₀
  have hw₂ : Measurable w₂ := (hw.comp hq₀).mul (measurable_const.sub hq₀)
  have hw₁I : Integrable (fun p : R × Rᗮ => w₁ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) η := by
    refine hwI.norm.mono' ((hw.comp hqm).mul hqm).aestronglyMeasurable ?_
    filter_upwards [] with p
    change ‖w (q p) * q p‖ ≤ ‖w (q p)‖
    rw [norm_mul, Real.norm_of_nonneg (hqi p).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hqi p).2
  have hw₂I : Integrable (fun p : R × Rᗮ => w₂ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) η := by
    refine hwI.norm.mono' ((hw.comp hqm).mul (measurable_const.sub hqm)).aestronglyMeasurable ?_
    filter_upwards [] with p
    change ‖w (q p) * (1 - q p)‖ ≤ ‖w (q p)‖
    rw [norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr (hqi p).2)]
    exact mul_le_of_le_one_right (norm_nonneg _) (sub_le_self _ (hqi p).1)
  let B₁ := fun p : R × Rᗮ => w₁ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2) *
        (inner ℝ u₁ (sphereNormalize p.1)) ^ 2
  let B₂ := fun p : R × Rᗮ => w₂ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2) *
        (inner ℝ u₂ (sphereNormalize p.2)) ^ 2
  have hB₁I : Integrable B₁ η := integrable_weighted_sphere_prod_left w₁ hw₁ hw₁I u₁
  have hB₂I : Integrable B₂ η := by
    have hW : Measurable (w₂ ∘ Prod.swap) := hw₂.comp measurable_swap
    have hWI : Integrable (fun p : Rᗮ × R => (w₂ ∘ Prod.swap) (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) _ :=
      hw₂I.swap
    have h := (integrable_weighted_sphere_prod_left (w₂ ∘ Prod.swap) hW hWI u₂).swap
    exact h
  have hB₁ (p : R × Rᗮ) : B₁ p = J p * L p ^ 2 := by
    by_cases h0 : p.1 = 0
    · simp [B₁, L, sphereNormalize, h0]
    · have hN : ‖p.1‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      change (w (q p) * q p) * (inner ℝ u₁ (‖p.1‖⁻¹ • p.1)) ^ 2 = _
      rw [real_inner_smul_right, mul_pow, inv_pow]
      unfold q J
      field_simp [hN]
      rfl
  have hB₂ (p : R × Rᗮ) : B₂ p = J p * D p ^ 2 := by
    by_cases h0 : p.2 = 0
    · simp [B₂, D, sphereNormalize, h0]
    · have hN : ‖p.2‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      have hAp : 0 < A p := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hN)
      change (w (q p) * (1 - q p)) * (inner ℝ u₂ (‖p.2‖⁻¹ • p.2)) ^ 2 = _
      rw [real_inner_smul_right, mul_pow, inv_pow]
      unfold q J
      field_simp [hN, hAp.ne']
      unfold A
      ring
  let K := fun x : E => w (t x) * (inner ℝ u (sphereNormalize x)) ^ 2
  have hK : Measurable K := (hw.comp ht).mul (measurable_sphere_inner_sq u)
  have hKInt : Integrable K μ := by
    have h := (integrable_map_measure hw.aestronglyMeasurable ht.aemeasurable).1
      (show Integrable w (μ.map t) by rwa [ht₀])
    refine (h.norm.mul_const (‖u‖ ^ 2)).mono' hK.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg (inner ℝ u (sphereNormalize x)))]
    exact mul_le_mul_of_nonneg_left (sphere_inner_sq_le u x) (norm_nonneg _)
  have hYInt : Integrable (K ∘ Y) η := by
    rw [← integrable_map_measure hK.aestronglyMeasurable hY.aemeasurable, hY₀]
    exact hKInt
  have hKL (p : R × Rᗮ) : K (Y p) = B₁ p + B₂ p + 2 * (J p * L p * D p) := by
    change w (t (Y p)) * (inner ℝ u (‖Y p‖⁻¹ • Y p)) ^ 2 = _
    rw [hQ, real_inner_smul_right, mul_pow, inv_pow, hA, hB₁, hB₂]
    have he : inner ℝ u (Y p) = L p + D p := by
      change inner ℝ u ((p.1 : E) + (p.2 : E)) = _
      rw [inner_add_right, ← R.inner_orthogonalProjectionOnto_eq_of_mem_right,
        ← Rᗮ.inner_orthogonalProjectionOnto_eq_of_mem_right]
    rw [he]
    unfold J
    ring
  let C := fun p => J p * L p * D p
  have hCI : Integrable C η := by
    refine ((hYInt.sub (hB₁I.add hB₂I)).div_const 2).congr (ae_of_all _ fun p => ?_)
    change (K (Y p) - (B₁ p + B₂ p)) / 2 = C p
    rw [hKL]
    unfold C
    ring
  have hC0 : (∫ p, C p ∂η) = 0 := by
    let e : R ≃ₗᵢ[ℝ] R := LinearIsometryEquiv.neg ℝ
    let U := Prod.map e (id : Rᗮ → Rᗮ)
    have hU : Measurable U := e.continuous.measurable.prodMap measurable_id
    have hAct : η.map U = η := by
      rw [← Measure.map_prod_map _ _ e.continuous.measurable measurable_id, stdGaussian_map e,
        Measure.map_id]
    have hn (p : R × Rᗮ) : C (U p) = -C p := by
      simp [C, U, e, J, q, A, L, D, mul_neg, neg_mul]
    have hCM : AEStronglyMeasurable C (η.map U) := by
      rw [hAct]
      exact hCI.aestronglyMeasurable
    have hh : (∫ p, C p ∂η) = -(∫ p, C p ∂η) := by
      calc
        _ = ∫ p, C p ∂η.map U := by rw [hAct]
        _ = ∫ p, C (U p) ∂η := integral_map hU.aemeasurable hCM
        _ = _ := by
          rw [← integral_neg]
          exact integral_congr_ae (ae_of_all _ hn)
    linarith
  have hin₁ := integral_weighted_sphere_prod_left hR w₁ hw₁ hw₁I u₁
  have hin₂ := integral_weighted_sphere_prod_right hC w₂ hw₂ hw₂I u₂
  have hMap₁ :
      (∫ p : R × Rᗮ, w₁ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2) ∂η) = ∫ z, w z * z ∂β := by
    have hh : Measurable (fun z : ℝ => w z * z) := hw.mul measurable_id
    rw [← hQMap, integral_map hqm.aemeasurable hh.aestronglyMeasurable]
  have hMap₂ :
      (∫ p : R × Rᗮ, w₂ (‖p.1‖ ^ 2, ‖p.2‖ ^ 2) ∂η) = ∫ z, w z * (1 - z) ∂β := by
    have hh : Measurable (fun z : ℝ => w z * (1 - z)) :=
      hw.mul (measurable_const.sub measurable_id)
    rw [← hQMap, integral_map hqm.aemeasurable hh.aestronglyMeasurable]
  change (∫ x, K x ∂μ) = _
  rw [← hY₀, integral_map hY.aemeasurable hK.aestronglyMeasurable,
    integral_congr_ae (ae_of_all _ hKL)]
  change (∫ p, (B₁ p + B₂ p) + 2 * C p ∂η) = _
  have hB : Integrable (fun p => B₁ p + B₂ p) η := hB₁I.add hB₂I
  rw [integral_add hB (hCI.const_mul 2), integral_add hB₁I hB₂I, integral_const_mul, hC0,
    mul_zero, add_zero]
  have hL₁ : (∫ p, B₁ p ∂η) = (‖u₁‖ ^ 2 / (Module.finrank ℝ R : ℝ)) *
      ∫ z, w z * z ∂β := hin₁.trans (congrArg (_ * ·) hMap₁)
  have hL₂ : (∫ p, B₂ p ∂η) = (‖u₂‖ ^ 2 / (Module.finrank ℝ Rᗮ : ℝ)) *
      ∫ z, w z * (1 - z) ∂β := hin₂.trans (congrArg (_ * ·) hMap₂)
  rw [hL₁, hL₂]

end SketchOrientation
