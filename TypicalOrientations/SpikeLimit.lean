import TypicalOrientations.SpikeCovariance
import SketchOrientation.CoordinateOrientationExample

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation Filter
open scoped Topology InnerProductSpace

private abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)

private theorem measurable_gaussianEnergy (n : ℕ) : Measurable (gaussianCoordinateEnergy n) := by
  unfold gaussianCoordinateEnergy
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i.val).pow_const 2

/-- The first ℓ coordinates of one spherical direction, using one
infinite Gaussian sequence for all ambient dimensions. -/
noncomputable def coupledSpikeFraction (n ℓ : ℕ) (ω : ℕ → ℝ) : ℝ :=
  gaussianCoordinateEnergy ℓ ω / gaussianCoordinateEnergy n ω

private theorem measurable_coupledSpikeFraction (n ℓ : ℕ) :
    Measurable (coupledSpikeFraction n ℓ) :=
  (measurable_gaussianEnergy ℓ).div (measurable_gaussianEnergy n)

private theorem gaussianEuclideanPrefix_law (n : ℕ) :
    infiniteGaussianCoordinateLaw.map (fun ω : ℕ → ℝ =>
      (WithLp.toLp 2 (fun i : Fin n => ω i.val) : Ambient n)) = stdGaussian (Ambient n) := by
  let f (ω : ℕ → ℝ) (i : Fin n) := ω i.val
  have hf : Measurable f := measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hTo : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → Ambient n) := WithLp.measurable_toLp _ _
  change infiniteGaussianCoordinateLaw.map (WithLp.toLp 2 ∘ f) = _
  rw [← Measure.map_map hTo hf]
  change ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map f).map (WithLp.toLp 2) = _
  rw [show (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map f =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) from
    infiniteProduct_map_embedding (gaussianReal 0 1) (Fin.valEmbedding (n := n)), map_pi_eq_stdGaussian]

private theorem coordinateStarProjection_sq {n ℓ : ℕ} (hℓn : ℓ ≤ n) (v : Ambient n) :
    ‖(orientationRowSpace (coordinateSketchProjector (Fin.castLEEmb hℓn))).starProjection v‖ ^ 2 =
      ∑ i : Fin ℓ, (v (Fin.castLE hℓn i)) ^ 2 := by
  let P := coordinateSketchProjector (Fin.castLEEmb hℓn)
  let B := rowSelector (Fin.castLEEmb hℓn)
  let R := orientationRowSpace P
  have hQ := R.re_inner_starProjection_eq_normSq v
  change inner ℝ (R.starProjection v) v = ‖R.starProjection v‖ ^ 2 at hQ
  change ‖R.starProjection v‖ ^ 2 = _
  rw [← hQ, show R = orientationRowSpace P from rfl, orientationRowSpace_starProjection,
    show P.val = Bᵀ * B from rfl, euclidean_mul, LinearMap.comp_apply,
    euclidean_transpose, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  have hB : (B.toEuclideanLin v) i = v (Fin.castLE hℓn i) := by
    change ((B *ᵥ WithLp.ofLp v) i) = _
    simp [B, Matrix.mulVec, dotProduct, rowSelector]
  rw [hB]

/-- The finite normalized Gaussian representation has the exact beta law,
with the ambient and sketch dimensions bound to the same draw. -/
theorem coupledSpikeFraction_law {n ℓ : ℕ} (hℓ : 0 < ℓ) (hℓn : ℓ < n) :
    infiniteGaussianCoordinateLaw.map (coupledSpikeFraction n ℓ) = projectionBetaLaw n ℓ := by
  let f (ω : ℕ → ℝ) : Ambient n := WithLp.toLp 2 (fun i : Fin n => ω i.val)
  let P := coordinateSketchProjector (Fin.castLEEmb hℓn.le)
  let R := orientationRowSpace P
  have hf : Measurable f :=
    (WithLp.measurable_toLp _ _).comp (measurable_pi_lambda _ fun i => measurable_pi_apply i.val)
  have hR : Module.finrank ℝ R = ℓ :=
    (rank_eq_finrank_euclidean P.val).symm.trans P.property.2.2
  have hC : Module.finrank ℝ Rᗮ = n - ℓ := by
    have h := R.finrank_add_finrank_orthogonal
    rw [hR, finrank_euclideanSpace_fin] at h
    omega
  have hv (x : Ambient n) : ‖R.starProjection (sphereNormalize x)‖ ^ 2 =
      ‖R.starProjection x‖ ^ 2 / ‖x‖ ^ 2 := by
    rw [sphereNormalize, map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      mul_pow, inv_pow, mul_comm, ← div_eq_mul_inv]
  have hEq : coupledSpikeFraction n ℓ = (sphereProjectionEnergy R) ∘ f := by
    funext ω
    rw [Function.comp_apply, sphereProjectionEnergy, hv,
      show R = orientationRowSpace (coordinateSketchProjector (Fin.castLEEmb hℓn.le)) from rfl,
      coordinateStarProjection_sq hℓn.le, EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [hEq, ← Measure.map_map (measurable_sphereProjectionEnergy R) hf,
    gaussianEuclideanPrefix_law]
  have hLaw := stdGaussian_sphere_projected_sq_beta R (by omega) (by omega)
  rw [hR, hC] at hLaw
  exact hLaw

/-- The exact chi-square coefficient appearing in the quantitative converse. -/
noncomputable def spikeLimitGap (ℓ : ℕ) : ℝ :=
  (1 + (ℓ : ℝ)) * (∫ y, (1 + y)⁻¹ ∂chiSquareLaw ℓ) - 1

/-- The covariance coefficient tends to minus the manuscript's `b_ℓ`. -/
theorem spikeScalarCovariance_tendsto {ℓ : ℕ} (hℓ : 0 < ℓ) :
    Tendsto (fun n => spikeScalarCovariance n ℓ) atTop (𝓝 (-spikeLimitGap ℓ)) := by
  let μ := infiniteGaussianCoordinateLaw
  let F (n : ℕ) (ω : ℕ → ℝ) := spikeReciprocal n (coupledSpikeFraction n ℓ ω)
  let G (ω : ℕ → ℝ) := (1 + gaussianCoordinateEnergy ℓ ω)⁻¹
  have hnonneg (n : ℕ) (ω : ℕ → ℝ) : 0 ≤ gaussianCoordinateEnergy n ω := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF (n : ℕ) : Measurable (F n) :=
    (((measurable_coupledSpikeFraction n ℓ).const_mul (n : ℝ)).const_add 1).inv
  have hG : Measurable G := ((measurable_gaussianEnergy ℓ).const_add 1).inv
  have hLim : Tendsto (fun n => ∫ ω, F n ω ∂μ) atTop (𝓝 (∫ ω, G ω ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · exact fun n => (hF n).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      refine ae_of_all _ fun ω => ?_
      have hx : 0 ≤ coupledSpikeFraction n ℓ ω := div_nonneg (hnonneg ℓ ω) (hnonneg n ω)
      have h1 : 1 ≤ 1 + (n : ℝ) * coupledSpikeFraction n ℓ ω :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hx)
      rw [show F n ω = (1 + (n : ℝ) * coupledSpikeFraction n ℓ ω)⁻¹ from rfl,
        Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans h1))]
      exact inv_le_one_of_one_le₀ h1
    · filter_upwards [gaussianCoordinateEnergy_strongLaw] with ω hω
      have ht : Tendsto (fun n => gaussianCoordinateEnergy ℓ ω /
        (gaussianCoordinateEnergy n ω / (n : ℝ))) atTop (𝓝 (gaussianCoordinateEnergy ℓ ω)) := by
        have h := (tendsto_const_nhds (x := gaussianCoordinateEnergy ℓ ω)).div hω one_ne_zero
        rw [div_one] at h
        exact h.congr (fun _ => rfl)
      have hpos : (1 : ℝ) + gaussianCoordinateEnergy ℓ ω ≠ 0 :=
        (add_pos_of_pos_of_nonneg zero_lt_one (hnonneg ℓ ω)).ne'
      apply ((ht.const_add 1).inv₀ hpos).congr
      intro n
      change (1 + gaussianCoordinateEnergy ℓ ω / (gaussianCoordinateEnergy n ω / (n : ℝ)))⁻¹ =
        (1 + (n : ℝ) * (gaussianCoordinateEnergy ℓ ω / gaussianCoordinateEnergy n ω))⁻¹
      simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
      congr 1
      ring
  have hLimG : (∫ ω, G ω ∂μ) = ∫ y, (1 + y)⁻¹ ∂chiSquareLaw ℓ := by
    let w : ℝ → ℝ := fun y => (1 + y)⁻¹
    have hw : Measurable w := (measurable_id.const_add (1 : ℝ)).inv
    change (∫ ω, w (gaussianCoordinateEnergy ℓ ω) ∂μ) = _
    rw [← integral_map (measurable_gaussianEnergy ℓ).aemeasurable hw.aestronglyMeasurable,
      gaussianCoordinateEnergy_law hℓ]
  have hLimF (n : ℕ) (hn : ℓ < n) : (∫ ω, F n ω ∂μ) =
      ∫ t, spikeReciprocal n t ∂projectionBetaLaw n ℓ := by
    have hw : Measurable (spikeReciprocal n) :=
      ((measurable_id.const_mul (n : ℝ)).const_add 1).inv
    change (∫ ω, spikeReciprocal n (coupledSpikeFraction n ℓ ω) ∂μ) = _
    rw [← integral_map (measurable_coupledSpikeFraction n ℓ).aemeasurable hw.aestronglyMeasurable,
      coupledSpikeFraction_law hℓ hn]
  rw [hLimG] at hLim
  have h := (hLim.const_mul (1 + (ℓ : ℝ))).const_sub 1
  have hResult : (1 - (1 + (ℓ : ℝ)) * ∫ y, (1 + y)⁻¹ ∂chiSquareLaw ℓ) =
      -spikeLimitGap ℓ := by unfold spikeLimitGap; ring
  rw [hResult] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop ℓ] with n hn
  rw [hLimF n hn]
  rfl


/-- The strict Jensen step for the reciprocal. The difference from the
tangent at the mean is positive away from that mean, a null singleton. -/
theorem spikeLimitGap_pos {ℓ : ℕ} (hℓ : 0 < ℓ) : 0 < spikeLimitGap ℓ := by
  let μ := chiSquareLaw ℓ
  let s : ℝ := ℓ
  let w (y : ℝ) : ℝ := (1 + y)⁻¹
  let a (y : ℝ) : ℝ := (1 + s)⁻¹ - (y - s) / (1 + s)^2
  let g (y : ℝ) : ℝ := w y - a y
  have hS : 0 ≤ s := Nat.cast_nonneg _
  have hD : 0 < 1 + s := add_pos_of_pos_of_nonneg zero_lt_one hS
  have : IsProbabilityMeasure μ :=
    isProbabilityMeasure_gammaMeasure (half_pos (Nat.cast_pos.mpr hℓ)) (by norm_num)
  have hW : Integrable w μ := by
    have hm : Measurable w := (measurable_id.const_add (1 : ℝ)).inv
    refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_chiSquare_pos ℓ] with y hy
    have hp : 1 ≤ 1 + y := le_add_of_nonneg_right hy.le
    change ‖(1 + y)⁻¹‖ ≤ 1
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hp))]
    exact inv_le_one_of_one_le₀ hp
  have hY : Integrable (fun y : ℝ => y) μ := (chiSquare_mean hℓ).1
  have hc : Integrable (fun y : ℝ => y - s) μ := hY.sub (integrable_const s)
  have hA : Integrable a μ := (integrable_const _).sub (hc.div_const _)
  have hG : Integrable g μ := hW.sub hA
  have ha : (∫ y, a y ∂μ) = (1 + s)⁻¹ := by
    unfold a
    rw [integral_sub (integrable_const _) (hc.div_const _), integral_div,
      integral_sub hY (integrable_const s), (chiSquare_mean hℓ).2]
    simp only [integral_const, probReal_univ, one_smul, show (ℓ : ℝ) = s from rfl,
      sub_self, zero_div, sub_zero]
  have hSingleton : μ {s} = 0 := by
    change (volume.withDensity (gammaPDF ((ℓ : ℝ) / 2) (1 / 2))) {s} = 0
    rw [withDensity_apply _ (measurableSet_singleton s)]
    simp
  have hNE : ∀ᵐ y ∂μ, y ≠ s := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using hSingleton
  have hPos : ∀ᵐ y ∂μ, 0 < g y := by
    filter_upwards [ae_chiSquare_pos ℓ, hNE] with y hy hn
    have hy' : 0 < 1 + y := add_pos zero_lt_one hy
    have he : g y = (y - s)^2 / ((1 + s)^2 * (1 + y)) := by
      unfold g w a
      field_simp [hD.ne', hy'.ne']
      ring
    rw [he]
    exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hn)) (mul_pos (sq_pos_of_pos hD) hy')
  have hGPos : 0 < ∫ y, g y ∂μ := by
    have hn : 0 ≤ ∫ y, g y ∂μ := integral_nonneg_of_ae (hPos.mono fun _ hp => hp.le)
    apply lt_of_le_of_ne hn
    intro hzero
    have hGZero := (integral_eq_zero_iff_of_nonneg_ae (hPos.mono fun _ hp => hp.le) hG).mp hzero.symm
    obtain ⟨y, hy, hzeroY⟩ := (hPos.and hGZero).exists
    exact hy.ne' hzeroY
  rw [show (∫ y, g y ∂μ) = (∫ y, w y ∂μ) - (1 + s)⁻¹ by
    rw [show g = fun y => w y - a y from rfl, integral_sub hW hA, ha]] at hGPos
  have h := mul_pos hD hGPos
  rw [mul_sub, mul_inv_cancel₀ hD.ne'] at h
  exact h

end TypicalOrientations
