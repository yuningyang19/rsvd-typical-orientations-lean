import SketchOrientation.GaussianOrientationNorm
import SketchOrientation.GaussianSphereConditionalQuadratic
import Mathlib.Probability.Moments.Covariance

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation
open scoped InnerProductSpace

private abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n ℓ : ℕ}

/-- The reciprocal in the single-spike formula, parameterized by unscaled
projection energy. -/
noncomputable def spikeReciprocal (n : ℕ) (t : ℝ) : ℝ := (1 + (n : ℝ) * t)⁻¹

/-- Law of the fraction of a spherical direction captured by a rank-ℓ sketch. -/
noncomputable def projectionBetaLaw (n ℓ : ℕ) : Measure ℝ :=
  betaMeasure ((ℓ : ℝ) / 2) (((n - ℓ : ℕ) : ℝ) / 2)

/-- Scalar covariance `Cov(f(X_n), X_n)` after using `X_n f(X_n)=1−f(X_n)`. -/
noncomputable def spikeScalarCovariance (n ℓ : ℕ) : ℝ :=
  1 - (1 + (ℓ : ℝ)) * ∫ t, spikeReciprocal n t ∂projectionBetaLaw n ℓ

/-- The fixed-dimension single-sketch reciprocal and the centered directional test,
evaluated at a Gaussian realization of a spherical direction. -/
noncomputable def spikeSketchReciprocal (P : OrthogonalProjector n ℓ) (x : Ambient n) : ℝ :=
  spikeReciprocal n (‖P.val.toEuclideanLin (sphereNormalize x)‖ ^ 2)

noncomputable def spikeDirectionalTest (u x : Ambient n) : ℝ :=
  (n : ℝ) * (inner ℝ u (sphereNormalize x)) ^ 2 - 1

/-- The conditional sketch average after drawing the orientation once. -/
noncomputable def spikeConditionalAverage (μ : Measure (OrthogonalProjector n ℓ))
    (x : Ambient n) : ℝ :=
  ∫ P, spikeSketchReciprocal P x ∂μ

private theorem measurable_spikeReciprocal (n : ℕ) : Measurable (spikeReciprocal n) :=
  ((measurable_id.const_mul (n : ℝ)).const_add 1).inv

private theorem spikeReciprocal_mem_Icc (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    spikeReciprocal n t ∈ Set.Icc (0 : ℝ) 1 := by
  have h : 1 ≤ 1 + (n : ℝ) * t := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) ht)
  exact ⟨inv_nonneg.mpr (zero_le_one.trans h), inv_le_one_of_one_le₀ h⟩

private theorem mean_betaReciprocal_identities (hℓ : 0 < ℓ) (hℓn : ℓ < n) :
    let β := projectionBetaLaw n ℓ
    let w := spikeReciprocal n
    Integrable w β ∧
      Integrable (fun t => w t * t) β ∧
      (n : ℝ) * (∫ t, w t * t ∂β) = 1 - ∫ t, w t ∂β := by
  intro β w
  let a := (ℓ : ℝ) / 2
  let b := ((n - ℓ : ℕ) : ℝ) / 2
  have ha : 0 < a := half_pos (Nat.cast_pos.mpr hℓ)
  have hb : 0 < b := half_pos (Nat.cast_pos.mpr (by omega))
  have : IsProbabilityMeasure β := isProbabilityMeasureBeta ha hb
  have hAe : ∀ᵐ t ∂β, t ∈ Set.Ioo (0 : ℝ) 1 := ae_beta_mem_Ioo a b
  have hW : Integrable w β := by
    refine (integrable_const (1 : ℝ)).mono' (measurable_spikeReciprocal n).aestronglyMeasurable ?_
    filter_upwards [hAe] with t ht
    obtain ⟨h₀, h₁⟩ := spikeReciprocal_mem_Icc n ht.1.le
    change ‖spikeReciprocal n t‖ ≤ 1
    rwa [Real.norm_of_nonneg h₀]
  have hT : Integrable (fun t => w t * t) β := by
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_spikeReciprocal n).mul measurable_id).aestronglyMeasurable ?_
    filter_upwards [hAe] with t ht
    obtain ⟨h₀, h₁⟩ := spikeReciprocal_mem_Icc n ht.1.le
    rw [Real.norm_of_nonneg (mul_nonneg h₀ ht.1.le)]
    exact mul_le_one₀ h₁ ht.1.le ht.2.le
  refine ⟨hW, hT, ?_⟩
  have hOne : (∫ _ : ℝ, (1 : ℝ) ∂β) = 1 := by simp
  rw [← integral_const_mul, ← hOne]
  rw [← integral_sub (integrable_const 1) hW]
  apply integral_congr_ae
  filter_upwards [hAe] with t ht
  have hD : 0 < 1 + (n : ℝ) * t :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (Nat.cast_nonneg _) ht.1.le)
  dsimp [w, spikeReciprocal]
  field_simp
  ring

private theorem spikeSketchReciprocal_mean (hℓ : 0 < ℓ) (hℓn : ℓ < n)
    (P : OrthogonalProjector n ℓ) :
    (∫ x, spikeSketchReciprocal P x ∂stdGaussian (Ambient n)) =
      ∫ t, spikeReciprocal n t ∂projectionBetaLaw n ℓ := by
  let R := orientationRowSpace P
  have hR : Module.finrank ℝ R = ℓ :=
    (rank_eq_finrank_euclidean P.val).symm.trans P.property.2.2
  have hC : Module.finrank ℝ Rᗮ = n - ℓ := by
    have h := R.finrank_add_finrank_orthogonal
    rw [hR, finrank_euclideanSpace_fin] at h
    omega
  have hMeas : Measurable (sphereProjectionEnergy R) := measurable_sphereProjectionEnergy R
  have hLaw := stdGaussian_sphere_projected_sq_beta R (by omega) (by omega)
  rw [hR, hC] at hLaw
  change (stdGaussian (Ambient n)).map (sphereProjectionEnergy R) = projectionBetaLaw n ℓ at hLaw
  rw [← hLaw, integral_map hMeas.aemeasurable (measurable_spikeReciprocal n).aestronglyMeasurable]
  simp only [spikeSketchReciprocal, sphereProjectionEnergy, R, orientationRowSpace_starProjection]

private theorem measurable_spikeDirectionalTest (u : Ambient n) :
    Measurable (spikeDirectionalTest u) :=
  ((measurable_sphere_inner_sq u).const_mul (n : ℝ)).sub_const 1

private theorem integrable_spikeDirectionalTest (u : Ambient n) :
    Integrable (spikeDirectionalTest u) (stdGaussian (Ambient n)) := by
  refine (integrable_const ((n : ℝ) * ‖u‖ ^ 2 + 1)).mono'
    (measurable_spikeDirectionalTest u).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  unfold spikeDirectionalTest
  calc
    _ ≤ ‖(n : ℝ) * (inner ℝ u (sphereNormalize x)) ^ 2‖ + ‖(1 : ℝ)‖ :=
      norm_sub_le _ _
    _ = (n : ℝ) * (inner ℝ u (sphereNormalize x)) ^ 2 + 1 := by
      rw [Real.norm_of_nonneg (by positivity), norm_one]
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left (sphere_inner_sq_le u x)
      (Nat.cast_nonneg _)) _

private theorem spikeDirectionalTest_mean (hn : 0 < n) (u : Ambient n) (hu : ‖u‖ = 1) :
    (∫ x, spikeDirectionalTest u x ∂stdGaussian (Ambient n)) = 0 := by
  have h := integral_radial_weighted_sphere_inner_sq (E := Ambient n)
    (by simpa using hn) (fun _ => 1) measurable_const (integrable_const 1) u
  simp only [one_mul, finrank_euclideanSpace_fin, hu, one_pow, integral_const,
    probReal_univ, one_smul, mul_one] at h
  have hSq : Integrable (fun x : Ambient n => (inner ℝ u (sphereNormalize x)) ^ (2 : ℕ))
      (stdGaussian (Ambient n)) := by
    simpa using integrable_radial_weighted_sphere_inner_sq (E := Ambient n)
      (fun _ => 1) measurable_const (integrable_const 1) u
  unfold spikeDirectionalTest
  rw [integral_sub (hSq.const_mul _) (integrable_const _), integral_const_mul,
    h, integral_const, probReal_univ, one_smul, mul_one_div,
    div_self (Nat.cast_ne_zero.mpr hn.ne'), sub_self]


set_option maxHeartbeats 900000 in
/-- The tested fixed-projector identity from the conditional block means
in the proof of the single-spike covariance. -/
theorem integral_spikeReciprocal_directionalTest (hℓ : 0 < ℓ) (hℓn : ℓ < n)
    (P : OrthogonalProjector n ℓ) (u : Ambient n) (hu : ‖u‖ = 1) :
    (∫ x, spikeSketchReciprocal P x * spikeDirectionalTest u x ∂stdGaussian (Ambient n)) =
      (n : ℝ) / ((ℓ : ℝ) * ((n : ℝ) - ℓ)) *
        (‖P.val.toEuclideanLin u‖ ^ 2 - (ℓ : ℝ) / n) * spikeScalarCovariance n ℓ := by
  let R := orientationRowSpace P
  let β := projectionBetaLaw n ℓ
  let w := spikeReciprocal n
  let A := ∫ t, w t ∂β
  let B := ∫ t, w t * t ∂β
  let a := ‖P.val.toEuclideanLin u‖ ^ 2
  have hR : Module.finrank ℝ R = ℓ :=
    (rank_eq_finrank_euclidean P.val).symm.trans P.property.2.2
  have hC : Module.finrank ℝ Rᗮ = n - ℓ := by
    have h := R.finrank_add_finrank_orthogonal
    rw [hR, finrank_euclideanSpace_fin] at h
    omega
  have hW := mean_betaReciprocal_identities hℓ hℓn
  have hInt : Integrable w
      (betaMeasure ((Module.finrank ℝ R : ℝ) / 2) ((Module.finrank ℝ Rᗮ : ℝ) / 2)) := by
    rw [hR, hC]
    exact hW.1
  have hQ := integral_sphere_conditionalQuadratic R (by omega) (by omega) w
    (measurable_spikeReciprocal n) hInt u
  rw [hR, hC, Nat.cast_sub hℓn.le] at hQ
  have hA : ‖R.orthogonalProjectionOnto u‖ ^ 2 = a := by
    change ‖R.starProjection u‖ ^ 2 = a
    simp only [a, R, orientationRowSpace_starProjection]
  have hB : ‖Rᗮ.orthogonalProjectionOnto u‖ ^ 2 = 1 - a := by
    have ht := R.norm_sq_eq_add_norm_sq_projection u
    rw [hu, one_pow, hA] at ht
    linarith
  have hT : (∫ t, w t * (1 - t) ∂β) = A - B := by
    simp only [mul_sub, mul_one]
    exact integral_sub hW.1 hW.2.1
  have hβ : betaMeasure ((ℓ : ℝ) / 2) (((n : ℝ) - ℓ) / 2) = β := by
    simp only [β, projectionBetaLaw, Nat.cast_sub hℓn.le]
  rw [hA, hB, hβ, hT] at hQ
  have hWrite (x : Ambient n) : w (sphereProjectionEnergy R x) = spikeSketchReciprocal P x := by
    simp only [w, spikeSketchReciprocal, sphereProjectionEnergy, R, orientationRowSpace_starProjection]
  simp_rw [hWrite] at hQ
  have hWP : Measurable (spikeSketchReciprocal P) :=
    (measurable_spikeReciprocal n).comp
      ((P.val.toEuclideanLin.toContinuousLinearMap.continuous.measurable.comp
        measurable_sphereNormalize).norm.pow_const _)
  have hWBound (x : Ambient n) : spikeSketchReciprocal P x ∈ Set.Icc (0 : ℝ) 1 :=
    spikeReciprocal_mem_Icc n (sq_nonneg _)
  have hWI : Integrable (spikeSketchReciprocal P) (stdGaussian (Ambient n)) := by
    exact (integrable_const (1 : ℝ)).mono' hWP.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hWBound x).1]; exact (hWBound x).2)
  have hQI : Integrable (fun x : Ambient n =>
      spikeSketchReciprocal P x * (inner ℝ u (sphereNormalize x)) ^ (2 : ℕ))
      (stdGaussian (Ambient n)) := by
    refine (integrable_const (1 : ℝ)).mono'
      (hWP.mul (measurable_sphere_inner_sq u)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have hx := sphere_inner_sq_le u x
    rw [hu, one_pow] at hx
    rw [Real.norm_of_nonneg (mul_nonneg (hWBound x).1 (sq_nonneg _))]
    exact mul_le_one₀ (hWBound x).2 (sq_nonneg _) hx
  have hExpand (x : Ambient n) :
      spikeSketchReciprocal P x * spikeDirectionalTest u x =
        (n : ℝ) * (spikeSketchReciprocal P x * (inner ℝ u (sphereNormalize x)) ^ 2) -
          spikeSketchReciprocal P x := by
    unfold spikeDirectionalTest
    ring
  simp_rw [hExpand]
  rw [integral_sub (hQI.const_mul _) hWI, integral_const_mul, hQ,
    spikeSketchReciprocal_mean hℓ hℓn P]
  change (n : ℝ) * (a / ℓ * B + (1 - a) / ((n : ℝ) - ℓ) * (A - B)) - A =
    (n : ℝ) / ((ℓ : ℝ) * ((n : ℝ) - ℓ)) * (a - (ℓ : ℝ) / n) * (1 - (1 + (ℓ : ℝ)) * A)
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (hℓ.trans hℓn).ne'
  have hL : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hLN : (ℓ : ℝ) < n := by exact_mod_cast hℓn
  have hAB : (n : ℝ) * B = 1 - A := hW.2.2
  have hB' : B = (1 - A) / (n : ℝ) := by
    apply (eq_div_iff hN).mpr
    rwa [mul_comm]
  rw [hB']
  field_simp [hL, hN, (sub_pos.mpr hLN).ne']
  ring


theorem measurable_spikeSketchReciprocal :
    Measurable (Function.uncurry (@spikeSketchReciprocal n ℓ)) := by
  have hP : Measurable (fun y : OrthogonalProjector n ℓ × Ambient n => y.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  have hx : Measurable (fun y : OrthogonalProjector n ℓ × Ambient n =>
      WithLp.ofLp (sphereNormalize y.2)) :=
    (PiLp.continuous_ofLp 2 _).measurable.comp (measurable_sphereNormalize.comp measurable_snd)
  have hM : Continuous (fun y : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) => y.1 *ᵥ y.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hg := (PiLp.continuous_toLp 2 _).measurable.comp (hM.measurable.comp (hP.prodMk hx))
  exact (measurable_spikeReciprocal n).comp (hg.norm.pow_const (2 : ℕ))

theorem measurable_spikeConditionalAverage (μ : Measure (OrthogonalProjector n ℓ))
    [IsProbabilityMeasure μ] : Measurable (spikeConditionalAverage μ) :=
  measurable_spikeSketchReciprocal.stronglyMeasurable.integral_prod_left.measurable

theorem spikeConditionalAverage_mem_Icc (μ : Measure (OrthogonalProjector n ℓ))
    [IsProbabilityMeasure μ] (x : Ambient n) :
    spikeConditionalAverage μ x ∈ Set.Icc (0 : ℝ) 1 := by
  have hf (P : OrthogonalProjector n ℓ) : spikeSketchReciprocal P x ∈ Set.Icc (0 : ℝ) 1 :=
    spikeReciprocal_mem_Icc n (sq_nonneg _)
  change 0 ≤ (∫ P, spikeSketchReciprocal P x ∂μ) ∧
    (∫ P, spikeSketchReciprocal P x ∂μ) ≤ 1
  refine ⟨integral_nonneg fun P => (hf P).1, ?_⟩
  have h := integral_mono_of_nonneg (ae_of_all μ fun P => (hf P).1) (integrable_const (1 : ℝ))
    (ae_of_all μ fun P => (hf P).2)
  have hOne : (∫ _ : OrthogonalProjector n ℓ, (1 : ℝ) ∂μ) = 1 := by simp
  exact h.trans_eq hOne

set_option maxHeartbeats 900000 in
/-- Equation (spike-cov) for any unit test direction. Taking the Rayleigh
maximizer of the mean projector gives the manuscript's `ρ_n` factor. -/
theorem spikeConditionalAverage_covariance (hℓ : 0 < ℓ) (hℓn : ℓ < n)
    (μ : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure μ]
    (u : Ambient n) (hu : ‖u‖ = 1) :
    covariance (spikeConditionalAverage μ) (spikeDirectionalTest u)
      (stdGaussian (Ambient n)) =
      (n : ℝ) / ((ℓ : ℝ) * ((n : ℝ) - ℓ)) *
        (inner ℝ ((meanSketchProjector μ).toEuclideanLin u) u - (ℓ : ℝ) / n) *
          spikeScalarCovariance n ℓ := by
  let γ := stdGaussian (Ambient n)
  let J := spikeConditionalAverage μ
  let H := spikeDirectionalTest u
  let F : OrthogonalProjector n ℓ × Ambient n → ℝ := fun y => spikeSketchReciprocal y.1 y.2 * H y.2
  let c := (n : ℝ) / ((ℓ : ℝ) * ((n : ℝ) - ℓ))
  let s := spikeScalarCovariance n ℓ
  let a := fun P : OrthogonalProjector n ℓ => ‖P.val.toEuclideanLin u‖ ^ 2
  have hH := integrable_spikeDirectionalTest u
  have hMeas : Measurable F := measurable_spikeSketchReciprocal.mul
    ((measurable_spikeDirectionalTest u).comp measurable_snd)
  have hF : Integrable F (μ.prod γ) := by
    have h := (measurePreserving_snd : MeasurePreserving Prod.snd (μ.prod γ) γ).integrable_comp_of_integrable hH
    refine h.norm.mono' hMeas.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    obtain ⟨h₀, h₁⟩ := spikeReciprocal_mem_Icc n
      (sq_nonneg ‖y.1.val.toEuclideanLin (sphereNormalize y.2)‖)
    change ‖spikeSketchReciprocal y.1 y.2 * H y.2‖ ≤ ‖H y.2‖
    rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ spikeSketchReciprocal y.1 y.2 from h₀)]
    exact mul_le_of_le_one_left (norm_nonneg _) h₁
  have hJH : Integrable (fun x => J x * H x) γ := by
    refine hH.norm.mono' ((measurable_spikeConditionalAverage μ).mul
      (measurable_spikeDirectionalTest u)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    obtain ⟨h₀, h₁⟩ := spikeConditionalAverage_mem_Icc μ x
    change ‖J x * H x‖ ≤ ‖H x‖
    rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ J x from h₀)]
    exact mul_le_of_le_one_left (norm_nonneg _) h₁
  have hJHprod (x : Ambient n) : J x * H x = ∫ P, F (P, x) ∂μ := by
    rw [show J x = (∫ P, spikeSketchReciprocal P x ∂μ) from rfl, ← integral_mul_const]
  have hProjI : Integrable a μ := by
    simpa only [a, orientationRowSpace_starProjection] using
      integrable_projected_energy μ orientationRowSpace u (measurable_orientationRowSpace_projection u)
  have hProj : (∫ P, a P ∂μ) = inner ℝ ((meanSketchProjector μ).toEuclideanLin u) u := by
    simpa only [a, orientationRowSpace_starProjection] using (meanSketchProjector_inner μ u).symm
  have hFixed (P : OrthogonalProjector n ℓ) :
      (∫ x, F (P, x) ∂γ) = c * (a P - (ℓ : ℝ) / n) * s :=
    integral_spikeReciprocal_directionalTest hℓ hℓn P u hu
  change covariance J H γ = c * (inner ℝ ((meanSketchProjector μ).toEuclideanLin u) u - (ℓ : ℝ) / n) * s
  unfold covariance
  rw [spikeDirectionalTest_mean (hℓ.trans hℓn) u hu]
  simp_rw [sub_zero, sub_mul]
  rw [integral_sub hJH (hH.const_mul _), integral_const_mul,
    spikeDirectionalTest_mean (hℓ.trans hℓn) u hu, mul_zero, sub_zero]
  simp_rw [hJHprod]
  rw [← integral_prod_symm _ hF, integral_prod _ hF]
  simp_rw [hFixed]
  rw [integral_mul_const, integral_const_mul, integral_sub hProjI (integrable_const _),
    integral_const, probReal_univ, one_smul, hProj]


/-- The scalar in equation (spike-cov) is the actual covariance of
`f(X_n)` and `X_n`, on the beta representation of `X_n/n`. -/
theorem spikeScalarCovariance_eq_covariance (hℓ : 0 < ℓ) (hℓn : ℓ < n) :
    covariance (spikeReciprocal n) (fun t => (n : ℝ) * t) (projectionBetaLaw n ℓ) =
      spikeScalarCovariance n ℓ := by
  let β := projectionBetaLaw n ℓ
  let w := spikeReciprocal n
  let a := (ℓ : ℝ) / 2
  let b := ((n - ℓ : ℕ) : ℝ) / 2
  let X : ℝ → ℝ := fun t => (n : ℝ) * t
  have ha : 0 < a := half_pos (Nat.cast_pos.mpr hℓ)
  have hb : 0 < b := half_pos (Nat.cast_pos.mpr (by omega))
  have : IsProbabilityMeasure β := isProbabilityMeasureBeta ha hb
  have ht : ∀ᵐ t ∂β, t ∈ Set.Ioo (0 : ℝ) 1 := ae_beta_mem_Ioo a b
  have hw2 : MemLp w 2 β := by
    refine MemLp.of_bound (measurable_spikeReciprocal n).aestronglyMeasurable 1 ?_
    filter_upwards [ht] with t h
    obtain ⟨h₀, h₁⟩ := spikeReciprocal_mem_Icc n h.1.le
    change ‖spikeReciprocal n t‖ ≤ 1
    rwa [Real.norm_of_nonneg h₀]
  have hX2 : MemLp X 2 β := by
    refine MemLp.of_bound (measurable_id.const_mul (n : ℝ)).aestronglyMeasurable n ?_
    filter_upwards [ht] with t h
    change ‖(n : ℝ) * t‖ ≤ n
    rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) h.1.le)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) h.2.le
  have hMean : (∫ t, X t ∂β) = ℓ := by
    rw [show X = fun t => (n : ℝ) * t from rfl, integral_const_mul,
      show β = betaMeasure a b from rfl, (beta_mean ha hb).2]
    have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (hℓ.trans hℓn).ne'
    dsimp [a, b]
    rw [Nat.cast_sub hℓn.le]
    field_simp [hN]
    ring
  have hProd : (∫ t, (w * X) t ∂β) = 1 - ∫ t, w t ∂β := by
    have he (t : ℝ) : (w * X) t = (n : ℝ) * (w t * t) := by
      simp only [Pi.mul_apply, X]
      ring
    simp_rw [he, integral_const_mul]
    exact (mean_betaReciprocal_identities hℓ hℓn).2.2
  change covariance w X β = spikeScalarCovariance n ℓ
  rw [covariance_eq_sub hw2 hX2, hProd, hMean]
  change 1 - (∫ t, w t ∂β) - (∫ t, w t ∂β) * (ℓ : ℝ) =
    1 - (1 + (ℓ : ℝ)) * (∫ t, w t ∂β)
  ring

end TypicalOrientations
