import TypicalOrientations.SpikeBridge
import TypicalOrientations.SpikeLimit
import TypicalOrientations.PaperTheorems
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation Filter
open scoped Topology InnerProductSpace

private abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Orientation (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The spike direction when the orientation variable is U = Qᵀ. -/
noncomputable def coordinateSpikeDirection {n : ℕ} (hn : 0 < n) (U : Orientation n) :
    Ambient n :=
  Uᵀ.toEuclideanLin (EuclideanSpace.single ⟨0, hn⟩ 1)

private theorem measurable_coordinateSpikeDirection {n : ℕ} (hn : 0 < n) :
    Measurable (coordinateSpikeDirection hn) := by
  apply Continuous.measurable
  change Continuous (fun U : Orientation n =>
    WithLp.toLp 2 (Uᵀ *ᵥ WithLp.ofLp (EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ))))
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_id.matrix_transpose.matrix_mulVec continuous_const)

private theorem coordinateSpikeDirection_law {n : ℕ} (hn : 0 < n) :
    (gaussianRightOrthogonalLaw n).map (coordinateSpikeDirection hn) =
      (stdGaussian (Ambient n)).map sphereNormalize :=
  gaussianRightOrthogonalLaw_map_transpose_direction _ (by
    simp [EuclideanSpace.single, PiLp.norm_single])

/-- The two finite loss coefficients of equation (spike-loss). -/
noncomputable def coordinateSpikeLoss (n k ℓ : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ) - ℓ - 1) / ((n : ℝ) - k) +
    (((n : ℝ) + 1) / ((n : ℝ) - k)) * spikeReciprocal n t

private theorem measurable_coordinateSpikeLoss (n k ℓ : ℕ) :
    Measurable (coordinateSpikeLoss n k ℓ) :=
  ((((measurable_id.const_mul (n : ℝ)).const_add 1).inv).const_mul _).const_add _

private theorem coordinateSpikeFraction_law {n ℓ : ℕ} (hℓ : 0 < ℓ) (hℓn : ℓ < n)
    (P : OrthogonalProjector n ℓ) :
    (gaussianRightOrthogonalLaw n).map
      (fun U => ‖P.val.toEuclideanLin (coordinateSpikeDirection (hℓ.trans hℓn) U)‖ ^ 2) =
        projectionBetaLaw n ℓ := by
  let R := orientationRowSpace P
  let v := coordinateSpikeDirection (hℓ.trans hℓn)
  let q (x : Ambient n) := ‖P.val.toEuclideanLin x‖ ^ 2
  have hq : Measurable q := (P.val.toEuclideanLin.continuous_of_finiteDimensional.measurable.norm).pow_const 2
  have hR : Module.finrank ℝ R = ℓ :=
    (rank_eq_finrank_euclidean P.val).symm.trans P.property.2.2
  have hC : Module.finrank ℝ Rᗮ = n - ℓ := by
    have h := R.finrank_add_finrank_orthogonal
    rw [hR, finrank_euclideanSpace_fin] at h
    omega
  change (gaussianRightOrthogonalLaw n).map (q ∘ v) = _
  rw [← Measure.map_map hq (measurable_coordinateSpikeDirection _),
    coordinateSpikeDirection_law, Measure.map_map hq measurable_sphereNormalize]
  have hComp : q ∘ sphereNormalize = sphereProjectionEnergy R := by
    funext x
    simp only [Function.comp_apply, q, R, sphereProjectionEnergy,
      orientationRowSpace_starProjection]
  rw [hComp]
  have hLaw := stdGaussian_sphere_projected_sq_beta R (by omega) (by omega)
  rw [hR, hC] at hLaw
  exact hLaw

/-- The exact finite one-draw residual law, for any fixed projector of rank ℓ. -/
theorem coordinateSpike_fixedProjector_loss_law {n k ℓ : ℕ} (hk : 0 < k) (hkn : k < n)
    (hℓ : 0 < ℓ) (hℓn : ℓ < n) (P : OrthogonalProjector n ℓ) :
    (gaussianRightOrthogonalLaw n).map (fun U =>
      squaredResidual (diagonal (spikeSpectrum n)) (U * P.val) /
        optimalSquaredTail k (spikeSpectrum n)) =
      (projectionBetaLaw n ℓ).map (coordinateSpikeLoss n k ℓ) := by
  let η := gaussianRightOrthogonalLaw n
  let v := coordinateSpikeDirection (hℓ.trans hℓn)
  let q (U : Orientation n) := ‖P.val.toEuclideanLin (v U)‖ ^ 2
  have hq : Measurable q :=
    (((P.val.toEuclideanLin.continuous_of_finiteDimensional.measurable.comp
      (measurable_coordinateSpikeDirection _)).norm).pow_const 2)
  rw [← coordinateSpikeFraction_law hℓ hℓn P,
    Measure.map_map (measurable_coordinateSpikeLoss n k ℓ) hq]
  apply Measure.map_congr
  filter_upwards [ae_gaussianRightOrthogonal n] with U hU
  have hNorm : ‖v U‖ = 1 := by
    change ‖Uᵀ.toEuclideanLin (EuclideanSpace.single ⟨0, hℓ.trans hℓn⟩ (1 : ℝ))‖ = 1
    rw [← orthogonalMatrixIsometry_apply Uᵀ
      (by rw [transpose_transpose]; exact mul_eq_one_comm.mp hU),
      LinearIsometryEquiv.norm_map]
    simp [EuclideanSpace.single, PiLp.norm_single]
  rw [spikeSpectrum_rotatedLoss_eq hk hkn U hU P]
  change _ + _ * spikeSketchReciprocal P (v U) = coordinateSpikeLoss n k ℓ (q U)
  simp [coordinateSpikeLoss, spikeSketchReciprocal, sphereNormalize, hNorm, q]

/-- The fixed sketch conditional mean is the loss at the first ℓ coordinates. -/
theorem coordinateSpike_fixedConditional_loss_eq {n k ℓ : ℕ} (hℓn : ℓ ≤ n)
    (U : Orientation n) :
    conditionalMean k (spikeSpectrum n) (fixedCoordinateSketchLaw hℓn) U =
      squaredResidual (diagonal (spikeSpectrum n))
        (U * (coordinateSketchProjector (Fin.castLEEmb hℓn)).val) /
        optimalSquaredTail k (spikeSpectrum n) := by
  unfold conditionalMean fixedCoordinateSketchLaw
  exact integral_dirac _ _

theorem coordinateSpike_fixedConditional_law {n k ℓ : ℕ} (hk : 0 < k) (hkn : k < n)
    (hℓ : 0 < ℓ) (hℓn : ℓ < n) :
    (gaussianRightOrthogonalLaw n).map
      (conditionalMean k (spikeSpectrum n) (fixedCoordinateSketchLaw hℓn.le)) =
      (projectionBetaLaw n ℓ).map (coordinateSpikeLoss n k ℓ) := by
  have h : conditionalMean k (spikeSpectrum n) (fixedCoordinateSketchLaw hℓn.le) =
      fun U => squaredResidual (diagonal (spikeSpectrum n))
        (U * (coordinateSketchProjector (Fin.castLEEmb hℓn.le)).val) /
          optimalSquaredTail k (spikeSpectrum n) :=
    funext (coordinateSpike_fixedConditional_loss_eq hℓn.le)
  rw [h]
  exact coordinateSpike_fixedProjector_loss_law hk hkn hℓ hℓn _

private theorem map_prod_constant_fiber {A X Y : Type*}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure A) (μ : Measure X) (ρ : Measure Y)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {f : A × X → Y} (hf : Measurable f) (h : ∀ a, μ.map (fun x => f (a, x)) = ρ) :
    (ν.prod μ).map f = ρ := by
  ext S hS
  rw [Measure.map_apply hf hS, Measure.prod_apply (hf hS)]
  have hFiber (a : A) : μ (Prod.mk a ⁻¹' (f ⁻¹' S)) = ρ S := by
    have hMeas : Measurable (fun x => f (a, x)) := hf.comp measurable_prodMk_left
    rw [← h a, Measure.map_apply hMeas hS]
    rfl
  simp_rw [hFiber]
  simp

/-- Drawing the coordinates independently of the orientation has the same
one-draw residual law as fixing the coordinates before drawing the orientation. -/
theorem coordinateSpike_fresh_loss_law {n k ℓ : ℕ} (hk : 0 < k) (hkn : k < n)
    (hℓ : 0 < ℓ) (hℓn : ℓ < n) :
    ((uniformCoordinateSketchLaw n ℓ).prod (gaussianRightOrthogonalLaw n)).map
      (fun z => squaredResidual (diagonal (spikeSpectrum n)) (z.2 * z.1.val) /
        optimalSquaredTail k (spikeSpectrum n)) =
      (gaussianRightOrthogonalLaw n).map
        (conditionalMean k (spikeSpectrum n) (fixedCoordinateSketchLaw hℓn.le)) := by
  let := isProbabilityMeasure_uniformCoordinateSketchLaw hℓn.le
  rw [coordinateSpike_fixedConditional_law hk hkn hℓ hℓn]
  let f (z : OrthogonalProjector n ℓ × Orientation n) :=
    squaredResidual (diagonal (spikeSpectrum n)) (z.2 * z.1.val) /
      optimalSquaredTail k (spikeSpectrum n)
  change ((uniformCoordinateSketchLaw n ℓ).prod (gaussianRightOrthogonalLaw n)).map f = _
  have hf : Measurable f := by
    have hP : Measurable (fun z : OrthogonalProjector n ℓ × Orientation n => z.1.val) :=
      measurable_subtype_coe.comp measurable_fst
    have hM : Measurable (fun z : OrthogonalProjector n ℓ × Orientation n => z.2 * z.1.val) :=
      measurable_matrix_product measurable_snd hP
    exact (measurable_rawResidual measurable_const hM).div_const _
  exact map_prod_constant_fiber _ _ _ hf
    (fun P => coordinateSpike_fixedProjector_loss_law hk hkn hℓ hℓn P)

private theorem measurable_coordinateEnergy (n : ℕ) : Measurable (gaussianCoordinateEnergy n) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i.val).pow_const 2

private theorem gaussianCoordinateEnergy_nonneg (n : ℕ) (ω : ℕ → ℝ) :
    0 ≤ gaussianCoordinateEnergy n ω :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem measurable_coupledCoordinateFraction (n ℓ : ℕ) :
    Measurable (coupledSpikeFraction n ℓ) :=
  (measurable_coordinateEnergy ℓ).div (measurable_coordinateEnergy n)

private noncomputable def coupledCoordinateLoss (n k ℓ : ℕ) (ω : ℕ → ℝ) : ℝ :=
  coordinateSpikeLoss n k ℓ (coupledSpikeFraction n ℓ ω)

private theorem measurable_coupledCoordinateLoss (n k ℓ : ℕ) :
    Measurable (coupledCoordinateLoss n k ℓ) :=
  (measurable_coordinateSpikeLoss n k ℓ).comp (measurable_coupledCoordinateFraction n ℓ)

private theorem coupledCoordinateLoss_law {n k ℓ : ℕ} (hℓ : 0 < ℓ) (hℓn : ℓ < n) :
    infiniteGaussianCoordinateLaw.map (coupledCoordinateLoss n k ℓ) =
      (projectionBetaLaw n ℓ).map (coordinateSpikeLoss n k ℓ) := by
  rw [show coupledCoordinateLoss n k ℓ = coordinateSpikeLoss n k ℓ ∘ coupledSpikeFraction n ℓ
    from rfl, ← Measure.map_map (measurable_coordinateSpikeLoss _ _ _)
      (measurable_coupledCoordinateFraction _ _), coupledSpikeFraction_law hℓ hℓn]

private theorem coordinateSpikeCoeff_tendsto (k ℓ : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) - ℓ - 1) / ((n : ℝ) - k)) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) - k)) atTop (𝓝 1) := by
  have hDen : Tendsto (fun n : ℕ => (n : ℝ) - k) atTop atTop :=
    tendsto_atTop_add_const_right _ (-(k : ℝ))
      tendsto_natCast_atTop_atTop
  have h (a : ℝ) :
      Tendsto (fun n : ℕ => ((n : ℝ) + a) / ((n : ℝ) - k)) atTop (𝓝 1) := by
    have hSmall : Tendsto (fun n : ℕ => (a + k) / ((n : ℝ) - k)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hDen
    have hSum : Tendsto (fun n : ℕ => 1 + (a + k) / ((n : ℝ) - k)) atTop (𝓝 1) := by
      simpa using hSmall.const_add 1
    apply hSum.congr'
    filter_upwards [eventually_gt_atTop k] with n hn
    have hNe : (n : ℝ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn.ne')
    field_simp
    ring
  exact ⟨by simpa [sub_eq_add_neg, add_assoc] using h (-(ℓ : ℝ) - 1), h 1⟩

private theorem coupledCoordinateReciprocal_ae_tendsto (ℓ : ℕ) :
    ∀ᵐ ω ∂infiniteGaussianCoordinateLaw,
      Tendsto (fun n => spikeReciprocal n (coupledSpikeFraction n ℓ ω))
        atTop (𝓝 ((1 + gaussianCoordinateEnergy ℓ ω)⁻¹)) := by
  filter_upwards [gaussianCoordinateEnergy_strongLaw] with ω hω
  have ha : Tendsto (fun n => gaussianCoordinateEnergy ℓ ω /
      (gaussianCoordinateEnergy n ω / (n : ℝ))) atTop (𝓝 (gaussianCoordinateEnergy ℓ ω)) := by
    have h := (tendsto_const_nhds (x := gaussianCoordinateEnergy ℓ ω)).div hω one_ne_zero
    rw [div_one] at h
    exact h.congr (fun _ => rfl)
  have hp : (1 : ℝ) + gaussianCoordinateEnergy ℓ ω ≠ 0 :=
    (add_pos_of_pos_of_nonneg zero_lt_one (gaussianCoordinateEnergy_nonneg ℓ ω)).ne'
  apply ((ha.const_add 1).inv₀ hp).congr
  intro n
  change (1 + gaussianCoordinateEnergy ℓ ω / (gaussianCoordinateEnergy n ω / (n : ℝ)))⁻¹ =
    (1 + (n : ℝ) * (gaussianCoordinateEnergy ℓ ω / gaussianCoordinateEnergy n ω))⁻¹
  simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
  congr 1
  ring

private theorem coordinateChiSquareProbability {ℓ : ℕ} (hℓ : 0 < ℓ) :
    IsProbabilityMeasure (chiSquareLaw ℓ) := by
  exact isProbabilityMeasure_gammaMeasure (half_pos (Nat.cast_pos.mpr hℓ)) (by norm_num)

private theorem tendstoInDistribution_of_same_laws {E A B : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace A] [MeasurableSpace B] {X Y : ℕ → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (Y j)]
    {μ : ∀ j, Measure (X j)} {ν : ∀ j, Measure (Y j)}
    {μ' : Measure A} {ν' : Measure B} [∀ j, IsProbabilityMeasure (μ j)]
    [∀ j, IsProbabilityMeasure (ν j)] [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    {f : ∀ j, X j → E} {g : ∀ j, Y j → E} {F : A → E} {G : B → E}
    (h : TendstoInDistribution g atTop G ν ν')
    (hf : ∀ j, AEMeasurable (f j) (μ j)) (hF : AEMeasurable F μ')
    (heq : ∀ j, (μ j).map (f j) = (ν j).map (g j)) (hEq : μ'.map F = ν'.map G) :
    TendstoInDistribution f atTop F μ μ' := by
  refine ⟨hf, hF, ?_⟩
  have hSeq :
      (fun j => (⟨(μ j).map (f j), Measure.isProbabilityMeasure_map (hf j)⟩ : ProbabilityMeasure E)) =
        (fun j => ⟨(ν j).map (g j), Measure.isProbabilityMeasure_map (h.forall_aemeasurable j)⟩) :=
    funext fun j => Subtype.ext (heq j)
  have hLim :
      (⟨μ'.map F, Measure.isProbabilityMeasure_map hF⟩ : ProbabilityMeasure E) =
        ⟨ν'.map G, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩ :=
    Subtype.ext hEq
  rw [hSeq, hLim]
  exact h.tendsto

/-- In the fixed-coordinate experiment the actual conditional residual tends
in law to (1+(1+Y)^{-1}), for (Y) with ℓ chi-square degrees of freedom. -/
theorem coordinateSpike_fixedConditional_tendstoInDistribution {d : ℕ → ℕ} {k ℓ : ℕ}
    (hk : 0 < k) (hkd : ∀ j, k < d j) (hℓ : 0 < ℓ) (hℓd : ∀ j, ℓ < d j)
    (hd : Tendsto d atTop atTop) :
    letI : IsProbabilityMeasure (chiSquareLaw ℓ) :=
      coordinateChiSquareProbability hℓ
    TendstoInDistribution
      (fun j => conditionalMean k (spikeSpectrum (d j)) (fixedCoordinateSketchLaw (hℓd j).le))
      atTop (fun y : ℝ => 1 + (1 + y)⁻¹)
      (fun j => gaussianRightOrthogonalLaw (d j)) (chiSquareLaw ℓ) := by
  let := coordinateChiSquareProbability hℓ
  let G (y : ℝ) := 1 + (1 + y)⁻¹
  have hG : Measurable G := ((measurable_id.const_add 1).inv).const_add 1
  have hCoupled : TendstoInDistribution (fun j => coupledCoordinateLoss (d j) k ℓ) atTop
      (fun ω => G (gaussianCoordinateEnergy ℓ ω)) (fun _ => infiniteGaussianCoordinateLaw)
      infiniteGaussianCoordinateLaw := by
    apply tendstoInDistribution_of_ae_tendsto
    · intro j
      exact (measurable_coupledCoordinateLoss (d j) k ℓ).aemeasurable
    · exact (hG.comp (measurable_coordinateEnergy ℓ)).aemeasurable
    · filter_upwards [coupledCoordinateReciprocal_ae_tendsto ℓ] with ω hω
      have h := ((coordinateSpikeCoeff_tendsto k ℓ).1.comp hd).add
        (((coordinateSpikeCoeff_tendsto k ℓ).2.comp hd).mul (hω.comp hd))
      rw [one_mul] at h
      exact h.congr (fun _ => rfl)
  apply tendstoInDistribution_of_same_laws hCoupled
    (fun j => (measurable_conditionalMean k (spikeSpectrum (d j)) _).aemeasurable)
    hG.aemeasurable
  · intro j
    exact (coordinateSpike_fixedConditional_law hk (hkd j) hℓ (hℓd j)).trans
      (coupledCoordinateLoss_law hℓ (hℓd j)).symm
  · change (chiSquareLaw ℓ).map G = infiniteGaussianCoordinateLaw.map
      (G ∘ gaussianCoordinateEnergy ℓ)
    rw [← Measure.map_map hG (measurable_coordinateEnergy ℓ), gaussianCoordinateEnergy_law hℓ]

/-- The Gaussian-sketched benchmark has the same mean as the fixed-coordinate
one-draw residual at each finite dimension. -/
theorem coordinateSpike_gaussianMean_eq {n k ℓ : ℕ}
    (hk : 0 < k) (hkn : k < n) (hℓ : 0 < ℓ) (hℓn : ℓ < n) :
    gaussianMean k ℓ (spikeSpectrum n) =
      ∫ ω, coupledCoordinateLoss n k ℓ ω ∂infiniteGaussianCoordinateLaw := by
  let μ := fixedCoordinateSketchLaw hℓn.le
  have htail : 0 < optimalSquaredTail k (spikeSpectrum n) :=
    (oneSpikeSpectra hk hkn).property.2.2
  rw [← conditionalMean_integral_eq_gaussianMean hℓn.le k _ htail μ]
  change (∫ U, id (conditionalMean k (spikeSpectrum n) μ U)
    ∂gaussianRightOrthogonalLaw n) =
      ∫ ω, id (coupledCoordinateLoss n k ℓ ω) ∂infiniteGaussianCoordinateLaw
  rw [← integral_map (measurable_conditionalMean k (spikeSpectrum n) μ).aemeasurable
    measurable_id.aestronglyMeasurable,
    ← integral_map (measurable_coupledCoordinateLoss n k ℓ).aemeasurable
      measurable_id.aestronglyMeasurable]
  change (∫ x : ℝ, id x ∂(gaussianRightOrthogonalLaw n).map
    (conditionalMean k (spikeSpectrum n) μ)) =
      ∫ x : ℝ, id x ∂infiniteGaussianCoordinateLaw.map (coupledCoordinateLoss n k ℓ)
  rw [coordinateSpike_fixedConditional_law hk hkn hℓ hℓn, coupledCoordinateLoss_law hℓ hℓn]

private theorem coordinateReciprocal_mem_Icc (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    spikeReciprocal n t ∈ Set.Icc (0 : ℝ) 1 := by
  have h : 1 ≤ 1 + (n : ℝ) * t :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) ht)
  exact ⟨inv_nonneg.mpr (zero_le_one.trans h), inv_le_one_of_one_le₀ h⟩

private theorem coupledCoordinateReciprocal_mean_tendsto {ℓ : ℕ} (hℓ : 0 < ℓ) :
    Tendsto (fun n => ∫ ω, spikeReciprocal n (coupledSpikeFraction n ℓ ω)
      ∂infiniteGaussianCoordinateLaw) atTop
      (𝓝 (∫ y, (1 + y)⁻¹ ∂chiSquareLaw ℓ)) := by
  have hF (n : ℕ) : Measurable
      (fun ω => spikeReciprocal n (coupledSpikeFraction n ℓ ω)) :=
    (((measurable_coupledCoordinateFraction n ℓ).const_mul (n : ℝ)).const_add 1).inv
  have hG : Measurable (fun y : ℝ => (1 + y)⁻¹) := (measurable_id.const_add 1).inv
  rw [← gaussianCoordinateEnergy_law hℓ, integral_map (measurable_coordinateEnergy ℓ).aemeasurable
    hG.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · exact fun n => (hF n).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    refine ae_of_all _ fun ω => ?_
    obtain ⟨h0, h1⟩ := coordinateReciprocal_mem_Icc n
      (div_nonneg (gaussianCoordinateEnergy_nonneg ℓ ω) (gaussianCoordinateEnergy_nonneg n ω))
    change ‖spikeReciprocal n
      (gaussianCoordinateEnergy ℓ ω / gaussianCoordinateEnergy n ω)‖ ≤ 1
    rw [Real.norm_of_nonneg h0]
    exact h1
  · exact coupledCoordinateReciprocal_ae_tendsto ℓ

/-- The Gaussian benchmark converges to the constant stated in the example. -/
theorem coordinateSpike_gaussianMean_tendsto {d : ℕ → ℕ} {k ℓ : ℕ}
    (hk : 0 < k) (hkd : ∀ j, k < d j) (hℓ : 0 < ℓ) (hℓd : ∀ j, ℓ < d j)
    (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => gaussianMean k ℓ (spikeSpectrum (d j)))
      atTop (𝓝 (1 + ∫ y, (1 + y)⁻¹ ∂chiSquareLaw ℓ)) := by
  have h := (coordinateSpikeCoeff_tendsto k ℓ).1.add
    ((coordinateSpikeCoeff_tendsto k ℓ).2.mul (coupledCoordinateReciprocal_mean_tendsto hℓ))
  rw [one_mul] at h
  apply (h.comp hd).congr
  intro j
  rw [coordinateSpike_gaussianMean_eq hk (hkd j) hℓ (hℓd j)]
  let n := d j
  let f (ω : ℕ → ℝ) := spikeReciprocal n (coupledSpikeFraction n ℓ ω)
  let c := ((n : ℝ) - ℓ - 1) / ((n : ℝ) - k)
  let a := ((n : ℝ) + 1) / ((n : ℝ) - k)
  have hF : Integrable f infiniteGaussianCoordinateLaw := by
    have hf : Measurable f := (((measurable_coupledCoordinateFraction n ℓ).const_mul
      (n : ℝ)).const_add 1).inv
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    refine ae_of_all _ fun ω => ?_
    obtain ⟨h0, h1⟩ := coordinateReciprocal_mem_Icc n
      (div_nonneg (gaussianCoordinateEnergy_nonneg ℓ ω) (gaussianCoordinateEnergy_nonneg n ω))
    change ‖spikeReciprocal n
      (gaussianCoordinateEnergy ℓ ω / gaussianCoordinateEnergy n ω)‖ ≤ 1
    rw [Real.norm_of_nonneg h0]
    exact h1
  change c + a * (∫ ω, f ω ∂infiniteGaussianCoordinateLaw) =
    ∫ ω, c + a * f ω ∂infiniteGaussianCoordinateLaw
  rw [integral_add (integrable_const _) (hF.const_mul _), integral_const_mul]
  simp

/-- The `ℓ` distinct coordinates of the actual spherical spike, scaled by
`√n`. The embedding fixes the order of the reported coordinates. -/
noncomputable def scaledCoordinateSpikeReadout {n ℓ : ℕ} (hn : 0 < n)
    (J : Fin ℓ ↪ Fin n) (U : Orientation n) : Ambient ℓ :=
  Real.sqrt n • (rowSelector J).toEuclideanLin (coordinateSpikeDirection hn U)

private theorem measurable_scaledCoordinateSpikeReadout {n ℓ : ℕ} (hn : 0 < n)
    (J : Fin ℓ ↪ Fin n) : Measurable (scaledCoordinateSpikeReadout hn J) :=
  by
    have h : Measurable (fun U => (rowSelector J).toEuclideanLin (coordinateSpikeDirection hn U)) :=
      (rowSelector J).toEuclideanLin.continuous_of_finiteDimensional.measurable.comp
        (measurable_coordinateSpikeDirection hn)
    exact h.const_smul (Real.sqrt n)

/-- At finite dimension all distinct ordered coordinate readouts have the same law. -/
theorem scaledCoordinateSpikeReadout_law_equal {n ℓ : ℕ} (hn : 0 < n)
    (J J' : Fin ℓ ↪ Fin n) :
    (gaussianRightOrthogonalLaw n).map (scaledCoordinateSpikeReadout hn J) =
      (gaussianRightOrthogonalLaw n).map (scaledCoordinateSpikeReadout hn J') := by
  have hJ : ((rowSelector J)ᵀ)ᵀ * (rowSelector J)ᵀ = 1 := by
    rw [transpose_transpose, rowSelector_orthonormal]
  have hJ' : ((rowSelector J')ᵀ)ᵀ * (rowSelector J')ᵀ = 1 := by
    rw [transpose_transpose, rowSelector_orthonormal]
  have hℓn : ℓ ≤ n := by simpa using Fintype.card_le_of_injective J J.injective
  obtain ⟨Q, hQ, he⟩ := exists_orthogonal_mul_frame_eq hℓn hJ hJ'
  let R : Orientation n → Orientation n := fun U => U * Q
  have hR : Measurable R := (continuous_id.matrix_mul continuous_const).measurable
  have hEq : scaledCoordinateSpikeReadout hn J ∘ R = scaledCoordinateSpikeReadout hn J' := by
    funext U
    have hRow : rowSelector J * Qᵀ = rowSelector J' := by
      have h := congrArg Matrix.transpose he
      simpa only [transpose_mul, transpose_transpose] using h
    simp only [Function.comp_apply, scaledCoordinateSpikeReadout, coordinateSpikeDirection, R,
      transpose_mul, euclidean_mul, LinearMap.comp_apply]
    rw [← LinearMap.comp_apply ((rowSelector J).toEuclideanLin) Qᵀ.toEuclideanLin,
      ← euclidean_mul, hRow]
  nth_rw 1 [← gaussianRightOrthogonalLaw_map_right Q hQ]
  rw [Measure.map_map (measurable_scaledCoordinateSpikeReadout hn J) hR, hEq]

/-- The independent fresh selector has the same finite vector law as the
fixed selector, before the sketch is averaged at fixed orientation. -/
theorem scaledCoordinateSpikeReadout_fresh_law {n ℓ : ℕ} (hn : 0 < n) (hℓn : ℓ ≤ n) :
    ((uniformCoordinateSubsetLaw n ℓ).prod (gaussianRightOrthogonalLaw n)).map
      (fun z => scaledCoordinateSpikeReadout hn (coordinateSubsetEmbedding z.1) z.2) =
      (gaussianRightOrthogonalLaw n).map
        (scaledCoordinateSpikeReadout hn (Fin.castLEEmb hℓn)) := by
  have hNE : Nonempty (CoordinateSubset n ℓ) :=
    ⟨⟨Finset.univ.map (Fin.castLEEmb hℓn), by simp⟩⟩
  let : IsProbabilityMeasure (uniformCoordinateSubsetLaw n ℓ) := by
    unfold uniformCoordinateSubsetLaw
    infer_instance
  apply map_prod_constant_fiber
  · exact measurable_from_prod_countable_right fun s =>
      measurable_scaledCoordinateSpikeReadout hn (coordinateSubsetEmbedding s)
  · exact fun s => scaledCoordinateSpikeReadout_law_equal hn
      (coordinateSubsetEmbedding s) (Fin.castLEEmb hℓn)

private noncomputable def gaussianCoordinatePrefix (n : ℕ) (ω : ℕ → ℝ) : Ambient n :=
  WithLp.toLp 2 (fun i : Fin n => ω i.val)

private theorem measurable_gaussianCoordinatePrefix (n : ℕ) :
    Measurable (gaussianCoordinatePrefix n) :=
  (WithLp.measurable_toLp _ _).comp (measurable_pi_lambda _ fun i => measurable_pi_apply i.val)

private theorem gaussianCoordinatePrefix_law (n : ℕ) :
    infiniteGaussianCoordinateLaw.map (gaussianCoordinatePrefix n) = stdGaussian (Ambient n) := by
  let f (ω : ℕ → ℝ) (i : Fin n) := ω i.val
  have hf : Measurable f := measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hTo : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → Ambient n) := WithLp.measurable_toLp _ _
  change infiniteGaussianCoordinateLaw.map (WithLp.toLp 2 ∘ f) = _
  rw [← Measure.map_map hTo hf]
  change ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map f).map (WithLp.toLp 2) = _
  rw [show (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map f =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) from
    infiniteProduct_map_embedding (gaussianReal 0 1) (Fin.valEmbedding (n := n)), map_pi_eq_stdGaussian]

private noncomputable def coupledCoordinateReadout (n ℓ : ℕ) (ω : ℕ → ℝ) : Ambient ℓ :=
  (Real.sqrt (gaussianCoordinateEnergy n ω / (n : ℝ)))⁻¹ • gaussianCoordinatePrefix ℓ ω

private theorem measurable_coupledCoordinateReadout (n ℓ : ℕ) :
    Measurable (coupledCoordinateReadout n ℓ) :=
  (Real.continuous_sqrt.measurable.comp ((measurable_coordinateEnergy n).div_const
    (n : ℝ))).inv.smul (measurable_gaussianCoordinatePrefix ℓ)

private theorem coupledCoordinateReadout_law {n ℓ : ℕ} (hn : 0 < n) (hℓn : ℓ ≤ n) :
    (gaussianRightOrthogonalLaw n).map (scaledCoordinateSpikeReadout hn (Fin.castLEEmb hℓn)) =
      infiniteGaussianCoordinateLaw.map (coupledCoordinateReadout n ℓ) := by
  let J := Fin.castLEEmb hℓn
  let r (x : Ambient n) := Real.sqrt n • (rowSelector J).toEuclideanLin x
  have hr : Measurable r :=
    (rowSelector J).toEuclideanLin.continuous_of_finiteDimensional.measurable.const_smul (Real.sqrt n)
  change (gaussianRightOrthogonalLaw n).map (r ∘ coordinateSpikeDirection hn) = _
  rw [← Measure.map_map hr (measurable_coordinateSpikeDirection hn), coordinateSpikeDirection_law,
    ← gaussianCoordinatePrefix_law n,
    Measure.map_map measurable_sphereNormalize (measurable_gaussianCoordinatePrefix n),
    Measure.map_map hr (measurable_sphereNormalize.comp (measurable_gaussianCoordinatePrefix n))]
  congr 1
  funext ω
  have hNorm : ‖gaussianCoordinatePrefix n ω‖ = Real.sqrt (gaussianCoordinateEnergy n ω) := by
    have hsq : ‖gaussianCoordinatePrefix n ω‖ ^ 2 = gaussianCoordinateEnergy n ω :=
      EuclideanSpace.real_norm_sq_eq (gaussianCoordinatePrefix n ω)
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hRows : (rowSelector J).toEuclideanLin (gaussianCoordinatePrefix n ω) =
      gaussianCoordinatePrefix ℓ ω := by
    ext i
    change ((rowSelector J) *ᵥ (fun j : Fin n => ω j.val)) i = ω i.val
    simp [Matrix.mulVec, dotProduct, rowSelector, J]
  show r (sphereNormalize (gaussianCoordinatePrefix n ω)) = coupledCoordinateReadout n ℓ ω
  dsimp only [r]
  rw [sphereNormalize, map_smul, smul_smul, hNorm, hRows, coupledCoordinateReadout,
    Real.sqrt_div (gaussianCoordinateEnergy_nonneg n ω), inv_div, div_eq_mul_inv]

/-- For any selectors of ℓ distinct coordinates, the scaled readout tends
jointly in law to ℓ independent standard Gaussian coordinates. -/
theorem scaledCoordinateSpikeReadout_tendstoInDistribution {d : ℕ → ℕ} {ℓ : ℕ}
    (hnd : ∀ j, 0 < d j) (hℓd : ∀ j, ℓ ≤ d j) (hd : Tendsto d atTop atTop)
    (J : ∀ j, Fin ℓ ↪ Fin (d j)) :
    TendstoInDistribution (fun j => scaledCoordinateSpikeReadout (hnd j) (J j)) atTop
      (id : Ambient ℓ → Ambient ℓ) (fun j => gaussianRightOrthogonalLaw (d j))
      (stdGaussian (Ambient ℓ)) := by
  have hCoupled : TendstoInDistribution (fun j => coupledCoordinateReadout (d j) ℓ)
      atTop (gaussianCoordinatePrefix ℓ) (fun _ => infiniteGaussianCoordinateLaw)
      infiniteGaussianCoordinateLaw := by
    apply tendstoInDistribution_of_ae_tendsto
    · exact fun j => (measurable_coupledCoordinateReadout (d j) ℓ).aemeasurable
    · exact (measurable_gaussianCoordinatePrefix ℓ).aemeasurable
    · filter_upwards [gaussianCoordinateEnergy_strongLaw] with ω hω
      have hs := ((Real.continuous_sqrt.tendsto 1).comp (hω.comp hd))
      rw [Real.sqrt_one] at hs
      have h := (hs.inv₀ one_ne_zero).smul
        (tendsto_const_nhds (x := gaussianCoordinatePrefix ℓ ω))
      rw [inv_one, one_smul] at h
      exact h.congr (fun _ => rfl)
  apply tendstoInDistribution_of_same_laws hCoupled
    (fun j => (measurable_scaledCoordinateSpikeReadout (hnd j) (J j)).aemeasurable)
    measurable_id.aemeasurable
  · intro j
    exact (scaledCoordinateSpikeReadout_law_equal (hnd j) (J j) _).trans
      (coupledCoordinateReadout_law (hnd j) (hℓd j))
  · rw [Measure.map_id, gaussianCoordinatePrefix_law]

/-- The uniform coordinate law has mean projector norm exactly `ℓ / n`. -/
theorem coordinateSpike_uniform_meanProjectorNorm {n ℓ : ℕ} (hn : 0 < n) (hℓn : ℓ ≤ n) :
    meanProjectorNorm (uniformCoordinateSketchLaw n ℓ) = (ℓ : ℝ) / n :=
  uniformCoordinateSketch_mean_norm hn hℓn

/-- The fixed-coordinate limiting law still fluctuates: it has no atoms. -/
theorem coordinateSpike_limit_no_atoms {ℓ : ℕ} (x : ℝ) :
    ((chiSquareLaw ℓ).map (fun y : ℝ => 1 + (1 + y)⁻¹)) {x} = 0 := by
  have hMeas : Measurable (fun y : ℝ => 1 + (1 + y)⁻¹) :=
    ((measurable_id.const_add 1).inv).const_add 1
  rw [Measure.map_apply hMeas (measurableSet_singleton x)]
  have hSet : (fun y : ℝ => 1 + (1 + y)⁻¹) ⁻¹' {x} = {(x - 1)⁻¹ - 1} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← h, add_sub_cancel_left, inv_inv, add_sub_cancel_left]
    · intro h
      rw [h, show 1 + ((x - 1)⁻¹ - 1) = (x - 1)⁻¹ by ring, inv_inv]
      ring
  rw [hSet]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton _)

/-- The main criterion supplies convergence of the discrepancy for uniform
coordinates, by the exact mean projector norm above. This theorem transports
it to the actual spike example using the finite Gaussian center and its limit. -/
theorem coordinateSpike_uniformConditional_tendsto_L1_of_discrepancy
    {d : ℕ → ℕ} {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (hℓd : ∀ j, k + p < d j) (hd : Tendsto d atTop atTop)
    (hD : Tendsto (fun j => meanDiscrepancy k (uniformCoordinateSketchLaw (d j) (k+p)))
      atTop (𝓝 0)) :
    Tendsto (fun j =>
      ∫ U, |conditionalMean k (spikeSpectrum (d j)) (uniformCoordinateSketchLaw (d j) (k+p)) U -
        (1 + ∫ y, (1 + y)⁻¹ ∂chiSquareLaw (k+p))| ∂gaussianRightOrthogonalLaw (d j)) atTop
        (𝓝 0) := by
  let ℓ := k + p
  have hℓ : 0 < ℓ := by omega
  have hkd : ∀ j, k < d j := fun j => lt_of_le_of_lt (Nat.le_add_right _ _) (hℓd j)
  let g (j : ℕ) := gaussianMean k ℓ (spikeSpectrum (d j))
  let D (j : ℕ) := meanDiscrepancy k (uniformCoordinateSketchLaw (d j) ℓ)
  let c := 1 + ∫ y, (1 + y)⁻¹ ∂chiSquareLaw ℓ
  have hg : Tendsto g atTop (𝓝 c) :=
    coordinateSpike_gaussianMean_tendsto hk hkd hℓ hℓd hd
  have hLim : Tendsto (fun j => D j + |g j - c|) atTop (𝓝 0) := by
    have h := ((hg.sub_const c).abs)
    rw [sub_self, abs_zero] at h
    simpa only [add_zero] using hD.add h
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
    _ hLim
  refine Eventually.of_forall fun j => ?_
  let n := d j
  let μ := uniformCoordinateSketchLaw n ℓ
  let := isProbabilityMeasure_uniformCoordinateSketchLaw (hℓd j).le
  let η := gaussianRightOrthogonalLaw n
  let σ := oneSpikeSpectra hk (hkd j)
  let F := conditionalMean k σ.val μ
  let C := squaredFrobenius (diagonal σ.val) / optimalSquaredTail k σ.val
  have hF : Measurable F := measurable_conditionalMean k σ.val μ
  have hFB (U : Orientation n) : ‖F U‖ ≤ C := by
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun P => squaredResidual (diagonal σ.val) (U * P.val) / optimalSquaredTail k σ.val)
      (C := C) (ae_of_all _ fun P => by
        rw [Real.norm_of_nonneg (residual_div_tail_nonneg k σ.val σ.property.2.2 _)]
        exact residual_div_tail_le k σ.val σ.property.2.2 _)
    simpa only [F, conditionalMean, probReal_univ, mul_one] using h
  have hFI : Integrable F η := Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hFB)
  have hGapI : Integrable (fun U => |F U - g j|) η :=
    (hFI.sub (integrable_const (g j))).abs
  have hD' : (∫ U, |F U - g j| ∂η) ≤ D j :=
    le_csSup (meanDiscrepancy_bddAbove hk hp (hℓd j).le μ) (Set.mem_range_self σ)
  change (∫ U, |F U - c| ∂η) ≤ D j + |g j - c|
  calc
    _ ≤ ∫ U, (|F U - g j| + |g j - c|) ∂η := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
        (hGapI.add (integrable_const _))
      refine ae_of_all _ fun U => ?_
      change |F U - c| ≤ |F U - g j| + |g j - c|
      rw [show F U - c = (F U - g j) + (g j - c) by ring]
      exact abs_add_le _ _
    _ = (∫ U, |F U - g j| ∂η) + |g j - c| := by
      rw [integral_add hGapI (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ _ := add_le_add hD' le_rfl

/-- For the actual uniform-coordinate conditional mean, the manuscript's
criterion and the exact mean projector norm give the stated constant in L¹. -/
theorem coordinateSpike_uniformConditional_tendsto_L1
    {d : ℕ → ℕ} {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (hℓd : ∀ j, k + p < d j) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j =>
      ∫ U, |conditionalMean k (spikeSpectrum (d j)) (uniformCoordinateSketchLaw (d j) (k+p)) U -
        (1 + ∫ y, (1 + y)⁻¹ ∂chiSquareLaw (k+p))| ∂gaussianRightOrthogonalLaw (d j)) atTop
        (𝓝 0) := by
  let μ (j : ℕ) := uniformCoordinateSketchLaw (d j) (k+p)
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    isProbabilityMeasure_uniformCoordinateSketchLaw (hℓd j).le
  have hρ : Tendsto (fun j => meanProjectorNorm (μ j)) atTop (𝓝 0) := by
    have h : Tendsto (fun j => ((k+p : ℕ) : ℝ) / (d j : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hd)
    apply h.congr
    intro j
    exact (coordinateSpike_uniform_meanProjectorNorm
      (Nat.zero_lt_of_lt (hℓd j)) (hℓd j).le).symm
  have hD := (theorem_1_1 hk hp d hd (fun j => (hℓd j).le) μ).1.mp hρ
  exact coordinateSpike_uniformConditional_tendsto_L1_of_discrepancy hk hp hℓd hd hD

end TypicalOrientations
