import TypicalOrientations.SpikeBridge
import TypicalOrientations.SpikeLimit
import TypicalOrientations.SpikeVariance
import TypicalOrientations.BenchmarkBound

namespace TypicalOrientations

open MeasureTheory ProbabilityTheory SketchOrientation Filter
open scoped Topology InnerProductSpace

private abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem spikeScalarCovariance_eventually_lower {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∀ᶠ n in atTop, spikeLimitGap ℓ / 2 ≤ |spikeScalarCovariance n ℓ| := by
  have hB := spikeLimitGap_pos hℓ
  have h := (spikeScalarCovariance_tendsto hℓ).eventually_lt_const
    (show -spikeLimitGap ℓ < -(spikeLimitGap ℓ / 2) by linarith)
  filter_upwards [h] with n hn
  exact (neg_le_abs _).trans' (by linarith)

set_option maxHeartbeats 1100000 in
private theorem spike_spherical_deviation_lower {n ℓ : ℕ} (hℓ : 0 < ℓ) (hℓn : ℓ < n)
    (hScalar : spikeLimitGap ℓ / 2 ≤ |spikeScalarCovariance n ℓ|)
    (μ : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure μ] :
    spikeLimitGap ℓ ^ 2 / (8 * (ℓ : ℝ)^2) * (meanProjectorNorm μ - (ℓ : ℝ) / n)^2 ≤
      ∫ x, |spikeConditionalAverage μ x -
        ∫ y, spikeConditionalAverage μ y ∂stdGaussian (Ambient n)| ∂stdGaussian (Ambient n) := by
  let γ := stdGaussian (Ambient n)
  let d := meanProjectorNorm μ - (ℓ : ℝ) / n
  let b := spikeLimitGap ℓ
  let J := spikeConditionalAverage μ
  have hn : 0 < n := hℓ.trans hℓn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hℓR : (0 : ℝ) < ℓ := Nat.cast_pos.mpr hℓ
  have hSub : 0 < (n : ℝ) - ℓ := sub_pos.mpr (by exact_mod_cast hℓn)
  have hD : 0 ≤ d := by
    have h := sketchRank_le_dim_mul_meanProjectedEnergy μ
    rw [meanProjectedEnergy_eq_meanSketchProjector_norm hn] at h
    change (ℓ : ℝ) ≤ (n : ℝ) * meanProjectorNorm μ at h
    rw [mul_comm] at h
    exact sub_nonneg.mpr ((div_le_iff₀ hnR).mpr h)
  have hB : 0 < b := spikeLimitGap_pos hℓ
  obtain ⟨u, hu, huRay⟩ := exists_unit_meanSketchProjector_rayleigh_eq_norm hn μ
  let C := covariance J (spikeDirectionalTest u) γ
  have hCov : C = (n : ℝ) / ((ℓ : ℝ) * ((n : ℝ) - ℓ)) * d * spikeScalarCovariance n ℓ := by
    unfold C J γ
    rw [spikeConditionalAverage_covariance hℓ hℓn μ u hu, huRay]
    rfl
  have hPre : 1 / (ℓ : ℝ) ≤ (n : ℝ) / ((ℓ : ℝ) * ((n : ℝ) - ℓ)) := by
    apply (div_le_div_iff₀ hℓR (mul_pos hℓR hSub)).mpr
    nlinarith
  have hA : b * d / (2 * (ℓ : ℝ)) ≤ |C| := by
    rw [hCov, abs_mul, abs_mul,
      abs_of_nonneg (div_nonneg hnR.le (mul_pos hℓR hSub).le), abs_of_nonneg hD]
    calc
      _ = (1 / (ℓ : ℝ)) * d * (b / 2) := by field_simp
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hPre hD) hScalar
        (by positivity) (by positivity)
  have hA2 := pow_le_pow_left₀ (div_nonneg (mul_nonneg hB.le hD) (by positivity)) hA 2
  have hNorm : (b * d / (2 * (ℓ : ℝ)))^2 = 2 * (b^2 / (8 * (ℓ : ℝ)^2) * d^2) := by
    field_simp [hℓR.ne']
    ring
  rw [hNorm, sq_abs] at hA2
  have hCS := spike_covariance_sq_le_twice_deviation (show 1 < n by omega) μ u hu
  change C^2 ≤ 2 * (∫ x, |J x - ∫ y, J y ∂γ| ∂γ) at hCS
  change b^2 / (8 * (ℓ : ℝ)^2) * d^2 ≤ ∫ x, |J x - ∫ y, J y ∂γ| ∂γ
  linarith

/-- Finite-dimensional lower bound on the actual one-spike discrepancy,
with the precise manuscript coefficient once its scalar test is large enough. -/
theorem spikeSpectrum_discrepancy_lower {n k ℓ : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ)
    (hkn : k < n) (hℓn : ℓ < n)
    (hScalar : spikeLimitGap ℓ / 2 ≤ |spikeScalarCovariance n ℓ|)
    (μ : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure μ] :
    spikeLimitGap ℓ ^ 2 / (8 * (ℓ : ℝ)^2) * (meanProjectorNorm μ - (ℓ : ℝ) / n)^2 ≤
      ∫ U, |conditionalMean k (spikeSpectrum n) μ U - gaussianMean k ℓ (spikeSpectrum n)|
        ∂gaussianRightOrthogonalLaw n := by
  rw [spikeSpectrum_discrepancy_eq hk hkn hℓn.le μ]
  have hK : (k : ℝ) < n := by exact_mod_cast hkn
  have hOne : (1 : ℝ) ≤ ((n : ℝ) + 1) / ((n : ℝ) - k) := by
    apply (le_div_iff₀ (sub_pos.mpr hK)).mpr
    have hK0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  exact (spike_spherical_deviation_lower hℓ hℓn hScalar μ).trans
    (le_mul_of_one_le_left (integral_nonneg fun _ => abs_nonneg _) hOne)


/-- The lower coefficient in equation (two-sided). -/
noncomputable def spikeConverseConstant (ℓ : ℕ) : ℝ :=
  spikeLimitGap ℓ ^ 2 / (8 * (ℓ : ℝ)^2)

theorem spikeConverseConstant_pos {ℓ : ℕ} (hℓ : 0 < ℓ) : 0 < spikeConverseConstant ℓ := by
  unfold spikeConverseConstant
  exact div_pos (sq_pos_of_pos (spikeLimitGap_pos hℓ))
    (by positivity)

/-- Pass from the fixed-spike witness to the discrepancy supremum. Its
boundedness is supplied by the uniform-in-spectrum Gaussian moment. -/
theorem meanDiscrepancy_lower_of_scalar {n k ℓ : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ)
    (hkn : k < n) (hℓn : ℓ < n)
    (hScalar : spikeLimitGap ℓ / 2 ≤ |spikeScalarCovariance n ℓ|)
    (μ : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure μ]
    (hBound : BddAbove (Set.range fun σ : Spectra n k =>
      ∫ U, |conditionalMean k σ.val μ U - gaussianMean k ℓ σ.val|
        ∂gaussianRightOrthogonalLaw n)) :
    spikeConverseConstant ℓ * (meanProjectorNorm μ - (ℓ : ℝ) / n)^2 ≤ meanDiscrepancy k μ := by
  refine (spikeSpectrum_discrepancy_lower hk hℓ hkn hℓn hScalar μ).trans ?_
  unfold meanDiscrepancy
  exact le_csSup hBound ⟨oneSpikeSpectra hk hkn, rfl⟩


/-- Equation (two-sided), lower direction, for all sufficiently large
dimensions. The threshold depends only on the fixed width. -/
theorem meanDiscrepancy_eventually_lower {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p) :
    ∀ᶠ n in atTop, ∀ (μ : Measure (OrthogonalProjector n (k+p))) [_hμ : IsProbabilityMeasure μ],
      spikeConverseConstant (k+p) * (meanProjectorNorm μ - ((k+p : ℕ) : ℝ) / n)^2 ≤
        meanDiscrepancy k μ := by
  have hℓ : 0 < k + p := by omega
  filter_upwards [eventually_gt_atTop (k + p), spikeScalarCovariance_eventually_lower hℓ]
    with n hn hs μ _
  exact meanDiscrepancy_lower_of_scalar hk hℓ (by omega) hn hs μ
    (meanDiscrepancy_bddAbove hk hp hn.le μ)

/-- The necessary implication in the criterion, using only the single
spike and the quantitative covariance lower bound. -/
theorem meanProjectorNorm_tendsto_zero_of_discrepancy {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (μ : ∀ i, Measure (OrthogonalProjector (n i) (k+p))) [∀ i, IsProbabilityMeasure (μ i)]
    (hD : Tendsto (fun i => meanDiscrepancy k (μ i)) atTop (𝓝 0)) :
    Tendsto (fun i => meanProjectorNorm (μ i)) atTop (𝓝 0) := by
  let ℓ := k + p
  let c := spikeConverseConstant ℓ
  let d (i : ℕ) : ℝ := meanProjectorNorm (μ i) - (ℓ : ℝ) / (n i : ℝ)
  have hℓ : 0 < ℓ := by omega
  have hc : 0 < c := spikeConverseConstant_pos hℓ
  have hEventually := hn.eventually (meanDiscrepancy_eventually_lower hk hp)
  have hT : Tendsto (fun i => c * d i ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hD
    · exact Eventually.of_forall fun i => mul_nonneg hc.le (sq_nonneg _)
    · filter_upwards [hEventually] with i hi
      exact hi (μ i)
  have hScale : Tendsto (fun i => c * d i ^ 2 / c) atTop (𝓝 0) := by
    simpa only [zero_div] using hT.div_const c
  have hSquare : Tendsto (fun i => d i ^ 2) atTop (𝓝 0) := by
    refine hScale.congr fun i => ?_
    exact mul_div_cancel_left₀ _ hc.ne'
  have hAbs : Tendsto (fun i => |d i|) atTop (𝓝 0) := by
    have hS := Real.continuous_sqrt.continuousAt.tendsto.comp hSquare
    rw [Real.sqrt_zero] at hS
    exact hS.congr (fun i => Real.sqrt_sq_eq_abs (d i))
  have hD0 : ∀ᶠ i in atTop, 0 ≤ d i := by
    filter_upwards [hn.eventually_gt_atTop ℓ] with i hi
    have h := sketchRank_le_dim_mul_meanProjectedEnergy (μ i)
    rw [meanProjectedEnergy_eq_meanSketchProjector_norm (hℓ.trans hi)] at h
    change (ℓ : ℝ) ≤ (n i : ℝ) * meanProjectorNorm (μ i) at h
    rw [mul_comm] at h
    exact sub_nonneg.mpr ((div_le_iff₀ (Nat.cast_pos.mpr (hℓ.trans hi))).mpr h)
  have hDelta : Tendsto d atTop (𝓝 0) := hAbs.congr' (hD0.mono fun _ hi => abs_of_nonneg hi)
  have hnR : Tendsto (fun i => (n i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hRatio : Tendsto (fun i => (ℓ : ℝ) / (n i : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnR
  have h := hDelta.add hRatio
  rw [add_zero] at h
  exact h.congr (fun i => sub_add_cancel _ _)


/-- Equation (Jconcentrates) before taking limits. -/
theorem spikeDeviation_le_discrepancy {n k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (hn : k + p ≤ n) (μ : Measure (OrthogonalProjector n (k+p))) [IsProbabilityMeasure μ] :
    (∫ x, |spikeConditionalAverage μ x -
      ∫ y, spikeConditionalAverage μ y ∂stdGaussian (Ambient n)| ∂stdGaussian (Ambient n)) ≤
      ((n : ℝ) - k) / ((n : ℝ) + 1) * meanDiscrepancy k μ := by
  have hkn : k < n := by omega
  let F := fun σ : Spectra n k =>
    ∫ U, |conditionalMean k σ.val μ U - gaussianMean k (k+p) σ.val|
      ∂gaussianRightOrthogonalLaw n
  let D := ∫ x, |spikeConditionalAverage μ x -
      ∫ y, spikeConditionalAverage μ y ∂stdGaussian (Ambient n)| ∂stdGaussian (Ambient n)
  have hWitness : F (oneSpikeSpectra hk hkn) ≤ meanDiscrepancy k μ :=
    le_csSup (meanDiscrepancy_bddAbove hk hp hn μ) (Set.mem_range_self _)
  change (∫ U, |conditionalMean k (spikeSpectrum n) μ U - gaussianMean k (k+p) (spikeSpectrum n)|
    ∂gaussianRightOrthogonalLaw n) ≤ meanDiscrepancy k μ at hWitness
  rw [spikeSpectrum_discrepancy_eq hk hkn hn μ] at hWitness
  have hNum : 0 < (n : ℝ) + 1 := by positivity
  have hDen : 0 < (n : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkn)
  change D ≤ ((n : ℝ) - k) / ((n : ℝ) + 1) * meanDiscrepancy k μ
  calc
    _ = (((n : ℝ) - k) / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / ((n : ℝ) - k) * D) := by
      field_simp [hDen.ne', hNum.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hWitness (div_nonneg hDen.le hNum.le)

end TypicalOrientations
