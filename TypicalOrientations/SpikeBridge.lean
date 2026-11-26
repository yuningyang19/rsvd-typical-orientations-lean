import TypicalOrientations.RotationModel
import TypicalOrientations.SpikeCovariance
import TypicalOrientations.SpikeResidual
import SketchOrientation.GaussianHaarDirectionBeta

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation
open scoped InnerProductSpace

private abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)

private noncomputable def vectorColumn {n : ℕ} (x : Ambient n) : Matrix (Fin n) (Fin 1) ℝ :=
  Matrix.of (fun i _ => x i)

private theorem vectorColumn_orthonormal {n : ℕ} (x : Ambient n) (hx : ‖x‖ = 1) :
    (vectorColumn x)ᵀ * vectorColumn x = 1 := by
  ext i j
  have he : i = j := Subsingleton.elim _ _
  subst j
  rw [Matrix.one_apply_eq]
  change (∑ a, x a * x a) = 1
  have hn := PiLp.norm_sq_eq_of_L2 _ x
  rw [hx, one_pow] at hn
  simpa [pow_two, Real.norm_eq_abs, abs_mul_abs_self] using hn.symm

private theorem mul_vectorColumn {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x : Ambient n) :
    Q * vectorColumn x = vectorColumn (Q.toEuclideanLin x) := by
  ext i j
  rfl

private theorem spikeProjectionEnergy_column {n ℓ : ℕ} (v : Ambient n) (P : OrthogonalProjector n ℓ) :
    spikeProjectionEnergy (vectorColumn v) P.val = ‖P.val.toEuclideanLin v‖ ^ 2 := by
  have h := (orientationRowSpace P).re_inner_starProjection_eq_normSq v
  change inner ℝ ((orientationRowSpace P).starProjection v) v =
    ‖(orientationRowSpace P).starProjection v‖ ^ 2 at h
  rw [orientationRowSpace_starProjection] at h
  rw [← h, EuclideanSpace.inner_eq_star_dotProduct, spikeProjectionEnergy,
    Matrix.mul_assoc, mul_vectorColumn]
  change (∑ i, v i * (P.val.toEuclideanLin v) i) =
    (∑ i, v i * star ((P.val.toEuclideanLin v) i))
  simp

/-- One squared singular value n+1, with every remaining squared value equal to one. -/
noncomputable def spikeSpectrum (n : ℕ) (i : Fin n) : ℝ :=
  if i.val = 0 then Real.sqrt ((n : ℝ) + 1) else 1

theorem spikeSpectrum_optimalSquaredTail {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    optimalSquaredTail k (spikeSpectrum n) = (n : ℝ) - k := by
  unfold optimalSquaredTail
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) ?_, Finset.sum_const, nsmul_eq_mul, mul_one]
  · have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => i.val < k)
    have hsmall := Fin.card_filter_val_lt (n := n) (m := k)
    simp only [Nat.not_lt, Fintype.card_fin, Finset.card_univ, hsmall, min_eq_right hkn] at hcard
    have h := show (Finset.univ.filter (fun i : Fin n => k ≤ i.val)).card = n - k by omega
    rw [h, Nat.cast_sub hkn]
  · intro i hi
    have hk' := (Finset.mem_filter.mp hi).2
    have hi0 : i.val ≠ 0 := by omega
    simp [spikeSpectrum, hi0]

noncomputable def oneSpikeSpectra {n k : ℕ} (hk : 0 < k) (hkn : k < n) : Spectra n k := by
  refine ⟨spikeSpectrum n, ?_, ?_, ?_⟩
  · intro i j hij
    have hij' : i.val ≤ j.val := hij
    by_cases hj : j.val = 0
    · have hi : i.val = 0 := by omega
      simp [spikeSpectrum, hi, hj]
    · by_cases hi : i.val = 0
      · simp only [spikeSpectrum, hi, hj, if_true, if_false]
        exact (Real.le_sqrt zero_le_one (by positivity)).mpr (by norm_num)
      · simp [spikeSpectrum, hi, hj]
  · intro i
    unfold spikeSpectrum
    split
    · exact Real.sqrt_nonneg _
    · exact zero_le_one
  · rw [spikeSpectrum_optimalSquaredTail hk hkn.le]
    exact sub_pos.mpr (by exact_mod_cast hkn)

private theorem diagonal_spikeSpectrum_gram {n : ℕ} (hn : 0 < n) :
    (diagonal (spikeSpectrum n))ᵀ * diagonal (spikeSpectrum n) =
      1 + (n : ℝ) • (vectorColumn (EuclideanSpace.single ⟨0, hn⟩ 1) *
        (vectorColumn (EuclideanSpace.single ⟨0, hn⟩ 1))ᵀ) := by
  let z : Fin n := ⟨0, hn⟩
  let e : Ambient n := EuclideanSpace.single z 1
  have he (i : Fin n) : e i = if i.val = 0 then 1 else 0 := by
    by_cases hi : i.val = 0
    · have hiz : i = z := Fin.ext hi
      subst i
      simp [e, z, EuclideanSpace.single]
    · have hiz : i ≠ z := fun h => hi (congrArg Fin.val h)
      simp [e, EuclideanSpace.single, hi, hiz]
  rw [diagonal_transpose, diagonal_mul_diagonal]
  ext i j
  have hab (i' j' : Fin n) : (vectorColumn e * (vectorColumn e)ᵀ) i' j' = e i' * e j' := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, vectorColumn, Matrix.of_apply,
      Fintype.sum_unique]
  change diagonal (fun a => spikeSpectrum n a * spikeSpectrum n a) i j =
    (1 : Matrix (Fin n) (Fin n) ℝ) i j + (n : ℝ) * (vectorColumn e * (vectorColumn e)ᵀ) i j
  rw [hab, he i, he j]
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val = 0
    · simp [spikeSpectrum, hi, ← pow_two, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1), add_comm]
    · simp [spikeSpectrum, hi]
  · have hDiff : i.val ≠ 0 ∨ j.val ≠ 0 := by
      by_contra! h
      exact hij (Fin.ext (h.1.trans h.2.symm))
    rcases hDiff with hi | hj
    · simp [hij, hi]
    · simp [hij, hj]

private theorem gaussianHead_norm {n : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
    ‖Uᵀ.toEuclideanLin (EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ))‖ = 1 := by
  rw [← orthogonalMatrixIsometry_apply Uᵀ (by rw [transpose_transpose]; exact mul_eq_one_comm.mp hU),
    LinearIsometryEquiv.norm_map]
  simp [EuclideanSpace.single, PiLp.norm_single]

private theorem spikeSpectrum_originalGram {n : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
    (diagonal (spikeSpectrum n) * U)ᵀ * (diagonal (spikeSpectrum n) * U) =
      1 + (n : ℝ) • (vectorColumn (Uᵀ.toEuclideanLin (EuclideanSpace.single ⟨0, hn⟩ 1)) *
        (vectorColumn (Uᵀ.toEuclideanLin (EuclideanSpace.single ⟨0, hn⟩ 1)))ᵀ) := by
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal (spikeSpectrum n))ᵀ,
    diagonal_spikeSpectrum_gram hn]
  simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add, hU,
    Matrix.mul_smul, ← mul_vectorColumn, transpose_mul, transpose_transpose, Matrix.mul_assoc]


private theorem spikeConditionalAverage_normalize {n ℓ : ℕ}
    (μ : Measure (OrthogonalProjector n ℓ)) (x : Ambient n) :
    spikeConditionalAverage μ (sphereNormalize x) = spikeConditionalAverage μ x := by
  have hN : sphereNormalize (sphereNormalize x) = sphereNormalize x := by
    by_cases h : x = 0
    · simp [h, sphereNormalize]
    · have hx := sphereNormalize_norm h
      nth_rw 1 [sphereNormalize]
      rw [hx, inv_one, one_smul]
  simp only [spikeConditionalAverage, spikeSketchReciprocal, hN]

/-- The exact one-spike loss at a specified orientation and projector. -/
theorem spikeSpectrum_rotatedLoss_eq {n k ℓ : ℕ} (hk : 0 < k) (hkn : k < n)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1)
    (P : OrthogonalProjector n ℓ) :
    squaredResidual (diagonal (spikeSpectrum n)) (U * P.val) /
        optimalSquaredTail k (spikeSpectrum n) =
      (((n : ℝ) - ℓ - 1) / ((n : ℝ) - k)) +
      (((n : ℝ) + 1) / ((n : ℝ) - k)) * spikeSketchReciprocal P
        (Uᵀ.toEuclideanLin (EuclideanSpace.single ⟨0, hk.trans hkn⟩ 1)) := by
  let v := Uᵀ.toEuclideanLin (EuclideanSpace.single ⟨0, hk.trans hkn⟩ (1 : ℝ))
  let c := ((n : ℝ) - ℓ - 1) / ((n : ℝ) - k)
  let a := ((n : ℝ) + 1) / ((n : ℝ) - k)
  have hUnit : ‖v‖ = 1 := gaussianHead_norm (hk.trans hkn) U hU
  let A := diagonal (spikeSpectrum n) * U
  let V := vectorColumn v
  have hV : Vᵀ * V = 1 := vectorColumn_orthonormal _ hUnit
  have hGram : Aᵀ * A = 1 + (n : ℝ) • (V * Vᵀ) := spikeSpectrum_originalGram (hk.trans hkn) U hU
  change _ = c + a * spikeSketchReciprocal P v
  rw [← residual_rotate_input k _ U hU P, spikeSpectrum_optimalSquaredTail hk hkn.le,
    ← spike_optimalTail hk hkn.le A V hV hGram]
  change tailRelativeError k A P.val = _
  rw [spike_tailRelativeError hk hkn A V hV P hGram,
    show spikeProjectionEnergy V P.val = ‖P.val.toEuclideanLin v‖ ^ 2 from
      spikeProjectionEnergy_column _ _, spikeSketchReciprocal, spikeReciprocal,
    show sphereNormalize v = v from by simp [sphereNormalize, hUnit]]

/-- The exact one-spike loss averaged over sketch projectors at a fixed orientation. -/
theorem spikeSpectrum_conditionalMean_eq {n k ℓ : ℕ} (hk : 0 < k) (hkn : k < n)
    (μ : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure μ]
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
    conditionalMean k (spikeSpectrum n) μ U =
      (((n : ℝ) - ℓ - 1) / ((n : ℝ) - k)) +
        (((n : ℝ) + 1) / ((n : ℝ) - k)) * spikeConditionalAverage μ
          (Uᵀ.toEuclideanLin (EuclideanSpace.single ⟨0, hk.trans hkn⟩ 1)) := by
  let v := Uᵀ.toEuclideanLin (EuclideanSpace.single ⟨0, hk.trans hkn⟩ (1 : ℝ))
  let c := ((n : ℝ) - ℓ - 1) / ((n : ℝ) - k)
  let a := ((n : ℝ) + 1) / ((n : ℝ) - k)
  have hA : 0 < a := div_pos (by positivity) (sub_pos.mpr (by exact_mod_cast hkn))
  have hLoss (P : OrthogonalProjector n ℓ) :
      squaredResidual (diagonal (spikeSpectrum n)) (U * P.val) /
          optimalSquaredTail k (spikeSpectrum n) = c + a * spikeSketchReciprocal P v :=
    spikeSpectrum_rotatedLoss_eq hk hkn U hU P
  change conditionalMean k (spikeSpectrum n) μ U = c + a * spikeConditionalAverage μ v
  let r := fun P : OrthogonalProjector n ℓ => spikeSketchReciprocal P v
  let L := fun P : OrthogonalProjector n ℓ =>
    squaredResidual (diagonal (spikeSpectrum n)) (U * P.val) / optimalSquaredTail k (spikeSpectrum n)
  have hUMeas : Measurable (fun P : OrthogonalProjector n ℓ => U * P.val) :=
    (continuous_const.matrix_mul continuous_id).measurable.comp measurable_subtype_coe
  have hLMeas : Measurable L :=
    (measurable_rawResidual measurable_const hUMeas).div_const _
  have hrEq : r = fun P => (L P - c) / a := by
    funext P
    rw [show L P = c + a * r P from hLoss P, add_sub_cancel_left, mul_comm a, mul_div_cancel_right₀ _ hA.ne']
  have hr : Measurable r := hrEq ▸ (hLMeas.sub_const c).div_const a
  have hrI : Integrable r μ := by
    refine Integrable.of_bound hr.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun P => ?_)
    have ht : 0 ≤ ‖P.val.toEuclideanLin (sphereNormalize v)‖ ^ 2 := sq_nonneg _
    have hp : 1 ≤ 1 + (n : ℝ) * ‖P.val.toEuclideanLin (sphereNormalize v)‖ ^ 2 :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) ht)
    change ‖(1 + (n : ℝ) * ‖P.val.toEuclideanLin (sphereNormalize v)‖ ^ 2)⁻¹‖ ≤ 1
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hp))]
    exact inv_le_one_of_one_le₀ hp
  unfold conditionalMean
  simp_rw [hLoss]
  rw [integral_add (integrable_const c) (hrI.const_mul a), integral_const,
    probReal_univ, one_smul, integral_const_mul]
  rfl

set_option maxHeartbeats 1200000 in
/-- The fixed-spectrum discrepancy equals the spherical reciprocal
deviation times the precise normalization in equation (spike-loss). -/
theorem spikeSpectrum_discrepancy_eq {n k ℓ : ℕ} (hk : 0 < k) (hkn : k < n) (hℓn : ℓ ≤ n)
    (μ : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure μ] :
    (∫ U, |conditionalMean k (spikeSpectrum n) μ U - gaussianMean k ℓ (spikeSpectrum n)|
      ∂gaussianRightOrthogonalLaw n) =
      ((n : ℝ) + 1) / ((n : ℝ) - k) *
        ∫ x, |spikeConditionalAverage μ x -
          ∫ y, spikeConditionalAverage μ y ∂stdGaussian (Ambient n)| ∂stdGaussian (Ambient n) := by
  let hn := hk.trans hkn
  let e : Ambient n := EuclideanSpace.single ⟨0, hn⟩ 1
  let γ := stdGaussian (Ambient n)
  let η := gaussianRightOrthogonalLaw n
  let v (U : Matrix (Fin n) (Fin n) ℝ) := Uᵀ.toEuclideanLin e
  let c := ((n : ℝ) - ℓ - 1) / ((n : ℝ) - k)
  let a := ((n : ℝ) + 1) / ((n : ℝ) - k)
  let J := spikeConditionalAverage μ
  let m := ∫ y, J y ∂γ
  have hA : 0 < a := div_pos (by positivity) (sub_pos.mpr (by exact_mod_cast hkn))
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.single, PiLp.norm_single]
  have hv : Measurable v := by
    have h : Continuous v := by
      change Continuous (fun U : Matrix (Fin n) (Fin n) ℝ =>
        WithLp.toLp 2 (Uᵀ *ᵥ WithLp.ofLp e))
      exact (PiLp.continuous_toLp 2 _).comp
        (continuous_id.matrix_transpose.matrix_mulVec continuous_const)
    exact h.measurable
  have hVLaw : η.map v = γ.map sphereNormalize := gaussianRightOrthogonalLaw_map_transpose_direction e he
  have hJ : Measurable J := measurable_spikeConditionalAverage μ
  have hRewrite (f : ℝ → ℝ) (hf : Measurable f) :
      (∫ U, f (J (v U)) ∂η) = ∫ x, f (J x) ∂γ := by
    have h := hf.comp hJ
    change (∫ U, (f ∘ J) (v U) ∂η) = ∫ x, f (J x) ∂γ
    rw [← integral_map hv.aemeasurable h.aestronglyMeasurable, hVLaw,
      integral_map measurable_sphereNormalize.aemeasurable h.aestronglyMeasurable]
    simp only [Function.comp_apply, J, spikeConditionalAverage_normalize]
  have hPoint U (hU : Uᵀ * U = 1) :
      conditionalMean k (spikeSpectrum n) μ U = c + a * J (v U) := by
    exact spikeSpectrum_conditionalMean_eq hk hkn μ U hU
  have hEq : (fun U => conditionalMean k (spikeSpectrum n) μ U) =ᵐ[η] fun U => c + a * J (v U) := by
    filter_upwards [ae_gaussianRightOrthogonal n] with U hU
    exact hPoint U hU
  have hJInt : Integrable (fun U => J (v U)) η := by
    refine Integrable.of_bound (hJ.comp hv).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun U => ?_)
    have h := spikeConditionalAverage_mem_Icc μ (v U)
    change ‖spikeConditionalAverage μ (v U)‖ ≤ 1
    rw [Real.norm_of_nonneg h.1]
    exact h.2
  have hCenter : gaussianMean k ℓ (spikeSpectrum n) = c + a * m := by
    have htail : 0 < optimalSquaredTail k (spikeSpectrum n) := (oneSpikeSpectra hk hkn).property.2.2
    rw [← conditionalMean_integral_eq_gaussianMean hℓn k _ htail μ,
      integral_congr_ae hEq, integral_add (integrable_const c) (hJInt.const_mul a),
      integral_const, probReal_univ, one_smul, integral_const_mul]
    exact congrArg (fun x => c + a * x) (hRewrite id measurable_id)
  rw [hCenter]
  have hAbs : (fun U => |conditionalMean k (spikeSpectrum n) μ U - (c + a * m)|) =ᵐ[η]
      fun U => a * |J (v U) - m| := by
    filter_upwards [hEq] with U hU
    rw [hU, show c + a * J (v U) - (c + a * m) = a * (J (v U) - m) by ring,
      abs_mul, abs_of_nonneg hA.le]
  rw [integral_congr_ae hAbs, integral_const_mul]
  exact congrArg (fun x => a * x) (hRewrite (fun t => |t - m|) ((measurable_id.sub_const m).abs))

end TypicalOrientations
