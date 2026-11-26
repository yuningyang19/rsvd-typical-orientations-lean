import SketchOrientation.UnequalSpikes
import SketchOrientation.CosineWindowHaar
import SketchOrientation.GaussianOrientationTheorem

namespace SketchOrientation

open Matrix MeasureTheory Filter Set
open scoped MatrixOrder Topology

variable {m n k l : ℕ}

set_option maxHeartbeats 800000 in
private theorem measurable_rawResidual {X : Type*} [MeasurableSpace X]
    {A : X → Matrix (Fin m) (Fin n) ℝ} {Ω : X → Matrix (Fin n) (Fin l) ℝ}
    (hA : Measurable A) (hΩ : Measurable Ω) :
    Measurable (fun x => squaredResidual (A x) (Ω x)) := by
  let f (R : Matrix (Fin l) (Fin n) ℚ) : Matrix (Fin l) (Fin n) ℝ := R.map Rat.cast
  let obj (x : X) (R : Matrix (Fin l) (Fin n) ℝ) :=
    squaredFrobenius (A x - (A x * Ω x) * R)
  have hDense : DenseRange f :=
    DenseRange.piMap (f := fun _ : Fin l => Pi.map (fun _ : Fin n => Rat.cast))
      (fun _ => DenseRange.piMap (fun _ => Rat.denseRange_cast))
  have hFrob : Continuous (squaredFrobenius : Matrix (Fin m) (Fin n) ℝ → ℝ) := by
    change Continuous (fun Q : Matrix (Fin m) (Fin n) ℝ => squaredFrobenius Q)
    simp only [Cosine.squaredFrobenius_eq_sum_entries]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_id.matrix_elem i j).pow 2
  have hEq (x : X) : squaredResidual (A x) (Ω x) = ⨅ R, obj x (f R) := by
    let t := ⨅ R, obj x (f R)
    have hb : BddBelow (Set.range fun R => obj x (f R)) :=
      ⟨0, by rintro _ ⟨R, rfl⟩; exact squaredFrobenius_nonneg _⟩
    refine le_antisymm (le_ciInf fun R => squaredResidual_le_sampled_approximation _ _ _) ?_
    have hc : Continuous (obj x) := by
      change Continuous (fun R : Matrix (Fin l) (Fin n) ℝ =>
        squaredFrobenius (A x - (A x * Ω x) * R))
      exact hFrob.comp (continuous_const.sub (continuous_const.matrix_mul continuous_id))
    have hLE : ∀ R, t ≤ obj x R := by
      intro R
      refine hDense.induction_on (p := fun R => t ≤ obj x R) R (isClosed_le continuous_const hc) ?_
      exact fun T => ciInf_le hb T
    let Y := A x * Ω x
    have hG : (Yᵀ * Y).IsHermitian := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_self Y
    let R := symmetricPseudoInverse (Yᵀ * Y) hG * Yᵀ * A x
    have hOpt : Y * R = rangeProjector Y * A x := by
      rw [rangeProjector_eq_gram_pseudoInverse]
      simp only [R, Matrix.mul_assoc]
    have hVal : obj x R = squaredResidual (A x) (Ω x) := by
      change squaredFrobenius (A x - Y * R) = squaredFrobenius ((1 - rangeProjector Y) * A x)
      rw [hOpt, Matrix.sub_mul, Matrix.one_mul]
    exact (hLE R).trans_eq hVal
  simp_rw [hEq]
  have : Countable (Matrix (Fin l) (Fin n) ℚ) :=
    inferInstanceAs (Countable (Fin l → Fin n → ℚ))
  apply Measurable.iInf
  intro R
  apply hFrob.measurable.comp
  have hMul : Measurable (fun x => (A x * Ω x) * f R) :=
    measurable_matrix_product (measurable_matrix_product hA hΩ) measurable_const
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact (((continuous_id.matrix_elem i j).measurable.comp hA).sub
    ((continuous_id.matrix_elem i j).measurable.comp hMul))

private theorem integrable_flatTail_loss (ν : Measure (OrthogonalProjector n l))
    [IsProbabilityMeasure ν] (A : Matrix (Fin m) (Fin n) ℝ)
    (hTail : optimalTail k A = (n : ℝ) - k) :
    Integrable (fun P : OrthogonalProjector n l => centeredRankLoss k A P.val) ν := by
  have hm := measurable_rawResidual (A := fun _ : OrthogonalProjector n l => A)
    (Ω := Subtype.val) measurable_const measurable_subtype_coe
  have hI : Integrable (fun P : OrthogonalProjector n l => squaredResidual A P.val) ν := by
    refine Integrable.of_bound hm.aestronglyMeasurable (squaredFrobenius A) ?_
    exact Eventually.of_forall fun P => by
      have hn : 0 ≤ squaredResidual A P.val := squaredFrobenius_nonneg _
      rw [Real.norm_of_nonneg hn]
      have h := squaredResidual_le_sampled_approximation A P.val (0 : Matrix (Fin n) (Fin n) ℝ)
      simpa only [Matrix.mul_zero, sub_zero] using h
  simpa only [centeredRankLoss, tailRelativeError, hTail, Pi.sub_apply] using
    (((hI.div_const ((n : ℝ) - k)).sub (integrable_const (1 : ℝ))).div_const (k : ℝ))

/-- The conditional mean with a flat unit tail and unequal leading spikes,
under a projector law independent of the Haar target. -/
noncomputable def unequalHaarConditionalMean (ν : Measure (OrthogonalProjector n l))
    (A : Matrix (Fin n) (Fin k) ℝ → Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ∫ P, centeredRankLoss k (A V) P.val ∂ν

/-- A single lower gap bounds the deviation of the conditional mean for
every finite upper gap. The right side is precisely the supremum from
(3.7) over equal-spike gaps including the endpoint. -/
theorem unequalSpikes_haarDeviation_le {p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (hl : k + p ≤ n) (ν : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure ν]
    {Γ₀ : ℝ} (hΓ₀ : 1 < Γ₀)
    (A : Matrix (Fin n) (Fin k) ℝ → Matrix (Fin m) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin k) ℝ → Matrix (Fin k) (Fin k) ℝ)
    (hGram : ∀ᵐ V ∂gaussianHaarFrameLaw (show k ≤ n by omega),
      (H V).PosSemidef ∧ (A V)ᵀ * A V = 1 + V * H V * Vᵀ ∧
      (Γ₀ - 1) • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ H V ∧
      ∃ Γ : ℝ, Γ₀ ≤ Γ ∧ H V ≤ (Γ - 1) • (1 : Matrix (Fin k) (Fin k) ℝ)) :
    ∀ᵐ V ∂gaussianHaarFrameLaw (show k ≤ n by omega),
      |unequalHaarConditionalMean ν A V - haarOrientationBenchmark n k (k + p)| ≤
        haarOrientationUniformDeviation ν Γ₀ V := by
  have hkn : k < n := by omega
  have hkp : k + 1 < k + p := by omega
  let r : ℝ := 5 / 4
  have hr : 1 < r := by norm_num [r]
  have hr₂ : r ≤ 2 := by norm_num [r]
  have hdr : r < ((k + p - k + 1 : ℕ) : ℝ) / 2 := by
    rw [Nat.add_sub_cancel_left, Nat.cast_add]
    dsimp [r]
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  filter_upwards [ae_gaussianHaarFrame_orthonormal hkn.le, hGram,
    ae_haarOrientationGap_bound hl hkp hk ν hr hr₂ hdr,
    ae_haarOrientationUniformDeviation_eq_max hl hkp hk ν hΓ₀ hr hr₂ hdr] with V hV hG hGap hMax
  obtain ⟨hH, hGram', hLow, Γ, hΓ, hHigh⟩ := hG
  have hΓ' : 1 < Γ := hΓ₀.trans_le hΓ
  have hPoint (P : OrthogonalProjector n (k + p)) := unequalSpikes_centeredRankLoss_bounds
    (A V) V hV (H V) hH hGram' hΓ₀.le hΓ'.le hLow hHigh
    (by simpa only [Fintype.card_fin] using hkn) P.val
  have hA := integrable_flatTail_loss ν (A V) (by
    simpa only [Fintype.card_fin] using flatTail_optimalTail (A V) V hV (H V) hH hGram')
  have hEnd (g : ℝ) (hg : 1 ≤ g) :
      Integrable (fun P : OrthogonalProjector n (k + p) => projectorTwoLevelLoss V P g) ν := by
    have hgGram := twoLevelInput_gram V hV (zero_le_one.trans hg)
    have ht := twoLevel_optimalTail _ _ hV hg hgGram
    exact integrable_flatTail_loss ν _ (by simpa only [Fintype.card_fin] using ht)
  have hLo : haarOrientationFiniteMean ν Γ₀ V ≤ unequalHaarConditionalMean ν A V :=
    integral_mono (hEnd _ hΓ₀.le) hA (fun P => by
      simpa only [Fintype.card_fin, projectorTwoLevelLoss] using (hPoint P).1)
  have hHi : unequalHaarConditionalMean ν A V ≤ haarOrientationFiniteMean ν Γ V :=
    integral_mono hA (hEnd _ hΓ'.le) (fun P => by
      simpa only [Fintype.card_fin, projectorTwoLevelLoss] using (hPoint P).2)
  rw [hMax]
  exact abs_le_max_abs_abs (sub_le_sub_right hLo _)
    (sub_le_sub_right (hHi.trans (sub_nonneg.mp (hGap Γ hΓ').1)) _)

/-- The same dimension-dependent uniform rate controls the true L¹ error
for unequal spikes. The upper gap may vary with the Haar frame. -/
theorem unequalSpikes_haarDeviation_L1 {p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (hl : k + p ≤ n) (ν : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure ν]
    {Γ₀ r : ℝ} (hΓ₀ : 1 < Γ₀) (hr : 1 < r) (hr₂ : r ≤ 2) (hr' : 2 * r < (p : ℝ) + 1)
    (A : Matrix (Fin n) (Fin k) ℝ → Matrix (Fin m) (Fin n) ℝ) (hA : Measurable A)
    (H : Matrix (Fin n) (Fin k) ℝ → Matrix (Fin k) (Fin k) ℝ)
    (hGram : ∀ᵐ V ∂gaussianHaarFrameLaw (show k ≤ n by omega),
      (H V).PosSemidef ∧ (A V)ᵀ * A V = 1 + V * H V * Vᵀ ∧
      (Γ₀ - 1) • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ H V ∧
      ∃ Γ : ℝ, Γ₀ ≤ Γ ∧ H V ≤ (Γ - 1) • (1 : Matrix (Fin k) (Fin k) ℝ)) :
    let η := gaussianHaarFrameLaw (show k ≤ n by omega)
    let d := fun V => |unequalHaarConditionalMean ν A V - haarOrientationBenchmark n k (k + p)|
    Integrable d η ∧ (∫ V, d V ∂η) ≤ orientationRateConstant p r *
      (‖(meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap‖ ^ (1 - 1 / r) +
        ((n : ℝ) * k / (Γ₀ - 1)) ^ (r - 1)) := by
  intro η d
  let h := haarOrientationBenchmark n k (k + p)
  let X := Matrix (Fin n) (Fin k) ℝ
  let Y := OrthogonalProjector n (k + p)
  let f (V : X) := haarOrientationFiniteMean ν Γ₀ V
  let e (V : X) := haarOrientationEndpoint ν V
  have hkn : k < n := by omega
  have hkp : k + 1 < k + p := by omega
  have hdr : r < ((k + p - k + 1 : ℕ) : ℝ) / 2 := by
    rw [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_one]
    linarith
  have hI : Integrable (haarOrientationUniformDeviation ν Γ₀) η := by
    have hf := integrable_haarOrientationFiniteMean hk hkn ν hΓ₀.le
    have he := (haarOrientationEndpoint_mean hl hk hkp ν).1
    exact (((hf.sub (integrable_const h)).abs).sup (he.sub (integrable_const h)).abs).congr
      (ae_haarOrientationUniformDeviation_eq_max hl hkp hk ν hΓ₀ hr hr₂ hdr).symm
  let G (z : X × Y) := ((squaredResidual (A z.1) z.2.val / ((n : ℝ) - k)) - 1) / (k : ℝ)
  have hG : Measurable G := by
    have hM := measurable_rawResidual (A := fun z : X × Y => A z.1) (Ω := fun z => z.2.val)
      (hA.comp measurable_fst) (measurable_subtype_coe.comp measurable_snd)
    exact ((hM.div_const ((n : ℝ) - k)).sub_const 1).div_const _
  have hF : (fun V : X => ∫ P, G (V, P) ∂ν) =ᵐ[η] unequalHaarConditionalMean ν A := by
    filter_upwards [hGram, ae_gaussianHaarFrame_orthonormal hkn.le] with V hS hV
    have ht : optimalTail k (A V) = (n : ℝ) - k := by
      simpa only [Fintype.card_fin] using flatTail_optimalTail (A V) V hV (H V) hS.1 hS.2.1
    simp only [G, unequalHaarConditionalMean, centeredRankLoss, tailRelativeError, ht]
  have hM : AEStronglyMeasurable d η := by
    have hm := hG.stronglyMeasurable.integral_prod_right' (ν := ν)
    exact ((hm.measurable.sub_const h).abs.aestronglyMeasurable).congr
      (hF.fun_comp fun y => |y - h|)
  have hb := unequalSpikes_haarDeviation_le hk hp hl ν hΓ₀ A H hGram
  have hInt : Integrable d η := hI.mono' hM (hb.mono fun V hV => by
    change ‖|unequalHaarConditionalMean ν A V - h|‖ ≤ _
    simpa only [Real.norm_of_nonneg (abs_nonneg _)] using hV)
  exact ⟨hInt, (integral_mono_ae hInt hI hb).trans
    (theorem_1_1_uniform_rate hk hp hl ν hΓ₀ hr hr₂ hr')⟩

/-- Unequal spikes have the same high-gap limit for independent Haar
targets under diffuseness and a diverging scaled lower gap. -/
theorem unequalSpikes_haar_tendsto {m n k : ℕ → ℕ} {p : ℕ} (hp : 2 ≤ p)
    (hk : ∀ i, 0 < k i) (hl : ∀ i, k i + p ≤ n i) (hn : Tendsto n atTop atTop)
    (ν : ∀ i, Measure (OrthogonalProjector (n i) (k i + p))) [∀ i, IsProbabilityMeasure (ν i)]
    (Γ₀ : ℕ → ℝ)
    (hGap : Tendsto (fun i => Γ₀ i / ((n i : ℝ) * k i)) atTop atTop)
    (hρ : Tendsto (fun i => ‖(meanSketchProjector (ν i)).toEuclideanLin.toContinuousLinearMap‖)
      atTop (𝓝 0))
    (A : ∀ i, Matrix (Fin (n i)) (Fin (k i)) ℝ → Matrix (Fin (m i)) (Fin (n i)) ℝ)
    (hA : ∀ i, Measurable (A i))
    (H : ∀ i, Matrix (Fin (n i)) (Fin (k i)) ℝ → Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (hGram : ∀ i, ∀ᵐ V ∂gaussianHaarFrameLaw ((Nat.le_add_right _ _).trans (hl i)),
      (H i V).PosSemidef ∧ (A i V)ᵀ * A i V = 1 + V * H i V * Vᵀ ∧
      (Γ₀ i - 1) • (1 : Matrix (Fin (k i)) (Fin (k i)) ℝ) ≤ H i V ∧
      ∃ Γ : ℝ, Γ₀ i ≤ Γ ∧ H i V ≤ (Γ - 1) • (1 : Matrix (Fin (k i)) (Fin (k i)) ℝ)) :
    Tendsto (fun i => ∫ V, |unequalHaarConditionalMean (ν i) (A i) V - 1 / ((p : ℝ) - 1)|
      ∂gaussianHaarFrameLaw ((Nat.le_add_right _ _).trans (hl i))) atTop (𝓝 0) := by
  let r : ℝ := 5 / 4
  let ρ (i : ℕ) := ‖(meanSketchProjector (ν i)).toEuclideanLin.toContinuousLinearMap‖
  let d (i : ℕ) := haarOrientationBenchmark (n i) (k i) (k i + p)
  let L (i : ℕ) := ((n i : ℝ) * k i)
  let q : ℝ := 1 / ((p : ℝ) - 1)
  have hL (i : ℕ) : 1 ≤ L i := by
    have hni : (1 : ℝ) ≤ n i := by exact_mod_cast (show 1 ≤ n i from (hk i).trans_le
      ((Nat.le_add_right _ _).trans (hl i)))
    have hki : (1 : ℝ) ≤ k i := by exact_mod_cast hk i
    exact one_le_mul_of_one_le_of_one_le hni hki
  have hFeasible : ∀ᶠ i in atTop, 1 < Γ₀ i := by
    filter_upwards [hGap.eventually_gt_atTop 1] with i hi
    exact (hL i).trans_lt (by simpa only [one_mul] using (lt_div_iff₀
      (zero_lt_one.trans_le (hL i))).mp hi)
  have hGap' : Tendsto (fun i => (Γ₀ i - 1) / L i) atTop atTop := by
    apply tendsto_atTop_mono (f := fun i => Γ₀ i / L i + (-1)) _
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) hGap)
    intro i
    rw [sub_div]
    have hi := inv_le_one_of_one_le₀ (hL i)
    rw [← one_div] at hi
    linarith
  have hInv : Tendsto (fun i => L i / (Γ₀ i - 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp hGap'
  have hr : 1 < r := by norm_num [r]
  have hr₂ : r ≤ 2 := by norm_num [r]
  have hr' : 2 * r < (p : ℝ) + 1 := by
    have h : (2 : ℝ) ≤ p := by exact_mod_cast hp
    dsimp [r]
    linarith
  have hExp : 0 < 1 - 1 / r := sub_pos.mpr ((div_lt_one (zero_lt_one.trans hr)).2 hr)
  have hRad : 0 < r - 1 := sub_pos.mpr hr
  have hPower₁ := (Real.continuous_rpow_const hExp.le).continuousAt (x := 0) |>.tendsto.comp hρ
  have hPower₂ := (Real.continuous_rpow_const hRad.le).continuousAt (x := 0) |>.tendsto.comp hInv
  simp only [Function.comp_def, Real.zero_rpow hExp.ne', Real.zero_rpow hRad.ne'] at hPower₁ hPower₂
  have hRate : Tendsto (fun i => orientationRateConstant p r *
      (ρ i ^ (1 - 1 / r) + (L i / (Γ₀ i - 1)) ^ (r - 1))) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hPower₁.add hPower₂).const_mul (orientationRateConstant p r)
  have hReal : Tendsto (fun i => (n i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hDen : Tendsto (fun i => (n i : ℝ) - k i) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hReal.const_mul_atTop (show 0 < (1 / 2 : ℝ) by norm_num))
    filter_upwards [hρ.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)] with i hi
    have hni : 0 < n i := (hk i).trans_le ((Nat.le_add_right _ _).trans (hl i))
    have hTrace := sketchRank_le_dim_mul_meanProjectedEnergy (ν i)
    rw [meanProjectedEnergy_eq_meanSketchProjector_norm hni] at hTrace
    change (↑(k i + p) : ℝ) ≤ (n i : ℝ) * ρ i at hTrace
    have hBound := mul_le_mul_of_nonneg_left hi.le (Nat.cast_nonneg (α := ℝ) (n i))
    push_cast at hTrace
    change (1 / 2 : ℝ) * n i ≤ n i - k i
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have hBench := Cosine.haarOrientationBenchmark_tendsto_window hk hp hl hDen
  have hErr : Tendsto (fun i => |d i - q|) atTop (𝓝 0) := by
    have ht := (tendsto_iff_dist_tendsto_zero.mp hBench)
    simpa only [Real.dist_eq] using ht
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _) ?_
    (by simpa only [add_zero] using hRate.add hErr)
  filter_upwards [hFeasible] with i hi
  obtain ⟨hI, hB⟩ := unequalSpikes_haarDeviation_L1 (hk i) hp (hl i) (ν i) hi hr hr₂ hr'
    (A i) (hA i) (H i) (hGram i)
  have hC : Integrable (fun _ : Matrix (Fin (n i)) (Fin (k i)) ℝ => |d i - q|)
      (gaussianHaarFrameLaw ((Nat.le_add_right _ _).trans (hl i))) := integrable_const _
  have hOne : (∫ _ : Matrix (Fin (n i)) (Fin (k i)) ℝ, |d i - q|
      ∂gaussianHaarFrameLaw ((Nat.le_add_right _ _).trans (hl i))) = |d i - q| := by simp
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    (hI.add hC) (Eventually.of_forall fun V => abs_sub_le (unequalHaarConditionalMean (ν i) (A i) V)
      (d i) q)).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add hI hC, hOne]
  exact add_le_add hB le_rfl

end SketchOrientation
