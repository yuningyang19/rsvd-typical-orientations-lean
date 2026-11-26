import TypicalOrientations.GaussianMomentReindex
import TypicalOrientations.RotationModel
import SketchOrientation.GaussianChiSquareMeans
import SketchOrientation.GaussianGramPairMoments

namespace TypicalOrientations

open Matrix SketchOrientation MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {n k p m : ℕ}

theorem optimalSquaredTail_eq_sum_tail (hkn : k ≤ n) (σ : Fin n → ℝ) :
    optimalSquaredTail k σ = ∑ i, σ (leadingTailEquiv hkn (Sum.inr i)) ^ 2 := by
  rw [optimalSquaredTail, Finset.sum_filter]
  let f := fun i : Fin n => if k ≤ i.val then σ i ^ 2 else 0
  change (∑ i, f i) = _
  rw [← Fintype.sum_equiv (leadingTailEquiv hkn) (f ∘ leadingTailEquiv hkn) f (fun _ => rfl),
    Fintype.sum_sum_type]
  simp [f, leadingTailEquiv_leading_val, leadingTailEquiv_tail_val,
    Nat.not_le_of_lt (Fin.isLt _)]

theorem chiSquareNegativeMoment_eq_expectation {d : ℕ} {r : ℝ}
    (hr : 0 < r) (hd : r < (d : ℝ) / 2) :
    Integrable (fun y : ℝ => y ^ (-r)) (chiSquareLaw d) ∧
    (∫ y, y ^ (-r) ∂chiSquareLaw d) = chiSquareNegativeMoment d r := by
  have hnn : 0 ≤ᵐ[chiSquareLaw d] (fun y : ℝ => y ^ (-r)) :=
    (ae_chiSquare_pos d).mono fun _ hy => Real.rpow_nonneg hy.le _
  have hm : AEStronglyMeasurable (fun y : ℝ => y ^ (-r)) (chiSquareLaw d) :=
    (measurable_id.pow_const _).aestronglyMeasurable
  have h := chiSquare_negative_moment hr hd
  change (∫⁻ y, ENNReal.ofReal (y ^ (-r)) ∂chiSquareLaw d) =
    ENNReal.ofReal (chiSquareNegativeMoment d r) at h
  have hγ : 0 < Real.Gamma ((d : ℝ) / 2 - r) := Real.Gamma_pos_of_pos (sub_pos.mpr hd)
  have hγ' : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (hr.trans hd)
  have hC : 0 ≤ chiSquareNegativeMoment d r := by
    unfold chiSquareNegativeMoment
    positivity
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, h]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hm, h, ENNReal.toReal_ofReal hC]

theorem gaussianTailMomentConstant_eq_integrals {r : ℝ} (hr : 0 < r)
    (hp : 2 * r < (p : ℝ) + 1) :
    gaussianTailMomentConstant k p r =
      1 + (k : ℝ) *
        ((∫ z, |z| ^ (2 * r) ∂gaussianReal 0 1) *
         (∫ y, y ^ (-r) ∂chiSquareLaw (p + 1))) ^ (1 / r) := by
  have hlim : r < ((p + 1 : ℕ) : ℝ) / 2 := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  rw [(chiSquareNegativeMoment_eq_expectation hr hlim).2]
  rfl

theorem gaussianTailMomentConstant_pos {r : ℝ} (hr : 0 < r)
    (hp : 2 * r < (p : ℝ) + 1) : 0 < gaussianTailMomentConstant k p r := by
  rw [gaussianTailMomentConstant_eq_integrals hr hp]
  have hZ : 0 ≤ ∫ z, |z| ^ (2 * r) ∂gaussianReal 0 1 := standardNormalMoment_nonneg _
  have hY : 0 ≤ ∫ y, y ^ (-r) ∂chiSquareLaw (p + 1) :=
    integral_nonneg_of_ae ((ae_chiSquare_pos (p+1)).mono fun _ hy => Real.rpow_nonneg hy.le _)
  positivity

private theorem lpNorm_mono_of_ae_norm_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {q : ℝ≥0∞} {f g : X → ℝ} (hf : MemLp f q μ) (hg : MemLp g q μ)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) : lpNorm f q μ ≤ lpNorm g q μ := by
  rw [← toReal_eLpNorm hf.aestronglyMeasurable, ← toReal_eLpNorm hg.aestronglyMeasurable]
  exact ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_ae h)

/-- Minkowski on the convex combination of tail-row energies. All tail rows
share the same random inverse; no independence among transformed rows is needed. -/
theorem gaussianWeightedRows_lpNorm (hk : 0 < k) {r : ℝ} (hr : 1 ≤ r)
    (hp : 2 * r < (p : ℝ) + 1) (b : Fin m → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hs : ∑ i, b i = 1) :
    MemLp (fun w => ∑ i, b i * gaussianTailRowEnergy (k := k) (ℓ := k + p) i w)
      (ENNReal.ofReal r) (gaussianSplitLaw k (k+p) m) ∧
    lpNorm (fun w => ∑ i, b i * gaussianTailRowEnergy (k := k) (ℓ := k + p) i w)
      (ENNReal.ofReal r) (gaussianSplitLaw k (k+p) m) ≤
        (k : ℝ) * (standardNormalMoment r * chiSquareNegativeMoment (p + 1) r) ^ (1 / r) := by
  let ℓ := k + p
  let q := ENNReal.ofReal r
  let μ := gaussianSplitLaw k ℓ m
  let Y := @gaussianTailRowEnergy k ℓ m
  let C := standardNormalMoment r * chiSquareNegativeMoment (p + 1) r
  let M := (k : ℝ) * C ^ (1 / r)
  let t (i : Fin m) := b i • Y i
  have hr' : 0 < r := zero_lt_one.trans_le hr
  have hq : q ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hr'
  have hq' : q ≠ ∞ := ENNReal.ofReal_ne_top
  have hqr : q.toReal = r := ENNReal.toReal_ofReal hr'.le
  have hq1 : 1 ≤ q := by simpa [q] using ENNReal.ofReal_le_ofReal hr
  have hdim : ℓ - k + 1 = p + 1 := by unfold ℓ; omega
  have hkℓ : k ≤ ℓ := by unfold ℓ; omega
  have hlim : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2 := by
    rw [hdim, Nat.cast_add, Nat.cast_one]
    linarith
  have hY (i : Fin m) :
      Integrable (fun w => Y i w ^ r) μ ∧ ∫ w, Y i w ^ r ∂μ ≤ (k : ℝ) ^ r * C := by
    simpa only [Y, μ, C, hdim] using gaussianTailRowEnergy_moment hk hkℓ i hr hlim
  have hM (i : Fin m) : MemLp (Y i) q μ := by
    refine (integrable_norm_rpow_iff
      (measurable_gaussianTailRowEnergy i).aestronglyMeasurable hq hq').1 ?_
    simp_rw [hqr, Real.norm_of_nonneg (gaussianTailRowEnergy_nonneg i _)]
    exact (hY i).1
  have hLp (i : Fin m) : lpNorm (Y i) q μ ≤ M := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hq hq' (hM i).aestronglyMeasurable, hqr]
    simp_rw [show ∀ w, ‖Y i w‖ = Y i w from fun w =>
      Real.norm_of_nonneg (gaussianTailRowEnergy_nonneg i w)]
    have h' := Real.rpow_le_rpow
      (integral_nonneg fun w => Real.rpow_nonneg (gaussianTailRowEnergy_nonneg i w) r)
      (hY i).2 (inv_nonneg.mpr hr'.le)
    refine h'.trans_eq ?_
    have hC : 0 ≤ C := by
      unfold C
      apply mul_nonneg (standardNormalMoment_nonneg r)
      have hlim' : r < ((p + 1 : ℕ) : ℝ) / 2 := hdim ▸ hlim
      rw [← (chiSquareNegativeMoment_eq_expectation hr' hlim').2]
      exact integral_nonneg_of_ae ((ae_chiSquare_pos (p+1)).mono fun _ hx =>
        Real.rpow_nonneg hx.le _)
    unfold M
    rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hC,
      ← Real.rpow_mul (Nat.cast_nonneg k), mul_inv_cancel₀ hr'.ne', Real.rpow_one, one_div]
  have hm (i : Fin m) : MemLp (t i) q μ := (hM i).const_smul (b i)
  have he : (fun w => ∑ i, b i * Y i w) = ∑ i, t i := by
    funext w
    simp only [Finset.sum_apply, t, Pi.smul_apply, smul_eq_mul]
  change MemLp (fun w => ∑ i, b i * Y i w) q μ ∧
    lpNorm (fun w => ∑ i, b i * Y i w) q μ ≤ M
  rw [he]
  refine ⟨?_, (lpNorm_sum_le (fun i _ => hm i) hq1).trans ?_⟩
  · simpa only [← Finset.sum_apply] using (memLp_finsetSum Finset.univ fun i _ => hm i)
  · have hm_pos : 0 < m := by
      by_contra! h
      have hm₀ : m = 0 := by omega
      subst m
      simp at hs
    let i₀ : Fin m := ⟨0, hm_pos⟩
    have hterm (i : Fin m) : lpNorm (t i) q μ = b i * lpNorm (Y i₀) q μ := by
      change lpNorm (b i • Y i) q μ = _
      rw [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg (hb i)]
      rw [← toReal_eLpNorm (hM i).aestronglyMeasurable,
        ← toReal_eLpNorm (hM i₀).aestronglyMeasurable,
        (gaussianTailRowEnergy_identDistrib i i₀).eLpNorm_eq q]
    simp_rw [hterm]
    rw [← Finset.sum_mul, hs, one_mul]
    exact hLp i₀

/-- Lemma 3.2 on the native independent Gaussian matrix law, with the
optimal squared tail appearing inside the moment and in every row weight. -/
theorem gaussian_relative_residual_lpNorm (hk : 0 < k) (hl : k + p ≤ n)
    (σ : Fin n → ℝ) (ht : 0 < optimalSquaredTail k σ)
    {r : ℝ} (hr : 1 < r) (hp : 2 * r < (p : ℝ) + 1) :
    MemLp (fun G => squaredResidual (diagonal σ) G / optimalSquaredTail k σ)
      (ENNReal.ofReal r) (gaussianMatrixLaw n (k+p)) ∧
    lpNorm (fun G => squaredResidual (diagonal σ) G / optimalSquaredTail k σ)
      (ENNReal.ofReal r) (gaussianMatrixLaw n (k+p)) ≤ gaussianTailMomentConstant k p r := by
  let ℓ := k + p
  let m := n - k
  let hkₙ : k ≤ n := by omega
  let S := splitGaussianMatrix (ℓ := ℓ) hkₙ
  let q := ENNReal.ofReal r
  let μ := gaussianMatrixLaw n ℓ
  let ν := gaussianSplitLaw k ℓ m
  let D : ℝ := optimalSquaredTail k σ
  let t (i : Fin m) := σ (leadingTailEquiv hkₙ (Sum.inr i))
  let b (i : Fin m) := t i ^ 2 / D
  let Y := @gaussianTailRowEnergy k ℓ m
  let W := fun w => ∑ i, b i * Y i w
  let F := fun G : Matrix (Fin n) (Fin ℓ) ℝ => squaredResidual (diagonal σ) G / D
  have hb (i : Fin m) : 0 ≤ b i := div_nonneg (sq_nonneg _) ht.le
  have hD : (∑ i, t i ^ 2) = D := (optimalSquaredTail_eq_sum_tail hkₙ σ).symm
  have hDn : D ≠ 0 := ht.ne'
  have hs : ∑ i, b i = 1 := by simp only [b, ← Finset.sum_div, hD, div_self hDn]
  have hW := gaussianWeightedRows_lpNorm hk hr.le hp b hb hs
  have hS : MeasurePreserving S μ ν := gaussianSplit_measurePreserving hkₙ
  have hU : MemLp (W ∘ S) q μ := hW.1.comp_measurePreserving hS
  have hU' : lpNorm (W ∘ S) q μ = lpNorm W q ν := by
    rw [← toReal_eLpNorm hW.1.aestronglyMeasurable, ← toReal_eLpNorm hU.aestronglyMeasurable,
      eLpNorm_comp_measurePreserving hW.1.aestronglyMeasurable hS]
  have h1 : MemLp (fun _ : Matrix (Fin n) (Fin ℓ) ℝ => (1 : ℝ)) q μ := memLp_const _
  have hZ : MemLp ((fun _ => 1) + (W ∘ S)) q μ := h1.add hU
  have hWnn (w : Matrix (Fin ℓ) (Fin k) ℝ × Matrix (Fin m) (Fin ℓ) ℝ) : 0 ≤ W w :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (gaussianTailRowEnergy_nonneg i w)
  have hSfst : MeasurePreserving (fun G => (S G).1) μ (gaussianMatrixLaw ℓ k) :=
    measurePreserving_fst.comp hS
  have hInj : ∀ᵐ G ∂μ, Function.Injective (S G).1.mulVec :=
    hSfst.quasiMeasurePreserving.tendsto_ae (ae_gaussianMatrix_injective (by omega : k ≤ ℓ))
  have hLE : ∀ᵐ G ∂μ, ‖F G‖ ≤ ‖(1 : ℝ) + W (S G)‖ := by
    filter_upwards [hInj] with G hG
    rw [Real.norm_of_nonneg (residual_div_tail_nonneg k σ ht G),
      Real.norm_of_nonneg (by linarith [hWnn (S G)] : 0 ≤ 1 + W (S G))]
    rw [diagonal_residual_eq_split hkₙ σ G]
    let s (i : Fin k) := σ (leadingTailEquiv hkₙ (Sum.inl i))
    change squaredResidual (fromBlocks (diagonal s) 0 0 (diagonal t))
      (fromRows (S G).1ᵀ (S G).2) / D ≤ 1 + W (S G)
    have h := diagonal_relative_residual_le_weighted_rows s t (hD.symm ▸ ht)
      (S G).1ᵀ (S G).2 (by simpa only [transpose_transpose] using hG)
    simp only [hD] at h
    exact h
  have hF : MemLp F q μ :=
    hZ.mono ((measurable_rawResidual measurable_const measurable_id).div_const _).aestronglyMeasurable hLE
  refine ⟨hF, (lpNorm_mono_of_ae_norm_le hF hZ hLE).trans ?_⟩
  have hq1 : 1 ≤ q := by simpa [q] using ENNReal.ofReal_le_ofReal hr.le
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le hq1)
  have hL := lpNorm_add_le (g := W ∘ S) h1 hq1
  rw [lpNorm_const' hq0 (show q ≠ ∞ from ENNReal.ofReal_ne_top), hU'] at hL
  simp only [norm_one, probReal_univ, Real.one_rpow, mul_one] at hL
  exact hL.trans (add_le_add le_rfl hW.2)

/-- The exact public statement of Lemma 3.2 on the uniform sketch-space law. -/
theorem haarSubspaceLoss_moment (hk : 0 < k) (hl : k + p ≤ n)
    (σ : Fin n → ℝ) (ht : 0 < optimalSquaredTail k σ)
    {r : ℝ} (hr : 1 < r) (_hr2 : r ≤ 2) (hp : 2 * r < (p : ℝ) + 1) :
    MemLp (subspaceLoss k σ) (ENNReal.ofReal r) (haarSketchProjectorLaw hl) ∧
    lpNorm (subspaceLoss k σ) (ENNReal.ofReal r) (haarSketchProjectorLaw hl) ≤
      gaussianTailMomentConstant k p r := by
  let ℓ := k + p
  let q := ENNReal.ofReal r
  let F := fun G : Matrix (Fin n) (Fin ℓ) ℝ => squaredResidual (diagonal σ) G / optimalSquaredTail k σ
  let H := subspaceLoss (l := ℓ) k σ
  let μ := gaussianMatrixLaw n ℓ
  let ν := haarSketchProjectorLaw hl
  have hG := gaussian_relative_residual_lpNorm hk hl σ ht hr hp
  have hF : Measurable F := (measurable_rawResidual measurable_const measurable_id).div_const _
  have hH : Measurable H := measurable_subspaceLoss k σ
  have hEq : μ.map F = ν.map H := gaussianLossLaw_eq_haarProjector hl k σ
  have hLp : MemLp (id : ℝ → ℝ) q (ν.map H) := by
    rw [← hEq]
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hF.aemeasurable).2 hG.1
  have hM : MemLp H q ν :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable hH.aemeasurable).1 hLp
  refine ⟨hM, ?_⟩
  have hN : eLpNorm H q ν = eLpNorm F q μ := by
    calc
      _ = eLpNorm (id : ℝ → ℝ) q (ν.map H) :=
        (eLpNorm_map_measure measurable_id.aestronglyMeasurable hH.aemeasurable).symm
      _ = eLpNorm (id : ℝ → ℝ) q (μ.map F) := by rw [hEq]
      _ = _ := eLpNorm_map_measure measurable_id.aestronglyMeasurable hF.aemeasurable
  change lpNorm H q ν ≤ _
  rw [← toReal_eLpNorm hM.aestronglyMeasurable, hN, toReal_eLpNorm hG.1.aestronglyMeasurable]
  exact hG.2

/-- The moment factor in the growing-width estimate. -/
theorem gaussianTailMomentConstant_two (hp : 4 ≤ p) :
    gaussianTailMomentConstant k p 2 =
      1 + (k : ℝ) * √(3 / (((p : ℝ) - 1) * ((p : ℝ) - 3))) := by
  have hN : standardNormalMoment 2 = 3 := by
    unfold standardNormalMoment
    have h4 (z : ℝ) : |z| ^ (2 * (2 : ℝ)) = z ^ 4 := by
      rw [show 2 * (2 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← abs_pow,
        abs_of_nonneg (by positivity : 0 ≤ z ^ 4)]
    simp_rw [h4]
    exact standardGaussian_fourth_moment
  rw [gaussianTailMomentConstant, hN, chiSquareNegativeMoment_two (by omega),
    Real.sqrt_eq_rpow]
  push_cast
  have h1 : (p : ℝ) + 1 - 2 = p - 1 := by ring
  have h3 : (p : ℝ) + 1 - 4 = p - 3 := by ring
  rw [h1, h3, mul_one_div]


end

end TypicalOrientations
