import SketchOrientation.GaussianGramMoments
import Mathlib.Analysis.MeanInequalitiesPow

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

variable {d k : ℕ}

/-- The uniform bound for the diagonal powers in Section 2.3. -/
noncomputable def chiSquareNegativeMoment (ν : ℕ) (r : ℝ) : ℝ :=
  2 ^ (-r) * Real.Gamma ((ν : ℝ) / 2 - r) / Real.Gamma ((ν : ℝ) / 2)

/-- Each inverse diagonal has the exact chi-square inverse power moment. -/
theorem gaussianGram_inv_diag_rpow_mean (hdk : k ≤ d) (j : Fin k) {r : ℝ}
    (hr : 0 < r) (hr' : r < ((d - k + 1 : ℕ) : ℝ) / 2) :
    Integrable (fun Z => ((gaussianGram Z)⁻¹ j j) ^ r) (gaussianMatrixLaw d k) ∧
      (∫ Z, ((gaussianGram Z)⁻¹ j j) ^ r ∂gaussianMatrixLaw d k) =
        chiSquareNegativeMoment (d - k + 1) r := by
  cases k with
  | zero => exact j.elim0
  | succ k =>
    have heq : d - (k + 1) + 1 = d - k := by omega
    rw [heq] at hr' ⊢
    have hm := measurable_gaussianGram_inv_entry (d := d) j j
    have ha := ae_gaussianGram_inv_diag_nonneg hdk j
    have hnn : 0 ≤ᵐ[gaussianMatrixLaw d (k + 1)] (fun Z => ((gaussianGram Z)⁻¹ j j) ^ r) :=
      ha.mono fun Z hz => Real.rpow_nonneg hz r
    have hl : (∫⁻ Z, ENNReal.ofReal (((gaussianGram Z)⁻¹ j j) ^ r)
        ∂gaussianMatrixLaw d (k + 1)) = ENNReal.ofReal (chiSquareNegativeMoment (d - k) r) := by
      calc
        _ = ∫⁻ Z, ENNReal.ofReal ((((gaussianGram Z)⁻¹ j j)⁻¹) ^ (-r))
            ∂gaussianMatrixLaw d (k + 1) := by
          apply lintegral_congr_ae
          filter_upwards [ha] with Z hZ
          rw [Real.inv_rpow hZ, ← Real.rpow_neg hZ, neg_neg]
        _ = ∫⁻ s, ENNReal.ofReal (s ^ (-r)) ∂(gaussianMatrixLaw d (k + 1)).map
            (fun Z => ((gaussianGram Z)⁻¹ j j)⁻¹) :=
          (lintegral_map (measurable_id.pow_const _).ennreal_ofReal hm.inv).symm
        _ = _ := by
          rw [gaussianGram_inv_diag_reciprocal_law hdk, chiSquare_negative_moment hr hr']
          rfl
    have hC : 0 ≤ chiSquareNegativeMoment (d - k) r := by
      unfold chiSquareNegativeMoment
      have ha' : 0 < ((d - k : ℕ) : ℝ) / 2 := hr.trans hr'
      have hγ : 0 < Real.Gamma (((d - k : ℕ) : ℝ) / 2 - r) :=
        Real.Gamma_pos_of_pos (sub_pos.mpr hr')
      have hγ' := Real.Gamma_pos_of_pos ha'
      positivity
    have hm' : AEStronglyMeasurable (fun Z => ((gaussianGram Z)⁻¹ j j) ^ r)
        (gaussianMatrixLaw d (k + 1)) := (hm.pow_const r).aestronglyMeasurable
    refine ⟨⟨hm', ?_⟩, ?_⟩
    · rw [hasFiniteIntegral_iff_ofReal hnn, hl]
      exact ENNReal.ofReal_lt_top
    · rw [integral_eq_lintegral_of_nonneg_ae hnn hm', hl, ENNReal.toReal_ofReal hC]

private theorem normalized_sum_rpow_le {r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (f : Fin k → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ((∑ i, f i) / k) ^ r ≤
      (if 1 ≤ r then (k : ℝ)⁻¹ else (k : ℝ) ^ (-r)) * ∑ i, (f i) ^ r := by
  classical
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hs : 0 ≤ ∑ i, f i := Finset.sum_nonneg fun i _ => hf i
  rw [Real.div_rpow hs hk'.le]
  split_ifs with hr'
  · apply (div_le_iff₀ (Real.rpow_pos_of_pos hk' r)).2
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ) (f := f) hr'
      (fun i _ => hf i)
    simp only [Finset.card_univ, Fintype.card_fin, Real.rpow_sub_one hk'.ne'] at h
    have hfactor : (k : ℝ)⁻¹ * (∑ i, f i ^ r) * (k : ℝ) ^ r =
        ((k : ℝ) ^ r / k) * (∑ i, f i ^ r) := by ring
    rw [hfactor]
    exact h
  · have hs' : (∑ i, f i) ^ r ≤ ∑ i, f i ^ r := by
      have hsub (s : Finset (Fin k)) : (∑ i ∈ s, f i) ^ r ≤ ∑ i ∈ s, f i ^ r := by
        induction s using Finset.induction_on with
        | empty => simp [Real.zero_rpow hr.ne']
        | insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi]
          exact (Real.rpow_add_le_add_rpow (hf i)
            (Finset.sum_nonneg fun j _ => hf j) hr.le (le_of_not_ge hr')).trans
              (add_le_add le_rfl ih)
      exact hsub _
    rw [Real.rpow_neg hk'.le, mul_comm ((k : ℝ) ^ r)⁻¹, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hs' (Real.rpow_nonneg hk'.le _)

/-- Inverse-trace power bounds, with the normalized convexity bound when
`r ≥ 1` and the subadditivity factor `k^(1-r)` when `0 < r < 1`. -/
theorem gaussianGram_inv_trace_moment (hk : 0 < k) (hdk : k ≤ d) {r : ℝ}
    (hr : 0 < r) (hr' : r < ((d - k + 1 : ℕ) : ℝ) / 2) :
    Integrable (fun Z => ((gaussianGram Z)⁻¹.trace / k) ^ r) (gaussianMatrixLaw d k) ∧
      (∫ Z, ((gaussianGram Z)⁻¹.trace / k) ^ r ∂gaussianMatrixLaw d k) ≤
        (if 1 ≤ r then 1 else (k : ℝ) ^ (1 - r)) *
          chiSquareNegativeMoment (d - k + 1) r := by
  let c : ℝ := if 1 ≤ r then (k : ℝ)⁻¹ else (k : ℝ) ^ (-r)
  let u := fun Z : Matrix (Fin d) (Fin k) ℝ => ((gaussianGram Z)⁻¹.trace / k) ^ r
  let v := fun Z : Matrix (Fin d) (Fin k) ℝ => c * ∑ i, ((gaussianGram Z)⁻¹ i i) ^ r
  let C := chiSquareNegativeMoment (d - k + 1) r
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hM (i : Fin k) := gaussianGram_inv_diag_rpow_mean hdk i hr hr'
  have hv : Integrable v (gaussianMatrixLaw d k) :=
    (integrable_finsetSum _ fun i _ => (hM i).1).const_mul c
  have hmu : Measurable u := by
    unfold u Matrix.trace
    simp only [Matrix.diag_apply]
    exact ((Finset.measurable_sum _ fun i _ => measurable_gaussianGram_inv_entry i i).div_const _).pow_const _
  have hpoint : ∀ᵐ Z ∂gaussianMatrixLaw d k, 0 ≤ u Z ∧ u Z ≤ v Z := by
    filter_upwards [ae_gaussianMatrix_injective hdk] with Z hZ
    have hdiag (i : Fin k) : 0 ≤ (gaussianGram Z)⁻¹ i i :=
      ((gaussianGram_posDef Z hZ).inv.diag_pos).le
    exact ⟨Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun i _ => hdiag i) hk'.le) _,
      normalized_sum_rpow_le hk hr _ hdiag⟩
  have hu : Integrable u (gaussianMatrixLaw d k) :=
    hv.mono' hmu.aestronglyMeasurable (hpoint.mono fun Z h => by
      rw [Real.norm_of_nonneg h.1]
      exact h.2)
  refine ⟨hu, (integral_mono_ae hu hv (hpoint.mono fun _ h => h.2)).trans_eq ?_⟩
  change (∫ Z, c * ∑ i, ((gaussianGram Z)⁻¹ i i) ^ r ∂gaussianMatrixLaw d k) =
    (if 1 ≤ r then 1 else (k : ℝ) ^ (1 - r)) * C
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hM i).1)]
  simp only [fun i => (hM i).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold c
  split_ifs with hr'
  · rw [← mul_assoc, inv_mul_cancel₀ hk'.ne', one_mul]
  · rw [← mul_assoc]
    congr 1
    calc
      (k : ℝ) ^ (-r) * k = (k : ℝ) ^ (-r) * (k : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (k : ℝ) ^ (1 - r) := by rw [← Real.rpow_add hk', neg_add_eq_sub]

end SketchOrientation
