import SketchOrientation.EdgeCap
import SketchOrientation.GaussianMatrixSpace
import SketchOrientation.SpectralGram

/-! The lower-tail criterion for the spectrum of the paper's real block. -/

namespace SketchOrientation

open Edge Filter Matrix MeasureTheory Topology

variable {k ℓ : ℕ}

/-- The normalized mean loss of Eq. (2.3) as a function of the block law. -/
noncomputable def rowBlockExpectedLoss (μ : ProbabilityMeasure (Matrix (Fin k) (Fin ℓ) ℝ))
    (n L : ℝ) : ℝ :=
  scaledGapMean μ (fun j B ↦ gramEigenvalues B j) n k ℓ L

/-- The vanishing lower-tail condition in Proposition 6.1, for the square of the least row
singular value of the rectangular block. -/
def RowBlockVanishingCap (μ : ℕ → ProbabilityMeasure (Matrix (Fin k) (Fin ℓ) ℝ))
    (hk : 0 < k) (b : ℕ → ℝ) : Prop :=
  VanishingCap (fun j ↦ (μ j : Measure (Matrix (Fin k) (Fin ℓ) ℝ)))
    (fun B ↦ minSingularValue B hk ^ 2) b

/-- The quantifier form of the condition equals the nested lower-tail limit in Eq. (6.1). -/
theorem rowBlockVanishingCap_iff_iInf_limsup
    (μ : ℕ → ProbabilityMeasure (Matrix (Fin k) (Fin ℓ) ℝ)) (hk : 0 < k) (b : ℕ → ℝ) :
    RowBlockVanishingCap μ hk b ↔
      (⨅ δ : {δ : ℝ // 0 < δ}, limsup (fun j ↦ capTail
        (μ j : Measure (Matrix (Fin k) (Fin ℓ) ℝ))
        (fun B ↦ minSingularValue B hk ^ 2) (b j) δ) atTop) = 0 :=
  vanishingCap_iff_iInf_limsup _ _ _

private theorem VanishingCap.congr_regularizer {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (X : Ω → ℝ) {b b' : ℕ → ℝ} (hb : b =ᶠ[atTop] b') :
    VanishingCap μ X b ↔ VanishingCap μ X b' := by
  constructor <;> intro h ε hε <;> obtain ⟨δ, hδ, hcut⟩ := h ε hε <;>
    refine ⟨δ, hδ, ?_⟩
  · filter_upwards [hb, hcut] with j he hj
    simpa only [he] using hj
  · filter_upwards [hb, hcut] with j he hj
    simpa only [← he] using hj

private theorem continuous_gramEigenvalues_apply (j : Fin k) :
    Continuous (fun B : Matrix (Fin k) (Fin ℓ) ℝ ↦ gramEigenvalues B j) :=
  (continuous_apply j).comp continuous_gramEigenvalues

/-- The reciprocal eigenvalue means sum to the inverse-trace mean. Integrability of the
inverse trace supplies the required integrability of each individual reciprocal. -/
theorem rowBlockInverseMean_eq_integral_trace
    (ν : ProbabilityMeasure (Matrix (Fin k) (Fin ℓ) ℝ))
    (hpos : ∀ᵐ B ∂(ν : Measure (Matrix (Fin k) (Fin ℓ) ℝ)), ∀ j, 0 < gramEigenvalues B j)
    (hint : Integrable (fun B : Matrix (Fin k) (Fin ℓ) ℝ ↦ ((B * Bᵀ)⁻¹).trace)
      (ν : Measure (Matrix (Fin k) (Fin ℓ) ℝ))) :
    (∀ j, Integrable (fun B ↦ (gramEigenvalues B j)⁻¹)
      (ν : Measure (Matrix (Fin k) (Fin ℓ) ℝ))) ∧
    inverseMean ν (fun j B ↦ gramEigenvalues B j) 0 =
      ∫ B : Matrix (Fin k) (Fin ℓ) ℝ, ((B * Bᵀ)⁻¹).trace ∂(ν : Measure (Matrix (Fin k) (Fin ℓ) ℝ)) := by
  have heq : (fun B : Matrix (Fin k) (Fin ℓ) ℝ ↦ ((B * Bᵀ)⁻¹).trace)
      =ᵐ[(ν : Measure (Matrix (Fin k) (Fin ℓ) ℝ))]
        (fun B ↦ ∑ j, (gramEigenvalues B j)⁻¹) :=
    hpos.mono fun B ↦ trace_inverse_rowGram_eq_sum B
  have hsum := hint.congr heq
  have hcoord (j : Fin k) : Integrable (fun B ↦ (gramEigenvalues B j)⁻¹)
      (ν : Measure (Matrix (Fin k) (Fin ℓ) ℝ)) := by
    apply hsum.mono' (continuous_gramEigenvalues_apply j).measurable.inv.aestronglyMeasurable
    apply ae_of_all
    intro B
    change ‖(gramEigenvalues B j)⁻¹‖ ≤ ∑ i, (gramEigenvalues B i)⁻¹
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (gramEigenvalues_nonneg B j))]
    exact Finset.single_le_sum (fun i _ ↦ inv_nonneg.mpr (gramEigenvalues_nonneg B i))
      (Finset.mem_univ j)
  refine ⟨hcoord, ?_⟩
  simp only [inverseMean, add_zero]
  rw [← integral_finsetSum _ (fun j _ ↦ hcoord j)]
  exact integral_congr_ae heq.symm

/-- The finite-gap lower-tail equivalence for the actual block, allowing a general limiting law
with positive spectrum and integrable reciprocals. -/
theorem tendsto_rowBlockExpectedLoss_iff {μ : ℕ → ProbabilityMeasure (Matrix (Fin k) (Fin ℓ) ℝ)}
    {ν : ProbabilityMeasure (Matrix (Fin k) (Fin ℓ) ℝ)} (hμ : Tendsto μ atTop (𝓝 ν))
    (hk : 0 < k) (hpos : ∀ j, ∀ᵐ B ∂(ν : Measure (Matrix (Fin k) (Fin ℓ) ℝ)),
      0 < gramEigenvalues B j)
    (hint : ∀ j, Integrable (fun B ↦ (gramEigenvalues B j)⁻¹)
      (ν : Measure (Matrix (Fin k) (Fin ℓ) ℝ)))
    {n L : ℕ → ℝ} (hn : Tendsto n atTop atTop) (hL : Tendsto L atTop atTop) :
    Tendsto (fun j ↦ rowBlockExpectedLoss (μ j) (n j) (L j)) atTop
      (𝓝 (inverseMean ν (fun j B ↦ gramEigenvalues B j) 0 / k)) ↔
      RowBlockVanishingCap μ hk (fun j ↦ gapRegularizer (n j) k (L j)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  let good := fun j ↦ (k : ℝ) < n j ∧ 0 < (k : ℝ) * L j - (n j)⁻¹
  have hdenom : Tendsto (fun j ↦ (k : ℝ) * L j - (n j)⁻¹) atTop atTop := by
    simpa only [sub_eq_add_neg, Pi.inv_apply] using
      (hL.const_mul_atTop hk').atTop_add hn.inv_tendsto_atTop.neg
  have hgood : ∀ᶠ j in atTop, good j :=
    (hn.eventually_gt_atTop k).and (hdenom.eventually_gt_atTop 0)
  let n' : ℕ → ℝ := fun j ↦ if good j then n j else k + 1
  let L' : ℕ → ℝ := fun j ↦ if good j then L j else gapOfRegularizer (k + 1) k 1
  have hN : n =ᶠ[atTop] n' := hgood.mono fun j hj ↦ by simp [n', hj]
  have hΛ : L =ᶠ[atTop] L' := hgood.mono fun j hj ↦ by simp [L', hj]
  have hNk (j : ℕ) : (k : ℝ) < n' j := by
    by_cases hj : good j
    · simpa [n', hj] using hj.1
    · simp [n', hj]
  have hD (j : ℕ) : 0 < (k : ℝ) * L' j - (n' j)⁻¹ := by
    by_cases hj : good j
    · simpa [n', L', hj] using hj.2
    · simp [n', L', hj, gapOfRegularizer, mul_div_cancel₀ _ hk'.ne']
  have hm := tendsto_scaledGapMean_iff (μ := μ) (X := fun j B ↦ gramEigenvalues B j)
    (ell := (ℓ : ℝ)) (m := inverseMean ν (fun j B ↦ gramEigenvalues B j) 0)
    hk' (hn.congr' hN) (hL.congr' hΛ) hNk hD
  have hcap := tendsto_inverseMean_iff_vanishingCap hμ continuous_gramEigenvalues_apply
    (fun j B ↦ gramEigenvalues_nonneg B j) hpos hint ⟨k - 1, by omega⟩
    (fun j B ↦ gramMinEigenvalue_le B hk j)
    (b := fun j ↦ gapRegularizer (n' j) k (L' j))
    (fun j ↦ inv_pos.mpr (hD j)) (tendsto_gapRegularizer hk' (hn.congr' hN) (hL.congr' hΛ))
  have hLoss : (fun j ↦ rowBlockExpectedLoss (μ j) (n j) (L j)) =ᶠ[atTop]
      (fun j ↦ scaledGapMean (μ j) (fun i B ↦ gramEigenvalues B i) (n' j) k ℓ (L' j)) := by
    filter_upwards [hN, hΛ] with j hnj hLj
    simp [rowBlockExpectedLoss, hnj, hLj]
  have hiso : (fun j ↦ gapRegularizer (n' j) k (L' j)) =ᶠ[atTop]
      (fun j ↦ gapRegularizer (n j) k (L j)) := by
    filter_upwards [hN, hΛ] with j hnj hLj
    simp [← hnj, ← hLj]
  rw [tendsto_congr' hLoss, hm, hcap, RowBlockVanishingCap]
  simp_rw [sq_minSingularValue_eq_gramMinEigenvalue]
  exact VanishingCap.congr_regularizer _ _ hiso

/-- The unregularized lower-tail condition is equivalent to the correct limit at every
sequence of diverging gaps for the same block laws. -/
theorem tendsto_rowBlockExpectedLoss_for_all_iff
    {μ : ℕ → ProbabilityMeasure (Matrix (Fin k) (Fin ℓ) ℝ)}
    {ν : ProbabilityMeasure (Matrix (Fin k) (Fin ℓ) ℝ)} (hμ : Tendsto μ atTop (𝓝 ν))
    (hk : 0 < k) (hpos : ∀ j, ∀ᵐ B ∂(ν : Measure (Matrix (Fin k) (Fin ℓ) ℝ)),
      0 < gramEigenvalues B j)
    (hint : ∀ j, Integrable (fun B ↦ (gramEigenvalues B j)⁻¹)
      (ν : Measure (Matrix (Fin k) (Fin ℓ) ℝ)))
    {n : ℕ → ℝ} (hn : Tendsto n atTop atTop) :
    (∀ L : ℕ → ℝ, Tendsto L atTop atTop →
      Tendsto (fun j ↦ rowBlockExpectedLoss (μ j) (n j) (L j)) atTop
        (𝓝 (inverseMean ν (fun j B ↦ gramEigenvalues B j) 0 / k))) ↔
      RowBlockVanishingCap μ hk (fun _ ↦ 0) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold RowBlockVanishingCap
  rw [← vanishingCap_all_iff]
  constructor
  · intro hall b hb hbt
    let L := fun j ↦ gapOfRegularizer (n j) k (b j)
    have hL := tendsto_gapOfRegularizer hk' hn hb hbt
    simpa only [RowBlockVanishingCap, L, gapRegularizer_gapOfRegularizer _ hk'] using
      (tendsto_rowBlockExpectedLoss_iff hμ hk hpos hint hn hL).mp (hall L hL)
  · intro hall L hL
    apply (tendsto_rowBlockExpectedLoss_iff hμ hk hpos hint hn hL).mpr
    let b := fun j ↦ gapRegularizer (n j) k (L j)
    have hbt := tendsto_gapRegularizer hk' hn hL
    have hdenom : Tendsto (fun j ↦ (k : ℝ) * L j - (n j)⁻¹) atTop atTop := by
      simpa only [sub_eq_add_neg, Pi.inv_apply] using
        (hL.const_mul_atTop hk').atTop_add hn.inv_tendsto_atTop.neg
    have hpos : ∀ᶠ j in atTop, 0 < b j :=
      (hdenom.eventually_gt_atTop 0).mono fun _ hj ↦ inv_pos.mpr hj
    let b' := fun j ↦ if 0 < b j then b j else 1
    have hb' (j : ℕ) : 0 < b' j := by
      by_cases hj : 0 < b j <;> simp [b', hj]
    have hb : b =ᶠ[atTop] b' := hpos.mono fun j hj ↦ by simp [b', hj]
    exact (VanishingCap.congr_regularizer _ _ hb).mpr (hall b' hb' (hbt.congr' hb))

end SketchOrientation
