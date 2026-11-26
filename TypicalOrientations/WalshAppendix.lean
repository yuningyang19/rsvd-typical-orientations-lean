import SketchOrientation.WalshRSVD
import SketchOrientation.AtomWorstCase
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation SketchOrientation.Edge.Walsh
open Filter Asymptotics
open scoped Topology ENNReal

noncomputable section

variable {m s : ℕ → ℕ} {ell : ℕ}

/-- The prescribed-width first columns in the fixed ordering of Walsh labels. -/
def walshFirstSelector {a : ℕ} (h : ell ≤ 2 ^ a) : Fin ell ↪ Label a :=
  (Fin.castLEEmb h).trans (Fintype.equivFinOfCardEq (card_label a)).symm.toEmbedding

/-- The mean excess over one of the actual residual of the rank-one input
with squared spike `2^m L`. -/
def walshMeanExcess {a b : ℕ} (rows : Fin b ↪ Label a) (cols : Fin ell ↪ Label a)
    (L : ℝ) : ℝ :=
  uniformMean fun d : SignedPermDraw a =>
    tailRelativeError 1 (twoLevelInput (targetFrame rows) ((2 : ℝ)^a * L)) (signedMatrix cols d) - 1

private theorem walshMeanExcess_eq_inherited {a b : ℕ} (rows : Fin b ↪ Label a)
    (cols : Fin ell ↪ Label a) (L : ℝ) :
    walshMeanExcess rows cols L =
      uniformMean fun d : SignedPermDraw a =>
        centeredRankLoss 1 (twoLevelInput (targetFrame rows) ((2 : ℝ)^a * L)) (signedMatrix cols d) := by
  simp only [walshMeanExcess, centeredRankLoss, Nat.cast_one, div_one]

/-- The finite-draw expression is precisely the expected actual residual
minus one under the native signed-Walsh sketch law. -/
theorem walshMeanExcess_eq_integral {a b : ℕ} (rows : Fin b ↪ Label a)
    (cols : Fin ell ↪ Label a) (L : ℝ) :
    walshMeanExcess rows cols L =
      (∫ Z, tailRelativeError 1 (twoLevelInput (targetFrame rows) ((2 : ℝ)^a * L)) Z
        ∂finiteLaw (signedMatrix cols)) - 1 := by
  rw [integral_finiteLaw_eq_uniformMean]
  unfold walshMeanExcess uniformMean
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sub_div, div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- The projection law is the law of the paper's vector `√n Ωᵀ v`. -/
theorem signedPermBlockLaw_eq_actualProjection {a b : ℕ}
    (rows : Fin b ↪ Label a) (cols : Fin ell ↪ Label a) :
    signedPermBlockLaw rows cols = finiteProbabilityLaw (fun d : SignedPermDraw a =>
      (WithLp.toLp 2 (fun j => Real.sqrt ((2 : ℝ)^a) *
        ((signedMatrix cols d)ᵀ * targetFrame rows) j 0) : Block ell)) := by
  unfold signedPermBlockLaw
  congr 1
  funext d
  congr 1
  funext j
  rw [normalizedProjection_eq_targetFrame, ← Matrix.transpose_transpose (targetFrame rows),
    ← Matrix.transpose_mul]
  rfl

private theorem walsh_embed_bound {a b : ℕ} (e : Fin b ↪ Label a) : b ≤ 2^a := by
  simpa only [Fintype.card_fin, card_label] using Fintype.card_le_of_injective e e.injective

private theorem walsh_dimension_tendsto
    (rows : ∀ i, Fin (s i) ↪ Label (m i)) (hs : Tendsto s atTop atTop) :
    Tendsto m atTop atTop := by
  refine tendsto_atTop.2 fun k => ?_
  filter_upwards [hs.eventually_ge_atTop ((2 : ℕ)^k)] with i hi
  by_contra! h
  exact not_lt_of_ge (hi.trans (walsh_embed_bound (rows i))) (Nat.pow_lt_pow_right (by decide) h)

/-- Equation (walsh-cost) and the gap-independent projected Gaussian limit
in §5.3. The statement holds for any fixed selectors, including the first
columns used in the paper. -/
theorem walsh_miss_cost (hell : 2 < ell)
    (rows : ∀ i, Fin (s i) ↪ Label (m i)) (cols : ∀ i, Fin ell ↪ Label (m i))
    (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0)) :
    Tendsto (fun i => signedPermBlockLaw (rows i) (cols i)) atTop (𝓝 (gaussianBlockLaw ell)) ∧
    ((fun i => actualMissProbability (rows i) (cols i)) ~[atTop]
      (fun i => (2 / Real.pi) ^ ((ell : ℝ) / 2) * (s i : ℝ) ^ (-(ell : ℝ) / 2))) ∧
    ∀ L : ℕ → ℝ, Tendsto L atTop atTop →
      Tendsto (fun i => walshMeanExcess (rows i) (cols i) (L i) -
        (2 : ℝ)^m i / ((2 : ℝ)^m i - 1) * L i * actualMissProbability (rows i) (cols i))
        atTop (𝓝 (1 / ((ell : ℝ) - 2))) := by
  obtain ⟨hMiss, hMean⟩ := proposition_6_4_actual hell rows cols hs he hgrowth
  have hRows : ∀ᶠ i in atTop, s i ≤ 2^m i := Eventually.of_forall fun i => walsh_embed_bound (rows i)
  have hCols : ∀ᶠ i in atTop, ell ≤ 2^m i := Eventually.of_forall fun i => walsh_embed_bound (cols i)
  refine ⟨?_, hMiss, ?_⟩
  · simp_rw [signedPermBlockLaw_eq_sampledBlockLaw]
    exact tendsto_sampledBlockLaw hs hRows hCols hgrowth
  · intro L hL
    simp_rw [walshMeanExcess_eq_inherited]
    exact hMean L hL

/-- Direct specialization of equation (walsh-cost) to the paper's first columns. -/
theorem walsh_firstColumns_miss_cost (hell : 2 < ell)
    (rows : ∀ i, Fin (s i) ↪ Label (m i)) (hw : ∀ i, ell ≤ 2 ^ m i)
    (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0)) :
    Tendsto (fun i => signedPermBlockLaw (rows i) (walshFirstSelector (hw i))) atTop
      (𝓝 (gaussianBlockLaw ell)) ∧
    ((fun i => actualMissProbability (rows i) (walshFirstSelector (hw i))) ~[atTop]
      (fun i => (2 / Real.pi) ^ ((ell : ℝ) / 2) * (s i : ℝ) ^ (-(ell : ℝ) / 2))) ∧
    ∀ L : ℕ → ℝ, Tendsto L atTop atTop →
      Tendsto (fun i => walshMeanExcess (rows i) (walshFirstSelector (hw i)) (L i) -
        (2 : ℝ)^m i / ((2 : ℝ)^m i - 1) * L i *
          actualMissProbability (rows i) (walshFirstSelector (hw i)))
        atTop (𝓝 (1 / ((ell : ℝ) - 2))) :=
  walsh_miss_cost hell rows (fun i => walshFirstSelector (hw i)) hs he hgrowth

/-- The error remaining in (walsh-cost) is literally an o(1) term. -/
theorem walsh_firstColumns_miss_cost_littleO (hell : 2 < ell)
    (rows : ∀ i, Fin (s i) ↪ Label (m i)) (hw : ∀ i, ell ≤ 2 ^ m i)
    (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    (fun i => walshMeanExcess (rows i) (walshFirstSelector (hw i)) (L i) -
      (2 : ℝ)^m i / ((2 : ℝ)^m i - 1) * L i *
        actualMissProbability (rows i) (walshFirstSelector (hw i)) - 1 / ((ell : ℝ) - 2))
      =o[atTop] (fun _ => (1 : ℝ)) := by
  apply (isLittleO_one_iff ℝ).2
  exact (tendsto_sub_nhds_zero_iff).2
    ((walsh_firstColumns_miss_cost hell rows hw hs he hgrowth).2.2 L hL)

private theorem walsh_dimension_ratio_tendsto
    (rows : ∀ i, Fin (s i) ↪ Label (m i)) (hs : Tendsto s atTop atTop) :
    Tendsto (fun i => (2 : ℝ)^m i / ((2 : ℝ)^m i - 1)) atTop (𝓝 1) := by
  have hm := walsh_dimension_tendsto rows hs
  have hn := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hm
  have hInv : Tendsto (fun i => ((2 : ℝ)^m i)⁻¹) atTop (𝓝 0) := hn.inv_tendsto_atTop
  have hDen : Tendsto (fun i => 1 - ((2 : ℝ)^m i)⁻¹) atTop (𝓝 1) := by
    simpa only [sub_zero] using hInv.const_sub 1
  have h := hDen.inv₀ one_ne_zero
  rw [inv_one] at h
  apply h.congr'
  filter_upwards [hm.eventually_ge_atTop 1] with i hi
  have hN : (1 : ℝ) < (2 : ℝ)^m i := one_lt_pow₀ (by norm_num) (by omega)
  have hM : (2 : ℝ)^m i ≠ 0 := (zero_lt_one.trans hN).ne'
  have hS : (2 : ℝ)^m i - 1 ≠ 0 := (sub_pos.mpr hN).ne'
  have hW : 1 - ((2 : ℝ)^m i)⁻¹ ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (inv_lt_one_of_one_lt₀ hN))
  change (1 - ((2 : ℝ)^m i)⁻¹)⁻¹ = (2 : ℝ)^m i / ((2 : ℝ)^m i - 1)
  field_simp [hM, hS, hW]

/-- All three asymptotic mean regimes with the same target and sketch laws.
The finite-limit clause includes zero and every finite positive correction. -/
theorem walsh_miss_cost_regimes (hell : 2 < ell)
    (rows : ∀ i, Fin (s i) ↪ Label (m i)) (cols : ∀ i, Fin ell ↪ Label (m i))
    (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    let X := fun i => L i * actualMissProbability (rows i) (cols i)
    let mean := fun i => walshMeanExcess (rows i) (cols i) (L i)
    (∀ a : ℝ, Tendsto X atTop (𝓝 a) → Tendsto mean atTop (𝓝 (1 / ((ell : ℝ) - 2) + a))) ∧
      (Tendsto X atTop atTop → Tendsto mean atTop atTop) := by
  intro X mean
  let ratio := fun i => (2 : ℝ)^m i / ((2 : ℝ)^m i - 1)
  let rem := fun i => mean i - ratio i * X i
  have hR : Tendsto ratio atTop (𝓝 1) := walsh_dimension_ratio_tendsto rows hs
  have hE : Tendsto rem atTop (𝓝 (1 / ((ell : ℝ) - 2))) := by
    refine ((walsh_miss_cost hell rows cols hs he hgrowth).2.2 L hL).congr (fun i => ?_)
    simp only [rem, ratio, X, mean, mul_assoc]
  have hSum (i : ℕ) : rem i + ratio i * X i = mean i := sub_add_cancel _ _
  constructor
  · intro a ha
    have h := hE.add (hR.mul ha)
    rw [one_mul] at h
    exact h.congr hSum
  · intro ha
    exact (hE.add_atTop (hR.pos_mul_atTop zero_lt_one ha)).congr hSum


/-- Explicit gap choices realize the three limits with the same sequence
of targets and sketches. The miss probabilities are eventually positive
and tend to zero, so the three choices can use their negative powers. -/
theorem walsh_miss_cost_realizes_regimes (hell : 2 < ell)
    (rows : ∀ i, Fin (s i) ↪ Label (m i)) (cols : ∀ i, Fin ell ↪ Label (m i))
    (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0)) :
    let mean := fun (L : ℕ → ℝ) i => walshMeanExcess (rows i) (cols i) (L i)
    (∃ L, Tendsto L atTop atTop ∧ Tendsto (mean L) atTop (𝓝 (1 / ((ell : ℝ) - 2)))) ∧
      (∀ a : ℝ, 0 < a → ∃ L, Tendsto L atTop atTop ∧
        Tendsto (mean L) atTop (𝓝 (1 / ((ell : ℝ) - 2) + a))) ∧
      (∃ L, Tendsto L atTop atTop ∧ Tendsto (mean L) atTop atTop) := by
  intro mean
  let πs := fun i => actualMissProbability (rows i) (cols i)
  let α : ℝ := (ell : ℝ) / 2
  let C : ℝ := (2 / Real.pi) ^ α
  have hα : 0 < α := half_pos (Nat.cast_pos.mpr (by omega))
  have hC : 0 < C := Real.rpow_pos_of_pos (div_pos (by norm_num) Real.pi_pos) α
  have hEq : πs ~[atTop] (fun i => C * (s i : ℝ) ^ (-α)) := by
    simpa only [πs, C, α, neg_div] using (walsh_miss_cost hell rows cols hs he hgrowth).2.1
  have hModel0 : Tendsto (fun i => C * (s i : ℝ) ^ (-α)) atTop (𝓝 0) := by
    have hS : Tendsto (fun i => (s i : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hs
    have h := ((tendsto_rpow_neg_atTop hα).comp hS).const_mul C
    rw [mul_zero] at h
    exact h.congr (fun _ => rfl)
  have hModelPos : ∀ᶠ i in atTop, 0 < C * (s i : ℝ) ^ (-α) := by
    filter_upwards [hs.eventually_ge_atTop 1] with i hi
    exact mul_pos hC (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _)
  have hπ0 := hEq.symm.tendsto_nhds hModel0
  have hπPos := hEq.eventually_pos hModelPos
  have hInv : Tendsto (fun i => (πs i)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hπ0, hπPos⟩)
  have hSq0 : Tendsto (fun i => Real.sqrt (πs i)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hπ0
    rw [Real.sqrt_zero] at h
    exact h
  have hSqPos : ∀ᶠ i in atTop, 0 < Real.sqrt (πs i) :=
    hπPos.mono fun _ hi => Real.sqrt_pos_of_pos hi
  let L₀ := fun i => (Real.sqrt (πs i))⁻¹
  have hL₀ : Tendsto L₀ atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hSq0, hSqPos⟩)
  have hX₀ : Tendsto (fun i => L₀ i * πs i) atTop (𝓝 0) := by
    apply hSq0.congr'
    filter_upwards [hπPos] with i hi
    change Real.sqrt (πs i) = (Real.sqrt (πs i))⁻¹ * πs i
    rw [eq_inv_mul_iff_mul_eq₀ (Real.sqrt_pos_of_pos hi).ne', ← pow_two, Real.sq_sqrt hi.le]
  refine ⟨⟨L₀, hL₀, ?_⟩, ?_, ?_⟩
  · simpa only [add_zero] using
      (walsh_miss_cost_regimes hell rows cols hs he hgrowth L₀ hL₀).1 0 hX₀
  · intro a ha
    let L := fun i => a * (πs i)⁻¹
    have hL : Tendsto L atTop atTop := hInv.const_mul_atTop ha
    have hX : Tendsto (fun i => L i * πs i) atTop (𝓝 a) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hπPos] with i hi
      simp only [L, mul_assoc, inv_mul_cancel₀ hi.ne', mul_one]
    exact ⟨L, hL, (walsh_miss_cost_regimes hell rows cols hs he hgrowth L hL).1 a hX⟩
  · let L := fun i => (πs i)⁻¹ ^ (2 : ℕ)
    have hL : Tendsto L atTop atTop := by
      have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp hInv
      exact h.congr (fun i => Real.rpow_two ((πs i)⁻¹))
    have hX : Tendsto (fun i => L i * πs i) atTop atTop := by
      apply hInv.congr'
      filter_upwards [hπPos] with i hi
      simp only [L, pow_two, mul_assoc, inv_mul_cancel₀ hi.ne', mul_one]
    exact ⟨L, hL, (walsh_miss_cost_regimes hell rows cols hs he hgrowth L hL).2 hX⟩

private theorem uniformMap_finiteLaw {A B : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace B] (f : A → B) :
    ((PMF.uniformOfFintype A).map f).toMeasure = finiteLaw f := by
  classical
  let : MeasurableSpace A := ⊤
  let : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  have hm : Measurable f := measurable_from_top
  ext S hs : 1
  rw [PMF.toMeasure_map_apply _ _ _ hm hs, PMF.toMeasure_apply_fintype,
    finiteLaw, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply Finset.univ (fun a => Measure.dirac (f a)) S, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : f a ∈ S
  · simp [Set.indicator, ha, Measure.dirac_apply' _ hs, PMF.uniformOfFintype_apply]
  · simp [Set.indicator, ha, Measure.dirac_apply' _ hs]

private theorem finiteLaw_positive_atom {A B : Type*} [Fintype A] [Nonempty A] [MeasurableSpace B]
    [MeasurableSingletonClass B] (f : A → B) (a : A) :
    0 < (finiteLaw f).real {f a} := by
  rw [measureReal_def, ← uniformMap_finiteLaw f,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), ENNReal.toReal_pos_iff]
  refine ⟨(PMF.apply_pos_iff _ _).mpr ?_, PMF.apply_lt_top _ _⟩
  rw [PMF.support_map]
  exact ⟨a, PMF.mem_support_uniformOfFintype a, rfl⟩

private def figureDctProjector {n l : ℕ} (d : DctDraw n l) : OrthogonalProjector n l := by
  let U := DctPasses.two.sketch d
  have hU : Uᵀ * U = 1 := DctPasses.sketch_orthonormal .two d
  refine ⟨U * Uᵀ, by simp, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
  · rw [Matrix.rank_self_mul_transpose, ← Matrix.rank_transpose_mul_self, hU,
      Matrix.rank_one, Fintype.card_fin]

private theorem integral_twoPassDct_eq_projector {n k l : ℕ} (hl : l ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∫ Z, tailRelativeError k A Z ∂
      (DctPasses.two.sketchLaw hl : Measure (Matrix (Fin n) (Fin l) ℝ))) =
      ∫ P, tailRelativeError k A P.val ∂finiteLaw (@figureDctProjector n l) := by
  let : Nonempty (DctDraw n l) :=
    ⟨(Fin.castLEEmb hl, fun _ => false, fun _ => false)⟩
  have hNative : (DctPasses.two.sketchLaw hl : Measure (Matrix (Fin n) (Fin l) ℝ)) =
      finiteLaw (DctPasses.two.sketch : DctDraw n l → Matrix (Fin n) (Fin l) ℝ) := by
    change ((PMF.uniformOfFintype (DctDraw n l)).map DctPasses.two.sketch).toMeasure = _
    exact uniformMap_finiteLaw _
  rw [hNative, integral_finiteLaw_eq_uniformMean, integral_finiteLaw_eq_uniformMean]
  apply congrArg uniformMean
  funext d
  unfold tailRelativeError
  rw [show (figureDctProjector d).val = DctPasses.two.sketch d * (DctPasses.two.sketch d)ᵀ from rfl,
    squaredResidual_frame_projector A _ (DctPasses.sketch_orthonormal .two d)]

/-- Appendix A.2: the worst-case two-pass DCT mean is unbounded already
over positive-tail invertible square input matrices. -/
theorem twoPassDct_figureNotes_unbounded {n k l : ℕ}
    (hk : 0 < k) (hkl : k < l) (hln : l < n) :
    ∀ a : ℝ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsUnit A ∧ 0 < optimalTail k A ∧
      a < ∫ Z, tailRelativeError k A Z ∂
        (DctPasses.two.sketchLaw hln.le : Measure (Matrix (Fin n) (Fin l) ℝ)) := by
  intro a
  let draw : DctDraw n l := (Fin.castLEEmb hln.le, fun _ => false, fun _ => false)
  let : Nonempty (DctDraw n l) := ⟨draw⟩
  let law := finiteLaw (@figureDctProjector n l)
  obtain ⟨V, hV, hMean⟩ := atom_tailRelativeMean_unbounded hk hkl hln
    law (figureDctProjector draw) (finiteLaw_positive_atom _ draw)
  obtain ⟨Γ, hΓ, hA⟩ := ((eventually_ge_atTop (1 : ℝ)).and (hMean.eventually_gt_atTop a)).exists
  let A := twoLevelInput V Γ
  have hΓ0 : 0 ≤ Γ := zero_le_one.trans hΓ
  have hGram := twoLevelInput_gram V hV hΓ0
  refine ⟨A, ?_, ?_, ?_⟩
  · have hPos : (Aᵀ * A).PosDef := by
      rw [show Aᵀ * A = 1 + (Γ - 1) • (V * Vᵀ) from hGram]
      have hP : (V * Vᵀ).PosSemidef := by
        simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose V
      exact PosDef.one.add_posSemidef (hP.smul (sub_nonneg.mpr hΓ))
    have hd := (Aᵀ * A).isUnit_iff_isUnit_det.mp hPos.isUnit
    rw [Matrix.det_mul, Matrix.det_transpose] at hd
    exact A.isUnit_iff_isUnit_det.mpr (isUnit_of_mul_isUnit_left hd)
  · have hTail := twoLevel_optimalTail A V hV hΓ hGram
    simp only [Fintype.card_fin] at hTail
    rw [hTail]
    exact sub_pos.mpr (by exact_mod_cast hkl.trans hln)
  · rw [integral_twoPassDct_eq_projector hln.le]
    exact hA

end

end TypicalOrientations
