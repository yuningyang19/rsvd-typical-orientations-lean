import TypicalOrientations.CoordinateProjectionExample
import TypicalOrientations.GaussianWorstCase

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation Filter Edge.Walsh
open scoped Topology

noncomputable section

variable {n ℓ : ℕ}

private theorem coordinateProjector_eq_diagonal (J : Fin ℓ ↪ Fin n) :
    (coordinateSketchProjector J).val =
      diagonal (fun i => (coordinateSketchProjector J).val i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  rw [diagonal_apply_ne _ hij]
  change (∑ a, (if J a = i then (1 : ℝ) else 0) * (if J a = j then 1 else 0)) = 0
  apply Finset.sum_eq_zero
  intro a _
  by_cases hi : J a = i
  · simp [hi, hij]
  · simp [hi]

private theorem squaredResidual_coordinate_diagonal (σ : Fin n → ℝ)
    (hσ : ∀ i, σ i ≠ 0) (J : Fin ℓ ↪ Fin n) :
    squaredResidual (diagonal σ) (coordinateSketchProjector J).val =
      ∑ i, (1 - (coordinateSketchProjector J).val i i) * (σ i) ^ 2 := by
  let P := coordinateSketchProjector J
  let s (i : Fin n) := P.val i i
  let A := diagonal σ
  have hP : P.val = diagonal s := coordinateProjector_eq_diagonal J
  have hDet : IsUnit A.det := by
    change IsUnit (diagonal σ).det
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hσ i)
  have hSurj : Function.Surjective A.toEuclideanLin := by
    intro x
    refine ⟨A⁻¹.toEuclideanLin x, ?_⟩
    change (A.toEuclideanLin.comp A⁻¹.toEuclideanLin) x = x
    rw [← euclidean_mul, Matrix.mul_nonsing_inv _ hDet]
    simp
  have hComm : A * P.val = P.val * A := by
    rw [hP]
    simp only [A, diagonal_mul_diagonal, mul_comm]
  have hImg : rangeProjector (A * P.val) = P.val := by
    rw [hComm]
    calc
      _ = rangeProjector P.val := by
        apply rangeProjector_eq_of_range_eq
        rw [euclidean_mul, LinearMap.range_comp, LinearMap.range_eq_top.mpr hSurj, Submodule.map_top]
      _ = _ := rangeProjector_of_projector _ P.property.1 P.property.2.1
  have hI : (1 : Matrix (Fin n) (Fin n) ℝ) - P.val = diagonal (fun i => 1 - s i) := by
    rw [hP, ← diagonal_one, ← diagonal_sub]
  have hId (i : Fin n) : s i * s i = s i := by
    have h := P.property.2.1
    rw [hP, diagonal_mul_diagonal] at h
    simpa only [diagonal_apply_eq] using congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B i i) h
  change squaredResidual A P.val = ∑ i, (1 - s i) * σ i ^ 2
  rw [squaredResidual, hImg, hI, show A = diagonal σ from rfl, diagonal_mul_diagonal,
    Cosine.squaredFrobenius_eq_sum_entries]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [diagonal_apply_eq, mul_pow, show (1 - s i) ^ 2 = 1 - s i by nlinarith [hId i]]
  · intro j _ hji
    rw [diagonal_apply_ne _ (Ne.symm hji), zero_pow (by decide : 2 ≠ 0)]
  · simp

/-- At the identity orientation every omitted coordinate contributes its
full singular-value energy, with common omission probability `1-ℓ/n`. -/
theorem uniformCoordinates_identity_conditionalMean {k : ℕ} (hn : 0 < n)
    (hℓn : ℓ ≤ n) (σ : Fin n → ℝ) (hσ : ∀ i, σ i ≠ 0) :
    conditionalMean k σ (uniformCoordinateSketchLaw n ℓ) 1 =
      (1 - (ℓ : ℝ) / n) * (∑ i, σ i ^ 2) / optimalSquaredTail k σ := by
  let μ := uniformCoordinateSketchLaw n ℓ
  let : IsProbabilityMeasure μ := isProbabilityMeasure_uniformCoordinateSketchLaw hℓn
  let T := optimalSquaredTail k σ
  let f (i : Fin n) (P : OrthogonalProjector n ℓ) := (1 - P.val i i) * σ i ^ 2
  change (∫ P, squaredResidual (diagonal σ) (1 * P.val) / T ∂μ) = _
  simp only [Matrix.one_mul]
  rw [integral_div]
  have hExpansion : (∫ P, squaredResidual (diagonal σ) P.val ∂μ) = ∫ P, ∑ i, f i P ∂μ := by
    change (∫ P, squaredResidual (diagonal σ) P.val ∂uniformCoordinateSketchLaw n ℓ) =
      ∫ P, ∑ i, f i P ∂uniformCoordinateSketchLaw n ℓ
    rw [uniformCoordinateSketchLaw, integral_finiteLaw, integral_finiteLaw]
    simp_rw [squaredResidual_coordinate_diagonal σ hσ]
    rfl
  rw [hExpansion]
  congr 1
  have hf (i : Fin n) : Integrable (f i) μ :=
    ((integrable_const (1 : ℝ)).sub (integrable_sketchProjector_entry μ i i)).mul_const _
  rw [integral_finsetSum _ (fun i _ => hf i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (∫ P : OrthogonalProjector n ℓ, P.val i i ∂μ) = (ℓ : ℝ) / n := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i)
      (meanSketchProjector_uniformCoordinate hn hℓn)
    simpa only [meanSketchProjector, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, μ] using h
  rw [show (fun P => f i P) = fun P => (1 - P.val i i) * σ i ^ 2 from rfl,
    integral_mul_const, integral_sub (integrable_const _) (integrable_sketchProjector_entry μ i i),
    integral_const, probReal_univ, one_smul, he]

private theorem equalSpikeSpectrum_one_total (hn : 0 < n) {Γ : ℝ} (hΓ : 0 ≤ Γ) :
    (∑ i, (equalSpikeSpectrum (n := n) 1 Γ i) ^ 2) = Γ + n - 1 := by
  classical
  let z : Fin n := ⟨0, hn⟩
  have h (i : Fin n) : (equalSpikeSpectrum 1 Γ i) ^ 2 = 1 + if i = z then Γ - 1 else 0 := by
    by_cases hi : i = z
    · subst i
      simp [equalSpikeSpectrum, z, Real.sq_sqrt hΓ]
    · have hi' : ¬i.val < 1 := by
        intro hlt
        exact hi (Fin.ext (show i.val = 0 by omega))
      simp [equalSpikeSpectrum, hi, hi']
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  simp
  ring

private theorem equalSpikeSpectrum_ne_zero (k : ℕ) {Γ : ℝ} (hΓ : 0 < Γ) (i : Fin n) :
    equalSpikeSpectrum k Γ i ≠ 0 := by
  unfold equalSpikeSpectrum
  split
  · exact (Real.sqrt_pos.2 hΓ).ne'
  · exact one_ne_zero

/-- The two exact expressions for the identity-orientation spike in the introduction. -/
theorem intro_coordinateSpike_identity_mean (hn : 1 < n) (hℓn : ℓ ≤ n)
    {Γ : ℝ} (hΓ : 1 < Γ) :
    conditionalMean 1 (equalSpikeSpectrum (n := n) 1 Γ) (uniformCoordinateSketchLaw n ℓ) 1 =
      ((1 - (ℓ : ℝ) / n) * (Γ + n - 1)) / ((n : ℝ) - 1) ∧
    conditionalMean 1 (equalSpikeSpectrum (n := n) 1 Γ) (uniformCoordinateSketchLaw n ℓ) 1 =
      ((n : ℝ) - ℓ) / ((n : ℝ) - 1) * (1 + (Γ - 1) / n) := by
  have h₁ := uniformCoordinates_identity_conditionalMean (k := 1) (by omega : 0 < n) hℓn
    (equalSpikeSpectrum 1 Γ) (equalSpikeSpectrum_ne_zero 1 (zero_lt_one.trans hΓ))
  rw [equalSpikeSpectrum_one_total (by omega) (zero_lt_one.trans hΓ).le,
    equalSpikeSpectrum_optimalSquaredTail hn.le, Nat.cast_one] at h₁
  refine ⟨h₁, h₁.trans ?_⟩
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn₁ : (n : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn.ne')
  field_simp [hn₀, hn₁]
  ring

/-- The introduction's spectrum is bounded by the exact Gaussian worst-case
benchmark in equation (1.2), at the same dimension and width. -/
theorem intro_coordinateSpike_gaussianMean_le_worstCase {p : ℕ}
    (hp : 2 ≤ p) (hn : 1 + p ≤ n) {Γ : ℝ} (hΓ : 1 < Γ) :
    gaussianMean 1 (1+p) (equalSpikeSpectrum (n := n) 1 Γ) ≤
      ((n : ℝ) - (1+p : ℕ)) / ((n : ℝ) - 1) * (1 + 1 / ((p : ℝ) - 1)) := by
  have hkn : 1 < n := by omega
  let σ := equalSpikeSpectra hkn Γ hΓ.le
  simpa only [gaussianWorstCaseValue, Nat.cast_one, σ, equalSpikeSpectra] using
    gaussianMean_le_worstCase (by decide : 0 < 1) hp hn σ

/-- For the introduction's choice Γ=n² the identity-orientation mean
diverges, although the same-spectrum Gaussian benchmark is uniformly bounded
and the Haar-oriented conditional mean approaches that benchmark in L¹. -/
theorem intro_coordinateSpike_divergence_and_Haar_agreement
    {d : ℕ → ℕ} {p : ℕ} (hp : 2 ≤ p)
    (hℓd : ∀ j, 1 + p ≤ d j) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => conditionalMean 1 (equalSpikeSpectrum (n := d j) 1 ((d j : ℝ)^2))
      (uniformCoordinateSketchLaw (d j) (1+p)) 1) atTop atTop ∧
    (∀ j, gaussianMean 1 (1+p) (equalSpikeSpectrum (n := d j) 1 ((d j : ℝ)^2)) ≤
      gaussianTailMomentConstant 1 p (5/4)) ∧
    Tendsto (fun j =>
      ∫ U, |conditionalMean 1 (equalSpikeSpectrum (n := d j) 1 ((d j : ℝ)^2))
        (uniformCoordinateSketchLaw (d j) (1+p)) U -
        gaussianMean 1 (1+p) (equalSpikeSpectrum (n := d j) 1 ((d j : ℝ)^2))|
        ∂gaussianRightOrthogonalLaw (d j)) atTop (𝓝 0) := by
  let ℓ := 1 + p
  let μ (j : ℕ) := uniformCoordinateSketchLaw (d j) ℓ
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    isProbabilityMeasure_uniformCoordinateSketchLaw (hℓd j)
  have hn (j : ℕ) : 1 < d j := by have := hℓd j; omega
  have hΓ (j : ℕ) : (1 : ℝ) < (d j : ℝ) ^ 2 := by
    have h : (1 : ℝ) < d j := by exact_mod_cast hn j
    nlinarith
  let σ (j : ℕ) := equalSpikeSpectra (hn j) ((d j : ℝ)^2) (hΓ j).le
  refine ⟨?_, ?_, ?_⟩
  · have hN : Tendsto (fun j : ℕ => (d j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hd
    have hDen : Tendsto (fun j : ℕ => (d j : ℝ) - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ (-1) hN
    have hSmall : Tendsto (fun j => (1 - (ℓ : ℝ)) / ((d j : ℝ) - 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hDen
    have hFactor : Tendsto (fun j => 1 + (1 - (ℓ : ℝ)) / ((d j : ℝ) - 1)) atTop (𝓝 1) := by
      simpa using hSmall.const_add 1
    have hFactor' : Tendsto (fun j => ((d j : ℝ) - ℓ) / ((d j : ℝ) - 1)) atTop (𝓝 1) := by
      apply hFactor.congr
      intro j
      have hne : (d j : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (hn j).ne')
      field_simp
      ring
    have hSize : Tendsto (fun j => 1 + (((d j : ℝ)^2) - 1) / (d j : ℝ)) atTop atTop := by
      refine tendsto_atTop_mono (fun j => ?_) hN
      have h : (1 : ℝ) < (d j : ℝ) := by exact_mod_cast hn j
      have h' : (d j : ℝ) - 1 ≤ (((d j : ℝ)^2) - 1) / (d j : ℝ) := by
        apply (le_div_iff₀ (lt_trans zero_lt_one h)).2
        nlinarith
      linarith
    apply (hFactor'.pos_mul_atTop zero_lt_one hSize).congr
    intro j
    exact (intro_coordinateSpike_identity_mean (hn j) (hℓd j) (hΓ j)).2.symm
  · intro j
    exact gaussianMean_le_momentConstant (by decide : 0 < 1) hp (hℓd j) (σ j)
  · have hρ : Tendsto (fun j => meanProjectorNorm (μ j)) atTop (𝓝 0) := by
      have h : Tendsto (fun j => (ℓ : ℝ) / (d j : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hd)
      exact h.congr (fun j => (coordinateSpike_uniform_meanProjectorNorm
        (Nat.zero_lt_of_lt (hn j)) (hℓd j)).symm)
    have hD := (theorem_1_1 (by decide : 0 < 1) hp d hd hℓd μ).1.mp hρ
    apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))) _ hD
    exact Eventually.of_forall (fun j =>
      le_csSup (meanDiscrepancy_bddAbove (by decide : 0 < 1) hp (hℓd j) (μ j))
        (Set.mem_range_self (σ j)))

private theorem coordinateProjector_diagonal_entry (J : Fin ℓ ↪ Fin n) (i : Fin n) :
    (coordinateSketchProjector J).val i i = if i ∈ Set.range J then 1 else 0 := by
  classical
  change (∑ a, (if J a = i then (1 : ℝ) else 0) * (if J a = i then 1 else 0)) = _
  by_cases h : i ∈ Set.range J
  · obtain ⟨a, rfl⟩ := h
    rw [if_pos (Set.mem_range_self a)]
    simp [J.injective.eq_iff]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    have ha : J a ≠ i := fun he => h ⟨a, he⟩
    simp [ha]

/-- The ambient projector law corresponding to any law of distinct coordinate subsets. -/
def coordinateSubsetProjectorLaw (ν : Measure (CoordinateSubset n ℓ)) :
    Measure (OrthogonalProjector n ℓ) :=
  ν.map (fun s => coordinateSketchProjector (coordinateSubsetEmbedding s))

/-- Each mean diagonal entry is the inclusion probability of that coordinate. -/
theorem coordinateSubsetProjectorLaw_mean (ν : Measure (CoordinateSubset n ℓ)) :
    meanSketchProjector (coordinateSubsetProjectorLaw ν) =
      diagonal (fun i : Fin n => ν.real {s | i ∈ s.val}) := by
  classical
  ext i j
  have hMap : Measurable (fun s : CoordinateSubset n ℓ =>
      coordinateSketchProjector (coordinateSubsetEmbedding s)) := measurable_of_countable _
  have he : Measurable (fun P : OrthogonalProjector n ℓ => P.val i j) :=
    (continuous_id.matrix_elem i j).measurable.comp measurable_subtype_coe
  change (∫ P : OrthogonalProjector n ℓ, P.val i j ∂coordinateSubsetProjectorLaw ν) = _
  rw [coordinateSubsetProjectorLaw, integral_map hMap.aemeasurable he.aestronglyMeasurable]
  by_cases hij : i = j
  · subst j
    rw [diagonal_apply_eq]
    have hS : MeasurableSet {s : CoordinateSubset n ℓ | i ∈ s.val} := (Set.to_countable _).measurableSet
    rw [← integral_indicator_one hS]
    apply integral_congr_ae
    refine ae_of_all _ fun s => ?_
    have hRange : Set.range (coordinateSubsetEmbedding s) = (s.val : Set (Fin n)) :=
      Finset.range_orderEmbOfFin s.val s.property
    change (coordinateSketchProjector (coordinateSubsetEmbedding s)).val i i =
      {s : CoordinateSubset n ℓ | i ∈ s.val}.indicator (fun _ => (1 : ℝ)) s
    rw [coordinateProjector_diagonal_entry]
    have hMem : i ∈ Set.range (coordinateSubsetEmbedding s) ↔ i ∈ s.val := by
      rw [hRange]
      rfl
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hMem]
  · rw [diagonal_apply_ne _ hij]
    have hOff (s : CoordinateSubset n ℓ) :
        (coordinateSketchProjector (coordinateSubsetEmbedding s)).val i j = 0 := by
      rw [coordinateProjector_eq_diagonal, diagonal_apply_ne _ hij]
    simp_rw [hOff]
    exact integral_zero _ _

open scoped Matrix.Norms.L2Operator in
/-- For an arbitrary distinct-coordinate sampling law, ρ is its largest inclusion probability. -/
theorem coordinateSubsetProjectorLaw_meanNorm (hn : 0 < n)
    (ν : Measure (CoordinateSubset n ℓ)) :
    let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    meanProjectorNorm (coordinateSubsetProjectorLaw ν) =
      Finset.univ.sup' Finset.univ_nonempty (fun i : Fin n => ν.real {s | i ∈ s.val}) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let f (i : Fin n) := ν.real {s : CoordinateSubset n ℓ | i ∈ s.val}
  let b := Finset.univ.sup' Finset.univ_nonempty f
  have h0 (i : Fin n) : 0 ≤ f i := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := (h0 ⟨0, hn⟩).trans (Finset.le_sup' f (Finset.mem_univ _))
  change ‖meanSketchProjector (coordinateSubsetProjectorLaw ν)‖ = b
  rw [coordinateSubsetProjectorLaw_mean, l2_opNorm_diagonal]
  change ‖f‖ = b
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg hb).2
    intro i
    rw [Real.norm_of_nonneg (h0 i)]
    exact Finset.le_sup' f (Finset.mem_univ i)
  · apply Finset.sup'_le _ _
    intro i _
    simpa only [Real.norm_of_nonneg (h0 i)] using norm_le_pi_norm f i

/-- A uniform draw of ℓ coordinates supported on the first m coordinates. -/
def uniformPrefixCoordinateSketchLaw {m : ℕ} (hmn : m ≤ n) :
    Measure (OrthogonalProjector n ℓ) :=
  finiteLaw (fun s : CoordinateSubset m ℓ =>
    coordinateSketchProjector ((coordinateSubsetEmbedding s).trans (Fin.castLEEmb hmn)))

theorem isProbabilityMeasure_uniformPrefixCoordinateSketchLaw {m : ℕ}
    (hℓm : ℓ ≤ m) (hmn : m ≤ n) :
    IsProbabilityMeasure (uniformPrefixCoordinateSketchLaw (ℓ := ℓ) hmn) := by
  have : Nonempty (CoordinateSubset m ℓ) :=
    ⟨⟨Finset.univ.map (Fin.castLEEmb hℓm), by simp⟩⟩
  unfold uniformPrefixCoordinateSketchLaw
  infer_instance

/-- The exact mean projector of uniform selection inside the indicated prefix. -/
theorem uniformPrefixCoordinateSketch_meanProjector {m : ℕ}
    (hm : 0 < m) (hℓm : ℓ ≤ m) (hmn : m ≤ n) :
    meanSketchProjector (uniformPrefixCoordinateSketchLaw (ℓ := ℓ) hmn) =
      diagonal (fun i : Fin n => if i.val < m then (ℓ : ℝ) / m else 0) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    rw [diagonal_apply_eq]
    change (∫ P : OrthogonalProjector n ℓ, P.val i i
      ∂uniformPrefixCoordinateSketchLaw hmn) = _
    by_cases hi : i.val < m
    · rw [if_pos hi]
      let a : Fin m := ⟨i.val, hi⟩
      have he : Fin.castLEEmb hmn a = i := Fin.ext rfl
      have hEntry (s : CoordinateSubset m ℓ) :
          (coordinateSketchProjector ((coordinateSubsetEmbedding s).trans (Fin.castLEEmb hmn))).val i i =
            (coordinateSketchProjector (coordinateSubsetEmbedding s)).val a a := by
        simp only [coordinateProjector_diagonal_entry]
        have hRange : i ∈ Set.range ((coordinateSubsetEmbedding s).trans (Fin.castLEEmb hmn)) ↔
            a ∈ Set.range (coordinateSubsetEmbedding s) := by
          constructor
          · rintro ⟨b, hb⟩
            exact ⟨b, (Fin.castLEEmb hmn).injective (hb.trans he.symm)⟩
          · rintro ⟨b, hb⟩
            exact ⟨b, (congrArg (Fin.castLEEmb hmn) hb).trans he⟩
        by_cases hb : a ∈ Set.range (coordinateSubsetEmbedding s) <;> simp [hRange, hb]
      have hMean : (∫ P : OrthogonalProjector m ℓ, P.val a a ∂uniformCoordinateSketchLaw m ℓ) =
          (ℓ : ℝ) / m := by
        have h := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => M a a)
          (meanSketchProjector_uniformCoordinate hm hℓm)
        simpa only [meanSketchProjector, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one] using h
      rw [uniformCoordinateSketchLaw, integral_finiteLaw] at hMean
      rw [uniformPrefixCoordinateSketchLaw, integral_finiteLaw]
      simp_rw [hEntry]
      exact hMean
    · rw [if_neg hi, uniformPrefixCoordinateSketchLaw, integral_finiteLaw]
      have hEntry (s : CoordinateSubset m ℓ) :
          (coordinateSketchProjector ((coordinateSubsetEmbedding s).trans (Fin.castLEEmb hmn))).val i i =
            0 := by
        rw [coordinateProjector_diagonal_entry, if_neg]
        rintro ⟨b, hb⟩
        exact hi (by rw [← hb]; exact ((coordinateSubsetEmbedding s) b).isLt)
      simp_rw [hEntry]
      simp
  · rw [diagonal_apply_ne _ hij]
    change (∫ P : OrthogonalProjector n ℓ, P.val i j
      ∂uniformPrefixCoordinateSketchLaw hmn) = 0
    rw [uniformPrefixCoordinateSketchLaw, integral_finiteLaw]
    have hEntry (s : CoordinateSubset m ℓ) :
        (coordinateSketchProjector ((coordinateSubsetEmbedding s).trans (Fin.castLEEmb hmn))).val i j =
          0 := by
      rw [coordinateProjector_eq_diagonal, diagonal_apply_ne _ hij]
    simp_rw [hEntry]
    simp

open scoped Matrix.Norms.L2Operator in
/-- The largest coordinate inclusion probability is exactly ℓ/m. -/
theorem uniformPrefixCoordinateSketch_meanProjectorNorm {m : ℕ}
    (hm : 0 < m) (hℓm : ℓ ≤ m) (hmn : m ≤ n) :
    meanProjectorNorm (uniformPrefixCoordinateSketchLaw (ℓ := ℓ) hmn) =
      (ℓ : ℝ) / m := by
  change ‖meanSketchProjector (uniformPrefixCoordinateSketchLaw (ℓ := ℓ) hmn)‖ = _
  rw [uniformPrefixCoordinateSketch_meanProjector hm hℓm hmn, l2_opNorm_diagonal]
  let f (i : Fin n) := if i.val < m then (ℓ : ℝ) / m else 0
  let i : Fin n := ⟨0, hm.trans_le hmn⟩
  have hVal : f i = (ℓ : ℝ) / m := if_pos hm
  have hNonneg : 0 ≤ (ℓ : ℝ) / m := by positivity
  change ‖f‖ = _
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg hNonneg).2
    intro a
    by_cases h : a.val < m
    · rw [show f a = (ℓ : ℝ) / m from if_pos h, Real.norm_of_nonneg hNonneg]
    · rw [show f a = 0 from if_neg h, norm_zero]
      exact hNonneg
  · simpa only [hVal, Real.norm_of_nonneg hNonneg] using (norm_le_pi_norm f i)

/-- Every individual draw misses each coordinate outside the allowed prefix. -/
theorem uniformPrefixCoordinateSketch_outside_eq_zero {m : ℕ}
    (hmn : m ≤ n) (s : CoordinateSubset m ℓ) (i : Fin n) (hi : m ≤ i.val) :
    (coordinateSketchProjector ((coordinateSubsetEmbedding s).trans (Fin.castLEEmb hmn))).val.toEuclideanLin
      (EuclideanSpace.single i (1 : ℝ)) = 0 := by
  let J := (coordinateSubsetEmbedding s).trans (Fin.castLEEmb hmn)
  have hR : i ∉ Set.range J := by
    rintro ⟨b, hb⟩
    have h : (J b).val < m := ((coordinateSubsetEmbedding s) b).isLt
    rw [hb] at h
    exact (not_lt_of_ge hi) h
  ext j
  change (∑ a, (coordinateSketchProjector J).val j a * (EuclideanSpace.single i (1 : ℝ)) a) = 0
  have hEntry : (coordinateSketchProjector J).val j i = 0 := by
    by_cases hji : j = i
    · rw [hji, coordinateProjector_diagonal_entry, if_neg hR]
    · rw [coordinateProjector_eq_diagonal, diagonal_apply_ne _ hji]
  simp [EuclideanSpace.single, hEntry]

/-- At a prefix of size ⌊√n⌋, both the accessible fraction and the mean
projector norm vanish, and the exact discrepancy tends to zero by Theorem 1.1. -/
theorem uniformPrefixCoordinateSketch_sqrt_regime {d : ℕ → ℕ} {k p : ℕ}
    (hk : 0 < k) (hp : 2 ≤ p) (hℓd : ∀ j, k + p ≤ (d j).sqrt)
    (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => (((d j).sqrt : ℕ) : ℝ) / d j) atTop (𝓝 0) ∧
    Tendsto (fun j => meanProjectorNorm
      (uniformPrefixCoordinateSketchLaw (ℓ := k+p) (Nat.sqrt_le_self (d j)))) atTop (𝓝 0) ∧
    Tendsto (fun j => meanDiscrepancy k
      (uniformPrefixCoordinateSketchLaw (ℓ := k+p) (Nat.sqrt_le_self (d j)))) atTop (𝓝 0) := by
  let m (j : ℕ) := (d j).sqrt
  let μ (j : ℕ) := uniformPrefixCoordinateSketchLaw (ℓ := k + p) (Nat.sqrt_le_self (d j))
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    isProbabilityMeasure_uniformPrefixCoordinateSketchLaw (hℓd j) (Nat.sqrt_le_self (d j))
  have hm (j : ℕ) : 0 < m j := by
    have h : k + p ≤ m j := hℓd j
    omega
  have hM : Tendsto m atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_atTop.1 hd (b^2)] with j hj
    exact Nat.le_sqrt'.2 hj
  have hR : Tendsto (fun j => (m j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hInv : Tendsto (fun j => 1 / (m j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hR
  have hm_frac : Tendsto (fun j => (m j : ℝ) / d j) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _ hInv
    refine Eventually.of_forall fun j => ?_
    have hj : 0 < d j := (hm j).trans_le (Nat.sqrt_le_self (d j))
    apply (div_le_div_iff₀ (Nat.cast_pos.mpr hj) (Nat.cast_pos.mpr (hm j))).2
    rw [one_mul, ← pow_two]
    exact_mod_cast Nat.sqrt_le' (d j)
  have hRho : Tendsto (fun j => meanProjectorNorm (μ j)) atTop (𝓝 0) := by
    have h : Tendsto (fun j => ((k+p : ℕ) : ℝ) / (m j : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hR
    apply h.congr
    intro j
    exact (uniformPrefixCoordinateSketch_meanProjectorNorm (hm j) (hℓd j)
      (Nat.sqrt_le_self (d j))).symm
  exact ⟨hm_frac, hRho, (theorem_1_1 hk hp d hd
    (fun j => (hℓd j).trans (Nat.sqrt_le_self (d j))) μ).1.mp hRho⟩

end

end TypicalOrientations
