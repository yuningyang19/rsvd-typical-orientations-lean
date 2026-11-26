import TypicalOrientations.WalshRareMiss
import TypicalOrientations.PaperTheorems
import TypicalOrientations.RankDeficiency

namespace TypicalOrientations

open Matrix Filter MeasureTheory SketchOrientation SketchOrientation.Edge.Walsh
open scoped Topology

noncomputable section

variable {m ell : ℕ}

private def swapWalshRows (x y : Label m) : (Fin ell ↪ Label m) ≃ (Fin ell ↪ Label m) where
  toFun J := J.trans (Equiv.swap x y).toEmbedding
  invFun J := J.trans (Equiv.swap x y).toEmbedding
  left_inv J := by ext j; simp
  right_inv J := by ext j; simp

/-- Conditional on any sign vector, a given row is included with probability
ℓ/n under the independent uniform row draw used in §5.2. -/
theorem flatWalsh_uniform_row_inclusion (h : ell ≤ 2^m) (x : Label m) :
    uniformProbability (fun J : Fin ell ↪ Label m => x ∈ Set.range J) = (ell : ℝ) / (2 : ℝ)^m := by
  classical
  let : Nonempty (Fin ell ↪ Label m) := label_embedding_nonempty h
  let f (r : Label m) (J : Fin ell ↪ Label m) := indicator (r ∈ Set.range J)
  have hEqual (r s : Label m) : uniformMean (f r) = uniformMean (f s) := by
    refine (congrArg uniformMean (funext fun J => ?_)).trans
      (uniformMean_equiv (swapWalshRows r s) (f s))
    have hmem : r ∈ Set.range J ↔ s ∈ Set.range (swapWalshRows r s J) := by
      simp only [Set.mem_range]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, Equiv.swap_apply_left (J i) s⟩
      · rintro ⟨i, hi⟩
        refine ⟨i, (Equiv.swap r s).injective ?_⟩
        rw [Equiv.swap_apply_left]
        exact hi
    simp only [f, hmem]
  have hSum (J : Fin ell ↪ Label m) : (∑ r, f r J) = ell := by
    have hmem (r : Label m) : r ∈ Set.range J ↔ r ∈ Finset.univ.map J := by simp [Set.mem_range]
    simp only [f, indicator, hmem]
    rw [← Finset.sum_filter, show (Finset.univ.filter (fun r => r ∈ Finset.univ.map J)) =
      Finset.univ.map J from by ext r; simp]
    simp
  change uniformMean (f x) = _
  apply (eq_div_iff (by positivity : (2 : ℝ)^m ≠ 0)).2
  calc
    uniformMean (f x) * (2 : ℝ)^m = ∑ r : Label m, uniformMean (f r) := by
      simp_rw [fun r => hEqual r x]
      simp [mul_comm]
    _ = uniformMean (fun J : Fin ell ↪ Label m => ∑ r, f r J) :=
      (uniformMean_sum (fun J r => f r J)).symm
    _ = ell := by simp_rw [hSum]; exact uniformMean_const _

private theorem flatWalsh_uniform_selected_sum (h : ell ≤ 2^m) (f : Label m → ℝ) :
    uniformMean (fun J : Fin ell ↪ Label m => ∑ j, f (J j)) =
      ((ell : ℝ) / (2 : ℝ)^m) * ∑ r, f r := by
  classical
  have hsum (J : Fin ell ↪ Label m) : (∑ j, f (J j)) =
      ∑ r, indicator (r ∈ Set.range J) * f r := by
    rw [← Finset.sum_map]
    simp only [indicator, ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
    congr 1
    ext x
    simp [Set.mem_range]
  simp_rw [hsum, uniformMean_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  calc
    uniformMean (fun J : Fin ell ↪ Label m => indicator (r ∈ Set.range J) * f r) =
        uniformProbability (fun J : Fin ell ↪ Label m => r ∈ Set.range J) * f r := by
      simp only [uniformProbability, uniformMean]
      rw [← Finset.sum_mul]
      ring
    _ = _ := by rw [flatWalsh_uniform_row_inclusion h r]

private theorem flatWalsh_signed_core_column_orthogonal (z : Label m → ZMod 2) (x y : Label m) :
    (∑ r : Label m, (core m r x * signValue (z x)) * (core m r y * signValue (z y))) =
      if x = y then 1 else 0 := by
  let n : ℝ := (2 : ℝ)^m
  let c := (Real.sqrt n)⁻¹ ^ 2 * (signValue (z x) * signValue (z y))
  have hTerm (r : Label m) :
      (core m r x * signValue (z x)) * (core m r y * signValue (z y)) =
        c * (signValue (parity r x) * signValue (parity r y)) := by
    dsimp [core, c, n]
    ring
  simp_rw [hTerm, ← Finset.mul_sum, sum_signValue_parity_mul]
  by_cases h : x = y
  · subst y
    simp only [if_true, c, ← pow_two (signValue (z x)), signValue_sq, mul_one]
    change (Real.sqrt n)⁻¹ ^ 2 * n = 1
    rw [inv_pow, Real.sq_sqrt (by unfold n; positivity), inv_mul_cancel₀ (by unfold n; positivity)]
  · simp [h]

/-- The conditional mean over rows is isotropic for every fixed vector of signs. -/
theorem flatWalsh_conditional_projector_entry (h : ell ≤ 2^m)
    (z : Label m → ZMod 2) (x y : Label m) :
    uniformMean (fun J : Fin ell ↪ Label m =>
      (flatWalshSketch (J,z) * (flatWalshSketch (J,z))ᵀ) x y) =
      ((ell : ℝ) / (2 : ℝ)^m) * (if x = y then 1 else 0) := by
  let f (r : Label m) := (core m r x * signValue (z x)) * (core m r y * signValue (z y))
  change uniformMean (fun J : Fin ell ↪ Label m => ∑ j, f (J j)) = _
  rw [flatWalsh_uniform_selected_sum h f, flatWalsh_signed_core_column_orthogonal]

/-- Relabel the Walsh coordinates by `Fin n`, where `n=2^m`. -/
def flatWalshRelabel (m : ℕ) : Label m ≃ Fin (2^m) :=
  Fintype.equivFinOfCardEq (card_label m)

/-- The projector law of the actual SRHT in §5.2, in the coordinates of Theorem 1.1. -/
def flatWalshProjectorLaw (h : ell ≤ 2^m) : Measure (OrthogonalProjector (2^m) ell) :=
  (flatWalshSketchMeasure m ell).map (fun Ω => haarFrameProjector h (Ω.submatrix (flatWalshRelabel m).symm id))

private theorem flatWalsh_relabel_orthonormal (d : FlatWalshDraw m ell) :
    let Ω := (flatWalshSketch d).submatrix (flatWalshRelabel m).symm id
    Ωᵀ * Ω = 1 := by
  dsimp only
  rw [transpose_submatrix, Matrix.submatrix_mul_equiv, flatWalshSketch_orthonormal,
    Matrix.submatrix_id_id]

private theorem measurable_flatWalsh_relabelProjector (h : ell ≤ 2^m) :
    Measurable (fun Ω : Matrix (Label m) (Fin ell) ℝ =>
      haarFrameProjector h (Ω.submatrix (flatWalshRelabel m).symm id)) :=
  (measurable_haarFrameProjector h).comp (continuous_id.matrix_submatrix _ _).measurable

instance (h : ell ≤ 2^m) : IsProbabilityMeasure (flatWalshProjectorLaw h) := by
  let : IsProbabilityMeasure (flatWalshSketchMeasure m ell) := isProbabilityMeasure_flatWalshSketchMeasure h
  exact Measure.isProbabilityMeasure_map (measurable_flatWalsh_relabelProjector h).aemeasurable

/-- The mean sketch projector is exactly ℓ/n times the identity for the
same actual law used in the rare-miss construction. -/
theorem flatWalsh_meanSketchProjector (h : ell ≤ 2^m) :
    meanSketchProjector (flatWalshProjectorLaw h) =
      ((ell : ℝ) / ((2^m : ℕ) : ℝ)) • (1 : Matrix (Fin (2^m)) (Fin (2^m)) ℝ) := by
  classical
  let : Nonempty (Fin ell ↪ Label m) := label_embedding_nonempty h
  let e := (flatWalshRelabel m).symm
  ext i j
  change (∫ P, P.val i j ∂flatWalshProjectorLaw h) = _
  have hm : Measurable (fun P : OrthogonalProjector (2^m) ell => P.val i j) :=
    (continuous_id.matrix_elem i j).measurable.comp measurable_subtype_coe
  rw [flatWalshProjectorLaw, integral_map (measurable_flatWalsh_relabelProjector h).aemeasurable
    hm.aestronglyMeasurable,
    flatWalshSketchMeasure, integral_finiteLaw_eq_uniformMean]
  have hEntry (d : FlatWalshDraw m ell) :
      (haarFrameProjector h ((flatWalshSketch d).submatrix e id)).val i j =
        (flatWalshSketch d * (flatWalshSketch d)ᵀ) (e i) (e j) := by
    rw [haarFrameProjector_val h (flatWalsh_relabel_orthonormal d), transpose_submatrix]
    rfl
  change uniformMean (fun d : FlatWalshDraw m ell => (haarFrameProjector h
    ((flatWalshSketch d).submatrix e id)).val i j) = _
  simp_rw [hEntry]
  rw [uniformMean_prod', uniformMean_comm]
  simp_rw [flatWalsh_conditional_projector_entry h]
  rw [uniformMean_const]
  simp [e.injective.eq_iff, Matrix.one_apply]

/-- The conditional mean really averages the actual finite Walsh draws,
with the same multiplication by the given orientation on each frame. -/
theorem flatWalsh_conditionalMean_eq_draw_average (h : ell ≤ 2^m)
    (k : ℕ) (σ : Fin (2^m) → ℝ) (U : Matrix (Fin (2^m)) (Fin (2^m)) ℝ) :
    conditionalMean k σ (flatWalshProjectorLaw h) U =
      uniformMean (fun d : FlatWalshDraw m ell => squaredResidual (diagonal σ)
        (U * (flatWalshSketch d).submatrix (flatWalshRelabel m).symm id) / optimalSquaredTail k σ) := by
  have hM : Measurable (fun P : OrthogonalProjector (2^m) ell =>
      squaredResidual (diagonal σ) (U * P.val) / optimalSquaredTail k σ) :=
    (measurable_rawResidual measurable_const
      ((continuous_const.matrix_mul continuous_id).measurable.comp measurable_subtype_coe)).div_const _
  rw [conditionalMean, flatWalshProjectorLaw,
    integral_map (measurable_flatWalsh_relabelProjector h).aemeasurable hM.aestronglyMeasurable,
    flatWalshSketchMeasure, integral_finiteLaw_eq_uniformMean]
  apply congrArg uniformMean
  funext d
  let G := (flatWalshSketch d).submatrix (flatWalshRelabel m).symm id
  have hG : Gᵀ * G = 1 := flatWalsh_relabel_orthonormal d
  have hSurj : Function.Surjective Gᵀ.toEuclideanLin := by
    intro x
    refine ⟨G.toEuclideanLin x, ?_⟩
    exact LinearMap.congr_fun (show Gᵀ.toEuclideanLin.comp G.toEuclideanLin = LinearMap.id by
      rw [← euclidean_mul, hG]
      ext y : 1
      simp) x
  change squaredResidual (diagonal σ) (U * (haarFrameProjector h G).val) / _ =
    squaredResidual (diagonal σ) (U * G) / _
  have hP : rangeProjector ((diagonal σ * (U * G)) * Gᵀ) =
      rangeProjector (diagonal σ * (U * G)) := by
    apply rangeProjector_eq_of_range_eq
    rw [euclidean_mul, LinearMap.range_comp, LinearMap.range_eq_top.mpr hSurj, Submodule.map_top]
  rw [haarFrameProjector_val h hG, squaredResidual, squaredResidual,
    ← Matrix.mul_assoc U G, ← Matrix.mul_assoc (diagonal σ) (U * G) Gᵀ, hP]

/-- The squared leading singular value exactly as in the rare-miss construction. -/
def flatWalshGap (m : ℕ) : ℝ := ((2 : ℝ)^m)^2 * (2 : ℝ)^((2 : ℕ)^m)

private theorem flatWalshGap_ge_one (m : ℕ) : 1 ≤ flatWalshGap m :=
  one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (one_le_pow₀ (by norm_num))) (one_le_pow₀ (by norm_num))

/-- The Gaussian mean stays bounded at the exact spectrum and width of the
rare-miss construction. -/
theorem flatWalsh_gap_gaussianMean_le {p : ℕ} (hp : 2 ≤ p) (h : 1+p ≤ 2^m) :
    gaussianMean 1 (1+p) (equalSpikeSpectrum (n := 2^m) 1 (flatWalshGap m)) ≤
      gaussianTailMomentConstant 1 p (5/4) :=
  gaussianMean_le_momentConstant (by decide : 0 < 1) hp h
    (equalSpikeSpectra (by omega : 1 < 2^m) _ (flatWalshGap_ge_one m))

/-- Giving the rare-miss example's spike an independent Haar orientation
restores L¹ agreement with the Gaussian mean for its exact spectrum. -/
theorem flatWalsh_gap_Haar_agreement {digits : ℕ → ℕ} {p : ℕ} (hp : 2 ≤ p)
    (hm : Tendsto digits atTop atTop) (h : ∀ j, 1+p ≤ 2^(digits j)) :
    Tendsto (fun j => ∫ U,
      |conditionalMean 1 (equalSpikeSpectrum (n := 2^(digits j)) 1 (flatWalshGap (digits j)))
        (flatWalshProjectorLaw (h j)) U -
        gaussianMean 1 (1+p) (equalSpikeSpectrum (n := 2^(digits j)) 1 (flatWalshGap (digits j)))|
      ∂gaussianRightOrthogonalLaw (2^(digits j))) atTop (𝓝 0) := by
  let n (j : ℕ) := 2^(digits j)
  let μ (j : ℕ) := flatWalshProjectorLaw (h j)
  have hWidth (j : ℕ) : 1+p ≤ n j := h j
  have hPos (j : ℕ) : 1 < n j := by have := hWidth j; omega
  let σ (j : ℕ) := equalSpikeSpectra (hPos j)
    (flatWalshGap (digits j)) (flatWalshGap_ge_one (digits j))
  have hnR : Tendsto (fun j => (n j : ℝ)) atTop atTop := by
    have ht : Tendsto (fun j => (2 : ℝ)^digits j) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hm
    simpa only [n, Nat.cast_pow, Nat.cast_ofNat] using ht
  have hn : Tendsto n atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hnR.eventually_ge_atTop (b : ℝ)] with j hj
    exact_mod_cast hj
  have hRho : Tendsto (fun j => meanProjectorNorm (μ j)) atTop (𝓝 0) := by
    have hs : Tendsto (fun j => ((1+p : ℕ) : ℝ) / (n j : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnR
    apply hs.congr
    intro j
    exact (meanSketchProjector_norm_of_isotropic (Nat.zero_lt_of_lt (hPos j)) _
      (flatWalsh_meanSketchProjector (h j))).symm
  have hD := (theorem_1_1 (by decide : 0 < 1) hp n hn h μ).1.mp hRho
  change Tendsto (fun j => ∫ U, |conditionalMean 1 (σ j).val (μ j) U -
    gaussianMean 1 (1+p) (σ j).val| ∂gaussianRightOrthogonalLaw (n j)) atTop (𝓝 0)
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))) _ hD
  exact Eventually.of_forall (fun j =>
    le_csSup (meanDiscrepancy_bddAbove (by decide : 0 < 1) hp (h j) (μ j))
      (Set.mem_range_self (σ j)))

end

end TypicalOrientations
