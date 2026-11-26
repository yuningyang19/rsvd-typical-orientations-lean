import SketchOrientation.GaussianOrientationTheorem
import SketchOrientation.CosineWindowHaar
import SketchOrientation.DctSketchLaw
import SketchOrientation.GaussianTailGram
import SketchOrientation.StandardGaussianMoments
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

namespace SketchOrientation

open Matrix MeasureTheory ProbabilityTheory Filter Edge.Walsh
open scoped Topology RealInnerProductSpace Matrix.Norms.L2Operator

noncomputable section

variable {n l : ℕ}

/-- The actual projector onto the distinct coordinates selected by J. -/
def coordinateSketchProjector (J : Fin l ↪ Fin n) : OrthogonalProjector n l :=
  ⟨(rowSelector J)ᵀ * rowSelector J, by rw [transpose_mul, transpose_transpose],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (rowSelector J), rowSelector_orthonormal,
      Matrix.one_mul],
    by rw [Matrix.rank_transpose_mul_self, ← Matrix.rank_self_mul_transpose,
      rowSelector_orthonormal, Matrix.rank_one, Fintype.card_fin]⟩

abbrev CoordinateSubset (n l : ℕ) := {s : Finset (Fin n) // s.card = l}

def coordinateSubsetEmbedding (s : CoordinateSubset n l) : Fin l ↪ Fin n :=
  (s.val.orderEmbOfFin s.property).toEmbedding

/-- A uniformly drawn subset, with its order used only to name the readout. -/
def uniformCoordinateSubsetLaw (n l : ℕ) : Measure (CoordinateSubset n l) :=
  finiteLaw id

def fixedCoordinateSketchLaw (hl : l ≤ n) : Measure (OrthogonalProjector n l) :=
  Measure.dirac (coordinateSketchProjector (Fin.castLEEmb hl))

def uniformCoordinateSketchLaw (n l : ℕ) : Measure (OrthogonalProjector n l) :=
  finiteLaw (fun s : CoordinateSubset n l => coordinateSketchProjector (coordinateSubsetEmbedding s))

private theorem nonempty_coordinateSubset (hl : l ≤ n) : Nonempty (CoordinateSubset n l) :=
  ⟨⟨Finset.univ.map (Fin.castLEEmb hl), by simp⟩⟩

instance (hl : l ≤ n) : IsProbabilityMeasure (fixedCoordinateSketchLaw hl) := inferInstanceAs
  (IsProbabilityMeasure (Measure.dirac _))

theorem isProbabilityMeasure_uniformCoordinateSketchLaw (hl : l ≤ n) :
    IsProbabilityMeasure (uniformCoordinateSketchLaw n l) := by
  let := nonempty_coordinateSubset hl
  unfold uniformCoordinateSketchLaw
  infer_instance

private theorem coordinateSketchProjector_subset_entry (s : CoordinateSubset n l) (i j : Fin n) :
    (coordinateSketchProjector (coordinateSubsetEmbedding s)).val i j =
      if i = j ∧ i ∈ s.val then 1 else 0 := by
  classical
  let J := coordinateSubsetEmbedding s
  change (∑ a, (if J a = i then (1 : ℝ) else 0) * (if J a = j then 1 else 0)) = _
  have hRange : Set.range J = (s.val : Set (Fin n)) := Finset.range_orderEmbOfFin s.val s.property
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ s.val
    · obtain ⟨a, rfl⟩ : i ∈ Set.range J := by rwa [hRange]
      rw [if_pos ⟨rfl, hi⟩]
      simp [J.injective.eq_iff]
    · rw [if_neg (fun h => hi h.2)]
      refine Finset.sum_eq_zero fun a _ => ?_
      have hn : J a ≠ i := by
        intro e
        have he : i ∈ Set.range J := ⟨a, e⟩
        rw [hRange] at he
        exact hi he
      simp [hn]
  · rw [if_neg (fun h => hij h.1)]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases h : J a = i
    · simp [h, hij]
    · simp [h]

private def coordinateSubsetSwap (i j : Fin n) : CoordinateSubset n l ≃ CoordinateSubset n l where
  toFun s := ⟨s.val.map (Equiv.swap i j).toEmbedding, (Finset.card_map _).trans s.property⟩
  invFun s := ⟨s.val.map (Equiv.swap i j).toEmbedding, (Finset.card_map _).trans s.property⟩
  left_inv s := by
    apply Subtype.ext
    change (s.val.map (Equiv.swap i j).toEmbedding).map (Equiv.swap i j).toEmbedding = s.val
    ext x
    simp only [Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_self]
  right_inv s := by
    apply Subtype.ext
    change (s.val.map (Equiv.swap i j).toEmbedding).map (Equiv.swap i j).toEmbedding = s.val
    ext x
    simp only [Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_self]

/-- The uniform-coordinate mean projector is exactly (l/n) times the identity. -/
theorem meanSketchProjector_uniformCoordinate (hn : 0 < n) (hl : l ≤ n) :
    meanSketchProjector (uniformCoordinateSketchLaw n l) =
      ((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  let := nonempty_coordinateSubset hl
  let f (i : Fin n) (s : CoordinateSubset n l) := if i ∈ s.val then (1 : ℝ) else 0
  have hEqual (i j : Fin n) : uniformMean (f i) = uniformMean (f j) := by
    have h := uniformMean_equiv (coordinateSubsetSwap (l := l) i j) (f j)
    refine (congrArg uniformMean (funext fun s => ?_)).trans h
    change (if i ∈ s.val then (1 : ℝ) else 0) =
      (if j ∈ s.val.map (Equiv.swap i j).toEmbedding then 1 else 0)
    simp only [Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_right]
  have hSum (s : CoordinateSubset n l) : (∑ i, f i s) = l := by
    change (∑ i : Fin n, if i ∈ s.val then (1 : ℝ) else 0) = l
    simp [s.property]
  have hRing (i : Fin n) : uniformMean (f i) = (l : ℝ) / n := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hn.ne')).2
    calc
      uniformMean (f i) * n = ∑ j : Fin n, uniformMean (f j) := by
        simp_rw [fun j : Fin n => hEqual j i]
        simp [mul_comm]
      _ = uniformMean (fun s : CoordinateSubset n l => ∑ j, f j s) := by
        unfold uniformMean
        rw [← Finset.sum_div, Finset.sum_comm]
      _ = l := by simp_rw [hSum]; exact uniformMean_const _
  ext i j
  change (∫ P, P.val i j ∂uniformCoordinateSketchLaw n l) = _
  rw [uniformCoordinateSketchLaw, integral_finiteLaw]
  simp_rw [coordinateSketchProjector_subset_entry]
  rw [Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp only [true_and, smul_eq_mul, if_true, mul_one]
    simpa only [uniformMean, div_eq_mul_inv, mul_comm, f] using hRing i
  · simp [hij]

/-- The Gaussian observation at each prescribed selector has exactly the
same rectangular iid law. In particular this holds at every atom of an
independently sampled coordinate subset. -/
theorem coordinateSketch_readout_law (J : Fin l ↪ Fin n) :
    (gaussianMatrixLaw n 1).map (fun G => G.submatrix J id) = gaussianMatrixLaw l 1 :=
  gaussianMatrixLaw_map_submatrix_rows J

private theorem coordinateCompression_rankOne (J : Fin l ↪ Fin n)
    (V : Matrix (Fin n) (Fin 1) ℝ) :
    (Vᵀ * (coordinateSketchProjector J).val * V) 0 0 = ∑ i, V (J i) 0 ^ 2 := by
  let R := rowSelector J
  change (Vᵀ * (Rᵀ * R) * V) 0 0 = _
  have hGram : Vᵀ * (Rᵀ * R) * V = (R * V)ᵀ * (R * V) := by
    simp only [transpose_mul, Matrix.mul_assoc]
  have hR (i : Fin l) : (R * V) i 0 = V (J i) 0 := by
    simp [R, rowSelector, Matrix.mul_apply]
  rw [hGram, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, hR, pow_two]

open scoped MatrixOrder in
/-- The native polar target at rank one is exactly the Gaussian column
divided by its Euclidean norm. -/
theorem gaussianPolarFrame_rankOne_normalization (G : Matrix (Fin n) (Fin 1) ℝ) (i : Fin n) :
    gaussianPolarFrame G i 0 = G i 0 / Real.sqrt (∑ j, G j 0 ^ 2) := by
  let H := gaussianPolarRadial G
  have hH : (H 0 0) ^ 2 = ∑ j, G j 0 ^ 2 := by
    have h := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℝ => A 0 0) (gaussianPolarRadial_sq G)
    simpa only [H, Matrix.mul_apply, gaussianGram, transpose_apply, Fintype.sum_unique,
      Fin.default_eq_zero, pow_two] using h
  have hP : H.PosSemidef := (CFC.sqrt_nonneg (gaussianGram G)).posSemidef
  have hE : H 0 0 = Real.sqrt (∑ j, G j 0 ^ 2) := by
    rw [← hH, Real.sqrt_sq hP.diag_nonneg]
  calc
    _ = G i 0 * (H 0 0)⁻¹ := by
      simp [gaussianPolarFrame, Matrix.mul_apply, Matrix.inv_subsingleton, Fin.default_eq_zero, H]
    _ = _ := by rw [hE, div_eq_mul_inv]

/-- The exact squared cosine for a rank-one polar target and any coordinate
selector is the selected normal energy divided by its total energy. -/
theorem coordinatePolarCompression_eq (J : Fin l ↪ Fin n)
    (G : Matrix (Fin n) (Fin 1) ℝ) :
    ((gaussianPolarFrame G)ᵀ * (coordinateSketchProjector J).val * gaussianPolarFrame G) 0 0 =
      (∑ i, G (J i) 0 ^ 2) / (∑ j, G j 0 ^ 2) := by
  let H := gaussianPolarRadial G
  have hH : (H 0 0) ^ 2 = ∑ j, G j 0 ^ 2 := by
    have h := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℝ => A 0 0) (gaussianPolarRadial_sq G)
    simpa only [H, Matrix.mul_apply, gaussianGram, transpose_apply, Fintype.sum_unique,
      Fin.default_eq_zero, pow_two] using h
  have hV (i : Fin n) : gaussianPolarFrame G i 0 = G i 0 * (H 0 0)⁻¹ := by
    simp [gaussianPolarFrame, Matrix.mul_apply, Matrix.inv_subsingleton, Fin.default_eq_zero, H]
  rw [coordinateCompression_rankOne]
  calc
    _ = ∑ i : Fin l, G (J i) 0 ^ 2 * ((H 0 0) ^ 2)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hV, mul_pow, inv_pow]
    _ = _ := by rw [← Finset.sum_mul, hH, div_eq_mul_inv]

private theorem trace_inv_finOne (A : Matrix (Fin 1) (Fin 1) ℝ) : A⁻¹.trace = (A 0 0)⁻¹ := by
  simp [Matrix.inv_subsingleton, Matrix.trace_diagonal, Fin.default_eq_zero]

/-- The conditional endpoint for a deterministic coordinate sketch, in the
same normalization as the actual two-level residual. -/
theorem fixedCoordinateEndpoint_eq (hl : l ≤ n) (G : Matrix (Fin n) (Fin 1) ℝ) :
    haarOrientationEndpoint (fixedCoordinateSketchLaw hl) (gaussianPolarFrame G) =
      (((∑ j, G j 0 ^ 2) / (∑ i : Fin l, G (Fin.castLEEmb hl i) 0 ^ 2)) - l) /
        ((n : ℝ) - 1) := by
  unfold haarOrientationEndpoint fixedCoordinateSketchLaw
  rw [integral_dirac]
  unfold gaussianOrientationScore gaussianProjectedInverseTrace
  rw [trace_inv_finOne, coordinatePolarCompression_eq, inv_div]
  simp

private theorem measurable_coordinateCompression (J : Fin l ↪ Fin n) :
    Measurable (fun V : Matrix (Fin n) (Fin 1) ℝ => Vᵀ * (coordinateSketchProjector J).val * V) :=
  ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).measurable

/-- Redrawing a Haar target for the individual sketch gives the same
compressed Gram law at every deterministic coordinate selector. -/
theorem coordinateSketch_compression_law_equal (hl : l ≤ n) (hn : 1 ≤ n)
    (J J' : Fin l ↪ Fin n) :
    (gaussianHaarFrameLaw hn).map (fun V : Matrix (Fin n) (Fin 1) ℝ =>
      Vᵀ * (coordinateSketchProjector J).val * V) =
    (gaussianHaarFrameLaw hn).map (fun V : Matrix (Fin n) (Fin 1) ℝ =>
      Vᵀ * (coordinateSketchProjector J').val * V) := by
  have hJ : ((rowSelector J)ᵀ)ᵀ * (rowSelector J)ᵀ = 1 := by
    rw [transpose_transpose, rowSelector_orthonormal]
  have hJ' : ((rowSelector J')ᵀ)ᵀ * (rowSelector J')ᵀ = 1 := by
    rw [transpose_transpose, rowSelector_orthonormal]
  obtain ⟨Q, hQ, he⟩ := exists_orthogonal_mul_frame_eq hl hJ hJ'
  let f (V : Matrix (Fin n) (Fin 1) ℝ) := Vᵀ * (coordinateSketchProjector J).val * V
  let g (V : Matrix (Fin n) (Fin 1) ℝ) := Vᵀ * (coordinateSketchProjector J').val * V
  let F (V : Matrix (Fin n) (Fin 1) ℝ) := Qᵀ * V
  have hF : Measurable F := (continuous_const.matrix_mul continuous_id).measurable
  have hθ : (gaussianHaarFrameLaw hn).map F = gaussianHaarFrameLaw hn := by
    exact gaussianHaarFrameLaw_map_left hn Qᵀ
      (by rw [transpose_transpose]; exact mul_eq_one_comm.mp hQ)
  have hP : (coordinateSketchProjector J').val =
      Q * (coordinateSketchProjector J).val * Qᵀ := by
    have hProj (I : Fin l ↪ Fin n) :
        (coordinateSketchProjector I).val = (rowSelector I)ᵀ * ((rowSelector I)ᵀ)ᵀ := by
      rw [transpose_transpose]
      rfl
    rw [hProj J', ← he, hProj J]
    simp only [transpose_mul, Matrix.mul_assoc]
  have hf : f ∘ F = g := by
    funext V
    simp only [f, F, g, hP, Function.comp_apply, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  change (gaussianHaarFrameLaw hn).map f = (gaussianHaarFrameLaw hn).map g
  nth_rw 1 [← hθ]
  rw [Measure.map_map (measurable_coordinateCompression J) hF, hf]

/-- At finite gap the laws of the full single-draw errors coincide. -/
theorem coordinateSketch_singleDraw_finite_law_equal (hl : l ≤ n) (hn : 1 < n)
    (J J' : Fin l ↪ Fin n) {Γ : ℝ} (hΓ : 1 ≤ Γ) :
    (gaussianHaarFrameLaw hn.le).map (fun V : Matrix (Fin n) (Fin 1) ℝ =>
      projectorTwoLevelLoss V (coordinateSketchProjector J) Γ) =
    (gaussianHaarFrameLaw hn.le).map (fun V : Matrix (Fin n) (Fin 1) ℝ =>
      projectorTwoLevelLoss V (coordinateSketchProjector J') Γ) := by
  let η := gaussianHaarFrameLaw hn.le
  let f (A : Matrix (Fin 1) (Fin 1) ℝ) :=
    (Γ * ((1 + (Γ - 1) • A)⁻¹).trace - (l : ℝ)) / ((1 : ℝ) * ((n : ℝ) - 1))
  have hF : Measurable f := by
    unfold f
    have hC : Continuous (fun A : Matrix (Fin 1) (Fin 1) ℝ => 1 + (Γ - 1) • A) :=
      continuous_const.add (continuous_id.const_smul (Γ - 1))
    exact (((measurable_matrix_trace.comp (measurable_matrix_nonsing_inv.comp hC.measurable)).const_mul
      Γ).sub_const _).div_const _
  have h (I : Fin l ↪ Fin n) :
      η.map (fun V => projectorTwoLevelLoss V (coordinateSketchProjector I) Γ) =
        (η.map (fun V => Vᵀ * (coordinateSketchProjector I).val * V)).map f := by
    rw [Measure.map_map hF (measurable_coordinateCompression I)]
    apply Measure.map_congr
    filter_upwards [ae_gaussianHaarFrame_orthonormal hn.le] with V hV
    simpa only [Function.comp_apply, orientationFiniteLoss, Nat.cast_one, f] using
      (orientationFiniteLoss_eq_actual (by decide) hn Γ hΓ (coordinateSketchProjector I) V hV).symm
  rw [h J, h J', coordinateSketch_compression_law_equal hl hn.le J J']

/-- The endpoint single-draw laws also coincide for all selectors. -/
theorem coordinateSketch_singleDraw_endpoint_law_equal (hl : l ≤ n) (hn : 1 ≤ n)
    (J J' : Fin l ↪ Fin n) :
    (gaussianHaarFrameLaw hn).map (fun V : Matrix (Fin n) (Fin 1) ℝ =>
      projectorOrientationEndpoint V (coordinateSketchProjector J)) =
    (gaussianHaarFrameLaw hn).map (fun V : Matrix (Fin n) (Fin 1) ℝ =>
      projectorOrientationEndpoint V (coordinateSketchProjector J')) := by
  let η := gaussianHaarFrameLaw hn
  let f (A : Matrix (Fin 1) (Fin 1) ℝ) :=
    (A⁻¹.trace - (l : ℝ)) / ((1 : ℝ) * ((n : ℝ) - 1))
  have hF : Measurable f :=
    ((measurable_matrix_trace.comp measurable_matrix_nonsing_inv).sub_const _).div_const _
  have h (I : Fin l ↪ Fin n) :
      η.map (fun V => projectorOrientationEndpoint V (coordinateSketchProjector I)) =
        (η.map (fun V => Vᵀ * (coordinateSketchProjector I).val * V)).map f := by
    rw [Measure.map_map hF (measurable_coordinateCompression I)]
    apply Measure.map_congr
    exact ae_of_all _ fun V => by simp only [Function.comp_apply, projectorOrientationEndpoint, Nat.cast_one, f]
  rw [h J, h J', coordinateSketch_compression_law_equal hl hn J J']

theorem uniformCoordinateSketch_mean_norm (hn : 0 < n) (hl : l ≤ n) :
    ‖(meanSketchProjector (uniformCoordinateSketchLaw n l)).toEuclideanLin.toContinuousLinearMap‖ =
      (l : ℝ) / n := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [meanSketchProjector_uniformCoordinate hn hl]
  change ‖toEuclideanCLM (𝕜 := ℝ) (((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ))‖ = _
  rw [map_smul, map_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change (l : ℝ) / n * ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ = _
  rw [ContinuousLinearMap.norm_id, mul_one]

/-- The conditional mean of the uniform coordinate sketch converges in L¹
over the Haar target to the inverse chi-square expectation. -/
theorem uniformCoordinateEndpoint_L1 {D : ℕ → ℕ} {p : ℕ} (hp : 2 ≤ p)
    (hD : ∀ i, 1 + p ≤ D i) (hn : Tendsto D atTop atTop) :
    Tendsto (fun i =>
      ∫ V, |haarOrientationEndpoint (k := 1) (uniformCoordinateSketchLaw (D i) (1+p)) V -
        1 / ((p : ℝ) - 1)| ∂gaussianHaarFrameLaw (show 1 ≤ D i by have := hD i; omega))
      atTop (𝓝 0) := by
  let ν (i : ℕ) := uniformCoordinateSketchLaw (D i) (1 + p)
  let η (i : ℕ) := gaussianHaarFrameLaw (show 1 ≤ D i by have := hD i; omega)
  let q := 1 / ((p : ℝ) - 1)
  let h (i : ℕ) := haarOrientationBenchmark (D i) 1 (1+p)
  let e (i : ℕ) := haarOrientationEndpoint (k := 1) (ν i)
  let (i : ℕ) : IsProbabilityMeasure (ν i) := isProbabilityMeasure_uniformCoordinateSketchLaw (hD i)
  have hNorm : Tendsto (fun i => ‖(meanSketchProjector (ν i)).toEuclideanLin.toContinuousLinearMap‖)
      atTop (𝓝 0) := by
    have hd : Tendsto (fun i => ((1+p : ℕ) : ℝ) / D i) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hn)
    exact hd.congr fun i =>
      (uniformCoordinateSketch_mean_norm (show 0 < D i from by have := hD i; omega) (hD i)).symm
  have hL1 : Tendsto (fun i => ∫ V, |e i V - h i| ∂η i) atTop (𝓝 0) :=
    haarOrientationL1_of_diffuse (by decide) hp D hD ν (fun _ => ⊤) tendsto_const_nhds hNorm
  have hR : Tendsto (fun i => (D i : ℝ) - (1 : ℝ)) atTop atTop :=
    by
      simpa only [sub_eq_add_neg, Function.comp_apply] using
        tendsto_atTop_add_const_right atTop (-1 : ℝ) (tendsto_natCast_atTop_atTop.comp hn)
  have hH : Tendsto h atTop (𝓝 q) := by
    apply Cosine.haarOrientationBenchmark_tendsto_window (fun _ => by decide) hp hD
    simpa only [Nat.cast_one] using hR
  have hAbs : Tendsto (fun i => |h i - q|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, sub_self, abs_zero] using
      (hH.sub (tendsto_const_nhds (x := q))).norm
  have hMajor := hL1.add hAbs
  rw [zero_add] at hMajor
  refine squeeze_zero (fun i => integral_nonneg fun _ => abs_nonneg _) (fun i => ?_) hMajor
  have hi : Integrable (e i) (η i) :=
    (haarOrientationEndpoint_mean (hD i) (by decide) (by omega) (ν i)).1
  calc
    _ ≤ ∫ V, |e i V - h i| + |h i - q| ∂η i := by
      exact integral_mono (hi.sub (integrable_const _)).abs
        ((hi.sub (integrable_const _)).abs.add (integrable_const _))
        (fun V => abs_sub_le ..)
    _ = _ := by
      have hI : Integrable (fun V => |e i V - h i|) (η i) :=
        (hi.sub (integrable_const _)).abs
      rw [integral_add hI (integrable_const _)]
      simp

/-- One infinite sequence of independent standard real Gaussians. -/
def infiniteGaussianCoordinateLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure infiniteGaussianCoordinateLaw := by
  unfold infiniteGaussianCoordinateLaw
  infer_instance

def gaussianCoordinatePrefix (d : ℕ) (ω : ℕ → ℝ) : Matrix (Fin d) (Fin 1) ℝ :=
  Matrix.of fun i _ => ω i

private theorem measurable_gaussianCoordinatePrefix (d : ℕ) :
    Measurable (gaussianCoordinatePrefix d) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun _ => ?_
  exact measurable_pi_apply i.val

private theorem gaussianColumn_stdGaussian_pushforward (d : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map
      (fun x => Matrix.of (fun (i : Fin d) (_ : Fin 1) => x i)) = gaussianMatrixLaw d 1 := by
  let F := fun x : EuclideanSpace ℝ (Fin d) => Matrix.of (fun i (_ : Fin 1) => x i)
  have hF : Measurable F := measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun _ =>
    (PiLp.continuous_apply 2 _ i).measurable
  have hEval := measurePreserving_eval (fun _ : Fin 1 => stdGaussian (EuclideanSpace ℝ (Fin d))) 0
  have hEq : matrixOfGaussianColumns (d := d) (k := 1) =
      F ∘ fun X : Fin 1 → EuclideanSpace ℝ (Fin d) => X 0 := by
    funext X
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  change (stdGaussian (EuclideanSpace ℝ (Fin d))).map F = _
  unfold gaussianMatrixLaw gaussianColumnLaw
  rw [hEq, ← Measure.map_map hF hEval.measurable, hEval.map_eq]

/-- Every finite prefix in the infinite coupling has the native iid matrix law. -/
theorem gaussianCoordinatePrefix_law (d : ℕ) :
    infiniteGaussianCoordinateLaw.map (gaussianCoordinatePrefix d) = gaussianMatrixLaw d 1 := by
  let E (x : ℕ → ℝ) (i : Fin d) := x i.val
  let F (x : EuclideanSpace ℝ (Fin d)) := Matrix.of (fun i (_ : Fin 1) => x i)
  have hE : Measurable E := measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hF : Measurable F := measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun _ =>
    (PiLp.continuous_apply 2 _ i).measurable
  have hTo : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
    WithLp.measurable_toLp _ _
  change (infiniteGaussianCoordinateLaw.map (F ∘ (WithLp.toLp 2) ∘ E)) = _
  rw [← Measure.map_map hF (hTo.comp hE), ← Measure.map_map hTo hE]
  rw [show infiniteGaussianCoordinateLaw.map E = Measure.pi (fun _ : Fin d => gaussianReal 0 1) from
    infiniteProduct_map_embedding (gaussianReal 0 1) (Fin.valEmbedding (n := d)),
    map_pi_eq_stdGaussian]
  exact gaussianColumn_stdGaussian_pushforward d

def gaussianCoordinateEnergy (d : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ i : Fin d, (ω i.val)^2

private theorem measurable_gaussianCoordinateEnergy (d : ℕ) :
    Measurable (gaussianCoordinateEnergy d) := by unfold gaussianCoordinateEnergy; fun_prop

theorem gaussianCoordinateEnergy_law (hd : 0 < d) :
    infiniteGaussianCoordinateLaw.map (gaussianCoordinateEnergy d) = chiSquareLaw d := by
  let E (x : ℕ → ℝ) (i : Fin d) := x i.val
  have hE : Measurable E := measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  let F (x : EuclideanSpace ℝ (Fin d)) := ‖x‖ ^ 2
  have hF : Measurable F := by unfold F; fun_prop
  have hTo : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
    WithLp.measurable_toLp _ _
  have he : gaussianCoordinateEnergy d = F ∘ WithLp.toLp 2 ∘ E := by
    funext ω
    simp [F, E, gaussianCoordinateEnergy, EuclideanSpace.real_norm_sq_eq]
  rw [he, ← Measure.map_map hF (hTo.comp hE), ← Measure.map_map hTo hE]
  rw [show infiniteGaussianCoordinateLaw.map E = Measure.pi (fun _ : Fin d => gaussianReal 0 1) from
    infiniteProduct_map_embedding (gaussianReal 0 1) (Fin.valEmbedding (n := d)),
    map_pi_eq_stdGaussian]
  exact stdGaussian_norm_sq_map hd

/-- The normalized total square energy tends to one under the common
infinite coupling, by the strong law applied to the independent squares. -/
theorem gaussianCoordinateEnergy_strongLaw :
    ∀ᵐ ω ∂infiniteGaussianCoordinateLaw,
      Tendsto (fun d => gaussianCoordinateEnergy d ω / (d : ℝ)) atTop (𝓝 1) := by
  let μ := infiniteGaussianCoordinateLaw
  let m := gaussianReal 0 1
  let X (i : ℕ) (ω : ℕ → ℝ) := (ω i)^2
  have hEval (i : ℕ) : MeasurePreserving (fun ω : ℕ → ℝ => ω i) μ m :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => m) i
  have hs : Measurable (fun x : ℝ => x^2) := by fun_prop
  have hX (i : ℕ) : Measurable (X i) := hs.comp (hEval i).measurable
  have hInt : Integrable (X 0) μ :=
    (hEval 0).integrable_comp_of_integrable (standardGaussian_power_integrable 2)
  have hInd : iIndepFun X μ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => m) (X := fun _ : ℕ => fun x : ℝ => x^2) (fun _ => hs)
  have hMap (i : ℕ) : μ.map (X i) = m.map (fun x : ℝ => x^2) := by
    change μ.map ((fun x : ℝ => x^2) ∘ fun ω => ω i) = _
    rw [← Measure.map_map hs (hEval i).measurable, (hEval i).map_eq]
  have hId (i : ℕ) : IdentDistrib (X i) (X 0) μ μ :=
    ⟨(hX i).aemeasurable, (hX 0).aemeasurable, (hMap i).trans (hMap 0).symm⟩
  have hm : (∫ ω, X 0 ω ∂μ) = 1 := by
    calc
      _ = ∫ x, x ^ 2 ∂m := by
        rw [← (hEval 0).map_eq, integral_map (hEval 0).aemeasurable hs.aestronglyMeasurable]
      _ = _ := standardGaussian_second_moment
  have h := strong_law_ae_real X hInt (fun i j hij => hInd.indepFun hij) hId
  rw [hm] at h
  filter_upwards [h] with ω hω
  apply hω.congr
  intro d
  unfold X gaussianCoordinateEnergy
  rw [Fin.sum_univ_eq_sum_range (fun j => (ω j)^2)]

/-- The exact fixed-coordinate endpoint evaluated on the common Gaussian
sequence. This representation keeps the numerator energy fixed as dimension grows. -/
def coupledFixedCoordinateEndpoint (l d : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (gaussianCoordinateEnergy d ω / gaussianCoordinateEnergy l ω - (l : ℝ)) / ((d : ℝ) - 1)

private theorem measurable_coupledFixedCoordinateEndpoint (l d : ℕ) :
    Measurable (coupledFixedCoordinateEndpoint l d) :=
  (((measurable_gaussianCoordinateEnergy d).div (measurable_gaussianCoordinateEnergy l)).sub_const _).div_const _

/-- The fixed-coordinate endpoint converges almost surely in the specific
infinite Gaussian coupling used in Example 3.1. -/
theorem coupledFixedCoordinateEndpoint_ae_tendsto {D : ℕ → ℕ} (hD : ∀ i, l ≤ D i)
    (hn : Tendsto D atTop atTop) (hl : 2 < l) :
    ∀ᵐ ω ∂infiniteGaussianCoordinateLaw,
      Tendsto (fun i => coupledFixedCoordinateEndpoint l (D i) ω) atTop
        (𝓝 (gaussianCoordinateEnergy l ω)⁻¹) := by
  have hAE : ∀ᵐ ω ∂infiniteGaussianCoordinateLaw, 0 < gaussianCoordinateEnergy l ω := by
    apply (ae_map_iff (measurable_gaussianCoordinateEnergy l).aemeasurable
      (measurableSet_lt measurable_const measurable_id)).mp
    rw [gaussianCoordinateEnergy_law (by omega : 0 < l)]
    exact ae_chiSquare_pos l
  have H : Tendsto (fun i => (D i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hnInv := H.inv_tendsto_atTop
  have hlInv : Tendsto (fun i => (l : ℝ) / (D i : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop H
  filter_upwards [gaussianCoordinateEnergy_strongLaw, hAE] with ω hω hpos
  let S := gaussianCoordinateEnergy l ω
  have hAs : Tendsto (fun i => gaussianCoordinateEnergy (D i) ω / (D i : ℝ))
      atTop (𝓝 1) := hω.comp hn
  have hNum := (hAs.div_const S).sub hlInv
  have hDen : Tendsto (fun i => 1 - (D i : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero, Pi.inv_apply] using hnInv.const_sub 1
  have hAll := hNum.div hDen one_ne_zero
  simp only [sub_zero, div_one, one_div] at hAll
  refine hAll.congr (fun i => ?_)
  have hNi : (D i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hD i; omega)
  have hd : (D i : ℝ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast (show D i ≠ 1 by have := hD i; omega))
  change (gaussianCoordinateEnergy (D i) ω / (D i : ℝ) / S - (l : ℝ) / (D i : ℝ)) /
      (1 - (D i : ℝ)⁻¹) = (gaussianCoordinateEnergy (D i) ω / S - (l : ℝ)) / ((D i : ℝ) - 1)
  field_simp [hNi, hd, hpos.ne']

/-- The inverse chi-square probability law with the original degrees of freedom. -/
def inverseChiSquareProbabilityLaw (hl : 0 < l) : ProbabilityMeasure ℝ := by
  have : IsProbabilityMeasure (chiSquareLaw l) :=
    isProbabilityMeasure_gammaMeasure (div_pos (Nat.cast_pos.mpr hl) (by norm_num)) (by norm_num)
  have hInv : Measurable (fun x : ℝ => x⁻¹) := by fun_prop
  exact ⟨(chiSquareLaw l).map (fun x => x⁻¹), Measure.isProbabilityMeasure_map hInv.aemeasurable⟩

def fixedCoordinateEndpointLaw (hl : l ≤ n) (hn : 1 ≤ n) : ProbabilityMeasure ℝ :=
  ⟨(gaussianHaarFrameLaw hn).map (haarOrientationEndpoint (fixedCoordinateSketchLaw hl)),
    Measure.isProbabilityMeasure_map
      (measurable_haarOrientationEndpoint (fixedCoordinateSketchLaw hl)).aemeasurable⟩

private theorem coupledFixedCoordinateEndpoint_law (hl : l ≤ n) (hn : 1 ≤ n) :
    infiniteGaussianCoordinateLaw.map (coupledFixedCoordinateEndpoint l n) =
      (fixedCoordinateEndpointLaw hl hn : Measure ℝ) := by
  let E := haarOrientationEndpoint (k := 1) (fixedCoordinateSketchLaw hl)
  have hE : Measurable E := measurable_haarOrientationEndpoint _
  have hEq : coupledFixedCoordinateEndpoint l n = E ∘ gaussianPolarFrame ∘ gaussianCoordinatePrefix n := by
    funext ω
    simp only [Function.comp_apply, E, fixedCoordinateEndpoint_eq, coupledFixedCoordinateEndpoint,
      gaussianCoordinateEnergy, gaussianCoordinatePrefix, Matrix.of_apply, Fin.castLEEmb_apply, Fin.val_castLE]
  change _ = (gaussianHaarFrameLaw hn).map E
  rw [hEq, ← Measure.map_map hE (measurable_gaussianPolarFrame.comp (measurable_gaussianCoordinatePrefix n)),
    ← Measure.map_map measurable_gaussianPolarFrame (measurable_gaussianCoordinatePrefix n),
    gaussianCoordinatePrefix_law, gaussianPolarFrameLaw_eq_haar]

/-- With the same Haar-target law as the finite sketch, a fixed selector's
conditional mean tends in distribution to the inverse chi-square law. -/
theorem fixedCoordinateEndpoint_tendsto_law {D : ℕ → ℕ} (hD : ∀ i, l ≤ D i)
    (hn : Tendsto D atTop atTop) (hl : 2 < l) :
    Tendsto (fun i => fixedCoordinateEndpointLaw (hD i) (show 1 ≤ D i by have := hD i; omega))
      atTop (𝓝 (inverseChiSquareProbabilityLaw (show 0 < l by omega))) := by
  have hM : Measurable (fun ω : ℕ → ℝ => (gaussianCoordinateEnergy l ω)⁻¹) :=
    (measurable_gaussianCoordinateEnergy l).inv
  have hLaw := (tendstoInDistribution_of_ae_tendsto
    (fun i => (measurable_coupledFixedCoordinateEndpoint l (D i)).aemeasurable) hM.aemeasurable
    (coupledFixedCoordinateEndpoint_ae_tendsto hD hn hl)).tendsto
  have hInv : infiniteGaussianCoordinateLaw.map (fun ω => (gaussianCoordinateEnergy l ω)⁻¹) =
      (inverseChiSquareProbabilityLaw (show 0 < l by omega) : Measure ℝ) := by
    change (infiniteGaussianCoordinateLaw.map ((fun x : ℝ => x⁻¹) ∘ gaussianCoordinateEnergy l)) =
      (chiSquareLaw l).map (fun x => x⁻¹)
    have hh : Measurable (fun x : ℝ => x⁻¹) := by fun_prop
    rw [← Measure.map_map hh (measurable_gaussianCoordinateEnergy l),
      gaussianCoordinateEnergy_law (by omega : 0 < l)]
  rw [show (⟨_, _⟩ : ProbabilityMeasure ℝ) = inverseChiSquareProbabilityLaw (show 0 < l by omega) from
    Subtype.ext hInv] at hLaw
  exact hLaw.congr (fun i => Subtype.ext (coupledFixedCoordinateEndpoint_law (hD i) _))

/-- The limiting inverse chi-square mean is exactly the Haar benchmark limit. -/
theorem inverseChiSquareProbabilityLaw_mean (hl : 2 < l) :
    (∫ x, x ∂(inverseChiSquareProbabilityLaw (show 0 < l by omega) : Measure ℝ)) =
      1 / ((l : ℝ) - 2) := by
  change (∫ x, x ∂(chiSquareLaw l).map (fun x : ℝ => x⁻¹)) = _
  have hInv : Measurable (fun x : ℝ => x⁻¹) := by fun_prop
  have hid : Measurable (fun x : ℝ => x) := measurable_id
  rw [integral_map hInv.aemeasurable hid.aestronglyMeasurable]
  exact (chiSquare_inverse_mean hl).2

/-- The fixed selector's limiting law has zero mass on every singleton. -/
theorem inverseChiSquareProbabilityLaw_no_atoms (hl : 0 < l) (a : ℝ) :
    (inverseChiSquareProbabilityLaw hl : Measure ℝ) {a} = 0 := by
  change ((chiSquareLaw l).map (fun x : ℝ => x⁻¹)) {a} = 0
  have hInv : Measurable (fun x : ℝ => x⁻¹) := by fun_prop
  rw [Measure.map_apply hInv (measurableSet_singleton _)]
  have hEq : (fun x : ℝ => x⁻¹) ⁻¹' {a} = {a⁻¹} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      rw [← hx, inv_inv]
    · intro hx
      rw [hx, inv_inv]
  rw [hEq]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton _)

private theorem map_product_fibers {A X Y : Type*}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure A) (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × X → Y} (hF : Measurable F) (h : ∀ a, μ.map (fun x => F (a,x)) = ν) :
    (ρ.prod μ).map (fun z => (z.1, F z)) = ρ.prod ν := by
  let f (z : A × X) := (z.1, F z)
  have hf : Measurable f := measurable_fst.prodMk hF
  ext S hS
  rw [Measure.map_apply hf hS, Measure.prod_apply (hf hS), Measure.prod_apply hS]
  apply lintegral_congr
  intro a
  have hm : Measurable (fun x => F (a,x)) := hF.comp measurable_prodMk_left
  rw [← h a, Measure.map_apply hm (measurable_prodMk_left hS)]
  rfl

/-- The selector is independent of the Gaussian readout under the exact
finite uniform-subset draw. This identifies every conditional readout law. -/
theorem uniformCoordinate_readout_joint :
    ((uniformCoordinateSubsetLaw n l).prod (gaussianMatrixLaw n 1)).map
      (fun z => (z.1, z.2.submatrix (coordinateSubsetEmbedding z.1) id)) =
      (uniformCoordinateSubsetLaw n l).prod (gaussianMatrixLaw l 1) := by
  apply map_product_fibers
  · apply measurable_from_prod_countable_right
    intro s
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    exact (continuous_id.matrix_elem (coordinateSubsetEmbedding s i) j).measurable
  · exact fun s => coordinateSketch_readout_law (coordinateSubsetEmbedding s)

private theorem marginal_map_product_fibers {A X Y : Type*}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure A) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × X → Y} (hF : Measurable F) (h : ∀ a, μ.map (fun x => F (a,x)) = ν) :
    (ρ.prod μ).map F = ν := by
  have hJoint := map_product_fibers ρ μ ν hF h
  have hS := congrArg (Measure.map Prod.snd) hJoint
  rw [Measure.map_map measurable_snd (measurable_fst.prodMk hF), Measure.map_snd_prod,
    measure_univ, one_smul] at hS
  exact hS

/-- For a freshly drawn Haar target, a uniform coordinate selector gives
the same endpoint law as the fixed selector's single-draw error. -/
theorem uniformCoordinate_singleDraw_endpoint_law (hl : l ≤ n) (hn : 1 ≤ n) :
    ((uniformCoordinateSubsetLaw n l).prod (gaussianHaarFrameLaw hn)).map
      (fun z => projectorOrientationEndpoint z.2
        (coordinateSketchProjector (coordinateSubsetEmbedding z.1))) =
    (gaussianHaarFrameLaw hn).map (fun V : Matrix (Fin n) (Fin 1) ℝ =>
      projectorOrientationEndpoint V (coordinateSketchProjector (Fin.castLEEmb hl))) := by
  let η := gaussianHaarFrameLaw hn
  let ν := η.map (fun V : Matrix (Fin n) (Fin 1) ℝ => projectorOrientationEndpoint V
    (coordinateSketchProjector (Fin.castLEEmb hl)))
  let F (z : CoordinateSubset n l × Matrix (Fin n) (Fin 1) ℝ) :=
    projectorOrientationEndpoint z.2 (coordinateSketchProjector (coordinateSubsetEmbedding z.1))
  have : Nonempty (CoordinateSubset n l) := nonempty_coordinateSubset hl
  have : IsProbabilityMeasure (uniformCoordinateSubsetLaw n l) := inferInstanceAs
    (IsProbabilityMeasure (finiteLaw (id : CoordinateSubset n l → CoordinateSubset n l)))
  have hFun (J : Fin l ↪ Fin n) :
      Measurable (fun V : Matrix (Fin n) (Fin 1) ℝ =>
        projectorOrientationEndpoint V (coordinateSketchProjector J)) := by
    unfold projectorOrientationEndpoint
    exact (((measurable_matrix_trace.comp measurable_matrix_nonsing_inv).comp
      (measurable_coordinateCompression J)).sub_const _).div_const _
  have : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (hFun _).aemeasurable
  exact marginal_map_product_fibers _ η ν (measurable_from_prod_countable_right
    (fun s => hFun (coordinateSubsetEmbedding s))) (fun s =>
      coordinateSketch_singleDraw_endpoint_law_equal hl hn (coordinateSubsetEmbedding s) _)

/-- For a freshly drawn Haar target, a uniform coordinate selector gives
the same actual finite-gap single-draw error law as the fixed selector. -/
theorem uniformCoordinate_singleDraw_finite_law (hl : l ≤ n) (hn : 1 < n)
    {Γ : ℝ} (hΓ : 1 ≤ Γ) :
    ((uniformCoordinateSubsetLaw n l).prod (gaussianHaarFrameLaw hn.le)).map
      (fun z => projectorTwoLevelLoss z.2 (coordinateSketchProjector (coordinateSubsetEmbedding z.1)) Γ) =
    (gaussianHaarFrameLaw hn.le).map (fun V : Matrix (Fin n) (Fin 1) ℝ =>
      projectorTwoLevelLoss V (coordinateSketchProjector (Fin.castLEEmb hl)) Γ) := by
  let η := gaussianHaarFrameLaw hn.le
  let τ := uniformCoordinateSubsetLaw n l
  let F (z : CoordinateSubset n l × Matrix (Fin n) (Fin 1) ℝ) :=
    orientationFiniteLoss Γ (coordinateSketchProjector (coordinateSubsetEmbedding z.1)) z.2
  let f (V : Matrix (Fin n) (Fin 1) ℝ) := orientationFiniteLoss Γ
    (coordinateSketchProjector (Fin.castLEEmb hl)) V
  let ν := η.map f
  have : Nonempty (CoordinateSubset n l) := nonempty_coordinateSubset hl
  have : IsProbabilityMeasure τ := inferInstanceAs
    (IsProbabilityMeasure (finiteLaw (id : CoordinateSubset n l → CoordinateSubset n l)))
  have hMeas (J : Fin l ↪ Fin n) : Measurable (fun V : Matrix (Fin n) (Fin 1) ℝ =>
      orientationFiniteLoss Γ (coordinateSketchProjector J) V) := by
    have hP : Measurable (fun V : Matrix (Fin n) (Fin 1) ℝ => (coordinateSketchProjector J, V)) :=
      measurable_const.prodMk measurable_id
    simpa only [Function.uncurry_def, Function.comp_def] using
      (@measurable_orientationFiniteLoss n 1 l Γ).comp hP
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (hMeas _).aemeasurable
  have heq (J : Fin l ↪ Fin n) :
      η.map (fun V : Matrix (Fin n) (Fin 1) ℝ => orientationFiniteLoss Γ (coordinateSketchProjector J) V) =
      η.map (fun V : Matrix (Fin n) (Fin 1) ℝ => projectorTwoLevelLoss V (coordinateSketchProjector J) Γ) := by
    apply Measure.map_congr
    filter_upwards [ae_gaussianHaarFrame_orthonormal hn.le] with V hV
    exact orientationFiniteLoss_eq_actual (by decide) hn Γ hΓ _ V hV
  have hprod : (τ.prod η).map F = ν := by
    apply marginal_map_product_fibers τ η ν (measurable_from_prod_countable_right
      (fun s => hMeas (coordinateSubsetEmbedding s)))
    intro s
    change η.map (fun V => orientationFiniteLoss Γ
      (coordinateSketchProjector (coordinateSubsetEmbedding s)) V) =
      η.map (fun V => orientationFiniteLoss Γ (coordinateSketchProjector (Fin.castLEEmb hl)) V)
    rw [heq, heq]
    exact coordinateSketch_singleDraw_finite_law_equal hl hn _ _ hΓ
  have hAE : ∀ᵐ z : CoordinateSubset n l × Matrix (Fin n) (Fin 1) ℝ ∂(τ.prod η), z.2ᵀ * z.2 = 1 := by
    have hBase : MeasurableSet {U : Matrix (Fin n) (Fin 1) ℝ | Uᵀ * U = 1} :=
      (isClosed_singleton.preimage (continuous_id.matrix_transpose.matrix_mul continuous_id)).measurableSet
    have hm : MeasurableSet {z : CoordinateSubset n l × Matrix (Fin n) (Fin 1) ℝ | z.2ᵀ * z.2 = 1} :=
      hBase.preimage measurable_snd
    exact (Measure.ae_prod_iff_ae_ae hm).2 (ae_of_all _ fun _ => ae_gaussianHaarFrame_orthonormal hn.le)
  have he : (τ.prod η).map (fun z => projectorTwoLevelLoss z.2
      (coordinateSketchProjector (coordinateSubsetEmbedding z.1)) Γ) = (τ.prod η).map F := by
    apply Measure.map_congr
    filter_upwards [hAE] with z hz
    exact (orientationFiniteLoss_eq_actual (by decide) hn Γ hΓ _ z.2 hz).symm
  rw [he, hprod]
  exact heq (Fin.castLEEmb hl)

/-- The exact endpoint means agree for the two selector laws after
averaging over the target, even before taking the dimension limit. -/
theorem coordinateSketch_endpoint_means_eq_benchmark (hl : l ≤ n) (hℓ : 2 < l) :
    (∫ V, haarOrientationEndpoint (k := 1) (fixedCoordinateSketchLaw hl) V
        ∂gaussianHaarFrameLaw (show 1 ≤ n by omega)) = haarOrientationBenchmark n 1 l ∧
    (∫ V, haarOrientationEndpoint (k := 1) (uniformCoordinateSketchLaw n l) V
        ∂gaussianHaarFrameLaw (show 1 ≤ n by omega)) = haarOrientationBenchmark n 1 l := by
  have : IsProbabilityMeasure (uniformCoordinateSketchLaw n l) :=
    isProbabilityMeasure_uniformCoordinateSketchLaw hl
  exact ⟨(haarOrientationEndpoint_mean hl (by decide) hℓ (fixedCoordinateSketchLaw hl)).2,
    (haarOrientationEndpoint_mean hl (by decide) hℓ (uniformCoordinateSketchLaw n l)).2⟩

/-- The different conditional mean limits of Example 3.1. The fixed
selector has a non-atomic limiting law, while the uniform selector tends
to the same law's expectation in L¹. -/
theorem example_3_1 {D : ℕ → ℕ} (hD : ∀ i, l ≤ D i) (hn : Tendsto D atTop atTop) (hl : 2 < l) :
    Tendsto (fun i => fixedCoordinateEndpointLaw (hD i) (show 1 ≤ D i by have := hD i; omega))
      atTop (𝓝 (inverseChiSquareProbabilityLaw (show 0 < l by omega))) ∧
    Tendsto (fun i =>
      ∫ V, |haarOrientationEndpoint (k := 1) (uniformCoordinateSketchLaw (D i) l) V -
        1 / ((l : ℝ) - 2)| ∂gaussianHaarFrameLaw (show 1 ≤ D i by have := hD i; omega))
      atTop (𝓝 0) ∧
    (∫ x, x ∂(inverseChiSquareProbabilityLaw (show 0 < l by omega) : Measure ℝ)) =
      1 / ((l : ℝ) - 2) ∧
    (∀ a : ℝ, (inverseChiSquareProbabilityLaw (show 0 < l by omega) : Measure ℝ) {a} = 0) := by
  refine ⟨fixedCoordinateEndpoint_tendsto_law hD hn hl, ?_,
    inverseChiSquareProbabilityLaw_mean hl, inverseChiSquareProbabilityLaw_no_atoms (by omega)⟩
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ l by omega)
  have hp : 2 ≤ p := by omega
  have hq : 1 / (((1 + p : ℕ) : ℝ) - 2) = 1 / ((p : ℝ) - 1) := by
    congr 1
    push_cast
    ring
  rw [hq]
  exact uniformCoordinateEndpoint_L1 hp hD hn

end

end SketchOrientation
