import SketchOrientation.CoordinateOrientationExample
import SketchOrientation.ProjectorOverlap
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation
open scoped ENNReal

noncomputable section

variable {n l : ℕ}

/-- The orthogonal transforms in Corollary 4.1, with their Borel structure. -/
abbrev OrthogonalTransform (n : ℕ) :=
  {O : Matrix (Fin n) (Fin n) ℝ // Oᵀ * O = 1}

/-- The sampled rows, written as columns. -/
def sampledRowFrame (O : OrthogonalTransform n) (J : CoordinateSubset n l) :
    Matrix (Fin n) (Fin l) ℝ :=
  (rowSelector (coordinateSubsetEmbedding J) * O.val)ᵀ

private theorem sampledRowFrame_orthonormal (O : OrthogonalTransform n)
    (J : CoordinateSubset n l) :
    (sampledRowFrame O J)ᵀ * sampledRowFrame O J = 1 := by
  simp only [sampledRowFrame, transpose_transpose, transpose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc O.val,
    mul_eq_one_comm.mp O.property, Matrix.one_mul, rowSelector_orthonormal]

/-- The projector onto the sampled rows of the orthogonal transform. -/
def orthogonalRowProjector (O : OrthogonalTransform n) (J : CoordinateSubset n l) :
    OrthogonalProjector n l :=
  let B := sampledRowFrame O J
  have hB := sampledRowFrame_orthonormal O J
  ⟨B * Bᵀ, by simp, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Bᵀ, hB, Matrix.one_mul],
    by rw [Matrix.rank_self_mul_transpose, ← Matrix.rank_transpose_mul_self, hB,
      Matrix.rank_one, Fintype.card_fin]⟩

theorem orthogonalRowProjector_eq_rangeProjector (O : OrthogonalTransform n)
    (J : CoordinateSubset n l) :
    (orthogonalRowProjector O J).val = rangeProjector (sampledRowFrame O J) :=
  (rangeProjector_of_frame _ (sampledRowFrame_orthonormal O J)).symm

def rowInclusionDiagonal (J : CoordinateSubset n l) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => if i ∈ J.val then 1 else 0)

private theorem rowSelector_gram_eq_inclusionDiagonal (J : CoordinateSubset n l) :
    (rowSelector (coordinateSubsetEmbedding J))ᵀ * rowSelector (coordinateSubsetEmbedding J) =
      rowInclusionDiagonal J := by
  classical
  let e := coordinateSubsetEmbedding J
  have hRange : Set.range e = (J.val : Set (Fin n)) :=
    Finset.range_orderEmbOfFin J.val J.property
  ext i j
  change (∑ a, (if e a = i then (1 : ℝ) else 0) * (if e a = j then 1 else 0)) =
    diagonal (fun i => if i ∈ J.val then (1 : ℝ) else 0) i j
  by_cases hij : i = j
  · subst j
    rw [diagonal_apply_eq]
    by_cases hi : i ∈ J.val
    · obtain ⟨a, rfl⟩ : i ∈ Set.range e := by rwa [hRange]
      simp [hi, e.injective.eq_iff]
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun a _ => ?_
      have h : e a ≠ i := by
        intro ha
        exact hi (show i ∈ (J.val : Set (Fin n)) from hRange ▸ ⟨a, ha⟩)
      simp [h]
  · rw [diagonal_apply_ne _ hij]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases h : e a = i
    · simp [h, hij]
    · simp [h]

theorem orthogonalRowProjector_val (O : OrthogonalTransform n) (J : CoordinateSubset n l) :
    (orthogonalRowProjector O J).val = O.valᵀ * rowInclusionDiagonal J * O.val := by
  change sampledRowFrame O J * (sampledRowFrame O J)ᵀ = _
  rw [sampledRowFrame, transpose_mul, transpose_mul, transpose_transpose,
    transpose_transpose, ← rowSelector_gram_eq_inclusionDiagonal]
  simp only [Matrix.mul_assoc]

theorem measurable_orthogonalRowProjector :
    Measurable (fun z : OrthogonalTransform n × CoordinateSubset n l =>
      orthogonalRowProjector z.1 z.2) := by
  apply Measurable.subtype_mk
  change Measurable (fun z : OrthogonalTransform n × CoordinateSubset n l =>
    (orthogonalRowProjector z.1 z.2).val)
  simp_rw [orthogonalRowProjector_val]
  have hO : Measurable (fun z : OrthogonalTransform n × CoordinateSubset n l =>
      z.1.val) := measurable_subtype_coe.comp measurable_fst
  have hJ : Measurable (rowInclusionDiagonal (n := n) (l := l)) :=
    Measurable.of_discrete
  exact measurable_matrix_product
    (measurable_matrix_product (measurable_matrix_transpose hO) (hJ.comp measurable_snd)) hO

/-- Equation (4.1) at a fixed transform. Only the marginal inclusion probabilities matter. -/
theorem orthogonalRows_conditional_entry (O : OrthogonalTransform n)
    (μ : Measure (CoordinateSubset n l)) [IsProbabilityMeasure μ]
    (hIncl : ∀ i : Fin n, μ.real {J | i ∈ J.val} = (l : ℝ) / n) (a b : Fin n) :
    (∫ J, (orthogonalRowProjector O J).val a b ∂μ) =
      (((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) a b := by
  classical
  let F (i : Fin n) (J : CoordinateSubset n l) : ℝ := if i ∈ J.val then 1 else 0
  have hF (i : Fin n) : Integrable (F i) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) Measurable.of_discrete.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun J => by by_cases h : i ∈ J.val <;> simp [F, h]
  have hInt (i : Fin n) : (∫ J, F i J ∂μ) = (l : ℝ) / n := by
    have hm : MeasurableSet {J : CoordinateSubset n l | i ∈ J.val} := MeasurableSet.of_discrete
    calc
      (∫ J, F i J ∂μ) = ∫ J, ({J : CoordinateSubset n l | i ∈ J.val}).indicator
          (fun _ => (1 : ℝ)) J ∂μ := by
        congr 1
        ext J
        by_cases h : i ∈ J.val <;> simp [F, h]
      _ = μ.real {J | i ∈ J.val} := by rw [integral_indicator hm]; simp
      _ = (l : ℝ) / n := hIncl i
  have hExp (J : CoordinateSubset n l) :
      (orthogonalRowProjector O J).val a b = ∑ i, O.val i a * (F i J * O.val i b) := by
    rw [orthogonalRowProjector_val, Matrix.mul_assoc, Matrix.mul_apply]
    simp [rowInclusionDiagonal, F]
  simp_rw [hExp]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_mul_const, hInt]
    have he : (∑ i, O.val i a * ((l : ℝ) / n * O.val i b)) =
        ((l : ℝ) / n) * (O.valᵀ * O.val) a b := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.transpose_apply]
      ring
    rw [he, O.property, Matrix.smul_apply, smul_eq_mul]
  · intro i _
    exact ((hF i).mul_const _).const_mul _

/-- Corollary 4.1's mean identity for arbitrary random transforms. The row law
is conditional on the transform and may vary with it. -/
theorem meanSketchProjector_orthogonalRows (μ : Measure (OrthogonalTransform n))
    [IsProbabilityMeasure μ] (κ : Kernel (OrthogonalTransform n) (CoordinateSubset n l))
    [IsMarkovKernel κ]
    (hIncl : ∀ᵐ O ∂μ, ∀ i : Fin n, (κ O).real {J | i ∈ J.val} = (l : ℝ) / n) :
    meanSketchProjector ((μ ⊗ₘ κ).map
      (fun z => orthogonalRowProjector z.1 z.2)) =
      ((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  let f := fun z : OrthogonalTransform n × CoordinateSubset n l => orthogonalRowProjector z.1 z.2
  have hf : Measurable f := measurable_orthogonalRowProjector
  let : IsProbabilityMeasure ((μ ⊗ₘ κ).map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  ext a b
  change (∫ P, P.val a b ∂(μ ⊗ₘ κ).map f) = _
  have hm : Measurable (fun P : OrthogonalProjector n l => P.val a b) :=
    (continuous_id.matrix_elem a b).measurable.comp measurable_subtype_coe
  have hi : Integrable (fun z => (f z).val a b) (μ ⊗ₘ κ) :=
    (integrable_sketchProjector_entry ((μ ⊗ₘ κ).map f) a b).comp_measurable hf
  rw [integral_map hf.aemeasurable hm.aestronglyMeasurable, Measure.integral_compProd hi]
  calc
    (∫ O, ∫ J, (orthogonalRowProjector O J).val a b ∂κ O ∂μ) =
        ∫ _ : OrthogonalTransform n, (((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) a b ∂μ :=
      integral_congr_ae (by
        filter_upwards [hIncl] with O hO
        exact orthogonalRows_conditional_entry O (κ O) hO a b)
    _ = _ := by simp

/-- The conditional-row argument also applies when one starts from a joint law. -/
theorem meanSketchProjector_orthogonalRows_joint (hl : l ≤ n)
    (joint : Measure (OrthogonalTransform n × CoordinateSubset n l))
    [IsProbabilityMeasure joint] :
    let _ : Nonempty (CoordinateSubset n l) :=
      ⟨⟨Finset.univ.map (Fin.castLEEmb hl), by simp⟩⟩
    (∀ᵐ O ∂joint.fst, ∀ i : Fin n,
      (joint.condKernel O).real {J | i ∈ J.val} = (l : ℝ) / n) →
    meanSketchProjector (joint.map (fun z => orthogonalRowProjector z.1 z.2)) =
      ((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro hNonempty hIncl
  let : Nonempty (CoordinateSubset n l) := hNonempty
  simpa only [joint.disintegrate joint.condKernel] using
    meanSketchProjector_orthogonalRows joint.fst joint.condKernel hIncl

private theorem meanProjector_entry_eq_of_conjugation
    (ν : Measure (OrthogonalProjector n l)) (S : Matrix (Fin n) (Fin n) ℝ)
    (hInvariant : (ν.map fun P => S * P.val * Sᵀ) = ν.map Subtype.val)
    (i j : Fin n) :
    (∫ P, (S * P.val * Sᵀ) i j ∂ν) = (meanSketchProjector ν) i j := by
  let e := fun P : Matrix (Fin n) (Fin n) ℝ => P i j
  let T := fun P : OrthogonalProjector n l => S * P.val * Sᵀ
  have he : Measurable e := (continuous_id.matrix_elem i j).measurable
  have hT : Measurable T := measurable_matrix_product
    (measurable_matrix_product measurable_const measurable_subtype_coe) measurable_const
  calc
    (∫ P, e (T P) ∂ν) = ∫ P, e P ∂ν.map T :=
      (integral_map hT.aemeasurable he.aestronglyMeasurable).symm
    _ = ∫ P : OrthogonalProjector n l, e P.val ∂ν := by
      rw [show ν.map T = ν.map Subtype.val from hInvariant,
        integral_map measurable_subtype_coe.aemeasurable he.aestronglyMeasurable]
    _ = _ := rfl

private theorem permMatrix_conjugation_entry (π : Equiv.Perm (Fin n))
    (P : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (π.permMatrix ℝ * P * (π.permMatrix ℝ)ᵀ) i j = P (π i) (π j) := by
  let S := π.permMatrix ℝ
  have hLeft (a b : Fin n) : (S * P) a b = P (π a) b := by
    change (π.permMatrix ℝ *ᵥ fun r => P r b) a = _
    rw [Matrix.permMatrix_mulVec]
    rfl
  change ((S * P) * Sᵀ) i j = _
  rw [show Sᵀ = (π⁻¹).permMatrix ℝ from Matrix.transpose_permMatrix π]
  change ((fun r => (S * P) i r) ᵥ* (π⁻¹).permMatrix ℝ) j = _
  rw [Matrix.vecMul_permMatrix]
  simpa only [Function.comp_apply, Equiv.Perm.inv_def, Equiv.symm_symm] using hLeft i (π j)

/-- The projector-mean identity in Corollary 4.2. The input is the law of the
full-column-rank sketch's column space, represented by its rank-l projector.
The hypotheses are conjugation by actual diagonal signs and actual
coordinate permutation matrices. -/
theorem meanSketchProjector_of_signed_permutation_symmetry (hn : 0 < n)
    (ν : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure ν]
    (hSign : ∀ s : Fin n → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
      (ν.map fun P => diagonal s * P.val * (diagonal s)ᵀ) = ν.map Subtype.val)
    (hPerm : ∀ π : Equiv.Perm (Fin n),
      (ν.map fun P => π.permMatrix ℝ * P.val * (π.permMatrix ℝ)ᵀ) = ν.map Subtype.val) :
    meanSketchProjector ν = ((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  let M := meanSketchProjector ν
  have hOff (i j : Fin n) (hij : i ≠ j) : M i j = 0 := by
    let s : Fin n → ℝ := fun a => if a = i then -1 else 1
    have hs (a : Fin n) : s a = 1 ∨ s a = -1 := by by_cases ha : a = i <;> simp [s, ha]
    have he := meanProjector_entry_eq_of_conjugation ν (diagonal s) (hSign s hs) i j
    have hEntry (P : OrthogonalProjector n l) :
        (diagonal s * P.val * (diagonal s)ᵀ) i j = -(P.val i j) := by
      simp [s, diagonal_transpose, Ne.symm hij]
    simp_rw [hEntry, integral_neg] at he
    change -(M i j) = M i j at he
    linarith
  have hSame (i j : Fin n) : M i i = M j j := by
    let π := Equiv.swap i j
    have he := meanProjector_entry_eq_of_conjugation ν (π.permMatrix ℝ) (hPerm π) i i
    simp only [permMatrix_conjugation_entry, π, Equiv.swap_apply_left] at he
    exact he.symm
  have hDiag (i : Fin n) : M i i = (l : ℝ) / n := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hn.ne')).2
    calc
      M i i * n = ∑ _j : Fin n, M i i := by simp [mul_comm]
      _ = ∑ j : Fin n, M j j := Finset.sum_congr rfl fun j _ => hSame i j
      _ = l := trace_meanSketchProjector ν
  ext i j
  change M i j = _
  by_cases h : i = j
  · subst j
    simpa [Matrix.one_apply] using hDiag i
  · simp [h, hOff i j h]

/-- A scalar isotropic mean has exactly the diffuseness parameter l/n. -/
theorem meanSketchProjector_norm_of_isotropic (hn : 0 < n)
    (ν : Measure (OrthogonalProjector n l))
    (hν : meanSketchProjector ν = ((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    ‖(meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap‖ = (l : ℝ) / n := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [hν]
  change ‖toEuclideanCLM (𝕜 := ℝ) (((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ))‖ = _
  rw [map_smul, map_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change (l : ℝ) / n * ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ = _
  rw [ContinuousLinearMap.norm_id, mul_one]

private theorem rank_rangeProjector (Y : Matrix (Fin n) (Fin l) ℝ) :
    (rangeProjector Y).rank = Y.rank := by
  apply Nat.cast_injective (R := ℝ)
  rw [← trace_rangeProjector Y, ← trace_rangeProjector (rangeProjector Y),
    rangeProjector_of_projector _ (rangeProjector_transpose Y) (rangeProjector_mul_self Y)]

/-- The range projector of a full-rank matrix has rank l. The value off that
event is an arbitrary coordinate projector, used only to define a total map. -/
def fullRankColumnProjector (hl : l ≤ n) (Y : Matrix (Fin n) (Fin l) ℝ) :
    OrthogonalProjector n l :=
  if hY : (Yᵀ * Y).det ≠ 0 then
    ⟨rangeProjector Y, rangeProjector_transpose Y, rangeProjector_mul_self Y, by
      rw [rank_rangeProjector, ← Matrix.rank_transpose_mul_self]
      simpa using Matrix.rank_of_det_ne_zero hY⟩
  else coordinateSketchProjector (Fin.castLEEmb hl)

theorem fullRankColumnProjector_val (hl : l ≤ n) (Y : Matrix (Fin n) (Fin l) ℝ)
    (hY : (Yᵀ * Y).det ≠ 0) :
    (fullRankColumnProjector hl Y).val = rangeProjector Y := by
  rw [fullRankColumnProjector, dif_pos hY]

theorem measurable_fullRankColumnProjector (hl : l ≤ n) :
    Measurable (fullRankColumnProjector hl) := by
  apply Measurable.subtype_mk
  change Measurable (fun Y : Matrix (Fin n) (Fin l) ℝ => (fullRankColumnProjector hl Y).val)
  let s : Set (Matrix (Fin n) (Fin l) ℝ) := {Y | (Yᵀ * Y).det ≠ 0}
  let D : Matrix (Fin n) (Fin n) ℝ := (coordinateSketchProjector (Fin.castLEEmb hl)).val
  let f := fun Y : Matrix (Fin n) (Fin l) ℝ => Y * (Yᵀ * Y)⁻¹ * Yᵀ
  have hGram := (continuous_id.matrix_transpose.matrix_mul continuous_id :
    Continuous (fun Y : Matrix (Fin n) (Fin l) ℝ => Yᵀ * Y))
  have hs : MeasurableSet s :=
    ((isClosed_eq hGram.matrix_det continuous_const).measurableSet).compl
  have hf : Measurable f := measurable_matrix_product
    (measurable_matrix_product measurable_id (measurable_matrix_nonsing_inv.comp hGram.measurable))
    (measurable_matrix_transpose measurable_id)
  convert hf.piecewise hs (measurable_const (a := D)) using 1
  funext Y
  by_cases hY : Y ∈ s
  · rw [Set.piecewise_eq_of_mem s f _ hY, fullRankColumnProjector_val hl Y hY]
    apply rangeProjector_of_inner_inverse
    have hUnit := isUnit_iff_ne_zero.mpr (show (Yᵀ * Y).det ≠ 0 from hY)
    rw [Matrix.mul_nonsing_inv _ hUnit, Matrix.one_mul]
  · rw [Set.piecewise_eq_of_notMem s f _ hY]
    unfold fullRankColumnProjector
    rw [dif_neg (show ¬ ((Yᵀ * Y).det ≠ 0) from hY)]

theorem rangeProjector_mul_orthogonal_left (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ * S = 1) (Y : Matrix (Fin n) (Fin l) ℝ) :
    rangeProjector (S * Y) = S * rangeProjector Y * Sᵀ := by
  have hG : (S * Y)ᵀ * (S * Y) = Yᵀ * Y := by
    rw [transpose_mul, Matrix.mul_assoc Yᵀ, ← Matrix.mul_assoc Sᵀ S, hS, Matrix.one_mul]
  let K (M : Matrix (Fin n) (Fin l) ℝ) := (⟨Mᵀ * M,
    by simpa only [conjTranspose_eq_transpose_of_trivial] using
      isHermitian_conjTranspose_mul_self M⟩ : {A : Matrix (Fin l) (Fin l) ℝ // A.IsHermitian})
  let inverse (A : {A : Matrix (Fin l) (Fin l) ℝ // A.IsHermitian}) :=
    symmetricPseudoInverse A.val A.property
  have hInv : inverse (K (S * Y)) = inverse (K Y) :=
    congrArg inverse (show K (S * Y) = K Y from Subtype.ext hG)
  rw [rangeProjector_eq_gram_pseudoInverse (S * Y), rangeProjector_eq_gram_pseudoInverse Y]
  change _ * inverse (K (S * Y)) * (S * Y)ᵀ = S * (Y * inverse (K Y) * Yᵀ) * Sᵀ
  rw [hInv, transpose_mul]
  simp only [Matrix.mul_assoc]

private theorem diagonal_sign_isOrthogonal {s : Fin n → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1) : (diagonal s)ᵀ * diagonal s = 1 := by
  rw [diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases hs i with hi | hi <;> simp [hi]

private theorem permMatrix_isOrthogonal (π : Equiv.Perm (Fin n)) :
    (π.permMatrix ℝ)ᵀ * (π.permMatrix ℝ) = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

/-- Corollary 4.2 stated for a matrix law. Only its column-space law is
required to be invariant under signs and permutations, and full column rank
is needed almost surely. -/
theorem meanSketchProjector_of_fullRankColumnSpace_symmetry (hn : 0 < n) (hl : l ≤ n)
    (μ : Measure (Matrix (Fin n) (Fin l) ℝ)) [IsProbabilityMeasure μ]
    (hRank : ∀ᵐ Y ∂μ, Function.Injective Y.mulVec)
    (hSign : ∀ s : Fin n → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
      (μ.map fun Y => rangeProjector (diagonal s * Y)) = μ.map rangeProjector)
    (hPerm : ∀ π : Equiv.Perm (Fin n),
      (μ.map fun Y => rangeProjector (π.permMatrix ℝ * Y)) = μ.map rangeProjector) :
    meanSketchProjector (μ.map (fullRankColumnProjector hl)) =
      ((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  let f := fullRankColumnProjector hl
  have hf : Measurable f := measurable_fullRankColumnProjector hl
  let : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hAE : (fun Y => (f Y).val) =ᵐ[μ] rangeProjector := by
    filter_upwards [hRank] with Y hY
    exact fullRankColumnProjector_val hl Y ((gaussianGram_det_ne_zero_iff Y).2 hY)
  have hComp (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ * S = 1)
      (hLaw : (μ.map fun Y => rangeProjector (S * Y)) = μ.map rangeProjector) :
      ((μ.map f).map fun P => S * P.val * Sᵀ) = (μ.map f).map Subtype.val := by
    rw [Measure.map_map (measurable_matrix_product
      (measurable_matrix_product measurable_const measurable_subtype_coe) measurable_const) hf,
      Measure.map_map measurable_subtype_coe hf]
    calc
      (μ.map fun Y => S * (f Y).val * Sᵀ) =
          μ.map (fun Y => rangeProjector (S * Y)) := by
        apply Measure.map_congr
        filter_upwards [hAE] with Y hY
        exact (congrArg (fun T => S * T * Sᵀ) hY).trans (rangeProjector_mul_orthogonal_left S hS Y).symm
      _ = μ.map rangeProjector := hLaw
      _ = _ := Measure.map_congr hAE.symm
  exact meanSketchProjector_of_signed_permutation_symmetry hn (μ.map f)
    (fun s hs => hComp _ (diagonal_sign_isOrthogonal hs) (hSign s hs))
    (fun π => hComp _ (permMatrix_isOrthogonal π) (hPerm π))

end

end TypicalOrientations
