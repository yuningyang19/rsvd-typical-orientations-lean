import SketchOrientation.GaussianGramAlgebra
import SketchOrientation.GaussianMatrixSpace
import SketchOrientation.GaussianRadial

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal

variable {d k : ℕ}

/-- Product law of independent Euclidean standard-Gaussian columns.
The coordinates in each column are independently standard real Gaussians. -/
noncomputable def gaussianColumnLaw (d k : ℕ) :
    Measure (Fin k → EuclideanSpace ℝ (Fin d)) :=
  Measure.pi fun _ => stdGaussian _

instance (d k : ℕ) : IsProbabilityMeasure (gaussianColumnLaw d k) := by
  unfold gaussianColumnLaw
  infer_instance

/-- Place the random vectors in the columns of the matrix. -/
def matrixOfGaussianColumns (X : Fin k → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin k) ℝ :=
  Matrix.of fun i j => X j i

theorem measurable_matrixOfGaussianColumns :
    Measurable (@matrixOfGaussianColumns d k) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact (measurable_pi_apply i).comp
    ((WithLp.measurable_ofLp _ _).comp (measurable_pi_apply j))

/-- Law of the actual rectangular matrix of independent standard real
Gaussian entries, using the product by columns. -/
noncomputable def gaussianMatrixLaw (d k : ℕ) : Measure (Matrix (Fin d) (Fin k) ℝ) :=
  (gaussianColumnLaw d k).map matrixOfGaussianColumns

instance (d k : ℕ) : IsProbabilityMeasure (gaussianMatrixLaw d k) :=
  Measure.isProbabilityMeasure_map measurable_matrixOfGaussianColumns.aemeasurable

private theorem measurable_det_comp {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] [DecidableEq ι] {A : X → Matrix ι ι ℝ}
    (ha : ∀ i j, Measurable (fun x => A x i j)) : Measurable (fun x => (A x).det) := by
  simp_rw [Matrix.det_apply']
  exact Finset.measurable_sum _ fun σ _ =>
    (Finset.measurable_prod _ fun i _ => ha (σ i) i).const_mul _

theorem measurable_gaussianGram_entry (i j : Fin k) :
    Measurable (fun Z : Matrix (Fin d) (Fin k) ℝ => gaussianGram Z i j) := by
  unfold gaussianGram
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.measurable_sum _ fun l _ =>
    ((continuous_id.matrix_elem l i).mul (continuous_id.matrix_elem l j)).measurable

theorem measurable_gaussianGram_det :
    Measurable (fun Z : Matrix (Fin d) (Fin k) ℝ => (gaussianGram Z).det) :=
  measurable_det_comp measurable_gaussianGram_entry

private theorem measurableSet_injective_gramColumns :
    MeasurableSet {Z : Matrix (Fin d) (Fin k) ℝ | Function.Injective Z.mulVec} := by
  simp_rw [← gaussianGram_det_ne_zero_iff]
  exact (measurable_gaussianGram_det (d := d) (k := k) (measurableSet_singleton 0)).compl

theorem ae_not_mem_proper_submodule (S : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hS : S ≠ ⊤) : ∀ᵐ z ∂stdGaussian _, z ∉ S := by
  rw [ae_iff]
  simp only [not_not]
  rw [stdGaussian_euclidean_density]
  exact withDensity_absolutelyContinuous _ _ (Measure.addHaar_submodule volume S hS)

private theorem dropGramColumn_of_insert (x : EuclideanSpace ℝ (Fin d))
    (X : Fin k → EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) :
    dropGramColumn (matrixOfGaussianColumns (j.insertNth (α := fun _ => EuclideanSpace ℝ (Fin d)) x X)) j =
      matrixOfGaussianColumns X := by
  ext i l
  change ((j.insertNth (α := fun _ => EuclideanSpace ℝ (Fin d)) x X) (j.succAbove l)) i = (X l) i
  rw [Fin.insertNth_apply_succAbove]

private theorem col_of_insert (x : EuclideanSpace ℝ (Fin d))
    (X : Fin k → EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) :
    WithLp.toLp 2 ((matrixOfGaussianColumns (j.insertNth (α := fun _ => EuclideanSpace ℝ (Fin d)) x X)).col j) = x := by
  change j.insertNth (α := fun _ => EuclideanSpace ℝ (Fin d)) x X j = x
  exact Fin.insertNth_apply_same _ _ _

theorem range_ne_top_of_width_lt (Y : Matrix (Fin d) (Fin k) ℝ) (hk : k < d) :
    LinearMap.range Y.toEuclideanLin ≠ ⊤ := by
  intro he
  have := Y.toEuclideanLin.finrank_range_le
  rw [he, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at this
  omega

private theorem measurePreserving_insertGaussianColumn (j : Fin (k + 1)) :
    MeasurePreserving (fun (p : EuclideanSpace ℝ (Fin d) ×
      (Fin k → EuclideanSpace ℝ (Fin d))) => j.insertNth (α := fun _ => EuclideanSpace ℝ (Fin d)) p.1 p.2)
      ((stdGaussian _).prod (gaussianColumnLaw d k)) (gaussianColumnLaw d (k + 1)) :=
  (measurePreserving_piFinSuccAbove (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d))) j).symm

private theorem ae_gaussianColumnLaw_injective (hkd : k ≤ d) :
    ∀ᵐ X ∂gaussianColumnLaw d k, Function.Injective (matrixOfGaussianColumns X).mulVec := by
  induction k with
  | zero =>
    exact ae_of_all _ fun _ _ _ _ => Subsingleton.elim _ _
  | succ k ih =>
    let e := fun (p : EuclideanSpace ℝ (Fin d) × (Fin k → EuclideanSpace ℝ (Fin d))) =>
      (0 : Fin (k + 1)).insertNth (α := fun _ => EuclideanSpace ℝ (Fin d)) p.1 p.2
    let P := fun (p : EuclideanSpace ℝ (Fin d) × (Fin k → EuclideanSpace ℝ (Fin d))) =>
      Function.Injective (matrixOfGaussianColumns (e p)).mulVec
    have hpres := measurePreserving_insertGaussianColumn (d := d) (0 : Fin (k + 1))
    have hm : MeasurableSet {X : Fin (k + 1) → EuclideanSpace ℝ (Fin d) |
        Function.Injective (matrixOfGaussianColumns X).mulVec} :=
      measurableSet_injective_gramColumns.preimage measurable_matrixOfGaussianColumns
    have hmp : MeasurableSet {p | P p} := hm.preimage hpres.measurable
    rw [← hpres.map_eq]
    apply (ae_map_iff hpres.measurable.aemeasurable hm).2
    change ∀ᵐ p ∂(stdGaussian _).prod (gaussianColumnLaw d k), P p
    rw [Measure.ae_prod_iff_ae_ae hmp, Measure.ae_ae_comm hmp]
    filter_upwards [ih (by omega)] with X hX
    let Y := matrixOfGaussianColumns X
    filter_upwards [ae_not_mem_proper_submodule (LinearMap.range Y.toEuclideanLin)
      (range_ne_top_of_width_lt Y (by omega))] with x hx
    apply gramColumns_injective_of_drop _ (0 : Fin (k + 1))
    · rwa [dropGramColumn_of_insert]
    · rwa [dropGramColumn_of_insert, col_of_insert]

/-- A rectangular matrix of independent standard normals has full column
rank almost surely whenever its row count is at least its column count. -/
theorem ae_gaussianMatrix_injective (hkd : k ≤ d) :
    ∀ᵐ Z ∂gaussianMatrixLaw d k, Function.Injective Z.mulVec := by
  rw [gaussianMatrixLaw, ae_map_iff measurable_matrixOfGaussianColumns.aemeasurable
    measurableSet_injective_gramColumns]
  exact ae_gaussianColumnLaw_injective hkd


theorem measurable_gaussianGram_inv_entry (i j : Fin k) :
    Measurable (fun Z : Matrix (Fin d) (Fin k) ℝ => (gaussianGram Z)⁻¹ i j) := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, Matrix.adjugate_apply]
  refine (measurable_gaussianGram_det.inv).mul (measurable_det_comp fun a b => ?_)
  by_cases hab : a = j
  · subst a
    simp_rw [Matrix.updateRow_self]
    exact measurable_const
  · simp_rw [Matrix.updateRow_ne hab]
    exact measurable_gaussianGram_entry a b

private theorem stdGaussian_subspace_norm_sq_map (S : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (h : 0 < Module.finrank ℝ S) :
    (stdGaussian S).map (fun x => ‖x‖ ^ 2) = chiSquareLaw (Module.finrank ℝ S) := by
  let e := (stdOrthonormalBasis ℝ S).repr
  have he := stdGaussian_map e
  have hcomp : (fun x : S => ‖x‖ ^ 2) = (fun y : EuclideanSpace ℝ _ => ‖y‖ ^ 2) ∘ e := by
    funext x
    simp [e]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), he, stdGaussian_norm_sq_map h]

private theorem gaussianColumnResidualSq_law (Y : Matrix (Fin d) (Fin k) ℝ)
    (hY : Function.Injective Y.mulVec) (hkd : k < d) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (columnResidualSq Y) = chiSquareLaw (d - k) := by
  let S := LinearMap.range Y.toEuclideanLin
  have hY' : Function.Injective Y.toEuclideanLin := by
    intro x y h
    apply WithLp.ofLp_injective
    exact hY (congrArg WithLp.ofLp h)
  have hs : Module.finrank ℝ S = k := by
    change Module.finrank ℝ (LinearMap.range Y.toEuclideanLin) = k
    rw [LinearMap.finrank_range_of_inj hY', finrank_euclideanSpace_fin]
  have hd := S.finrank_add_finrank_orthogonal
  rw [hs, finrank_euclideanSpace_fin] at hd
  have hS : Module.finrank ℝ Sᗮ = d - k := by omega
  have heq : columnResidualSq Y =
      (fun x : Sᗮ => ‖x‖ ^ 2) ∘ Sᗮ.orthogonalProjectionOnto := by
    funext x
    change ‖x - S.starProjection x‖ ^ 2 = ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2
    rw [S.orthogonalProjectionOnto_orthogonal]
    rfl
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop),
    stdGaussian_map_projection, stdGaussian_subspace_norm_sq_map _ (by omega), hS]


private abbrev GaussianColumns (d k : ℕ) := Fin k → EuclideanSpace ℝ (Fin d)

private def insertGaussianColumn (j : Fin (k + 1))
    (p : EuclideanSpace ℝ (Fin d) × GaussianColumns d k) : GaussianColumns d (k + 1) :=
  j.insertNth p.1 p.2

private noncomputable def invDiagReciprocal (j : Fin k)
    (Z : Matrix (Fin d) (Fin k) ℝ) : ℝ :=
  ((gaussianGram Z)⁻¹ j j)⁻¹

private theorem conditionalInvDiag_law (hkd : k + 1 ≤ d) (j : Fin (k + 1))
    (X : GaussianColumns d k) (hX : Function.Injective (matrixOfGaussianColumns X).mulVec) :
    (stdGaussian _).map (fun x => invDiagReciprocal j
      (matrixOfGaussianColumns (insertGaussianColumn j (x, X)))) = chiSquareLaw (d - k) := by
  let Y := matrixOfGaussianColumns X
  refine (Measure.map_congr ?_).trans (gaussianColumnResidualSq_law Y hX (by omega))
  filter_upwards [ae_not_mem_proper_submodule (LinearMap.range Y.toEuclideanLin)
    (range_ne_top_of_width_lt Y (by omega))] with x hx
  let Z := matrixOfGaussianColumns (j.insertNth x X)
  have hd : dropGramColumn Z j = Y := dropGramColumn_of_insert x X j
  have hc : WithLp.toLp 2 (Z.col j) = x := col_of_insert x X j
  have hfull : Function.Injective Z.mulVec := by
    apply gramColumns_injective_of_drop Z j
    · rwa [hd]
    · rwa [hd, hc]
  change ((gaussianGram Z)⁻¹ j j)⁻¹ = columnResidualSq Y x
  rw [gaussianGram_inv_diag _ hfull, inv_inv, hd, hc]

/-- The reciprocal of each inverse-Gram diagonal has the law of the squared
norm of a standard Gaussian in the complementary dimension. -/
theorem gaussianGram_inv_diag_reciprocal_law (hkd : k + 1 ≤ d) (j : Fin (k + 1)) :
    (gaussianMatrixLaw d (k + 1)).map (fun Z => ((gaussianGram Z)⁻¹ j j)⁻¹) =
      chiSquareLaw (d - k) := by
  let f := invDiagReciprocal (d := d) j
  let e := insertGaussianColumn (d := d) j
  let F := f ∘ matrixOfGaussianColumns ∘ e
  let μ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hf : Measurable f := (measurable_gaussianGram_inv_entry j j).inv
  have hpres : MeasurePreserving e (μ.prod (gaussianColumnLaw d k)) (gaussianColumnLaw d (k + 1)) :=
    measurePreserving_insertGaussianColumn j
  have hF : Measurable F := hf.comp (measurable_matrixOfGaussianColumns.comp hpres.measurable)
  have heq : (gaussianMatrixLaw d (k + 1)).map f = (μ.prod (gaussianColumnLaw d k)).map F := by
    unfold gaussianMatrixLaw
    rw [Measure.map_map hf measurable_matrixOfGaussianColumns, ← hpres.map_eq,
      Measure.map_map (hf.comp measurable_matrixOfGaussianColumns) hpres.measurable]
    rfl
  change (gaussianMatrixLaw d (k + 1)).map f = _
  rw [heq]
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hF hs, Measure.prod_apply_symm (hs.preimage hF)]
  calc
    _ = ∫⁻ _x, chiSquareLaw (d - k) s ∂gaussianColumnLaw d k := by
      apply lintegral_congr_ae
      filter_upwards [ae_gaussianColumnLaw_injective (d := d) (k := k) (by omega)] with X hX
      let g := fun x => F (x, X)
      have hg : Measurable g := hF.comp (measurable_id.prodMk measurable_const)
      change μ (g ⁻¹' s) = _
      rw [← Measure.map_apply hg hs]
      exact congrArg (fun ν : Measure ℝ => ν s) (conditionalInvDiag_law hkd j X hX)
    _ = _ := by simp

end SketchOrientation
