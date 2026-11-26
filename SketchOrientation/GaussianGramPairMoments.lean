import SketchOrientation.GaussianChiSquareMeans
import SketchOrientation.GaussianGramPairAlgebra
import SketchOrientation.GaussianGramTracePowers
import SketchOrientation.GaussianSphereBeta

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix Submodule
open scoped ENNReal RealInnerProductSpace ProbabilityTheory

noncomputable section

/-- The inverse-square chi-square moment, in rational form. -/
theorem chiSquareNegativeMoment_two {ν : ℕ} (hν : 4 < ν) :
    chiSquareNegativeMoment ν 2 = 1 / (((ν : ℝ) - 2) * ((ν : ℝ) - 4)) := by
  have hν' : (4 : ℝ) < ν := by exact_mod_cast hν
  let a : ℝ := (ν : ℝ) / 2
  have h₂ : 0 < a - 2 := by dsimp [a]; linarith
  have h₁ : 0 < a - 1 := by linarith
  have hg := (Real.Gamma_pos_of_pos h₂).ne'
  have hG : Real.Gamma a = (a - 1) * ((a - 2) * Real.Gamma (a - 2)) := by
    calc
      _ = Real.Gamma ((a - 1) + 1) := by ring_nf
      _ = (a - 1) * Real.Gamma ((a - 2) + 1) := by
        rw [Real.Gamma_add_one h₁.ne', show a - 2 + 1 = a - 1 by ring]
      _ = _ := by rw [Real.Gamma_add_one h₂.ne']
  change (2 : ℝ) ^ (-(2 : ℝ)) * Real.Gamma (a - 2) / Real.Gamma a = _
  rw [hG, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
  generalize Real.Gamma (a - 2) = g at hg ⊢
  have hν₂ : (ν : ℝ) - 2 ≠ 0 := by linarith
  have hν₄ : (ν : ℝ) - 4 ≠ 0 := by linarith
  field_simp [hg, h₁.ne', h₂.ne', hν₂, hν₄]
  dsimp [a]
  ring

/-- Exact second reciprocal moment under the native chi-square law. -/
theorem chiSquare_inverse_sq_mean {ν : ℕ} (hν : 4 < ν) :
    Integrable (fun x : ℝ => x⁻¹ ^ 2) (chiSquareLaw ν) ∧
      (∫ x, x⁻¹ ^ 2 ∂chiSquareLaw ν) =
        1 / (((ν : ℝ) - 2) * ((ν : ℝ) - 4)) := by
  have hν' : (4 : ℝ) < ν := by exact_mod_cast hν
  have hnn : 0 ≤ᵐ[chiSquareLaw ν] (fun x : ℝ => x⁻¹ ^ 2) :=
    ae_of_all _ fun x => sq_nonneg _
  have hm : AEStronglyMeasurable (fun x : ℝ => x⁻¹ ^ 2) (chiSquareLaw ν) :=
    (measurable_id.inv.pow_const _).aestronglyMeasurable
  have hL : (∫⁻ x, ENNReal.ofReal (x⁻¹ ^ 2) ∂chiSquareLaw ν) =
      ENNReal.ofReal (1 / (((ν : ℝ) - 2) * ((ν : ℝ) - 4))) := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (x ^ (-(2 : ℝ))) ∂chiSquareLaw ν := by
        apply lintegral_congr_ae
        filter_upwards [ae_chiSquare_pos ν] with x hx
        rw [Real.rpow_neg hx.le, Real.rpow_two, inv_pow]
      _ = ENNReal.ofReal (chiSquareNegativeMoment ν 2) :=
        chiSquare_negative_moment (by norm_num) (by linarith)
      _ = _ := by rw [chiSquareNegativeMoment_two hν]
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, hL]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hm, hL, ENNReal.toReal_ofReal]
    exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))

variable {d k : ℕ}

private abbrev GaussianVector (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev GaussianColumns (d k : ℕ) := Fin k → GaussianVector d

private theorem residual_projections (Y : Matrix (Fin d) (Fin k) ℝ) :
    let S := Y.toEuclideanLin.range
    columnResidualSq Y = (fun x : Sᗮ => ‖x‖ ^ 2) ∘ Sᗮ.orthogonalProjectionOnto := by
  intro S
  funext x
  change ‖x - S.starProjection x‖ ^ 2 = ‖Sᗮ.orthogonalProjectionOnto x‖ ^ 2
  rw [S.orthogonalProjectionOnto_orthogonal]
  rfl

private theorem measurePreserving_residualSq (Y : Matrix (Fin d) (Fin k) ℝ)
    (hY : Function.Injective Y.mulVec) (hkd : k < d) :
    MeasurePreserving (columnResidualSq Y) (stdGaussian (GaussianVector d)) (chiSquareLaw (d - k)) := by
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
  have hpos : 0 < Module.finrank ℝ Sᗮ := by omega
  rw [residual_projections]
  exact ⟨by fun_prop, by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), stdGaussian_map_projection,
      stdGaussian_norm_sq_map_finrank hpos, hS]⟩

private theorem gaussian_inner_sq_mean (u : GaussianVector d) :
    (∫ x, ⟪u, x⟫ ^ 2 ∂stdGaussian (GaussianVector d)) = ‖u‖ ^ 2 := by
  let L := innerSL ℝ u
  have hL := variance_dual_stdGaussian L
  rw [variance_eq_sub (IsGaussian.memLp_dual _ L 2 (by norm_num)),
    integral_strongDual_stdGaussian, zero_pow (by decide : 2 ≠ 0), sub_zero, innerSL_apply_norm] at hL
  exact hL

private theorem gaussian_inner_sq_indep_inverse_residual_sq (Y : Matrix (Fin d) (Fin k) ℝ)
    (u : GaussianVector d) (hu : u ∈ Y.toEuclideanLin.range) :
    IndepFun (fun x => ⟪u, x⟫ ^ 2) (fun x => (columnResidualSq Y x)⁻¹ ^ 2)
      (stdGaussian (GaussianVector d)) := by
  let S := Y.toEuclideanLin.range
  let f := fun x : S => ⟪u, (x : GaussianVector d)⟫ ^ 2
  let g := fun x : Sᗮ => (‖x‖ ^ 2 : ℝ)⁻¹ ^ 2
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have h := (stdGaussian_orthogonal_split_indep S).comp hf hg
  have he : f ∘ S.orthogonalProjectionOnto = fun x => ⟪u, x⟫ ^ 2 := by
    funext x
    change ⟪u, S.starProjection x⟫ ^ 2 = _
    rw [← S.inner_starProjection_left_eq_right, S.starProjection_eq_self_iff.mpr hu]
  rw [he] at h
  rw [residual_projections]
  exact h

private def insertColumn (j : Fin (k + 1)) (xy : GaussianVector d × GaussianColumns d k) :
    GaussianColumns d (k + 1) := j.insertNth xy.1 xy.2

private theorem dropGramColumn_insert (j : Fin (k + 1)) (x : GaussianVector d)
    (X : GaussianColumns d k) :
    dropGramColumn (matrixOfGaussianColumns (insertColumn j (x, X))) j =
      matrixOfGaussianColumns X := by
  ext i l
  change (j.insertNth (α := fun _ => GaussianVector d) x X (j.succAbove l)) i = (X l) i
  rw [Fin.insertNth_apply_succAbove]

private theorem col_insert (j : Fin (k + 1)) (x : GaussianVector d) (X : GaussianColumns d k) :
    WithLp.toLp 2 ((matrixOfGaussianColumns (insertColumn j (x, X))).col j) = x := by
  change j.insertNth (α := fun _ => GaussianVector d) x X j = x
  exact Fin.insertNth_apply_same _ _ _

private theorem conditional_diag_product {p : ℕ} (hp : 4 ≤ p) (j : Fin (k + 1)) (i : Fin k)
    (X : GaussianColumns (k + 1 + p) k) (hX : Function.Injective (matrixOfGaussianColumns X).mulVec)
    (hInt : Integrable (fun x =>
      let Z := matrixOfGaussianColumns (insertColumn j (x, X))
      (gaussianGram Z)⁻¹ (j.succAbove i) (j.succAbove i) * (gaussianGram Z)⁻¹ j j)
      (stdGaussian (GaussianVector (k + 1 + p)))) :
    (∫ x, (let Z := matrixOfGaussianColumns (insertColumn j (x, X))
      (gaussianGram Z)⁻¹ (j.succAbove i) (j.succAbove i) * (gaussianGram Z)⁻¹ j j)
      ∂stdGaussian (GaussianVector (k + 1 + p))) =
      (gaussianGram (matrixOfGaussianColumns X))⁻¹ i i *
        (1 / ((p : ℝ) - 1) + 1 / (((p : ℝ) - 1) * ((p : ℝ) - 3))) := by
  let d := k + 1 + p
  let Y := matrixOfGaussianColumns X
  let u := gaussianGramDualColumn Y i
  let C := (gaussianGram Y)⁻¹ i i
  let t := columnResidualSq Y
  let μ := stdGaussian (GaussianVector d)
  let a := fun x => C * (t x)⁻¹
  let f := fun x => ⟪u, x⟫ ^ 2
  let g := fun x => (t x)⁻¹ ^ 2
  have ht := measurePreserving_residualSq Y hX (by omega)
  have hn : d - k = p + 1 := by dsimp [d]; omega
  change MeasurePreserving t μ _ at ht
  rw [hn] at ht
  have hInv := chiSquare_inverse_mean (ν := p + 1) (by omega)
  have hInv₂ := chiSquare_inverse_sq_mean (ν := p + 1) (by omega)
  have hInt₁ := (ht.integrable_comp_of_integrable hInv.1).const_mul C
  change Integrable a μ at hInt₁
  have hAe : (fun x =>
      let Z := matrixOfGaussianColumns (insertColumn j (x, X))
      (gaussianGram Z)⁻¹ (j.succAbove i) (j.succAbove i) * (gaussianGram Z)⁻¹ j j)
      =ᵐ[μ] fun x => a x + f x * g x := by
    filter_upwards [ae_not_mem_proper_submodule Y.toEuclideanLin.range
      (range_ne_top_of_width_lt Y (by omega))] with x hx
    let Z := matrixOfGaussianColumns (insertColumn j (x, X))
    have hd : dropGramColumn Z j = Y := dropGramColumn_insert j x X
    have hc : WithLp.toLp 2 (Z.col j) = x := col_insert j x X
    have hZ : Function.Injective Z.mulVec := by
      apply gramColumns_injective_of_drop Z j
      · rwa [hd]
      · rwa [hd, hc]
    have h := gaussianGram_inv_succAbove_diag Z j i hZ (hd ▸ hX)
    dsimp only at h
    rw [hd, hc] at h
    change _ * _ = _
    rw [h, gaussianGram_inv_diag Z hZ j, hd, hc]
    change (C + f x / t x) * (t x)⁻¹ = C * (t x)⁻¹ + f x * ((t x)⁻¹ ^ 2)
    rw [div_eq_mul_inv]
    ring
  have hInt₂ : Integrable (fun x => f x * g x) μ := by
    exact ((hInt.congr hAe).sub hInt₁).congr (ae_of_all _ fun x => add_sub_cancel_left ..)
  have hI₁ : (∫ x, (t x)⁻¹ ∂μ) = 1 / ((p : ℝ) - 1) := by
    have he := integral_map (μ := μ) ht.measurable.aemeasurable
      (f := fun s : ℝ => s⁻¹) measurable_id.inv.aestronglyMeasurable
    rw [ht.map_eq, hInv.2] at he
    rw [← he]
    push_cast
    ring_nf
  have hI₂ : (∫ x, g x ∂μ) = 1 / (((p : ℝ) - 1) * ((p : ℝ) - 3)) := by
    change (∫ x, (t x)⁻¹ ^ 2 ∂μ) = _
    have he := integral_map (μ := μ) ht.measurable.aemeasurable
      (f := fun s : ℝ => s⁻¹ ^ 2) (measurable_id.inv.pow_const (2 : ℕ)).aestronglyMeasurable
    rw [ht.map_eq, hInv₂.2] at he
    rw [← he]
    push_cast
    ring_nf
  have hInd : IndepFun f g μ := gaussian_inner_sq_indep_inverse_residual_sq Y u
    (gaussianGramDualColumn_mem_range Y i)
  have hF : (∫ x, f x ∂μ) = C := (gaussian_inner_sq_mean u).trans
    (gaussianGramDualColumn_norm_sq Y hX i)
  rw [integral_congr_ae hAe, integral_add hInt₁ hInt₂,
    hInd.integral_fun_mul_eq_mul_integral (by dsimp [f]; fun_prop)
      (ht.measurable.inv.pow_const _).aestronglyMeasurable]
  change (∫ x, C * (t x)⁻¹ ∂μ) + (∫ x, f x ∂μ) * (∫ x, g x ∂μ) = _
  rw [integral_const_mul, hI₁, hI₂, hF, mul_add]

private theorem diag_sq_mean {k p : ℕ} (hp : 4 ≤ p) (i : Fin k) :
    Integrable (fun Z => ((gaussianGram Z)⁻¹ i i) ^ 2) (gaussianMatrixLaw (k + p) k) ∧
      (∫ Z, ((gaussianGram Z)⁻¹ i i) ^ 2 ∂gaussianMatrixLaw (k + p) k) =
        1 / (((p : ℝ) - 1) * ((p : ℝ) - 3)) := by
  have hn : k + p - k + 1 = p + 1 := by omega
  have hr : (2 : ℝ) < ((k + p - k + 1 : ℕ) : ℝ) / 2 := by
    rw [hn, Nat.cast_add, Nat.cast_one]
    have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h := gaussianGram_inv_diag_rpow_mean (d := k + p) (by omega) i (by norm_num) hr
  rw [hn, chiSquareNegativeMoment_two (by omega)] at h
  simp only [Real.rpow_two, Nat.cast_add, Nat.cast_one] at h
  have h₁ : (p : ℝ) + 1 - 2 = p - 1 := by ring
  have h₃ : (p : ℝ) + 1 - 4 = p - 3 := by ring
  simpa only [h₁, h₃] using h

/-- Products of two diagonal entries of the inverse Gaussian Gram matrix
are integrable at oversampling at least four. -/
theorem integrable_gaussianGram_inv_diag_product {k p : ℕ} (hp : 4 ≤ p) (i j : Fin k) :
    Integrable (fun Z => (gaussianGram Z)⁻¹ i i * (gaussianGram Z)⁻¹ j j)
      (gaussianMatrixLaw (k + p) k) := by
  have hm (a : Fin k) :
      MemLp (fun Z => (gaussianGram Z)⁻¹ a a) 2 (gaussianMatrixLaw (k + p) k) :=
    (memLp_two_iff_integrable_sq (measurable_gaussianGram_inv_entry a a).aestronglyMeasurable).2
      (diag_sq_mean hp a).1
  exact (hm i).integrable_mul (hm j)

private theorem off_diag_product_mean {k p : ℕ} (hp : 4 ≤ p) (j : Fin (k + 1)) (i : Fin k) :
    (∫ Z, (gaussianGram Z)⁻¹ (j.succAbove i) (j.succAbove i) * (gaussianGram Z)⁻¹ j j
      ∂gaussianMatrixLaw (k + 1 + p) (k + 1)) =
      ((p : ℝ) - 2) / (p * ((p : ℝ) - 1) * ((p : ℝ) - 3)) := by
  let d := k + 1 + p
  let μ := stdGaussian (GaussianVector d)
  let ν := gaussianColumnLaw d k
  let f := fun Z : Matrix (Fin d) (Fin (k + 1)) ℝ =>
    (gaussianGram Z)⁻¹ (j.succAbove i) (j.succAbove i) * (gaussianGram Z)⁻¹ j j
  let m := matrixOfGaussianColumns (d := d) (k := k + 1)
  let F := f ∘ m ∘ (insertColumn (d := d) j)
  have hm : MeasurePreserving m (gaussianColumnLaw d (k + 1))
      (gaussianMatrixLaw d (k + 1)) := ⟨measurable_matrixOfGaussianColumns, rfl⟩
  have he : MeasurePreserving (insertColumn (d := d) j) (μ.prod ν)
      (gaussianColumnLaw d (k + 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ => stdGaussian (GaussianVector d)) j).symm
  have hpres := hm.comp he
  have hf : Integrable f (gaussianMatrixLaw d (k + 1)) :=
    integrable_gaussianGram_inv_diag_product hp (j.succAbove i) j
  have hF : Integrable F (μ.prod ν) := hpres.integrable_comp_of_integrable hf
  let c : ℝ := 1 / ((p : ℝ) - 1) + 1 / (((p : ℝ) - 1) * ((p : ℝ) - 3))
  have hX : ∀ᵐ X ∂ν, Function.Injective (matrixOfGaussianColumns X).mulVec :=
    ae_of_ae_map measurable_matrixOfGaussianColumns.aemeasurable
      (ae_gaussianMatrix_injective (d := d) (k := k) (by dsimp [d]; omega))
  have hcond : (fun X => ∫ x, F (x, X) ∂μ) =ᵐ[ν]
      fun X => (gaussianGram (matrixOfGaussianColumns X))⁻¹ i i * c := by
    filter_upwards [hX, hF.prod_left_ae] with X hX' hIX
    exact conditional_diag_product hp j i X hX' hIX
  change (∫ Z, f Z ∂gaussianMatrixLaw d (k + 1)) = _
  rw [← hpres.map_eq, integral_map hpres.measurable.aemeasurable]
  · change (∫ z, F z ∂μ.prod ν) = _
    rw [integral_prod_symm _ hF, integral_congr_ae hcond, integral_mul_const]
    have hmean := (gaussianGram_inv_diag_mean (d := d) (k := k) (by dsimp [d] <;> omega) i).2
    rw [gaussianMatrixLaw, integral_map measurable_matrixOfGaussianColumns.aemeasurable
      (measurable_gaussianGram_inv_entry i i).aestronglyMeasurable] at hmean
    change (∫ X, (gaussianGram (matrixOfGaussianColumns X))⁻¹ i i ∂ν) = _ at hmean
    rw [hmean]
    have hcast : (d : ℝ) - k - 1 = p := by dsimp [d]; push_cast; ring
    rw [hcast]
    have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
    dsimp [c]
    field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith,
      show (p : ℝ) - 3 ≠ 0 by linarith]
    <;> ring
  · exact ((measurable_gaussianGram_inv_entry (j.succAbove i) (j.succAbove i)).mul
      (measurable_gaussianGram_inv_entry j j)).aestronglyMeasurable

/-- Exact inverse-Wishart diagonal products, including the repeated index,
for the native Gaussian Gram law at oversampling at least four. -/
theorem gaussianGram_inv_diag_product_mean {k p : ℕ} (hp : 4 ≤ p) (i j : Fin k) :
    (∫ Z, (gaussianGram Z)⁻¹ i i * (gaussianGram Z)⁻¹ j j
      ∂gaussianMatrixLaw (k + p) k) =
      ((p : ℝ) - 2 + 2 * (if i = j then 1 else 0)) /
        (p * ((p : ℝ) - 1) * ((p : ℝ) - 3)) := by
  by_cases hij : i = j
  · subst j
    simp only [if_true, mul_one, ← pow_two, eq_self]
    rw [(diag_sq_mean hp i).2]
    have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
    field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith,
      show (p : ℝ) - 3 ≠ 0 by linarith]
    <;> ring
  · cases k with
    | zero => exact i.elim0
    | succ k =>
      obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hij
      simpa [hij] using off_diag_product_mean hp j a

/-- The exact covariance between two inverse-Wishart diagonal entries. -/
theorem gaussianGram_inv_diag_covariance {k p : ℕ} (hp : 4 ≤ p) (i j : Fin k) :
    cov[fun Z => (gaussianGram Z)⁻¹ i i, fun Z => (gaussianGram Z)⁻¹ j j;
      gaussianMatrixLaw (k + p) k] =
      (2 + 2 * ((p : ℝ) - 1) * (if i = j then 1 else 0)) /
        (p * ((p : ℝ) - 1) ^ 2 * ((p : ℝ) - 3)) := by
  have hLp (j : Fin k) :
      MemLp (fun Z => (gaussianGram Z)⁻¹ j j) 2 (gaussianMatrixLaw (k + p) k) :=
    (memLp_two_iff_integrable_sq (measurable_gaussianGram_inv_entry j j).aestronglyMeasurable).2
      (diag_sq_mean hp j).1
  have hMean (j : Fin k) :
      (∫ Z, (gaussianGram Z)⁻¹ j j ∂gaussianMatrixLaw (k + p) k) = 1 / ((p : ℝ) - 1) := by
    rw [(gaussianGram_inv_diag_mean (d := k + p) (by omega) j).2, Nat.cast_add, add_sub_cancel_left]
  have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
  rw [covariance_eq_sub (hLp i) (hLp j)]
  change (∫ Z, (gaussianGram Z)⁻¹ i i * (gaussianGram Z)⁻¹ j j ∂gaussianMatrixLaw (k + p) k) -
    (∫ Z, (gaussianGram Z)⁻¹ i i ∂gaussianMatrixLaw (k + p) k) *
      (∫ Z, (gaussianGram Z)⁻¹ j j ∂gaussianMatrixLaw (k + p) k) = _
  rw [gaussianGram_inv_diag_product_mean hp i j, hMean, hMean]
  field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith,
    show (p : ℝ) - 3 ≠ 0 by linarith]
  <;> ring

/-- The normalized inverse trace has a finite second moment. -/
theorem memLp_gaussianGram_inv_normalized_trace {k p : ℕ} (hk : 0 < k) (hp : 4 ≤ p) :
    MemLp (fun Z => (gaussianGram Z)⁻¹.trace / (k : ℝ)) 2 (gaussianMatrixLaw (k + p) k) := by
  have hn : k + p - k + 1 = p + 1 := by omega
  have hr : (2 : ℝ) < ((k + p - k + 1 : ℕ) : ℝ) / 2 := by
    rw [hn, Nat.cast_add, Nat.cast_one]
    have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h := (gaussianGram_inv_trace_moment (d := k + p) hk (by omega) (by norm_num) hr).1
  simp only [Real.rpow_two] at h
  have hM : Measurable (fun Z : Matrix (Fin (k + p)) (Fin k) ℝ =>
      (gaussianGram Z)⁻¹.trace / (k : ℝ)) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact (Finset.measurable_sum _ fun i _ => measurable_gaussianGram_inv_entry i i).div_const _
  exact (memLp_two_iff_integrable_sq hM.aestronglyMeasurable).2 h

/-- Exact inverse-Wishart variance of the normalized inverse trace. -/
theorem gaussianGram_inv_normalized_trace_variance {k p : ℕ} (hk : 0 < k) (hp : 4 ≤ p) :
    Var[fun Z => (gaussianGram Z)⁻¹.trace / (k : ℝ); gaussianMatrixLaw (k + p) k] =
      2 * ((k : ℝ) + p - 1) / (k * p * ((p : ℝ) - 1) ^ 2 * ((p : ℝ) - 3)) := by
  let μ := gaussianMatrixLaw (k + p) k
  let B := fun Z : Matrix (Fin (k + p)) (Fin k) ℝ => (gaussianGram Z)⁻¹
  let D := (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 3)
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hMean : (∫ Z, (B Z).trace / (k : ℝ) ∂μ) = 1 / ((p : ℝ) - 1) := by
    change (∫ Z, (gaussianGram Z)⁻¹.trace / (k : ℝ) ∂μ) = _
    rw [integral_div, (gaussianGram_inv_trace_mean (d := k + p) (k := k) (by omega)).2]
    push_cast
    have he : (k : ℝ) + p - k - 1 = p - 1 := by ring
    rw [he]
    field_simp [hk'.ne', show (p : ℝ) - 1 ≠ 0 by linarith]
  have hInt (i j : Fin k) : Integrable (fun Z => B Z i i * B Z j j) μ :=
    integrable_gaussianGram_inv_diag_product hp i j
  have hProd (i j : Fin k) : (∫ Z, B Z i i * B Z j j ∂μ) =
      ((p : ℝ) - 2 + 2 * (if i = j then 1 else 0)) / D :=
    gaussianGram_inv_diag_product_mean hp i j
  have hSq : (∫ Z, ((B Z).trace / (k : ℝ)) ^ 2 ∂μ) =
      ((k : ℝ) * ((k : ℝ) * ((p : ℝ) - 2) + 2)) / (D * (k : ℝ) ^ 2) := by
    simp_rw [div_pow]
    rw [integral_div]
    have hpoint (Z : Matrix (Fin (k + p)) (Fin k) ℝ) : (B Z).trace ^ 2 =
        ∑ i : Fin k, ∑ j : Fin k, B Z i i * B Z j j := by
      simp_rw [Matrix.trace, Matrix.diag_apply, pow_two, Finset.sum_mul, Finset.mul_sum]
    simp_rw [hpoint]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hInt i j)]
    simp_rw [integral_finsetSum _ (fun j _ => hInt _ j), hProd, ← Finset.sum_div]
    have hSum (i : Fin k) : (∑ j : Fin k, ((p : ℝ) - 2 + 2 * (if i = j then 1 else 0))) =
        (k : ℝ) * ((p : ℝ) - 2) + 2 := by
      simp [Finset.sum_add_distrib, Finset.sum_ite_eq]
      ring
    simp_rw [hSum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_div]
  rw [variance_eq_sub (memLp_gaussianGram_inv_normalized_trace hk hp)]
  change (∫ Z, ((B Z).trace / (k : ℝ)) ^ 2 ∂μ) - (∫ Z, (B Z).trace / (k : ℝ) ∂μ) ^ 2 = _
  rw [hSq, hMean]
  dsimp [D]
  field_simp [hk'.ne', show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith,
    show (p : ℝ) - 3 ≠ 0 by linarith]
  <;> ring

end

end SketchOrientation
