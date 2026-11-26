import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Sequences

/-! Continuity of the full ordered spectrum of a real symmetric matrix. -/

namespace SketchOrientation

open Filter Matrix Polynomial Set Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem charpoly_eq_orderedFactors {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A.charpoly = ∏ j, (X - C (hA.eigenvalues₀ j)) := by
  rw [hA.splits_charpoly.eq_prod_roots_of_monic A.charpoly_monic,
    hA.roots_charpoly_eq_eigenvalues₀]
  simp [Function.comp_def, Finset.prod]

private theorem norm_eigenvalues₀_le_row_max {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (j : Fin (Fintype.card ι)) {R : ℝ} (hR : ∀ a b, ‖A a b‖ ≤ R) :
    ‖hA.eigenvalues₀ j‖ ≤ Fintype.card ι * R := by
  have hspec : hA.eigenvalues₀ j ∈ spectrum ℝ A := by
    simpa [Matrix.IsHermitian.eigenvalues] using
      hA.eigenvalues_mem_spectrum_real ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
  have heig : Module.End.HasEigenvalue A.toLin' (hA.eigenvalues₀ j) := by
    rwa [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
  obtain ⟨a, ha⟩ := eigenvalue_mem_ball heig
  rw [mem_closedBall_iff_norm'] at ha
  calc
    ‖hA.eigenvalues₀ j‖ = ‖A a a - (A a a - hA.eigenvalues₀ j)‖ := by ring_nf
    _ ≤ ‖A a a‖ + ‖A a a - hA.eigenvalues₀ j‖ := norm_sub_le _ _
    _ ≤ ‖A a a‖ + ∑ b ∈ Finset.univ.erase a, ‖A a b‖ := add_le_add_right ha _
    _ = ∑ b, ‖A a b‖ := Finset.add_sum_erase _ (fun b ↦ ‖A a b‖) (Finset.mem_univ a)
    _ ≤ Fintype.card ι * R := by
      simpa using (Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) ↦ hR a b)

private theorem orderedFactors_identify {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    {u : Fin (Fintype.card ι) → ℝ} (hu : Antitone u)
    (heq : A.charpoly = ∏ j, (X - C (u j))) : u = hA.eigenvalues₀ := by
  have hroots : A.charpoly.roots = Finset.univ.val.map u := by
    rw [heq, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hs := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at hs
  simp only [RCLike.re_to_real, Multiset.map_id', Fin.univ_val_map, Multiset.coe_sort] at hs
  rw [List.mergeSort_of_pairwise (by
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hu.sortedGE_ofFn)] at hs
  exact List.ofFn_inj.mp hs

/-- The nonincreasing list of all real eigenvalues is continuous on the space of real symmetric
matrices, with repetition according to algebraic multiplicity. -/
theorem continuous_orderedEigenvalues :
    Continuous (fun A : {A : Matrix ι ι ℝ // A.IsHermitian} ↦ A.property.eigenvalues₀) := by
  let : FirstCountableTopology (Matrix ι ι ℝ) :=
    inferInstanceAs (FirstCountableTopology (ι → ι → ℝ))
  apply continuous_iff_seqContinuous.mpr
  intro A A₀ hA
  let e := fun n ↦ (A n).property.eigenvalues₀
  change Tendsto e atTop (𝓝 A₀.property.eigenvalues₀)
  let R : ℝ := 1 + ∑ a : ι, ∑ b : ι, ‖A₀.val a b‖
  have hbound (a b : ι) : ∀ᶠ n in atTop, ‖(A n).val a b‖ ≤ R := by
    have hab : ‖A₀.val a b‖ < R := by
      have ha := Finset.single_le_sum (f := fun a : ι ↦ ∑ b : ι, ‖A₀.val a b‖)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ a)
      have hb := Finset.single_le_sum (f := fun b : ι ↦ ‖A₀.val a b‖)
        (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ b)
      exact (hb.trans ha).trans_lt (lt_add_of_pos_left _ zero_lt_one)
    have hcont := (continuous_subtype_val (p := fun A : Matrix ι ι ℝ ↦ A.IsHermitian)).matrix_elem a b
    exact (hcont.norm.seqContinuous hA).eventually_le_const hab
  have hbound' : ∀ᶠ n in atTop, ∀ a b : ι, ‖(A n).val a b‖ ≤ R := by
    simp_rw [Filter.eventually_all]
    exact hbound
  let M := Fintype.card ι * R
  have hcomp : IsCompact (Set.pi Set.univ (fun _ : Fin (Fintype.card ι) ↦ Set.Icc (-M) M)) :=
    isCompact_univ_pi fun _ ↦ isCompact_Icc
  refine hcomp.tendsto_nhds_of_unique_mapClusterPt ?_ ?_
  · filter_upwards [hbound'] with n hn j _
    exact abs_le.mp (by simpa [Real.norm_eq_abs, M] using
      norm_eigenvalues₀_le_row_max (A n).property j hn)
  · intro u _ hu
    obtain ⟨φ, hφ, hφu⟩ := hu.tendsto_subseq
    have hcoord (j : Fin (Fintype.card ι)) : Tendsto (fun n ↦ e (φ n) j) atTop (𝓝 (u j)) :=
      (continuous_apply j).continuousAt.tendsto.comp hφu
    refine orderedFactors_identify A₀.property ?_ ?_
    · intro i j hij
      exact le_of_tendsto_of_tendsto' (hcoord j) (hcoord i)
        fun n ↦ (A (φ n)).property.eigenvalues₀_antitone hij
    · apply Polynomial.funext
      intro t
      simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      have hdet : Tendsto (fun n ↦ (A (φ n)).val.charpoly.eval t) atTop
          (𝓝 (A₀.val.charpoly.eval t)) := by
        simp only [Matrix.eval_charpoly]
        exact ((by fun_prop : Continuous (fun A : {A : Matrix ι ι ℝ // A.IsHermitian} ↦
          (Matrix.scalar ι t - A.val).det)).seqContinuous hA).comp hφ.tendsto_atTop
      have hprod : Tendsto (fun n ↦ ∏ j, (t - e (φ n) j)) atTop (𝓝 (∏ j, (t - u j))) :=
        tendsto_finsetProd Finset.univ fun j _ ↦ tendsto_const_nhds.sub (hcoord j)
      have hpoint (n : ℕ) : (A (φ n)).val.charpoly.eval t = ∏ j, (t - e (φ n) j) := by
        rw [charpoly_eq_orderedFactors (A (φ n)).property]
        simp [Polynomial.eval_prod, e]
      exact tendsto_nhds_unique (hdet.congr hpoint) hprod

/-- The ordered eigenvalues indexed directly by `Fin k` for a `k × k` symmetric matrix. -/
noncomputable def orderedEigenvaluesFin {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.IsHermitian) (j : Fin k) : ℝ :=
  hA.eigenvalues₀ (Fin.cast (Fintype.card_fin k).symm j)

theorem orderedEigenvaluesFin_nonneg {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosSemidef) (j : Fin k) : 0 ≤ orderedEigenvaluesFin hA.isHermitian j := by
  simpa [orderedEigenvaluesFin, Matrix.IsHermitian.eigenvalues] using
    hA.eigenvalues_nonneg
      ((Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (Fintype.card_fin k).symm j))

theorem orderedEigenvaluesFin_pos {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosDef) (j : Fin k) : 0 < orderedEigenvaluesFin hA.isHermitian j := by
  simpa [orderedEigenvaluesFin, Matrix.IsHermitian.eigenvalues] using
    (hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA)
      ((Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (Fintype.card_fin k).symm j))

@[simp]
theorem orderedEigenvaluesFin_zero {k : ℕ} (h : (0 : Matrix (Fin k) (Fin k) ℝ).IsHermitian)
    (j : Fin k) : orderedEigenvaluesFin h j = 0 := by
  simpa [orderedEigenvaluesFin, Matrix.IsHermitian.eigenvalues] using
    congrFun (h.eigenvalues_eq_zero_iff.mpr rfl)
      ((Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (Fintype.card_fin k).symm j))

/-- Nonnegative scaling preserves the common order of the eigenvalues, including multiplicities. -/
theorem orderedEigenvaluesFin_smul_nonneg {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.IsHermitian) {a : ℝ} (ha : 0 ≤ a) (hs : (a • A).IsHermitian) (j : Fin k) :
    orderedEigenvaluesFin hs j = a * orderedEigenvaluesFin hA j := by
  let U := hA.eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℝ _ U
  have hd : C (diagonal (fun i ↦ a * hA.eigenvalues i)) = a • A := by
    have hdiag : diagonal (fun i ↦ a * hA.eigenvalues i) = a • diagonal hA.eigenvalues := by
      ext i j
      by_cases h : i = j <;> simp [h, smul_eq_mul]
    rw [hdiag, map_smul]
    exact congrArg (a • ·) hA.spectral_theorem.symm
  have hchar : (a • A).charpoly = ∏ i, (X - Polynomial.C (a * hA.eigenvalues i)) := by
    conv_lhs => rw [← hd, Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
    simp [Matrix.charpoly_diagonal]
  have hchar' : (a • A).charpoly = ∏ i, (X - Polynomial.C (a * hA.eigenvalues₀ i)) := by
    rw [hchar, ← Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin k))))]
    simp [Matrix.IsHermitian.eigenvalues]
  have heq := orderedFactors_identify hs
    (u := fun i ↦ a * hA.eigenvalues₀ i)
    (fun _ _ hij ↦ mul_le_mul_of_nonneg_left (hA.eigenvalues₀_antitone hij) ha) hchar'
  exact (congrFun heq (Fin.cast (Fintype.card_fin k).symm j)).symm

variable {k ℓ : ℕ}

/-- The row Gram matrix of the paper's `k × ℓ` block is symmetric. -/
theorem rowGram_isHermitian (B : Matrix (Fin k) (Fin ℓ) ℝ) : (B * Bᵀ).IsHermitian := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_conjTranspose_self B

/-- All `k` eigenvalues of `B Bᵀ`, in nonincreasing order, including zeros. -/
noncomputable def gramEigenvalues (B : Matrix (Fin k) (Fin ℓ) ℝ) : Fin k → ℝ :=
  orderedEigenvaluesFin (rowGram_isHermitian B)

/-- The full ordered spectrum of the row Gram matrix depends continuously on the block. -/
theorem continuous_gramEigenvalues :
    Continuous (gramEigenvalues (k := k) (ℓ := ℓ)) := by
  have hgram : Continuous (fun B : Matrix (Fin k) (Fin ℓ) ℝ ↦
      (⟨B * Bᵀ, rowGram_isHermitian B⟩ : {A : Matrix (Fin k) (Fin k) ℝ // A.IsHermitian})) :=
    (continuous_id.matrix_mul continuous_id.matrix_transpose).subtype_mk _
  exact continuous_pi fun j ↦ (continuous_apply (Fin.cast (Fintype.card_fin k).symm j)).comp
    (continuous_orderedEigenvalues.comp hgram)

theorem gramEigenvalues_nonneg (B : Matrix (Fin k) (Fin ℓ) ℝ) (j : Fin k) :
    0 ≤ gramEigenvalues B j := by
  simpa [gramEigenvalues, orderedEigenvaluesFin, Matrix.IsHermitian.eigenvalues] using
    Matrix.eigenvalues_self_mul_conjTranspose_nonneg B
      ((Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (Fintype.card_fin k).symm j))

theorem gramEigenvalues_antitone (B : Matrix (Fin k) (Fin ℓ) ℝ) :
    Antitone (gramEigenvalues B) := by
  intro i j hij
  exact (rowGram_isHermitian B).eigenvalues₀_antitone hij

/-- The least eigenvalue of the row Gram matrix when `k > 0`. -/
noncomputable def gramMinEigenvalue (B : Matrix (Fin k) (Fin ℓ) ℝ) (hk : 0 < k) : ℝ :=
  gramEigenvalues B ⟨k - 1, by omega⟩

theorem gramMinEigenvalue_le (B : Matrix (Fin k) (Fin ℓ) ℝ) (hk : 0 < k) (j : Fin k) :
    gramMinEigenvalue B hk ≤ gramEigenvalues B j :=
  gramEigenvalues_antitone B (show j.val ≤ k - 1 by omega)

theorem continuous_gramMinEigenvalue (hk : 0 < k) :
    Continuous (fun B : Matrix (Fin k) (Fin ℓ) ℝ ↦ gramMinEigenvalue B hk) :=
  (continuous_apply _).comp continuous_gramEigenvalues

end SketchOrientation
