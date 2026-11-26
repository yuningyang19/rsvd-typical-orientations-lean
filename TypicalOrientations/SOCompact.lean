import TypicalOrientations.RotationProduct
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace TypicalOrientations

open Matrix MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The real special orthogonal group, using Mathlib's matrix group. -/
abbrev SO (n : ℕ) := ↥(Matrix.specialOrthogonalGroup (Fin n) ℝ)

namespace SO

variable {n : ℕ}

theorem mem_iff {U : Matrix (Fin n) (Fin n) ℝ} :
    U ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ ↔ Uᵀ * U = 1 ∧ U.det = 1 := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff']

theorem orthogonal (U : SO n) : U.valᵀ * U.val = 1 := (mem_iff.mp U.property).1

theorem det_eq_one (U : SO n) : U.val.det = 1 := (mem_iff.mp U.property).2

@[simp] theorem val_one (n : ℕ) : (1 : SO n).val = 1 := rfl

@[simp] theorem val_mul (U V : SO n) : (U * V).val = U.val * V.val := rfl

@[simp] theorem val_inv (U : SO n) : U⁻¹.val = U.valᵀ := by
  change star U.val = U.valᵀ
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

theorem isClosed_SO (n : ℕ) :
    IsClosed (Matrix.specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) := by
  have hs : (Matrix.specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) =
      {U | Uᵀ * U = 1} ∩ {U | U.det = 1} := by
    ext U
    exact mem_iff
  rw [hs]
  exact (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const).inter
    (isClosed_eq continuous_id.matrix_det continuous_const)

theorem abs_entry_le_one (U : SO n) (i j : Fin n) : |U.val i j| ≤ 1 := by
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j j) (orthogonal U)
  have hSum : (∑ a : Fin n, U.val a j ^ 2) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, pow_two] using he
  have hi : U.val i j ^ 2 ≤ 1 := by
    rw [← hSum]
    exact Finset.single_le_sum (fun a _ => sq_nonneg (U.val a j)) (Finset.mem_univ i)
  rw [abs_le]
  constructor <;> nlinarith

instance (n : ℕ) : CompactSpace (SO n) := by
  apply isCompact_iff_compactSpace.mp
  let box : Set (Matrix (Fin n) (Fin n) ℝ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1
  have hb : IsCompact box := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hb.of_isClosed_subset (isClosed_SO n) ?_
  intro U hU
  exact Set.mem_pi.mpr fun i _ => Set.mem_pi.mpr fun j _ =>
    abs_le.mp (abs_entry_le_one (⟨U,hU⟩ : SO n) i j)

instance (n : ℕ) : IsTopologicalGroup (SO n) where
  continuous_mul := by
    apply continuous_induced_rng.2
    exact (continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply continuous_induced_rng.2
    change Continuous (fun U : SO n => (U⁻¹).val)
    simp_rw [val_inv]
    exact continuous_subtype_val.matrix_transpose

instance (n : ℕ) : SecondCountableTopology (SO n) := by
  change SecondCountableTopology {U : (Fin n → Fin n → ℝ) //
    U ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ}
  infer_instance

instance (n : ℕ) : BorelSpace (SO n) := by
  change BorelSpace {U : Matrix (Fin n) (Fin n) ℝ // U ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ}
  infer_instance

theorem measurableEmbedding_val (n : ℕ) :
    MeasurableEmbedding (Subtype.val : SO n → Matrix (Fin n) (Fin n) ℝ) :=
  MeasurableEmbedding.subtype_coe (isClosed_SO n).measurableSet

end SO

/-- Pull the folded orthogonal law back to the actual compact group. -/
def soHaar (n : ℕ) : Measure (SO n) :=
  (specialOrientationLaw n).comap Subtype.val

theorem soHaar_map_val (n : ℕ) : (soHaar n).map Subtype.val = specialOrientationLaw n := by
  rw [soHaar, (SO.measurableEmbedding_val n).map_comap]
  have hR : Set.range (Subtype.val : SO n → Matrix (Fin n) (Fin n) ℝ) =
      (Matrix.specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) := by
    ext U
    exact ⟨by rintro ⟨V, rfl⟩; exact V.property, fun h => ⟨⟨U, h⟩, rfl⟩⟩
  rw [hR]
  apply Measure.restrict_eq_self_of_ae_mem
  cases n with
  | zero =>
    apply ae_of_all
    intro U
    have hU : U = (1 : Matrix (Fin 0) (Fin 0) ℝ) := Subsingleton.elim _ _
    simp [hU]
  | succ n =>
    filter_upwards [ae_specialOrientation (Nat.succ_pos n)] with U hU
    exact SO.mem_iff.mpr hU

theorem measurePreserving_soHaar_val (n : ℕ) :
    MeasurePreserving (Subtype.val : SO n → Matrix (Fin n) (Fin n) ℝ)
      (soHaar n) (specialOrientationLaw n) :=
  ⟨(SO.measurableEmbedding_val n).measurable, soHaar_map_val n⟩

theorem integral_soHaar_val {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    (∫ U : SO n, f U.val ∂soHaar n) = ∫ U, f U ∂specialOrientationLaw n :=
  (measurePreserving_soHaar_val n).integral_comp (SO.measurableEmbedding_val n) f

instance (n : ℕ) : IsProbabilityMeasure (soHaar n) where
  measure_univ := by
    calc
      _ = ((soHaar n).map Subtype.val) Set.univ := by
        rw [Measure.map_apply (SO.measurableEmbedding_val n).measurable MeasurableSet.univ,
          Set.preimage_univ]
      _ = _ := by rw [soHaar_map_val, measure_univ]

theorem soHaar_map_mul_right {n : ℕ} (R : SO n) :
    (soHaar n).map (fun U => U * R) = soHaar n := by
  apply (SO.measurableEmbedding_val n).map_injective
  rw [Measure.map_map measurable_subtype_coe (continuous_mul_const R).measurable]
  change (soHaar n).map
    ((fun U : Matrix (Fin n) (Fin n) ℝ => U * R.val) ∘ Subtype.val) =
    (soHaar n).map Subtype.val
  have hm : Measurable (fun U : Matrix (Fin n) (Fin n) ℝ => U * R.val) :=
    (continuous_id.matrix_mul continuous_const).measurable
  rw [← Measure.map_map hm measurable_subtype_coe,
    soHaar_map_val, specialOrientationLaw_map_right R.val R.orthogonal R.det_eq_one]

instance (n : ℕ) : (soHaar n).IsMulRightInvariant :=
  ⟨soHaar_map_mul_right⟩

private theorem soHaar_inv_eq (n : ℕ) : (soHaar n).inv = soHaar n := by
  let μ := soHaar n
  let ν := μ.inv
  have : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_inv : Measurable (Inv.inv : SO n → SO n)).aemeasurable
  ext s hs
  classical
  let f : SO n → ℝ≥0∞ := s.indicator 1
  have hf : Measurable f := measurable_const.indicator hs
  have hm : Measurable (Function.uncurry fun x y : SO n => f (x * y)) :=
    hf.comp (continuous_mul : Continuous (fun p : SO n × SO n => p.1 * p.2)).measurable
  have h := lintegral_lintegral_swap (μ := μ) (ν := ν) hm.aemeasurable
  simp_rw [lintegral_mul_left_eq_self (μ := ν) f, lintegral_mul_right_eq_self (μ := μ) f,
    lintegral_const, measure_univ, mul_one, f, lintegral_indicator_one hs] at h
  exact h

instance (n : ℕ) : (soHaar n).IsMulLeftInvariant := by
  rw [← soHaar_inv_eq n]
  exact Measure.inv.instIsMulLeftInvariant

instance (n : ℕ) : (soHaar n).IsOpenPosMeasure :=
  isOpenPosMeasure_of_mulLeftInvariant_of_compact (μ := soHaar n) Set.univ isCompact_univ (by simp)

instance (n : ℕ) : (soHaar n).IsHaarMeasure where
  toIsFiniteMeasureOnCompacts := inferInstance
  toIsMulLeftInvariant := inferInstance
  toIsOpenPosMeasure := inferInstance

theorem integral_so_mul_left {n : ℕ} (f : SO n → ℝ) (R : SO n) :
    (∫ U, f (R * U) ∂soHaar n) = ∫ U, f U ∂soHaar n :=
  integral_mul_left_eq_self f R

theorem integral_so_mul_right {n : ℕ} (f : SO n → ℝ) (R : SO n) :
    (∫ U, f (U * R) ∂soHaar n) = ∫ U, f U ∂soHaar n :=
  integral_mul_right_eq_self f R

end

end TypicalOrientations
