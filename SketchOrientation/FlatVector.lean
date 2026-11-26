import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Field.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace SketchOrientation

open Set

/-- The cube-section argument used to select each column of the frame in
Theorem 6.2. The normalization is the Euclidean one. -/
theorem exists_flat_unit_vector {ι : Type*} [Fintype ι] (E : Submodule ℝ (ι → ℝ))
    (hE : 0 < Module.finrank ℝ E) :
    ∃ v : ι → ℝ, v ∈ E ∧ (∑ i, v i ^ 2) = 1 ∧
      ∀ i, |v i| ≤ (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹ := by
  classical
  let cube : Set (ι → ℝ) := {x | ∀ i, x i ∈ Icc (-1) 1}
  let sectionSet : Set (ι → ℝ) := (E : Set (ι → ℝ)) ∩ cube
  have hcub : IsCompact cube := by
    exact isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hcompact : IsCompact sectionSet := hcub.inter_left E.closed_of_finiteDimensional
  have hnempty : sectionSet.Nonempty := ⟨0, E.zero_mem, by
    intro i
    change (-1 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1
    norm_num⟩
  obtain ⟨x, hx⟩ := hcompact.extremePoints_nonempty hnempty
  obtain ⟨⟨hxE, hxC⟩, hextreme⟩ := mem_extremePoints_iff_left.mp hx
  have hcoord (i : ι) : |x i| ≤ 1 :=
    abs_le.mpr (hxC i)
  let active : ι → Prop := fun i => |x i| = 1
  let read : E →ₗ[ℝ] ({i // active i} → ℝ) :=
    { toFun := fun z i => z.val i.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective read := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hz0 (i : ι) (hi : active i) : z.val i = 0 :=
      congrFun (LinearMap.mem_ker.mp hz) ⟨i, hi⟩
    have hlt (i : ι) : (if active i then 0 else |x i|) < (1 : ℝ) := by
      split_ifs with hi
      · norm_num
      · exact lt_of_le_of_ne (hcoord i) hi
    obtain ⟨ε, hε, heps⟩ := Pi.exists_forall_pos_add_lt
      (x := fun i => if active i then (0 : ℝ) else |x i|) (y := fun _ => 1) hlt
    let M : ℝ := 1 + ∑ i, |z.val i|
    have hM : 0 < M := by
      dsimp [M]
      positivity
    let t := ε / M
    have ht : 0 < t := div_pos hε hM
    have ht_bound (i : ι) : |t * z.val i| ≤ ε := by
      have hi : |z.val i| ≤ M := by
        have := Finset.single_le_sum (f := fun j => |z.val j|)
          (fun j _ => abs_nonneg (z.val j)) (Finset.mem_univ i)
        dsimp [M]
        linarith
      rw [abs_mul, abs_of_pos ht]
      calc
        t * |z.val i| ≤ t * M := mul_le_mul_of_nonneg_left hi ht.le
        _ = ε := div_mul_cancel₀ ε hM.ne'
    have hplus : x + t • z.val ∈ sectionSet := by
      refine ⟨E.add_mem hxE (E.smul_mem t z.property), ?_⟩
      intro i
      apply abs_le.mp
      change |x i + t * z.val i| ≤ 1
      by_cases hi : active i
      · simpa [hz0 i hi] using hcoord i
      · have he := heps i
        simp only [if_neg hi] at he
        exact (abs_add_le ..).trans (by linarith [ht_bound i])
    have hminus : x - t • z.val ∈ sectionSet := by
      refine ⟨E.sub_mem hxE (E.smul_mem t z.property), ?_⟩
      intro i
      apply abs_le.mp
      change |x i - t * z.val i| ≤ 1
      by_cases hi : active i
      · simpa [hz0 i hi] using hcoord i
      · have he := heps i
        simp only [if_neg hi] at he
        calc
          |x i - t * z.val i| ≤ |x i| + |t * z.val i| := by
            simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le (x i) (-(t * z.val i)))
          _ ≤ 1 := by linarith [ht_bound i]
    have hxeq := hextreme _ hplus _ hminus (mem_openSegment_add_sub (𝕜 := ℝ) x (t • z.val))
    apply Subtype.ext
    funext i
    have hi := congrFun hxeq i
    change x i + t * z.val i = x i at hi
    exact (mul_eq_zero.mp (by linarith : t * z.val i = 0)).resolve_left ht.ne'
  have hcard : Module.finrank ℝ E ≤ (Finset.univ.filter active).card := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype] using
      LinearMap.finrank_le_finrank_of_injective hinj
  have hs : (Module.finrank ℝ E : ℝ) ≤ ∑ i, x i ^ 2 := by
    calc
      _ ≤ ((Finset.univ.filter active).card : ℝ) := by exact_mod_cast hcard
      _ = ∑ i ∈ Finset.univ.filter active, x i ^ 2 := by
        have hconst : (∑ _i ∈ Finset.univ.filter active, (1 : ℝ)) =
            ((Finset.univ.filter active).card : ℝ) := by simp
        rw [← hconst]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : |x i| = 1 := (Finset.mem_filter.mp hi).2
        rw [← sq_abs, hi', one_pow]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        (fun _ _ _ => sq_nonneg _)
  let q := ∑ i, x i ^ 2
  have hd : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hE
  have hq : 0 < q := hd.trans_le hs
  have hr := Real.sqrt_pos.2 hq
  refine ⟨(Real.sqrt q)⁻¹ • x, E.smul_mem _ hxE, ?_, ?_⟩
  · change (∑ i, ((Real.sqrt q)⁻¹ * x i) ^ 2) = 1
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, ← show q = ∑ i, x i ^ 2 from rfl, inv_pow, Real.sq_sqrt hq.le,
      inv_mul_cancel₀ hq.ne']
  · intro i
    change |(Real.sqrt q)⁻¹ * x i| ≤ _
    rw [abs_mul, abs_of_pos (inv_pos.mpr hr)]
    calc
      _ ≤ (Real.sqrt q)⁻¹ * 1 := mul_le_mul_of_nonneg_left (hcoord i) (inv_pos.mpr hr).le
      _ ≤ _ := by
        rw [mul_one]
        exact inv_anti₀ (Real.sqrt_pos.2 hd) (Real.sqrt_le_sqrt hs)


/-- The column-by-column construction in Theorem 6.2, in a subspace of
dimension d. Column j has squared entries bounded by 1/(d-j). -/
theorem exists_flat_frame {ι : Type*} [Fintype ι] (E : Submodule ℝ (ι → ℝ))
    (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    ∃ V : Fin k → ι → ℝ, (∀ j, V j ∈ E) ∧
      (∀ j t, V j ⬝ᵥ V t = if j = t then 1 else 0) ∧
      (∀ j i, V j i ^ 2 ≤ ((Module.finrank ℝ E - j.val : ℕ) : ℝ)⁻¹) := by
  classical
  induction k with
  | zero =>
    exact ⟨Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩
  | succ j ih =>
    obtain ⟨V, hV, horth, hbound⟩ := ih (by omega)
    let pairing (t : Fin j) : E →ₗ[ℝ] ℝ :=
      { toFun := fun z => V t ⬝ᵥ z.val
        map_add' := fun _ _ => dotProduct_add _ _ _
        map_smul' := fun r z => by
          change V t ⬝ᵥ (r • z.val) = r * (V t ⬝ᵥ z.val)
          rw [dotProduct_smul]
          rfl }
    let f : E →ₗ[ℝ] (Fin j → ℝ) := LinearMap.pi pairing
    let K := f.ker.map E.subtype
    have hdim := f.finrank_range_add_finrank_ker
    have hrange : Module.finrank ℝ f.range ≤ j := by simpa using f.range.finrank_le
    have hker : Module.finrank ℝ K = Module.finrank ℝ f.ker :=
      E.finrank_map_subtype_eq f.ker
    obtain ⟨v, hvK, hnorm, hflat⟩ := exists_flat_unit_vector K (by omega)
    obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.mp hvK
    change z.val = v at hzv
    have hvE : v ∈ E := hzv ▸ z.property
    have hperp (t : Fin j) : V t ⬝ᵥ v = 0 := by
      rw [← hzv]
      exact congrFun (LinearMap.mem_ker.mp hz) t
    let W : Fin (j + 1) → ι → ℝ := fun t => Fin.lastCases v V t
    refine ⟨W, ?_, ?_, ?_⟩
    · intro t
      refine Fin.lastCases ?_ (fun u => ?_) t
      · simpa [W] using hvE
      · simpa [W] using hV u
    · intro t s
      refine Fin.lastCases ?_ (fun u => ?_) t
      · refine Fin.lastCases ?_ (fun w => ?_) s
        · simpa [W, dotProduct, pow_two] using hnorm
        · have hh : Fin.last j ≠ w.castSucc := by
            intro e
            have := congrArg Fin.val e
            exact w.isLt.ne' this
          simpa [W, hh, dotProduct_comm v (V w)] using hperp w
      · refine Fin.lastCases ?_ (fun w => ?_) s
        · have hh : u.castSucc ≠ Fin.last j := by
            intro e
            exact u.isLt.ne (congrArg Fin.val e)
          simpa [W, hh] using hperp u
        · simp [W, horth]
    · intro t i
      refine Fin.lastCases ?_ (fun u => ?_) t
      · rw [Fin.val_last]
        simp only [W, Fin.lastCases_last]
        have hdimR : (0 : ℝ) < Module.finrank ℝ K := by exact_mod_cast (show 0 < Module.finrank ℝ K by omega)
        have hleR : ((Module.finrank ℝ E - j : ℕ) : ℝ) ≤ Module.finrank ℝ K := by
          exact_mod_cast (show Module.finrank ℝ E - j ≤ Module.finrank ℝ K by omega)
        have hposR : (0 : ℝ) < ((Module.finrank ℝ E - j : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < Module.finrank ℝ E - j by omega)
        calc
          v i ^ 2 = |v i| ^ 2 := (sq_abs (v i)).symm
          _ ≤ ((Real.sqrt (Module.finrank ℝ K : ℝ))⁻¹) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hflat i) 2
          _ ≤ _ := by
            rw [inv_pow, Real.sq_sqrt hdimR.le]
            exact inv_anti₀ hposR hleR
      · simpa [W] using hbound u i


/-- Adding the squared entry bounds gives both leverage bounds in Theorem 6.2. -/
theorem exists_flat_frame_with_leverage {ι : Type*} [Fintype ι]
    (E : Submodule ℝ (ι → ℝ)) (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    ∃ V : Fin k → ι → ℝ, (∀ j, V j ∈ E) ∧
      (∀ j t, V j ⬝ᵥ V t = if j = t then 1 else 0) ∧
      (∀ i, ∑ j, V j i ^ 2 ≤ ∑ j : Fin k, ((Module.finrank ℝ E - j.val : ℕ) : ℝ)⁻¹) ∧
      (∑ j : Fin k, ((Module.finrank ℝ E - j.val : ℕ) : ℝ)⁻¹) ≤
        (k : ℝ) / ((Module.finrank ℝ E - k + 1 : ℕ) : ℝ) := by
  obtain ⟨V, hE, horth, hbound⟩ := exists_flat_frame E k hk
  refine ⟨V, hE, horth, fun i => Finset.sum_le_sum fun j _ => hbound j i, ?_⟩
  calc
    _ ≤ ∑ _j : Fin k, (((Module.finrank ℝ E - k + 1 : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro j _
      have hj := j.isLt
      apply inv_anti₀
      · positivity
      · exact_mod_cast (show Module.finrank ℝ E - k + 1 ≤ Module.finrank ℝ E - j.val by omega)
    _ = _ := by simp [div_eq_mul_inv]

end SketchOrientation
