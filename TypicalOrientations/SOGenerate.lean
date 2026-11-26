import TypicalOrientations.SOCompact
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TypicalOrientations

open Matrix Real
open scoped Matrix

noncomputable section

variable {n : ℕ}

private def pairIndex (i j : Fin n) : Fin 2 → Fin n := ![i, j]

private theorem pairIndex_injective {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (pairIndex i j) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [pairIndex, Ne.symm hij]

private abbrev PlaneComplement (i j : Fin n) :=
  {a : Fin n // a ∉ Set.range (pairIndex i j)}

private def planeIndex (i j : Fin n) (hij : i ≠ j) :
    (Fin 2 ⊕ PlaneComplement i j) ≃ Fin n := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective _ (pairIndex_injective hij)) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range (pairIndex i j)))

private theorem planeIndex_left {i j : Fin n} (hij : i ≠ j) (a : Fin 2) :
    planeIndex i j hij (.inl a) = pairIndex i j a := rfl

private theorem planeIndex_right {i j : Fin n} (hij : i ≠ j) (a : PlaneComplement i j) :
    planeIndex i j hij (.inr a) = a.val := rfl

private def rotationBlock (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ; sin θ, cos θ]

private theorem rotationBlock_orthogonal (θ : ℝ) :
    (rotationBlock θ)ᵀ * rotationBlock θ = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotationBlock, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem rotationBlock_det (θ : ℝ) : (rotationBlock θ).det = 1 := by
  rw [rotationBlock, Matrix.det_fin_two_of]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Positive-angle coordinate plane rotation in the ordered coordinates (i,j). -/
def planeRotation (i j : Fin n) (hij : i ≠ j) (θ : ℝ) : SO n := by
  classical
  let e := planeIndex i j hij
  let B := Matrix.fromBlocks (rotationBlock θ) 0 0
    (1 : Matrix (PlaneComplement i j) (PlaneComplement i j) ℝ)
  refine ⟨B.submatrix e.symm e.symm, SO.mem_iff.mpr ⟨?_, ?_⟩⟩
  · rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
    have hB : Bᵀ * B = 1 := by
      simp [B, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, rotationBlock_orthogonal,
        Matrix.fromBlocks_one]
    rw [hB, Matrix.submatrix_one_equiv]
  · rw [Matrix.det_submatrix_equiv_self]
    simp [B, rotationBlock_det]

private theorem planeRotation_mulVec_eq {i j : Fin n} (hij : i ≠ j)
    (θ : ℝ) (x : Fin n → ℝ) :
    (planeRotation i j hij θ).val *ᵥ x =
      (Sum.elim (rotationBlock θ *ᵥ (x ∘ pairIndex i j))
        (fun a : PlaneComplement i j => x a.val)) ∘ (planeIndex i j hij).symm := by
  classical
  let e := planeIndex i j hij
  let B := Matrix.fromBlocks (rotationBlock θ) 0 0
    (1 : Matrix (PlaneComplement i j) (PlaneComplement i j) ℝ)
  change B.submatrix e.symm e.symm *ᵥ x = _
  rw [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec]
  simp only [Equiv.symm_symm, Matrix.zero_mulVec, zero_add, add_zero, Matrix.one_mulVec]
  rfl

theorem planeRotation_mulVec_fst {i j : Fin n} (hij : i ≠ j) (θ : ℝ) (x : Fin n → ℝ) :
    ((planeRotation i j hij θ).val *ᵥ x) i = cos θ * x i - sin θ * x j := by
  have h : (planeIndex i j hij).symm i = .inl 0 := by
    apply (planeIndex i j hij).injective
    simp [planeIndex_left, pairIndex]
  rw [planeRotation_mulVec_eq hij θ x]
  simp [h, rotationBlock, dotProduct, Fin.sum_univ_two, pairIndex, sub_eq_add_neg]

theorem planeRotation_mulVec_snd {i j : Fin n} (hij : i ≠ j) (θ : ℝ) (x : Fin n → ℝ) :
    ((planeRotation i j hij θ).val *ᵥ x) j = sin θ * x i + cos θ * x j := by
  have h : (planeIndex i j hij).symm j = .inl 1 := by
    apply (planeIndex i j hij).injective
    simp [planeIndex_left, pairIndex]
  rw [planeRotation_mulVec_eq hij θ x]
  simp [h, rotationBlock, dotProduct, Fin.sum_univ_two, pairIndex]

theorem planeRotation_mulVec_other {i j a : Fin n} (hij : i ≠ j)
    (ha : a ≠ i) (hb : a ≠ j) (θ : ℝ) (x : Fin n → ℝ) :
    ((planeRotation i j hij θ).val *ᵥ x) a = x a := by
  have hn : a ∉ Set.range (pairIndex i j) := by
    rintro ⟨b, rfl⟩
    fin_cases b <;> simp_all [pairIndex]
  have h : (planeIndex i j hij).symm a = .inr ⟨a, hn⟩ := by
    apply (planeIndex i j hij).injective
    simp [planeIndex_right]
  rw [planeRotation_mulVec_eq hij θ x]
  simp [h]

private def skewBlock : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The tangent generator of a positive-angle coordinate plane rotation. -/
def planeSkew (i j : Fin n) (hij : i ≠ j) : Matrix (Fin n) (Fin n) ℝ :=
  let e := (planeIndex i j hij).symm
  (fromBlocks skewBlock 0 0
    (0 : Matrix (PlaneComplement i j) (PlaneComplement i j) ℝ)).submatrix e e

theorem planeSkew_transpose (i j : Fin n) (hij : i ≠ j) :
    (planeSkew i j hij)ᵀ = -planeSkew i j hij := by
  have h : skewBlockᵀ = -skewBlock := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [skewBlock]
  rw [planeSkew, transpose_submatrix, fromBlocks_transpose, h]
  ext a b
  let e := (planeIndex i j hij).symm
  change fromBlocks (-skewBlock) 0 0 0 (e a) (e b) =
    -fromBlocks skewBlock 0 0 0 (e a) (e b)
  cases e a <;> cases e b <;> simp

@[simp] theorem planeRotation_zero (i j : Fin n) (hij : i ≠ j) :
    planeRotation i j hij 0 = 1 := by
  have h : rotationBlock 0 = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [rotationBlock, Matrix.one_apply]
  apply Subtype.ext
  change (fromBlocks (rotationBlock 0) 0 0
    (1 : Matrix (PlaneComplement i j) (PlaneComplement i j) ℝ)).submatrix
      (planeIndex i j hij).symm (planeIndex i j hij).symm = 1
  rw [h, fromBlocks_one, submatrix_one_equiv]

section

open scoped Matrix.Norms.Operator

private def derivativeBlock (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-sin θ, -cos θ; cos θ, -sin θ]

private theorem rotationBlock_mul_skewBlock (θ : ℝ) :
    rotationBlock θ * skewBlock = derivativeBlock θ := by
  rw [rotationBlock, skewBlock, Matrix.mul_fin_two]
  simp [derivativeBlock]

theorem hasDerivAt_planeRotation (i j : Fin n) (hij : i ≠ j) (θ : ℝ) :
    HasDerivAt (fun t => (planeRotation i j hij t).val)
      ((planeRotation i j hij θ).val * planeSkew i j hij) θ := by
  let e := (planeIndex i j hij).symm
  let D := fromBlocks (derivativeBlock θ) 0 0
    (0 : Matrix (PlaneComplement i j) (PlaneComplement i j) ℝ)
  have hM : (planeRotation i j hij θ).val * planeSkew i j hij = D.submatrix e e := by
    change (fromBlocks (rotationBlock θ) 0 0
      (1 : Matrix (PlaneComplement i j) (PlaneComplement i j) ℝ)).submatrix e e *
        (fromBlocks skewBlock 0 0 0).submatrix e e = _
    rw [submatrix_mul_equiv, fromBlocks_multiply]
    simp [D, rotationBlock_mul_skewBlock]
  rw [hM]
  have hEntry (a b : Fin n) :
      HasDerivAt (fun t => (planeRotation i j hij t).val a b) (D.submatrix e e a b) θ := by
    change HasDerivAt (fun t =>
        fromBlocks (rotationBlock t) 0 0
          (1 : Matrix (PlaneComplement i j) (PlaneComplement i j) ℝ) (e a) (e b))
      (D (e a) (e b)) θ
    cases e a with
    | inl a =>
      cases e b with
      | inr b => exact hasDerivAt_const θ (0 : ℝ)
      | inl b =>
        change HasDerivAt (fun t => rotationBlock t a b) (derivativeBlock θ a b) θ
        fin_cases a <;> fin_cases b <;>
          first | exact hasDerivAt_cos θ | exact (hasDerivAt_sin θ).neg | exact hasDerivAt_sin θ
    | inr a =>
      cases e b with
      | inl b => exact hasDerivAt_const θ (0 : ℝ)
      | inr b => exact hasDerivAt_const θ ((1 : Matrix (PlaneComplement i j) (PlaneComplement i j) ℝ) a b)
  let assemble : (Fin n → Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := Matrix.of, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  have hRaw : HasDerivAt (fun t => fun a b => (planeRotation i j hij t).val a b)
      (fun a b => D.submatrix e e a b) θ :=
    hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mpr fun b => hEntry a b
  exact assemble.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ hRaw

/-- The Givens rotation is the exponential of its coordinate skew generator. -/
theorem planeRotation_val_eq_exp (i j : Fin n) (hij : i ≠ j) (θ : ℝ) :
    (planeRotation i j hij θ).val = NormedSpace.exp (θ • planeSkew i j hij) := by
  let L := planeSkew i j hij
  let P := fun t => (planeRotation i j hij t).val
  let E := fun t : ℝ => NormedSpace.exp (t • (-L))
  let F := fun t => P t * E t
  have hF (t : ℝ) : HasDerivAt F 0 t := by
    have hComm : Commute L (E t) := (((Commute.refl L).neg_right).smul_right t).exp_right
    have hP : HasDerivAt P (P t * L) t := hasDerivAt_planeRotation i j hij t
    have hE : HasDerivAt E (E t * (-L)) t := hasDerivAt_exp_smul_const (-L) t
    have H := hP.mul hE
    have hzero : P t * L * E t + P t * (E t * -L) = 0 := by
      simp [Matrix.mul_assoc, hComm.eq]
    rw [hzero] at H
    exact H
  have hc := is_const_of_deriv_eq_zero (fun t => (hF t).differentiableAt)
    (fun t => (hF t).deriv) θ 0
  have h0 : F 0 = 1 := by simp [F, P, E, NormedSpace.exp_zero]
  have hInv : E θ * NormedSpace.exp (θ • L) = 1 := by
    have hComm : Commute (θ • -L) (θ • L) :=
      (((Commute.refl L).neg_left).smul_left θ).smul_right θ
    change NormedSpace.exp (θ • -L) * NormedSpace.exp (θ • L) = 1
    rw [← Matrix.exp_add_of_commute _ _ hComm, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
  calc
    P θ = P θ * (E θ * NormedSpace.exp (θ • L)) := by rw [hInv, mul_one]
    _ = F θ * NormedSpace.exp (θ • L) := (mul_assoc _ _ _).symm
    _ = NormedSpace.exp (θ • L) := by rw [hc, h0, one_mul]

end

/-- The coordinate plane rotations in a fixed dimension. -/
def planeRotationGenerators (n : ℕ) : Set (SO n) :=
  {U | ∃ (i j : Fin n) (hij : i ≠ j) (θ : ℝ), planeRotation i j hij θ = U}

private abbrev generatedSO (n : ℕ) : Subgroup (SO n) :=
  Subgroup.closure (planeRotationGenerators n)

theorem planeRotation_mem_closure (i j : Fin n) (hij : i ≠ j) (θ : ℝ) :
    planeRotation i j hij θ ∈ Subgroup.closure (planeRotationGenerators n) :=
  Subgroup.subset_closure ⟨i, j, hij, θ, rfl⟩

private theorem exists_angle_annihilate_snd (a b : ℝ) :
    ∃ θ : ℝ, sin θ * a + cos θ * b = 0 := by
  let z : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have hre : z.re = a := by simp [z, Complex.mul_re]
  have him : z.im = b := by simp [z, Complex.mul_im]
  by_cases hz : z = 0
  · have hb : b = 0 := by rw [← him, hz, Complex.zero_im]
    exact ⟨0, by simp [hb]⟩
  · refine ⟨-z.arg, ?_⟩
    rw [sin_neg, cos_neg, Complex.sin_arg, Complex.cos_arg hz, hre, him]
    ring

private theorem zero_coordinates (i : Fin n) (s : Finset (Fin n)) (x : Fin n → ℝ) :
    i ∉ s →
    ∃ R ∈ generatedSO n, ∀ a ∈ s, (R.val *ᵥ x) a = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨1, Subgroup.one_mem _, by simp⟩
  | @insert j s hjs ih =>
    intro hi
    have hji : i ≠ j := fun h => hi (by simp [h])
    have his : i ∉ s := fun h => hi (Finset.mem_insert_of_mem h)
    obtain ⟨R, hR, hZ⟩ := ih his
    let y := R.val *ᵥ x
    obtain ⟨θ, hθ⟩ := exists_angle_annihilate_snd (y i) (y j)
    let T := planeRotation i j hji θ
    refine ⟨T * R, Subgroup.mul_mem _ (planeRotation_mem_closure i j hji θ) hR, ?_⟩
    intro a ha
    change ((T.val * R.val) *ᵥ x) a = 0
    rw [← Matrix.mulVec_mulVec]
    change (T.val *ᵥ y) a = 0
    rcases Finset.mem_insert.mp ha with rfl | hs
    · rw [planeRotation_mulVec_snd hji, hθ]
    · have h₁ : a ≠ i := fun h => his (h ▸ hs)
      have h₂ : a ≠ j := fun h => hjs (h ▸ hs)
      rw [planeRotation_mulVec_other hji h₁ h₂]
      exact hZ a hs

private theorem first_column_reduction (U : SO (n + 2)) :
    ∃ R ∈ generatedSO (n + 2), ∀ a : Fin (n + 2),
      (R * U).val a 0 = if a = 0 then 1 else 0 := by
  classical
  let x : Fin (n+2) → ℝ := fun a => U.val a 0
  let S : Finset (Fin (n+2)) := Finset.univ.erase 0
  obtain ⟨R, hR, hZ⟩ := zero_coordinates 0 S x (by simp [S])
  let y : Fin (n+2) → ℝ := R.val *ᵥ x
  have hy (a : Fin (n+2)) : y a = (R * U).val a 0 := rfl
  have hY (a : Fin (n+2)) (ha : a ≠ 0) : y a = 0 :=
    hZ a (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩)
  have hNorm : (∑ a : Fin (n+2), y a ^ 2) = 1 := by
    have hh := congrArg (fun B : Matrix (Fin (n+2)) (Fin (n+2)) ℝ => B 0 0)
      (R * U).orthogonal
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at hh
    simp only [hy, pow_two, hh]
  have hSingle : y 0 ^ 2 = 1 := by
    rw [Finset.sum_eq_single (0 : Fin (n+2))
      (fun a _ ha => by simp [hY a ha]) (by simp)] at hNorm
    exact hNorm
  have hSign : y 0 = 1 ∨ y 0 = -1 := by
    have hd : (y 0 - 1) * (y 0 + 1) = 0 := by nlinarith
    exact (mul_eq_zero.mp hd).imp (by intro h; linarith) (by intro h; linarith)
  rcases hSign with hp | hm
  · refine ⟨R, hR, fun a => ?_⟩
    rw [← hy]
    by_cases ha : a = 0
    · simp [ha, hp]
    · simp [ha, hY a ha]
  · have h01 : (0 : Fin (n+2)) ≠ 1 := Fin.zero_ne_one
    let T := planeRotation (0 : Fin (n+2)) 1 h01 π
    refine ⟨T * R, Subgroup.mul_mem _ (planeRotation_mem_closure _ _ h01 π) hR, fun a => ?_⟩
    change (((T.val * R.val) * U.val) a 0) = _
    rw [Matrix.mul_assoc]
    change (T.val *ᵥ y) a = _
    by_cases h0 : a = 0
    · subst a
      rw [planeRotation_mulVec_fst h01]
      simp [hm]
    · by_cases h1 : a = 1
      · subst a
        rw [planeRotation_mulVec_snd h01]
        simp [h0, hY 1 h0]
      · rw [planeRotation_mulVec_other h01 h0 h1, hY a h0, if_neg h0]

private def headTailIndex (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (.inl 0) (fun a => .inr a)
  left_inv := by
    intro a
    rcases a with a | a
    · have ha : a = 0 := Subsingleton.elim _ _
      simp [ha]
    · rfl
  right_inv := by
    intro a
    refine Fin.cases ?_ (fun _ => ?_) a <;> rfl

private theorem headTailIndex_inl (i : Fin 1) : headTailIndex n (.inl i) = 0 := rfl

private theorem headTailIndex_inr (i : Fin n) : headTailIndex n (.inr i) = i.succ := rfl

private def blockHead (B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
  fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 B

private def embedSOHead (n : ℕ) : SO n →* SO (n + 1) where
  toFun U := by
    let e := (headTailIndex n).symm
    refine ⟨(blockHead U.val).submatrix e e, SO.mem_iff.mpr ⟨?_, ?_⟩⟩
    · rw [transpose_submatrix, submatrix_mul_equiv]
      have hB : (blockHead U.val)ᵀ * blockHead U.val = 1 := by
        simp [blockHead, fromBlocks_transpose, fromBlocks_multiply, U.orthogonal, fromBlocks_one]
      rw [hB, submatrix_one_equiv]
    · rw [det_submatrix_equiv_self]
      simp [blockHead, U.det_eq_one]
  map_one' := by
    apply Subtype.ext
    change (blockHead (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix
      (headTailIndex n).symm (headTailIndex n).symm = 1
    rw [blockHead, fromBlocks_one, submatrix_one_equiv]
  map_mul' U V := by
    apply Subtype.ext
    change (blockHead (U.val * V.val)).submatrix (headTailIndex n).symm (headTailIndex n).symm =
      (blockHead U.val).submatrix (headTailIndex n).symm (headTailIndex n).symm *
      (blockHead V.val).submatrix (headTailIndex n).symm (headTailIndex n).symm
    rw [submatrix_mul_equiv]
    simp [blockHead, fromBlocks_multiply]

private theorem embedSOHead_mulVec (U : SO n) (x : Fin (n + 1) → ℝ) :
    (embedSOHead n U).val *ᵥ x = Fin.cases (x 0) (U.val *ᵥ (x ∘ Fin.succ)) := by
  let e := (headTailIndex n).symm
  change (blockHead U.val).submatrix e e *ᵥ x = _
  rw [submatrix_mulVec_equiv, blockHead, fromBlocks_mulVec]
  funext a
  refine Fin.cases ?_ (fun i => ?_) a
  · simp [e, headTailIndex, Function.comp_apply]
  · simp [e, headTailIndex, Function.comp_apply]
    rfl

private theorem embedSOHead_planeRotation (i j : Fin n) (hij : i ≠ j) (θ : ℝ) :
    embedSOHead n (planeRotation i j hij θ) =
      planeRotation i.succ j.succ (Fin.succ_injective _ |>.ne hij) θ := by
  let h := Fin.succ_injective n |>.ne hij
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro b
  let x : Fin (n + 1) → ℝ := Pi.single b 1
  change (embedSOHead n (planeRotation i j hij θ)).val *ᵥ x =
    (planeRotation i.succ j.succ h θ).val *ᵥ x
  rw [embedSOHead_mulVec]
  funext a
  refine Fin.cases ?_ (fun k => ?_) a
  · rw [Fin.cases_zero, planeRotation_mulVec_other h (Fin.succ_ne_zero i).symm
      (Fin.succ_ne_zero j).symm]
  · rw [Fin.cases_succ]
    by_cases hi : k = i
    · subst k
      rw [planeRotation_mulVec_fst hij, planeRotation_mulVec_fst h]
      rfl
    · by_cases hj : k = j
      · subst k
        rw [planeRotation_mulVec_snd hij, planeRotation_mulVec_snd h]
        rfl
      · rw [planeRotation_mulVec_other hij hi hj,
          planeRotation_mulVec_other h (Fin.succ_injective n |>.ne hi)
            (Fin.succ_injective n |>.ne hj)]
        rfl

private theorem exists_embedSOHead_of_fstCol (B : SO (n + 1))
    (hCol : ∀ a : Fin (n+1), B.val a 0 = if a = 0 then 1 else 0) :
    ∃ T : SO n, embedSOHead n T = B := by
  have hRow (a : Fin n) : B.val 0 a.succ = 0 := by
    have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M 0 a.succ)
      B.orthogonal
    change (∑ i : Fin (n+1), B.val i 0 * B.val i a.succ) = _ at h
    simpa [hCol, Matrix.one_apply, Ne.symm (Fin.succ_ne_zero a)] using h
  let e := headTailIndex n
  let T := B.val.submatrix Fin.succ Fin.succ
  have hB : B.val.submatrix e e = blockHead T := by
    ext (i | i) (j | j)
    · have hij : i = j := Subsingleton.elim _ _
      simp [e, blockHead, headTailIndex_inl, hCol, hij]
    · simp [e, blockHead, headTailIndex_inl, headTailIndex_inr, hRow]
    · simp [e, blockHead, headTailIndex_inl, headTailIndex_inr, hCol, Fin.succ_ne_zero]
    · simp [e, blockHead, headTailIndex_inr, T]
  have hDet : T.det = 1 := by
    have h := B.det_eq_one
    rw [← det_submatrix_equiv_self e, hB] at h
    simpa [blockHead] using h
  have hOrt : Tᵀ * T = 1 := by
    have h : (B.val.submatrix e e)ᵀ * B.val.submatrix e e = 1 := by
      rw [transpose_submatrix, submatrix_mul_equiv, B.orthogonal, submatrix_one_equiv]
    rw [hB] at h
    have he := congrArg
      (fun C : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ => C.toBlocks₂₂) h
    simpa [blockHead, fromBlocks_transpose, fromBlocks_multiply, ← fromBlocks_one] using he
  let U : SO n := ⟨T, SO.mem_iff.mpr ⟨hOrt,hDet⟩⟩
  refine ⟨U, ?_⟩
  apply Subtype.ext
  change (blockHead T).submatrix e.symm e.symm = B.val
  rw [← hB, submatrix_submatrix]
  simp

private theorem embedSOHead_mem_closure (U : SO n) (hU : U ∈ generatedSO n) :
    embedSOHead n U ∈ generatedSO (n + 1) := by
  have h : generatedSO n ≤ (generatedSO (n + 1)).comap (embedSOHead n) := by
    apply (Subgroup.closure_le _).mpr
    rintro V ⟨i, j, hij, θ, rfl⟩
    change embedSOHead n (planeRotation i j hij θ) ∈ generatedSO (n + 1)
    rw [embedSOHead_planeRotation]
    exact planeRotation_mem_closure _ _ _ _
  exact h hU

private theorem all_mem_generatedSO : ∀ n, ∀ U : SO n, U ∈ generatedSO n := by
  apply Nat.twoStepInduction
  · intro U
    have h : U = 1 := Subtype.ext (Subsingleton.elim _ _)
    rw [h]
    exact Subgroup.one_mem _
  · intro U
    have h : U = 1 := by
      apply Subtype.ext
      have hD := U.det_eq_one
      rw [Matrix.det_fin_one] at hD
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      simpa [hi, hj] using hD
    rw [h]
    exact Subgroup.one_mem _
  · intro n _ ih U
    obtain ⟨R, hR, hCol⟩ := first_column_reduction U
    obtain ⟨T, hT⟩ := exists_embedSOHead_of_fstCol (R * U) hCol
    have hRT : R * U ∈ generatedSO (n + 2) :=
      hT ▸ embedSOHead_mem_closure T (ih T)
    simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ hR) hRT

/-- Every special orthogonal matrix is generated by coordinate plane rotations. -/
theorem closure_planeRotationGenerators (n : ℕ) :
    Subgroup.closure (planeRotationGenerators n) = ⊤ :=
  top_unique (fun U _ => all_mem_generatedSO n U)

/-- Invariance under right multiplication by every coordinate plane rotation
already makes a function constant on the whole group. -/
theorem eq_const_of_right_invariant_planeRotations {α : Type*} (f : SO n → α)
    (hF : ∀ (i j : Fin n) (hij : i ≠ j) (θ : ℝ) (U : SO n),
      f (U * planeRotation i j hij θ) = f U) (U : SO n) : f U = f 1 := by
  let S : Subgroup (SO n) :=
    { carrier := {R | ∀ V : SO n, f (V * R) = f V}
      mul_mem' := by
        intro A B hA hB V
        rw [← mul_assoc, hB (V * A), hA V]
      one_mem' := by simp
      inv_mem' := by
        intro A hA V
        simpa [mul_assoc] using (hA (V * A⁻¹)).symm }
  have h := (Subgroup.closure_le S).2 (show planeRotationGenerators n ⊆ S by
    rintro R ⟨i, j, hij, θ, rfl⟩
    exact hF i j hij θ)
  have hU : U ∈ S := h (all_mem_generatedSO n U)
  simpa only [one_mul] using hU (1 : SO n)

end

end TypicalOrientations
