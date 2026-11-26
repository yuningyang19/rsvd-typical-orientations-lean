import TypicalOrientations.BCLMPolyEnergy

namespace TypicalOrientations

open Matrix MvPolynomial

noncomputable section

variable {n d : ℕ}

/-- Right translation by R is a degree-preserving substitution. -/
def polynomialRightTranslate (R : Matrix (Fin n) (Fin n) ℝ) (p : RotationPolynomial n) :
    RotationPolynomial n :=
  aeval (rightVectorComponent R) p

theorem polynomialRightTranslate_totalDegree (R : Matrix (Fin n) (Fin n) ℝ)
    (p : RotationPolynomial n) : (polynomialRightTranslate R p).totalDegree ≤ p.totalDegree := by
  have hMon (s : RotationCoordinate n →₀ ℕ) (a : ℝ) :
      (polynomialRightTranslate R (monomial s a)).totalDegree ≤ s.sum (fun _ e => e) := by
    simp only [polynomialRightTranslate, monomial_eq, map_mul, aeval_C,
      MvPolynomial.algebraMap_eq, Finsupp.prod, map_prod, map_pow, aeval_X, Finsupp.sum]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (totalDegree_pow _ _).trans (by
      have h := rightVectorComponent_totalDegree R i
      simpa using Nat.mul_le_mul_left (s i) h)
  conv_lhs => rw [polynomialRightTranslate, p.as_sum, map_sum]
  exact totalDegree_finsetSum_le fun s hs => (hMon s _).trans (le_totalDegree hs)

theorem rotationEval_polynomialRightTranslate (R A : Matrix (Fin n) (Fin n) ℝ)
    (p : RotationPolynomial n) :
    rotationEval (polynomialRightTranslate R p) A = rotationEval p (A * R) := by
  let f : RotationCoordinate n → ℝ := fun ij => A ij.1 ij.2
  let g : RotationCoordinate n → ℝ := fun ij => (A * R) ij.1 ij.2
  change ((aeval f).comp (aeval (rightVectorComponent R))) p = aeval g p
  have he : (aeval f).comp (aeval (rightVectorComponent R)) = aeval g := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X]
    exact rotationEval_rightVectorComponent R A i
  rw [he]

private def rightTranslatePolynomialFunction (R : SO n) (f : polynomialSpace n d) :
    polynomialSpace n d := by
  refine ⟨⟨fun U => f.val (U * R), f.val.continuous.comp (continuous_id.mul continuous_const)⟩, ?_⟩
  obtain ⟨p, hp, he⟩ := exists_polynomialRepresentative f
  refine ⟨polynomialRightTranslate R.val p,
    (mem_restrictTotalDegree (m := d) (RotationCoordinate n) _).mpr
      ((polynomialRightTranslate_totalDegree R.val p).trans hp), ?_⟩
  ext U
  change rotationEval (polynomialRightTranslate R.val p) U.val = f.val (U * R)
  rw [rotationEval_polynomialRightTranslate]
  exact congrArg (fun F : C(SO n, ℝ) => F (U * R)) he

/-- Right translations stay in the same finite-dimensional polynomial space. -/
def onSOtranslation (R : SO n) : polynomialSpace n d →ₗ[ℝ] polynomialSpace n d where
  toFun := rightTranslatePolynomialFunction R
  map_add' f g := by ext U; rfl
  map_smul' a f := by ext U; rfl

@[simp] theorem onSOtranslation_apply (R : SO n) (f : polynomialSpace n d) (U : SO n) :
    (onSOtranslation R f).val U = f.val (U * R) := rfl

def soPolyL2translation (R : SO n) : soPolyL2 n d →ₗ[ℝ] soPolyL2 n d :=
  (soPolyToL2 n d).toLinearMap.comp
    ((onSOtranslation R).comp (soPolyToL2 n d).symm.toLinearMap)

@[simp] theorem soPolyCont_translation (R : SO n) (x : soPolyL2 n d) (U : SO n) :
    soPolyCont n d (soPolyL2translation R x) U = soPolyCont n d x (U * R) := by
  change soPolyCont n d (soPolyToL2 n d (onSOtranslation R ((soPolyToL2 n d).symm x))) U = _
  rw [soPolyCont_toL2]
  rfl

theorem soPolyCont_eval_injective :
    Function.Injective (fun x : soPolyL2 n d => soPolyCont n d x) := by
  intro x y h
  apply (soPolyToL2 n d).symm.injective
  apply Subtype.ext
  exact h

theorem conjugateDirection_skew (R : SO n) (L : Matrix (Fin n) (Fin n) ℝ)
    (hL : Lᵀ = -L) : (R.valᵀ * L * R.val)ᵀ = -(R.valᵀ * L * R.val) := by
  simp [transpose_mul, hL, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem rotationExponential_conjugate (R : SO n) (L : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    rotationExponential (R.valᵀ * L * R.val) t = R.valᵀ * rotationExponential L t * R.val := by
  have hRinv : R.val⁻¹ = R.valᵀ := Matrix.inv_eq_left_inv (SO.orthogonal R)
  have hr : IsUnit R.val := (Matrix.isUnit_iff_isUnit_det _).mpr (by simp [SO.det_eq_one])
  unfold rotationExponential
  rw [← hRinv, ← Matrix.exp_conj' R.val _ hr]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul]

private theorem soExponential_mul_eq_conjugate (R : SO n) (L : Matrix (Fin n) (Fin n) ℝ)
    (hL : Lᵀ = -L) (t : ℝ) :
    soExponential L hL t * R = R *
      soExponential (R.valᵀ * L * R.val) (conjugateDirection_skew R L hL) t := by
  apply Subtype.ext
  change rotationExponential L t * R.val = R.val * rotationExponential (R.valᵀ * L * R.val) t
  rw [rotationExponential_conjugate, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_eq_one_comm.mp (SO.orthogonal R), Matrix.one_mul]

theorem onSOdirection_translation (R : SO n) (L : Matrix (Fin n) (Fin n) ℝ)
    (hL : Lᵀ = -L) (f : polynomialSpace n d) :
    onSOdirection L hL d (onSOtranslation R f) =
      onSOtranslation R (onSOdirection (R.valᵀ * L * R.val) (conjugateDirection_skew R L hL) d f) := by
  apply Subtype.ext
  ext U
  let K := R.valᵀ * L * R.val
  let hK := conjugateDirection_skew R L hL
  have h₁ := hasDerivAt_onSOdirection L hL (onSOtranslation R f) U 0
  have h₂ := hasDerivAt_onSOdirection K hK f (U * R) 0
  have he : (fun s => (onSOtranslation R f).val (U * soExponential L hL s)) =
      (fun s => f.val ((U * R) * soExponential K hK s)) := by
    funext s
    simp only [onSOtranslation_apply, mul_assoc, K, hK, soExponential_mul_eq_conjugate]
  rw [he] at h₁
  simpa only [soExponential_zero, mul_one, onSOtranslation_apply, K, hK] using h₁.unique h₂

theorem soPolyL2direction_translation (R : SO n) (L : Matrix (Fin n) (Fin n) ℝ)
    (hL : Lᵀ = -L) (x : soPolyL2 n d) :
    soPolyL2direction L hL (soPolyL2translation R x) =
      soPolyL2translation R (soPolyL2direction (R.valᵀ * L * R.val)
        (conjugateDirection_skew R L hL) x) := by
  simp only [soPolyL2direction, soPolyL2translation, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [onSOdirection_translation]

end

end TypicalOrientations
