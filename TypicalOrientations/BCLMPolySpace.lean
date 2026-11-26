import TypicalOrientations.BCLMPolynomial
import TypicalOrientations.BCLMDirections
import TypicalOrientations.SOCompact
import Mathlib.MeasureTheory.Function.L2Space

namespace TypicalOrientations

open Matrix MvPolynomial MeasureTheory
open scoped Matrix.Norms.Operator

noncomputable section

variable {n : ℕ}

def soExponential (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) (t : ℝ) : SO n :=
  ⟨rotationExponential L t, SO.mem_iff.mpr
    ⟨rotationExponential_transpose_mul L hL t, rotationExponential_det L hL t⟩⟩

@[simp] theorem soExponential_zero (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) :
    soExponential L hL 0 = 1 := Subtype.ext (rotationExponential_zero L)

theorem continuous_soExponential (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) :
    Continuous (soExponential L hL) :=
  (continuous_rotationExponential L).subtype_mk _

theorem hasDerivAt_polynomial_rotation (p : RotationPolynomial n) (U : SO n)
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) (t : ℝ) :
    HasDerivAt (fun s => rotationEval p (U * soExponential L hL s).val)
      (rotationEval (polynomialDirection L p) (U * soExponential L hL t).val) t := by
  apply rotationEval_hasDerivAt
  intro i j
  exact hasDerivAt_matrix_entry (hasDerivAt_right_rotationExponential U.val L t) i j

/-- Evaluation of formal polynomials on the compact matrix group. -/
def polynomialOnSO (n : ℕ) : RotationPolynomial n →ₗ[ℝ] C(SO n, ℝ) where
  toFun p := ⟨fun U => rotationEval p U.val, (rotationEval_continuous p).comp continuous_subtype_val⟩
  map_add' := by
    intro p q
    ext U
    exact map_add (MvPolynomial.eval (fun ij : RotationCoordinate n => U.val ij.1 ij.2)) p q
  map_smul' := by
    intro c p
    ext U
    change (MvPolynomial.aeval (fun ij : RotationCoordinate n => U.val ij.1 ij.2)) (c • p) =
      c • (MvPolynomial.aeval (fun ij : RotationCoordinate n => U.val ij.1 ij.2)) p
    exact map_smul _ _ _

theorem polynomialOnSO_apply (p : RotationPolynomial n) (U : SO n) :
    polynomialOnSO n p U = rotationEval p U.val := rfl

/-- The finite-dimensional space of polynomial functions of degree at most d. -/
def polynomialSpace (n d : ℕ) : Submodule ℝ C(SO n, ℝ) :=
  (MvPolynomial.restrictTotalDegree (RotationCoordinate n) ℝ d).map (polynomialOnSO n)

instance polynomialSpace_finite (n d : ℕ) : Module.Finite ℝ (polynomialSpace n d) := by
  unfold polynomialSpace
  infer_instance

variable {d : ℕ}

def restrictedPolynomial (p : RotationPolynomial n) (hp : p.totalDegree ≤ d) :
    polynomialSpace n d :=
  ⟨polynomialOnSO n p, ⟨p, (MvPolynomial.mem_restrictTotalDegree (m := d) (RotationCoordinate n) p).mpr hp, rfl⟩⟩

@[simp] theorem restrictedPolynomial_apply (p : RotationPolynomial n) (hp : p.totalDegree ≤ d)
    (U : SO n) : (restrictedPolynomial p hp).val U = rotationEval p U.val := rfl

theorem exists_polynomialRepresentative (f : polynomialSpace n d) :
    ∃ p : RotationPolynomial n, p.totalDegree ≤ d ∧ polynomialOnSO n p = f.val := by
  obtain ⟨p, hp, hEq⟩ := f.property
  exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (m := d) (RotationCoordinate n) p).mp hp, hEq⟩

private def representative (f : polynomialSpace n d) : RotationPolynomial n :=
  (exists_polynomialRepresentative f).choose

private theorem representative_degree (f : polynomialSpace n d) :
    (representative f).totalDegree ≤ d :=
  (exists_polynomialRepresentative f).choose_spec.1

private theorem representative_eq (f : polynomialSpace n d) :
    polynomialOnSO n (representative f) = f.val :=
  (exists_polynomialRepresentative f).choose_spec.2

theorem polynomialDirection_eval_eq_of_polynomialOnSO_eq
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L)
    {p q : RotationPolynomial n} (h : polynomialOnSO n p = polynomialOnSO n q) :
    polynomialOnSO n (polynomialDirection L p) = polynomialOnSO n (polynomialDirection L q) := by
  ext U
  have hp := hasDerivAt_polynomial_rotation p U L hL 0
  have hq := hasDerivAt_polynomial_rotation q U L hL 0
  have he : (fun t => rotationEval p (U * soExponential L hL t).val) =
      (fun t => rotationEval q (U * soExponential L hL t).val) :=
    funext fun t => congrArg (fun F : C(SO n, ℝ) => F (U * soExponential L hL t)) h
  rw [he] at hp
  simpa only [soExponential_zero, mul_one, polynomialOnSO_apply] using hp.unique hq

/-- Lift the polynomial derivation to the space of restrictions. Its value
is independent of the representative by uniqueness of curve derivatives. -/
def onSOdirection (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) (d : ℕ) :
    polynomialSpace n d →ₗ[ℝ] polynomialSpace n d where
  toFun f := restrictedPolynomial (polynomialDirection L (representative f))
    ((polynomialDirection_totalDegree L _).trans (representative_degree f))
  map_add' f g := by
    apply Subtype.ext
    have h : polynomialOnSO n (representative (f + g)) =
        polynomialOnSO n (representative f + representative g) := by
      rw [representative_eq, map_add, representative_eq, representative_eq]
      rfl
    change polynomialOnSO n (polynomialDirection L (representative (f + g))) =
      polynomialOnSO n (polynomialDirection L (representative f)) +
        polynomialOnSO n (polynomialDirection L (representative g))
    rw [polynomialDirection_eval_eq_of_polynomialOnSO_eq L hL h, map_add, map_add]
  map_smul' a f := by
    apply Subtype.ext
    have h : polynomialOnSO n (representative (a • f)) =
        polynomialOnSO n (a • representative f) := by
      rw [representative_eq, map_smul, representative_eq]
      rfl
    change polynomialOnSO n (polynomialDirection L (representative (a • f))) =
      a • polynomialOnSO n (polynomialDirection L (representative f))
    rw [polynomialDirection_eval_eq_of_polynomialOnSO_eq L hL h, Derivation.map_smul, map_smul]

theorem onSOdirection_restricted (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L)
    (p : RotationPolynomial n) (hp : p.totalDegree ≤ d) :
    onSOdirection L hL d (restrictedPolynomial p hp) =
      restrictedPolynomial (polynomialDirection L p) ((polynomialDirection_totalDegree L _).trans hp) := by
  apply Subtype.ext
  apply polynomialDirection_eval_eq_of_polynomialOnSO_eq L hL
  exact representative_eq _

theorem hasDerivAt_onSOdirection (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L)
    (f : polynomialSpace n d) (U : SO n) (t : ℝ) :
    HasDerivAt (fun s => f.val (U * soExponential L hL s))
      ((onSOdirection L hL d f).val (U * soExponential L hL t)) t := by
  have h := hasDerivAt_polynomial_rotation (representative f) U L hL t
  change HasDerivAt (fun s => polynomialOnSO n (representative f) (U * soExponential L hL s)) _ _ at h
  rwa [representative_eq] at h

/-- The canonical faithful L² realization of the finite polynomial space. -/
def polynomialL2 (n : ℕ) :
    C(SO n, ℝ) →L[ℝ] MeasureTheory.Lp ℝ 2 (soHaar n) :=
  ContinuousMap.toLp 2 (soHaar n) ℝ

theorem polynomialL2_injective (n : ℕ) : Function.Injective (polynomialL2 n) :=
  ContinuousMap.toLp_injective (soHaar n)

end

end TypicalOrientations
