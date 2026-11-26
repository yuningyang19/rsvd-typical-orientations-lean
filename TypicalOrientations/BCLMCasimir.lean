import TypicalOrientations.BCLMTranslation
import TypicalOrientations.BCLMSkewSpace
import TypicalOrientations.SOGenerate

namespace TypicalOrientations

open Filter Matrix MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {n d : ℕ}

abbrev skewIndex (n : ℕ) := Fin (Module.finrank ℝ (SkewFrobenius n))

def skewBasis (n : ℕ) : OrthonormalBasis (skewIndex n) ℝ (SkewFrobenius n) :=
  stdOrthonormalBasis ℝ (SkewFrobenius n)

def soDirectional (n d : ℕ) :
    SkewFrobenius n →ₗ[ℝ] (soPolyL2 n d →ₗ[ℝ] soPolyL2 n d) where
  toFun L := soPolyL2direction (skewMatrix L) (skewMatrix_transpose L)
  map_add' L K := by
    apply LinearMap.ext
    intro x
    change soPolyL2direction (skewMatrix (L + K)) _ x =
      soPolyL2direction (skewMatrix L) _ x + soPolyL2direction (skewMatrix K) _ x
    simp only [soPolyL2direction, LinearMap.comp_apply, LinearEquiv.coe_coe, ← map_add]
    apply congrArg (soPolyToL2 n d)
    apply Subtype.ext
    simp only [onSOdirection, restrictedPolynomial, map_add, polynomialDirection_add, Derivation.add_apply]
    rfl
  map_smul' a L := by
    apply LinearMap.ext
    intro x
    change soPolyL2direction (skewMatrix (a • L)) _ x =
      a • soPolyL2direction (skewMatrix L) _ x
    simp only [soPolyL2direction, LinearMap.comp_apply, LinearEquiv.coe_coe, ← map_smul]
    apply congrArg (soPolyToL2 n d)
    apply Subtype.ext
    simp only [onSOdirection, restrictedPolynomial, map_smul, polynomialDirection_smul, Derivation.smul_apply]
    rfl

def skewRotation (L : SkewFrobenius n) (t : ℝ) : SO n :=
  soExponential (skewMatrix L) (skewMatrix_transpose L) t

theorem hasDerivAt_soDirectional (L : SkewFrobenius n) (x : soPolyL2 n d)
    (U : SO n) (t : ℝ) :
    HasDerivAt (fun s => soPolyCont n d x (U * skewRotation L s))
      (soPolyCont n d (soDirectional n d L x) (U * skewRotation L t)) t := by
  let f := (soPolyToL2 n d).symm x
  have h := hasDerivAt_onSOdirection (skewMatrix L) (skewMatrix_transpose L) f U t
  change HasDerivAt (fun s => f.val (U * skewRotation L s))
    (soPolyCont n d (soPolyToL2 n d (onSOdirection (skewMatrix L) (skewMatrix_transpose L) d f))
      (U * skewRotation L t)) t
  rwa [soPolyCont_toL2]

private theorem soDirectional_skew (L : SkewFrobenius n) (x y : soPolyL2 n d) :
    ⟪soDirectional n d L x, y⟫_ℝ = -⟪x, soDirectional n d L y⟫_ℝ :=
  skew_symmetric_soPolyL2direction (skewMatrix L) (skewMatrix_transpose L) x y

/-- The Casimir operator, the sum of squared left-invariant
infinitesimal rotations in a Frobenius-orthonormal basis. -/
def casimir (n d : ℕ) : soPolyL2 n d →ₗ[ℝ] soPolyL2 n d :=
  ∑ j : skewIndex n, (soDirectional n d (skewBasis n j)).comp (soDirectional n d (skewBasis n j))

theorem casimir_apply (x : soPolyL2 n d) :
    casimir n d x = ∑ j : skewIndex n, soDirectional n d (skewBasis n j)
      (soDirectional n d (skewBasis n j) x) := by
  simp only [casimir, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]

theorem casimir_isSymmetric (n d : ℕ) : (casimir n d).IsSymmetric := by
  intro x y
  rw [casimir_apply, casimir_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  let L := skewBasis n j
  change ⟪soDirectional n d L (soDirectional n d L x), y⟫_ℝ =
    ⟪x, soDirectional n d L (soDirectional n d L y)⟫_ℝ
  rw [soDirectional_skew, soDirectional_skew, neg_neg]

theorem casimir_energy (x : soPolyL2 n d) :
    ⟪x, casimir n d x⟫_ℝ =
      -(∑ j : skewIndex n, ‖soDirectional n d (skewBasis n j) x‖ ^ 2) := by
  rw [casimir_apply, inner_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  let L := skewBasis n j
  change ⟪x, soDirectional n d L (soDirectional n d L x)⟫_ℝ =
    -‖soDirectional n d L x‖ ^ 2
  rw [← real_inner_self_eq_norm_sq, soDirectional_skew, neg_neg]

theorem casimir_nonpositive (x : soPolyL2 n d) : ⟪x, casimir n d x⟫_ℝ ≤ 0 := by
  rw [casimir_energy]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem soPolyIntegral_casimir_zero (x : soPolyL2 n d) : soPolyIntegral n d (casimir n d x) = 0 := by
  rw [casimir_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact soPolyIntegral_direction_zero _ _ _

theorem soDirectional_zero_of_casimir_zero (x : soPolyL2 n d)
    (hx : casimir n d x = 0) (L : SkewFrobenius n) :
    soDirectional n d L x = 0 := by
  have he := casimir_energy x
  rw [hx, inner_zero_right] at he
  have hz : (∑ j : skewIndex n, ‖soDirectional n d (skewBasis n j) x‖ ^ 2) = 0 := by linarith
  have hb (j : skewIndex n) : soDirectional n d (skewBasis n j) x = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      sq_nonneg ‖soDirectional n d (skewBasis n j) x‖)).mp hz j (Finset.mem_univ j)
    exact norm_eq_zero.mp (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0) |>.mp h)
  rw [← (skewBasis n).sum_repr L, map_sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply, map_smul, LinearMap.smul_apply, hb,
    smul_zero, Finset.sum_const_zero]

/-- The kernel of the Casimir on polynomial functions consists of constants,
because all right coordinate-plane rotations generate SO(n). -/
theorem soPolyCont_const_of_casimir_zero (x : soPolyL2 n d) (hx : casimir n d x = 0)
    (U : SO n) : soPolyCont n d x U = soPolyIntegral n d x := by
  let f := soPolyCont n d x
  have h (i j : Fin n) (hij : i ≠ j) (t : ℝ) (V : SO n) :
      f (V * planeRotation i j hij t) = f V := by
    let L := skewOfMatrix (planeSkew i j hij) (planeSkew_transpose i j hij)
    have hDir : soDirectional n d L x = 0 := soDirectional_zero_of_casimir_zero x hx L
    have hRot (s : ℝ) : skewRotation L s = planeRotation i j hij s := by
      apply Subtype.ext
      change rotationExponential (skewMatrix L) s = (planeRotation i j hij s).val
      dsimp only [L]
      rw [skewMatrix_skewOfMatrix]
      exact (planeRotation_val_eq_exp i j hij s).symm
    have hD (s : ℝ) : HasDerivAt (fun r => f (V * skewRotation L r)) 0 s := by
      simpa only [f, hDir, map_zero, ContinuousMap.zero_apply] using hasDerivAt_soDirectional L x V s
    have hf := is_const_of_deriv_eq_zero (fun s => (hD s).differentiableAt) (fun s => (hD s).deriv) t 0
    simpa only [hRot, planeRotation_zero, mul_one] using hf
  have hc (U : SO n) := eq_const_of_right_invariant_planeRotations f h U
  change f U = ∫ V, f V ∂soHaar n
  simp_rw [hc]
  simp

private def casimirBilinear (x : soPolyL2 n d) :
    SkewFrobenius n →ₗ[ℝ] SkewFrobenius n →ₗ[ℝ] soPolyL2 n d where
  toFun L := {
    toFun := fun K => soDirectional n d L (soDirectional n d K x)
    map_add' := by intros; simp
    map_smul' := by intros; simp }
  map_add' L K := by
    apply LinearMap.ext
    intro Q
    simp
  map_smul' a L := by
    apply LinearMap.ext
    intro Q
    simp

/-- The Casimir is unchanged by right rotation. Conjugation rotates its
orthonormal direction basis and leaves the sum of second derivatives fixed. -/
theorem casimir_translation (R : SO n) (x : soPolyL2 n d) :
    casimir n d (soPolyL2translation R x) = soPolyL2translation R (casimir n d x) := by
  let e := skewConjugate R.val (SO.orthogonal R)
  have hD (L : SkewFrobenius n) (z : soPolyL2 n d) :
      soDirectional n d L (soPolyL2translation R z) =
        soPolyL2translation R (soDirectional n d (e L) z) := by
    change soPolyL2direction (skewMatrix L) _ (soPolyL2translation R z) =
      soPolyL2translation R (soPolyL2direction (skewMatrix (e L)) _ z)
    have he : skewMatrix (e L) = R.valᵀ * skewMatrix L * R.val :=
      skewMatrix_skewConjugate R.val (SO.orthogonal R) L
    have he' (K : Matrix (Fin n) (Fin n) ℝ) (hK : Kᵀ = -K)
        (heK : K = R.valᵀ * skewMatrix L * R.val) :
        soPolyL2direction K hK z =
          soPolyL2direction (R.valᵀ * skewMatrix L * R.val)
            (conjugateDirection_skew R (skewMatrix L) (skewMatrix_transpose L)) z := by
      subst K
      rfl
    rw [he' _ _ he]
    exact soPolyL2direction_translation R (skewMatrix L) (skewMatrix_transpose L) z
  rw [casimir_apply, casimir_apply]
  simp_rw [hD]
  rw [← map_sum]
  apply congrArg (soPolyL2translation R)
  exact sum_bilinear_diagonal_linearIsometryEquiv (casimirBilinear x) (skewBasis n) e

end

end TypicalOrientations
