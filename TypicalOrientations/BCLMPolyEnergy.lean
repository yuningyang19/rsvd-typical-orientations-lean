import TypicalOrientations.BCLMPolySpace
import TypicalOrientations.BCLMHeatComparison

namespace TypicalOrientations

open Matrix MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {n d : ℕ}

theorem soExponential_add (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) (s t : ℝ) :
    soExponential L hL (s+t) = soExponential L hL s * soExponential L hL t :=
  Subtype.ext (rotationExponential_add L s t)

theorem continuous_soExponentialAction (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) :
    Continuous (fun z : ℝ × SO n => z.2 * soExponential L hL z.1) :=
  continuous_snd.mul ((continuous_soExponential L hL).comp continuous_fst)

private theorem integral_onSOdirection_product_zero
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) (f g : polynomialSpace n d) :
    (∫ U, (onSOdirection L hL d f).val U * g.val U +
      f.val U * (onSOdirection L hL d g).val U ∂soHaar n) = 0 := by
  let M (U : SO n) := f.val U * g.val U
  let N (U : SO n) := (onSOdirection L hL d f).val U * g.val U +
    f.val U * (onSOdirection L hL d g).val U
  let F (t : ℝ) (U : SO n) := M (U * soExponential L hL t)
  let F' (t : ℝ) (U : SO n) := N (U * soExponential L hL t)
  have hM : Continuous M := f.val.continuous.mul g.val.continuous
  have hN : Continuous N :=
    (((onSOdirection L hL d f).val.continuous).mul g.val.continuous).add
      (f.val.continuous.mul ((onSOdirection L hL d g).val.continuous))
  have hD (t : ℝ) (U : SO n) : HasDerivAt (fun s => F s U) (F' t U) t :=
    (hasDerivAt_onSOdirection L hL f U t).mul (hasDerivAt_onSOdirection L hL g U t)
  have h := hasDerivAt_integral_compact (soHaar n) F F' 0
    (hM.comp (continuous_soExponentialAction L hL)) (hN.comp (continuous_soExponentialAction L hL)) hD
  have he : (fun t => ∫ U, F t U ∂soHaar n) = fun _ : ℝ => ∫ U, M U ∂soHaar n :=
    funext fun t => integral_so_mul_right M (soExponential L hL t)
  rw [he] at h
  simpa only [F', soExponential_zero, mul_one, N] using h.unique (hasDerivAt_const 0 _)

theorem integral_onSOdirection_zero
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) (f : polynomialSpace n d) :
    (∫ U, (onSOdirection L hL d f).val U ∂soHaar n) = 0 := by
  let F (t : ℝ) (U : SO n) := f.val (U * soExponential L hL t)
  let F' (t : ℝ) (U : SO n) := (onSOdirection L hL d f).val (U * soExponential L hL t)
  have h := hasDerivAt_integral_compact (soHaar n) F F' 0
    (f.val.continuous.comp (continuous_soExponentialAction L hL))
    ((onSOdirection L hL d f).val.continuous.comp (continuous_soExponentialAction L hL))
    (fun t U => hasDerivAt_onSOdirection L hL f U t)
  have he : (fun t => ∫ U, F t U ∂soHaar n) = fun _ : ℝ => ∫ U, f.val U ∂soHaar n :=
    funext fun t => integral_so_mul_right f.val (soExponential L hL t)
  rw [he] at h
  simpa only [F', soExponential_zero, mul_one] using h.unique (hasDerivAt_const 0 _)

/-- The finite-dimensional image in Haar L². -/
abbrev soPolyL2 (n d : ℕ) :=
  LinearMap.range ((polynomialL2 n).toLinearMap.comp (polynomialSpace n d).subtype)

instance (n d : ℕ) : FiniteDimensional ℝ (soPolyL2 n d) := inferInstance

def soPolyToL2 (n d : ℕ) : polynomialSpace n d ≃ₗ[ℝ] soPolyL2 n d :=
  LinearEquiv.ofInjective _ ((polynomialL2_injective n).comp Subtype.val_injective)

def soPolyCont (n d : ℕ) : soPolyL2 n d →L[ℝ] C(SO n, ℝ) :=
  ((polynomialSpace n d).subtype.comp (soPolyToL2 n d).symm.toLinearMap).toContinuousLinearMap

@[simp] theorem soPolyCont_toL2 (f : polynomialSpace n d) :
    soPolyCont n d (soPolyToL2 n d f) = f.val := by
  change ((soPolyToL2 n d).symm ((soPolyToL2 n d) f)).val = _
  rw [LinearEquiv.symm_apply_apply]

theorem continuous_soPolyContEval :
    Continuous (fun z : soPolyL2 n d × SO n => soPolyCont n d z.1 z.2) :=
  continuous_eval.comp (((soPolyCont n d).continuous.comp continuous_fst).prodMk continuous_snd)

def soPolyL2direction (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L) :
    soPolyL2 n d →ₗ[ℝ] soPolyL2 n d :=
  (soPolyToL2 n d).toLinearMap.comp ((onSOdirection L hL d).comp (soPolyToL2 n d).symm.toLinearMap)

theorem soPolyL2_inner (f g : soPolyL2 n d) :
    ⟪f, g⟫_ℝ = ∫ U, soPolyCont n d f U * soPolyCont n d g U ∂soHaar n := by
  let w := (soPolyToL2 n d).symm f
  let v := (soPolyToL2 n d).symm g
  have hw : (soPolyToL2 n d) w = f := (soPolyToL2 n d).apply_symm_apply f
  have hv : (soPolyToL2 n d) v = g := (soPolyToL2 n d).apply_symm_apply g
  rw [← hw, ← hv, soPolyCont_toL2, soPolyCont_toL2]
  change ⟪ContinuousMap.toLp 2 (soHaar n) ℝ w.val,
    ContinuousMap.toLp 2 (soHaar n) ℝ v.val⟫_ℝ = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun U => by
    simp only [starRingEnd_apply, star_trivial]; exact mul_comm _ _

theorem skew_symmetric_soPolyL2direction (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L)
    (f g : soPolyL2 n d) :
    ⟪soPolyL2direction L hL f, g⟫_ℝ = -⟪f, soPolyL2direction L hL g⟫_ℝ := by
  rw [soPolyL2_inner, soPolyL2_inner]
  let f' := (soPolyToL2 n d).symm f
  let g' := (soPolyToL2 n d).symm g
  have h := integral_onSOdirection_product_zero L hL f' g'
  change (∫ U, soPolyCont n d (soPolyToL2 n d (onSOdirection L hL d f')) U *
    soPolyCont n d g U ∂soHaar n) =
      -(∫ U, soPolyCont n d f U *
        soPolyCont n d (soPolyToL2 n d (onSOdirection L hL d g')) U ∂soHaar n)
  rw [soPolyCont_toL2, soPolyCont_toL2]
  change (∫ U, (onSOdirection L hL d f').val U * g'.val U ∂soHaar n) =
    -(∫ U, f'.val U * (onSOdirection L hL d g').val U ∂soHaar n)
  have h1 : Integrable (fun U => (onSOdirection L hL d f').val U * g'.val U) (soHaar n) :=
    ((onSOdirection L hL d f').val.continuous.mul g'.val.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun U => f'.val U * (onSOdirection L hL d g').val U) (soHaar n) :=
    (f'.val.continuous.mul (onSOdirection L hL d g').val.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add h1 h2] at h
  linarith

def soPolyIntegral (n d : ℕ) : soPolyL2 n d →ₗ[ℝ] ℝ where
  toFun x := ∫ U, soPolyCont n d x U ∂soHaar n
  map_add' f g := by
    simp only [map_add, ContinuousMap.add_apply]
    exact integral_add
      ((soPolyCont n d f).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((soPolyCont n d g).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  map_smul' c f := by simp [ContinuousMap.smul_apply, integral_const_mul]

theorem soPolyIntegral_direction_zero (L : Matrix (Fin n) (Fin n) ℝ) (hL : Lᵀ = -L)
    (x : soPolyL2 n d) :
    soPolyIntegral n d (soPolyL2direction L hL x) = 0 := by
  change (∫ U, soPolyCont n d
    (soPolyToL2 n d ((onSOdirection L hL d) ((soPolyToL2 n d).symm x))) U ∂soHaar n) = _
  simp only [soPolyCont_toL2]
  exact integral_onSOdirection_zero L hL _

end

end TypicalOrientations
