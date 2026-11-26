import SketchOrientation.GaussianChaosKernel
import SketchOrientation.GaussianChaosSplit
import Mathlib.Analysis.InnerProductSpace.GramMatrix

namespace SketchOrientation

open MeasureTheory Matrix
open scoped Matrix InnerProductSpace

variable {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] [Fintype ι]

/-- Matrix quadratic form of a real kernel on a finite family of parameters. -/
def kernelQuadratic (M : Matrix ι ι ℝ) (a : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * (M i j * a j)

private theorem kernelQuadratic_eq (M : Matrix ι ι ℝ) (a : ι → ℝ) :
    kernelQuadratic M a = a ⬝ᵥ (M *ᵥ a) := by
  simp [kernelQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]

private theorem kernelQuadratic_sub (M N : Matrix ι ι ℝ) (a : ι → ℝ) :
    kernelQuadratic (M - N) a = kernelQuadratic M a - kernelQuadratic N a := by
  simp_rw [kernelQuadratic, Matrix.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]

private theorem kernelQuadratic_smul (c : ℝ) (M : Matrix ι ι ℝ) (a : ι → ℝ) :
    kernelQuadratic (c • M) a = c * kernelQuadratic M a := by
  simp only [kernelQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem kernelQuadratic_nonneg {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (a : ι → ℝ) :
    0 ≤ kernelQuadratic M a := by
  rw [kernelQuadratic_eq, ← star_trivial a]
  exact hM.dotProduct_mulVec_nonneg a

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem kernelQuadratic_gram (u : ι → E) (a : ι → ℝ) :
    kernelQuadratic (Matrix.gram ℝ u) a = ‖∑ i, a i • u i‖ ^ 2 := by
  conv_lhs => rw [kernelQuadratic_eq, ← star_trivial a, Matrix.star_dotProduct_gram_mulVec]
  simp only [star_trivial, real_inner_self_eq_norm_sq]

private theorem integral_kernelQuadratic {μ : Measure Ω} {M : Ω → Matrix ι ι ℝ}
    (hM : ∀ i j, Integrable (fun ω => M ω i j) μ) (a : ι → ℝ) :
    (∫ ω, kernelQuadratic (M ω) a ∂μ) =
      kernelQuadratic (Matrix.of fun i j => ∫ ω, M ω i j ∂μ) a := by
  have hi (i j : ι) : Integrable (fun ω => a i * (M ω i j * a j)) μ :=
    ((hM i j).mul_const _).const_mul _
  simp only [kernelQuadratic, Matrix.of_apply]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul, integral_mul_const]

private theorem integrable_kernelQuadratic {μ : Measure Ω} {M : Ω → Matrix ι ι ℝ}
    (hM : ∀ i j, Integrable (fun ω => M ω i j) μ) (a : ι → ℝ) :
    Integrable (fun ω => kernelQuadratic (M ω) a) μ :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((hM i j).mul_const _).const_mul _

omit [MeasurableSpace E] [BorelSpace E] [Fintype ι] in
private theorem gram_split_sub (S : Submodule ℝ E) (u : ι → E) :
    Matrix.gram ℝ u - Matrix.gram ℝ (S.starProjection ∘ u) =
      Matrix.gram ℝ (Sᗮ.starProjection ∘ u) := by
  ext i j
  have h := S.orthogonalDecomposition.inner_map_map (u i) (u j)
  simp only [WithLp.prod_inner_apply, S.orthogonalDecomposition_apply] at h
  simp only [Matrix.sub_apply, Matrix.gram_apply, Function.comp_apply, Submodule.starProjection_apply]
  change inner ℝ (u i) (u j) -
    inner ℝ (S.orthogonalProjectionOnto (u i)) (S.orthogonalProjectionOnto (u j)) =
    inner ℝ (Sᗮ.orthogonalProjectionOnto (u i)) (Sᗮ.orthogonalProjectionOnto (u j))
  exact sub_eq_of_eq_add' h.symm

/-- Averaging over orthogonal projections preserves the centered exponential
kernel bound, on every finite family of generating parameters. -/
theorem gaussianProjection_expKernel_average (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ E)
    (hS : ∀ u : E, Measurable (fun ω => (S ω).starProjection u))
    (ρ : ℝ) (hρ : ∀ u : E, (∫ ω, ‖(S ω).starProjection u‖ ^ 2 ∂μ) ≤ ρ * ‖u‖ ^ 2)
    (u : ι → E) (a : ι → ℝ) :
    (∫ ω, kernelQuadratic (Matrix.of fun i j =>
      Real.exp (inner ℝ ((S ω).starProjection (u i)) ((S ω).starProjection (u j))) - 1) a ∂μ) ≤
      ρ * kernelQuadratic (Matrix.of fun i j => Real.exp (inner ℝ (u i) (u j)) - 1) a := by
  let A := Matrix.gram ℝ u
  let B := fun ω => Matrix.gram ℝ ((S ω).starProjection ∘ u)
  let L := Matrix.of fun i j => expm1Div (A i j)
  let C := fun M : Matrix ι ι ℝ => Matrix.of fun i j => Real.exp (M i j) - 1
  let Bmean := Matrix.of fun i j => ∫ ω, B ω i j ∂μ
  have hA : A.PosSemidef := Matrix.posSemidef_gram ℝ u
  have hBnd (ω : Ω) (i j : ι) : ‖B ω i j‖ ≤ ‖u i‖ * ‖u j‖ := by
    exact (norm_inner_le_norm _ _).trans (mul_le_mul
      ((S ω).norm_starProjection_apply_le (u i))
      ((S ω).norm_starProjection_apply_le (u j)) (norm_nonneg _) (norm_nonneg _))
  have hBMeas (i j : ι) : Measurable (fun ω => B ω i j) :=
    (continuous_inner (𝕜 := ℝ) (E := E)).measurable.comp ((hS (u i)).prodMk (hS (u j)))
  have hBInt (i j : ι) : Integrable (fun ω => B ω i j) μ :=
    (integrable_const (‖u i‖ * ‖u j‖)).mono' (hBMeas i j).aestronglyMeasurable
      (ae_of_all _ fun ω => hBnd ω i j)
  have hCInt (i j : ι) : Integrable (fun ω => C (B ω) i j) μ := by
    apply (integrable_const (Real.exp (‖u i‖ * ‖u j‖) + 1)).mono'
    · exact ((hBMeas i j).exp.sub_const _).aestronglyMeasurable
    · filter_upwards [] with ω
      change ‖Real.exp (B ω i j) - 1‖ ≤ _
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      gcongr
      exact (le_abs_self _).trans (hBnd ω i j)
  have hLInt (i j : ι) : Integrable (fun ω => (L ⊙ B ω) i j) μ :=
    (hBInt i j).const_mul _
  have hmean : (ρ • A - Bmean).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
    · ext i j
      simp only [conjTranspose_apply, star_trivial, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, Bmean, Matrix.of_apply]
      have h1 : A j i = A i j := by simpa using hA.isHermitian.apply i j
      have h2 (ω : Ω) : B ω j i = B ω i j := by
        exact real_inner_comm _ _
      simp_rw [h1, h2]
    · rw [star_trivial, ← kernelQuadratic_eq, kernelQuadratic_sub, kernelQuadratic_smul,
        ← integral_kernelQuadratic hBInt v]
      simp only [A, B, kernelQuadratic_gram, Function.comp_apply, ← map_smul, ← map_sum]
      exact sub_nonneg.mpr (hρ _)
  have hbound (ω : Ω) : kernelQuadratic (C (B ω)) a ≤ kernelQuadratic (L ⊙ B ω) a := by
    apply sub_nonneg.mp
    rw [← kernelQuadratic_sub]
    exact kernelQuadratic_nonneg (posSemidef_exponential_compress_first hA
      (Matrix.posSemidef_gram ℝ _) (by rw [gram_split_sub]; exact Matrix.posSemidef_gram ℝ _)) a
  have hweighted : kernelQuadratic (L ⊙ Bmean) a ≤ ρ * kernelQuadratic (C A) a := by
    apply sub_nonneg.mp
    rw [← kernelQuadratic_smul, ← kernelQuadratic_sub]
    have heq : ρ • C A - L ⊙ Bmean = L ⊙ (ρ • A - Bmean) := by
      have hLA : C A = L ⊙ A := (expm1Div_hadamard_self A).symm
      rw [hLA]
      ext i j
      simp only [Matrix.sub_apply, hadamard_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact kernelQuadratic_nonneg ((posSemidef_expm1Div_gram hA).hadamard hmean) a
  change (∫ ω, kernelQuadratic (C (B ω)) a ∂μ) ≤ _
  refine (integral_mono (integrable_kernelQuadratic hCInt a)
    (integrable_kernelQuadratic hLInt a) hbound).trans ?_
  rw [integral_kernelQuadratic hLInt a]
  have he : (Matrix.of fun i j => ∫ ω, (L ⊙ B ω) i j ∂μ) = L ⊙ Bmean := by
    ext i j
    simp [hadamard_apply, Bmean, integral_const_mul]
  rw [he]
  exact hweighted

end SketchOrientation
