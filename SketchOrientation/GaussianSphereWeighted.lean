import SketchOrientation.GaussianSphereIsotropy

namespace SketchOrientation

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

section Product

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]

theorem integrable_weighted_sphere_prod_left (w : ℝ × ℝ → ℝ)
    (hw : Measurable w)
    (hI : Integrable (fun p : E × F => w (‖p.1‖ ^ 2, ‖p.2‖ ^ 2))
      ((stdGaussian E).prod (stdGaussian F))) (u : E) :
    Integrable (fun p : E × F =>
      w (‖p.1‖ ^ 2, ‖p.2‖ ^ 2) * (inner ℝ u (sphereNormalize p.1)) ^ 2)
      ((stdGaussian E).prod (stdGaussian F)) := by
  have hm : Measurable (fun p : E × F => w (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)) :=
    hw.comp ((measurable_fst.norm.pow_const (2 : ℕ)).prodMk (measurable_snd.norm.pow_const (2 : ℕ)))
  have h₂ : Measurable (fun p : E × F => (inner ℝ u (sphereNormalize p.1)) ^ 2) :=
    (measurable_sphere_inner_sq u).comp measurable_fst
  refine (hI.norm.mul_const (‖u‖ ^ 2)).mono' (hm.mul h₂).aestronglyMeasurable ?_
  filter_upwards [] with p
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (sphere_inner_sq_le u p.1) (norm_nonneg _)

/-- The first independent spherical factor remains isotropic under a weight
that depends on both Gaussian lengths. -/
theorem integral_weighted_sphere_prod_left (hE : 0 < Module.finrank ℝ E) (w : ℝ × ℝ → ℝ)
    (hw : Measurable w)
    (hI : Integrable (fun p : E × F => w (‖p.1‖ ^ 2, ‖p.2‖ ^ 2))
      ((stdGaussian E).prod (stdGaussian F))) (u : E) :
    (∫ p : E × F, w (‖p.1‖ ^ 2, ‖p.2‖ ^ 2) * (inner ℝ u (sphereNormalize p.1)) ^ 2
      ∂(stdGaussian E).prod (stdGaussian F)) =
      (‖u‖ ^ 2 / (Module.finrank ℝ E : ℝ)) *
        ∫ p : E × F, w (‖p.1‖ ^ 2, ‖p.2‖ ^ 2) ∂(stdGaussian E).prod (stdGaussian F) := by
  have h := integrable_weighted_sphere_prod_left w hw hI u
  rw [integral_prod_symm _ h, integral_prod_symm _ hI, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hI.prod_left_ae] with y hy
  have hw' : Measurable (fun t => w (t, ‖y‖ ^ 2)) :=
    hw.comp (measurable_id.prodMk measurable_const)
  exact integral_radial_weighted_sphere_inner_sq hE (fun t => w (t, ‖y‖ ^ 2)) hw' hy u

/-- The same weighted moment for the second independent spherical factor. -/
theorem integral_weighted_sphere_prod_right (hF : 0 < Module.finrank ℝ F) (w : ℝ × ℝ → ℝ)
    (hw : Measurable w)
    (hI : Integrable (fun p : E × F => w (‖p.1‖ ^ 2, ‖p.2‖ ^ 2))
      ((stdGaussian E).prod (stdGaussian F))) (u : F) :
    (∫ p : E × F, w (‖p.1‖ ^ 2, ‖p.2‖ ^ 2) * (inner ℝ u (sphereNormalize p.2)) ^ 2
      ∂(stdGaussian E).prod (stdGaussian F)) =
      (‖u‖ ^ 2 / (Module.finrank ℝ F : ℝ)) *
        ∫ p : E × F, w (‖p.1‖ ^ 2, ‖p.2‖ ^ 2) ∂(stdGaussian E).prod (stdGaussian F) := by
  have hW : Measurable (w ∘ Prod.swap) := hw.comp measurable_swap
  have h : Integrable (fun p : F × E => (w ∘ Prod.swap) (‖p.1‖ ^ 2, ‖p.2‖ ^ 2))
      ((stdGaussian F).prod (stdGaussian E)) := hI.swap
  have h' := integral_weighted_sphere_prod_left hF (w ∘ Prod.swap) hW h u
  simp only [Function.comp_apply, Prod.swap_prod_mk] at h'
  rw [← integral_prod_swap, ← integral_prod_swap (f := fun p : E × F => w (‖p.1‖ ^ 2, ‖p.2‖ ^ 2))]
  exact h'

end Product

end SketchOrientation
