import SketchOrientation.GaussianRadial
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

namespace SketchOrientation

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]

/-- The product of independent standard Gaussians is standard Gaussian in the
Hilbert direct sum. -/
theorem stdGaussian_hilbert_product :
    ((stdGaussian E).prod (stdGaussian F)).map (WithLp.toLp 2) =
      stdGaussian (WithLp 2 (E × F)) := by
  have : IsProbabilityMeasure (((stdGaussian E).prod (stdGaussian F)).map (WithLp.toLp 2)) :=
    Measure.isProbabilityMeasure_map (WithLp.measurable_toLp _ _).aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_prod, charFun_stdGaussian, charFun_stdGaussian, charFun_stdGaussian,
    ← Complex.exp_add]
  have hn := congrArg (fun x : ℝ => (x : ℂ)) (WithLp.prod_norm_sq_eq_of_L2 t)
  push_cast at hn
  rw [hn]
  change Complex.exp (-↑‖t.fst‖ ^ 2 / 2 + -↑‖t.snd‖ ^ 2 / 2) = _
  congr 1
  ring

/-- Orthogonal complementary projections split a standard Gaussian into two
independent standard Gaussians in the corresponding subspaces. -/
theorem stdGaussian_orthogonal_split (S : Submodule ℝ E) :
    (stdGaussian E).map (fun x => (S.orthogonalProjectionOnto x,
      Sᗮ.orthogonalProjectionOnto x)) = (stdGaussian S).prod (stdGaussian Sᗮ) := by
  let e := MeasurableEquiv.toLp 2 (S × Sᗮ)
  have h : Measurable (fun x => (S.orthogonalProjectionOnto x, Sᗮ.orthogonalProjectionOnto x)) :=
    S.orthogonalProjectionOnto.continuous.measurable.prodMk
      Sᗮ.orthogonalProjectionOnto.continuous.measurable
  apply e.measurableEmbedding.map_injective
  rw [Measure.map_map e.measurable h]
  change (stdGaussian E).map (WithLp.toLp 2 ∘ _) =
    ((stdGaussian S).prod (stdGaussian Sᗮ)).map (WithLp.toLp 2)
  have he : (WithLp.toLp 2 ∘ fun x =>
      (S.orthogonalProjectionOnto x, Sᗮ.orthogonalProjectionOnto x)) = S.orthogonalDecomposition := by
    funext x
    exact (S.orthogonalDecomposition_apply (x := x)).symm
  rw [he, stdGaussian_map, stdGaussian_hilbert_product]

/-- The two complementary observations are independent under a standard
Gaussian input. -/
theorem stdGaussian_orthogonal_split_indep (S : Submodule ℝ E) :
    IndepFun S.orthogonalProjectionOnto Sᗮ.orthogonalProjectionOnto (stdGaussian E) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map
    S.orthogonalProjectionOnto.continuous.measurable.aemeasurable
    Sᗮ.orthogonalProjectionOnto.continuous.measurable.aemeasurable,
    stdGaussian_map_projection, stdGaussian_map_projection]
  exact stdGaussian_orthogonal_split S

end SketchOrientation
