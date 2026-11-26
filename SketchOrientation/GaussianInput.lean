import SketchOrientation.GaussianGramLaw

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix

/-- Equivalent coordinate-product description of the primitive matrix law.
Each factor is the scalar standard Gaussian and the factors range over every
row and every column. -/
theorem gaussianMatrixLaw_eq_coordinate_product (d k : ℕ) :
    gaussianMatrixLaw d k =
      (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 1))).map
      (fun X => Matrix.of (fun (i : Fin d) (j : Fin k) => X j i)) := by
  let f := fun (X : Fin k → Fin d → ℝ) (j : Fin k) => WithLp.toLp 2 (X j)
  have hf : Measurable f := by
    refine measurable_pi_iff.mpr fun j => ?_
    exact (WithLp.measurable_toLp _ _).comp (measurable_pi_apply j)
  have he := Measure.pi_map_pi
    (μ := fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 1))
    (f := fun _ : Fin k => (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)))
    (fun _ => (WithLp.measurable_toLp _ _).aemeasurable)
  change (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 1))).map f =
    _ at he
  simp_rw [map_pi_eq_stdGaussian] at he
  unfold gaussianMatrixLaw
  change (Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d)))).map
    matrixOfGaussianColumns = _
  rw [← he, Measure.map_map measurable_matrixOfGaussianColumns hf]
  rfl

end SketchOrientation
