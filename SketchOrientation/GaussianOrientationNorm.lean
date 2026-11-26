import SketchOrientation.GaussianOrientationRate
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace SketchOrientation

open MeasureTheory Matrix
open scoped InnerProductSpace

variable {n ℓ : ℕ}

/-- Entrywise mean of the sketch projector in the ambient Euclidean basis. -/
noncomputable def meanSketchProjector (ν : Measure (OrthogonalProjector n ℓ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∫ P, P.val i j ∂ν

theorem integrable_sketchProjector_entry (ν : Measure (OrthogonalProjector n ℓ))
    [IsProbabilityMeasure ν] (i j : Fin n) :
    Integrable (fun P => P.val i j) ν := by
  have hm : Measurable (fun P : OrthogonalProjector n ℓ => P.val i j) :=
    (continuous_id.matrix_elem i j).measurable.comp measurable_subtype_coe
  refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [] with P
  let u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  have he : ((orientationRowSpace P).starProjection u) i = P.val i j := by
    rw [orientationRowSpace_starProjection]
    change ((toLpLin 2 2 P.val) u) i = _
    simp [u, Matrix.toLpLin_apply, EuclideanSpace.single]
  rw [← he]
  calc
    _ ≤ ‖(orientationRowSpace P).starProjection u‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖u‖ := (orientationRowSpace P).norm_starProjection_apply_le _
    _ = 1 := by simp [u, EuclideanSpace.single, PiLp.norm_single]

theorem meanSketchProjector_transpose (ν : Measure (OrthogonalProjector n ℓ)) :
    (meanSketchProjector ν)ᵀ = meanSketchProjector ν := by
  ext i j
  change (∫ P, P.val j i ∂ν) = ∫ P, P.val i j ∂ν
  exact integral_congr_ae (ae_of_all _ fun P => congrFun (congrFun P.property.1 i) j)

/-- The Rayleigh form of the mean projector is the mean squared projected norm. -/
theorem meanSketchProjector_inner (ν : Measure (OrthogonalProjector n ℓ))
    [IsProbabilityMeasure ν] (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((meanSketchProjector ν).toEuclideanLin u) u =
      ∫ P, ‖(orientationRowSpace P).starProjection u‖ ^ 2 ∂ν := by
  have hE (P : OrthogonalProjector n ℓ) :
      ‖(orientationRowSpace P).starProjection u‖ ^ 2 = inner ℝ (P.val.toEuclideanLin u) u := by
    have h := (orientationRowSpace P).re_inner_starProjection_eq_normSq u
    change inner ℝ ((orientationRowSpace P).starProjection u) u =
      ‖(orientationRowSpace P).starProjection u‖ ^ 2 at h
    rw [orientationRowSpace_starProjection] at h ⊢
    exact h.symm
  have hLin (A : Matrix (Fin n) (Fin n) ℝ) :
      inner ℝ (A.toEuclideanLin u) u = ∑ i, u i * ∑ j, A i j * u j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i, u i * star (∑ j, A i j * u j)) = _
    simp
  simp_rw [hE, hLin]
  have hI (i j : Fin n) : Integrable (fun P => P.val i j * u j) ν :=
    (integrable_sketchProjector_entry ν i j).mul_const _
  rw [integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ => hI i j).const_mul _]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_finsetSum _ fun j _ => hI i j]
  simp_rw [integral_mul_const, meanSketchProjector, Matrix.of_apply]

/-- The geometric diffuseness parameter is exactly the operator norm of
the mean sketch projector. -/
theorem meanProjectedEnergy_eq_meanSketchProjector_norm (hn : 0 < n)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] :
    meanProjectedEnergy ν orientationRowSpace =
      ‖(meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap‖ := by
  let T := (meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap
  let ρ := meanProjectedEnergy ν orientationRowSpace
  have hS : T.IsSymmetric := by
    have hAd : (meanSketchProjector ν).toEuclideanLin.adjoint =
        (meanSketchProjector ν).toEuclideanLin := by
      rw [← euclidean_transpose, meanSketchProjector_transpose]
    intro x y
    change inner ℝ ((meanSketchProjector ν).toEuclideanLin x) y =
      inner ℝ x ((meanSketchProjector ν).toEuclideanLin y)
    rw [← LinearMap.adjoint_inner_right, hAd]
  have hR (u : EuclideanSpace ℝ (Fin n)) :
      |T.rayleighQuotient u| =
        (∫ P, ‖(orientationRowSpace P).starProjection u‖ ^ 2 ∂ν) / ‖u‖ ^ 2 := by
    change |inner ℝ ((meanSketchProjector ν).toEuclideanLin u) u / ‖u‖ ^ 2| = _
    rw [meanSketchProjector_inner, abs_of_nonneg]
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)
  have hρ : 0 ≤ ρ := by
    by_contra! hneg
    have h := sketchRank_le_dim_mul_meanProjectedEnergy ν
    exact (mul_neg_of_pos_of_neg (Nat.cast_pos.mpr hn) hneg).not_ge
      ((Nat.cast_nonneg ℓ).trans h)
  change ρ = ‖T‖
  apply le_antisymm
  · apply csSup_le
    · let i : Fin n := ⟨0, hn⟩
      have hu : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by
        simp [EuclideanSpace.single, PiLp.norm_single]
      exact Set.range_nonempty_iff_nonempty.mpr ⟨⟨_, hu⟩⟩
    · rintro _ ⟨u, rfl⟩
      have h := T.rayleighQuotient_le_norm u
      simpa only [hR, u.property, one_pow, div_one] using h
  · rw [T.norm_eq_iSup_rayleighQuotient hS]
    apply ciSup_le
    intro u
    rw [hR]
    by_cases hu : u = 0
    · simp [hu, hρ]
    · exact (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu))).2
        (projectedEnergy_le_meanProjectedEnergy ν orientationRowSpace
          measurable_orientationRowSpace_projection u)

end SketchOrientation
