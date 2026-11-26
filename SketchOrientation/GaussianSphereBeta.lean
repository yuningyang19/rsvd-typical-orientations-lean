import SketchOrientation.GaussianBetaMoments
import SketchOrientation.GaussianChaosSplit
import SketchOrientation.GaussianHaarColumnSchur

namespace SketchOrientation

open Matrix MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Normalize a Gaussian direction, using zero at the null exceptional point. -/
noncomputable def sphereNormalize (x : E) : E := ‖x‖⁻¹ • x

theorem measurable_sphereNormalize : Measurable (@sphereNormalize E _ _) :=
  (measurable_id.norm.inv).smul measurable_id

theorem stdGaussian_norm_sq_map_finrank (h : 0 < Module.finrank ℝ E) :
    (stdGaussian E).map (fun x => ‖x‖ ^ 2) = chiSquareLaw (Module.finrank ℝ E) := by
  let e := (stdOrthonormalBasis ℝ E).repr
  have he := stdGaussian_map e
  have hcomp : (fun x : E => ‖x‖ ^ 2) = (fun y : EuclideanSpace ℝ _ => ‖y‖ ^ 2) ∘ e := by
    funext x
    simp [e]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), he, stdGaussian_norm_sq_map h]

/-- Projection energy of the normalized spherical direction has the exact
beta law with shapes set by the two orthogonal block dimensions. -/
theorem stdGaussian_sphere_projected_sq_beta (R : Submodule ℝ E)
    (hr : 0 < Module.finrank ℝ R) (hs : 0 < Module.finrank ℝ Rᗮ) :
    (stdGaussian E).map (fun x => ‖R.starProjection (sphereNormalize x)‖ ^ 2) =
      betaMeasure ((Module.finrank ℝ R : ℝ) / 2) ((Module.finrank ℝ Rᗮ : ℝ) / 2) := by
  let X := fun x : E => (R.orthogonalProjectionOnto x, Rᗮ.orthogonalProjectionOnto x)
  let B := fun p : R × Rᗮ => (‖p.1‖ ^ 2, ‖p.2‖ ^ 2)
  let F := fun p : ℝ × ℝ => p.1 / (p.1 + p.2)
  have hX : Measurable X := R.orthogonalProjectionOnto.continuous.measurable.prodMk
    Rᗮ.orthogonalProjectionOnto.continuous.measurable
  have hB : Measurable B := by fun_prop
  have hF : Measurable F := by fun_prop
  have hX' : (stdGaussian E).map X = (stdGaussian R).prod (stdGaussian Rᗮ) :=
    stdGaussian_orthogonal_split R
  have hB' : ((stdGaussian R).prod (stdGaussian Rᗮ)).map B =
      (chiSquareLaw (Module.finrank ℝ R)).prod (chiSquareLaw (Module.finrank ℝ Rᗮ)) := by
    change ((stdGaussian R).prod (stdGaussian Rᗮ)).map
      (Prod.map (fun x : R => ‖x‖ ^ 2) (fun y : Rᗮ => ‖y‖ ^ 2)) = _
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      stdGaussian_norm_sq_map_finrank hr, stdGaussian_norm_sq_map_finrank hs]
  have he : (fun x => ‖R.starProjection (sphereNormalize x)‖ ^ 2) = F ∘ B ∘ X := by
    funext x
    change ‖R.starProjection (‖x‖⁻¹ • x)‖ ^ 2 =
      ‖R.orthogonalProjectionOnto x‖ ^ 2 /
        (‖R.orthogonalProjectionOnto x‖ ^ 2 + ‖Rᗮ.orthogonalProjectionOnto x‖ ^ 2)
    rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), mul_pow,
      ← Submodule.norm_sq_eq_add_norm_sq_projection x R, inv_pow, mul_comm, ← div_eq_mul_inv]
    rfl
  rw [he, ← Measure.map_map hF (hB.comp hX), ← Measure.map_map hB hX, hX', hB']
  exact gamma_ratio_law (half_pos (Nat.cast_pos.mpr hr)) (half_pos (Nat.cast_pos.mpr hs))
    (by norm_num)

end Sphere

variable {n k ℓ : ℕ}

theorem starProjection_comap_subtype {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (R S : Submodule ℝ E) (hRS : R ≤ S) (u : S) :
    ((R.comap S.subtype).starProjection u : E) = R.starProjection (u : E) := by
  apply Eq.symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ((R.comap S.subtype).orthogonalProjectionOnto u).property
  · intro w hw
    let w' : S := ⟨w, hRS hw⟩
    have hw' : w' ∈ R.comap S.subtype := hw
    have h := (R.comap S.subtype).sub_starProjection_mem_orthogonal u _ hw'
    exact h

set_option maxHeartbeats 900000 in
/-- In the conditional frame construction, the squared Schur residual
has the beta law with the manuscript's conditional dimensions. -/
theorem gaussianHaarColumn_schur_beta (P : OrthogonalProjector n ℓ) (hℓn : ℓ < n)
    (hkℓ : k < ℓ) (W : Matrix (Fin n) (Fin k) ℝ) (hW : Wᵀ * W = 1)
    (hPW : Function.Injective (P.val * W).mulVec) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map
      (fun x => ‖(schurSketchProjector P W).toEuclideanLin (haarCompletionColumn W x)‖ ^ 2) =
      betaMeasure (((ℓ - k : ℕ) : ℝ) / 2) (((n - ℓ : ℕ) : ℝ) / 2) := by
  let S := W.toEuclideanLin.rangeᗮ
  let R := (schurSketchProjector P W).toEuclideanLin.range
  let R' := R.comap S.subtype
  have hRS : R ≤ S := schurSketchProjector_range_le_orthogonal P W
  have hr : Module.finrank ℝ R' = ℓ - k := by
    rw [(Submodule.comapSubtypeEquivOfLe hRS).finrank_eq, ← rank_eq_finrank_euclidean]
    exact schurSketchProjector_rank P W hPW
  have hs : Module.finrank ℝ S = n - k := finrank_orthonormalFrame_complement W hW
  have hs' : Module.finrank ℝ R'ᗮ = n - ℓ := by
    have h := R'.finrank_add_finrank_orthogonal
    rw [hr, hs] at h
    omega
  let F := fun u : S => ‖R'.starProjection (sphereNormalize u)‖ ^ 2
  let X := S.orthogonalProjectionOnto
  have hf : Measurable F :=
    (R'.starProjection.continuous.measurable.comp measurable_sphereNormalize).norm.pow_const _
  have he : (fun x => ‖(schurSketchProjector P W).toEuclideanLin (haarCompletionColumn W x)‖ ^ 2) =
      F ∘ X := by
    funext x
    unfold F
    rw [schurSketchProjector_eq_projection]
    have hp := starProjection_comap_subtype R S hRS (sphereNormalize (X x))
    have he' : (↑(sphereNormalize (E := S) (X x)) : EuclideanSpace ℝ (Fin n)) = haarCompletionColumn W x := by
      simp only [sphereNormalize, haarCompletionColumn, haarResidualColumn_eq_projection W hW]
      rfl
    rw [← he', ← hp]
    rfl
  rw [he, ← Measure.map_map hf X.continuous.measurable, stdGaussian_map_projection]
  have h := stdGaussian_sphere_projected_sq_beta R' (by omega) (by omega)
  rw [hr, hs'] at h
  exact h

end SketchOrientation
