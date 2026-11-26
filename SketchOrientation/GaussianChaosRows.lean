import SketchOrientation.GaussianChaosContraction
import SketchOrientation.GaussianGramLaw

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace

section Energy

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]

/-- Mean projected energy maximized over unit inputs, as in Equation (3.1). -/
noncomputable def meanProjectedEnergy (μ : Measure Ω) (S : Ω → Submodule ℝ E) : ℝ :=
  sSup (Set.range fun u : {u : E // ‖u‖ = 1} => ∫ ω, ‖(S ω).starProjection u‖ ^ 2 ∂μ)

theorem integrable_projected_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ E) (u : E) (h : Measurable (fun ω => (S ω).starProjection u)) :
    Integrable (fun ω => ‖(S ω).starProjection u‖ ^ 2) μ := by
  refine (integrable_const (‖u‖ ^ 2)).mono' (h.norm.pow_const _).aestronglyMeasurable ?_
  filter_upwards [] with ω
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((S ω).norm_starProjection_apply_le u) _

theorem projectedEnergy_le_meanProjectedEnergy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ E) (hS : ∀ u : E, Measurable (fun ω => (S ω).starProjection u))
    (u : E) :
    (∫ ω, ‖(S ω).starProjection u‖ ^ 2 ∂μ) ≤ meanProjectedEnergy μ S * ‖u‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  have hbound : BddAbove
      (Set.range fun z : {z : E // ‖z‖ = 1} => ∫ ω, ‖(S ω).starProjection z‖ ^ 2 ∂μ) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hle (ω : Ω) : ‖(S ω).starProjection z‖ ^ 2 ≤ 1 := by
      calc
        _ ≤ ‖(z : E)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ((S ω).norm_starProjection_apply_le z) _
        _ = 1 := by simp [z.property]
    simpa using integral_mono (integrable_projected_energy μ S z (hS z)) (integrable_const (1 : ℝ)) hle
  let z := ‖u‖⁻¹ • u
  have hn : ‖z‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]
  have hz : ‖u‖ • z = u := by
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
  have he (ω : Ω) : ‖(S ω).starProjection u‖ ^ 2 =
      ‖u‖ ^ 2 * ‖(S ω).starProjection z‖ ^ 2 := by
    conv_lhs => rw [← hz]
    rw [map_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg _), mul_pow]
  simp_rw [he, integral_const_mul]
  rw [mul_comm (meanProjectedEnergy μ S)]
  exact mul_le_mul_of_nonneg_left (le_csSup hbound ⟨⟨z, hn⟩, rfl⟩) (sq_nonneg _)

end Energy

section Columns

variable {Ω : Type*} [MeasurableSpace Ω]
variable {n k : ℕ}

/-- The Hilbert space of all columns, with its squared Frobenius norm. -/
abbrev GaussianColumnHilbert (n k : ℕ) := PiLp 2 (fun _ : Fin k => EuclideanSpace ℝ (Fin n))

/-- The column product law becomes the standard Gaussian in the Hilbert
space of all entries, without any scaling. -/
theorem gaussianColumnLaw_map_toLp :
    (gaussianColumnLaw n k).map (WithLp.toLp 2) = stdGaussian (GaussianColumnHilbert n k) := by
  have : IsProbabilityMeasure ((gaussianColumnLaw n k).map (WithLp.toLp 2)) :=
    Measure.isProbabilityMeasure_map (WithLp.measurable_toLp _ _).aemeasurable
  apply Measure.ext_of_charFun
  funext t
  unfold gaussianColumnLaw
  rw [charFun_pi, charFun_stdGaussian]
  simp_rw [charFun_stdGaussian, ← Complex.exp_sum]
  have hn := congrArg (fun x : ℝ => (x : ℂ)) (PiLp.norm_sq_eq_of_L2 _ t)
  push_cast at hn
  rw [hn, ← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- Observe each Gaussian column in the same row subspace. -/
def columnwiseSubspace (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (GaussianColumnHilbert n k) :=
  (Submodule.pi Set.univ fun _ : Fin k => S).comap (WithLp.linearEquiv 2 ℝ _).toLinearMap

theorem columnwiseSubspace_starProjection (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : GaussianColumnHilbert n k) :
    (columnwiseSubspace S).starProjection x =
      WithLp.toLp 2 (fun j => S.starProjection (x j)) := by
  let y : GaussianColumnHilbert n k := WithLp.toLp 2 (fun j => S.starProjection (x j))
  have hy : y ∈ columnwiseSubspace S := by
    change (fun j => S.starProjection (x j)) ∈ Submodule.pi Set.univ (fun _ : Fin k => S)
    exact Submodule.mem_pi.mpr fun j _ => (S.orthogonalProjectionOnto (x j)).property
  apply Submodule.eq_starProjection_of_mem_orthogonal hy
  intro w hw
  change inner ℝ w (x - y) = 0
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro j _
  change inner ℝ (w j) (x j - S.starProjection (x j)) = 0
  change WithLp.ofLp w ∈ Submodule.pi Set.univ (fun _ : Fin k => S) at hw
  exact S.sub_starProjection_mem_orthogonal (x j) (w j) (Submodule.mem_pi.mp hw j (Set.mem_univ j))

theorem projected_columns_le_meanProjectedEnergy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ u : EuclideanSpace ℝ (Fin n), Measurable (fun ω => (S ω).starProjection u))
    (u : GaussianColumnHilbert n k) :
    (∫ ω, ‖(columnwiseSubspace (S ω)).starProjection u‖ ^ 2 ∂μ) ≤
      meanProjectedEnergy μ S * ‖u‖ ^ 2 := by
  simp_rw [PiLp.norm_sq_eq_of_L2 _ ((columnwiseSubspace _).starProjection _),
    columnwiseSubspace_starProjection]
  change (∫ ω, ∑ j, ‖(S ω).starProjection (u j)‖ ^ 2 ∂μ) ≤ _
  rw [PiLp.norm_sq_eq_of_L2 _ u,
    integral_finsetSum _ (fun j _ => integrable_projected_energy μ S (u j) (hS (u j))),
    Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => projectedEnergy_le_meanProjectedEnergy μ S hS (u j)

/-- The first assertion of Lemma 3.2 for a Gaussian matrix. The coefficient
depends only on the law of its row-space observation, for every width. -/
theorem gaussianMatrixProjection_L2_contraction (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ u : EuclideanSpace ℝ (Fin n), Measurable (fun ω => (S ω).starProjection u))
    (f : GaussianL2 (GaussianColumnHilbert n k))
    (hf : (∫ x, f x ∂stdGaussian (GaussianColumnHilbert n k)) = 0) :
    (∫ ω, ‖gaussianConditionalProjection (columnwiseSubspace (S ω)) f‖ ^ 2 ∂μ) ≤
      meanProjectedEnergy μ S * ‖f‖ ^ 2 := by
  apply (gaussianProjection_L2_contraction μ (fun ω => columnwiseSubspace (S ω)) _
    (meanProjectedEnergy μ S) (projected_columns_le_meanProjectedEnergy μ S hS) f hf).2
  intro u
  simp_rw [columnwiseSubspace_starProjection]
  exact (WithLp.measurable_toLp _ _).comp (measurable_pi_iff.mpr fun j => hS (u j))

end Columns

end SketchOrientation
