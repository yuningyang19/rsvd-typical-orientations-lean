import TypicalOrientations.RotationModel
import Mathlib.MeasureTheory.Order.Lattice

namespace TypicalOrientations

open MeasureTheory Filter Matrix SketchOrientation
open scoped Topology

noncomputable section

variable {n k l : ℕ} {ι : Type*}

/-- One sketch's absolute discrepancy at the shared input orientation. -/
def orientationGap (k : ℕ) (μ : Measure (OrthogonalProjector n l))
    (σ : Spectra n k) (U : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  |conditionalMean k σ.val μ U - gaussianMean k l σ.val|

def sharedOrientationGap [Fintype ι] [Nonempty ι] (k : ℕ)
    (μ : ι → Measure (OrthogonalProjector n l)) (σ : Spectra n k)
    (U : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => orientationGap k (μ j) σ U)

/-- The maximum is for one common orientation. The supremum over fixed
spectra is outside the integral, as in Corollary 4.3. -/
def commonMeanDiscrepancy [Fintype ι] [Nonempty ι] (k : ℕ)
    (μ : ι → Measure (OrthogonalProjector n l)) : ℝ :=
  sSup (Set.range fun σ : Spectra n k =>
    ∫ U, sharedOrientationGap k μ σ U ∂gaussianRightOrthogonalLaw n)

/-- The direct comparison between two sketches at one common orientation. -/
def pairwiseMeanDiscrepancy (k : ℕ)
    (μ ν : Measure (OrthogonalProjector n l)) : ℝ :=
  sSup (Set.range fun σ : Spectra n k =>
    ∫ U, |conditionalMean k σ.val μ U - conditionalMean k σ.val ν U|
      ∂gaussianRightOrthogonalLaw n)

private theorem spectra_nonempty (hkn : k < n) : Nonempty (Spectra n k) := by
  let i : Fin n := ⟨k, hkn⟩
  have hi : i ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val) := by simp [i]
  refine ⟨⟨fun _ => 1, fun _ _ _ => le_rfl, fun _ => zero_le_one, ?_⟩⟩
  exact zero_lt_one.trans_le (by
    simpa [optimalSquaredTail] using
      (Finset.single_le_sum (fun _ _ => zero_le_one) hi :
        (1 : ℝ) ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val), 1))

private theorem integral_mem_nonneg_interval {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (C : ℝ)
    (hf : Measurable f) (h : ∀ x, f x ∈ Set.Icc 0 C) :
    (∫ x, f x ∂μ) ∈ Set.Icc 0 C := by
  have hInt : Integrable f μ :=
    (integrable_const C).mono' hf.aestronglyMeasurable
      (ae_of_all μ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h x).1]; exact (h x).2)
  refine ⟨integral_nonneg (fun x => (h x).1), ?_⟩
  simpa using integral_mono hInt (integrable_const C) (fun x => (h x).2)

private theorem measurable_orientationGap (σ : Spectra n k)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    Measurable (orientationGap k μ σ) :=
  ((measurable_conditionalMean k σ.val μ).sub_const _).abs

theorem integrable_orientationGap (σ : Spectra n k)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ] :
    Integrable (orientationGap k μ σ) (gaussianRightOrthogonalLaw n) := by
  let C := squaredFrobenius (diagonal σ.val) / optimalSquaredTail k σ.val
  have hF (U : Matrix (Fin n) (Fin n) ℝ) :
      conditionalMean k σ.val μ U ∈ Set.Icc 0 C :=
    integral_mem_nonneg_interval μ _ C
      ((measurable_rawResidual measurable_const
        (measurable_matrix_product measurable_const measurable_subtype_coe)).div_const _)
      (fun _ => ⟨residual_div_tail_nonneg k σ.val σ.property.2.2 _,
        residual_div_tail_le k σ.val σ.property.2.2 _⟩)
  have hg : gaussianMean k l σ.val ∈ Set.Icc 0 C :=
    integral_mem_nonneg_interval (gaussianMatrixLaw n l) _ C
      ((measurable_rawResidual measurable_const measurable_id).div_const _)
      (fun _ => ⟨residual_div_tail_nonneg k σ.val σ.property.2.2 _,
        residual_div_tail_le k σ.val σ.property.2.2 _⟩)
  refine (integrable_const C).mono' (measurable_orientationGap σ μ).aestronglyMeasurable
    (ae_of_all _ fun U => ?_)
  rw [Real.norm_eq_abs, orientationGap, abs_abs]
  exact abs_le.mpr ⟨by linarith [(hF U).1, hg.2], by linarith [(hF U).2, hg.1]⟩

/-- Exact finite-dimensional reduction of the common-mean part of
Corollary 4.3. Boundedness of the individual spectral discrepancies is
discharged by the criterion in the manuscript. -/
theorem commonMeanDiscrepancy_le_sum [Fintype ι] [Nonempty ι]
    (hkn : k < n)
    (μ : ι → Measure (OrthogonalProjector n l)) [∀ j, IsProbabilityMeasure (μ j)]
    (hBounds : ∀ j, BddAbove (Set.range fun σ : Spectra n k =>
      ∫ U, orientationGap k (μ j) σ U ∂gaussianRightOrthogonalLaw n)) :
    0 ≤ commonMeanDiscrepancy k μ ∧
      commonMeanDiscrepancy k μ ≤ ∑ j, meanDiscrepancy k (μ j) := by
  classical
  let ν := gaussianRightOrthogonalLaw n
  let B := ∑ j, meanDiscrepancy k (μ j)
  let f (σ : Spectra n k) := fun U => sharedOrientationGap k μ σ U
  let R (σ : Spectra n k) := ∫ U, f σ U ∂ν
  have hNonneg (σ : Spectra n k) (U : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ f σ U := by
    let j : ι := Classical.choice inferInstance
    exact (abs_nonneg _).trans (Finset.le_sup' (fun a => orientationGap k (μ a) σ U)
      (Finset.mem_univ j))
  have hUpper (σ : Spectra n k) : R σ ≤ B := by
    let g (j : ι) := orientationGap k (μ j) σ
    have hi (j : ι) : Integrable (g j) ν := integrable_orientationGap σ (μ j)
    have hle (U : Matrix (Fin n) (Fin n) ℝ) : f σ U ≤ ∑ j, g j U := by
      refine Finset.sup'_le _ _ (fun j hj => ?_)
      exact Finset.single_le_sum (f := fun j => g j U) (fun _ _ => abs_nonneg _) hj
    have hmeas : Measurable (f σ) := by
      have he : f σ = Finset.univ.sup' Finset.univ_nonempty g :=
        funext fun U => (Finset.sup'_apply Finset.univ_nonempty g U).symm
      rw [he]
      exact Finset.measurable_sup' _ (fun j _ => measurable_orientationGap σ (μ j))
    have hsum : Integrable (fun U => ∑ j, g j U) ν :=
      integrable_finsetSum _ (fun j _ => hi j)
    have hF : Integrable (f σ) ν := hsum.mono' hmeas.aestronglyMeasurable
      (ae_of_all _ fun U => by rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg σ U)]; exact hle U)
    calc
      R σ ≤ ∫ U, ∑ j, g j U ∂ν := integral_mono hF hsum hle
      _ = ∑ j, ∫ U, g j U ∂ν := integral_finsetSum _ (fun j _ => hi j)
      _ ≤ B := Finset.sum_le_sum (fun j _ => le_csSup (hBounds j) ⟨σ, rfl⟩)
  let : Nonempty (Spectra n k) := spectra_nonempty hkn
  have hb : BddAbove (Set.range R) := ⟨B, by rintro _ ⟨σ, rfl⟩; exact hUpper σ⟩
  have hn : (Set.range R).Nonempty := Set.range_nonempty _
  change 0 ≤ sSup (Set.range R) ∧ sSup (Set.range R) ≤ B
  obtain ⟨σ⟩ := spectra_nonempty hkn
  exact ⟨(integral_nonneg (hNonneg σ)).trans (le_csSup hb ⟨σ, rfl⟩),
    csSup_le hn (by rintro _ ⟨τ, rfl⟩; exact hUpper τ)⟩

/-- The pairwise part of Corollary 4.3 follows by inserting the Gaussian
mean at the same spectrum. -/
theorem pairwiseMeanDiscrepancy_le_add
    (hkn : k < n) (μ₁ μ₂ : Measure (OrthogonalProjector n l))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : BddAbove (Set.range fun σ : Spectra n k =>
      ∫ U, orientationGap k μ₁ σ U ∂gaussianRightOrthogonalLaw n))
    (h₂ : BddAbove (Set.range fun σ : Spectra n k =>
      ∫ U, orientationGap k μ₂ σ U ∂gaussianRightOrthogonalLaw n)) :
    0 ≤ pairwiseMeanDiscrepancy k μ₁ μ₂ ∧
      pairwiseMeanDiscrepancy k μ₁ μ₂ ≤ meanDiscrepancy k μ₁ + meanDiscrepancy k μ₂ := by
  let ν := gaussianRightOrthogonalLaw n
  let B := meanDiscrepancy k μ₁ + meanDiscrepancy k μ₂
  let f (σ : Spectra n k) := fun U =>
    |conditionalMean k σ.val μ₁ U - conditionalMean k σ.val μ₂ U|
  let R (σ : Spectra n k) := ∫ U, f σ U ∂ν
  have hUpper (σ : Spectra n k) : R σ ≤ B := by
    let g₁ := orientationGap k μ₁ σ
    let g₂ := orientationGap k μ₂ σ
    have hi₁ : Integrable g₁ ν := integrable_orientationGap σ μ₁
    have hi₂ : Integrable g₂ ν := integrable_orientationGap σ μ₂
    have hle (U : Matrix (Fin n) (Fin n) ℝ) : f σ U ≤ g₁ U + g₂ U := by
      simpa only [f, g₁, g₂, orientationGap,
        abs_sub_comm (gaussianMean k l σ.val) (conditionalMean k σ.val μ₂ U)] using
        abs_sub_le (conditionalMean k σ.val μ₁ U) (gaussianMean k l σ.val)
          (conditionalMean k σ.val μ₂ U)
    have hm : Measurable (f σ) :=
      ((measurable_conditionalMean k σ.val μ₁).sub (measurable_conditionalMean k σ.val μ₂)).abs
    have hF : Integrable (f σ) ν := (hi₁.add hi₂).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun U => by rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]; exact hle U)
    calc
      R σ ≤ ∫ U, g₁ U + g₂ U ∂ν := integral_mono hF (hi₁.add hi₂) hle
      _ = (∫ U, g₁ U ∂ν) + ∫ U, g₂ U ∂ν := integral_add hi₁ hi₂
      _ ≤ B := add_le_add (le_csSup h₁ ⟨σ, rfl⟩) (le_csSup h₂ ⟨σ, rfl⟩)
  let : Nonempty (Spectra n k) := spectra_nonempty hkn
  have hb : BddAbove (Set.range R) := ⟨B, by rintro _ ⟨σ, rfl⟩; exact hUpper σ⟩
  have hn : (Set.range R).Nonempty := Set.range_nonempty _
  change 0 ≤ sSup (Set.range R) ∧ sSup (Set.range R) ≤ B
  obtain ⟨σ⟩ := spectra_nonempty hkn
  exact ⟨(integral_nonneg (fun _ => abs_nonneg _)).trans (le_csSup hb ⟨σ, rfl⟩),
    csSup_le hn (by rintro _ ⟨τ, rfl⟩; exact hUpper τ)⟩

/-- Corollary 4.3's two limit conclusions, from the individual limits
provided by Theorem 1.1. The finite index type is the same at all dimensions. -/
theorem commonMean_of_individual_limits [Fintype ι] [Nonempty ι]
    (dims : ℕ → ℕ) (hkn : ∀ t, k < dims t)
    (μ : (t : ℕ) → ι → Measure (OrthogonalProjector (dims t) l))
    [∀ t j, IsProbabilityMeasure (μ t j)]
    (hBounds : ∀ t j, BddAbove (Set.range fun σ : Spectra (dims t) k =>
      ∫ U, orientationGap k (μ t j) σ U ∂gaussianRightOrthogonalLaw (dims t)))
    (hLimit : ∀ j, Tendsto (fun t => meanDiscrepancy k (μ t j)) atTop (𝓝 0)) :
    Tendsto (fun t => commonMeanDiscrepancy k (μ t)) atTop (𝓝 0) ∧
      ∀ i j, Tendsto (fun t => pairwiseMeanDiscrepancy k (μ t i) (μ t j)) atTop (𝓝 0) := by
  constructor
  · refine squeeze_zero (fun t => (commonMeanDiscrepancy_le_sum (hkn t) (μ t) (hBounds t)).1)
      (fun t => (commonMeanDiscrepancy_le_sum (hkn t) (μ t) (hBounds t)).2) ?_
    simpa using tendsto_finsetSum Finset.univ (fun j _ => hLimit j)
  · intro i j
    refine squeeze_zero
      (fun t => (pairwiseMeanDiscrepancy_le_add (hkn t) (μ t i) (μ t j) (hBounds t i) (hBounds t j)).1)
      (fun t => (pairwiseMeanDiscrepancy_le_add (hkn t) (μ t i) (μ t j) (hBounds t i) (hBounds t j)).2) ?_
    simpa using (hLimit i).add (hLimit j)

end

end TypicalOrientations
