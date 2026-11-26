import SketchOrientation.GaussianGramTracePowers
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace TypicalOrientations

open Matrix SketchOrientation MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

noncomputable section

/-- The scalar moment for the Gaussian variable in Lemma 3.2. -/
def standardNormalMoment (r : ℝ) : ℝ :=
  ∫ z, |z| ^ (2 * r) ∂gaussianReal 0 1

theorem standardNormalMoment_nonneg (r : ℝ) : 0 ≤ standardNormalMoment r :=
  integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _

private theorem integrable_standardNormalMoment {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun z : ℝ => |z| ^ (2 * r)) (gaussianReal 0 1) := by
  apply integrable_rpow_abs_of_mem_interior_integrableExpSet (X := id)
  · have h : integrableExpSet id (gaussianReal 0 1) = Set.univ :=
      Set.eq_univ_of_forall fun a => integrable_exp_mul_gaussianReal a
    simp [h]
  · positivity

/-- The law used to integrate the independent standard Gaussian row. -/
abbrev gaussianRowLaw (ℓ : ℕ) : Measure (Fin ℓ → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

private theorem gaussianRow_dot_map {ℓ : ℕ} (u : Fin ℓ → ℝ) :
    (gaussianRowLaw ℓ).map (fun z => z ⬝ᵥ u) =
      (gaussianReal 0 1).map (fun x => √(∑ i, u i ^ 2) * x) := by
  let U := WithLp.toLp 2 u
  let L := InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin ℓ)) U
  have hL (z : Fin ℓ → ℝ) : L (WithLp.toLp 2 z) = z ⬝ᵥ u := by
    change inner ℝ U (WithLp.toLp 2 z) = z ⬝ᵥ u
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [U]
  simp_rw [← hL]
  change (gaussianRowLaw ℓ).map (L ∘ WithLp.toLp 2) =
    (gaussianReal 0 1).map (fun x => √(∑ i, u i ^ 2) * x)
  rw [← Measure.map_map L.continuous.measurable (WithLp.measurable_toLp _ _),
    map_pi_eq_stdGaussian, IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, gaussianReal_map_const_mul]
  have hnorm : ‖L‖ ^ 2 = ∑ i, u i ^ 2 := by
    dsimp [L]
    rw [(InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin ℓ))).norm_map]
    exact EuclideanSpace.real_norm_sq_eq U
  rw [hnorm, mul_zero, mul_one]
  congr 1
  apply Subtype.ext
  change ((∑ i, u i ^ 2).toNNReal : ℝ) = √(∑ i, u i ^ 2) ^ 2
  rw [Real.coe_toNNReal _ (Finset.sum_nonneg fun i _ => sq_nonneg (u i)),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (u i))]

private theorem gaussianRow_dot_moment {ℓ : ℕ} (u : Fin ℓ → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun z => ((z ⬝ᵥ u) ^ (2 : ℕ)) ^ r) (gaussianRowLaw ℓ) ∧
    (∫ z, ((z ⬝ᵥ u) ^ (2 : ℕ)) ^ r ∂gaussianRowLaw ℓ) =
      (∑ i, u i ^ 2) ^ r * standardNormalMoment r := by
  let a : ℝ := ∑ i, u i ^ 2
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => sq_nonneg (u i)
  let f := fun x : ℝ => (x ^ (2 : ℕ)) ^ r
  have hf : Measurable f := by fun_prop
  have hm : Measurable (fun z : Fin ℓ → ℝ => z ⬝ᵥ u) :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _
  have hs : Measurable (fun x : ℝ => √a * x) := by fun_prop
  have he (x : ℝ) : f (√a * x) = a ^ r * |x| ^ (2 * r) := by
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt ha, Real.mul_rpow ha (sq_nonneg x),
      ← sq_abs x, ← Real.rpow_natCast_mul (abs_nonneg x)]
    norm_num
  have hint : Integrable (fun x : ℝ => f (√a * x)) (gaussianReal 0 1) := by
    simp_rw [he]
    exact (integrable_standardNormalMoment hr).const_mul _
  have hint' : Integrable f ((gaussianRowLaw ℓ).map (fun z => z ⬝ᵥ u)) := by
    rw [gaussianRow_dot_map]
    exact (integrable_map_measure hf.aestronglyMeasurable hs.aemeasurable).2 hint
  exact ⟨hint'.comp_measurable hm, by
    change (∫ z, f (z ⬝ᵥ u) ∂gaussianRowLaw ℓ) = a ^ r * standardNormalMoment r
    rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, gaussianRow_dot_map,
      integral_map hs.aemeasurable hf.aestronglyMeasurable]
    simp_rw [he]
    rw [integral_const_mul]
    rfl⟩

/-- The moment of the squared Euclidean length of a Gaussian row after a
fixed linear map. Convexity uses the directional marginal variances as
weights, giving the same trace bound as the covariance eigenbasis argument. -/
theorem gaussianRow_vecMul_moment {ℓ k : ℕ} (R : Matrix (Fin ℓ) (Fin k) ℝ)
    {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun z => (∑ j, (z ᵥ* R) j ^ 2) ^ r) (gaussianRowLaw ℓ) ∧
    (∫ z, (∑ j, (z ᵥ* R) j ^ 2) ^ r ∂gaussianRowLaw ℓ) ≤
      (∑ j, ∑ i, R i j ^ 2) ^ r * standardNormalMoment r := by
  let v : Fin k → ℝ := fun j => ∑ i, R i j ^ 2
  let q (j : Fin k) (z : Fin ℓ → ℝ) : ℝ := (z ᵥ* R) j ^ 2
  let s : ℝ := ∑ j, v j
  let w : Fin k → ℝ := fun j => if v j = 0 then 0 else 1 / v j
  have hv (j : Fin k) : 0 ≤ v j := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hq (j : Fin k) (z : Fin ℓ → ℝ) : 0 ≤ q j z := sq_nonneg _
  have hm (j : Fin k) : Measurable (q j) := by
    unfold q Matrix.vecMul
    exact (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _).pow_const (2 : ℕ)
  have hw (j : Fin k) : 0 ≤ w j := by
    unfold w
    split_ifs
    · exact le_rfl
    · exact one_div_nonneg.mpr (hv j)
  have hz (j : Fin k) (hj : v j = 0) (z : Fin ℓ → ℝ) : q j z = 0 := by
    have hR (i : Fin ℓ) : R i j = 0 := by
      have hsq : R i j ^ 2 ≤ v j := Finset.single_le_sum (fun a _ => sq_nonneg (R a j))
        (Finset.mem_univ i)
      rw [hj] at hsq
      nlinarith
    simp [q, vecMul, dotProduct, hR]
  have hW (j : Fin k) (z : Fin ℓ → ℝ) : v j * (w j * q j z) = q j z := by
    by_cases hj : v j = 0
    · simp [hj, hz j hj z]
    · simp [w, hj, div_eq_mul_inv]
  have hM (j : Fin k) :
      Integrable (fun z => q j z ^ r) (gaussianRowLaw ℓ) ∧
      (∫ z, q j z ^ r ∂gaussianRowLaw ℓ) = (v j) ^ r * standardNormalMoment r :=
    gaussianRow_dot_moment (fun i => R i j) (zero_le_one.trans hr)
  have hi (j : Fin k) : Integrable (fun z => (w j * q j z) ^ r) (gaussianRowLaw ℓ) := by
    simp_rw [Real.mul_rpow (hw j) (hq j _)]
    exact (hM j).1.const_mul _
  have hJ (j : Fin k) :
      (∫ z, (w j * q j z) ^ r ∂gaussianRowLaw ℓ) ≤ standardNormalMoment r := by
    simp_rw [Real.mul_rpow (hw j) (hq j _)]
    rw [integral_const_mul, (hM j).2, ← mul_assoc, ← Real.mul_rpow (hw j) (hv j)]
    apply mul_le_of_le_one_left (standardNormalMoment_nonneg r)
    apply (Real.rpow_le_one (mul_nonneg (hw j) (hv j)) ?_ (zero_le_one.trans hr))
    by_cases hj : v j = 0
    · simp [hj]
    · simp [w, hj]
  change Integrable (fun z => (∑ j, q j z) ^ r) (gaussianRowLaw ℓ) ∧
    (∫ z, (∑ j, q j z) ^ r ∂gaussianRowLaw ℓ) ≤ s ^ r * standardNormalMoment r
  by_cases hs : s = 0
  · have he : (fun z => (∑ j, q j z) ^ r) = (fun _ => 0 : (Fin ℓ → ℝ) → ℝ) := by
      funext z
      have he' (j : Fin k) : v j = 0 := le_antisymm
        ((Finset.single_le_sum (fun a _ => hv a) (Finset.mem_univ j)).trans_eq hs) (hv j)
      simp [fun j => hz j (he' j) z, Real.zero_rpow (by linarith : r ≠ 0)]
    rw [he, hs, Real.zero_rpow (by linarith : r ≠ 0), zero_mul]
    simp
  have hs' : 0 < s := lt_of_le_of_ne (Finset.sum_nonneg fun j _ => hv j) (Ne.symm hs)
  let c (j : Fin k) : ℝ := v j / s
  have hc (j : Fin k) : 0 ≤ c j := div_nonneg (hv j) hs'.le
  have hsum : ∑ j, c j = 1 := by
    rw [show (∑ j, c j) = s / s by exact (Finset.sum_div _ _ _).symm, div_self hs]
  let W (z : Fin ℓ → ℝ) : ℝ := s ^ r * ∑ j, c j * (w j * q j z) ^ r
  have hWint : Integrable W (gaussianRowLaw ℓ) :=
    (integrable_finsetSum _ fun j _ => (hi j).const_mul _).const_mul _
  have hpoint (z : Fin ℓ → ℝ) : (∑ j, q j z) ^ r ≤ W z := by
    have hcv := (convexOn_rpow hr).map_sum_le (t := Finset.univ) (w := c)
      (p := fun j => w j * q j z) (fun j _ => hc j) hsum
      (fun j _ => mul_nonneg (hw j) (hq j z))
    have he : (∑ j, c j • (w j * q j z)) = (∑ j, q j z) / s := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_eq_mul, show c j = v j / s from rfl, div_mul_eq_mul_div, hW]
    rw [he, Real.div_rpow (Finset.sum_nonneg fun j _ => hq j z) hs'.le] at hcv
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hs' _)).mp hcv |>.trans_eq (by
      simp only [W, smul_eq_mul, mul_comm (s ^ r)])
  have hm' : Measurable (fun z => (∑ j, q j z) ^ r) :=
    (Finset.measurable_sum _ fun j _ => hm j).pow_const _
  have hI := hWint.mono' hm'.aestronglyMeasurable (ae_of_all _ fun z => by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun j _ => hq j z) _)]
    exact hpoint z)
  refine ⟨hI, (integral_mono hI hWint hpoint).trans ?_⟩
  unfold W
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hi j).const_mul _]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hs'.le _)
  simp_rw [integral_const_mul]
  exact (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hJ j) (hc j)).trans_eq (by
    rw [← Finset.sum_mul, hsum, one_mul])

end

end TypicalOrientations
