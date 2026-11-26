import SketchOrientation.GaussianOrientationNorm
import SketchOrientation.GaussianHaarDirectionBeta
import Mathlib.Analysis.Convex.Integral

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix Set
open scoped InnerProductSpace

variable {n k p : ℕ}

private theorem abs_sub_le_max_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x - y| ≤ max x y := by
  rw [abs_le]
  have hx' := le_max_left x y
  have hy' := le_max_right x y
  constructor <;> linarith

set_option maxHeartbeats 1500000 in
/-- The normalized centered inverse endpoint has a uniform moment above
one throughout the entire oversampling range. -/
theorem haarOrientationEndpoint_centered_rpow_bound
    (hkn : k + p ≤ n) (hk : 0 < k) (hp : 2 ≤ p)
    (ν : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure ν] :
    let η := gaussianHaarFrameLaw (show k ≤ n by omega)
    let f := fun V => (|haarOrientationEndpoint ν V - haarOrientationBenchmark n k (k + p)| : ℝ) ^
      ((5 : ℝ) / 4)
    Integrable f η ∧ (∫ V, f V ∂η) ≤ chiSquareNegativeMoment (p + 1) ((5 : ℝ) / 4) + 1 := by
  intro η f
  let ℓ := k + p
  let r := (5 : ℝ) / 4
  let b := (n : ℝ) - k - 1
  let c := (n : ℝ) - k
  let a := (ℓ : ℝ) - k - 1
  let M := chiSquareNegativeMoment (p + 1) r
  let Y := fun z : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ =>
    gaussianOrientationScore z.1 z.2 / c
  let A := fun V : Matrix (Fin n) (Fin k) ℝ => ∫ P, Y (P, V) ∂ν
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hr : 1 ≤ r := by norm_num [r]
  have hp'': (1 : ℝ) ≤ a := by dsimp [a, ℓ]; push_cast; linarith
  have hn : (k : ℝ) + (p : ℝ) ≤ n := by exact_mod_cast hkn
  have hb : 0 < b := by dsimp [b]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hbc : b / c ≤ 1 := (div_le_one hc).2 (by dsimp [b, c]; linarith)
  have harg : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2 := by
    dsimp [r, ℓ]
    rw [Nat.add_sub_cancel_left, Nat.cast_add]
    linarith
  have hY : Measurable Y := measurable_gaussianOrientationScore.div_const _
  have hY₀ (z : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ) : 0 ≤ Y z :=
    div_nonneg (gaussianOrientationScore_nonneg _ _) hc.le
  have hI : Integrable Y (ν.prod η) := by
    have h := (haarOrientationScore_moment_prod hkn hk (by omega) ν
      (r := 1) le_rfl ((show 1 < r by norm_num [r]).trans harg)).1
    have hi : Integrable (Function.uncurry (@gaussianOrientationScore n k ℓ)) (ν.prod η) := by
      simpa only [Function.uncurry_def, Real.rpow_one] using h
    exact hi.div_const _
  have hPowRaw := haarOrientationScore_moment_prod hkn hk (by omega) ν hr harg
  have hR : Integrable (fun z => Y z ^ r) (ν.prod η) ∧ (∫ z, Y z ^ r ∂ν.prod η) ≤ M := by
    have he (z : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ) :
        Y z ^ r = gaussianOrientationScore z.1 z.2 ^ r / c ^ r :=
      Real.div_rpow (gaussianOrientationScore_nonneg _ _) hc.le r
    simp_rw [he]
    refine ⟨hPowRaw.1.div_const _, ?_⟩
    rw [integral_div]
    refine (div_le_div_of_nonneg_right hPowRaw.2 (Real.rpow_nonneg hc.le _)).trans ?_
    have hM : 0 ≤ M := by
      unfold M chiSquareNegativeMoment
      push_cast
      have h₁ := Real.Gamma_pos_of_pos (show 0 < ((p : ℝ) + 1) / 2 - r by linarith [harg])
      have h₂ := Real.Gamma_pos_of_pos (show 0 < ((p : ℝ) + 1) / 2 by linarith)
      positivity
    change b ^ r * chiSquareNegativeMoment (ℓ - k + 1) r / c ^ r ≤ _
    dsimp [ℓ]
    rw [Nat.add_sub_cancel_left, mul_div_right_comm, ← Real.div_rpow hb.le hc.le]
    apply mul_le_of_le_one_left hM
    exact Real.rpow_le_one (div_nonneg hb.le hc.le) hbc (zero_le_one.trans hr)
  have hA : Measurable A := hY.stronglyMeasurable.integral_prod_left'.measurable
  have hA0 (V : Matrix (Fin n) (Fin k) ℝ) : 0 ≤ A V := integral_nonneg (fun P => hY₀ (P, V))
  have hJ : ∀ᵐ V ∂η, A V ^ r ≤ ∫ P, Y (P, V) ^ r ∂ν := by
    filter_upwards [hI.prod_left_ae, hR.1.prod_left_ae] with V h₁ h₂
    exact (convexOn_rpow hr).map_integral_le
      (Real.continuous_rpow_const (zero_le_one.trans hr)).continuousOn isClosed_Ici
      (ae_of_all _ fun P => hY₀ (P, V)) h₁ h₂
  have hAI : Integrable (fun V => A V ^ r) η := by
    refine hR.1.integral_prod_right.mono' (hA.pow_const _).aestronglyMeasurable ?_
    filter_upwards [hJ] with V hV
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hA0 V) _)]
    exact hV
  have hAm : (∫ V, A V ^ r ∂η) ≤ M := by
    refine (integral_mono_ae hAI hR.1.integral_prod_right hJ).trans ?_
    rw [← integral_prod_symm _ hR.1]
    exact hR.2
  let m := (b / c) / a
  have hm₀ : 0 ≤ m := by positivity
  have hm₁ : m ≤ 1 := (div_le_one (zero_lt_one.trans_le hp'')).2 (hbc.trans hp'')
  have he (V : Matrix (Fin n) (Fin k) ℝ) :
      haarOrientationEndpoint ν V - haarOrientationBenchmark n k ℓ = A V - m := by
    unfold haarOrientationEndpoint haarOrientationBenchmark
    change (((∫ P, gaussianOrientationScore P V ∂ν) - (ℓ : ℝ) / k) / c -
      (b * (1 / a) - (ℓ : ℝ) / k) / c) = (∫ P, gaussianOrientationScore P V / c ∂ν) - m
    rw [integral_div]
    unfold m
    ring
  have hB (V : Matrix (Fin n) (Fin k) ℝ) : f V ≤ A V ^ r + 1 := by
    change |haarOrientationEndpoint ν V - haarOrientationBenchmark n k ℓ| ^ r ≤ _
    rw [he]
    have h := abs_sub_le_max_of_nonneg (hA0 V) hm₀
    have hp₀ : 0 ≤ r := zero_le_one.trans hr
    refine (Real.rpow_le_rpow (abs_nonneg _) h hp₀).trans ?_
    rcases le_total (A V) m with h | h
    · rw [max_eq_right h]
      exact (Real.rpow_le_one hm₀ hm₁ hp₀).trans (le_add_of_nonneg_left (Real.rpow_nonneg (hA0 V) _))
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right zero_le_one
  have hF : Measurable f :=
    ((measurable_haarOrientationEndpoint ν).sub_const _).abs.pow_const _
  have hAI' : Integrable (fun V => A V ^ r + 1) η := hAI.add (integrable_const _)
  have hfi : Integrable f η := by
    refine hAI'.mono' hF.aestronglyMeasurable ?_
    filter_upwards [] with V
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hB V
  refine ⟨hfi, (integral_mono hfi hAI' hB).trans ?_⟩
  rw [integral_add hAI (integrable_const _), integral_const, probReal_univ, one_smul]
  exact add_le_add hAm le_rfl

/-- Fixed-rank bounded moments for the centered Haar test from the converse. -/
theorem haarFrameDirectionTest_moment (hk : 0 < k) (hkn : k < n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    let η := gaussianHaarFrameLaw hkn.le
    let f := fun V => (|(n : ℝ) * haarFrameQuadratic u V - (k : ℝ)| : ℝ) ^ (10 : ℝ)
    Integrable f η ∧ (∫ V, f V ∂η) ≤
      (∏ j ∈ Finset.range 10, ((k : ℝ) + 2 * j)) + (k : ℝ) ^ (10 : ℕ) := by
  intro η f
  let q := @haarFrameQuadratic n k u
  let g := fun x : ℝ => ((n : ℝ) * x) ^ (10 : ℕ)
  have hq : Measurable q := measurable_haarFrameQuadratic u
  have hg : Measurable g := (measurable_id.const_mul _).pow_const _
  have hLaw : η.map q = _ := haarFrameQuadratic_beta hk hkn u hu
  have hM := beta_scaled_rank_moment hk hkn 10
  have hG : Integrable (g ∘ q) η := by
    rw [← integrable_map_measure hg.aestronglyMeasurable hq.aemeasurable, hLaw]
    exact hM.1
  have hGm : (∫ V, (g ∘ q) V ∂η) ≤ ∏ j ∈ Finset.range 10, ((k : ℝ) + 2 * j) := by
    change (∫ V, g (q V) ∂η) ≤ _
    rw [← integral_map hq.aemeasurable hg.aestronglyMeasurable, hLaw]
    exact hM.2
  have hf : Measurable f :=
    ((hq.const_mul (n : ℝ)).sub_const _).abs.pow_const _
  have hf₀ (V : Matrix (Fin n) (Fin k) ℝ) : 0 ≤ f V :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hB (V : Matrix (Fin n) (Fin k) ℝ) : f V ≤ (g ∘ q) V + (k : ℝ) ^ (10 : ℕ) := by
    let a := (n : ℝ) * q V
    have h₀ : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have h₁ : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    change |a - (k : ℝ)| ^ (10 : ℝ) ≤ a ^ (10 : ℕ) + (k : ℝ) ^ (10 : ℕ)
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_max_of_nonneg h₀ h₁) (10 : ℕ)
    refine h.trans ?_
    rcases le_total a (k : ℝ) with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (pow_nonneg h₀ _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (pow_nonneg h₁ _)
  have hGI : Integrable (fun V => (g ∘ q) V + (k : ℝ) ^ (10 : ℕ)) η := hG.add (integrable_const _)
  have hfi : Integrable f η := by
    refine hGI.mono' hf.aestronglyMeasurable ?_
    filter_upwards [] with V
    rw [Real.norm_of_nonneg (hf₀ V)]
    exact hB V
  refine ⟨hfi, (integral_mono hfi hGI hB).trans ?_⟩
  rw [integral_add hG (integrable_const _), integral_const, probReal_univ, one_smul]
  exact add_le_add hGm le_rfl

/-- A unit direction attaining the operator norm of the positive mean
sketch projector exists in each positive ambient dimension. -/
theorem exists_unit_meanSketchProjector_rayleigh_eq_norm {ℓ : ℕ} (hn : 0 < n)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] :
    ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
      inner ℝ ((meanSketchProjector ν).toEuclideanLin u) u =
        ‖(meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap‖ := by
  let E := EuclideanSpace ℝ (Fin n)
  let q := fun u : E => inner ℝ ((meanSketchProjector ν).toEuclideanLin u) u
  have hq : Continuous q := (meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap.continuous.inner continuous_id
  have hN : (Metric.sphere (0 : E) 1).Nonempty := by
    let e : E := EuclideanSpace.single ⟨0, hn⟩ 1
    refine ⟨e, ?_⟩
    apply mem_sphere_zero_iff_norm.mpr
    change ‖PiLp.single 2 (β := fun _ : Fin n => ℝ) ⟨0, hn⟩ 1‖ = 1
    rw [PiLp.norm_single]
    norm_num
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hN hq.continuousOn
  have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
  refine ⟨u, hu1, ?_⟩
  rw [← meanProjectedEnergy_eq_meanSketchProjector_norm hn ν]
  apply le_antisymm
  · rw [meanSketchProjector_inner]
    simpa only [hu1, one_pow, mul_one] using (projectedEnergy_le_meanProjectedEnergy ν
      orientationRowSpace measurable_orientationRowSpace_projection u)
  · change _ ≤ q u
    unfold meanProjectedEnergy
    have hv : Nonempty {u : E // ‖u‖ = 1} := ⟨⟨u, hu1⟩⟩
    apply csSup_le (Set.range_nonempty_iff_nonempty.mpr hv)
    rintro _ ⟨v, rfl⟩
    change (∫ P, ‖(orientationRowSpace P).starProjection (v : E)‖ ^ 2 ∂ν) ≤ q u
    rw [← meanSketchProjector_inner]
    exact hmax (mem_sphere_zero_iff_norm.mpr v.property)

end SketchOrientation
