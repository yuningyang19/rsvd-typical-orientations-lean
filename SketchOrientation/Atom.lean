import SketchOrientation.FlatVector
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace SketchOrientation

open Matrix

/-- The deterministic target for the atom in Theorem 6.2, in matrix form. -/
theorem exists_flat_kernelFrame {n k ℓ : ℕ} (P₀ : Matrix (Fin n) (Fin n) ℝ)
    (hRank : P₀.rank = ℓ) (hDims : k + ℓ ≤ n) :
    ∃ V : Matrix (Fin n) (Fin k) ℝ,
      P₀ * V = 0 ∧ Vᵀ * V = 1 ∧
      (∀ i, (∑ j, V i j ^ 2) ≤ ∑ j : Fin k, ((n - ℓ - j.val : ℕ) : ℝ)⁻¹) ∧
      (∑ j : Fin k, ((n - ℓ - j.val : ℕ) : ℝ)⁻¹) ≤
        (k : ℝ) / ((n - ℓ - k + 1 : ℕ) : ℝ) := by
  classical
  let E := P₀.mulVecLin.ker
  have hdim := P₀.mulVecLin.finrank_range_add_finrank_ker
  change P₀.rank + Module.finrank ℝ E = Module.finrank ℝ (Fin n → ℝ) at hdim
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hRank] at hdim
  have hd : Module.finrank ℝ E = n - ℓ := by omega
  obtain ⟨v, hV, hOrtho, hLev, hsum⟩ :=
    exists_flat_frame_with_leverage E k (by omega)
  let V : Matrix (Fin n) (Fin k) ℝ := fun i j => v j i
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · ext i j
    have hv : P₀ *ᵥ v j = 0 := LinearMap.mem_ker.mp (hV j)
    exact congrFun hv i
  · ext i j
    change v i ⬝ᵥ v j = (1 : Matrix (Fin k) (Fin k) ℝ) i j
    rw [hOrtho, Matrix.one_apply]
  · intro i
    simpa only [V, hd] using hLev i
  · simpa only [hd] using hsum


open MeasureTheory

/-- The all-zero event bound for the angle formula in the proof of Theorem
6.2. This is the expectation step after the compressed eigenvalues are known. -/
theorem atom_spectralLoss_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {n ℓ Γ : ℝ}
    (hk : 0 < k) (hn : (k : ℝ) < n) (hΓ : 1 ≤ Γ)
    (t : Fin k → Ω → ℝ) (hmeas : ∀ j, Measurable (t j))
    (hnonneg : ∀ j w, 0 ≤ t j w)
    {A : Set Ω} (hA : MeasurableSet A) (hzero : ∀ w ∈ A, ∀ j, t j w = 0) :
    (μ.real A * Γ - ℓ / (k : ℝ)) / (n - k) ≤
      ∫ w, ((∑ j : Fin k, Γ / (1 + (Γ - 1) * t j w)) - ℓ) / ((k : ℝ) * (n - k)) ∂μ := by
  classical
  have hΓ' : 0 ≤ Γ := by linarith
  have hΓsub : 0 ≤ Γ - 1 := by linarith
  have hden (j : Fin k) (w : Ω) : 1 ≤ 1 + (Γ - 1) * t j w := by
    linarith [mul_nonneg hΓsub (hnonneg j w)]
  let s : Ω → ℝ := fun w => ∑ j : Fin k, Γ / (1 + (Γ - 1) * t j w)
  have hsmeas : Measurable s := by
    unfold s
    apply Finset.measurable_sum
    intro j _
    exact measurable_const.div (measurable_const.add (measurable_const.mul (hmeas j)))
  have hs_nonneg (w : Ω) : 0 ≤ s w := Finset.sum_nonneg fun j _ =>
    div_nonneg hΓ' (zero_le_one.trans (hden j w))
  have hs_le (w : Ω) : s w ≤ (k : ℝ) * Γ := by
    calc
      _ ≤ ∑ _ : Fin k, Γ := by
        apply Finset.sum_le_sum
        intro j _
        exact div_le_self hΓ' (hden j w)
      _ = _ := by simp
  have hsint : Integrable s μ := Integrable.of_bound hsmeas.aestronglyMeasurable ((k : ℝ) * Γ)
    (Filter.Eventually.of_forall fun w => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hs_nonneg w)] using hs_le w)
  have hlowInt : Integrable (A.indicator (fun _ => (k : ℝ) * Γ)) μ :=
    (integrable_const _).indicator hA
  have hpoint : A.indicator (fun _ => (k : ℝ) * Γ) ≤ s := by
    intro w
    by_cases hw : w ∈ A
    · simp [Set.indicator_of_mem hw, s, hzero w hw]
    · simpa [Set.indicator_of_notMem hw] using hs_nonneg w
  have hlow := integral_mono hlowInt hsint hpoint
  rw [integral_indicator_const ((k : ℝ) * Γ) hA, smul_eq_mul] at hlow
  have hkn : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnorm : (μ.real A * Γ - ℓ / (k : ℝ)) / (n - k) =
      (μ.real A * ((k : ℝ) * Γ) - ℓ) / ((k : ℝ) * (n - k)) := by
    field_simp [hkn.ne', (sub_pos.mpr hn).ne']
  rw [hnorm]
  change _ ≤ ∫ w, (s w - ℓ) / ((k : ℝ) * (n - k)) ∂μ
  rw [integral_div, integral_sub hsint (integrable_const _), integral_const]
  simp only [probReal_univ, one_smul]
  exact div_le_div_of_nonneg_right (by linarith) (mul_nonneg hkn.le (sub_nonneg.mpr hn.le))

end SketchOrientation
