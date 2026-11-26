import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

namespace SketchOrientation

open Filter Topology

private theorem abs_pow_four (x : ℝ) : |x| ^ 4 = x ^ 4 := by
  calc
    _ = (|x| ^ 2) ^ 2 := by ring
    _ = _ := by rw [sq_abs]; ring

private theorem cos_secondOrder_bound (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2)| ≤ x ^ 4 := by
  let z := (x : ℂ) * Complex.I
  have hz : ‖z‖ = |x| := by simp [z]
  let q : ℂ := Complex.exp z - ∑ j ∈ Finset.range 4, z ^ j / j.factorial
  have hre : q.re = Real.cos x - (1 - x ^ 2 / 2) := by
    dsimp [q, z]
    rw [Complex.exp_ofReal_mul_I_re]
    norm_num [Finset.sum_range_succ, pow_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.normSq]
    ring
  rw [← hre]
  have he := Complex.exp_bound (x := z) (n := 4) (hz ▸ hx) (by decide)
  calc
    _ ≤ ‖q‖ := Complex.abs_re_le_norm q
    _ ≤ _ := by
      change ‖q‖ ≤ _ at he
      rw [hz, abs_pow_four] at he
      norm_num at he
      exact he.trans (by nlinarith [sq_nonneg (x ^ 2)])

private theorem cos_sub_gaussianFactor_bound (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cos x - Real.exp (-(x ^ 2 / 2))| ≤ 2 * x ^ 4 := by
  have hsq : x ^ 2 ≤ 1 := by nlinarith [abs_le.mp hx, sq_abs x]
  have harg : |-(x ^ 2 / 2)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    linarith
  have he := Real.abs_exp_sub_one_sub_id_le harg
  have hes : |(1 - x ^ 2 / 2) - Real.exp (-(x ^ 2 / 2))| ≤ x ^ 4 := by
    rw [abs_sub_comm, show Real.exp (-(x ^ 2 / 2)) - (1 - x ^ 2 / 2) =
      Real.exp (-(x ^ 2 / 2)) - 1 - -(x ^ 2 / 2) by ring]
    exact he.trans (by nlinarith [sq_nonneg (x ^ 2)])
  calc
    _ ≤ |Real.cos x - (1 - x ^ 2 / 2)| +
        |(1 - x ^ 2 / 2) - Real.exp (-(x ^ 2 / 2))| := abs_sub_le ..
    _ ≤ x ^ 4 + x ^ 4 := add_le_add (cos_secondOrder_bound x hx) hes
    _ = _ := by ring

private theorem abs_diff_products_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |(∏ i ∈ s, a i) - (∏ i ∈ s, b i)| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have has (j : ι) (hj : j ∈ s) : |a j| ≤ 1 := ha j (Finset.mem_insert_of_mem hj)
    have hbs (j : ι) (hj : j ∈ s) : |b j| ≤ 1 := hb j (Finset.mem_insert_of_mem hj)
    let p := ∏ j ∈ s, a j
    let q := ∏ j ∈ s, b j
    have hq : |q| ≤ 1 := by
      dsimp [q]
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun j _ => abs_nonneg (b j)) (fun j hj => hbs j hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    change |a i * p - b i * q| ≤ _
    rw [show a i * p - b i * q = a i * (p - q) + (a i - b i) * q by ring]
    calc
      _ ≤ |a i * (p - q)| + |(a i - b i) * q| := abs_add_le ..
      _ ≤ 1 * |p - q| + |a i - b i| * 1 := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (ha i (Finset.mem_insert_self ..)) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hq (abs_nonneg _))
      _ ≤ _ := by
        simp only [one_mul, mul_one]
        rw [add_comm]
        linarith only [ih has hbs]

/-- The conditional Rademacher characteristic product is within a fourth
moment error of the Gaussian characteristic function with the same variance. -/
theorem abs_cos_product_sub_gaussian {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (ht : ∀ i, |t i| ≤ 1) :
    |(∏ i, Real.cos (t i)) - Real.exp (-(∑ i, t i ^ 2) / 2)| ≤
      2 * ∑ i, t i ^ 4 := by
  have hExp : Real.exp (-(∑ i, t i ^ 2) / 2) =
      ∏ i, Real.exp (-(t i ^ 2 / 2)) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [Finset.sum_neg_distrib, ← Finset.sum_div, neg_div]
  rw [hExp, Finset.mul_sum]
  refine (abs_diff_products_le Finset.univ _ _ (fun i _ => Real.abs_cos_le_one _)
    (fun i _ => ?_)).trans (Finset.sum_le_sum (fun i _ => cos_sub_gaussianFactor_bound _ (ht i)))
  rw [abs_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))

/-- The log-cosine step of the manuscript, expressed through an equivalent
quartic-error bound on the characteristic-function products. -/
theorem tendsto_cos_product_of_fourth_sum {d : ℕ → ℕ} (t : (j : ℕ) → Fin (d j) → ℝ)
    {v : ℝ} (hVar : Tendsto (fun j => ∑ i, t j i ^ 2) atTop (𝓝 v))
    (hFourth : Tendsto (fun j => ∑ i, t j i ^ 4) atTop (𝓝 0)) :
    Tendsto (fun j => ∏ i, Real.cos (t j i)) atTop (𝓝 (Real.exp (-v / 2))) := by
  have hSmall : ∀ᶠ j in atTop, ∀ i, |t j i| ≤ 1 := by
    filter_upwards [hFourth.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hj i
    have hi : t j i ^ 4 ≤ ∑ a, t j a ^ 4 :=
      Finset.single_le_sum (f := fun a => t j a ^ 4) (fun a (_ : a ∈ Finset.univ) => by positivity) (Finset.mem_univ i)
    by_contra! h
    have hp : (1 : ℝ) < |t j i| ^ 4 := by
      simpa only [one_pow] using pow_lt_pow_left₀ h zero_le_one (by decide : (4 : ℕ) ≠ 0)
    rw [abs_pow_four] at hp
    linarith
  let ε := fun j => (∏ i, Real.cos (t j i)) - Real.exp (-(∑ i, t j i ^ 2) / 2)
  have hε : Tendsto ε atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (g := fun j => 2 * ∑ i, t j i ^ 4)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [hSmall] with j hj
      simpa [ε, Real.norm_eq_abs] using abs_cos_product_sub_gaussian (t j) hj
    · simpa only [mul_zero] using hFourth.const_mul 2
  have hMain := Real.continuous_exp.continuousAt.tendsto.comp (hVar.neg.div_const 2)
  have hSum := hε.add hMain
  simpa only [ε, Function.comp_apply, sub_add_cancel, zero_add] using hSum

end SketchOrientation
