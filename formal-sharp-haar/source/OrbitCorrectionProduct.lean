import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import OptimalCylinderPacking

set_option autoImplicit false

open Filter Topology

namespace CollatzCanonical.Correction

variable {ι : Type*}

theorem summable_log_correction {f : ι → ℝ} (hpos : ∀ i, 0 ≤ f i)
    (hf : Summable f) : Summable (fun i ↦ Real.log (1 + f i)) := by
  apply Summable.of_nonneg_of_le
    (fun i ↦ Real.log_nonneg (by linarith [hpos i])) _ hf
  intro i
  simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + f i by linarith [hpos i])

theorem product_eq_exp_sum {f : ι → ℝ} (hpos : ∀ i, 0 ≤ f i)
    (hf : Summable f) :
    (∏' i, (1 + f i)) = Real.exp (∑' i, Real.log (1 + f i)) := by
  have hl := summable_log_correction hpos hf
  have hp : HasProd (fun i ↦ 1 + f i) (Real.exp (∑' i, Real.log (1 + f i))) :=
    by
      have heq : (Real.exp ∘ fun i ↦ Real.log (1 + f i)) = (fun i ↦ 1 + f i) := by
        ext i
        exact Real.exp_log (by linarith [hpos i])
      simpa only [heq] using hl.hasSum.rexp
  exact hp.tprod_eq

theorem product_bounds {f : ι → ℝ} (hpos : ∀ i, 0 ≤ f i)
    (hf : Summable f) :
    1 ≤ ∏' i, (1 + f i) ∧ (∏' i, (1 + f i)) ≤ Real.exp (∑' i, f i) := by
  have hp : ∀ i, 0 < 1 + f i := fun i ↦ by linarith [hpos i]
  have hl := summable_log_correction hpos hf
  rw [product_eq_exp_sum hpos hf]
  constructor
  · calc
      1 = Real.exp 0 := by simp
      _ ≤ _ := Real.exp_le_exp.mpr
        (tsum_nonneg fun i ↦ Real.log_nonneg (by linarith [hpos i]))
  · exact Real.exp_le_exp.mpr (Summable.tsum_le_tsum
      (fun i ↦ by simpa using Real.log_le_sub_one_of_pos (hp i)) hl hf)

theorem product_positive {f : ι → ℝ} (hpos : ∀ i, 0 ≤ f i)
    (hf : Summable f) : 0 < ∏' i, (1 + f i) := by
  linarith [(product_bounds hpos hf).1]

theorem tail_product_tendsto_one {f : ℕ → ℝ} (hpos : ∀ i, 0 ≤ f i)
    (hf : Summable f) :
    Tendsto (fun j ↦ ∏' i, (1 + f (i + j))) atTop (𝓝 1) := by
  have hs : Summable (fun i ↦ Real.log (1 + f i)) := summable_log_correction hpos hf
  have hlim := (Real.continuous_exp.tendsto 0).comp
    (tendsto_sum_nat_add (fun i ↦ Real.log (1 + f i)))
  simp only [Real.exp_zero] at hlim
  convert hlim using 1
  ext j
  apply product_eq_exp_sum (fun i ↦ hpos (i+j))
  exact (summable_nat_add_iff j).2 hf

theorem finite_product_bounds {f : ι → ℝ} (hpos : ∀ i, 0 ≤ f i) (s : Finset ι) :
    1 ≤ ∏ i ∈ s, (1 + f i) ∧
      (∏ i ∈ s, (1 + f i)) ≤ Real.exp (∑ i ∈ s, f i) := by
  classical
  constructor
  · calc
      1 = ∏ i ∈ s, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ by norm_num)
        (fun i _ ↦ by linarith [hpos i])
  · rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro i hi
      linarith [hpos i]
    · intro i hi
      have := Real.add_one_le_exp (f i)
      linarith

open CollatzCylinderPacking

noncomputable def oddCorrection (n : ℕ) : ℝ :=
  if n % 2 = 1 then (3 * (n : ℝ))⁻¹ else 0

theorem oddCorrection_nonneg (n : ℕ) : 0 ≤ oddCorrection n := by
  unfold oddCorrection
  split_ifs <;> positivity

theorem step_pos {n : ℕ} (hn : 0 < n) : 0 < step n := by
  unfold step
  split_ifs with he <;> omega

theorem iterate_pos (k : ℕ) {n : ℕ} (hn : 0 < n) : 0 < iterate k n := by
  induction k with
  | zero => exact hn
  | succ k ih => exact step_pos ih

theorem oddCorrection_le_third_reciprocal (n : ℕ) :
    oddCorrection n ≤ (1 / 3 : ℝ) * (n : ℝ)⁻¹ := by
  unfold oddCorrection
  split_ifs
  · simp only [mul_inv_rev, one_div]
    exact le_of_eq (mul_comm _ _)
  · positivity

theorem orbit_product_bounds (n : ℕ)
    (hs : Summable (fun i ↦ ((iterate i n : ℕ) : ℝ)⁻¹)) :
    1 ≤ ∏' i, (1 + oddCorrection (iterate i n)) ∧
      (∏' i, (1 + oddCorrection (iterate i n))) ≤
        Real.exp ((1 / 3 : ℝ) * ∑' i, ((iterate i n : ℕ) : ℝ)⁻¹) := by
  have hd := hs.mul_left (1 / 3 : ℝ)
  have hc : Summable (fun i ↦ oddCorrection (iterate i n)) :=
    Summable.of_nonneg_of_le (fun i ↦ oddCorrection_nonneg _) 
      (fun i ↦ oddCorrection_le_third_reciprocal _) hd
  obtain ⟨hl, hu⟩ := product_bounds (fun i ↦ oddCorrection_nonneg _) hc
  refine ⟨hl, hu.trans ?_⟩
  apply Real.exp_le_exp.mpr
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun i ↦ oddCorrection_le_third_reciprocal _) hc hd


theorem step_correction_identity {n : ℕ} (hn : 0 < n) :
    (2 : ℝ) * (step n : ℝ) =
      (3 : ℝ) ^ (n % 2) * (n : ℝ) * (1 + oddCorrection n) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  by_cases he : n % 2 = 0
  · have hstep : (2 : ℝ) * (step n : ℝ) = n := by exact_mod_cast step_even he
    simpa [oddCorrection, he] using hstep
  · have ho : n % 2 = 1 := by omega
    have hstep : (2 : ℝ) * (step n : ℝ) = 3 * n + 1 := by
      exact_mod_cast step_odd ho
    rw [ho, pow_one, hstep]
    simp only [oddCorrection, ho, if_true]
    field_simp

theorem iterate_correction_identity (k : ℕ) {n : ℕ} (hn : 0 < n) :
    (2 : ℝ) ^ k * (iterate k n : ℝ) =
      (3 : ℝ) ^ oddCount k n * (n : ℝ) *
        ∏ i ∈ Finset.range k, (1 + oddCorrection (iterate i n)) := by
  induction k with
  | zero => simp [iterate, oddCount]
  | succ k ih =>
    calc
      (2 : ℝ) ^ (k+1) * (iterate (k+1) n : ℝ) =
          2 ^ k * (2 * (step (iterate k n) : ℝ)) := by
            simp only [iterate, pow_succ]
            ring
      _ = 2 ^ k * (3 ^ (iterate k n % 2) * (iterate k n : ℝ) *
            (1 + oddCorrection (iterate k n))) := by
              rw [step_correction_identity (iterate_pos k hn)]
      _ = (2 ^ k * (iterate k n : ℝ)) * 3 ^ (iterate k n % 2) *
            (1 + oddCorrection (iterate k n)) := by ring
      _ = _ := by
        rw [ih]
        simp only [oddCount, pow_add, Finset.prod_range_succ]
        ring

theorem iterate_add (i j n : ℕ) : iterate (i+j) n = iterate i (iterate j n) := by
  induction i with
  | zero => simp [iterate]
  | succ i ih => simp only [Nat.succ_add, iterate, ih]

theorem orbit_corrections_summable (n : ℕ)
    (hs : Summable (fun i ↦ ((iterate i n : ℕ) : ℝ)⁻¹)) :
    Summable (fun i ↦ oddCorrection (iterate i n)) :=
  Summable.of_nonneg_of_le (fun _ ↦ oddCorrection_nonneg _)
    (fun _ ↦ oddCorrection_le_third_reciprocal _) (hs.mul_left (1 / 3 : ℝ))

theorem forward_orbit_product_tendsto_one (n : ℕ)
    (hs : Summable (fun i ↦ ((iterate i n : ℕ) : ℝ)⁻¹)) :
    Tendsto (fun j ↦ ∏' i, (1 + oddCorrection (iterate i (iterate j n))))
      atTop (𝓝 1) := by
  simpa only [iterate_add] using tail_product_tendsto_one
    (fun i ↦ oddCorrection_nonneg (iterate i n)) (orbit_corrections_summable n hs)

theorem product_prefix_tail {f : ℕ → ℝ} (hpos : ∀ i, 0 ≤ f i)
    (hf : Summable f) (j : ℕ) :
    (∏ i ∈ Finset.range j, (1 + f i)) * (∏' i, (1 + f (i+j))) =
      ∏' i, (1 + f i) := by
  have hl := summable_log_correction hpos hf
  rw [product_eq_exp_sum hpos hf,
    product_eq_exp_sum (fun i ↦ hpos (i+j)) ((summable_nat_add_iff j).2 hf),
    ← hl.sum_add_tsum_nat_add j, Real.exp_add, Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (by linarith [hpos i])).symm

theorem orbit_product_prefix_tail (n j : ℕ)
    (hs : Summable (fun i ↦ ((iterate i n : ℕ) : ℝ)⁻¹)) :
    (∏ i ∈ Finset.range j, (1 + oddCorrection (iterate i n))) *
      (∏' i, (1 + oddCorrection (iterate i (iterate j n)))) =
        ∏' i, (1 + oddCorrection (iterate i n)) := by
  simpa only [iterate_add] using product_prefix_tail
    (fun i ↦ oddCorrection_nonneg (iterate i n)) (orbit_corrections_summable n hs) j


theorem finite_orbit_product_bounds (n k : ℕ) :
    1 ≤ ∏ i ∈ Finset.range k, (1 + oddCorrection (iterate i n)) ∧
      (∏ i ∈ Finset.range k, (1 + oddCorrection (iterate i n))) ≤
        Real.exp ((1 / 3 : ℝ) * ∑ i ∈ Finset.range k, (iterate i n : ℝ)⁻¹) := by
  obtain ⟨hl, hu⟩ := finite_product_bounds
    (fun i ↦ oddCorrection_nonneg (iterate i n)) (Finset.range k)
  refine ⟨hl, hu.trans (Real.exp_le_exp.mpr ?_)⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ oddCorrection_le_third_reciprocal _

theorem finite_orbit_product_le_of_reciprocal_bound (n k : ℕ) {R : ℝ}
    (hR : (∑ i ∈ Finset.range k, (iterate i n : ℝ)⁻¹) ≤ R) :
    1 ≤ ∏ i ∈ Finset.range k, (1 + oddCorrection (iterate i n)) ∧
      (∏ i ∈ Finset.range k, (1 + oddCorrection (iterate i n))) ≤ Real.exp (R/3) := by
  obtain ⟨hl, hu⟩ := finite_orbit_product_bounds n k
  refine ⟨hl, hu.trans (Real.exp_le_exp.mpr ?_)⟩
  linarith

#print axioms product_bounds
#print axioms tail_product_tendsto_one
#print axioms orbit_product_bounds
#print axioms iterate_correction_identity
#print axioms forward_orbit_product_tendsto_one
#print axioms orbit_product_prefix_tail
#print axioms finite_orbit_product_le_of_reciprocal_bound

end CollatzCanonical.Correction
