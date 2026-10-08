import TrapMicroscopicElimination
import TrapFiniteErrors

set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace CollatzResearch

theorem trap_signed_span_eq_sum (T h g : ℕ → ℤ) (r : ℕ)
    (hstep : ∀ i < r, T (i + 1) = T i + h (i + 1) + g i) :
    h 0 + T r - T 0 =
      (∑ i ∈ Finset.range (r + 1), h i) + ∑ i ∈ Finset.range r, g i := by
  have hs := trap_schedule_segment T (fun i => h (i + 1) + g i) 0 r
    (fun i hi => by simpa only [Nat.zero_add, add_assoc] using hstep i hi)
  simp only [Nat.zero_add, Finset.sum_add_distrib] at hs
  rw [Finset.sum_range_succ']
  linarith

theorem trap_signed_span_difference (T h g : ℕ → ℤ) (r a b : ℕ)
    (hab : a ≤ b) (hbr : b ≤ r)
    (hstep : ∀ i < r, T (i + 1) = T i + h (i + 1) + g i) :
    (h 0 + T r - T 0) - (h a + T b - T a) =
      (∑ i ∈ Finset.range a, h i) + (∑ i ∈ Finset.range a, g i) +
      (∑ i ∈ Finset.range (r - b), h (b + i + 1)) +
        ∑ i ∈ Finset.range (r - b), g (b + i) := by
  have hp := trap_signed_span_eq_sum T h g a (fun i hi => hstep i (by omega))
  rw [Finset.sum_range_succ] at hp
  have ht := trap_schedule_segment T (fun i => h (i + 1) + g i) b (r - b)
    (fun i hi => by simpa only [add_assoc] using hstep (b + i) (by omega))
  rw [Nat.add_sub_of_le hbr, Finset.sum_add_distrib] at ht
  linarith

theorem eventually_trap_height_sublinear (h m : ℕ → ℕ) (e : ℕ → ℤ)
    (N : ℕ → ℝ) (heq : ∀ k, (h k : ℤ) = 4 * (m k : ℤ) + e k)
    (hm : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop, (m k : ℝ) ≤ gamma * N k)
    (he : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop, |(e k : ℝ)| ≤ gamma * N k) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop, (h k : ℝ) ≤ gamma * N k := by
  intro gamma hgamma
  filter_upwards [hm (gamma / 8) (by positivity), he (gamma / 2) (by positivity)]
    with k hmk hek
  have heq' : (h k : ℝ) = 4 * (m k : ℝ) + (e k : ℝ) := by
    exact_mod_cast heq k
  linarith [le_abs_self (e k : ℝ)]

theorem eventually_trap_range_int_sublinear (e : ℕ → ℕ → ℤ) (N : ℕ → ℝ)
    (a t : ℕ) (hN : ∀ᶠ k in atTop, 0 ≤ N k)
    (he : ∀ i < t, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k (a + i) : ℝ)| ≤ gamma * N k) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop,
      |((∑ i ∈ Finset.range t, e k (a + i) : ℤ) : ℝ)| ≤ gamma * N k := by
  have hsum := eventually_trap_finset_abs_sublinear (Finset.range t)
    (fun k i => (e k (a + i) : ℝ)) N hN
    (fun i hi => he i (Finset.mem_range.mp hi))
  intro gamma hgamma
  filter_upwards [hsum gamma hgamma] with k hk
  have habs := Finset.abs_sum_le_sum_abs (fun i => (e k (a + i) : ℝ)) (Finset.range t)
  simpa only [Int.cast_sum] using habs.trans hk

theorem eventually_trap_deleted_span_sublinear
    (T g : ℕ → ℕ → ℤ) (h : ℕ → ℕ → ℕ) (N : ℕ → ℝ) (r a b : ℕ)
    (hab : a ≤ b) (hbr : b ≤ r)
    (hstep : ∀ k i, i < r → T k (i + 1) = T k i + (h k (i + 1) : ℤ) + g k i)
    (hN : ∀ᶠ k in atTop, 0 ≤ N k)
    (hh : ∀ i, i < a ∨ (b < i ∧ i ≤ r) → ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (h k i : ℝ) ≤ gamma * N k)
    (hg : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k i : ℝ)| ≤ gamma * N k) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop,
      |((((h k 0 : ℤ) + T k r - T k 0) -
        ((h k a : ℤ) + T k b - T k a) : ℤ) : ℝ)| ≤ gamma * N k := by
  have hA := eventually_trap_range_int_sublinear (fun k i => (h k i : ℤ)) N 0 a hN
    (by
      intro i hi gamma hgamma
      simpa only [Nat.zero_add, Int.cast_natCast, Nat.abs_cast] using
        hh i (Or.inl hi) gamma hgamma)
  have hB := eventually_trap_range_int_sublinear g N 0 a hN
    (by intro i hi; simpa only [Nat.zero_add] using hg i (by omega))
  have hC := eventually_trap_range_int_sublinear (fun k i => (h k i : ℤ)) N (b + 1)
    (r - b) hN (by
      intro i hi gamma hgamma
      simpa only [Int.cast_natCast, Nat.abs_cast] using
        hh (b + 1 + i) (Or.inr ⟨by omega, by omega⟩) gamma hgamma)
  have hD := eventually_trap_range_int_sublinear g N b (r - b) hN
    (by intro i hi; exact hg (b + i) (by omega))
  intro gamma hgamma
  filter_upwards [hA (gamma / 4) (by positivity), hB (gamma / 4) (by positivity),
    hC (gamma / 4) (by positivity), hD (gamma / 4) (by positivity)] with k hAk hBk hCk hDk
  rw [trap_signed_span_difference (T k) (fun i => (h k i : ℤ)) (g k) r a b hab hbr
    (hstep k)]
  simp only [Int.cast_add, Int.cast_sum, Int.cast_natCast, Nat.zero_add] at *
  have hac : ∑ i ∈ Finset.range (r - b), (h k (b + i + 1) : ℝ) =
      ∑ i ∈ Finset.range (r - b), (h k (b + 1 + i) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show b + i + 1 = b + 1 + i by omega]
  rw [hac]
  calc
    _ ≤ |∑ i ∈ Finset.range a, (h k i : ℝ)| + |∑ i ∈ Finset.range a, (g k i : ℝ)| +
        |∑ i ∈ Finset.range (r - b), (h k (b + 1 + i) : ℝ)| +
        |∑ i ∈ Finset.range (r - b), (g k (b + i) : ℝ)| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ gamma * N k := by linarith

theorem eventually_trap_total_mass_from_entropy
    (T e g : ℕ → ℕ → ℤ) (h m : ℕ → ℕ → ℕ) (N : ℕ → ℕ) (r : ℕ)
    {eta : ℝ} (heta : 0 < eta)
    (hstep : ∀ k i, i < r → T k (i + 1) = T k i + (h k (i + 1) : ℤ) + g k i)
    (hh : ∀ k i, i ≤ r → (h k i : ℤ) = 4 * (m k i : ℤ) + e k i)
    (hgap : ∀ᶠ k in atTop, (N k : ℝ) * Real.log 3 + eta * (N k : ℝ) ≤
      (((h k 0 : ℤ) + T k r - T k 0 : ℤ) : ℝ) * Real.log 2)
    (he : ∀ i ≤ r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k i : ℝ)| ≤ gamma * (N k : ℝ))
    (hg : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k i : ℝ)| ≤ gamma * (N k : ℝ)) :
    ∀ᶠ k in atTop, (eta / (8 * Real.log 2)) * (N k : ℝ) ≤
      ∑ i ∈ Finset.range (r + 1), (m k i : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hN0 : ∀ᶠ k in atTop, (0 : ℝ) ≤ N k := Eventually.of_forall fun _ => by positivity
  have hE := eventually_trap_finset_abs_sublinear (Finset.range (r + 1))
    (fun k i => (e k i : ℝ)) (fun k => (N k : ℝ)) hN0
    (fun i hi => he i (by have := Finset.mem_range.mp hi; omega))
  have hG := eventually_trap_finset_abs_sublinear (Finset.range r)
    (fun k i => (g k i : ℝ)) (fun k => (N k : ℝ)) hN0
    (fun i hi => hg i (Finset.mem_range.mp hi))
  have hrate : 0 < eta / (4 * Real.log 2) := by positivity
  filter_upwards [hgap, hE _ hrate, hG _ hrate] with k hgapk hEk hGk
  have hspan := trap_signed_span_eq_sum (T k) (fun i => (h k i : ℤ)) (g k) r (hstep k)
  have hspan' : (((h k 0 : ℤ) + T k r - T k 0 : ℤ) : ℝ) =
      (∑ i ∈ Finset.range (r + 1), (h k i : ℝ)) +
        ∑ i ∈ Finset.range r, (g k i : ℝ) := by exact_mod_cast hspan
  have hhbound := trap_deleted_height_bound (Finset.range (r + 1))
    (fun i => (h k i : ℝ)) (fun i => (m k i : ℝ)) (fun i => (e k i : ℝ))
    (by
      intro i hi
      have hi' : i ≤ r := by have := Finset.mem_range.mp hi; omega
      exact_mod_cast hh k i hi')
  have hgbound : (∑ i ∈ Finset.range r, (g k i : ℝ)) ≤
      ∑ i ∈ Finset.range r, |(g k i : ℝ)| :=
    Finset.sum_le_sum (fun i _ => le_abs_self (g k i : ℝ))
  have hupper : (((h k 0 : ℤ) + T k r - T k 0 : ℤ) : ℝ) ≤
      4 * (∑ i ∈ Finset.range (r + 1), (m k i : ℝ)) +
        (eta / (2 * Real.log 2)) * (N k : ℝ) := by
    rw [hspan']
    have hrateadd : eta / (4 * Real.log 2) * (N k : ℝ) +
        eta / (4 * Real.log 2) * (N k : ℝ) =
        eta / (2 * Real.log 2) * (N k : ℝ) := by ring
    linarith
  have hupper' := mul_le_mul_of_nonneg_right hupper hlog2.le
  have hterm : eta / (2 * Real.log 2) * (N k : ℝ) * Real.log 2 =
      eta / 2 * (N k : ℝ) := by field_simp
  have hpositive : 0 ≤ (N k : ℝ) * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hmain : eta * (N k : ℝ) ≤
      8 * Real.log 2 * (∑ i ∈ Finset.range (r + 1), (m k i : ℝ)) := by
    rw [add_mul, hterm] at hupper'
    linarith
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 8 * Real.log 2 by positivity)).mpr
  simpa only [mul_comm] using hmain

end CollatzResearch

#print axioms CollatzResearch.trap_signed_span_difference
#print axioms CollatzResearch.eventually_trap_deleted_span_sublinear
#print axioms CollatzResearch.eventually_trap_total_mass_from_entropy
