import Mathlib.Tactic

/-! Finite walk bounds from the number of white sample points. -/

set_option autoImplicit false
open scoped BigOperators Classical

namespace CollatzResearch

noncomputable def trapWhiteCount (W : ℕ → Prop) (M : ℕ) : ℕ :=
  ((Finset.range M).filter W).card

theorem trap_white_count_mono (W : ℕ → Prop) : Monotone (trapWhiteCount W) := by
  intro a b hab
  apply Finset.card_le_card
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hq, hW⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hq).trans_le hab), hW⟩

theorem trap_white_count_succ (W : ℕ → Prop) (q : ℕ) (hq : W q) :
    trapWhiteCount W (q + 1) = trapWhiteCount W q + 1 := by
  simp [trapWhiteCount, Finset.range_add_one, Finset.filter_insert, hq]

theorem trap_white_count_of_all (W : ℕ → Prop) (M : ℕ)
    (hW : ∀ q < M, W q) : trapWhiteCount W M = M := by
  have hf : (Finset.range M).filter W = Finset.range M :=
    Finset.filter_eq_self.mpr (fun q hq => hW q (Finset.mem_range.mp hq))
  simp only [trapWhiteCount, hf, Finset.card_range]

theorem trap_nat_walk_le (j : ℕ → ℕ) (H M : ℕ)
    (hstep : ∀ q < M, j (q + 1) ≤ j q + H) :
    j M ≤ j 0 + H * M := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hp := ih (fun q hq => hstep q (by omega))
      have hs := hstep M (by omega)
      nlinarith

theorem trap_initial_entry_le (W : ℕ → Prop) (j : ℕ → ℕ) (H M first K : ℕ)
    (hfirst : first ≤ M) (hcount : trapWhiteCount W M ≤ K)
    (hwhite : ∀ q < first, W q)
    (hstep : ∀ q < M, j (q + 1) ≤ j q + H) :
    first ≤ K ∧ j first ≤ j 0 + H * K := by
  have htime : first ≤ K := by
    rw [← trap_white_count_of_all W first hwhite]
    exact (trap_white_count_mono W hfirst).trans hcount
  refine ⟨htime, (trap_nat_walk_le j H first (fun q hq => hstep q (by omega))).trans ?_⟩
  exact Nat.add_le_add_left (Nat.mul_le_mul_left H htime) _

/-- A step from below the top costs one overshoot; every subsequent step
from above the top is charged to a white sample point. -/
theorem trap_post_top_gap_le (W : ℕ → Prop) (l : ℕ → ℝ)
    (a b : ℕ) (T V : ℝ) (hab : a ≤ b) (hV : 0 ≤ V) (ha : l a ≤ T)
    (hstep : ∀ q < b, l (q + 1) ≤ l q + V)
    (hwhite : ∀ q, a ≤ q → q < b → T < l q → W q) :
    l b ≤ T + V * ((trapWhiteCount W b - trapWhiteCount W a : ℕ) + 1 : ℝ) := by
  revert hstep hwhite
  induction b, hab using Nat.le_induction with
  | base =>
      intro _ _
      simpa using ha.trans (le_add_of_nonneg_right hV)
  | succ b hab ih =>
      intro hstep hwhite
      have hb := ih (fun q hq => hstep q (by omega))
        (fun q haq hqb hT => hwhite q haq (by omega) hT)
      have hs := hstep b (by omega)
      by_cases hT : T < l b
      · have hW := hwhite b hab (by omega) hT
        have hCa := trap_white_count_mono W hab
        rw [trap_white_count_succ W b hW,
          show trapWhiteCount W b + 1 - trapWhiteCount W a =
            (trapWhiteCount W b - trapWhiteCount W a) + 1 by omega]
        push_cast
        linarith
      · have hcount0 : (0 : ℝ) ≤ (trapWhiteCount W (b + 1) - trapWhiteCount W a : ℕ) := by
          positivity
        have hprod := mul_nonneg hV hcount0
        linarith

theorem trap_white_adjacent_sum_le (W : ℕ → Prop) (t : ℕ → ℕ) (r M : ℕ)
    (ht : ∀ i < r, t i ≤ t (i + 1)) (hM : t r ≤ M) :
    (∑ i ∈ Finset.range r,
      (trapWhiteCount W (t (i + 1)) - trapWhiteCount W (t i))) ≤ trapWhiteCount W M := by
  have hsum : (∑ i ∈ Finset.range r,
      (trapWhiteCount W (t (i + 1)) - trapWhiteCount W (t i))) ≤ trapWhiteCount W (t r) := by
    clear hM
    induction r with
    | zero => simp
    | succ r ih =>
        have hp := ih (fun i hi => ht i (by omega))
        have hm := trap_white_count_mono W (ht r (by omega))
        rw [Finset.sum_range_succ]
        omega
  exact hsum.trans (trap_white_count_mono W hM)

theorem trap_post_top_gap_sum_le (W : ℕ → Prop) (l T : ℕ → ℝ)
    (t : ℕ → ℕ) (r M : ℕ) (V : ℝ) (hV : 0 ≤ V)
    (ht : ∀ i < r, t i ≤ t (i + 1)) (hM : ∀ i ≤ r, t i ≤ M)
    (hstart : ∀ i < r, l (t i) ≤ T i)
    (hend : ∀ i < r, T i ≤ l (t (i + 1)))
    (hstep : ∀ q < M, l (q + 1) ≤ l q + V)
    (hwhite : ∀ i < r, ∀ q, t i ≤ q → q < t (i + 1) → T i < l q → W q) :
    (∑ i ∈ Finset.range r, |l (t (i + 1)) - T i|) ≤
      V * ((trapWhiteCount W M : ℝ) + r) := by
  have hpoint : ∀ i < r, |l (t (i + 1)) - T i| ≤
      V * (((trapWhiteCount W (t (i + 1)) - trapWhiteCount W (t i) : ℕ) : ℝ) + 1) := by
    intro i hi
    rw [abs_of_nonneg (sub_nonneg.mpr (hend i hi))]
    have hg := trap_post_top_gap_le W l (t i) (t (i + 1)) (T i) V
      (ht i hi) hV (hstart i hi) (fun q hq => hstep q (by have := hM (i + 1) (by omega); omega))
      (hwhite i hi)
    linarith
  have hs := Finset.sum_le_sum (s := Finset.range r)
    (fun i hi => hpoint i (Finset.mem_range.mp hi))
  have hc := trap_white_adjacent_sum_le W t r M ht (hM r le_rfl)
  have hcr : (∑ i ∈ Finset.range r,
      ((trapWhiteCount W (t (i + 1)) - trapWhiteCount W (t i) : ℕ) : ℝ)) ≤
        (trapWhiteCount W M : ℝ) := by exact_mod_cast hc
  calc
    (∑ i ∈ Finset.range r, |l (t (i + 1)) - T i|) ≤
        V * ((∑ i ∈ Finset.range r,
          ((trapWhiteCount W (t (i + 1)) - trapWhiteCount W (t i) : ℕ) : ℝ)) + r) := by
      simpa only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one] using hs
    _ ≤ V * ((trapWhiteCount W M : ℝ) + r) := by gcongr

theorem trap_terminal_top_bound (W : ℕ → Prop) (l : ℕ → ℝ)
    (a M K : ℕ) (T V : ℝ) (haM : a ≤ M) (hV : 0 ≤ V) (ha : l a ≤ T)
    (hcount : trapWhiteCount W M ≤ K)
    (hstep : ∀ q < M, l (q + 1) ≤ l q + V)
    (hwhite : ∀ q, a ≤ q → q < M → T < l q → W q) :
    l M ≤ T + V * ((K : ℝ) + 1) := by
  apply (trap_post_top_gap_le W l a M T V haM hV ha hstep hwhite).trans
  have hc : trapWhiteCount W M - trapWhiteCount W a ≤ K := (Nat.sub_le _ _).trans hcount
  have hcr : ((trapWhiteCount W M - trapWhiteCount W a : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hc
  gcongr

end CollatzResearch

#print axioms CollatzResearch.trap_initial_entry_le
#print axioms CollatzResearch.trap_post_top_gap_le
#print axioms CollatzResearch.trap_post_top_gap_sum_le
#print axioms CollatzResearch.trap_terminal_top_bound
