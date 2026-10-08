import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
Compactness selects a fixed set of macroscopic coordinates from a fixed finite
family. The other coordinates are sublinear along the selected subsequence.
There is no claim about a family whose number of coordinates grows.
-/

set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace CollatzResearch

theorem trap_finset_uniform_positive {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ i ∈ s, delta ≤ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨delta, hdelta, hd⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hai := ha i (Finset.mem_insert_self i s)
      refine ⟨min delta (a i), lt_min hdelta hai, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hd j hj)

theorem trap_block_ratio_subsequence {r : ℕ} (m : ℕ → Fin r → ℝ) (N : ℕ → ℕ)
    (hm : ∀ k i, 0 ≤ m k i ∧ m k i ≤ (N k : ℝ)) :
    ∃ (limit : Fin r → ℝ) (sigma : ℕ → ℕ),
      (∀ i, 0 ≤ limit i ∧ limit i ≤ 1) ∧ StrictMono sigma ∧
      ∀ i, Tendsto (fun k => m (sigma k) i / ((N (sigma k) : ℝ) + 1))
        atTop (𝓝 (limit i)) := by
  let x : ℕ → Fin r → ℝ := fun k i => m k i / ((N k : ℝ) + 1)
  have hx : ∀ k, x k ∈ Set.Icc (0 : Fin r → ℝ) 1 := by
    intro k
    constructor <;> intro i
    · exact div_nonneg (hm k i).1 (by positivity)
    · exact (div_le_one (by positivity)).mpr (by linarith [(hm k i).2])
  obtain ⟨limit, hl, sigma, hsigma, hlim⟩ := isCompact_Icc.tendsto_subseq hx
  refine ⟨limit, sigma, (fun i => ⟨hl.1 i, hl.2 i⟩), hsigma, ?_⟩
  intro i
  exact (tendsto_pi_nhds.mp hlim) i

theorem trap_block_subsequence {r : ℕ} (m : ℕ → Fin r → ℝ) (N : ℕ → ℕ)
    (hm : ∀ k i, 0 ≤ m k i ∧ m k i ≤ (N k : ℝ))
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop) :
    ∃ (sigma : ℕ → ℕ) (S : Finset (Fin r)) (delta : ℝ),
      StrictMono sigma ∧ 0 < delta ∧
      (∀ i ∈ S, ∀ᶠ k in atTop, delta * (N (sigma k) : ℝ) ≤ m (sigma k) i) ∧
      (∀ i ∉ S, ∀ gamma : ℝ, 0 < gamma →
        ∀ᶠ k in atTop, m (sigma k) i ≤ gamma * (N (sigma k) : ℝ)) := by
  classical
  obtain ⟨limit, sigma, hl, hsigma, hlim⟩ := trap_block_ratio_subsequence m N hm
  let S : Finset (Fin r) := Finset.univ.filter (fun i => 0 < limit i)
  obtain ⟨delta, hdelta, hd⟩ := trap_finset_uniform_positive S
    (fun i => limit i / 2) (by
      intro i hi
      have hi' : 0 < limit i := (Finset.mem_filter.mp hi).2
      positivity)
  have hNsigma := hN.comp hsigma.tendsto_atTop
  refine ⟨sigma, S, delta, hsigma, hdelta, ?_, ?_⟩
  · intro i hi
    have hpos : 0 < limit i := (Finset.mem_filter.mp hi).2
    have hlt : delta < limit i := by linarith [hd i hi]
    filter_upwards [(hlim i).eventually_const_lt hlt] with k hk
    have hdpos : 0 < (N (sigma k) : ℝ) + 1 := by positivity
    have hmul := (lt_div_iff₀ hdpos).mp hk
    linarith
  · intro i hi gamma hgamma
    have hzero : limit i = 0 := by
      have hnonpos : ¬ 0 < limit i := by
        intro hpos
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩)
      linarith [(hl i).1]
    have hsmall := (hlim i).eventually_lt_const (show limit i < gamma / 2 by
      rw [hzero]; positivity)
    filter_upwards [hsmall, hNsigma.eventually_ge_atTop 1] with k hk hn
    change 1 ≤ (N (sigma k) : ℝ) at hn
    have hdpos : 0 < (N (sigma k) : ℝ) + 1 := by positivity
    have hmul := (div_lt_iff₀ hdpos).mp hk
    have hprod := mul_le_mul_of_nonneg_left hn (show 0 ≤ gamma / 2 by positivity)
    linarith

theorem trap_sublinear_support_nonempty {r : ℕ}
    (m : ℕ → Fin r → ℝ) (N : ℕ → ℕ) (S : Finset (Fin r))
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (hsmall : ∀ i ∉ S, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, m k i ≤ gamma * (N k : ℝ))
    (c : ℝ) (hc : 0 < c)
    (hmass : ∀ᶠ k in atTop, c * (N k : ℝ) ≤ ∑ i : Fin r, m k i) :
    S.Nonempty := by
  classical
  by_contra hS
  have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
  let gamma : ℝ := c / (2 * ((r : ℝ) + 1))
  have hgamma : 0 < gamma := by dsimp [gamma]; positivity
  have hall : ∀ᶠ k in atTop, ∀ i : Fin r, m k i ≤ gamma * (N k : ℝ) := by
    have hall' := (eventually_all_finset (Finset.univ : Finset (Fin r))).mpr
      (fun i _ => hsmall i (by simp [hempty]) gamma hgamma)
    simpa only [Finset.mem_univ, forall_true_left] using hall'
  obtain ⟨k, hk, hmassk, hn⟩ :=
    (hall.and (hmass.and (hN.eventually_ge_atTop 1))).exists
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hk i)
  have hsum' : (∑ i : Fin r, m k i) ≤ (r : ℝ) * gamma * (N k : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc] using hsum
  have hfactor : (r : ℝ) * gamma < c := by
    dsimp [gamma]
    have hr : 0 < 2 * ((r : ℝ) + 1) := by positivity
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hr).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  have hstrict := mul_lt_mul_of_pos_right hfactor (show 0 < (N k : ℝ) by linarith)
  linarith

theorem trap_block_subsequence_nonempty {r : ℕ}
    (m : ℕ → Fin r → ℝ) (N : ℕ → ℕ)
    (hm : ∀ k i, 0 ≤ m k i ∧ m k i ≤ (N k : ℝ))
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (c : ℝ) (hc : 0 < c)
    (hmass : ∀ᶠ k in atTop, c * (N k : ℝ) ≤ ∑ i : Fin r, m k i) :
    ∃ (sigma : ℕ → ℕ) (S : Finset (Fin r)) (delta : ℝ),
      StrictMono sigma ∧ S.Nonempty ∧ 0 < delta ∧
      (∀ i ∈ S, ∀ᶠ k in atTop, delta * (N (sigma k) : ℝ) ≤ m (sigma k) i) ∧
      (∀ i ∉ S, ∀ gamma : ℝ, 0 < gamma →
        ∀ᶠ k in atTop, m (sigma k) i ≤ gamma * (N (sigma k) : ℝ)) := by
  obtain ⟨sigma, S, delta, hsigma, hdelta, hlarge, hsmall⟩ :=
    trap_block_subsequence m N hm hN
  have hS := trap_sublinear_support_nonempty (fun k => m (sigma k))
    (fun k => N (sigma k)) S (hN.comp hsigma.tendsto_atTop) hsmall c hc
    (hsigma.tendsto_atTop.eventually hmass)
  exact ⟨sigma, S, delta, hsigma, hS, hdelta, hlarge, hsmall⟩

end CollatzResearch

#print axioms CollatzResearch.trap_block_ratio_subsequence
#print axioms CollatzResearch.trap_block_subsequence
#print axioms CollatzResearch.trap_sublinear_support_nonempty
#print axioms CollatzResearch.trap_block_subsequence_nonempty
