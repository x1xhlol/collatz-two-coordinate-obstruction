import Erdos1135.Tao.Probability.LogWindow
import Mathlib.Tactic

/-!
# Logarithmic Window Prefix Bridges

This module relates finite odd logarithmic windows to the ambient prefix
`logCount` API.  The prefix is `hi`, matching the project convention that
`logCount s N` sums over the positive values `1, ..., N`.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

/-- Set view of the inclusive finite odd window `[lo, hi]`. -/
def oddLogWindowSet (lo hi : ℕ) : Set ℕ :=
  {n : ℕ | lo ≤ n ∧ n ≤ hi ∧ n % 2 = 1}

@[simp]
theorem oddLogWindowSet_mem {lo hi n : ℕ} :
    n ∈ oddLogWindowSet lo hi ↔ lo ≤ n ∧ n ≤ hi ∧ n % 2 = 1 := by
  rfl

theorem oddLogWindowSet_subset_Iic (lo hi : ℕ) :
    oddLogWindowSet lo hi ⊆ Set.Iic hi := by
  intro n hn
  exact (oddLogWindowSet_mem.mp hn).2.1

theorem oddLogWindowSet_disjoint_of_hi_lt_lo
    {lo₁ hi₁ lo₂ hi₂ : ℕ} (hsep : hi₁ < lo₂) :
    Disjoint (oddLogWindowSet lo₁ hi₁) (oddLogWindowSet lo₂ hi₂) := by
  rw [Set.disjoint_left]
  intro n hn₁ hn₂
  have hn_hi₁ : n ≤ hi₁ := (oddLogWindowSet_mem.mp hn₁).2.1
  have hlo₂_n : lo₂ ≤ n := (oddLogWindowSet_mem.mp hn₂).1
  omega

theorem oddLogWindowSet_disjoint_of_hi_lt_lo_symm
    {lo₁ hi₁ lo₂ hi₂ : ℕ} (hsep : hi₂ < lo₁) :
    Disjoint (oddLogWindowSet lo₁ hi₁) (oddLogWindowSet lo₂ hi₂) := by
  exact (oddLogWindowSet_disjoint_of_hi_lt_lo
    (lo₁ := lo₂) (hi₁ := hi₂) (lo₂ := lo₁) (hi₂ := hi₁) hsep).symm

theorem oddLogWindowSet_pairwise_disjoint_of_ordered_gaps
    (I : Finset ℕ) (lo hi : ℕ → ℕ)
    (hgap : ∀ i ∈ I, ∀ j ∈ I, i < j → hi i < lo j) :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (oddLogWindowSet (lo i) (hi i)) (oddLogWindowSet (lo j) (hi j)) := by
  intro i hiI j hjI hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact oddLogWindowSet_disjoint_of_hi_lt_lo (hgap i hiI j hjI hijlt)
  · exact oddLogWindowSet_disjoint_of_hi_lt_lo_symm (hgap j hjI i hiI hjilt)

/-- Prefix indices `i` whose positive values `i + 1` lie in the odd window. -/
def oddLogWindowPrefixIndices (lo hi : ℕ) : Finset ℕ :=
  (Finset.range hi).filter
    (fun i => lo ≤ i + 1 ∧ i + 1 ≤ hi ∧ (i + 1) % 2 = 1)

@[simp]
theorem oddLogWindow_mem_set {lo hi n : ℕ} :
    n ∈ oddLogWindow lo hi ↔ n ∈ oddLogWindowSet lo hi := by
  rw [oddLogWindow_mem, oddLogWindowSet_mem]

@[simp]
theorem oddLogWindowPrefixIndices_mem {lo hi i : ℕ} :
    i ∈ oddLogWindowPrefixIndices lo hi ↔
      i < hi ∧ i + 1 ∈ oddLogWindowSet lo hi := by
  simp [oddLogWindowPrefixIndices]

theorem oddLogWindow_eq_image_prefixIndices (lo hi : ℕ) :
    oddLogWindow lo hi = (oddLogWindowPrefixIndices lo hi).image (fun i => i + 1) := by
  ext n
  rw [Finset.mem_image]
  constructor
  · intro hn
    have hmem := oddLogWindow_mem.mp hn
    refine ⟨n - 1, ?_, by omega⟩
    rw [oddLogWindowPrefixIndices, Finset.mem_filter, Finset.mem_range]
    omega
  · rintro ⟨i, hi_mem, rfl⟩
    rw [oddLogWindowPrefixIndices, Finset.mem_filter, Finset.mem_range] at hi_mem
    exact oddLogWindow_mem.mpr hi_mem.2

theorem oddLogWindow_filter_eq_image_prefixIndices_filter (lo hi : ℕ) (E : Set ℕ)
    [DecidablePred (fun n => n ∈ E)] :
    (oddLogWindow lo hi).filter (fun n => n ∈ E) =
      ((oddLogWindowPrefixIndices lo hi).filter (fun i => i + 1 ∈ E)).image
        (fun i => i + 1) := by
  ext n
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · intro hn
    have _hmem := oddLogWindow_mem.mp hn.1
    refine ⟨n - 1, ?_, by omega⟩
    rw [Finset.mem_filter, oddLogWindowPrefixIndices, Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · simpa [show n - 1 + 1 = n by omega] using hn.2
  · rintro ⟨i, hi_mem, rfl⟩
    rw [Finset.mem_filter] at hi_mem
    constructor
    · rw [oddLogWindow_eq_image_prefixIndices]
      exact Finset.mem_image.mpr ⟨i, hi_mem.1, rfl⟩
    · exact hi_mem.2

theorem logCount_oddLogWindowSet_eq_prefix_sum (lo hi : ℕ) :
    logCount (oddLogWindowSet lo hi) hi =
      ∑ i ∈ oddLogWindowPrefixIndices lo hi, logWeight i := by
  classical
  simp [logCount, oddLogWindowPrefixIndices, oddLogWindowSet, Finset.sum_filter]

theorem logFinsetMass_oddLogWindow_eq_prefix_sum (lo hi : ℕ) :
    logFinsetMass (oddLogWindow lo hi) =
      ∑ i ∈ oddLogWindowPrefixIndices lo hi, logWeight i := by
  classical
  rw [oddLogWindow_eq_image_prefixIndices]
  unfold logFinsetMass
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _hi_mem
    simp [logNatWeight]
  · intro a _ b _ h
    exact Nat.succ.inj h

theorem logCount_oddLogWindowSet_eq_logFinsetMass (lo hi : ℕ) :
    logCount (oddLogWindowSet lo hi) hi =
      logFinsetMass (oddLogWindow lo hi) := by
  rw [logCount_oddLogWindowSet_eq_prefix_sum, logFinsetMass_oddLogWindow_eq_prefix_sum]

theorem logCount_oddLogWindowSet_inter_eq_prefix_sum (lo hi : ℕ) (E : Set ℕ)
    [DecidablePred (fun n => n ∈ E)] :
    logCount (oddLogWindowSet lo hi ∩ E) hi =
      ∑ i ∈ (oddLogWindowPrefixIndices lo hi).filter (fun i => i + 1 ∈ E),
        logWeight i := by
  classical
  simp [logCount, oddLogWindowPrefixIndices, oddLogWindowSet, Set.mem_inter_iff,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi_mem
  by_cases hp : lo ≤ i + 1 ∧ i < hi ∧ (i + 1) % 2 = 1
  · by_cases he : i + 1 ∈ E <;> simp [hp, he]
  · simp [hp]

theorem logFinset_filter_event_eq_prefix_sum (lo hi : ℕ) (E : Set ℕ)
    [DecidablePred (fun n => n ∈ E)] :
    (∑ n ∈ (oddLogWindow lo hi).filter (fun n => n ∈ E), logNatWeight n) =
      ∑ i ∈ (oddLogWindowPrefixIndices lo hi).filter (fun i => i + 1 ∈ E),
        logWeight i := by
  classical
  rw [oddLogWindow_filter_eq_image_prefixIndices_filter]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _hi_mem
    simp [logNatWeight]
  · intro a _ b _ h
    exact Nat.succ.inj h

private theorem sum_oddLogWindowPrefixIndices_filter_eq
    (lo hi : ℕ) (E : Set ℕ) [DecidablePred (fun n => n ∈ E)] :
    (∑ i ∈ (oddLogWindowPrefixIndices lo hi).filter (fun i => i + 1 ∈ E),
      logWeight i) =
      ∑ n ∈ (oddLogWindow lo hi).filter (fun n => n ∈ E), logNatWeight n :=
  (logFinset_filter_event_eq_prefix_sum lo hi E).symm

private theorem logCount_oddLogWindowSet_inter_eq_filter_sum (lo hi : ℕ) (E : Set ℕ)
    [DecidablePred (fun n => n ∈ E)] :
    logCount (oddLogWindowSet lo hi ∩ E) hi =
      ∑ n ∈ (oddLogWindow lo hi).filter (fun n => n ∈ E), logNatWeight n := by
  rw [logCount_oddLogWindowSet_inter_eq_prefix_sum,
    sum_oddLogWindowPrefixIndices_filter_eq]

theorem logFinsetProb_oddLogWindow_eq_logCount_ratio
    (lo hi : ℕ) (E : Set ℕ) :
    logFinsetProb (oddLogWindow lo hi) E =
      logCount (oddLogWindowSet lo hi ∩ E) hi /
        logCount (oddLogWindowSet lo hi) hi := by
  classical
  rw [logFinsetProb, logCount_oddLogWindowSet_inter_eq_filter_sum,
    logCount_oddLogWindowSet_eq_logFinsetMass]

theorem logCount_oddWindow_inter_ge_of_logFinsetProb_ge
    {lo hi : ℕ} {Good : Set ℕ} {p : ℝ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (hprob : p ≤ logFinsetProb (oddLogWindow lo hi) Good) :
    p * logCount (oddLogWindowSet lo hi) hi ≤
      logCount (oddLogWindowSet lo hi ∩ Good) hi := by
  have hden : 0 < logCount (oddLogWindowSet lo hi) hi := by
    rw [logCount_oddLogWindowSet_eq_logFinsetMass]
    exact hmass
  rw [logFinsetProb_oddLogWindow_eq_logCount_ratio] at hprob
  exact (le_div_iff₀ hden).mp hprob

end Tao
end Erdos1135
