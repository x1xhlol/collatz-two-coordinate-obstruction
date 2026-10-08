/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Terras.Density.NaturalDensity
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Logarithmic Density For The Tao Lane

This module starts the logarithmic-density API needed for the Tao almost-bounded-orbits
formalization.  We use harmonic weights over the positive integers: the `N`th prefix sums over
`1, ..., N`, represented as `i + 1` for `i < N`.
-/

namespace Erdos1135SecondScale
namespace Tao

open Filter
open scoped BigOperators Topology

/-- Harmonic weight of the positive integer indexed by `i + 1`. -/
noncomputable def logWeight (i : ℕ) : ℝ :=
  (1 : ℝ) / ((i + 1 : ℕ) : ℝ)

/-- Harmonic mass of the first `N` positive integers. -/
noncomputable def logMass (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, logWeight i

/-- Harmonic mass of a set inside the first `N` positive integers. -/
noncomputable def logCount (s : Set ℕ) (N : ℕ) : ℝ := by
  classical
  exact ∑ i ∈ Finset.range N, if i + 1 ∈ s then logWeight i else 0

/-- Logarithmic counting ratio, normalized by the harmonic mass of the prefix. -/
noncomputable def logCountingRatio (s : Set ℕ) (N : ℕ) : ℝ :=
  logCount s N / logMass N

/-- Project-local logarithmic density predicate for sets of natural numbers. -/
def HasLogDensity (s : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => logCountingRatio s N) atTop (nhds d)

theorem logWeight_pos (i : ℕ) : 0 < logWeight i := by
  unfold logWeight
  positivity

theorem logWeight_nonneg (i : ℕ) : 0 ≤ logWeight i :=
  (logWeight_pos i).le

theorem logMass_pos {N : ℕ} (hN : 0 < N) : 0 < logMass N := by
  unfold logMass
  exact Finset.sum_pos (fun i _hi => logWeight_pos i) ⟨0, Finset.mem_range.mpr hN⟩

theorem logMass_eq_harmonic (N : ℕ) :
    logMass N = (harmonic N : ℝ) := by
  simp [logMass, logWeight, harmonic]

theorem logMass_succ (N : ℕ) :
    logMass (N + 1) = logMass N + logWeight N := by
  simp [logMass, Finset.sum_range_succ]

theorem logCount_succ (s : Set ℕ) (N : ℕ) [Decidable (N + 1 ∈ s)] :
    logCount s (N + 1) =
      logCount s N + if N + 1 ∈ s then logWeight N else 0 := by
  classical
  simp [logCount, Finset.sum_range_succ]

theorem logCount_succ_of_mem {s : Set ℕ} {N : ℕ} (hmem : N + 1 ∈ s) :
    logCount s (N + 1) = logCount s N + logWeight N := by
  classical
  simpa [hmem] using logCount_succ s N

theorem logCount_succ_of_not_mem {s : Set ℕ} {N : ℕ} (hmem : N + 1 ∉ s) :
    logCount s (N + 1) = logCount s N := by
  classical
  simpa [hmem] using logCount_succ s N

theorem logMass_tendsto_atTop :
    Tendsto logMass atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N + 1 : ℕ) : ℝ)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  refine Filter.tendsto_atTop_mono ?_ hlog
  intro N
  rw [logMass_eq_harmonic]
  exact log_add_one_le_harmonic N

@[simp]
theorem logCount_empty (N : ℕ) : logCount (∅ : Set ℕ) N = 0 := by
  simp [logCount]

@[simp]
theorem logCount_univ (N : ℕ) : logCount Set.univ N = logMass N := by
  simp [logCount, logMass]

theorem hasLogDensity_empty : HasLogDensity (∅ : Set ℕ) 0 := by
  simp [HasLogDensity, logCountingRatio]

theorem hasLogDensity_univ : HasLogDensity (Set.univ : Set ℕ) 1 := by
  unfold HasLogDensity
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine eventually_atTop.mpr ⟨1, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hmass : logMass N ≠ 0 := (logMass_pos hNpos).ne'
  simp [logCountingRatio, hmass]

theorem logCount_mono {s t : Set ℕ} (hsub : s ⊆ t) (N : ℕ) :
    logCount s N ≤ logCount t N := by
  classical
  unfold logCount
  refine Finset.sum_le_sum ?_
  intro i _hi
  by_cases hs : i + 1 ∈ s
  · have ht : i + 1 ∈ t := hsub hs
    simp [hs, ht]
  · by_cases ht : i + 1 ∈ t
    · simp [hs, ht, logWeight_nonneg i]
    · simp [hs, ht]

theorem logCount_le_logMass (s : Set ℕ) (N : ℕ) :
    logCount s N ≤ logMass N := by
  simpa using logCount_mono (Set.subset_univ s) N

theorem logCount_nonneg (s : Set ℕ) (N : ℕ) :
    0 ≤ logCount s N := by
  classical
  unfold logCount
  refine Finset.sum_nonneg ?_
  intro i _hi
  by_cases hs : i + 1 ∈ s
  · simp [hs, logWeight_nonneg i]
  · simp [hs]

theorem logCountingRatio_nonneg_eventually (s : Set ℕ) :
    ∀ᶠ N in atTop, 0 ≤ logCountingRatio s N := by
  refine eventually_atTop.mpr ⟨1, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  exact div_nonneg (logCount_nonneg s N) (logMass_pos hNpos).le

theorem logCountingRatio_mono_eventually {s t : Set ℕ} (hsub : s ⊆ t) :
    ∀ᶠ N in atTop, logCountingRatio s N ≤ logCountingRatio t N := by
  refine eventually_atTop.mpr ⟨1, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  exact div_le_div_of_nonneg_right (logCount_mono hsub N) (logMass_pos hNpos).le

theorem logCountingRatio_le_one_eventually (s : Set ℕ) :
    ∀ᶠ N in atTop, logCountingRatio s N ≤ 1 := by
  refine eventually_atTop.mpr ⟨1, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hmass_pos := logMass_pos hNpos
  have hle :=
    div_le_div_of_nonneg_right (logCount_le_logMass s N) hmass_pos.le
  simpa [logCountingRatio, hmass_pos.ne'] using hle

theorem logCount_le_logMass_of_subset_Iio {s : Set ℕ} {B : ℕ}
    (hsub : s ⊆ {n : ℕ | n < B}) (N : ℕ) :
    logCount s N ≤ logMass B := by
  classical
  unfold logCount logMass
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro i hi
    have hi_mem : i + 1 ∈ s := (Finset.mem_filter.mp hi).2
    have hi_lt : i + 1 < B := hsub hi_mem
    exact Finset.mem_range.mpr (Nat.lt_of_succ_lt hi_lt)
  · intro i _hi _hnot
    exact logWeight_nonneg i

theorem hasLogDensity_zero_of_subset_Iio {s : Set ℕ} {B : ℕ}
    (hsub : s ⊆ {n : ℕ | n < B}) :
    HasLogDensity s 0 := by
  unfold HasLogDensity logCountingRatio
  refine @squeeze_zero' ℕ
    (fun N : ℕ => logCount s N / logMass N)
    (fun N : ℕ => logMass B / logMass N)
    atTop (logCountingRatio_nonneg_eventually s) ?_ ?_
  · refine eventually_atTop.mpr ⟨1, ?_⟩
    intro N hN
    have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
    exact div_le_div_of_nonneg_right
      (logCount_le_logMass_of_subset_Iio hsub N) (logMass_pos hNpos).le
  · exact logMass_tendsto_atTop.const_div_atTop (logMass B)

theorem logCount_union_of_disjoint {s t : Set ℕ} (hdisj : Disjoint s t) (N : ℕ) :
    logCount (s ∪ t) N = logCount s N + logCount t N := by
  classical
  unfold logCount
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hnot : ¬(i + 1 ∈ s ∧ i + 1 ∈ t) := by
    intro h
    exact (Set.disjoint_left.mp hdisj h.1) h.2
  by_cases hs : i + 1 ∈ s <;> by_cases ht : i + 1 ∈ t
  · exact (hnot ⟨hs, ht⟩).elim
  · simp [Set.mem_union, hs, ht]
  · simp [Set.mem_union, hs, ht]
  · simp [Set.mem_union, hs, ht]

theorem logCountingRatio_le_add_error_of_eventually_subset {A S : Set ℕ}
    (hsub : ∀ᶠ n in atTop, n ∈ A → n ∈ S) :
    ∃ C : ℕ, ∀ᶠ N in atTop,
      logCountingRatio A N ≤ logCountingRatio S N + logMass C / logMass N := by
  rcases Filter.eventually_atTop.mp hsub with ⟨C, hC⟩
  let bad : Set ℕ := {n | n ∈ A ∧ n ∉ S}
  have hbad_subset : bad ⊆ {n : ℕ | n < C} := by
    intro n hn
    by_contra hnot
    exact hn.2 (hC n (le_of_not_gt hnot) hn.1)
  have hA_subset : A ⊆ S ∪ bad := by
    intro n hn
    by_cases hs : n ∈ S
    · exact Or.inl hs
    · exact Or.inr ⟨hn, hs⟩
  have hdisj : Disjoint S bad := by
    rw [Set.disjoint_left]
    intro n hs hbad
    exact hbad.2 hs
  refine ⟨C, eventually_atTop.mpr ⟨1, ?_⟩⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hmass_nonneg : 0 ≤ logMass N := (logMass_pos hNpos).le
  have hbad_le : logCount bad N ≤ logMass C :=
    logCount_le_logMass_of_subset_Iio hbad_subset N
  have hcount_le : logCount A N ≤ logCount S N + logMass C := by
    calc
      logCount A N ≤ logCount (S ∪ bad) N := logCount_mono hA_subset N
      _ = logCount S N + logCount bad N := logCount_union_of_disjoint hdisj N
      _ ≤ logCount S N + logMass C :=
        add_le_add (le_refl (logCount S N)) hbad_le
  have hdiv :=
    div_le_div_of_nonneg_right hcount_le hmass_nonneg
  simpa [logCountingRatio, add_div] using hdiv

theorem logCount_congr_on_pos {s t : Set ℕ}
    (h : ∀ n : ℕ, 0 < n → (n ∈ s ↔ n ∈ t)) (N : ℕ) :
    logCount s N = logCount t N := by
  classical
  unfold logCount
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hiff := h (i + 1) (Nat.succ_pos i)
  by_cases hs : i + 1 ∈ s
  · have ht : i + 1 ∈ t := hiff.mp hs
    simp [hs, ht]
  · have ht : i + 1 ∉ t := fun ht => hs (hiff.mpr ht)
    simp [hs, ht]

theorem HasLogDensity.congr_on_pos {s t : Set ℕ} {d : ℝ}
    (h : ∀ n : ℕ, 0 < n → (n ∈ s ↔ n ∈ t)) (hs : HasLogDensity s d) :
    HasLogDensity t d := by
  unfold HasLogDensity logCountingRatio at hs ⊢
  refine hs.congr' ?_
  filter_upwards with N
  rw [logCount_congr_on_pos h N]

theorem HasLogDensity.union_of_disjoint {s t : Set ℕ} {a b : ℝ}
    (hs : HasLogDensity s a) (ht : HasLogDensity t b) (hdisj : Disjoint s t) :
    HasLogDensity (s ∪ t) (a + b) := by
  unfold HasLogDensity logCountingRatio at hs ht ⊢
  have hsum := hs.add ht
  refine hsum.congr' ?_
  filter_upwards with N
  rw [logCount_union_of_disjoint hdisj N]
  ring

theorem logCount_diff_of_subset {s t : Set ℕ} (hsub : t ⊆ s) (N : ℕ) :
    logCount (s \ t) N = logCount s N - logCount t N := by
  have hcover : s = (s \ t) ∪ t := by
    ext n
    constructor
    · intro hs
      by_cases ht : n ∈ t
      · exact Or.inr ht
      · exact Or.inl ⟨hs, ht⟩
    · intro h
      rcases h with hdiff | ht
      · exact hdiff.1
      · exact hsub ht
  have hdisj : Disjoint (s \ t) t := by
    rw [Set.disjoint_left]
    intro _n hdiff ht
    exact hdiff.2 ht
  have hcount := logCount_union_of_disjoint hdisj N
  rw [← hcover] at hcount
  rw [hcount]
  ring

theorem HasLogDensity.diff_of_subset {s t : Set ℕ} {a b : ℝ}
    (hs : HasLogDensity s a) (ht : HasLogDensity t b) (hsub : t ⊆ s) :
    HasLogDensity (s \ t) (a - b) := by
  unfold HasLogDensity logCountingRatio at hs ht ⊢
  have hdiff := hs.sub ht
  refine hdiff.congr' ?_
  filter_upwards with N
  rw [logCount_diff_of_subset hsub N]
  ring

theorem HasLogDensity.inter_Ici {s : Set ℕ} {d : ℝ} (hs : HasLogDensity s d) (B : ℕ) :
    HasLogDensity {n : ℕ | n ∈ s ∧ B ≤ n} d := by
  let low : Set ℕ := {n | n ∈ s ∧ n < B}
  let high : Set ℕ := {n | n ∈ s ∧ B ≤ n}
  have hlow_density : HasLogDensity low 0 := by
    apply hasLogDensity_zero_of_subset_Iio (B := B)
    intro _n hn
    exact hn.2
  have hcount : ∀ N, logCount s N = logCount low N + logCount high N := by
    intro N
    have hcover : s = low ∪ high := by
      ext n
      constructor
      · intro hs_mem
        by_cases hn : n < B
        · exact Or.inl ⟨hs_mem, hn⟩
        · exact Or.inr ⟨hs_mem, le_of_not_gt hn⟩
      · intro h
        rcases h with hlow | hhigh
        · exact hlow.1
        · exact hhigh.1
    have hdisj : Disjoint low high := by
      rw [Set.disjoint_left]
      intro _n hlow hhigh
      exact (not_lt_of_ge hhigh.2) hlow.2
    rw [hcover]
    exact logCount_union_of_disjoint hdisj N
  unfold HasLogDensity logCountingRatio at hs hlow_density ⊢
  have hdiff := hs.sub hlow_density
  have hdiff' :
      Tendsto
        (fun N : ℕ => logCount s N / logMass N - logCount low N / logMass N)
        atTop (nhds d) := by
    simpa using hdiff
  refine hdiff'.congr' ?_
  filter_upwards with N
  have hc : logCount s N = logCount low N + logCount high N := hcount N
  change logCount s N / logMass N - logCount low N / logMass N =
    logCount high N / logMass N
  rw [hc]
  ring

theorem HasLogDensity.of_superset_of_tendsto_one {A : ℕ → Set ℕ} {S : Set ℕ} {d : ℕ → ℝ}
    (hsub : ∀ k, A k ⊆ S)
    (hA : ∀ k, HasLogDensity (A k) (d k))
    (hd : Tendsto d atTop (nhds 1)) :
    HasLogDensity S 1 := by
  unfold HasLogDensity
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    rcases ((tendsto_order.1 hd).1 b hb).exists with ⟨k, hk⟩
    have hlower : ∀ᶠ N in atTop, b < logCountingRatio (A k) N :=
      (tendsto_order.1 (hA k)).1 b hk
    have hmono : ∀ᶠ N in atTop, logCountingRatio (A k) N ≤ logCountingRatio S N :=
      logCountingRatio_mono_eventually (hsub k)
    filter_upwards [hlower, hmono] with N hlow hle
    exact lt_of_lt_of_le hlow hle
  · intro b hb
    filter_upwards [logCountingRatio_le_one_eventually S] with N hle
    exact lt_of_le_of_lt hle hb

theorem HasLogDensity.of_eventually_superset_of_lower_tendsto_one
    {A : ℕ → Set ℕ} {S : Set ℕ} {d : ℕ → ℝ}
    (hsub : ∀ k, ∀ᶠ n in atTop, n ∈ A k → n ∈ S)
    (hlower : ∀ k, ∀ᶠ N in atTop, d k ≤ logCountingRatio (A k) N)
    (hd : Tendsto d atTop (nhds 1)) :
    HasLogDensity S 1 := by
  unfold HasLogDensity
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    rcases ((tendsto_order.1 hd).1 b hb).exists with ⟨k, hk⟩
    rcases logCountingRatio_le_add_error_of_eventually_subset (hsub k) with
      ⟨C, herr⟩
    have hdelta : 0 < d k - b := sub_pos.mpr hk
    have hsmall : ∀ᶠ N in atTop, logMass C / logMass N < d k - b :=
      (tendsto_order.1
        (logMass_tendsto_atTop.const_div_atTop (logMass C))).2
        (d k - b) hdelta
    filter_upwards [hlower k, herr, hsmall] with N hlow herrN hsmallN
    have hsum : d k ≤
        logMass C / logMass N + logCountingRatio S N := by
      rw [add_comm]
      exact le_trans hlow herrN
    have hdiff_le :
        d k - logCountingRatio S N ≤ logMass C / logMass N :=
      sub_le_iff_le_add.mpr hsum
    have hdiff_lt : d k - logCountingRatio S N < d k - b :=
      lt_of_le_of_lt hdiff_le hsmallN
    exact (sub_lt_sub_iff_left (d k)).mp hdiff_lt
  · intro b hb
    filter_upwards [logCountingRatio_le_one_eventually S] with N hle
    exact lt_of_le_of_lt hle hb

end Tao
end Erdos1135SecondScale
