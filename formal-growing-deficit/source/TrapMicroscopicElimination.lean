import Mathlib.Tactic

/-!
Finite deletion budgets and telescoping schedules. The sets attached to new
transitions must be disjoint subsets of the old transitions and deleted blocks.
The lemmas do not construct a subsequence or assert an arithmetic obstruction.
-/

set_option autoImplicit false
open Filter
open scoped BigOperators

namespace CollatzResearch

theorem trap_schedule_segment {A : Type*} [AddCommMonoid A]
    (x w : ℕ → A) (a t : ℕ)
    (hstep : ∀ i < t, x (a + i + 1) = x (a + i) + w (a + i)) :
    x (a + t) = x a + ∑ i ∈ Finset.range t, w (a + i) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show a + (t + 1) = a + t + 1 by omega, hstep t (by omega)]
      rw [ih (fun i hi => hstep i (by omega)), Finset.sum_range_succ]
      simp only [add_assoc]

theorem trap_deleted_horizontal_schedule (j m u : ℕ → ℕ) (a t : ℕ)
    (hstep : ∀ i < t + 1,
      j (a + i + 1) = j (a + i) + m (a + i) + u (a + i)) :
    j (a + t + 1) = j a + m a +
      ((∑ i ∈ Finset.range (t + 1), u (a + i)) +
        ∑ i ∈ Finset.range t, m (a + i + 1)) := by
  have h := trap_schedule_segment j (fun i => m i + u i) a (t + 1)
    (fun i hi => by simpa only [add_assoc] using hstep i hi)
  rw [Finset.sum_add_distrib, Finset.sum_range_succ'] at h
  simpa only [Nat.add_assoc, Nat.add_zero, add_left_comm, add_comm] using h

theorem trap_deleted_vertical_schedule (T h g : ℕ → ℤ) (a t : ℕ)
    (hstep : ∀ i < t + 1,
      T (a + i + 1) = T (a + i) + h (a + i + 1) + g (a + i)) :
    T (a + t + 1) = T a + h (a + t + 1) +
      ((∑ i ∈ Finset.range (t + 1), g (a + i)) +
        ∑ i ∈ Finset.range t, h (a + i + 1)) := by
  have hs := trap_schedule_segment T (fun i => h (i + 1) + g i) a (t + 1)
    (fun i hi => by simpa only [add_assoc] using hstep i hi)
  rw [Finset.sum_add_distrib, Finset.sum_range_succ] at hs
  simpa only [Nat.add_assoc, add_assoc, add_left_comm, add_comm] using hs

theorem trap_disjoint_subsums_le {ι κ : Type*} [DecidableEq ι]
    (s : Finset κ) (parts : κ → Finset ι) (all : Finset ι) (f : ι → ℝ)
    (hdisj : Set.PairwiseDisjoint (↑s) parts)
    (hsub : ∀ k ∈ s, parts k ⊆ all)
    (hf : ∀ i ∈ all, 0 ≤ f i) :
    ∑ k ∈ s, ∑ i ∈ parts k, f i ≤ ∑ i ∈ all, f i := by
  rw [← Finset.sum_biUnion hdisj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hi
    exact hsub k hk hik
  · intro i hi _
    exact hf i hi

theorem trap_deleted_height_bound {ι : Type*} (deleted : Finset ι)
    (h m e : ι → ℝ) (heq : ∀ i ∈ deleted, h i = 4 * m i + e i) :
    ∑ i ∈ deleted, h i ≤
      4 * ∑ i ∈ deleted, m i + ∑ i ∈ deleted, |e i| := by
  calc
    ∑ i ∈ deleted, h i ≤ ∑ i ∈ deleted, (4 * m i + |e i|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [heq i hi]
      linarith [le_abs_self (e i)]
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem trap_compressed_omission_bound {ι κ τ : Type*}
    [DecidableEq ι] [DecidableEq τ]
    (new : Finset κ) (old : Finset τ) (deleted : Finset ι)
    (steps : κ → Finset τ) (inside : κ → Finset ι)
    (u : τ → ℝ) (m : ι → ℝ)
    (hsteps : Set.PairwiseDisjoint (↑new) steps)
    (hinside : Set.PairwiseDisjoint (↑new) inside)
    (hstepSub : ∀ k ∈ new, steps k ⊆ old)
    (hinsideSub : ∀ k ∈ new, inside k ⊆ deleted)
    (hu : ∀ i ∈ old, 0 ≤ u i) (hm : ∀ i ∈ deleted, 0 ≤ m i) :
    ∑ k ∈ new, ((∑ i ∈ steps k, u i) + ∑ i ∈ inside k, m i) ≤
      (∑ i ∈ old, u i) + ∑ i ∈ deleted, m i := by
  rw [Finset.sum_add_distrib]
  exact add_le_add
    (trap_disjoint_subsums_le new steps old u hsteps hstepSub hu)
    (trap_disjoint_subsums_le new inside deleted m hinside hinsideSub hm)

theorem trap_compressed_gap_bound {ι κ τ : Type*}
    [DecidableEq ι] [DecidableEq τ]
    (new : Finset κ) (old : Finset τ) (deleted : Finset ι)
    (steps : κ → Finset τ) (inside : κ → Finset ι)
    (g : τ → ℝ) (h : ι → ℝ)
    (hsteps : Set.PairwiseDisjoint (↑new) steps)
    (hinside : Set.PairwiseDisjoint (↑new) inside)
    (hstepSub : ∀ k ∈ new, steps k ⊆ old)
    (hinsideSub : ∀ k ∈ new, inside k ⊆ deleted)
    (hh : ∀ i ∈ deleted, 0 ≤ h i) :
    ∑ k ∈ new, |(∑ i ∈ steps k, g i) + ∑ i ∈ inside k, h i| ≤
      (∑ i ∈ old, |g i|) + ∑ i ∈ deleted, h i := by
  have hlocal : ∀ k ∈ new,
      |(∑ i ∈ steps k, g i) + ∑ i ∈ inside k, h i| ≤
        (∑ i ∈ steps k, |g i|) + ∑ i ∈ inside k, h i := by
    intro k hk
    have hnonneg : 0 ≤ ∑ i ∈ inside k, h i :=
      Finset.sum_nonneg (fun i hi => hh i (hinsideSub k hk hi))
    exact (abs_add_le _ _).trans (by
      rw [abs_of_nonneg hnonneg]
      exact add_le_add (Finset.abs_sum_le_sum_abs g (steps k)) le_rfl)
  calc
    _ ≤ ∑ k ∈ new, ((∑ i ∈ steps k, |g i|) + ∑ i ∈ inside k, h i) :=
      Finset.sum_le_sum hlocal
    _ ≤ _ := trap_compressed_omission_bound new old deleted steps inside
      (fun i => |g i|) h hsteps hinside hstepSub hinsideSub
      (fun i _ => abs_nonneg (g i)) hh

theorem trap_microscopic_deletion_error_budget {ι κ τ : Type*}
    [DecidableEq ι] [DecidableEq τ]
    (blocks kept : Finset ι) (new : Finset κ) (old : Finset τ)
    (steps : κ → Finset τ) (inside : κ → Finset ι)
    (h m e : ι → ℝ) (u g : τ → ℝ)
    (hkept : kept ⊆ blocks)
    (hsteps : Set.PairwiseDisjoint (↑new) steps)
    (hinside : Set.PairwiseDisjoint (↑new) inside)
    (hstepSub : ∀ k ∈ new, steps k ⊆ old)
    (hinsideSub : ∀ k ∈ new, inside k ⊆ blocks \ kept)
    (hu : ∀ i ∈ old, 0 ≤ u i)
    (hm : ∀ i ∈ blocks \ kept, 0 ≤ m i)
    (hh : ∀ i ∈ blocks \ kept, 0 ≤ h i)
    (heq : ∀ i ∈ blocks \ kept, h i = 4 * m i + e i) :
    (∑ i ∈ kept, |e i|) +
      (∑ k ∈ new, ((∑ i ∈ steps k, u i) + ∑ i ∈ inside k, m i)) +
      (∑ k ∈ new, |(∑ i ∈ steps k, g i) + ∑ i ∈ inside k, h i|) ≤
        (∑ i ∈ blocks, |e i|) + (∑ i ∈ old, u i) +
          (∑ i ∈ old, |g i|) + 5 * ∑ i ∈ blocks \ kept, m i := by
  have hu' := trap_compressed_omission_bound new old (blocks \ kept) steps inside
    u m hsteps hinside hstepSub hinsideSub hu hm
  have hg' := trap_compressed_gap_bound new old (blocks \ kept) steps inside
    g h hsteps hinside hstepSub hinsideSub hh
  have hh' := trap_deleted_height_bound (blocks \ kept) h m e heq
  have he' := Finset.sum_sdiff hkept (f := fun i => |e i|)
  linarith

theorem trap_microscopic_deletion_span_budget {ι τ : Type*}
    [DecidableEq ι] [DecidableEq τ]
    (deleted tailBlocks : Finset ι) (old tailSteps : Finset τ)
    (h m e : ι → ℝ) (g : τ → ℝ)
    (hb : tailBlocks ⊆ deleted) (hs : tailSteps ⊆ old)
    (hh : ∀ i ∈ deleted, 0 ≤ h i)
    (heq : ∀ i ∈ deleted, h i = 4 * m i + e i) :
    |(∑ i ∈ tailBlocks, h i) + ∑ i ∈ tailSteps, g i| ≤
      4 * (∑ i ∈ deleted, m i) + (∑ i ∈ deleted, |e i|) +
        ∑ i ∈ old, |g i| := by
  have hnonneg : 0 ≤ ∑ i ∈ tailBlocks, h i :=
    Finset.sum_nonneg (fun i hi => hh i (hb hi))
  have hhsub : ∑ i ∈ tailBlocks, h i ≤ ∑ i ∈ deleted, h i :=
    Finset.sum_le_sum_of_subset_of_nonneg hb (fun i hi _ => hh i hi)
  have hgsub : ∑ i ∈ tailSteps, |g i| ≤ ∑ i ∈ old, |g i| :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => abs_nonneg (g i))
  calc
    _ ≤ |∑ i ∈ tailBlocks, h i| + |∑ i ∈ tailSteps, g i| := abs_add_le _ _
    _ ≤ (∑ i ∈ deleted, h i) + ∑ i ∈ old, |g i| := by
      rw [abs_of_nonneg hnonneg]
      exact add_le_add hhsub ((Finset.abs_sum_le_sum_abs g tailSteps).trans hgsub)
    _ ≤ _ := add_le_add (trap_deleted_height_bound deleted h m e heq) le_rfl

theorem eventually_trap_deletion_sublinear (E M Eret N : ℕ → ℝ)
    (hE : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, E n ≤ gamma * N n)
    (hM : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, M n ≤ gamma * N n)
    (hbound : ∀ᶠ n in atTop, Eret n ≤ E n + 5 * M n) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, Eret n ≤ gamma * N n := by
  intro gamma hgamma
  filter_upwards [hbound, hE (gamma / 2) (by positivity),
    hM (gamma / 10) (by positivity)] with n hb he hm
  linarith

end CollatzResearch

#print axioms CollatzResearch.trap_deleted_horizontal_schedule
#print axioms CollatzResearch.trap_deleted_vertical_schedule
#print axioms CollatzResearch.trap_microscopic_deletion_error_budget
#print axioms CollatzResearch.trap_microscopic_deletion_span_budget
#print axioms CollatzResearch.eventually_trap_deletion_sublinear
