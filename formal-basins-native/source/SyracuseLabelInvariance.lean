import ActualOddLabelLaw
import DefaultPassComposition
import Mathlib.Data.Nat.Lattice

open Filter
open scoped Topology

namespace CollatzCanonical.LabelLaw
open Erdos1135.Tao CollatzClockAudit

noncomputable def syracuseGlobalMinimum (q : ℕ) : ℕ :=
  sInf (Set.range (fun k : ℕ => (syracuse^[k]) q))

theorem syracuseGlobalMinimum_mem (q : ℕ) :
    ∃ k : ℕ, (syracuse^[k]) q = syracuseGlobalMinimum q := by
  change sInf (Set.range (fun k : ℕ => (syracuse^[k]) q)) ∈
    Set.range (fun k : ℕ => (syracuse^[k]) q)
  apply Nat.sInf_mem
  exact ⟨q, 0, by simp⟩

theorem syracuseGlobalMinimum_le (q k : ℕ) :
    syracuseGlobalMinimum q ≤ (syracuse^[k]) q := Nat.sInf_le ⟨k, rfl⟩

theorem syracuseGlobalMinimum_first_passage {x : ℝ} {q τ : ℕ}
    (hτ : syracuseFirstHitAtMostReal x q τ) :
    syracuseGlobalMinimum q = syracuseGlobalMinimum ((syracuse^[τ]) q) := by
  apply le_antisymm
  · obtain ⟨k, hk⟩ := syracuseGlobalMinimum_mem ((syracuse^[τ]) q)
    rw [← hk, ← Function.iterate_add_apply]
    exact syracuseGlobalMinimum_le q (k + τ)
  · obtain ⟨k, hk⟩ := syracuseGlobalMinimum_mem q
    rw [← hk]
    by_cases hkt : k < τ
    · have hu := syracuseGlobalMinimum_le ((syracuse^[τ]) q) 0
      simp only [Function.iterate_zero, id_eq] at hu
      have hreal : (syracuseGlobalMinimum ((syracuse^[τ]) q) : ℝ) <
          ((syracuse^[k]) q : ℝ) :=
        lt_of_le_of_lt ((Nat.cast_le.mpr hu).trans hτ.1) (hτ.2 k hkt)
      exact (Nat.cast_lt.mp hreal).le
    · have htk : τ ≤ k := by omega
      have he : (syracuse^[k]) q = (syracuse^[k - τ]) ((syracuse^[τ]) q) := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel htk]
      rw [he]
      exact syracuseGlobalMinimum_le _ _

theorem global_minimum_eventually_passage_invariant :
    EventuallyLabelPassageInvariant syracuseGlobalMinimum := by
  apply Filter.Eventually.of_forall
  intro x q _ τ hτ
  exact syracuseGlobalMinimum_first_passage hτ

def SyracuseTailRelated (q r : ℕ) : Prop :=
  ∃ j k : ℕ, (syracuse^[j]) q = (syracuse^[k]) r

theorem SyracuseTailRelated_equivalence : Equivalence SyracuseTailRelated := by
  constructor
  · intro q
    exact ⟨0, 0, rfl⟩
  · rintro q r ⟨j, k, hjk⟩
    exact ⟨k, j, hjk.symm⟩
  · rintro q r s ⟨i, j, hij⟩ ⟨k, l, hkl⟩
    refine ⟨k + i, j + l, ?_⟩
    calc
      (syracuse^[k + i]) q = (syracuse^[k]) ((syracuse^[i]) q) :=
        Function.iterate_add_apply _ _ _ _
      _ = (syracuse^[k]) ((syracuse^[j]) r) := by rw [hij]
      _ = (syracuse^[j]) ((syracuse^[k]) r) := by
        rw [← Function.iterate_add_apply, Nat.add_comm k j, Function.iterate_add_apply]
      _ = (syracuse^[j]) ((syracuse^[l]) s) := by rw [hkl]
      _ = (syracuse^[j + l]) s := (Function.iterate_add_apply _ _ _ _).symm

def syracuseTailSetoid : Setoid ℕ := ⟨SyracuseTailRelated, SyracuseTailRelated_equivalence⟩
abbrev SyracuseTailComponent := Quotient syracuseTailSetoid

def syracuseTailLabel (q : ℕ) : SyracuseTailComponent := Quotient.mk syracuseTailSetoid q

theorem tail_component_eventually_passage_invariant :
    EventuallyLabelPassageInvariant syracuseTailLabel := by
  apply Filter.Eventually.of_forall
  intro x q _ τ _
  unfold syracuseTailLabel
  apply Quotient.sound
  exact ⟨τ, 0, by simp⟩

noncomputable def fixedPassageLabel (M : ℕ) (hM : 1 ≤ M) (q : ℕ) : {n : ℕ // n ≤ M} :=
  syracusePassLocationAtMostOrOne M q hM

theorem fixed_passage_eventually_passage_invariant (M : ℕ) (hM : 1 ≤ M) :
    EventuallyLabelPassageInvariant (fixedPassageLabel M hM) := by
  filter_upwards [eventually_ge_atTop (M : ℝ)] with x hx
  intro q _ τ hτ
  have hx0 : 0 ≤ x := (Nat.cast_nonneg M).trans hx
  have hMx : M ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr hx
  have hx1 : 1 ≤ ⌊x⌋₊ := hM.trans hMx
  have hfirst := (syracuseFirstHitAtMostReal_iff_floor hx0).mp hτ
  have he := passAtMostOrOne_compose (q := q) hM hMx hx1
  rw [passAtMostOrOne_of_first_hit hx1 hfirst] at he
  exact he.symm

theorem actual_global_minimum_label_law :
    ∃ μ : PMF ℕ, Tendsto
      (fun t => ∑' i, |oddLabelLaw syracuseGlobalMinimum t i - (μ i).toReal|)
      atTop (𝓝 0) := actual_odd_label_PMF_law _ global_minimum_eventually_passage_invariant

theorem actual_tail_component_label_law :
    ∃ μ : PMF SyracuseTailComponent, Tendsto
      (fun t => ∑' i, |oddLabelLaw syracuseTailLabel t i - (μ i).toReal|)
      atTop (𝓝 0) := actual_odd_label_PMF_law _ tail_component_eventually_passage_invariant

theorem actual_fixed_passage_label_law (M : ℕ) (hM : 1 ≤ M) :
    ∃ μ : PMF {n : ℕ // n ≤ M}, Tendsto
      (fun t => ∑' i, |oddLabelLaw (fixedPassageLabel M hM) t i - (μ i).toReal|)
      atTop (𝓝 0) := actual_odd_label_PMF_law _ (fixed_passage_eventually_passage_invariant M hM)

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.global_minimum_eventually_passage_invariant
#print axioms CollatzCanonical.LabelLaw.tail_component_eventually_passage_invariant
#print axioms CollatzCanonical.LabelLaw.fixed_passage_eventually_passage_invariant
#print axioms CollatzCanonical.LabelLaw.actual_global_minimum_label_law
#print axioms CollatzCanonical.LabelLaw.actual_tail_component_label_law
#print axioms CollatzCanonical.LabelLaw.actual_fixed_passage_label_law
