import PreBarrierWeightedOccupation
import ShortcutTailComponents

set_option autoImplicit false
open scoped BigOperators

namespace CollatzCanonical.RawOccupation
open Erdos1135 CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao CollatzCanonical.ForwardComponent

theorem firstHitWeight_factor_through_divergent_root
    {q u N A j : ℕ} (hu : Function.Injective (fun i => iterate i u))
    (hroot : FirstHit q u A) (hfuture : iterate j u = N) :
    firstHitWeight N q = firstHitWeight u q * firstHitWeight N u := by
  have hq : Function.Injective (fun i => iterate i q) :=
    shortcut_component_injective ⟨A, 0, by simpa using hroot.1⟩ hu
  have havoid : ∀ i < A, iterate i q ≠ N := by
    intro i hi he
    have hfuture' : iterate (A + j) q = N := by rw [iterate_add, hroot.1, hfuture]
    have := hq (he.trans hfuture'.symm)
    omega
  rw [firstHitWeight_prefix_factorization havoid, hroot.1,
    firstHitWeight_eq_pathWeight hroot]

theorem preBarrier_target_ne_divergent_future
    {M : ℝ} {q u T A i j : ℕ} (hq : Odd q) (hM : 0 ≤ M)
    (hu : Odd u) (hsmall : (u : ℝ) ≤ M)
    (hinj : Function.Injective (fun k => iterate k u))
    (hroot : iterate A q = u)
    (hT : Tao.syracuseFirstHitAtMostReal M q T) (hi : i < T) :
    (Tao.syracuse^[i]) q ≠ iterate j u := by
  let B := Tao.taoTupleWeight (Tao.syracuseValuationPNatList T q hq)
  let C := Tao.taoTupleWeight (Tao.syracuseValuationPNatList i q hq)
  have hCB : C < B := syracuse_clock_strictMono q hq hi
  have hpass := native_real_first_passage_is_oddBarrier hM hq hT
  change OddBarrierPassage q B M at hpass
  have hBA : B ≤ A := by
    by_contra h
    have hhigh := hpass.prefix_high A (by omega) (by simpa only [hroot] using Nat.odd_iff.mp hu)
    rw [hroot] at hhigh
    exact not_lt_of_ge hsmall hhigh
  have hqinj : Function.Injective (fun k => iterate k q) :=
    shortcut_component_injective ⟨A, 0, by simpa using hroot⟩ hinj
  intro he
  have hleft : iterate C q = (Tao.syracuse^[i]) q := syracuse_shortcut_landing i q hq
  have hright : iterate (A + j) q = iterate j u := by rw [iterate_add, hroot]
  have := hqinj (hleft.trans (he.trans hright.symm))
  omega

theorem divergent_future_occupation_lower {R q u : ℕ} (F : Finset ℕ)
    (hinj : Function.Injective (fun i => iterate i u))
    (hF : ∀ N ∈ F, Odd N ∧ N ≤ R ∧ ∃ j, iterate j u = N) :
    firstHitWeight u q * (∑ N ∈ F, firstHitWeight N u) ≤ oddTargetOccupation R q := by
  classical
  by_cases hh : ∃ A, iterate A q = u
  · have hroot := firstHit_find hh
    have heq : firstHitWeight u q * (∑ N ∈ F, firstHitWeight N u) =
        ∑ N ∈ F, firstHitWeight N q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      obtain ⟨j, hj⟩ := (hF N hN).2.2
      exact (firstHitWeight_factor_through_divergent_root hinj hroot hj).symm
    rw [heq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro N hN
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (hF N hN).2.1; omega),
        (hF N hN).1⟩
    · exact fun N _ _ => (firstHitWeight_bounds N q).1
  · have hz : firstHitWeight u q = 0 := by simp only [firstHitWeight, dif_neg hh]
    simpa only [hz, zero_mul] using oddTargetOccupation_nonneg R q

/-- The pre-barrier segment and a divergent root's finite forward target set
contribute disjoint first-hit weights, including sources outside its basin. -/
theorem preBarrier_occupation_add_divergent_future
    {M B : ℝ} {R q u a T : ℕ} (F : Finset ℕ)
    (hq : Odd q) (hM : 0 ≤ M) (hu : Odd u) (hsmall : (u : ℝ) ≤ M)
    (hinj : Function.Injective (fun i => iterate i u))
    (hF : ∀ N ∈ F, Odd N ∧ N ≤ R ∧ ∃ j, iterate j u = N)
    (hT : Tao.syracuseFirstHitAtMostReal M q T)
    (hweight : ∀ i < T, B ≤ firstHitWeight ((Tao.syracuse^[i]) q) q)
    (hheight : ∀ i, a ≤ i → i < T → (Tao.syracuse^[i]) q ≤ R) :
    ((T - a : ℕ) : ℝ) * B + firstHitWeight u q * (∑ N ∈ F, firstHitWeight N u) ≤
      oddTargetOccupation R q := by
  classical
  by_cases hh : ∃ A, iterate A q = u
  · let A := Nat.find hh
    have hroot : FirstHit q u A := firstHit_find hh
    let I := Finset.Ico a T
    let Q := I.image (fun i => (Tao.syracuse^[i]) q)
    have hQsub : Q ⊆ (Finset.range (R + 1)).filter Odd := by
      intro N hN
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hN
      have hi' := Finset.mem_Ico.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        have := hheight i hi'.1 hi'.2
        omega), Tao.syracuse_iterate_odd i q hq⟩
    have hFsub : F ⊆ (Finset.range (R + 1)).filter Odd := by
      intro N hN
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (hF N hN).2.1; omega),
        (hF N hN).1⟩
    have hdis : Disjoint Q F := by
      apply Finset.disjoint_left.mpr
      intro N hN hNF
      obtain ⟨i, hi, hiN⟩ := Finset.mem_image.mp hN
      obtain ⟨j, hj⟩ := (hF N hNF).2.2
      exact preBarrier_target_ne_divergent_future hq hM hu hsmall hinj hroot.1 hT
        (Finset.mem_Ico.mp hi).2 (hiN.trans hj.symm)
    have hQinj : Set.InjOn (fun i => (Tao.syracuse^[i]) q) I := by
      apply (syracuse_first_passage_prefix_injective hT).mono
      intro i hi
      exact Finset.mem_range.mpr (by have := (Finset.mem_Ico.mp hi).2; omega)
    have hpre : ((T - a : ℕ) : ℝ) * B ≤ ∑ N ∈ Q, firstHitWeight N q := by
      calc
        ((T - a : ℕ) : ℝ) * B = ∑ i ∈ I, B := by simp [I]
        _ ≤ ∑ i ∈ I, firstHitWeight ((Tao.syracuse^[i]) q) q :=
          Finset.sum_le_sum (fun i hi => hweight i (Finset.mem_Ico.mp hi).2)
        _ = ∑ N ∈ Q, firstHitWeight N q := by
          symm
          exact Finset.sum_image hQinj
    have hpost : firstHitWeight u q * (∑ N ∈ F, firstHitWeight N u) =
        ∑ N ∈ F, firstHitWeight N q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      obtain ⟨j, hj⟩ := (hF N hN).2.2
      exact (firstHitWeight_factor_through_divergent_root hinj hroot hj).symm
    rw [hpost]
    calc
      ((T - a : ℕ) : ℝ) * B + (∑ N ∈ F, firstHitWeight N q) ≤
          (∑ N ∈ Q, firstHitWeight N q) + ∑ N ∈ F, firstHitWeight N q := by linarith
      _ = ∑ N ∈ Q ∪ F, firstHitWeight N q := (Finset.sum_union hdis).symm
      _ ≤ oddTargetOccupation R q := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.union_subset hQsub hFsub) (fun N _ _ => (firstHitWeight_bounds N q).1)
  · have hz : firstHitWeight u q = 0 := by simp only [firstHitWeight, dif_neg hh]
    simpa only [hz, zero_mul, add_zero] using preBarrier_occupation_lower hq hT hweight hheight

#print axioms firstHitWeight_factor_through_divergent_root
#print axioms preBarrier_target_ne_divergent_future
#print axioms divergent_future_occupation_lower
#print axioms preBarrier_occupation_add_divergent_future

end CollatzCanonical.RawOccupation
