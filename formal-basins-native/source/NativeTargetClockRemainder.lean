import ActualClockAdapter
import NativeSyracuseClockBridge

set_option autoImplicit false

namespace CollatzCanonical.NativeTao

open Erdos1135 CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

theorem native_first_passage_oddDepth_split {M : ℝ} {q n N K : ℕ} (hM : 0 ≤ M)
    (hq : Odd q) (hfirst : Tao.syracuseFirstHitAtMostReal M q n)
    (hN : (N : ℝ) ≤ M) (hland : N < (Tao.syracuse^[n]) q)
    (htarget : FirstHit q N K) :
    firstHitOddDepth N q = n + firstHitOddDepth N ((Tao.syracuse^[n]) q) := by
  obtain ⟨_, hsuffix, hcount⟩ :=
    native_first_passage_target_split hM hq hfirst hN hland htarget
  rw [firstHitOddDepth_of_first_hit htarget, firstHitOddDepth_of_first_hit hsuffix]
  exact hcount

/-- A finite remainder bound over odd landings at most B that lie in the
actual shortcut basin of N. Its definition assumes no global termination. -/
noncomputable def boundedTargetOddRemainder (N B : ℕ) : ℕ := by
  classical
  exact ((Finset.range (B + 1)).filter fun u =>
    Odd u ∧ ∃ K, iterate K u = N).sup (firstHitOddDepth N)

theorem firstHitOddDepth_le_boundedTargetOddRemainder {N B u : ℕ}
    (hu : u ≤ B) (ho : Odd u) (hbasin : ∃ K, iterate K u = N) :
    firstHitOddDepth N u ≤ boundedTargetOddRemainder N B := by
  classical
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ho, hbasin⟩

/-- Every successful real-threshold passage with landing above the target
leaves a uniformly bounded amount of the actual target odd clock. -/
theorem native_first_passage_bounded_target_remainder {M : ℝ} {q n N : ℕ}
    (hM : 0 ≤ M) (hq : Odd q) (hfirst : Tao.syracuseFirstHitAtMostReal M q n)
    (hN : (N : ℝ) ≤ M) (hland : N < (Tao.syracuse^[n]) q)
    (hbasin : ∃ K, iterate K q = N) :
    n ≤ firstHitOddDepth N q ∧
      firstHitOddDepth N q - n ≤ boundedTargetOddRemainder N ⌊M⌋₊ := by
  have htarget := firstHit_find hbasin
  obtain ⟨_, hsuffix, _⟩ :=
    native_first_passage_target_split hM hq hfirst hN hland htarget
  have hsplit := native_first_passage_oddDepth_split hM hq hfirst hN hland htarget
  have hu : (Tao.syracuse^[n]) q ≤ ⌊M⌋₊ := (Nat.le_floor_iff hM).mpr hfirst.1
  have hb := firstHitOddDepth_le_boundedTargetOddRemainder hu
    (Tao.syracuse_iterate_odd n q hq) ⟨_, hsuffix.1⟩
  omega

theorem native_first_passage_real_target_remainder {M : ℝ} {q n N : ℕ}
    (hM : 0 ≤ M) (hq : Odd q) (hfirst : Tao.syracuseFirstHitAtMostReal M q n)
    (hN : (N : ℝ) ≤ M) (hland : N < (Tao.syracuse^[n]) q)
    (hbasin : ∃ K, iterate K q = N) :
    |(firstHitOddDepth N q : ℝ) - n| ≤ boundedTargetOddRemainder N ⌊M⌋₊ := by
  obtain ⟨hlo, hhi⟩ := native_first_passage_bounded_target_remainder
    hM hq hfirst hN hland hbasin
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlo))]
  exact_mod_cast hhi

#print axioms native_first_passage_oddDepth_split
#print axioms native_first_passage_bounded_target_remainder
#print axioms native_first_passage_real_target_remainder

end CollatzCanonical.NativeTao
