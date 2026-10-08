import NativeTaoArithmeticBridge

set_option autoImplicit false

namespace CollatzCanonical.NativeTao

open Erdos1135 CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

theorem oddCount_eq_native_parity_count (A q : ℕ) :
    oddCount A q = (Terras.parityPrefixList A q).count true := by
  induction A generalizing q with
  | zero => rfl
  | succ A ih =>
    rw [show A + 1 = 1 + A by omega, oddCount_add]
    rw [ih]
    have hs : iterate 1 q = Terras.accelerated q := step_eq_native q
    rw [hs]
    rw [Nat.add_comm 1 A]
    simp only [oddCount, iterate, Nat.zero_add]
    change q % 2 + (Terras.parityPrefixList A (Terras.accelerated q)).count true =
      (Terras.parityBit q :: Terras.parityPrefixList A (Terras.accelerated q)).count true
    rcases Nat.mod_two_eq_zero_or_one q with he | ho
    · simp [Terras.parityBit, Nat.even_iff, he]
    · simp [Terras.parityBit, Nat.even_iff, ho, Nat.add_comm]

theorem syracuse_shortcut_oddCount (n q : ℕ) (hq : Odd q) :
    oddCount (Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq)) q = n := by
  rw [oddCount_eq_native_parity_count, Tao.parityPrefixList_syracuseValuationPNatList,
    Tao.syracuseParityList_count_true]
  exact Tao.syracuseValuationPNatList_length n q hq

theorem firstHit_suffix_of_prefix_avoids {A K q N : ℕ}
    (havoid : ∀ i < A, iterate i q ≠ N) (hfirst : FirstHit q N K) :
    A ≤ K ∧ FirstHit (iterate A q) N (K - A) := by
  have hAK : A ≤ K := by
    by_contra h
    exact havoid K (Nat.lt_of_not_ge h) hfirst.1
  refine ⟨hAK, ?_, ?_⟩
  · rw [← iterate_add, Nat.add_sub_of_le hAK]
    exact hfirst.1
  · intro i hi he
    apply hfirst.2 (A + i) (by omega)
    simpa only [iterate_add] using he

/-- First passage to a barrier above an arbitrary shortcut target splits
both its exact first-hit time and its odd-source count. -/
theorem native_first_passage_target_split {M : ℝ} {q n N K : ℕ} (hM : 0 ≤ M)
    (hq : Odd q) (hfirst : Tao.syracuseFirstHitAtMostReal M q n)
    (hN : (N : ℝ) ≤ M) (hland : N < (Tao.syracuse^[n]) q)
    (htarget : FirstHit q N K) :
    let A := Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq)
    A ≤ K ∧ FirstHit ((Tao.syracuse^[n]) q) N (K - A) ∧
      oddCount K q = n + oddCount (K - A) ((Tao.syracuse^[n]) q) := by
  dsimp only
  let A := Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq)
  have hpass := native_real_first_passage_is_oddBarrier hM hq hfirst
  have hu : iterate A q = (Tao.syracuse^[n]) q := syracuse_shortcut_landing n q hq
  have havoid := hpass.prefix_avoids_of_landing_gt hN
    (by simpa only [syracuse_shortcut_landing] using hland)
  obtain ⟨hAK, hsuffix⟩ := firstHit_suffix_of_prefix_avoids havoid htarget
  refine ⟨hAK, by simpa only [syracuse_shortcut_landing] using hsuffix, ?_⟩
  have he := oddCount_add A (K - A) q
  rw [Nat.add_sub_of_le hAK, hu, syracuse_shortcut_oddCount n q hq] at he
  exact he

#print axioms syracuse_shortcut_oddCount
#print axioms native_first_passage_target_split

end CollatzCanonical.NativeTao
