import Erdos1135.Tao.Syracuse.ParityBridge
import Erdos1135.Tao.Syracuse.FirstPassage

set_option autoImplicit false

namespace CollatzCanonical.NativeTao

open Erdos1135

theorem follows_false_prefix_even {k M : ℕ}
    (h : Terras.FollowsParityList (List.replicate k false) M) :
    ∀ i < k, Even ((Terras.accelerated^[i]) M) := by
  induction k generalizing M with
  | zero => intro i hi; omega
  | succ k ih =>
    have hp : Even M ∧ Terras.FollowsParityList (List.replicate k false) (Terras.accelerated M) := by
      simpa only [List.replicate_succ, Terras.FollowsParityList, Terras.FollowsParityBit,
        Bool.false_eq_true, ↓reduceIte] using h
    intro i hi
    cases i with
    | zero => simpa using hp.1
    | succ i =>
      simpa only [Function.iterate_succ_apply] using ih hp.2 i (by omega)

theorem odd_index_in_syracuse_block_eq_zero {q i : ℕ} (hq : Odd q)
    (hi : i < Tao.syracuseExponent q) (hodd : Odd ((Terras.accelerated^[i]) q)) : i = 0 := by
  by_contra hne
  have hi0 : 0 < i := Nat.pos_of_ne_zero hne
  have hf := Tao.followsParityList_syracuseParityBlock hq
  change Terras.FollowsParityBit true q ∧
    Terras.FollowsParityList (List.replicate (Tao.syracuseExponent q - 1) false)
      (Terras.accelerated q) at hf
  have he := follows_false_prefix_even hf.2 (i - 1) (by omega)
  have heq : (Terras.accelerated^[i - 1]) (Terras.accelerated q) =
      (Terras.accelerated^[i]) q := by
    rw [← Function.iterate_succ_apply]
    congr 1
    omega
  rw [heq] at he
  exact (Nat.not_even_iff_odd.mpr hodd) he

/-- Every odd source state inside the shortcut expansion of a Syracuse prefix
is one of the actual Syracuse source states in that prefix. -/
theorem odd_shortcut_prefix_is_syracuse_source (n q : ℕ) (hq : Odd q)
    (i : ℕ) (hi : i < Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq))
    (hodd : Odd ((Terras.accelerated^[i]) q)) :
    ∃ j < n, (Terras.accelerated^[i]) q = (Tao.syracuse^[j]) q := by
  induction n generalizing q i with
  | zero => simp [Tao.syracuseValuationPNatList, Tao.taoTupleWeight] at hi
  | succ n ih =>
    have hlength : Tao.taoTupleWeight (Tao.syracuseValuationPNatList (n + 1) q hq) =
        Tao.syracuseExponent q +
          Tao.taoTupleWeight (Tao.syracuseValuationPNatList n (Tao.syracuse q) (Tao.syracuse_odd q)) := by
      simp [Tao.syracuseValuationPNatList, Tao.taoTupleWeight]
    rw [hlength] at hi
    have hland : (Terras.accelerated^[Tao.syracuseExponent q]) q = Tao.syracuse q := by
      simpa only [Tao.syracuseParityBlock_length] using
        Tao.accelerated_iterate_syracuseParityBlock_length_eq_syracuse hq
    by_cases hblock : i < Tao.syracuseExponent q
    · have hiz := odd_index_in_syracuse_block_eq_zero hq hblock hodd
      subst i
      exact ⟨0, Nat.succ_pos n, rfl⟩
    · have hai : Tao.syracuseExponent q ≤ i := Nat.le_of_not_gt hblock
      have he : (Terras.accelerated^[i]) q =
          (Terras.accelerated^[i - Tao.syracuseExponent q]) (Tao.syracuse q) := by
        rw [← hland, ← Function.iterate_add_apply, Nat.sub_add_cancel hai]
      obtain ⟨j, hj, hjEq⟩ := ih (Tao.syracuse q) (Tao.syracuse_odd q)
        (i - Tao.syracuseExponent q) (by omega) (by simpa only [he] using hodd)
      refine ⟨j + 1, by omega, ?_⟩
      simpa only [Function.iterate_succ_apply] using he.trans hjEq

theorem first_passage_shortcut_odd_sources_above {B q n : ℕ} (hq : Odd q)
    (hfirst : Tao.syracuseFirstHitAtMost B q n) :
    ∀ i < Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq),
      Odd ((Terras.accelerated^[i]) q) → B < (Terras.accelerated^[i]) q := by
  intro i hi hodd
  obtain ⟨j, hj, he⟩ := odd_shortcut_prefix_is_syracuse_source n q hq i hi hodd
  rw [he]
  exact hfirst.2 j hj

#print axioms odd_shortcut_prefix_is_syracuse_source
#print axioms first_passage_shortcut_odd_sources_above

end CollatzCanonical.NativeTao
