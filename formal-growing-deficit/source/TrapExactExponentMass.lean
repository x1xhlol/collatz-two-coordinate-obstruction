import TrapMicrocanonicalSource
import Mathlib.Tactic

/-! The exact negative-binomial mass of the positive geometric source. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace Erdos1135.Tao

theorem trap_tuple_weight_eq_sum (as : List ℕ+) :
    taoTupleWeight as = (as.map fun a : ℕ+ => (a : ℕ)).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa [taoTupleWeight] using congrArg (fun n => (a : ℕ) + n) ih

theorem trap_bounded_tuple_of_list {as : List ℕ+} {n M : ℕ}
    (hlen : as.length = n) (hw : taoTupleWeight as < M) :
    ∃ v : BoundedValuationTuple n M, BoundedValuationTuple.toList v = as := by
  subst n
  have hentry (i : Fin as.length) : (as.get i : ℕ) < M := by
    apply lt_of_le_of_lt ?_ hw
    rw [trap_tuple_weight_eq_sum]
    exact List.single_le_sum (fun x _ => Nat.zero_le x) _
      (List.mem_map_of_mem (f := fun a : ℕ+ => (a : ℕ)) (as.get_mem i))
  let f : Fin as.length → PNatBelow M :=
    fun i => ⟨⟨(as.get i : ℕ), hentry i⟩, (as.get i).2⟩
  have hsum : (∑ i, (PNatBelow.toPNat (f i) : ℕ)) = taoTupleWeight as := by
    rw [trap_tuple_weight_eq_sum]
    change (∑ i : Fin as.length, (as.get i : ℕ)) = (as.map fun a : ℕ+ => (a : ℕ)).sum
    calc
      _ = (List.ofFn fun i : Fin as.length => (as.get i : ℕ)).sum :=
        (List.sum_ofFn).symm
      _ = ((List.ofFn as.get).map fun a : ℕ+ => (a : ℕ)).sum := by
        rw [List.map_ofFn]
        rfl
      _ = _ := by rw [List.ofFn_get]
  refine ⟨⟨f, hsum ▸ hw⟩, ?_⟩
  change List.ofFn (fun i => PNatBelow.toPNat (f i)) = as
  calc
    _ = List.ofFn as.get := by
      congr 1
    _ = as := List.ofFn_get as

def trapCompleteValuationTuple {n s : ℕ} (v : BoundedValuationTuple n s) : List ℕ+ :=
  ⟨s - taoTupleWeight (BoundedValuationTuple.toList v),
    Nat.sub_pos_of_lt (BoundedValuationTuple.taoTupleWeight_toList_lt v)⟩ ::
      BoundedValuationTuple.toList v

theorem trapCompleteValuationTuple_length {n s : ℕ} (v : BoundedValuationTuple n s) :
    (trapCompleteValuationTuple v).length = n + 1 := by
  simp [trapCompleteValuationTuple, BoundedValuationTuple.toList_length]

theorem trapCompleteValuationTuple_weight {n s : ℕ} (v : BoundedValuationTuple n s) :
    taoTupleWeight (trapCompleteValuationTuple v) = s := by
  change s - taoTupleWeight (BoundedValuationTuple.toList v) +
    taoTupleWeight (BoundedValuationTuple.toList v) = s
  exact Nat.sub_add_cancel (Nat.le_of_lt (BoundedValuationTuple.taoTupleWeight_toList_lt v))

theorem trapCompleteValuationTuple_injective (n s : ℕ) :
    Function.Injective (trapCompleteValuationTuple (n := n) (s := s)) := by
  intro v w h
  exact boundedValuationTuple_toList_injective (List.cons.inj h).2

theorem trapCompleteValuationTuple_surjective {n s : ℕ} {as : List ℕ+}
    (hlen : as.length = n + 1) (hw : taoTupleWeight as = s) :
    ∃ v : BoundedValuationTuple n s, trapCompleteValuationTuple v = as := by
  cases as with
  | nil => simp at hlen
  | cons a as =>
      have htail : as.length = n := by simpa using hlen
      have hweight : (a : ℕ) + taoTupleWeight as = s := hw
      have hlt : taoTupleWeight as < s := by have ha : 0 < (a : ℕ) := a.2; omega
      obtain ⟨v, hv⟩ := trap_bounded_tuple_of_list htail hlt
      refine ⟨v, ?_⟩
      unfold trapCompleteValuationTuple
      refine congrArg₂ List.cons ?_ hv
      apply Subtype.ext
      change s - taoTupleWeight (BoundedValuationTuple.toList v) = (a : ℕ)
      rw [hv]
      omega

theorem unitSourceExponentMass_succ_eq_choose (n s : ℕ) (hs : 0 < s) :
    unitSourceExponentMass (n + 1) s =
      ((s - 1).choose n : ℝ) * (1 / 2 : ℝ) ^ s := by
  classical
  let S : Finset (List ℕ+) := Finset.univ.image
    (trapCompleteValuationTuple (n := n) (s := s))
  have hout (as : List ℕ+) (has : as ∉ S) :
      (if taoTupleWeight as = s then (geom2PNatListPMF (n + 1) as).toReal else 0) = 0 := by
    by_cases hw : taoTupleWeight as = s
    · have hlen : as.length ≠ n + 1 := by
        intro heq
        obtain ⟨v, hv⟩ := trapCompleteValuationTuple_surjective heq hw
        exact has (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hv⟩)
      rw [ite_eq_left hw, geom2PNatListPMF_apply_eq_zero_of_length_ne (n + 1) as hlen]
      rfl
    · simp [hw]
  rw [unitSourceExponentMass_eq_tsum, tsum_eq_sum hout]
  change (∑ as ∈ Finset.univ.image (trapCompleteValuationTuple (n := n) (s := s)),
    if taoTupleWeight as = s then (geom2PNatListPMF (n + 1) as).toReal else 0) = _
  rw [Finset.sum_image (fun v _ w _ h => trapCompleteValuationTuple_injective n s h)]
  have hterm (v : BoundedValuationTuple n s) :
      (if taoTupleWeight (trapCompleteValuationTuple v) = s then
        (geom2PNatListPMF (n + 1) (trapCompleteValuationTuple v)).toReal else 0) =
          (1 / 2 : ℝ) ^ s := by
    rw [trapCompleteValuationTuple_weight, ite_eq_left rfl]
    have h := geom2PNatListPMF_apply_length_toReal_eq_weight (trapCompleteValuationTuple v)
    rw [trapCompleteValuationTuple_length, trapCompleteValuationTuple_weight] at h
    exact h
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_boundedValuationTuple n s hs]

theorem unitSourceExponentMass_eq_choose (k s : ℕ) (hk : 1 ≤ k) (hs : 0 < s) :
    unitSourceExponentMass k s =
      ((s - 1).choose (k - 1) : ℝ) * (1 / 2 : ℝ) ^ s := by
  have h := unitSourceExponentMass_succ_eq_choose (k - 1) s hs
  simpa [Nat.sub_add_cancel hk] using h

theorem unitSourceExponentMass_central_eq_choose (k : ℕ) (hk : 1 ≤ k) :
    unitSourceExponentMass k (2 * k) =
      ((2 * k - 1).choose (k - 1) : ℝ) * (1 / 2 : ℝ) ^ (2 * k) := by
  exact unitSourceExponentMass_eq_choose k (2 * k) hk (by omega)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.unitSourceExponentMass_eq_choose
#print axioms Erdos1135.Tao.unitSourceExponentMass_central_eq_choose
