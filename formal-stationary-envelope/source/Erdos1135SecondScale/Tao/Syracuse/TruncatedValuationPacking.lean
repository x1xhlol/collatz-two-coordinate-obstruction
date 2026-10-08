/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Truncation

/-!
# Packing truncated valuation tuples

This file gives the strict finite packer used by the Proposition 1.9 route.
Lists of the wrong length or of total weight at least the cutoff are sent to
the overflow value `none`.
-/

namespace Erdos1135SecondScale.Tao

private theorem taoTupleWeight_eq_map_sum (as : List ℕ+) :
    taoTupleWeight as = (as.map fun a : ℕ+ => (a : ℕ)).sum := by
  unfold taoTupleWeight
  rw [List.bind_eq_flatMap]
  rw [show List.map (fun a : ℕ => a)
        (List.flatMap (fun a : ℕ+ => pure (a : ℕ)) as) =
      List.flatMap (fun a : ℕ+ => pure (a : ℕ)) as by
    exact List.map_id _]
  rw [show List.flatMap (fun a : ℕ+ => pure (a : ℕ)) as =
      List.map (fun a : ℕ+ => (a : ℕ)) as by
    simpa [Function.comp_def] using
      List.flatMap_pure_eq_map (fun a : ℕ+ => (a : ℕ)) as]

namespace BoundedValuationTuple

private noncomputable def getLength {n : ℕ} (as : List ℕ+)
    (hlen : as.length = n) : Fin n → ℕ+ :=
  fun i => as.get (Fin.cast hlen.symm i)

private theorem ofFn_getLength {n : ℕ} (as : List ℕ+)
    (hlen : as.length = n) :
    List.ofFn (getLength as hlen) = as := by
  subst n
  unfold getLength
  convert List.ofFn_get as using 1

private theorem exists_toList_eq {n M : ℕ} (as : List ℕ+)
    (hlen : as.length = n) (hweight : taoTupleWeight as < M) :
    ∃ v : BoundedValuationTuple n M, toList v = as := by
  let f : Fin n → ℕ+ := getLength as hlen
  have hf : List.ofFn f = as := ofFn_getLength as hlen
  let g : Fin n → PNatBelow M := fun i => by
    have hmem : f i ∈ as := by
      rw [← hf]
      simp
    have hmemNat : (f i : ℕ) ∈ as.map (fun a : ℕ+ => (a : ℕ)) :=
      List.mem_map.mpr ⟨f i, hmem, rfl⟩
    have hle : (f i : ℕ) ≤ taoTupleWeight as := by
      rw [taoTupleWeight_eq_map_sum]
      exact List.le_sum_of_mem hmemNat
    exact ⟨⟨(f i : ℕ), hle.trans_lt hweight⟩, (f i).2⟩
  have hgweight : (Finset.univ.sum fun i =>
      (PNatBelow.toPNat (g i) : ℕ)) < M := by
    change (Finset.univ.sum fun i => (f i : ℕ)) < M
    have hmap : List.ofFn (fun i => (f i : ℕ)) =
        as.map (fun a : ℕ+ => (a : ℕ)) := by
      simpa [Function.comp_def] using
        congrArg (List.map fun a : ℕ+ => (a : ℕ)) hf
    calc
      (Finset.univ.sum fun i => (f i : ℕ)) =
          (List.ofFn (fun i => (f i : ℕ))).sum := List.sum_ofFn.symm
      _ = (as.map fun a : ℕ+ => (a : ℕ)).sum := congrArg List.sum hmap
      _ = taoTupleWeight as := (taoTupleWeight_eq_map_sum as).symm
      _ < M := hweight
  let v : BoundedValuationTuple n M := ⟨g, hgweight⟩
  refine ⟨v, ?_⟩
  change List.ofFn (fun i => PNatBelow.toPNat (g i)) = as
  change List.ofFn f = as
  exact hf

/-- Pack a list of the correct length and strict total weight into a bounded tuple. -/
noncomputable def ofList {n M : ℕ} (as : List ℕ+)
    (hlen : as.length = n) (hweight : taoTupleWeight as < M) :
    BoundedValuationTuple n M :=
  Classical.choose (exists_toList_eq as hlen hweight)

@[simp] theorem toList_ofList {n M : ℕ} (as : List ℕ+)
    (hlen : as.length = n) (hweight : taoTupleWeight as < M) :
    toList (ofList as hlen hweight) = as :=
  Classical.choose_spec (exists_toList_eq as hlen hweight)

theorem toList_injective {n M : ℕ} :
    Function.Injective (toList (n := n) (M := M)) := by
  intro v w h
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply Fin.ext
  have hf : (fun i : Fin n => PNatBelow.toPNat (v.1 i)) =
      (fun i : Fin n => PNatBelow.toPNat (w.1 i)) := by
    apply List.ofFn_injective
    exact h
  have hi := congrFun hf i
  exact congrArg Subtype.val hi

@[simp] theorem ofList_toList {n M : ℕ} (v : BoundedValuationTuple n M) :
    ofList (toList v) (toList_length v) (taoTupleWeight_toList_lt v) = v := by
  apply toList_injective
  rw [toList_ofList]

end BoundedValuationTuple

/-- Pack an exact-length, strict-weight list, sending every other list to overflow. -/
noncomputable def truncateValuationList (n M : ℕ) (as : List ℕ+) :
    TruncatedValuationTuple n M :=
  if hlen : as.length = n then
    if hweight : taoTupleWeight as < M then
      some (BoundedValuationTuple.ofList as hlen hweight)
    else
      none
  else
    none

theorem truncateValuationList_eq_some_iff {n M : ℕ} {as : List ℕ+}
    {v : BoundedValuationTuple n M} :
    truncateValuationList n M as = some v ↔
      as = BoundedValuationTuple.toList v := by
  by_cases hlen : as.length = n
  · by_cases hweight : taoTupleWeight as < M
    · constructor
      · intro h
        simp [truncateValuationList, hlen, hweight] at h
        rw [← h, BoundedValuationTuple.toList_ofList]
      · intro h
        subst as
        simp [truncateValuationList, BoundedValuationTuple.toList_length,
          BoundedValuationTuple.taoTupleWeight_toList_lt,
          BoundedValuationTuple.ofList_toList]
    · constructor
      · intro h
        simp [truncateValuationList, hlen, hweight] at h
      · intro h
        subst as
        exact False.elim
          (hweight (BoundedValuationTuple.taoTupleWeight_toList_lt v))
  · constructor
    · intro h
      simp [truncateValuationList, hlen] at h
    · intro h
      subst as
      exact False.elim (hlen (BoundedValuationTuple.toList_length v))

theorem truncateValuationList_eq_none_iff (n M : ℕ) (as : List ℕ+) :
    truncateValuationList n M as = none ↔
      as.length ≠ n ∨ M ≤ taoTupleWeight as := by
  by_cases hlen : as.length = n
  · by_cases hweight : taoTupleWeight as < M
    · simp [truncateValuationList, hlen, hweight]
    · simp [truncateValuationList, hlen, hweight, Nat.le_of_not_gt hweight]
  · simp [truncateValuationList, hlen]

theorem truncateValuationList_eq_none_iff_of_length {n M : ℕ} {as : List ℕ+}
    (hlen : as.length = n) :
    truncateValuationList n M as = none ↔ M ≤ taoTupleWeight as := by
  rw [truncateValuationList_eq_none_iff]
  simp [hlen]

theorem truncateValuationList_eq_none_of_weight_eq {n M : ℕ} {as : List ℕ+}
    (hweight : taoTupleWeight as = M) :
    truncateValuationList n M as = none := by
  rw [truncateValuationList_eq_none_iff]
  exact Or.inr hweight.ge

theorem truncateValuationList_eq_none_of_length_ne {n M : ℕ} {as : List ℕ+}
    (hlen : as.length ≠ n) :
    truncateValuationList n M as = none := by
  rw [truncateValuationList_eq_none_iff]
  exact Or.inl hlen

theorem truncateValuationList_zero_zero_nil :
    truncateValuationList 0 0 [] = none := by
  apply truncateValuationList_eq_none_of_weight_eq
  rfl

theorem truncateValuationList_zero_one_nil_isSome :
    (truncateValuationList 0 1 []).isSome = true := by
  simp [truncateValuationList, taoTupleWeight]

theorem truncateValuationList_one_two_one_isSome :
    (truncateValuationList 1 2 [1]).isSome = true := by
  norm_num [truncateValuationList, taoTupleWeight]

theorem truncateValuationList_one_two_two_none :
    truncateValuationList 1 2 [2] = none := by
  apply truncateValuationList_eq_none_of_weight_eq
  rfl

theorem truncateValuationList_wrong_length_canary :
    truncateValuationList 1 3 [] = none := by
  apply truncateValuationList_eq_none_of_length_ne
  simp

end Erdos1135SecondScale.Tao
