/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.Truncation

namespace Erdos1135Predecessor.Tao

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

noncomputable def ofList {n M : ℕ} (as : List ℕ+)
    (hlen : as.length = n) (hweight : taoTupleWeight as < M) :
    BoundedValuationTuple n M :=
  Classical.choose (exists_toList_eq as hlen hweight)

@[simp] theorem toList_ofList {n M : ℕ} (as : List ℕ+)
    (hlen : as.length = n) (hweight : taoTupleWeight as < M) :
    toList (ofList as hlen hweight) = as :=
  Classical.choose_spec (exists_toList_eq as hlen hweight)

end BoundedValuationTuple

end Erdos1135Predecessor.Tao
