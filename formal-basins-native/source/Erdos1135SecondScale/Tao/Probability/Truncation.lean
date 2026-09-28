/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Geom
import Erdos1135SecondScale.Tao.Syracuse.Affine
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Sym.Card

/-!
# Finite Truncation Interface For Valuation Tuples

This module introduces a finite codomain for later truncated positive-valuation tuple laws.  It
defines the bounded tuple type, its list/weight adapters, and the finite stars-and-bars count for
bounded positive tuples.  Iid tuple PMFs, tail estimates, and Proposition 1.9 statements are left
to later modules.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Positive naturals less than a cutoff `M`, represented as positive elements of `Fin M`. -/
abbrev PNatBelow (M : ℕ) : Type :=
  {a : Fin M // 0 < (a : ℕ)}

namespace PNatBelow

def toPNat {M : ℕ} (a : PNatBelow M) : ℕ+ :=
  ⟨a.1, a.2⟩

theorem toPNat_lt {M : ℕ} (a : PNatBelow M) :
    (toPNat a : ℕ) < M :=
  a.1.2

instance (M : ℕ) : Fintype (PNatBelow M) := inferInstance
instance (M : ℕ) : DecidableEq (PNatBelow M) := inferInstance

end PNatBelow

/-- Length-`n` positive valuation tuples with every entry below `M` and total weight `< M`. -/
abbrev BoundedValuationTuple (n M : ℕ) : Type :=
  {v : Fin n → PNatBelow M //
    (Finset.univ.sum fun i => (PNatBelow.toPNat (v i) : ℕ)) < M}

/-- Length-`n` nonnegative tuples whose shifted positive total is below `M + 1`. -/
abbrev NonnegBoundedTuple (n M : ℕ) : Type :=
  {f : Fin n → ℕ // (Finset.univ.sum fun i => f i) + n < M + 1}

namespace BoundedValuationTuple

instance (n M : ℕ) : Fintype (BoundedValuationTuple n M) := inferInstance
instance (n M : ℕ) : DecidableEq (BoundedValuationTuple n M) := inferInstance

def toList {n M : ℕ} (v : BoundedValuationTuple n M) : List ℕ+ :=
  List.ofFn fun i : Fin n => PNatBelow.toPNat (v.1 i)

theorem toList_length {n M : ℕ} (v : BoundedValuationTuple n M) :
    (toList v).length = n := by
  simp [toList]

theorem taoTupleWeight_toList {n M : ℕ} (v : BoundedValuationTuple n M) :
    taoTupleWeight (toList v) =
      Finset.univ.sum fun i => (PNatBelow.toPNat (v.1 i) : ℕ) := by
  unfold taoTupleWeight toList
  rw [List.bind_eq_flatMap]
  rw [show List.map (fun a : ℕ => a)
        (List.flatMap (fun a : ℕ+ => pure (a : ℕ))
          (List.ofFn fun i : Fin n => PNatBelow.toPNat (v.1 i))) =
      List.flatMap (fun a : ℕ+ => pure (a : ℕ))
          (List.ofFn fun i : Fin n => PNatBelow.toPNat (v.1 i)) by
    exact List.map_id _]
  rw [show List.flatMap (fun a : ℕ+ => pure (a : ℕ))
        (List.ofFn fun i : Fin n => PNatBelow.toPNat (v.1 i)) =
      List.map (fun a : ℕ+ => (a : ℕ))
        (List.ofFn fun i : Fin n => PNatBelow.toPNat (v.1 i)) by
    simpa [Function.comp_def] using
      List.flatMap_pure_eq_map (fun a : ℕ+ => (a : ℕ))
        (List.ofFn fun i : Fin n => PNatBelow.toPNat (v.1 i))]
  rw [List.map_ofFn]
  change (List.ofFn (fun i : Fin n => (PNatBelow.toPNat (v.1 i) : ℕ))).sum =
    Finset.univ.sum fun i => (PNatBelow.toPNat (v.1 i) : ℕ)
  rw [List.sum_ofFn]

theorem taoTupleWeight_toList_lt {n M : ℕ} (v : BoundedValuationTuple n M) :
    taoTupleWeight (toList v) < M := by
  rw [taoTupleWeight_toList]
  exact v.2

/-- Subtract one from each positive entry of a successor-cutoff bounded tuple. -/
noncomputable def toNonneg {n M : ℕ} (v : BoundedValuationTuple n (M + 1)) :
    Fin n → ℕ :=
  fun i => (PNatBelow.toPNat (v.1 i) : ℕ) - 1

theorem sum_toNonneg_add_length {n M : ℕ} (v : BoundedValuationTuple n (M + 1)) :
    (Finset.univ.sum fun i => toNonneg v i) + n =
      Finset.univ.sum fun i => (PNatBelow.toPNat (v.1 i) : ℕ) := by
  unfold toNonneg
  calc
    (Finset.univ.sum fun i : Fin n => (PNatBelow.toPNat (v.1 i) : ℕ) - 1) + n
        = (Finset.univ.sum fun i : Fin n => (PNatBelow.toPNat (v.1 i) : ℕ) - 1) +
            (Finset.univ.sum fun _i : Fin n => 1) := by
      simp
    _ = Finset.univ.sum fun i : Fin n =>
        ((PNatBelow.toPNat (v.1 i) : ℕ) - 1 + 1) := by
      rw [Finset.sum_add_distrib]
    _ = Finset.univ.sum fun i : Fin n => (PNatBelow.toPNat (v.1 i) : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hpos : 0 < (PNatBelow.toPNat (v.1 i) : ℕ) :=
        (PNatBelow.toPNat (v.1 i)).2
      omega

theorem sum_toNonneg_lt {n M : ℕ} (v : BoundedValuationTuple n (M + 1)) :
    Finset.univ.sum (fun i => toNonneg v i) < M + 1 - n := by
  have hsum := sum_toNonneg_add_length v
  have hv := v.2
  omega

/-- Positive bounded tuples are nonnegative bounded tuples after subtracting one entrywise. -/
noncomputable def equivNonnegBounded (n M : ℕ) :
    BoundedValuationTuple n (M + 1) ≃ NonnegBoundedTuple n M where
  toFun v := ⟨toNonneg v, by
    rw [sum_toNonneg_add_length]
    exact v.2⟩
  invFun f := by
    refine ⟨fun i => ⟨⟨f.1 i + 1, ?_⟩, Nat.succ_pos _⟩, ?_⟩
    · have hfi_le_sum : f.1 i ≤ Finset.univ.sum fun j : Fin n => f.1 j := by
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
      have hf := f.2
      omega
    · have hsum_add :
          (Finset.univ.sum fun i : Fin n => (f.1 i + 1)) =
            (Finset.univ.sum fun i : Fin n => f.1 i) + n := by
        rw [Finset.sum_add_distrib]
        simp
      change (Finset.univ.sum fun i : Fin n => (f.1 i + 1)) < M + 1
      rw [hsum_add]
      exact f.2
  left_inv := by
    intro v
    apply Subtype.ext
    funext i
    apply Subtype.ext
    apply Fin.ext
    simp [toNonneg]
    have hval : (PNatBelow.toPNat (v.1 i) : ℕ) = ((v.1 i).1 : ℕ) := rfl
    have hpos : 0 < (PNatBelow.toPNat (v.1 i) : ℕ) :=
      (PNatBelow.toPNat (v.1 i)).2
    omega
  right_inv := by
    intro f
    apply Subtype.ext
    funext i
    change (f.1 i + 1) - 1 = f.1 i
    omega

noncomputable def nonnegBoundedEquivSigmaExact (n M : ℕ) :
    NonnegBoundedTuple n M ≃
      Σ s : Fin (M + 1 - n),
        {f : Fin n → ℕ // Finset.univ.sum (fun i => f i) = (s : ℕ)} where
  toFun f := ⟨⟨Finset.univ.sum fun i => f.1 i, by
      exact sum_toNonneg_lt ((equivNonnegBounded n M).symm f)⟩, ⟨f.1, rfl⟩⟩
  invFun x := ⟨x.2.1, by
    rw [x.2.2]
    have hx : (x.1 : ℕ) < M + 1 - n := x.1.2
    omega⟩
  left_inv := by
    intro f
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨s, hs⟩, ⟨f, hf⟩⟩
    dsimp at hf ⊢
    cases hf
    rfl

noncomputable def sigmaExactEquivSigmaSym (n M : ℕ) :
    (Σ s : Fin (M + 1 - n),
        {f : Fin n → ℕ // Finset.univ.sum (fun i => f i) = (s : ℕ)}) ≃
      Σ s : Fin (M + 1 - n), Sym (Fin n) (s : ℕ) where
  toFun x := ⟨x.1, (Sym.equivNatSumOfFintype (Fin n) (x.1 : ℕ)).symm x.2⟩
  invFun x := ⟨x.1, (Sym.equivNatSumOfFintype (Fin n) (x.1 : ℕ)) x.2⟩
  left_inv := by
    intro x
    cases x
    simp
  right_inv := by
    intro x
    cases x
    simp

noncomputable def equivSigmaSym (n M : ℕ) :
    BoundedValuationTuple n (M + 1) ≃
      Σ s : Fin (M + 1 - n), Sym (Fin n) (s : ℕ) :=
  (equivNonnegBounded n M).trans
    ((nonnegBoundedEquivSigmaExact n M).trans (sigmaExactEquivSigmaSym n M))

theorem card_sigma_sym_fin_cutoff (n M : ℕ) :
    Fintype.card (Σ s : Fin (M + 1 - n), Sym (Fin n) (s : ℕ)) =
      Nat.choose M n := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Sym.card_sym_eq_multichoose, Fintype.card_fin]
  by_cases hK : 0 < M + 1 - n
  · rw [Finset.sum_fin_eq_sum_range]
    have hsum_if :
        (∑ x ∈ Finset.range (M + 1 - n),
            if h : x < M + 1 - n then Nat.multichoose n x else 0) =
          ∑ x ∈ Finset.range (M + 1 - n), Nat.multichoose n x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]
    rw [hsum_if]
    rw [show M + 1 - n = (M + 1 - n - 1) + 1 by omega]
    have htop : M + 1 - n - 1 + n = M := by omega
    simpa [htop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.sum_range_multichoose (M + 1 - n - 1) n
  · have hn_gt : M < n := by omega
    rw [Nat.choose_eq_zero_of_lt hn_gt]
    have hK0 : M + 1 - n = 0 := by omega
    rw [hK0]
    simp

theorem card_succ (n M : ℕ) :
    Fintype.card (BoundedValuationTuple n (M + 1)) = Nat.choose M n := by
  rw [Fintype.card_congr (equivSigmaSym n M)]
  exact card_sigma_sym_fin_cutoff n M

theorem card (n M : ℕ) (hM : 0 < M) :
    Fintype.card (BoundedValuationTuple n M) = Nat.choose (M - 1) n := by
  have hsucc : M - 1 + 1 = M := by omega
  simpa [hsucc] using card_succ n (M - 1)

end BoundedValuationTuple

theorem card_boundedValuationTuple_succ (n M : ℕ) :
    Fintype.card (BoundedValuationTuple n (M + 1)) = Nat.choose M n :=
  BoundedValuationTuple.card_succ n M

theorem card_boundedValuationTuple (n M : ℕ) (hM : 0 < M) :
    Fintype.card (BoundedValuationTuple n M) = Nat.choose (M - 1) n :=
  BoundedValuationTuple.card n M hM

/-- Finite truncation codomain: `none` is the overflow bucket. -/
abbrev TruncatedValuationTuple (n M : ℕ) : Type :=
  Option (BoundedValuationTuple n M)

instance (n M : ℕ) : Fintype (TruncatedValuationTuple n M) := inferInstance
instance (n M : ℕ) : DecidableEq (TruncatedValuationTuple n M) := inferInstance

end Tao
end Erdos1135SecondScale
