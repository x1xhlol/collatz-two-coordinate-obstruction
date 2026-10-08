import Erdos1135.ND.Fourier.FiberConditioning
import Erdos1135.Tao.Syracuse.AffineTrajectory

/-!
# Subtraction-Free Fixed-Total Splitting

This leaf splits a fixed-total positive valuation list at a prescribed block
boundary.  The split index records both block totals and their additive
relation to the original total; no truncated subtraction is used.

The index carries the necessary length lower bounds used by later finite
uniform laws.  Actual feasibility comes from inhabiting its accompanying
fiber: at zero length the lower bound alone is not sufficient.  The
equivalence itself is unconditional, including at zero block lengths and on
empty fibers.
-/

namespace Erdos1135
namespace ND

open Tao

private theorem nd_length_le_taoTupleWeight (as : List ℕ+) :
    as.length ≤ Tao.taoTupleWeight as := by
  induction as with
  | nil =>
      simp [Tao.taoTupleWeight]
  | cons a as ih =>
      have ha : 1 ≤ (a : ℕ) := a.2
      change as.length + 1 ≤ (a : ℕ) + Tao.taoTupleWeight as
      omega

/-- Head and tail totals with necessary length lower bounds and the original
additive total. -/
@[ext]
structure NDFixedTotalSplitIndex
    (headLength tailLength L : ℕ) where
  headTotal : ℕ
  tailTotal : ℕ
  headLength_le : headLength ≤ headTotal
  tailLength_le : tailLength ≤ tailTotal
  total_eq : headTotal + tailTotal = L

/-- The product of the two fixed-total valuation fibers at a split index. -/
abbrev NDFixedTotalSplitFiber
    {headLength tailLength L : ℕ}
    (s : NDFixedTotalSplitIndex headLength tailLength L) :=
  NDFixedTotalValuations headLength s.headTotal ×
    NDFixedTotalValuations tailLength s.tailTotal

/-- A fixed-total valuation list represented by its additive split index and
the two corresponding blocks. -/
abbrev NDFixedTotalSplit (headLength tailLength L : ℕ) :=
  Σ s : NDFixedTotalSplitIndex headLength tailLength L,
    NDFixedTotalSplitFiber s

private def ndFixedTotalSplitForward
    (h t L : ℕ) (a : NDFixedTotalValuations (h + t) L) :
    NDFixedTotalSplit h t L := by
  let head := a.1.take h
  let tail := a.1.drop h
  have hheadLength : head.length = h := by
    dsimp [head]
    rw [List.length_take, a.2.1]
    omega
  have htailLength : tail.length = t := by
    dsimp [tail]
    rw [List.length_drop, a.2.1]
    omega
  refine ⟨{
    headTotal := Tao.taoTupleWeight head
    tailTotal := Tao.taoTupleWeight tail
    headLength_le := ?_
    tailLength_le := ?_
    total_eq := ?_
  }, ⟨⟨head, ⟨hheadLength, rfl⟩⟩,
      ⟨tail, ⟨htailLength, rfl⟩⟩⟩⟩
  · simpa only [hheadLength] using nd_length_le_taoTupleWeight head
  · simpa only [htailLength] using nd_length_le_taoTupleWeight tail
  · simpa only [head, tail] using
      (Tao.taoTupleWeight_take_add_drop_trajectory a.1 h).trans a.2.2

private def ndFixedTotalSplitBackward
    (h t L : ℕ) (z : NDFixedTotalSplit h t L) :
    NDFixedTotalValuations (h + t) L :=
  ⟨z.2.1.1 ++ z.2.2.1, by
    constructor
    · simp only [List.length_append, z.2.1.2.1, z.2.2.2.1]
    · calc
        Tao.taoTupleWeight (z.2.1.1 ++ z.2.2.1) =
            Tao.taoTupleWeight z.2.1.1 +
              Tao.taoTupleWeight z.2.2.1 :=
          Tao.taoTupleWeight_append_trajectory _ _
        _ = z.1.headTotal + z.1.tailTotal := by
          rw [z.2.1.2.2, z.2.2.2.2]
        _ = L := z.1.total_eq⟩

private theorem nd_prod_heq {alpha alpha' beta beta' : Type}
    {a : alpha} {a' : alpha'} {b : beta} {b' : beta'}
    (ha : a ≍ a') (hb : b ≍ b') : (a, b) ≍ (a', b') := by
  cases ha
  cases hb
  rfl

/-- Taking and dropping at the head length gives an exact additive
decomposition of a fixed-total valuation fiber. -/
def ndFixedTotalValuationsEquivSplit (h t L : ℕ) :
    NDFixedTotalValuations (h + t) L ≃
      NDFixedTotalSplit h t L where
  toFun := ndFixedTotalSplitForward h t L
  invFun := ndFixedTotalSplitBackward h t L
  left_inv a := by
    apply Subtype.ext
    exact List.take_append_drop h a.1
  right_inv z := by
    rcases z with
      ⟨⟨headTotal, tailTotal, _hheadFeasible, _htailFeasible, htotal⟩,
        ⟨⟨head, hheadLength, hheadWeight⟩,
          ⟨tail, htailLength, htailWeight⟩⟩⟩
    change Tao.taoTupleWeight head = headTotal at hheadWeight
    change Tao.taoTupleWeight tail = tailTotal at htailWeight
    subst headTotal
    subst tailTotal
    have htake : List.take h (head ++ tail) = head := by
      rw [← hheadLength]
      exact List.take_append_length
    have hdrop : List.drop h (head ++ tail) = tail := by
      rw [← hheadLength]
      exact List.drop_append_length
    simp [ndFixedTotalSplitForward, ndFixedTotalSplitBackward, htake, hdrop]
    apply nd_prod_heq
    · refine (Subtype.heq_iff_coe_eq ?_).2 rfl
      intro xs
      simp [htake]
    · refine (Subtype.heq_iff_coe_eq ?_).2 rfl
      intro ys
      simp [hdrop]

@[simp]
theorem ndFixedTotalValuationsEquivSplit_headTotal
    (h t L : ℕ) (a : NDFixedTotalValuations (h + t) L) :
    ((ndFixedTotalValuationsEquivSplit h t L) a).1.headTotal =
      Tao.taoTupleWeight (a.1.take h) := rfl

@[simp]
theorem ndFixedTotalValuationsEquivSplit_tailTotal
    (h t L : ℕ) (a : NDFixedTotalValuations (h + t) L) :
    ((ndFixedTotalValuationsEquivSplit h t L) a).1.tailTotal =
      Tao.taoTupleWeight (a.1.drop h) := rfl

@[simp]
theorem ndFixedTotalValuationsEquivSplit_head
    (h t L : ℕ) (a : NDFixedTotalValuations (h + t) L) :
    ((ndFixedTotalValuationsEquivSplit h t L) a).2.1.1 =
      a.1.take h := rfl

@[simp]
theorem ndFixedTotalValuationsEquivSplit_tail
    (h t L : ℕ) (a : NDFixedTotalValuations (h + t) L) :
    ((ndFixedTotalValuationsEquivSplit h t L) a).2.2.1 =
      a.1.drop h := rfl

@[simp]
theorem ndFixedTotalValuationsEquivSplit_symm_apply_val
    (h t L : ℕ) (z : NDFixedTotalSplit h t L) :
    ((ndFixedTotalValuationsEquivSplit h t L).symm z).1 =
      z.2.1.1 ++ z.2.2.1 := rfl

end ND
end Erdos1135
