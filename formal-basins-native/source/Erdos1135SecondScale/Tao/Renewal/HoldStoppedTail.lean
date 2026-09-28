/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.HoldIID
import Erdos1135SecondScale.Tao.Renewal.QFiniteApprox

/-!
# Shared Hold Stopped-Tail Support

This module records the first reusable Hold-list algebra needed before the
outer `(7.54)` large-horizontal tail and Lemma 7.10 `E'` probability sockets.
It proves fixed-list append mass identities and a finite prefix/tail cylinder
inequality, then names the shared stopped-tail bound surface that later
probability work should consume.

It does not prove a stopped strong-Markov theorem, a tail estimate, outer
`(7.54)`, Lemma 7.10, Proposition 7.8, or Tao's theorem.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

theorem taoSection7HoldListMass_append
    (pre tail : List TaoSection7RenewalPoint) :
    taoSection7HoldListMass (pre ++ tail) =
      taoSection7HoldListMass pre * taoSection7HoldListMass tail := by
  simp [taoSection7HoldListMass, List.map_append, List.prod_append]

theorem taoSection7HoldListPMF_append_toReal
    (pre tail : List TaoSection7RenewalPoint) :
    (taoSection7HoldListPMF (pre.length + tail.length)
      (pre ++ tail)).toReal =
      (taoSection7HoldListPMF pre.length pre).toReal *
        (taoSection7HoldListPMF tail.length tail).toReal := by
  have hlen : (pre ++ tail).length = pre.length + tail.length := by
    simp [List.length_append]
  rw [← hlen]
  rw [taoSection7HoldListPMF_apply_length_toReal]
  rw [taoSection7HoldListPMF_apply_length_toReal]
  rw [taoSection7HoldListPMF_apply_length_toReal]
  simp [taoSection7HoldListMass_append]

theorem taoSection7HoldListPMF_append_toReal_of_lengths
    {K p : ℕ} {pre tail : List TaoSection7RenewalPoint}
    (hpre : pre.length = K) (htail : tail.length = p) :
    (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal =
      (taoSection7HoldListPMF K pre).toReal *
        (taoSection7HoldListPMF p tail).toReal := by
  subst K
  subst p
  exact taoSection7HoldListPMF_append_toReal pre tail

theorem taoSection7HoldListPMF_append_toReal_of_prefix_length
    {K p : ℕ} {pre tail : List TaoSection7RenewalPoint}
    (hpre : pre.length = K) :
    (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal =
      (taoSection7HoldListPMF K pre).toReal *
        (taoSection7HoldListPMF p tail).toReal := by
  by_cases htail : tail.length = p
  · exact taoSection7HoldListPMF_append_toReal_of_lengths hpre htail
  · have hfull_ne : (pre ++ tail).length ≠ K + p := by
      intro hfull
      have hsum : K + tail.length = K + p := by
        simpa [List.length_append, hpre] using hfull
      exact htail (Nat.add_left_cancel hsum)
    have hleft :
        taoSection7HoldListPMF (K + p) (pre ++ tail) = 0 :=
      taoSection7HoldListPMF_apply_eq_zero_of_length_ne
        (K + p) (pre ++ tail) hfull_ne
    have hright : taoSection7HoldListPMF p tail = 0 :=
      taoSection7HoldListPMF_apply_eq_zero_of_length_ne p tail htail
    simp [hleft, hright]

/-- One-step list mass for a singleton terminal `Hold` increment. -/
theorem taoSection7HoldListPMF_singleton_toReal
    (last : TaoSection7RenewalPoint) :
    (taoSection7HoldListPMF 1 [last]).toReal =
      (taoSection7HoldPMF last).toReal := by
  simpa [taoSection7HoldListMass] using
    (taoSection7HoldListPMF_apply_length_toReal [last])

/-- Snoc form of the finite iid `Hold` list independence identity. -/
theorem taoSection7HoldListPMF_snoc_toReal
    (pre : List TaoSection7RenewalPoint) (last : TaoSection7RenewalPoint) :
    (taoSection7HoldListPMF (pre.length + 1) (pre ++ [last])).toReal =
      (taoSection7HoldListPMF pre.length pre).toReal *
        (taoSection7HoldPMF last).toReal := by
  simpa [taoSection7HoldListPMF_singleton_toReal] using
    (taoSection7HoldListPMF_append_toReal pre [last])

/-- Snoc form with an externally named prefix length. -/
theorem taoSection7HoldListPMF_snoc_toReal_of_length
    {n : ℕ} {pre : List TaoSection7RenewalPoint}
    (hpre : pre.length = n) (last : TaoSection7RenewalPoint) :
    (taoSection7HoldListPMF (n + 1) (pre ++ [last])).toReal =
      (taoSection7HoldListPMF n pre).toReal *
        (taoSection7HoldPMF last).toReal := by
  subst n
  exact taoSection7HoldListPMF_snoc_toReal pre last

/--
Finite prefix/tail cylinder algebra for fixed Hold lists.

This is a finite pair-sum inequality, not yet a stopped event probability
theorem.  A later stopped-tail theorem must still identify which stopped
prefixes are being summed and prove the relevant tail-event bound.
-/
theorem taoSection7HoldListPMF_prefixCylinderTail_finset_le
    {K p : ℕ} (S T : Finset (List TaoSection7RenewalPoint))
    (hS : ∀ pre, pre ∈ S → pre.length = K)
    (hT : ∀ tail, tail ∈ T → tail.length = p)
    {b : ℝ}
    (hTail :
      (∑ tail ∈ T, (taoSection7HoldListPMF p tail).toReal) ≤ b) :
    (∑ pre ∈ S, ∑ tail ∈ T,
        (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal)
      ≤ (∑ pre ∈ S, (taoSection7HoldListPMF K pre).toReal) * b := by
  classical
  calc
    (∑ pre ∈ S, ∑ tail ∈ T,
        (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal)
        = ∑ pre ∈ S,
            (taoSection7HoldListPMF K pre).toReal *
              ∑ tail ∈ T, (taoSection7HoldListPMF p tail).toReal := by
          refine Finset.sum_congr rfl ?_
          intro pre hpreS
          calc
            (∑ tail ∈ T,
                (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal)
                = ∑ tail ∈ T,
                    (taoSection7HoldListPMF K pre).toReal *
                      (taoSection7HoldListPMF p tail).toReal := by
                  refine Finset.sum_congr rfl ?_
                  intro tail htailT
                  exact
                    taoSection7HoldListPMF_append_toReal_of_lengths
                      (hS pre hpreS) (hT tail htailT)
            _ = (taoSection7HoldListPMF K pre).toReal *
                  ∑ tail ∈ T,
                    (taoSection7HoldListPMF p tail).toReal := by
                  rw [Finset.mul_sum]
    _ ≤ ∑ pre ∈ S, (taoSection7HoldListPMF K pre).toReal * b := by
          refine Finset.sum_le_sum ?_
          intro pre _hpreS
          exact
            mul_le_mul_of_nonneg_left hTail
              ENNReal.toReal_nonneg
    _ = (∑ pre ∈ S, (taoSection7HoldListPMF K pre).toReal) * b := by
          rw [Finset.sum_mul]

/--
Shared stopped-tail bound surface for Hold suffixes.

The event may depend on the stopped prefix, but its tail probability must be
uniformly bounded using the fixed length-`p` Hold-list law.  This is only the
consumer-facing surface; a later theorem must prove such bounds from stopped
prefix algebra and concrete tail estimates.
-/
structure TaoSection7StoppedHoldTailBound
    (p : ℕ)
    (TailBad :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel TailBad]
    (b : ℝ) : Prop where
  tail_prob_le :
    ∀ pre : List TaoSection7RenewalPoint,
      (∑' tail : List TaoSection7RenewalPoint,
        if TailBad pre tail then
          (taoSection7HoldListPMF p tail).toReal
        else 0) ≤ b

/--
Fixed-`K` stopped-prefix family for a stopped-tail slice.

This is only one prefix-length slice of the later stopped-tail law.  A
source-faithful stopped strong-Markov theorem must still aggregate across the
random first-passage length `K`.
-/
structure TaoSection7StoppedHoldPrefixFamily
    (K : ℕ) (S : Finset (List TaoSection7RenewalPoint)) : Prop where
  length_eq : ∀ pre, pre ∈ S → pre.length = K
  mass_le_one :
    (∑ pre ∈ S, (taoSection7HoldListPMF K pre).toReal) ≤ 1

/--
Fixed-`K` stopped-prefix/tail summation bridge.

Given a finite family of stopped prefixes of one fixed length `K`, and a
uniform tail bound for the bad suffix event under the length-`p` Hold-list law,
the total mass of the corresponding prefix/tail bad cylinders is bounded by
the same tail budget.  This is slice infrastructure only; it does not prove
the variable-`K` first-passage partition or the concrete tail estimate.
-/
theorem taoSection7StoppedHoldPrefixTail_tsum_le
    {K p : ℕ}
    (S : Finset (List TaoSection7RenewalPoint))
    (hS : TaoSection7StoppedHoldPrefixFamily K S)
    (TailBad :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel TailBad]
    {b : ℝ}
    (hb : 0 ≤ b)
    (hTail : TaoSection7StoppedHoldTailBound p TailBad b) :
    (∑ pre ∈ S,
      ∑' tail : List TaoSection7RenewalPoint,
        if TailBad pre tail then
          (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal
        else 0) ≤ b := by
  classical
  calc
    (∑ pre ∈ S,
      ∑' tail : List TaoSection7RenewalPoint,
        if TailBad pre tail then
          (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal
        else 0)
        ≤ ∑ pre ∈ S, (taoSection7HoldListPMF K pre).toReal * b := by
          refine Finset.sum_le_sum ?_
          intro pre hpreS
          have hpre : pre.length = K := hS.length_eq pre hpreS
          have htsum :
              (∑' tail : List TaoSection7RenewalPoint,
                if TailBad pre tail then
                  (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal
                else 0)
                =
              (taoSection7HoldListPMF K pre).toReal *
                (∑' tail : List TaoSection7RenewalPoint,
                  if TailBad pre tail then
                    (taoSection7HoldListPMF p tail).toReal
                  else 0) := by
            calc
              (∑' tail : List TaoSection7RenewalPoint,
                if TailBad pre tail then
                  (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal
                else 0)
                  =
                ∑' tail : List TaoSection7RenewalPoint,
                  (taoSection7HoldListPMF K pre).toReal *
                    (if TailBad pre tail then
                      (taoSection7HoldListPMF p tail).toReal
                    else 0) := by
                    refine tsum_congr ?_
                    intro tail
                    by_cases hbad : TailBad pre tail
                    · simp [hbad,
                        taoSection7HoldListPMF_append_toReal_of_prefix_length
                          hpre]
                    · simp [hbad]
              _ =
                (taoSection7HoldListPMF K pre).toReal *
                  (∑' tail : List TaoSection7RenewalPoint,
                    if TailBad pre tail then
                      (taoSection7HoldListPMF p tail).toReal
                    else 0) := by
                    rw [tsum_mul_left]
          calc
            (∑' tail : List TaoSection7RenewalPoint,
              if TailBad pre tail then
                (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal
              else 0)
                =
              (taoSection7HoldListPMF K pre).toReal *
                (∑' tail : List TaoSection7RenewalPoint,
                  if TailBad pre tail then
                    (taoSection7HoldListPMF p tail).toReal
                  else 0) := htsum
            _ ≤ (taoSection7HoldListPMF K pre).toReal * b := by
              exact
                mul_le_mul_of_nonneg_left
                  (hTail.tail_prob_le pre)
                  ENNReal.toReal_nonneg
    _ = (∑ pre ∈ S, (taoSection7HoldListPMF K pre).toReal) * b := by
          rw [Finset.sum_mul]
    _ ≤ 1 * b := by
          exact mul_le_mul_of_nonneg_right hS.mass_le_one hb
    _ = b := by ring

/--
Finite variable-prefix family for stopped-tail aggregation.

The `PrefixOK` field is the socket for a later first-passage/source
certificate on each `(K, pre)` pair.  This record only supplies the algebraic
data needed by the generic summation theorem below: the prefix length and a
direct total-mass bound for the family.
-/
structure TaoSection7StoppedHoldVariablePrefixFamily
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint)) : Prop where
  prefix_ok : ∀ item, item ∈ S → PrefixOK item
  length_eq : ∀ item, item ∈ S → item.2.length = item.1
  mass_le_one :
    (∑ item ∈ S, (taoSection7HoldListPMF item.1 item.2).toReal) ≤ 1

/--
Finite variable-`K` prefix/tail mass-aggregation bridge.

This lifts the fixed-`K` slice algebra to a finite family of stopped-prefix
pairs `(K, pre)` with a supplied total-mass bound.  It is still not the
stopped strong-Markov law: later work must instantiate `PrefixOK` with actual
first-passage/source certificates and prove coverage or disjointness for the
source event being bounded.
-/
theorem taoSection7StoppedHoldVariablePrefixTail_tsum_le
    {p : ℕ}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (hS : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S)
    (TailBad :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel TailBad]
    {b : ℝ}
    (hb : 0 ≤ b)
    (hTail : TaoSection7StoppedHoldTailBound p TailBad b) :
    (∑ item ∈ S,
      ∑' tail : List TaoSection7RenewalPoint,
        if TailBad item.2 tail then
          (taoSection7HoldListPMF (item.1 + p) (item.2 ++ tail)).toReal
        else 0) ≤ b := by
  classical
  calc
    (∑ item ∈ S,
      ∑' tail : List TaoSection7RenewalPoint,
        if TailBad item.2 tail then
          (taoSection7HoldListPMF (item.1 + p) (item.2 ++ tail)).toReal
        else 0)
        ≤ ∑ item ∈ S,
            (taoSection7HoldListPMF item.1 item.2).toReal * b := by
          refine Finset.sum_le_sum ?_
          intro item hitemS
          have hpre : item.2.length = item.1 := hS.length_eq item hitemS
          have htsum :
              (∑' tail : List TaoSection7RenewalPoint,
                if TailBad item.2 tail then
                  (taoSection7HoldListPMF
                    (item.1 + p) (item.2 ++ tail)).toReal
                else 0)
                =
              (taoSection7HoldListPMF item.1 item.2).toReal *
                (∑' tail : List TaoSection7RenewalPoint,
                  if TailBad item.2 tail then
                    (taoSection7HoldListPMF p tail).toReal
                  else 0) := by
            calc
              (∑' tail : List TaoSection7RenewalPoint,
                if TailBad item.2 tail then
                  (taoSection7HoldListPMF
                    (item.1 + p) (item.2 ++ tail)).toReal
                else 0)
                  =
                ∑' tail : List TaoSection7RenewalPoint,
                  (taoSection7HoldListPMF item.1 item.2).toReal *
                    (if TailBad item.2 tail then
                      (taoSection7HoldListPMF p tail).toReal
                    else 0) := by
                    refine tsum_congr ?_
                    intro tail
                    by_cases hbad : TailBad item.2 tail
                    · simp [hbad,
                        taoSection7HoldListPMF_append_toReal_of_prefix_length
                          hpre]
                    · simp [hbad]
              _ =
                (taoSection7HoldListPMF item.1 item.2).toReal *
                  (∑' tail : List TaoSection7RenewalPoint,
                    if TailBad item.2 tail then
                      (taoSection7HoldListPMF p tail).toReal
                    else 0) := by
                    rw [tsum_mul_left]
          calc
            (∑' tail : List TaoSection7RenewalPoint,
              if TailBad item.2 tail then
                (taoSection7HoldListPMF
                  (item.1 + p) (item.2 ++ tail)).toReal
              else 0)
                =
              (taoSection7HoldListPMF item.1 item.2).toReal *
                (∑' tail : List TaoSection7RenewalPoint,
                  if TailBad item.2 tail then
                    (taoSection7HoldListPMF p tail).toReal
                  else 0) := htsum
            _ ≤ (taoSection7HoldListPMF item.1 item.2).toReal * b := by
              exact
                mul_le_mul_of_nonneg_left
                  (hTail.tail_prob_le item.2)
                  ENNReal.toReal_nonneg
    _ = (∑ item ∈ S,
          (taoSection7HoldListPMF item.1 item.2).toReal) * b := by
          rw [Finset.sum_mul]
    _ ≤ 1 * b := by
          exact mul_le_mul_of_nonneg_right hS.mass_le_one hb
    _ = b := by ring

/--
Outer `(7.54)` stopped-tail input for the large-horizontal suffix event.

The first-passage high-`j` tail and the bad-event expectation contribution are
separate fields for the later outer `(7.54)` socket, not part of this shared
tail-bound surface.
-/
structure TaoSection7Case3Outer754StoppedTailInput
    (P : ℕ)
    (OuterBadJTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel OuterBadJTail]
    (bJ : ℝ) : Prop where
  tail_bound :
    TaoSection7StoppedHoldTailBound P OuterBadJTail bJ

/--
Lemma 7.10 stopped-tail inputs for the post-`k` vertical and horizontal pieces
of the exceptional event `E'`.

First-passage `(7.48)` bounds, scale absorption, and the downstream
lower-tip/kernel geometry remain separate later sockets.
-/
structure TaoSection7Lemma710EprimeStoppedTailInput
    (p : ℕ)
    (Lemma710VerticalTail Lemma710HorizontalTail :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel Lemma710VerticalTail]
    [DecidableRel Lemma710HorizontalTail]
    (bL bJ : ℝ) : Prop where
  vertical_tail :
    TaoSection7StoppedHoldTailBound p Lemma710VerticalTail bL
  horizontal_tail :
    TaoSection7StoppedHoldTailBound p Lemma710HorizontalTail bJ

end Tao
end Erdos1135SecondScale
