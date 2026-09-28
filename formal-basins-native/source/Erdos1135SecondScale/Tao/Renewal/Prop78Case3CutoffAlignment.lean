/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Prop78Case3Event
import Erdos1135SecondScale.Tao.Renewal.GeometryBridge
import Erdos1135SecondScale.Tao.Renewal.SourceActualQ

/-!
# Section 7 Case 3 Cutoff Alignment Support

This module records the checked alignment layer that keeps the local
low-window predicate `W : Nat -> Prop` tied to Tao's source cutoff-white
predicate before source-facing Case 3 consumers use it.

It is support-only.  It transfers finite low-window counts and raw-white facts
under explicit full-window alignment hypotheses.  It does not produce the
alignment, source-path data, source `(7.11)`, source `r`/`t_R`, Lemma 7.9,
Lemma 7.10, Tao's many-whites inequality, `(7.41)`, Proposition 7.8,
Proposition 7.3/7.1, or Tao's theorem.
-/

namespace Erdos1135SecondScale
namespace Tao

open Finset

/-- The point-indexed cutoff-white predicate used by the Case 3 low window. -/
def taoSection7Case3SourceCutoffPointW
    (pointAt : ℕ → TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ) (p : ℕ) : Prop :=
  taoSection7SourcePointInDomain J (pointAt p) ∧
    taoSection7SourceWhitePoint n xi epsilon (pointAt p)

/-- Finite low-window counts are invariant under pointwise equivalence on `range P`. -/
theorem taoSection7Case3WindowWhiteCount_congr_range
    (W W' : ℕ → Prop) [DecidablePred W] [DecidablePred W']
    {P : ℕ}
    (halign : ∀ p : ℕ, p < P → (W p ↔ W' p)) :
    taoSection7Case3WindowWhiteCount W P =
      taoSection7Case3WindowWhiteCount W' P := by
  unfold taoSection7Case3WindowWhiteCount
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp_lt : p < P := Finset.mem_range.mp hp
  by_cases hW : W p
  · have hW' : W' p := (halign p hp_lt).mp hW
    simp [hW, hW']
  · have hW' : ¬ W' p := by
      intro h'
      exact hW ((halign p hp_lt).mpr h')
    simp [hW, hW']

/--
Transfer a low-window bound from the source cutoff predicate to an arbitrary
local predicate once they agree on the full `P` window.
-/
theorem taoSection7Case3WindowWhiteCount_le_of_sourceCutoffPoint_alignment
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J P threshold : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred (taoSection7Case3SourceCutoffPointW pointAt n xi epsilon J)]
    (halign :
      ∀ p : ℕ, p < P →
        (W p ↔ taoSection7Case3SourceCutoffPointW pointAt n xi epsilon J p))
    (hcutoff :
      taoSection7Case3WindowWhiteCount
        (taoSection7Case3SourceCutoffPointW pointAt n xi epsilon J) P ≤
          threshold) :
    taoSection7Case3WindowWhiteCount W P ≤ threshold := by
  have hcount :=
    taoSection7Case3WindowWhiteCount_congr_range
      W (taoSection7Case3SourceCutoffPointW pointAt n xi epsilon J) halign
  simpa [hcount] using hcutoff

/--
The same transfer specialized to Tao's source actual cutoff predicate
`J = n / 2`.
-/
theorem taoSection7Case3WindowWhiteCount_le_of_sourceActualPoint_alignment
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n P threshold : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (taoSection7Case3SourceCutoffPointW pointAt n xi epsilon (n / 2))]
    (halign :
      ∀ p : ℕ, p < P →
        (W p ↔
          taoSection7Case3SourceCutoffPointW pointAt n xi epsilon (n / 2) p))
    (hcutoff :
      taoSection7Case3WindowWhiteCount
        (taoSection7Case3SourceCutoffPointW pointAt n xi epsilon (n / 2)) P ≤
          threshold) :
    taoSection7Case3WindowWhiteCount W P ≤ threshold :=
  taoSection7Case3WindowWhiteCount_le_of_sourceCutoffPoint_alignment
    W pointAt halign hcutoff

/--
Full-window cutoff alignment and domain data provide the raw source-white
equivalence required by the existing later-black source-path consumer.
-/
theorem taoSection7Case3_rawWhite_iff_of_sourceCutoffPoint_alignment
    (W : ℕ → Prop)
    (pointAt : ℕ → TaoSection7Point)
    {n J P candidate : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (halign :
      ∀ p : ℕ, p < P →
        (W p ↔ taoSection7Case3SourceCutoffPointW pointAt n xi epsilon J p))
    (hcandidate : candidate < P)
    (hdomain : taoSection7SourcePointInDomain J (pointAt candidate)) :
    (W candidate ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt candidate)) := by
  constructor
  · intro hW
    exact ((halign candidate hcandidate).mp hW).2
  · intro hwhite
    exact (halign candidate hcandidate).mpr ⟨hdomain, hwhite⟩

/--
The renewal source-actual predicate agrees with the point-indexed cutoff
predicate after applying `toPoint`.
-/
theorem taoSection7Case3_sourceActualW_iff_sourceCutoffPointW_toPoint
    (renewalAt : ℕ → TaoSection7RenewalPoint)
    {n p : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ} :
    taoSection7SourceActualW n xi epsilon (renewalAt p) ↔
      taoSection7Case3SourceCutoffPointW
        (fun q => (renewalAt q).toPoint) n xi epsilon (n / 2) p := by
  simpa [taoSection7SourceActualW, taoSection7Case3SourceCutoffPointW] using
    (taoSection7SourceWhiteRenewal_cutoff_iff_toPoint
      (n := n) (J := n / 2) (xi := xi) (epsilon := epsilon)
      (p := renewalAt p))

end Tao
end Erdos1135SecondScale
