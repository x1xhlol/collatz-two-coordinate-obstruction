/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.HoldFirstPassagePMF
import Erdos1135SecondScale.Tao.Renewal.Lemma77PotentialCore
import Mathlib.Tactic

/-!
# Canonical First-Passage Endpoint Law

This module maps the p-free stopped-prefix law to its relative horizontal and
vertical endpoint.  It keeps the countable PMF in native `ENNReal`; the
terminal-coordinate reindex is developed below this surface.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Lemma77

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

/-- Relative endpoint of a concrete stopped prefix. -/
def lemma77EndpointOfPrefix
    (start : TaoSection7RenewalPoint)
    (pre : List TaoSection7RenewalPoint) : ℕ × ℤ :=
  (lemma77HoldPrefixIncrement start pre.length pre,
    lemma77HoldPrefixVerticalIncrement start pre.length pre)

/-- Translate a relative first-passage endpoint back to the absolute renewal
point based at `start`. -/
def lemma77RenewalPointOfRelativeEndpoint
    (start : TaoSection7RenewalPoint) (x : ℕ × ℤ) :
    TaoSection7RenewalPoint :=
  { j := taoSection7ShiftIndex start.j x.1
    l := start.l + x.2 }

@[simp] theorem lemma77RenewalPointOfRelativeEndpoint_j
    (start : TaoSection7RenewalPoint) (x : ℕ × ℤ) :
    ((lemma77RenewalPointOfRelativeEndpoint start x).j : ℕ) =
      (start.j : ℕ) + x.1 := by
  rfl

@[simp] theorem lemma77RenewalPointOfRelativeEndpoint_l
    (start : TaoSection7RenewalPoint) (x : ℕ × ℤ) :
    (lemma77RenewalPointOfRelativeEndpoint start x).l =
      start.l + x.2 := by
  rfl

/-- Translating the checked relative endpoint of a concrete prefix recovers
the actual renewal path endpoint. -/
theorem lemma77RenewalPointOfRelativeEndpoint_endpointOfPrefix
    (start : TaoSection7RenewalPoint)
    (pre : List TaoSection7RenewalPoint) :
    lemma77RenewalPointOfRelativeEndpoint start
        (lemma77EndpointOfPrefix start pre) =
      taoSection7RenewalPathPoint start pre pre.length := by
  ext
  · apply PNat.eq
    simp only [lemma77RenewalPointOfRelativeEndpoint_j, lemma77EndpointOfPrefix]
    rw [lemma77HoldPrefixIncrement_eq_horizontalDelta,
      lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta]
  · simp only [lemma77RenewalPointOfRelativeEndpoint_l, lemma77EndpointOfPrefix]
    simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement]

/-- Canonical p-free first-passage endpoint distribution. -/
noncomputable def lemma77CanonicalFirstPassageEndpointPMF
    (start : TaoSection7RenewalPoint) (s : ℕ) : PMF (ℕ × ℤ) :=
  (lemma77CanonicalFirstPassagePrefixPMF start s).map
    (lemma77EndpointOfPrefix start)

/-- A mapped PMF atom is the native `ENNReal` sum over its exact source fiber. -/
theorem pmf_map_apply_eq_tsum_fiber
    {α β : Type*} (p : PMF α) (f : α → β) (b : β) :
    (p.map f) b = ∑' a : {a : α // f a = b}, p a := by
  classical
  rw [PMF.map_apply]
  symm
  calc
    (∑' a : {a : α // f a = b}, p a) =
        ∑' a : {a : α // f a = b}, if b = f a then p a else 0 := by
      apply tsum_congr
      intro a
      rw [if_pos a.property.symm]
    _ = ∑' a : α, if b = f a then p a else 0 := by
      have hsupp :
          Function.support (fun a : α => if b = f a then p a else 0) ⊆
            {a : α | f a = b} := by
        intro a ha
        by_contra h
        have hb : b ≠ f a := fun hba => h hba.symm
        simp [hb] at ha
      exact tsum_subtype_eq_of_support_subset
        (f := fun a : α => if b = f a then p a else 0)
        (s := {a : α | f a = b}) hsupp

/-- Exact endpoint-fiber expansion of the canonical endpoint atom. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_apply_eq_tsum_fiber
    (start : TaoSection7RenewalPoint) (s r : ℕ) (ell : ℤ) :
    lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) =
      ∑' pre : {pre : List TaoSection7RenewalPoint //
          lemma77EndpointOfPrefix start pre = (r, ell)},
        lemma77CanonicalFirstPassagePrefixPMF start s pre.1 := by
  exact pmf_map_apply_eq_tsum_fiber
    (lemma77CanonicalFirstPassagePrefixPMF start s)
    (lemma77EndpointOfPrefix start) (r, ell)

/-- Exact endpoint prefixes restricted to nonzero canonical source atoms. -/
def Lemma77CanonicalEndpointSupportFiber
    (start : TaoSection7RenewalPoint) (s r : ℕ) (ell : ℤ) :=
  {pre : {pre : List TaoSection7RenewalPoint //
      lemma77EndpointOfPrefix start pre = (r, ell)} //
    lemma77CanonicalFirstPassagePrefixPMF start s pre.1 ≠ 0}

/-- The endpoint atom may be summed over only its nonzero source prefixes. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_apply_eq_tsum_supportFiber
    (start : TaoSection7RenewalPoint) (s r : ℕ) (ell : ℤ) :
    lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) =
      ∑' pre : Lemma77CanonicalEndpointSupportFiber start s r ell,
        lemma77CanonicalFirstPassagePrefixPMF start s pre.1.1 := by
  rw [lemma77CanonicalFirstPassageEndpointPMF_apply_eq_tsum_fiber]
  let f : {pre : List TaoSection7RenewalPoint //
      lemma77EndpointOfPrefix start pre = (r, ell)} → ENNReal :=
    fun pre => lemma77CanonicalFirstPassagePrefixPMF start s pre.1
  have hsupp : Function.support f ⊆ {pre | f pre ≠ 0} := by
    intro pre hpre
    exact hpre
  exact (tsum_subtype_eq_of_support_subset
    (f := f) (s := {pre | f pre ≠ 0}) hsupp).symm

/-- Every nonzero canonical endpoint atom has positive horizontal displacement
and lies strictly above the first-passage threshold. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_nonzero_support
    {start : TaoSection7RenewalPoint} {s r : ℕ} {ell : ℤ}
    (hne : lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) ≠ 0) :
    0 < r ∧ (s : ℤ) < ell := by
  classical
  have hmem :
      (r, ell) ∈ (lemma77CanonicalFirstPassageEndpointPMF start s).support := hne
  unfold lemma77CanonicalFirstPassageEndpointPMF at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨pre, hpre, hendpoint⟩
  have hfirst := lemma77CanonicalFirstPassagePrefixPMF_nonzero_certifies hpre
  have hr : lemma77HoldPrefixIncrement start pre.length pre = r := by
    simpa [lemma77EndpointOfPrefix] using congrArg Prod.fst hendpoint
  have hell : lemma77HoldPrefixVerticalIncrement start pre.length pre = ell := by
    simpa [lemma77EndpointOfPrefix] using congrArg Prod.snd hendpoint
  constructor
  · rw [← hr, lemma77HoldPrefixIncrement_eq_horizontalDelta]
    exact lt_of_lt_of_le hfirst.1.K_pos
      (lemma77HoldPrefixHorizontalDelta_ge_steps (by rfl))
  · have hcross := hfirst.1.crosses
    dsimp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement] at hell
    omega

/-- Unsupported endpoint coordinates have zero canonical mass. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_apply_eq_zero_of_invalid
    {start : TaoSection7RenewalPoint} {s r : ℕ} {ell : ℤ}
    (hinvalid : ¬(0 < r ∧ (s : ℤ) < ell)) :
    lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) = 0 := by
  by_contra hne
  exact hinvalid (lemma77CanonicalFirstPassageEndpointPMF_nonzero_support hne)

end TaoSection7Lemma77

end

end Tao
end Erdos1135SecondScale
