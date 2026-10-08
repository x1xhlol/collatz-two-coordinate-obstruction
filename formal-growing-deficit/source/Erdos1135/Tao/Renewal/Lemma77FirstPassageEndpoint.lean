import Erdos1135.Tao.Renewal.Lemma77HorizontalMarginal
import Erdos1135.Tao.Renewal.HoldStoppedTail

/-!
# Lemma 7.7 Pointwise First-Passage Endpoint Surface

This module names the red endpoint-law gate below the Lemma 7.7 horizontal
marginal summation.  It records the source/provenance facts and the pointwise
kernel shape that a future proof of Tao's Lemma 7.7 must provide.

It does not prove Lemma 7.7, Lemma 7.6, Lemma 2.2, the iid Hold stopped-prefix
law, endpoint-fiber probability estimates, vertical summation, `BadPre`, outer
`(7.54)`, Proposition 7.8, or Tao's theorem.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Lemma77

/-- Horizontal displacement from Tao's Lemma 7.7 center `s / 4`. -/
def lemma77CenteredHorizontalDisplacement (s r : ℕ) : ℝ :=
  (r : ℝ) - (s : ℝ) / 4

/--
Pointwise endpoint kernel shape for the Lemma 7.7 first-passage law.

The horizontal factor is centered at `s / 4`; the vertical factor is evaluated
at the shifted overshoot `ell - s`, supplied by `relativeVerticalOvershoot`.
This is a target kernel vocabulary, not an analytic estimate.
-/
def lemma77PointwiseEndpointKernel
    (A B C D : ℝ) (s r : ℕ) (overshoot : ℤ) : ℝ :=
  C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
    (Real.exp
        (-A * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
          (1 + (s : ℝ)))) +
      Real.exp (-B * |lemma77CenteredHorizontalDisplacement s r|)) *
    Real.exp (-D * (overshoot : ℝ))

/--
Source/provenance surface for the pointwise Lemma 7.7 endpoint law.

The first field is the stopped-prefix first-passage certificate already used
by the positive-overshoot support bridge.  The second field is a concrete
stopped-prefix source-law socket against finite iid `Hold` lists; it is kept
separate from the endpoint probability estimate so the analytic red gate is
not hidden as an opaque `hfiber` premise.
-/
structure Lemma77EndpointSourceProvenance
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s : ℕ) : Prop where
  first_passage :
    ∀ ω,
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        (start ω) s (K ω) (pre ω)
  stopped_prefix_mass_le_hold :
    ∀ n hs,
      pmfProb μ {ω | K ω = n ∧ pre ω = hs} ≤
        (taoSection7HoldListPMF n hs).toReal

/--
Residual-aware source/provenance surface on a good event.

This is the finite/truncated companion to `Lemma77EndpointSourceProvenance`:
first-passage and stopped-pair atom bounds are required only on `good`, leaving
the complement as an explicit residual for downstream additive-bad endpoints.
-/
structure Lemma77EndpointSourceProvenanceOnGood
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s : ℕ)
    (good : Set Ω) : Prop where
  first_passage_good :
    ∀ ω,
      ω ∈ good →
        TaoSection7Lemma710.VerticalFirstPassagePrefix
          (start ω) s (K ω) (pre ω)
  stopped_prefix_mass_le_hold_good :
    ∀ n hs,
      pmfProb μ {ω | ω ∈ good ∧ K ω = n ∧ pre ω = hs} ≤
        (taoSection7HoldListPMF n hs).toReal

/--
Constant-origin constructor for the endpoint source/provenance socket.

This isolates the genuine source-law obligation as the stopped-prefix
per-cylinder mass bound; downstream endpoint wrappers can then discharge their
global origin-alignment premise by reflexivity.
-/
theorem lemma77EndpointSourceProvenance_constOrigin_of_firstPassage_cylinderMass
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {origin : TaoSection7RenewalPoint}
    {K : Ω → ℕ} {pre : Ω → List TaoSection7RenewalPoint} {s : ℕ}
    (hfirst :
      ∀ ω,
        TaoSection7Lemma710.VerticalFirstPassagePrefix
          origin s (K ω) (pre ω))
    (hmass :
      ∀ n hs,
        pmfProb μ {ω | K ω = n ∧ pre ω = hs} ≤
          (taoSection7HoldListPMF n hs).toReal) :
    Lemma77EndpointSourceProvenance μ (fun _ => origin) K pre s where
  first_passage := by
    intro ω
    exact hfirst ω
  stopped_prefix_mass_le_hold := hmass

/-- Exact endpoint source/provenance restricts to any good event. -/
theorem lemma77EndpointSourceProvenanceOnGood_of_exact
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ} {pre : Ω → List TaoSection7RenewalPoint}
    {s : ℕ}
    (good : Set Ω)
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s) :
    Lemma77EndpointSourceProvenanceOnGood μ start K pre s good where
  first_passage_good := by
    intro ω _hgood
    exact hsrc.first_passage ω
  stopped_prefix_mass_le_hold_good := by
    intro n hs
    calc
      pmfProb μ {ω | ω ∈ good ∧ K ω = n ∧ pre ω = hs} ≤
          pmfProb μ {ω | K ω = n ∧ pre ω = hs} :=
        pmfProb_mono μ (by
          intro ω hω
          exact ⟨hω.2.1, hω.2.2⟩)
      _ ≤ (taoSection7HoldListPMF n hs).toReal :=
        hsrc.stopped_prefix_mass_le_hold n hs

/--
Finite event probability as a pushed-forward singleton atom.

Unlike `pmfProb_map_preimage`, this does not require the target type to be
finite; it only sums over the finite source carrier.
-/
theorem pmfProb_singleton_eq_map_apply_toReal
    {Ω β : Type*} [Fintype Ω]
    (μ : PMF Ω) (f : Ω → β) (b : β) :
    pmfProb μ {ω | f ω = b} = ((μ.map f) b).toReal := by
  classical
  rw [pmfProb, PMF.map_apply]
  rw [ENNReal.tsum_toReal_eq]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro ω _hω
    have hiff : (ω ∈ {ω | f ω = b}) ↔ b = f ω := by
      constructor
      · intro h
        exact h.symm
      · intro h
        exact h.symm
    by_cases hb : b = f ω
    · rw [ite_eq_left (hiff.mpr hb), ite_eq_left hb]
    · rw [ite_eq_right (fun hmem => hb (hiff.mp hmem)), ite_eq_right hb]
      rfl
  · intro ω
    by_cases hb : b = f ω <;>
      simp [hb, PMF.apply_ne_top μ ω]

/--
Stopped-prefix pair event probability as the atom of the pushed-forward
`(K, pre)` law.

This keeps the source-law canary local to Lemma 7.7: future producers can prove
pointwise bounds on `μ.map (fun ω => (K ω, pre ω))` without unfolding the
finite event `{ω | K ω = n ∧ pre ω = hs}` at every endpoint consumer.
-/
theorem pmfProb_stoppedPrefixPair_eq_map_apply_toReal
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (n : ℕ) (hs : List TaoSection7RenewalPoint) :
    pmfProb μ {ω | K ω = n ∧ pre ω = hs} =
      ((μ.map fun ω => (K ω, pre ω)) (n, hs)).toReal := by
  classical
  rw [pmfProb, PMF.map_apply]
  rw [ENNReal.tsum_toReal_eq]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro ω _hω
    have hiff :
        (ω ∈ {ω | K ω = n ∧ pre ω = hs}) ↔
          (n, hs) = (K ω, pre ω) := by
      constructor
      · intro h
        exact Prod.ext h.1.symm h.2.symm
      · intro h
        exact ⟨(Prod.ext_iff.mp h).1.symm, (Prod.ext_iff.mp h).2.symm⟩
    by_cases hpair : (n, hs) = (K ω, pre ω)
    · rw [ite_eq_left (hiff.mpr hpair), ite_eq_left hpair]
    · rw [ite_eq_right (fun hmem => hpair (hiff.mp hmem)), ite_eq_right hpair]
      rfl
  · intro ω
    by_cases hpair : (n, hs) = (K ω, pre ω) <;>
      simp [hpair, PMF.apply_ne_top μ ω]

/--
Mapped stopped-prefix atom bound from raw prefix-cylinder mass.

This is a source-law canary: if the stopped prefix is samplewise the `K`-prefix
of a full iid `Hold` list, and ordinary fixed-prefix cylinders are dominated by
the iid `Hold` prefix law, then the pushed-forward stopped-prefix law has the
atom bound required by `Lemma77EndpointSourceProvenance`.
-/
theorem lemma77StoppedPrefixPair_map_mass_le_of_take_prefixCylinderMass
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {full : Ω → List TaoSection7RenewalPoint}
    {K : Ω → ℕ} {pre : Ω → List TaoSection7RenewalPoint}
    (hpre_take : ∀ ω, pre ω = (full ω).take (K ω))
    (hprefix_mass :
      ∀ n hs,
        pmfProb μ {ω | (full ω).take n = hs} ≤
          (taoSection7HoldListPMF n hs).toReal) :
    ∀ n hs,
      ((μ.map fun ω => (K ω, pre ω)) (n, hs)).toReal ≤
        (taoSection7HoldListPMF n hs).toReal := by
  intro n hs
  rw [← pmfProb_stoppedPrefixPair_eq_map_apply_toReal μ K pre n hs]
  exact le_trans
    (pmfProb_mono μ (by
      intro ω hω
      have htake : (full ω).take (K ω) = hs := by
        calc
          (full ω).take (K ω) = pre ω := (hpre_take ω).symm
          _ = hs := hω.2
      simpa [hω.1] using htake))
    (hprefix_mass n hs)

/--
Raw prefix-cylinder mass from a finite full-`Hold`-list law.

This is pure finite-horizon source-law plumbing: if the decoded full list has
law `taoSection7HoldListPMF (K + L)`, then its `K`-prefix cylinder has exactly
the length-`K` iid `Hold` list mass.
-/
theorem lemma77HoldList_prefixCylinderMass_eq_of_fullHoldListLaw
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {full : Ω → List TaoSection7RenewalPoint}
    {K L : ℕ}
    (hfull_law : μ.map full = taoSection7HoldListPMF (K + L))
    (hs : List TaoSection7RenewalPoint) :
    pmfProb μ {ω | (full ω).take K = hs} =
      (taoSection7HoldListPMF K hs).toReal := by
  rw [pmfProb_singleton_eq_map_apply_toReal]
  change ((μ.map
      ((fun xs : List TaoSection7RenewalPoint => xs.take K) ∘ full)) hs).toReal =
    (taoSection7HoldListPMF K hs).toReal
  rw [← PMF.map_comp]
  rw [hfull_law, taoSection7HoldListPMF_map_take_eq]

/--
Guarded raw prefix-cylinder bound from a finite full-`Hold`-list law.

This is the immediate fixed-horizon producer for the guarded source adapter:
the support guard may be kept in the event without changing the upper bound.
-/
theorem lemma77HoldList_prefixCylinderMass_onSupport_le_of_fullHoldListLaw
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {full : Ω → List TaoSection7RenewalPoint}
    {K L : ℕ}
    (hfull_law : μ.map full = taoSection7HoldListPMF (K + L))
    (hs : List TaoSection7RenewalPoint) :
    pmfProb μ {ω | (full ω).take K = hs ∧ K ≤ (full ω).length} ≤
      (taoSection7HoldListPMF K hs).toReal := by
  calc
    pmfProb μ {ω | (full ω).take K = hs ∧ K ≤ (full ω).length}
        ≤ pmfProb μ {ω | (full ω).take K = hs} :=
      pmfProb_mono μ (by intro ω hω; exact hω.1)
    _ = (taoSection7HoldListPMF K hs).toReal :=
      lemma77HoldList_prefixCylinderMass_eq_of_fullHoldListLaw
        (μ := μ) (full := full) (K := K) (L := L) hfull_law hs

/--
All-prefix guarded raw cylinder bound from a fixed full-`Hold`-list law.

The guarded endpoint-source constructor asks for every requested prefix length.
For a fixed horizon `N`, the `n <= N` branch uses the finite iid prefix
marginal, while the `N < n` branch is empty under the deterministic full-list
length hypothesis.
-/
theorem lemma77HoldList_prefixCylinderMass_onSupport_all_le_of_fullHoldListLaw
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {full : Ω → List TaoSection7RenewalPoint} {N : ℕ}
    (hfull_law : μ.map full = taoSection7HoldListPMF N)
    (hfull_len : ∀ ω, (full ω).length = N) :
    ∀ n hs,
      pmfProb μ {ω | (full ω).take n = hs ∧ n ≤ (full ω).length} ≤
        (taoSection7HoldListPMF n hs).toReal := by
  intro n hs
  by_cases hn : n ≤ N
  · have hfull_law' : μ.map full = taoSection7HoldListPMF (n + (N - n)) := by
      simpa [Nat.add_sub_of_le hn] using hfull_law
    exact lemma77HoldList_prefixCylinderMass_onSupport_le_of_fullHoldListLaw
      (μ := μ) (full := full) (K := n) (L := N - n) hfull_law' hs
  · let targetEvent : Set Ω :=
      {ω | (full ω).take n = hs ∧ n ≤ (full ω).length}
    have hempty : targetEvent = ∅ := by
      ext ω
      constructor
      · intro hω
        have hnN : n ≤ N := by
          simpa [targetEvent, hfull_len ω] using hω.2
        exact (hn hnN).elim
      · intro hω
        cases hω
    have hzero : pmfProb μ targetEvent = 0 := by
      rw [hempty, pmfProb_empty]
    calc
      pmfProb μ targetEvent = 0 := hzero
      _ ≤ (taoSection7HoldListPMF n hs).toReal := ENNReal.toReal_nonneg

/--
Transport guarded raw prefix-cylinder mass from a finite source carrier.

This is still only source-law plumbing: the source carrier must supply the
guarded prefix-cylinder bound after decoding by `sampleOf`.
-/
theorem lemma77_takePrefixCylinderMass_of_sourceCarrier
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {full : Ω → List TaoSection7RenewalPoint}
    (hμ : μ = ν.map sampleOf)
    (hsource :
      ∀ n hs,
        pmfProb ν {σ |
          (full (sampleOf σ)).take n = hs ∧
            n ≤ (full (sampleOf σ)).length} ≤
          (taoSection7HoldListPMF n hs).toReal) :
    ∀ n hs,
      pmfProb μ {ω | (full ω).take n = hs ∧ n ≤ (full ω).length} ≤
        (taoSection7HoldListPMF n hs).toReal := by
  intro n hs
  let targetEvent : Set Ω :=
    {ω | (full ω).take n = hs ∧ n ≤ (full ω).length}
  calc
    pmfProb μ targetEvent = pmfProb (ν.map sampleOf) targetEvent := by
      rw [hμ]
    _ = pmfProb ν (sampleOf ⁻¹' targetEvent) :=
      pmfProb_map_preimage ν sampleOf targetEvent
    _ ≤ (taoSection7HoldListPMF n hs).toReal := by
      simpa [targetEvent] using hsource n hs

/--
Finite-carrier guarded prefix mass from domination by the ideal source-prefix
pair carrier.

The finite carrier still must provide `hdom`; this theorem only converts that
domination into the guarded `hprefix_mass` shape used by the Lemma 7.7 source
socket.  For full horizon `N > 0`, such domination by the untruncated ideal
law is generally too strong for an actual finite source carrier; use this as
plumbing for an explicitly supplied domination law, not as the next source-law
producer.
-/
theorem lemma77_finiteCarrier_guardedPrefixMass_of_sourcePrefixAtomDom
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {srcFull : Ω → List (ℕ × List ℕ)} {N : ℕ}
    (hlen : ∀ ω, (srcFull ω).length = N)
    (hdom :
      ∀ n hs,
        n ≤ N →
          pmfProb μ {ω |
            ((srcFull ω).map
              (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).take n = hs} ≤
            (((taoSection7HoldSourcePrefixListPMF N).map
              (fun xs =>
                (xs.map
                  (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).take n)) hs).toReal) :
    ∀ n hs,
      pmfProb μ {ω |
        ((srcFull ω).map
          (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).take n = hs ∧
          n ≤ ((srcFull ω).map
            (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).length} ≤
        (taoSection7HoldListPMF n hs).toReal := by
  intro n hs
  by_cases hn : n ≤ N
  · calc
      pmfProb μ {ω |
          ((srcFull ω).map
            (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).take n = hs ∧
            n ≤ ((srcFull ω).map
              (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).length}
          ≤ pmfProb μ {ω |
              ((srcFull ω).map
                (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).take n = hs} :=
        pmfProb_mono μ (by intro ω hω; exact hω.1)
      _ ≤ (((taoSection7HoldSourcePrefixListPMF N).map
              (fun xs =>
                (xs.map
                  (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).take n)) hs).toReal :=
        hdom n hs hn
      _ = (taoSection7HoldListPMF n hs).toReal := by
        rw [taoSection7HoldSourcePrefixListPMF_map_take_holdPoint_eq_of_le hn]
  · let targetEvent : Set Ω :=
      {ω |
        ((srcFull ω).map
          (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).take n = hs ∧
          n ≤ ((srcFull ω).map
            (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).length}
    have hempty : targetEvent = ∅ := by
      ext ω
      constructor
      · intro hω
        have hnN : n ≤ N := by
          have hlen_map :
              ((srcFull ω).map
                (fun x => taoSection7HoldPointOfPrefix x.1 x.2)).length = N := by
            simp [hlen ω]
          simpa [targetEvent, hlen_map] using hω.2
        exact (hn hnN).elim
      · intro hω
        cases hω
    have hzero : pmfProb μ targetEvent = 0 := by
      rw [hempty, pmfProb_empty]
    calc
      pmfProb μ targetEvent = 0 := hzero
      _ ≤ (taoSection7HoldListPMF n hs).toReal := ENNReal.toReal_nonneg

/--
Guarded mapped stopped-prefix atom bound from raw prefix-cylinder mass.

Compared with
`lemma77StoppedPrefixPair_map_mass_le_of_take_prefixCylinderMass`, this version
keeps the finite-horizon support fact `K ω ≤ (full ω).length` explicit.  That
is the shape needed by finite source carriers whose prefix law is proved only
on the support where the requested prefix length exists.
-/
theorem lemma77StoppedPrefixPair_map_mass_le_of_take_prefixCylinderMass_onSupport
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {full : Ω → List TaoSection7RenewalPoint}
    {K : Ω → ℕ} {pre : Ω → List TaoSection7RenewalPoint}
    (hpre_take : ∀ ω, pre ω = (full ω).take (K ω))
    (hK_le : ∀ ω, K ω ≤ (full ω).length)
    (hprefix_mass :
      ∀ n hs,
        pmfProb μ {ω | (full ω).take n = hs ∧ n ≤ (full ω).length} ≤
          (taoSection7HoldListPMF n hs).toReal) :
    ∀ n hs,
      ((μ.map fun ω => (K ω, pre ω)) (n, hs)).toReal ≤
        (taoSection7HoldListPMF n hs).toReal := by
  intro n hs
  rw [← pmfProb_stoppedPrefixPair_eq_map_apply_toReal μ K pre n hs]
  exact le_trans
    (pmfProb_mono μ (by
      intro ω hω
      refine ⟨?_, ?_⟩
      · calc
          (full ω).take n = (full ω).take (K ω) := by rw [← hω.1]
          _ = pre ω := (hpre_take ω).symm
          _ = hs := hω.2
      · simpa [hω.1] using hK_le ω))
    (hprefix_mass n hs)

/--
Mapped stopped-prefix atom bound from source-prefix stopped data.

This is the stopped-pair route after the full-horizon finite-carrier
obstruction: the producer supplies atom bounds for the actual stopped source
prefix after decoding each `(m, pre)` pair to a `Hold` point, and this adapter
transfers them to the `pre` field used by Lemma 7.7.
-/
theorem lemma77StoppedPrefixPair_map_mass_le_of_sourcePrefixStoppedPairMass
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {K : Ω → ℕ}
    {srcPre : Ω → List (ℕ × List ℕ)}
    {pre : Ω → List TaoSection7RenewalPoint}
    (hpre :
      ∀ ω,
        pre ω =
          (srcPre ω).map fun x => taoSection7HoldPointOfPrefix x.1 x.2)
    (hmass :
      ∀ n hs,
        ((μ.map fun ω =>
          (K ω,
            (srcPre ω).map fun x =>
              taoSection7HoldPointOfPrefix x.1 x.2)) (n, hs)).toReal ≤
          (taoSection7HoldListPMF n hs).toReal) :
    ∀ n hs,
      ((μ.map fun ω => (K ω, pre ω)) (n, hs)).toReal ≤
        (taoSection7HoldListPMF n hs).toReal := by
  intro n hs
  have hmap :
      μ.map (fun ω => (K ω, pre ω)) =
        μ.map fun ω =>
          (K ω,
            (srcPre ω).map fun x =>
              taoSection7HoldPointOfPrefix x.1 x.2) := by
    apply congrArg
      (fun f : Ω → ℕ × List TaoSection7RenewalPoint => μ.map f)
    funext ω
    simp [hpre ω]
  rw [hmap]
  exact hmass n hs

/--
Mapped stopped-prefix atom bound from variable-length decoded source-prefix
atom domination.

Unlike the full-horizon finite-carrier bridge, this theorem compares the
stopped atom at length `n` with the ideal source-prefix list law at the same
length `n`.  It is therefore a stopped-pair adapter, not a fixed-full-list
source-law claim.
-/
theorem lemma77StoppedPrefixPair_map_mass_le_of_stoppedSourcePrefixDecodedAtomDom
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {srcFull : Ω → List (ℕ × List ℕ)}
    {K : Ω → ℕ} {pre : Ω → List TaoSection7RenewalPoint}
    (hpre :
      ∀ ω,
        pre ω =
          ((srcFull ω).take (K ω)).map fun x =>
            taoSection7HoldPointOfPrefix x.1 x.2)
    (hdom :
      ∀ n hs,
        pmfProb μ {ω |
          K ω = n ∧
            ((srcFull ω).take n).map
              (fun x => taoSection7HoldPointOfPrefix x.1 x.2) = hs} ≤
          (((taoSection7HoldSourcePrefixListPMF n).map
            (fun xs =>
              xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)) hs).toReal) :
    ∀ n hs,
      ((μ.map fun ω => (K ω, pre ω)) (n, hs)).toReal ≤
        (taoSection7HoldListPMF n hs).toReal := by
  intro n hs
  rw [← pmfProb_stoppedPrefixPair_eq_map_apply_toReal μ K pre n hs]
  calc
    pmfProb μ {ω | K ω = n ∧ pre ω = hs}
        ≤ pmfProb μ {ω |
          K ω = n ∧
            ((srcFull ω).take n).map
              (fun x => taoSection7HoldPointOfPrefix x.1 x.2) = hs} :=
      pmfProb_mono μ (by
        intro ω hω
        refine ⟨hω.1, ?_⟩
        calc
          ((srcFull ω).take n).map
              (fun x => taoSection7HoldPointOfPrefix x.1 x.2)
              = ((srcFull ω).take (K ω)).map
                  (fun x => taoSection7HoldPointOfPrefix x.1 x.2) := by
                rw [hω.1]
          _ = pre ω := (hpre ω).symm
          _ = hs := hω.2)
    _ ≤ (((taoSection7HoldSourcePrefixListPMF n).map
            (fun xs =>
              xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)) hs).toReal :=
      hdom n hs
    _ = (taoSection7HoldListPMF n hs).toReal := by
      rw [taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq]

/--
Good-event stopped-prefix atom bound from variable-length decoded
source-prefix atom domination.

The source-law premise is restricted to `good`, so any mass outside `good`
remains an explicit residual instead of being normalized away.
-/
theorem lemma77StoppedPrefixPair_good_mass_le_of_stoppedSourcePrefixDecodedAtomDom
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {srcFull : Ω → List (ℕ × List ℕ)}
    {K : Ω → ℕ} {pre : Ω → List TaoSection7RenewalPoint}
    {good : Set Ω}
    (hpre :
      ∀ ω,
        ω ∈ good →
          pre ω =
            ((srcFull ω).take (K ω)).map fun x =>
              taoSection7HoldPointOfPrefix x.1 x.2)
    (hdom :
      ∀ n hs,
        pmfProb μ {ω |
          ω ∈ good ∧
            K ω = n ∧
              ((srcFull ω).take n).map
                (fun x => taoSection7HoldPointOfPrefix x.1 x.2) = hs} ≤
          (((taoSection7HoldSourcePrefixListPMF n).map
            (fun xs =>
              xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)) hs).toReal) :
    ∀ n hs,
      pmfProb μ {ω | ω ∈ good ∧ K ω = n ∧ pre ω = hs} ≤
        (taoSection7HoldListPMF n hs).toReal := by
  intro n hs
  calc
    pmfProb μ {ω | ω ∈ good ∧ K ω = n ∧ pre ω = hs}
        ≤ pmfProb μ {ω |
          ω ∈ good ∧
            K ω = n ∧
              ((srcFull ω).take n).map
                (fun x => taoSection7HoldPointOfPrefix x.1 x.2) = hs} :=
      pmfProb_mono μ (by
        intro ω hω
        refine ⟨hω.1, hω.2.1, ?_⟩
        calc
          ((srcFull ω).take n).map
              (fun x => taoSection7HoldPointOfPrefix x.1 x.2)
              = ((srcFull ω).take (K ω)).map
                  (fun x => taoSection7HoldPointOfPrefix x.1 x.2) := by
                rw [hω.2.1]
          _ = pre ω := (hpre ω hω.1).symm
          _ = hs := hω.2.2)
    _ ≤ (((taoSection7HoldSourcePrefixListPMF n).map
            (fun xs =>
              xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)) hs).toReal :=
      hdom n hs
    _ = (taoSection7HoldListPMF n hs).toReal := by
      rw [taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq]

/--
Constant-origin endpoint source/provenance from a pushed-forward stopped-prefix
law.

The future source-law producer may naturally bound atoms of
`μ.map (fun ω => (K ω, pre ω))`; this adapter turns that pointwise mapped-law
bound into the exact stopped-prefix cylinder field required by
`Lemma77EndpointSourceProvenance`.
-/
theorem lemma77EndpointSourceProvenance_constOrigin_of_firstPassage_mappedCylinderMass
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {origin : TaoSection7RenewalPoint}
    {K : Ω → ℕ} {pre : Ω → List TaoSection7RenewalPoint} {s : ℕ}
    (hfirst :
      ∀ ω,
        TaoSection7Lemma710.VerticalFirstPassagePrefix
          origin s (K ω) (pre ω))
    (hmass :
      ∀ n hs,
        ((μ.map fun ω => (K ω, pre ω)) (n, hs)).toReal ≤
          (taoSection7HoldListPMF n hs).toReal) :
    Lemma77EndpointSourceProvenance μ (fun _ => origin) K pre s :=
  lemma77EndpointSourceProvenance_constOrigin_of_firstPassage_cylinderMass
    (μ := μ) (origin := origin) (K := K) (pre := pre) (s := s)
    hfirst
    (by
      intro n hs
      calc
        pmfProb μ {ω | K ω = n ∧ pre ω = hs} =
            ((μ.map fun ω => (K ω, pre ω)) (n, hs)).toReal :=
          pmfProb_stoppedPrefixPair_eq_map_apply_toReal μ K pre n hs
        _ ≤ (taoSection7HoldListPMF n hs).toReal := hmass n hs)

/--
Constant-origin endpoint source/provenance from stopped source-prefix pair
mass.

The producer-facing probability obligation is the stopped-pair atom bound after
decoding each source-prefix pair to a `Hold` point.  This keeps the stopped
length variable and avoids the full-horizon finite-carrier domination route.
-/
theorem lemma77EndpointSourceProvenance_constOrigin_of_firstPassage_sourcePrefixStoppedPairMass
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {origin : TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {srcPre : Ω → List (ℕ × List ℕ)}
    {pre : Ω → List TaoSection7RenewalPoint} {s : ℕ}
    (hfirst :
      ∀ ω,
        TaoSection7Lemma710.VerticalFirstPassagePrefix
          origin s (K ω) (pre ω))
    (hpre :
      ∀ ω,
        pre ω =
          (srcPre ω).map fun x => taoSection7HoldPointOfPrefix x.1 x.2)
    (hmass :
      ∀ n hs,
        ((μ.map fun ω =>
          (K ω,
            (srcPre ω).map fun x =>
              taoSection7HoldPointOfPrefix x.1 x.2)) (n, hs)).toReal ≤
          (taoSection7HoldListPMF n hs).toReal) :
    Lemma77EndpointSourceProvenance μ (fun _ => origin) K pre s :=
  lemma77EndpointSourceProvenance_constOrigin_of_firstPassage_mappedCylinderMass
    (μ := μ) (origin := origin) (K := K) (pre := pre) (s := s)
    hfirst
    (lemma77StoppedPrefixPair_map_mass_le_of_sourcePrefixStoppedPairMass
      (μ := μ) (K := K) (srcPre := srcPre) (pre := pre) hpre hmass)

/--
Constant-origin endpoint source/provenance from variable-length decoded
source-prefix atom domination.

This is the producer-facing stopped-pair canary after the full-horizon
finite-carrier obstruction: the source-law premise is already stopped at
`K = n`, and the ideal comparison uses the length-`n` source-prefix list law.
-/
theorem lemma77EndpointSourceProvenance_constOrigin_of_firstPassage_stoppedSourcePrefixDecodedAtomDom
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {origin : TaoSection7RenewalPoint}
    {srcFull : Ω → List (ℕ × List ℕ)}
    {K : Ω → ℕ} {pre : Ω → List TaoSection7RenewalPoint} {s : ℕ}
    (hfirst :
      ∀ ω,
        TaoSection7Lemma710.VerticalFirstPassagePrefix
          origin s (K ω) (pre ω))
    (hpre :
      ∀ ω,
        pre ω =
          ((srcFull ω).take (K ω)).map fun x =>
            taoSection7HoldPointOfPrefix x.1 x.2)
    (hdom :
      ∀ n hs,
        pmfProb μ {ω |
          K ω = n ∧
            ((srcFull ω).take n).map
              (fun x => taoSection7HoldPointOfPrefix x.1 x.2) = hs} ≤
          (((taoSection7HoldSourcePrefixListPMF n).map
            (fun xs =>
              xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)) hs).toReal) :
    Lemma77EndpointSourceProvenance μ (fun _ => origin) K pre s :=
  lemma77EndpointSourceProvenance_constOrigin_of_firstPassage_mappedCylinderMass
    (μ := μ) (origin := origin) (K := K) (pre := pre) (s := s)
    hfirst
    (lemma77StoppedPrefixPair_map_mass_le_of_stoppedSourcePrefixDecodedAtomDom
      (μ := μ) (srcFull := srcFull) (K := K) (pre := pre) hpre hdom)

/--
Constant-origin residual-aware endpoint source/provenance on a good event from
variable-length decoded source-prefix atom domination.

This is the finite/truncated producer-facing surface: first passage and atom
control are supplied only on `good`, and the complement remains a residual for
an additive-bad endpoint theorem.
-/
theorem lemma77EndpointSourceProvenanceOnGood_constOrigin_of_firstPassage_stoppedSourcePrefixDecodedAtomDom
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {origin : TaoSection7RenewalPoint}
    {srcFull : Ω → List (ℕ × List ℕ)}
    {K : Ω → ℕ} {pre : Ω → List TaoSection7RenewalPoint} {s : ℕ}
    {good : Set Ω}
    (hfirst :
      ∀ ω,
        ω ∈ good →
          TaoSection7Lemma710.VerticalFirstPassagePrefix
            origin s (K ω) (pre ω))
    (hpre :
      ∀ ω,
        ω ∈ good →
          pre ω =
            ((srcFull ω).take (K ω)).map fun x =>
              taoSection7HoldPointOfPrefix x.1 x.2)
    (hdom :
      ∀ n hs,
        pmfProb μ {ω |
          ω ∈ good ∧
            K ω = n ∧
              ((srcFull ω).take n).map
                (fun x => taoSection7HoldPointOfPrefix x.1 x.2) = hs} ≤
          (((taoSection7HoldSourcePrefixListPMF n).map
            (fun xs =>
              xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)) hs).toReal) :
    Lemma77EndpointSourceProvenanceOnGood μ (fun _ => origin) K pre s good where
  first_passage_good := by
    intro ω hω
    exact hfirst ω hω
  stopped_prefix_mass_le_hold_good :=
    lemma77StoppedPrefixPair_good_mass_le_of_stoppedSourcePrefixDecodedAtomDom
      (μ := μ) (srcFull := srcFull) (K := K) (pre := pre)
      (good := good) hpre hdom

/--
Constant-origin endpoint source/provenance from guarded raw prefix-cylinder
mass.

This is the finite-horizon producer-facing form of the source-law socket:
samplewise stopped prefixes must be `take K` of the full source list, the stop
must occur within that list, and the carrier must supply raw prefix-cylinder
mass only on the support where the prefix length exists.
-/
theorem lemma77EndpointSourceProvenance_constOrigin_of_firstPassage_takePrefixCylinderMass_onSupport
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {origin : TaoSection7RenewalPoint}
    {full : Ω → List TaoSection7RenewalPoint}
    {K : Ω → ℕ} {pre : Ω → List TaoSection7RenewalPoint} {s : ℕ}
    (hfirst :
      ∀ ω,
        TaoSection7Lemma710.VerticalFirstPassagePrefix
          origin s (K ω) (pre ω))
    (hpre_take : ∀ ω, pre ω = (full ω).take (K ω))
    (hK_le : ∀ ω, K ω ≤ (full ω).length)
    (hprefix_mass :
      ∀ n hs,
        pmfProb μ {ω | (full ω).take n = hs ∧ n ≤ (full ω).length} ≤
          (taoSection7HoldListPMF n hs).toReal) :
    Lemma77EndpointSourceProvenance μ (fun _ => origin) K pre s :=
  lemma77EndpointSourceProvenance_constOrigin_of_firstPassage_mappedCylinderMass
    (μ := μ) (origin := origin) (K := K) (pre := pre) (s := s)
    hfirst
    (lemma77StoppedPrefixPair_map_mass_le_of_take_prefixCylinderMass_onSupport
      (μ := μ) (full := full) (K := K) (pre := pre)
      hpre_take hK_le hprefix_mass)

/--
Finite-good-domain stopped-pair mass accounting.

If stopped-pair atom bounds are proved only on a finite good domain `G`, then
only the probability of `G` is controlled by the ideal `Hold` mass of the
finite stopped-pair image.  The complement of `G` is the residual that a finite
or truncated source route must keep explicit.
-/
theorem lemma77_stoppedPairFiniteImage_goodMass_le_holdMass_sum
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    (G : Finset Ω)
    (hmass :
      ∀ n hs,
        pmfProb μ {ω | ω ∈ G ∧ K ω = n ∧ pre ω = hs} ≤
          (taoSection7HoldListPMF n hs).toReal) :
    pmfProb μ {ω | ω ∈ G} ≤
      (G.image fun ω : Ω => (K ω, pre ω)).sum
        (fun item => (taoSection7HoldListPMF item.1 item.2).toReal) := by
  classical
  let S : Finset (ℕ × List TaoSection7RenewalPoint) :=
    G.image fun ω : Ω => (K ω, pre ω)
  change pmfProb μ {ω | ω ∈ G} ≤
    S.sum (fun item => (taoSection7HoldListPMF item.1 item.2).toReal)
  have hsource_eq_good :
      S.sum (fun item =>
        pmfProb μ {ω | ω ∈ G ∧ K ω = item.1 ∧ pre ω = item.2}) =
      pmfProb μ {ω | ω ∈ G} := by
    calc
      S.sum (fun item =>
        pmfProb μ {ω | ω ∈ G ∧ K ω = item.1 ∧ pre ω = item.2})
          = S.sum (fun item => Finset.univ.sum fun ω : Ω =>
              if ω ∈ G ∧ K ω = item.1 ∧ pre ω = item.2 then
                (μ ω).toReal
              else
                0) := by
            apply Finset.sum_congr rfl
            intro item _hitem
            rw [pmfProb]
            apply Finset.sum_congr rfl
            intro ω _hω
            simp
      _ = Finset.univ.sum (fun ω : Ω => S.sum fun item =>
              if ω ∈ G ∧ K ω = item.1 ∧ pre ω = item.2 then
                (μ ω).toReal
              else
                0) := by
            rw [Finset.sum_comm]
      _ = Finset.univ.sum (fun ω : Ω =>
              if ω ∈ G then (μ ω).toReal else 0) := by
            apply Finset.sum_congr rfl
            intro ω _hω
            by_cases hωG : ω ∈ G
            · have hmem : (K ω, pre ω) ∈ S := by
                exact Finset.mem_image.mpr ⟨ω, hωG, rfl⟩
              rw [Finset.sum_eq_single (K ω, pre ω)]
              · simp [hωG]
              · intro item _hitem hne
                have hnot :
                    ¬ (K ω = item.1 ∧ pre ω = item.2) := by
                  intro hpair
                  exact hne (Prod.ext hpair.1.symm hpair.2.symm)
                simp [hωG, hnot]
              · intro hnotmem
                exact (hnotmem hmem).elim
            · simp [hωG]
      _ = pmfProb μ {ω | ω ∈ G} := by
            rw [pmfProb]
            apply Finset.sum_congr rfl
            intro ω _hω
            simp
  have hsource_le :
      S.sum (fun item =>
        pmfProb μ {ω | ω ∈ G ∧ K ω = item.1 ∧ pre ω = item.2}) ≤
      S.sum (fun item =>
        (taoSection7HoldListPMF item.1 item.2).toReal) := by
    exact Finset.sum_le_sum fun item _hitem =>
      hmass item.1 item.2
  calc
    pmfProb μ {ω | ω ∈ G} =
        S.sum (fun item =>
          pmfProb μ {ω | ω ∈ G ∧ K ω = item.1 ∧ pre ω = item.2}) :=
      hsource_eq_good.symm
    _ ≤ S.sum (fun item =>
        (taoSection7HoldListPMF item.1 item.2).toReal) := hsource_le

/--
Necessary mass condition for exact finite stopped-pair source provenance.

If a normalized finite carrier satisfies the exact per-atom stopped-prefix law,
then the ideal `Hold` list law assigns total mass at least `1` to the finite
image of `(K, pre)`.  Finite truncation producers should therefore carry an
explicit residual rather than normalize a subprobability finite sample and feed
it to `Lemma77EndpointSourceProvenance`.
-/
theorem lemma77EndpointSourceProvenance_finiteImageHoldMass_sum_ge_one
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s : ℕ}
    (h :
      Lemma77EndpointSourceProvenance μ start K pre s) :
    1 ≤
      (Finset.univ.image (fun ω : Ω => (K ω, pre ω))).sum
        (fun item => (taoSection7HoldListPMF item.1 item.2).toReal) := by
  classical
  let S : Finset (ℕ × List TaoSection7RenewalPoint) :=
    Finset.univ.image (fun ω : Ω => (K ω, pre ω))
  change 1 ≤ S.sum
    (fun item => (taoSection7HoldListPMF item.1 item.2).toReal)
  have hsource_eq_one :
      S.sum (fun item =>
        pmfProb μ {ω | K ω = item.1 ∧ pre ω = item.2}) = 1 := by
    calc
      S.sum (fun item =>
        pmfProb μ {ω | K ω = item.1 ∧ pre ω = item.2})
          = S.sum (fun item => Finset.univ.sum fun ω : Ω =>
              if K ω = item.1 ∧ pre ω = item.2 then (μ ω).toReal else 0) := by
            apply Finset.sum_congr rfl
            intro item _hitem
            rw [pmfProb]
            apply Finset.sum_congr rfl
            intro ω _hω
            simp
      _ = Finset.univ.sum (fun ω : Ω => S.sum fun item =>
              if K ω = item.1 ∧ pre ω = item.2 then (μ ω).toReal else 0) := by
            rw [Finset.sum_comm]
      _ = Finset.univ.sum (fun ω : Ω => (μ ω).toReal) := by
            apply Finset.sum_congr rfl
            intro ω _hω
            have hmem : (K ω, pre ω) ∈ S := by
              exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩
            rw [Finset.sum_eq_single (K ω, pre ω)]
            · simp
            · intro item _hitem hne
              have hnot :
                  ¬ (K ω = item.1 ∧ pre ω = item.2) := by
                intro hpair
                exact hne (Prod.ext hpair.1.symm hpair.2.symm)
              simp [hnot]
            · intro hnotmem
              exact (hnotmem hmem).elim
      _ = 1 := pmf_sum_toReal μ
  have hsource_le :
      S.sum (fun item =>
        pmfProb μ {ω | K ω = item.1 ∧ pre ω = item.2}) ≤
      S.sum (fun item =>
        (taoSection7HoldListPMF item.1 item.2).toReal) := by
    exact Finset.sum_le_sum fun item _hitem =>
      h.stopped_prefix_mass_le_hold item.1 item.2
  calc
    1 = S.sum (fun item =>
        pmfProb μ {ω | K ω = item.1 ∧ pre ω = item.2}) := hsource_eq_one.symm
    _ ≤ S.sum (fun item =>
        (taoSection7HoldListPMF item.1 item.2).toReal) := hsource_le

/--
Contrapositive finite-image obstruction for exact endpoint source provenance.

If the ideal `Hold` list law assigns total mass strictly less than `1` to the
finite stopped-pair image of `(K, pre)`, then no normalized finite carrier with
that image can satisfy the exact `Lemma77EndpointSourceProvenance` source-law
field.
-/
theorem not_lemma77EndpointSourceProvenance_of_finiteImageHoldMass_sum_lt_one
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s : ℕ}
    (hmass_lt :
      (Finset.univ.image (fun ω : Ω => (K ω, pre ω))).sum
        (fun item => (taoSection7HoldListPMF item.1 item.2).toReal) < 1) :
    ¬ Lemma77EndpointSourceProvenance μ start K pre s := by
  intro h
  exact (not_le_of_gt hmass_lt)
    (lemma77EndpointSourceProvenance_finiteImageHoldMass_sum_ge_one h)

/--
Exact stopped-prefix snoc cylinder bound from the source-law field.

This is the one-cylinder terminal-independence algebra needed before the
endpoint-fiber source partition: if a stopped prefix is exactly `pref ++
[last]`, its source probability is bounded by the iid prefix mass times the
one-step terminal `Hold` mass.
-/
theorem lemma77EndpointSourceProvenance_snocCylinder_le
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s n : ℕ} {pref : List TaoSection7RenewalPoint}
    {last : TaoSection7RenewalPoint}
    (h :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hlen : pref.length = n) :
    pmfProb μ {ω | K ω = n + 1 ∧ pre ω = pref ++ [last]} ≤
      (taoSection7HoldListPMF n pref).toReal *
        (taoSection7HoldPMF last).toReal := by
  calc
    pmfProb μ {ω | K ω = n + 1 ∧ pre ω = pref ++ [last]} ≤
        (taoSection7HoldListPMF (n + 1) (pref ++ [last])).toReal :=
      h.stopped_prefix_mass_le_hold (n + 1) (pref ++ [last])
    _ = (taoSection7HoldListPMF n pref).toReal *
        (taoSection7HoldPMF last).toReal :=
      taoSection7HoldListPMF_snoc_toReal_of_length hlen last

/--
Good-domain stopped-prefix snoc cylinder bound from the restricted source-law
field.

This is the residual-aware companion to
`lemma77EndpointSourceProvenance_snocCylinder_le`: only samples in `good` are
charged to the iid Hold prefix law, so downstream endpoint adapters must pay
the complement separately.
-/
theorem lemma77EndpointSourceProvenanceOnGood_snocCylinder_le
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s n : ℕ} {pref : List TaoSection7RenewalPoint}
    {last : TaoSection7RenewalPoint} {good : Set Ω}
    (h :
      Lemma77EndpointSourceProvenanceOnGood μ start K pre s good)
    (hlen : pref.length = n) :
    pmfProb μ {ω | ω ∈ good ∧ K ω = n + 1 ∧
        pre ω = pref ++ [last]} ≤
      (taoSection7HoldListPMF n pref).toReal *
        (taoSection7HoldPMF last).toReal := by
  calc
    pmfProb μ {ω | ω ∈ good ∧ K ω = n + 1 ∧
        pre ω = pref ++ [last]} ≤
        (taoSection7HoldListPMF (n + 1) (pref ++ [last])).toReal :=
      h.stopped_prefix_mass_le_hold_good (n + 1) (pref ++ [last])
    _ = (taoSection7HoldListPMF n pref).toReal *
        (taoSection7HoldPMF last).toReal :=
      taoSection7HoldListPMF_snoc_toReal_of_length hlen last

/-- The first-passage field of the Lemma 7.7 endpoint source surface. -/
theorem lemma77EndpointSourceProvenance_firstPassage
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s : ℕ}
    (h :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (ω : Ω) :
    TaoSection7Lemma710.VerticalFirstPassagePrefix
      (start ω) s (K ω) (pre ω) :=
  h.first_passage ω

/--
Pointwise endpoint-law input for Tao Lemma 7.7.

The `pointwise_endpoint_bound` field is the actual red analytic gate: future
work must prove it from the iid Hold source law, first-passage construction,
Lemma 7.6, and Lemma 2.2.  It is stated with the shifted vertical overshoot,
not raw relative height.
-/
structure Lemma77PointwiseEndpointLawInputs
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s : ℕ)
    (A B C D : ℝ) : Prop where
  source :
    Lemma77EndpointSourceProvenance μ start K pre s
  constants_nonnegative :
    0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ 0 ≤ D
  pointwise_endpoint_bound :
    ∀ r ell,
      (s : ℤ) < ell →
        pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
          lemma77PointwiseEndpointKernel A B C D s r
            (relativeVerticalOvershoot s ell)

/-- Projection of the pointwise endpoint-law bound from the explicit input surface. -/
theorem relativeEndpointFiber_prob_le_of_pointwiseEndpointLawInputs
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ} {A B C D : ℝ}
    (h :
      Lemma77PointwiseEndpointLawInputs μ start K pre s A B C D)
    (hell : (s : ℤ) < ell) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      lemma77PointwiseEndpointKernel A B C D s r
        (relativeVerticalOvershoot s ell) :=
  h.pointwise_endpoint_bound r ell hell

/--
First-passage certificates from the endpoint-law source surface provide the
positive-support premise needed by the finite-support vertical-fiber package.
-/
theorem lemma77EndpointSourceProvenance_positiveOvershootOnSupport
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s r : ℕ}
    (h :
      Lemma77EndpointSourceProvenance μ start K pre s) :
    ∀ ell,
      ell ∈ relativeHorizontalVerticalSupport start K pre r →
        (s : ℤ) < ell :=
  relativeHorizontalVerticalSupport_positiveOvershoot_of_verticalFirstPassage
    (start := start) (K := K) (pre := pre) (s := s) (r := r)
    (by
      intro ω _hω
      exact h.first_passage ω)

/--
Finite vertical sum of the pointwise Lemma 7.7 endpoint kernel over the actual
target-space vertical support of a fixed horizontal marginal.

This is a named summation target, not the analytic comparison to
`exactKernelTailSummand`.
-/
def lemma77PointwiseKernelVerticalSum
    {Ω : Type*} [Fintype Ω]
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s r : ℕ) (A B C D : ℝ) : ℝ :=
  (relativeHorizontalVerticalSupport start K pre r).sum fun ell =>
    lemma77PointwiseEndpointKernel A B C D s r
      (relativeVerticalOvershoot s ell)

/--
Vertical kernel-sum input for the Lemma 7.7 endpoint route.

This is the remaining red summation gate after a pointwise endpoint law has
been supplied: each canonical horizontal bin must have its pointwise endpoint
kernel summed over the actual finite vertical support and compared to
`exactKernelTailSummand`.
-/
structure Lemma77VerticalKernelSumInputs
    {Ω : Type*} [Fintype Ω]
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s m N : ℕ) (a b K0 V delta A B C D : ℝ) : Prop where
  pointwise_kernel_sum_le_exact :
    ∀ idx, idx ∈ Finset.range N →
      lemma77PointwiseKernelVerticalSum start K pre s
          (centeredHighTailBinBase s m delta + idx) A B C D ≤
        exactKernelTailSummand a b K0 V delta s m idx

/-- Projection of the vertical kernel-sum comparison from its explicit input surface. -/
theorem lemma77PointwiseKernelVerticalSum_le_exactKernelTailSummand
    {Ω : Type*} [Fintype Ω]
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta A B C D : ℝ}
    (h :
      Lemma77VerticalKernelSumInputs
        start K pre s m N a b K0 V delta A B C D)
    {idx : ℕ} (hidx : idx ∈ Finset.range N) :
    lemma77PointwiseKernelVerticalSum start K pre s
        (centeredHighTailBinBase s m delta + idx) A B C D ≤
      exactKernelTailSummand a b K0 V delta s m idx :=
  h.pointwise_kernel_sum_le_exact idx hidx

/--
Endpoint-law input plus a remaining vertical kernel-sum comparison feeds the
restricted target-fiber package.

This is the first consumer below the pointwise endpoint-law red gate.  It does
not prove the endpoint law or the vertical summation into
`exactKernelTailSummand`; both remain explicit inputs.
-/
theorem restrictedTargetFiberInputs_of_pointwiseEndpointLaw
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta A B C D : ℝ}
    {validSource : Set Ωsrc}
    (hLaw :
      Lemma77PointwiseEndpointLawInputs μ start K pre s A B C D)
    (hsample : μ = ν.map sampleOf)
    (hvalid :
      sampleOf ⁻¹' centeredHighTailEvent start K pre s m ⊆ validSource)
    (hsupport :
      ∀ η, η ∈ validSource →
        sampleOf η ∈ centeredHighTailEvent start K pre s m →
          prefixIncrement start K pre (sampleOf η) <
            centeredHighTailBinBase s m delta + N)
    (hsum :
      ∀ idx, idx ∈ Finset.range N →
        (relativeHorizontalVerticalSupport start K pre
            (centeredHighTailBinBase s m delta + idx)).sum
            (fun ell =>
              lemma77PointwiseEndpointKernel A B C D s
                (centeredHighTailBinBase s m delta + idx)
                (relativeVerticalOvershoot s ell)) ≤
          exactKernelTailSummand a b K0 V delta s m idx) :
    RestrictedExactKernelCanonicalBinTargetFiberInputs
      ν μ sampleOf start K pre s m N a b K0 V delta validSource
        (fun idx =>
          relativeHorizontalEvent start K pre
            (centeredHighTailBinBase s m delta + idx)) :=
  restrictedTargetFiberInputs_of_firstPassagePositiveOvershootFintypeVerticalSupportBounds
    (ν := ν) (sampleOf := sampleOf) (μ := μ)
    (start := start) (K := K) (pre := pre)
    (s := s) (m := m) (N := N)
    (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
    (validSource := validSource)
    (fun idx overshoot =>
      lemma77PointwiseEndpointKernel A B C D s
        (centeredHighTailBinBase s m delta + idx) overshoot)
    hsample hvalid hsupport
    (by
      intro idx _hidx ω _hω
      exact hLaw.source.first_passage ω)
    (by
      intro idx _hidx ell _hell hell_pos
      exact
        relativeEndpointFiber_prob_le_of_pointwiseEndpointLawInputs
          (start := start) (K := K) (pre := pre)
          (s := s)
          (r := centeredHighTailBinBase s m delta + idx)
          (ell := ell) hLaw
          (by
            have hsub : 0 < ell - (s : ℤ) := by
              simpa [relativeVerticalOvershoot] using hell_pos
            exact sub_pos.mp hsub))
    hsum

/--
Endpoint-law and named vertical kernel-sum inputs feed the restricted
target-fiber package.

This is a dependency-explicit version of
`restrictedTargetFiberInputs_of_pointwiseEndpointLaw`: the pointwise endpoint
law and the vertical summation are separate red gates.
-/
theorem restrictedTargetFiberInputs_of_pointwiseEndpointLawAndVerticalKernelSum
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta A B C D : ℝ}
    {validSource : Set Ωsrc}
    (hLaw :
      Lemma77PointwiseEndpointLawInputs μ start K pre s A B C D)
    (hKernelSum :
      Lemma77VerticalKernelSumInputs
        start K pre s m N a b K0 V delta A B C D)
    (hsample : μ = ν.map sampleOf)
    (hvalid :
      sampleOf ⁻¹' centeredHighTailEvent start K pre s m ⊆ validSource)
    (hsupport :
      ∀ η, η ∈ validSource →
        sampleOf η ∈ centeredHighTailEvent start K pre s m →
          prefixIncrement start K pre (sampleOf η) <
            centeredHighTailBinBase s m delta + N) :
    RestrictedExactKernelCanonicalBinTargetFiberInputs
      ν μ sampleOf start K pre s m N a b K0 V delta validSource
        (fun idx =>
          relativeHorizontalEvent start K pre
            (centeredHighTailBinBase s m delta + idx)) :=
  restrictedTargetFiberInputs_of_pointwiseEndpointLaw
    (ν := ν) (sampleOf := sampleOf) (μ := μ)
    (start := start) (K := K) (pre := pre)
    (s := s) (m := m) (N := N)
    (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
    (A := A) (B := B) (C := C) (D := D)
    (validSource := validSource)
    hLaw hsample hvalid hsupport
    (by
      intro idx hidx
      simpa [lemma77PointwiseKernelVerticalSum] using
        lemma77PointwiseKernelVerticalSum_le_exactKernelTailSummand
          (start := start) (K := K) (pre := pre)
          (s := s) (m := m) (N := N)
          (a := a) (b := b) (K0 := K0) (V := V) (delta := delta)
          (A := A) (B := B) (C := C) (D := D)
          hKernelSum hidx)

end TaoSection7Lemma77

end

end Tao
end Erdos1135
