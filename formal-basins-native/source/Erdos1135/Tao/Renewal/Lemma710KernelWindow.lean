import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Renewal.HoldStoppedTail
import Erdos1135.Tao.Renewal.SeparatedWindowSum
import Erdos1135.Tao.Fourier.Section7Geometry

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma710

/-!
# Lemma 7.10 One-Center Kernel Window Socket

This module names the finite probability/summation interface needed after
deterministic `NearSigma` localization in Tao Lemma 7.10.  It deliberately does
not prove the one-center kernel estimate `(7.48)` or any stopped-tail law.
-/

/--
Squared-distance proximity to a center implies membership in the horizontal
integer window around that center.  This is the deterministic projection from
the two-dimensional `NearSigma` geometry to the one-dimensional `j`-kernel
summation surface.
-/
theorem j_mem_intWindow_of_distSq_le
    {R : ℕ} {p q : TaoSection7Point}
    (h : p.distSq q ≤ (R : ℝ) ^ 2) :
    (((p.j : ℕ) : ℤ) ∈
      taoSection7IntIccWindow R (((q.j : ℕ) : ℤ))) := by
  rw [mem_taoSection7IntIccWindow]
  have hsq_horiz :
      (p.jReal - q.jReal) ^ 2 ≤ (R : ℝ) ^ 2 := by
    have hv : 0 ≤ (p.lReal - q.lReal) ^ 2 := sq_nonneg _
    dsimp [TaoSection7Point.distSq] at h
    nlinarith
  have hR : 0 ≤ (R : ℝ) := by positivity
  have hbounds := abs_le_of_sq_le_sq' hsq_horiz hR
  constructor
  · have hleft_real :
        ((q.j : ℕ) : ℝ) - (R : ℝ) ≤ ((p.j : ℕ) : ℝ) := by
      dsimp [TaoSection7Point.jReal] at hbounds
      linarith
    exact_mod_cast hleft_real
  · have hright_real :
        ((p.j : ℕ) : ℝ) ≤ ((q.j : ℕ) : ℝ) + (R : ℝ) := by
      dsimp [TaoSection7Point.jReal] at hbounds
      linarith
    exact_mod_cast hright_real

/--
Finite one-dimensional local-average summation for a selected finite set of
`Sigma` centers, projected to their `j` coordinates.

This is deterministic finite-window support only.  The near-window mass,
local-average comparison, and total-window mass are all explicit inputs.
-/
theorem finiteSigmaJWindow_localAverage
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin Kgeo Bgeo : ℝ}
    (C : Finset TaoSection7Point)
    (_hC : ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo)
    (nearWindow avgWindow : TaoSection7Point → Finset ℤ)
    (kernel : ℤ → ℝ)
    {L lambda M : ℝ}
    (hkernel : TaoSection7KernelNonnegative kernel)
    (hL : 0 ≤ L) (hlambda : 0 ≤ lambda)
    (hnear :
      TaoSection7NearWindowMassBound C
        (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ))) nearWindow kernel L)
    (hlocal :
      TaoSection7LocalAverageAtCenters C
        (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ))) avgWindow kernel lambda)
    (htotal : TaoSection7AverageWindowTotalBound C avgWindow kernel M) :
    C.sum (fun c => (nearWindow c).sum (fun x => kernel x)) ≤ L * lambda * M :=
  taoSection7SeparatedWindowSum_localAverage C
    (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ)))
    nearWindow avgWindow kernel hkernel hL hlambda hnear hlocal htotal

/--
Per-center one-dimensional kernel bound for a finite family of selected
`Sigma` centers.  This is the theorem-shaped socket where Tao's one-center
estimate `(7.48)` should eventually land.
-/
def OneCenterJKernelBound
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (C : Finset TaoSection7Point)
    (event : TaoSection7Point → Set Ω) (kernel : ℤ → ℝ) (L : ℝ) : Prop :=
  ∀ c ∈ C, pmfProb μ (event c) ≤ L * kernel (((c.j : ℕ) : ℤ))

/--
Monotonicity of the one-center kernel-bound socket in its event family.

This is the safe way to pass from a broad one-center endpoint event to a
restricted event such as `largeEvent ∩ endpointNearCenter`.
-/
theorem oneCenterJKernelBound_mono_event
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {C : Finset TaoSection7Point}
    {eventSmall eventBig : TaoSection7Point → Set Ω}
    {kernel : ℤ → ℝ} {L : ℝ}
    (hsubset : ∀ c, c ∈ C → eventSmall c ⊆ eventBig c)
    (hbig : OneCenterJKernelBound μ C eventBig kernel L) :
    OneCenterJKernelBound μ C eventSmall kernel L := by
  intro c hc
  exact le_trans (pmfProb_mono μ (hsubset c hc)) (hbig c hc)

/--
Restricting a one-center event family to an ambient event preserves any
one-center kernel bound by monotonicity.
-/
theorem oneCenterJKernelBound_inter_left
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {C : Finset TaoSection7Point}
    {event : TaoSection7Point → Set Ω} {largeEvent : Set Ω}
    {kernel : ℤ → ℝ} {L : ℝ}
    (h : OneCenterJKernelBound μ C event kernel L) :
    OneCenterJKernelBound μ C (fun c => largeEvent ∩ event c) kernel L :=
  oneCenterJKernelBound_mono_event (by
    intro c _hc ω hω
    exact hω.2) h

/--
Post-stopped one-center mass for a finite family of stopped prefixes.

The event predicate is deliberately still phrased on `(prefix, tail)` lists:
later source-facing work must identify it with Tao's first-passage endpoint
event near a chosen center and prove the corresponding `(7.48)` kernel law.
-/
noncomputable def postStoppedOneCenterMass
    (p : ℕ)
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (EndpointNearCenter :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel EndpointNearCenter] : ℝ :=
  S.sum fun item =>
    ∑' tail : List TaoSection7RenewalPoint,
      if EndpointNearCenter item.2 tail then
        (taoSection7HoldListPMF (item.1 + p) (item.2 ++ tail)).toReal
      else 0

/--
Post-stopped one-center kernel input for Lemma 7.10.

This records the source-shaped data that should eventually come from the
first-passage endpoint law `(7.48)` plus post-`k` suffix convolution.  It does
not prove that law: the stopped prefix family, cylinder mass bound, and
near-window comparison are explicit fields.
-/
structure OneCenterPostStoppedKernelInput
    (p : ℕ)
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (center : TaoSection7Point)
    (nearWindow : Finset ℤ)
    (kernel : ℤ → ℝ)
    (EndpointNearCenter :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [DecidableRel EndpointNearCenter]
    (bound : ℝ) : Prop where
  prefixes : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S
  kernel_nonnegative : TaoSection7KernelNonnegative kernel
  cylinder_bound :
    postStoppedOneCenterMass p S EndpointNearCenter ≤ bound
  bound_le_near_window :
    bound ≤ nearWindow.sum fun x => kernel x

/--
The generic stopped-tail variable-prefix theorem supplies the post-stopped
one-center cylinder bound.
-/
theorem postStoppedOneCenterMass_le_of_stoppedTailBound
    {p : ℕ}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {EndpointNearCenter :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [DecidableRel EndpointNearCenter]
    {b : ℝ}
    (hS : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S)
    (hb : 0 ≤ b)
    (hTail : TaoSection7StoppedHoldTailBound p EndpointNearCenter b) :
    postStoppedOneCenterMass p S EndpointNearCenter ≤ b := by
  simpa [postStoppedOneCenterMass] using
    (taoSection7StoppedHoldVariablePrefixTail_tsum_le
      (p := p) (PrefixOK := PrefixOK) S hS EndpointNearCenter hb hTail)

/--
Construct the post-stopped one-center input from a stopped-tail bound and a
near-window comparison.
-/
theorem oneCenterPostStoppedKernelInput_of_stoppedTailBound
    {p : ℕ}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {center : TaoSection7Point}
    {nearWindow : Finset ℤ}
    {kernel : ℤ → ℝ}
    {EndpointNearCenter :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [DecidableRel EndpointNearCenter]
    {b : ℝ}
    (hS : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S)
    (hkernel : TaoSection7KernelNonnegative kernel)
    (hb : 0 ≤ b)
    (hTail : TaoSection7StoppedHoldTailBound p EndpointNearCenter b)
    (hb_near : b ≤ nearWindow.sum fun x => kernel x) :
    OneCenterPostStoppedKernelInput p PrefixOK S center nearWindow kernel
      EndpointNearCenter b where
  prefixes := hS
  kernel_nonnegative := hkernel
  cylinder_bound :=
    postStoppedOneCenterMass_le_of_stoppedTailBound hS hb hTail
  bound_le_near_window := hb_near

/--
The post-stopped one-center input controls the endpoint mass by its supplied
near-window kernel sum.
-/
theorem oneCenterPostStoppedKernelInput_mass_le_nearWindow
    {p : ℕ}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {center : TaoSection7Point}
    {nearWindow : Finset ℤ}
    {kernel : ℤ → ℝ}
    {EndpointNearCenter :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [DecidableRel EndpointNearCenter]
    {bound : ℝ}
    (h :
      OneCenterPostStoppedKernelInput p PrefixOK S center nearWindow kernel
        EndpointNearCenter bound) :
    postStoppedOneCenterMass p S EndpointNearCenter ≤
      nearWindow.sum fun x => kernel x :=
  le_trans h.cylinder_bound h.bound_le_near_window

/--
One-center post-stopped kernel bound after a supplied near-window estimate.

This is the local endpoint-law consumer that can later feed the finite
`OneCenterJKernelBound` surface once the stopped source event is identified
with a finite probability event.
-/
theorem oneCenterPostStoppedKernelInput_mass_le_kernel
    {p : ℕ}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {center : TaoSection7Point}
    {nearWindow : Finset ℤ}
    {kernel : ℤ → ℝ}
    {EndpointNearCenter :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [DecidableRel EndpointNearCenter]
    {bound L : ℝ}
    (h :
      OneCenterPostStoppedKernelInput p PrefixOK S center nearWindow kernel
        EndpointNearCenter bound)
    (hnear :
      nearWindow.sum (fun x => kernel x) ≤
        L * kernel (((center.j : ℕ) : ℤ))) :
    postStoppedOneCenterMass p S EndpointNearCenter ≤
      L * kernel (((center.j : ℕ) : ℤ)) :=
  le_trans
    (oneCenterPostStoppedKernelInput_mass_le_nearWindow h)
    hnear

/--
Source-law/cylinder mass-control socket for one-center events.

The cover premise is deterministic source coverage: each finite-PMF sample in
the one-center event must map to a selected stopped prefix and tail.  The
field then supplies the probability/source-law step bounding the finite PMF
event mass by the corresponding stopped-prefix/tail cylinder sum.  This is the
one-center analogue of the `(7.61)` post-`k` source-cylinder mass-control
surface, not a proof of that source law.
-/
structure Lemma710OneCenterSourceCylinderMassControl
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (p : ℕ)
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (fullOf : Ω → List TaoSection7RenewalPoint)
    (event : TaoSection7Point → Set Ω)
    (EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [∀ c, DecidableRel (EndpointNearCenter c)] : Prop where
  event_mass_le_cylinder :
    ∀ c,
      (∀ ω, ω ∈ event c →
        ∃ item, item ∈ S ∧
          ∃ tail : List TaoSection7RenewalPoint,
            fullOf ω = item.2 ++ tail ∧
              EndpointNearCenter c item.2 tail) →
      pmfProb μ (event c) ≤
        postStoppedOneCenterMass p S (EndpointNearCenter c)

/--
Canonical finite-PMF event whose sample source list is covered by one of the
selected stopped-prefix/post-`k` cylinders for a fixed center.

This is the lower source-law event used to instantiate
`Lemma710OneCenterSourceCylinderMassControl`: proving a probability bound for
this event is still a real source-law obligation.
-/
def Lemma710OneCenterStoppedCylinderEvent
    {Ω : Type*}
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (fullOf : Ω → List TaoSection7RenewalPoint)
    (EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    (c : TaoSection7Point) : Set Ω :=
  {ω | ∃ item, item ∈ S ∧
    ∃ tail : List TaoSection7RenewalPoint,
      fullOf ω = item.2 ++ tail ∧ EndpointNearCenter c item.2 tail}

/--
Concrete source-law socket for one-center stopped cylinders.

This is weaker and more concrete than
`Lemma710OneCenterSourceCylinderMassControl`: it only asks for the finite-PMF
probability of the canonical stopped-cylinder event to be bounded by the
corresponding stopped-prefix/tail cylinder sum.  It does not prove that source
law.
-/
structure Lemma710OneCenterStoppedCylinderSourceLaw
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω) (p : ℕ)
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (fullOf : Ω → List TaoSection7RenewalPoint)
    (EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    [∀ c, DecidableRel (EndpointNearCenter c)] : Prop where
  stopped_cylinder_event_mass_le :
    ∀ c,
      pmfProb μ
        (Lemma710OneCenterStoppedCylinderEvent S fullOf EndpointNearCenter c)
        ≤ postStoppedOneCenterMass p S (EndpointNearCenter c)

/--
Finite source-carrier bridge for the stopped-cylinder source-law socket.

If the finite sample law `μ` is the pushforward of a finite source-carrier law
`ν`, and the source carrier already satisfies the stopped-cylinder event
bound after decoding by `sampleOf`, then the finite sample space satisfies
`Lemma710OneCenterStoppedCylinderSourceLaw`.

This is still not a proof of the source event bound: the bound on the source
carrier is the remaining source-law input.
-/
theorem lemma710OneCenterStoppedCylinderSourceLaw_of_sourceCarrier
    {Ω Ωsrc : Type*} [Fintype Ω] [Fintype Ωsrc]
    {μ : PMF Ω} {ν : PMF Ωsrc} {p : ℕ}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {sampleOf : Ωsrc → Ω}
    {EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [∀ c, DecidableRel (EndpointNearCenter c)]
    (hμ : μ = ν.map sampleOf)
    (hsource :
      ∀ c,
        pmfProb ν
          {σ | ∃ item, item ∈ S ∧
            ∃ tail : List TaoSection7RenewalPoint,
              fullOf (sampleOf σ) = item.2 ++ tail ∧
                EndpointNearCenter c item.2 tail} ≤
          postStoppedOneCenterMass p S (EndpointNearCenter c)) :
    Lemma710OneCenterStoppedCylinderSourceLaw μ p S fullOf
      EndpointNearCenter where
  stopped_cylinder_event_mass_le := by
    intro c
    calc
      pmfProb μ
          (Lemma710OneCenterStoppedCylinderEvent S fullOf
            EndpointNearCenter c)
          = pmfProb (ν.map sampleOf)
              (Lemma710OneCenterStoppedCylinderEvent S fullOf
                EndpointNearCenter c) := by
              rw [hμ]
      _ =
          pmfProb ν
            (sampleOf ⁻¹'
              Lemma710OneCenterStoppedCylinderEvent S fullOf
                EndpointNearCenter c) := by
              exact pmfProb_map_preimage ν sampleOf
                (Lemma710OneCenterStoppedCylinderEvent S fullOf
                  EndpointNearCenter c)
      _ ≤ postStoppedOneCenterMass p S (EndpointNearCenter c) := by
              simpa [Lemma710OneCenterStoppedCylinderEvent, Set.preimage]
                using hsource c

/--
The canonical stopped-cylinder source-law socket implies the general
one-center source-cylinder mass-control record.

The proof is only event monotonicity: any event with a deterministic cover by
the selected stopped cylinders is a subset of the canonical stopped-cylinder
event.  The actual source-law bound for that canonical event remains the
input.
-/
theorem lemma710OneCenterSourceCylinderMassControl_of_stoppedCylinderSourceLaw
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {event : TaoSection7Point → Set Ω}
    {EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [∀ c, DecidableRel (EndpointNearCenter c)]
    (hsource :
      Lemma710OneCenterStoppedCylinderSourceLaw μ p S fullOf
        EndpointNearCenter) :
    Lemma710OneCenterSourceCylinderMassControl μ p S fullOf event
      EndpointNearCenter where
  event_mass_le_cylinder := by
    intro c hcover
    exact le_trans
      (pmfProb_mono μ (by
        intro ω hω
        exact hcover ω hω))
      (hsource.stopped_cylinder_event_mass_le c)

/--
Turn one-center source-cylinder mass control plus deterministic source
coverage into the exact event-identification premise consumed by
`oneCenterJKernelBound_of_stoppedTailBound_identification`.
-/
theorem oneCenterEventIdentification_of_sourceCylinderMassControl
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {C : Finset TaoSection7Point}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {event : TaoSection7Point → Set Ω}
    {EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [∀ c, DecidableRel (EndpointNearCenter c)]
    (hmass :
      Lemma710OneCenterSourceCylinderMassControl μ p S fullOf event
        EndpointNearCenter)
    (hcover :
      ∀ c ∈ C, ∀ ω, ω ∈ event c →
        ∃ item, item ∈ S ∧
          ∃ tail : List TaoSection7RenewalPoint,
            fullOf ω = item.2 ++ tail ∧
              EndpointNearCenter c item.2 tail) :
    ∀ c ∈ C,
      pmfProb μ (event c) ≤
        postStoppedOneCenterMass p S (EndpointNearCenter c) := by
  intro c hc
  exact hmass.event_mass_le_cylinder c (hcover c hc)

/--
Convert post-stopped one-center kernel inputs into the finite
`OneCenterJKernelBound` surface after a supplied event-identification step.

This is intentionally not a proof of Tao's `(7.48)`: the inequality comparing
the finite probability event to the post-stopped prefix/tail mass is an
explicit hypothesis for each center.
-/
theorem oneCenterJKernelBound_of_postStoppedKernelInput_identification
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {C : Finset TaoSection7Point}
    {event : TaoSection7Point → Set Ω}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {nearWindow : TaoSection7Point → Finset ℤ}
    {kernel : ℤ → ℝ}
    {EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [hdec : ∀ c, DecidableRel (EndpointNearCenter c)]
    {bound : TaoSection7Point → ℝ}
    {L : ℝ}
    (hidentify :
      ∀ c ∈ C,
        pmfProb μ (event c) ≤
          postStoppedOneCenterMass p S (EndpointNearCenter c))
    (hinput :
      ∀ c ∈ C,
        OneCenterPostStoppedKernelInput p PrefixOK S c (nearWindow c) kernel
          (EndpointNearCenter c) (bound c))
    (hnear :
      ∀ c ∈ C,
        (nearWindow c).sum (fun x => kernel x) ≤
          L * kernel (((c.j : ℕ) : ℤ))) :
    OneCenterJKernelBound μ C event kernel L := by
  intro c hc
  have hmass :
      postStoppedOneCenterMass p S (EndpointNearCenter c) ≤ bound c :=
    (hinput c hc).cylinder_bound
  have hnearWindow :
      bound c ≤ (nearWindow c).sum fun x => kernel x :=
    (hinput c hc).bound_le_near_window
  exact le_trans (hidentify c hc)
    (le_trans hmass (le_trans hnearWindow (hnear c hc)))

/--
Direct one-center kernel-bound wrapper from stopped-tail inputs.

This feeds `OneCenterJKernelBound` while keeping the real analytic and
probabilistic obligations explicit: event identification, the stopped-tail
law, the near-window comparison, and the final one-center kernel comparison.
-/
theorem oneCenterJKernelBound_of_stoppedTailBound_identification
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {C : Finset TaoSection7Point}
    {event : TaoSection7Point → Set Ω}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {nearWindow : TaoSection7Point → Finset ℤ}
    {kernel : ℤ → ℝ}
    {EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [hdec : ∀ c, DecidableRel (EndpointNearCenter c)]
    {bound : TaoSection7Point → ℝ}
    {L : ℝ}
    (hprefixes : TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S)
    (hkernel : TaoSection7KernelNonnegative kernel)
    (hbound_nonneg : ∀ c ∈ C, 0 ≤ bound c)
    (htail :
      ∀ c ∈ C,
        TaoSection7StoppedHoldTailBound p (EndpointNearCenter c) (bound c))
    (hidentify :
      ∀ c ∈ C,
        pmfProb μ (event c) ≤
          postStoppedOneCenterMass p S (EndpointNearCenter c))
    (hbound_near :
      ∀ c ∈ C,
        bound c ≤ (nearWindow c).sum fun x => kernel x)
    (hnear :
      ∀ c ∈ C,
        (nearWindow c).sum (fun x => kernel x) ≤
          L * kernel (((c.j : ℕ) : ℤ))) :
    OneCenterJKernelBound μ C event kernel L :=
  oneCenterJKernelBound_of_postStoppedKernelInput_identification
    (hidentify := hidentify)
    (hinput := by
      intro c hc
      exact
        @oneCenterPostStoppedKernelInput_of_stoppedTailBound
          p PrefixOK S c (nearWindow c) kernel (EndpointNearCenter c)
          (hdec c) (bound c) hprefixes hkernel (hbound_nonneg c hc)
          (htail c hc) (hbound_near c hc))
    (hnear := hnear)

/--
Finite one-center kernel summation over selected `Sigma` centers.

The inputs still include the per-center kernel bound, local-average
comparability, and total averaged-window mass.  Therefore this is only an
algebraic consumer for a future `(7.48)` estimate and separated-window mass
bound; it is not a proof of Lemma 7.10.
-/
theorem oneCenterJKernel_finiteSigmaWindow_sum_le
    {Ω : Type*} [Fintype Ω]
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin Kgeo Bgeo : ℝ}
    (μ : PMF Ω) (C : Finset TaoSection7Point)
    (_hC : ∀ c, c ∈ C → c ∈ Sigma family old sMin Kgeo Bgeo)
    (event : TaoSection7Point → Set Ω)
    (avgWindow : TaoSection7Point → Finset ℤ)
    (kernel : ℤ → ℝ)
    {L lambda M : ℝ}
    (_hkernel : TaoSection7KernelNonnegative kernel)
    (hL : 0 ≤ L) (hlambda : 0 ≤ lambda)
    (hone : OneCenterJKernelBound μ C event kernel L)
    (hlocal :
      TaoSection7LocalAverageAtCenters C
        (fun c : TaoSection7Point => (((c.j : ℕ) : ℤ))) avgWindow kernel lambda)
    (htotal : TaoSection7AverageWindowTotalBound C avgWindow kernel M) :
    C.sum (fun c => pmfProb μ (event c)) ≤ L * lambda * M := by
  classical
  have hpoint :
      ∀ c ∈ C,
        pmfProb μ (event c) ≤
          (L * lambda) * (avgWindow c).sum (fun x => kernel x) := by
    intro c hc
    have hone_c := hone c hc
    have hlocal_c := hlocal c hc
    have hmul :
        L * kernel (((c.j : ℕ) : ℤ)) ≤
          L * (lambda * (avgWindow c).sum (fun x => kernel x)) :=
      mul_le_mul_of_nonneg_left hlocal_c hL
    calc
      pmfProb μ (event c) ≤ L * kernel (((c.j : ℕ) : ℤ)) := hone_c
      _ ≤ L * (lambda * (avgWindow c).sum (fun x => kernel x)) := hmul
      _ = (L * lambda) * (avgWindow c).sum (fun x => kernel x) := by ring
  have hsum :=
    Finset.sum_le_sum hpoint
  have hsum_eq :
      C.sum (fun c => (L * lambda) * (avgWindow c).sum (fun x => kernel x)) =
        (L * lambda) * C.sum (fun c => (avgWindow c).sum (fun x => kernel x)) := by
    simpa using
      (Finset.mul_sum C (fun c => (avgWindow c).sum (fun x => kernel x)) (L * lambda)).symm
  have hcoeff : 0 ≤ L * lambda := mul_nonneg hL hlambda
  have htotal_mul :
      (L * lambda) * C.sum (fun c => (avgWindow c).sum (fun x => kernel x)) ≤
        (L * lambda) * M :=
    mul_le_mul_of_nonneg_left htotal hcoeff
  calc
    C.sum (fun c => pmfProb μ (event c))
        ≤ C.sum (fun c => (L * lambda) * (avgWindow c).sum (fun x => kernel x)) := hsum
    _ = (L * lambda) * C.sum (fun c => (avgWindow c).sum (fun x => kernel x)) := hsum_eq
    _ ≤ (L * lambda) * M := htotal_mul
    _ = L * lambda * M := by ring

end TaoSection7Lemma710

end

end Tao
end Erdos1135
