/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Band.A5ReferenceTerminalPacket
import Erdos1135.ND.Band.A5FixedCellReferenceProfiles
import Erdos1135.ND.Band.A5NominalTotalCap
import Erdos1135.ND.Probability.TrueAbsorption
import Erdos1135.ND.Fourier.FixedTotalConductorDecay

/-!
# A5 reference absorption at one physical time

This leaf performs true absorption over all retained terminal totals at one
fixed padded time.  The proportional eta row is absorbed before summation, so
the surviving coefficient has no tube-width factor.  Only the separate FM1
and absolute-tail rows use the endpoint-mass bound.
-/

namespace Erdos1135
namespace ND

open Tao
open scoped BigOperators

noncomputable section

/-- Literal harmonic nominal mass at one retained padded time. -/
def ndA5HarmonicNominalFixedTimeMass
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ)
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j}) : ℝ :=
  let nu := n.1 - Tao.taoSection5M0 B
  ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
    ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
      ∑ u : Sym (Fin nu) (L.1 - nu),
        ndA5HarmonicTerminalAtomNominalIdealMass
          (⟨n, ⟨L, (u, M)⟩⟩ :
            NDA5TerminalAtomIndex B branch C j E)

/-- Literal flat nominal mass at one retained padded time. -/
def ndA5FlatNominalFixedTimeMass
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ)
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j}) : ℝ :=
  let nu := n.1 - Tao.taoSection5M0 B
  ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
    ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
      ∑ u : Sym (Fin nu) (L.1 - nu),
        ndA5FlatTerminalAtomNominalIdealMass
          (⟨n, ⟨L, (u, M)⟩⟩ :
            NDA5TerminalAtomIndex B branch C j E)

/-- Fiber-free harmonic reference profile at one retained padded time. -/
def ndA5HarmonicReferenceFixedTimeProfile
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ)
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j}) : ℝ :=
  let nu := n.1 - Tao.taoSection5M0 B
  let z := ndA5BandLower B branch j
  let W := ndA5TubeWidth B C
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  ∑ M ∈ Tao.taoSection5EPrime B E,
    (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
      (((3 : ℝ) ^ m / ((M : ℝ) * H)) *
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandRawQTerm B branch
            (ndA5PhysicalPhase z M) W nu r)

/-- Fiber-free flat reference profile at one retained padded time.  The
exponential remains inside the named strict raw-Q term. -/
def ndA5FlatReferenceFixedTimeProfile
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ)
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j}) : ℝ :=
  let nu := n.1 - Tao.taoSection5M0 B
  let z := ndA5BandLower B branch j
  let W := ndA5TubeWidth B C
  let card := ((ndA5OddBand B branch j).card : ℝ)
  ∑ M ∈ Tao.taoSection5EPrime B E,
    (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
      (((z * (3 : ℝ) ^ m) / ((M : ℝ) * card)) *
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandFlatRawQTerm B branch
            (ndA5PhysicalPhase z M) W nu r)

/-- The harmonic nonproportional error before true absorption. -/
def ndA5HarmonicReferenceNonproportionalError (m : ℕ) (Cfm1 : ℝ) : ℝ :=
  20 * (Cfm1 / (m : ℝ) ^ 11) + 4 / (m : ℝ) ^ 3 * 20

/-- The flat nonproportional error before true absorption. -/
def ndA5FlatReferenceNonproportionalError (m : ℕ) (Cfm1 : ℝ) : ℝ :=
  80 * (Cfm1 / (m : ℝ) ^ 11) + 4 / (m : ℝ) ^ 3 * 80

private theorem sum_terminal_endpointMass_mul_le
    (nu : ℕ) (S : Finset ℕ) (e : ℝ) (he : 0 ≤ e) :
    (∑ L : {L // L ∈ S}, ndGeom2EndpointMass nu L.1 * e) ≤ e := by
  classical
  calc
    (∑ L : {L // L ∈ S}, ndGeom2EndpointMass nu L.1 * e) =
        ∑ L ∈ S, ndGeom2EndpointMass nu L * e := by
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach S (fun L => ndGeom2EndpointMass nu L * e)
    _ = (∑ L ∈ S, ndGeom2EndpointMass nu L) * e := by
      rw [Finset.sum_mul]
    _ ≤ 1 * e :=
      mul_le_mul_of_nonneg_right (sum_ndGeom2EndpointMass_le_one nu S) he
    _ = e := one_mul e

/-- At one padded time, harmonic terminal cells are absorbed componentwise.
The common eta coefficient multiplies the actual mass and has no factor equal
to the number of terminal totals. -/
theorem abs_ndA5HarmonicNominalFixedTimeMass_sub_reference_le_trueAbsorb
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {Cband : ℝ} {j : ℕ} {E : Set ℕ}
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hcount : 0 < ndA5BandCount B branch)
    {Cfm1 : ℝ} (hCfm1 : 0 ≤ Cfm1)
    (hFM1 : ndSection7ConditionedFM1NatAt 11
      ((771 / 100 : ℝ) * Cband) Cfm1)
    (hschedule : NDA5ReferenceTerminalCellPacketAt B Cband)
    (n : {n // n ∈ ndA5PaddedBandWindow B branch Cband j})
    (ht2 : NDA5T2ScaleFacts B n.1 Cband) :
    |ndA5HarmonicNominalFixedTimeMass B branch Cband j E n -
        ndA5HarmonicReferenceFixedTimeProfile B
          (ndA5ReferenceLevel B) branch Cband j E n| ≤
      2 * ndA5ReferenceAbsorbBar B Cband *
          ndA5HarmonicNominalFixedTimeMass B branch Cband j E n +
        2 * ndA5HarmonicReferenceNonproportionalError
          (ndA5ReferenceLevel B) Cfm1 := by
  classical
  let m := ndA5ReferenceLevel B
  let nu := n.1 - Tao.taoSection5M0 B
  let Y : {L // L ∈ ndA5TerminalTotals B Cband n.1} → ℝ := fun L =>
    ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
      ∑ u : Sym (Fin nu) (L.1 - nu),
        ndA5HarmonicTerminalAtomNominalIdealMass
          (⟨n, ⟨L, (u, M)⟩⟩ :
            NDA5TerminalAtomIndex B branch Cband j E)
  let q : {L // L ∈ ndA5TerminalTotals B Cband n.1} → ℝ := fun L =>
    ndGeom2EndpointMass nu L.1
  let R : {L // L ∈ ndA5TerminalTotals B Cband n.1} → ℝ := fun L =>
    ndPMFWeightedExpectation (Tao.syracPMF m)
      (fun X =>
        Tao.taoSection5PayloadFreeCoefficient m
            (ndA5FixedCellEndpoints B branch j E nu L.1) X /
          Tao.logFinsetMass (ndA5OddBand B branch j))
  let e : {L // L ∈ ndA5TerminalTotals B Cband n.1} → ℝ := fun _ =>
    ndA5HarmonicReferenceNonproportionalError m Cfm1
  let a : {L // L ∈ ndA5TerminalTotals B Cband n.1} → ℝ := fun L =>
    (43 / 25 : ℝ) *
      (ndFixedTotalRatioEps m nu L.1 + 8 / (m : ℝ) ^ 3)
  -- The time packet is available even when the terminal-total carrier is empty.
  rw [NDA5ReferenceTerminalCellPacketAt] at hschedule
  have htimePacket := hschedule.2.2.2.2 ht2
  have hcellPacket (L : {L // L ∈ ndA5TerminalTotals B Cband n.1}) :=
    htimePacket.2 L.2
  have hY : ∀ L ∈ (Finset.univ : Finset
      {L // L ∈ ndA5TerminalTotals B Cband n.1}), 0 ≤ Y L := by
    intro L _hL
    simpa only [Y, nu] using
      (ndA5NominalFixedCell_sums_nonneg facts hcount n L ht2).1
  have ha0 : ∀ L ∈ (Finset.univ : Finset
      {L // L ∈ ndA5TerminalTotals B Cband n.1}), 0 ≤ a L := by
    intro L _hL
    exact mul_nonneg (by norm_num) (hcellPacket L).2.2.1
  have haBar : ∀ L ∈ (Finset.univ : Finset
      {L // L ∈ ndA5TerminalTotals B Cband n.1}),
      a L ≤ ndA5ReferenceAbsorbBar B Cband := by
    intro L _hL
    exact (hcellPacket L).2.2.2.2
  have hlocal : ∀ L ∈ (Finset.univ : Finset
      {L // L ∈ ndA5TerminalTotals B Cband n.1}),
      |Y L - q L * R L| ≤ q L * (e L + a L * R L) := by
    intro L _hL
    have hpacket := hcellPacket L
    have hdesc :=
      abs_sum_ndA5HarmonicTerminalAtomNominalIdealMass_fixedCell_sub_syrac_le_fm1
        (E := E) n L ht2 lost facts.schedule.one_le_B hcount hFM1
        hschedule.1 htimePacket.1 hpacket.1 hpacket.2.1
        hpacket.2.2.2.1
    dsimp only at hdesc
    rw [← ndPMFWeightedExpectation_ndA5FixedCellHarmonicReference_low]
      at hdesc
    dsimp only [Y, q, R, e, a, m, nu,
      ndA5HarmonicReferenceNonproportionalError]
    convert hdesc using 1; ring
  have habsorb :=
    abs_sum_sub_sum_mul_le_trueAbsorb
      (Finset.univ : Finset
        {L // L ∈ ndA5TerminalTotals B Cband n.1})
      Y q R e a (ndA5ReferenceAbsorbBar B Cband)
      hY ha0 haBar hschedule.2.2.2.1 hlocal
  have href :
      (∑ L : {L // L ∈ ndA5TerminalTotals B Cband n.1}, q L * R L) =
        ndA5HarmonicReferenceFixedTimeProfile B m branch Cband j E n := by
    simpa only [q, R, m, nu,
      ndA5HarmonicReferenceFixedTimeProfile] using
        (sum_ndA5TerminalTotals_harmonicReference_eq_lowProfile
          facts.schedule.one_le_B hlogB ht2 (m := m)
            (branch := branch) (j := j) (E := E))
  have he0 : 0 ≤ ndA5HarmonicReferenceNonproportionalError m Cfm1 := by
    unfold ndA5HarmonicReferenceNonproportionalError
    have hm0 : (0 : ℝ) < m := by
      exact_mod_cast (by omega : 0 < m)
    positivity
  have herr :
      (∑ L : {L // L ∈ ndA5TerminalTotals B Cband n.1}, q L * e L) ≤
        ndA5HarmonicReferenceNonproportionalError m Cfm1 := by
    simpa only [q, e, nu] using
      sum_terminal_endpointMass_mul_le nu
        (ndA5TerminalTotals B Cband n.1)
        (ndA5HarmonicReferenceNonproportionalError m Cfm1) he0
  rw [href] at habsorb
  simpa only [Y, m, ndA5HarmonicNominalFixedTimeMass] using
    habsorb.trans (by nlinarith)

/-- At one padded time, flat terminal cells obey the same componentwise
absorption pattern, with cap `80` confined to nonproportional rows. -/
theorem abs_ndA5FlatNominalFixedTimeMass_sub_reference_le_trueAbsorb
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {Cband : ℝ} {j : ℕ} {E : Set ℕ}
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hcount : 0 < ndA5BandCount B branch)
    {Cfm1 : ℝ} (hCfm1 : 0 ≤ Cfm1)
    (hFM1 : ndSection7ConditionedFM1NatAt 11
      ((771 / 100 : ℝ) * Cband) Cfm1)
    (hschedule : NDA5ReferenceTerminalCellPacketAt B Cband)
    (n : {n // n ∈ ndA5PaddedBandWindow B branch Cband j})
    (ht2 : NDA5T2ScaleFacts B n.1 Cband) :
    |ndA5FlatNominalFixedTimeMass B branch Cband j E n -
        ndA5FlatReferenceFixedTimeProfile B
          (ndA5ReferenceLevel B) branch Cband j E n| ≤
      2 * ndA5ReferenceAbsorbBar B Cband *
          ndA5FlatNominalFixedTimeMass B branch Cband j E n +
        2 * ndA5FlatReferenceNonproportionalError
          (ndA5ReferenceLevel B) Cfm1 := by
  classical
  let m := ndA5ReferenceLevel B
  let nu := n.1 - Tao.taoSection5M0 B
  have hmnu : m ≤ nu := by
    have := hschedule
    rw [NDA5ReferenceTerminalCellPacketAt] at this
    have hroom := this.2.2.2.2 ht2
    omega
  let Y : {L // L ∈ ndA5TerminalTotals B Cband n.1} → ℝ := fun L =>
    ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
      ∑ u : Sym (Fin nu) (L.1 - nu),
        ndA5FlatTerminalAtomNominalIdealMass
          (⟨n, ⟨L, (u, M)⟩⟩ :
            NDA5TerminalAtomIndex B branch Cband j E)
  let q : {L // L ∈ ndA5TerminalTotals B Cband n.1} → ℝ := fun L =>
    ndGeom2EndpointMass nu L.1
  let R : {L // L ∈ ndA5TerminalTotals B Cband n.1} → ℝ := fun L =>
    ndPMFWeightedExpectation (Tao.syracPMF m)
      (ndA5FixedCellFlatCoarseTest hmnu B branch j E L.1)
  let e : {L // L ∈ ndA5TerminalTotals B Cband n.1} → ℝ := fun _ =>
    ndA5FlatReferenceNonproportionalError m Cfm1
  let a : {L // L ∈ ndA5TerminalTotals B Cband n.1} → ℝ := fun L =>
    (43 / 25 : ℝ) *
      (ndFixedTotalRatioEps m nu L.1 + 8 / (m : ℝ) ^ 3)
  rw [NDA5ReferenceTerminalCellPacketAt] at hschedule
  have htimePacket := hschedule.2.2.2.2 ht2
  have hcellPacket (L : {L // L ∈ ndA5TerminalTotals B Cband n.1}) :=
    htimePacket.2 L.2
  have hY : ∀ L ∈ (Finset.univ : Finset
      {L // L ∈ ndA5TerminalTotals B Cband n.1}), 0 ≤ Y L := by
    intro L _hL
    simpa only [Y, nu] using
      (ndA5NominalFixedCell_sums_nonneg facts hcount n L ht2).2
  have ha0 : ∀ L ∈ (Finset.univ : Finset
      {L // L ∈ ndA5TerminalTotals B Cband n.1}), 0 ≤ a L := by
    intro L _hL
    exact mul_nonneg (by norm_num) (hcellPacket L).2.2.1
  have haBar : ∀ L ∈ (Finset.univ : Finset
      {L // L ∈ ndA5TerminalTotals B Cband n.1}),
      a L ≤ ndA5ReferenceAbsorbBar B Cband := by
    intro L _hL
    exact (hcellPacket L).2.2.2.2
  have hlocal : ∀ L ∈ (Finset.univ : Finset
      {L // L ∈ ndA5TerminalTotals B Cband n.1}),
      |Y L - q L * R L| ≤ q L * (e L + a L * R L) := by
    intro L _hL
    have hpacket := hcellPacket L
    have hdesc :=
      abs_sum_ndA5FlatTerminalAtomNominalIdealMass_fixedCell_sub_syrac_le_fm1
        (E := E) n L ht2 lost facts.schedule.one_le_B hlogB hcount hFM1
        hschedule.1 htimePacket.1 hpacket.1 hpacket.2.1
        hpacket.2.2.2.1
    dsimp only at hdesc
    rw [← ndPMFWeightedExpectation_ndA5FixedCellFlatReference_low hmnu]
      at hdesc
    dsimp only [Y, q, R, e, a, m, nu,
      ndA5FlatReferenceNonproportionalError]
    convert hdesc using 1; ring
  have habsorb :=
    abs_sum_sub_sum_mul_le_trueAbsorb
      (Finset.univ : Finset
        {L // L ∈ ndA5TerminalTotals B Cband n.1})
      Y q R e a (ndA5ReferenceAbsorbBar B Cband)
      hY ha0 haBar hschedule.2.2.2.1 hlocal
  have href :
      (∑ L : {L // L ∈ ndA5TerminalTotals B Cband n.1}, q L * R L) =
        ndA5FlatReferenceFixedTimeProfile B m branch Cband j E n := by
    simpa only [q, R, m, nu,
      ndA5FlatReferenceFixedTimeProfile] using
        (sum_ndA5TerminalTotals_flatReference_eq_lowProfile
          facts.schedule.one_le_B hlogB ht2 hmnu
            (m := m) (branch := branch) (j := j) (E := E))
  have he0 : 0 ≤ ndA5FlatReferenceNonproportionalError m Cfm1 := by
    unfold ndA5FlatReferenceNonproportionalError
    have hm0 : (0 : ℝ) < m := by
      exact_mod_cast (by omega : 0 < m)
    positivity
  have herr :
      (∑ L : {L // L ∈ ndA5TerminalTotals B Cband n.1}, q L * e L) ≤
        ndA5FlatReferenceNonproportionalError m Cfm1 := by
    simpa only [q, e, nu] using
      sum_terminal_endpointMass_mul_le nu
        (ndA5TerminalTotals B Cband n.1)
        (ndA5FlatReferenceNonproportionalError m Cfm1) he0
  rw [href] at habsorb
  simpa only [Y, m, ndA5FlatNominalFixedTimeMass] using
    habsorb.trans (by nlinarith)

end
end ND
end Erdos1135
