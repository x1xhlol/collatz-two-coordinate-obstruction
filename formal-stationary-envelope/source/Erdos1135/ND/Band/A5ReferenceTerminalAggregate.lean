import Erdos1135.ND.Band.A5ReferenceFixedTimeAbsorption
import Erdos1135.ND.Band.A5TerminalAtomReconstruction
import Erdos1135.ND.Band.A5PhysicalWindowCard

/-!
# Whole-band A5 reference aggregation

This leaf sums the checked fixed-time true-absorption bounds over the physical
time window.  The actual nominal mass is capped only after summing all times,
so the proportional row remains free of a tube-width factor.  The physical
time count is charged only to the FM1 and absolute-tail rows.
-/

namespace Erdos1135
namespace ND

open Tao
open scoped BigOperators

noncomputable section

/-- Common endpoint kernel used by both physical reference profiles. -/
def ndA5ReferenceEndpointKernel (m M : ℕ) : ℝ :=
  (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
    ((3 : ℝ) ^ m / (M : ℝ))

/-- The whole-band harmonic physical reference profile. -/
def ndA5HarmonicReferencePhysicalProfile
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) : ℝ :=
  let z := ndA5BandLower B branch j
  let W := ndA5TubeWidth B C
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  ∑ M ∈ Tao.taoSection5EPrime B E,
    ndA5ReferenceEndpointKernel m M *
      ((∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
          ∑ r ∈ Finset.range 2,
            ndA5NominalStrictBandRawQTerm B branch
              (ndA5PhysicalPhase z M) W nu r) / H)

/-- The whole-band flat physical reference profile.  Its exponential remains
inside the named strict raw-Q summand. -/
def ndA5FlatReferencePhysicalProfile
    (B m : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) : ℝ :=
  let z := ndA5BandLower B branch j
  let W := ndA5TubeWidth B C
  let card := ((ndA5OddBand B branch j).card : ℝ)
  ∑ M ∈ Tao.taoSection5EPrime B E,
    ndA5ReferenceEndpointKernel m M *
      ((z / card) *
        ∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
          ∑ r ∈ Finset.range 2,
            ndA5NominalStrictBandFlatRawQTerm B branch
              (ndA5PhysicalPhase z M) W nu r)

/-- Summing the fixed-time harmonic references gives the exact physical
profile; this is a signed reindex and reassociation only. -/
theorem sum_ndA5HarmonicReferenceFixedTimeProfile_eq_physicalProfile
    {B m : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n) :
    (∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ndA5HarmonicReferenceFixedTimeProfile B m branch C j E n) =
      ndA5HarmonicReferencePhysicalProfile B m branch C j E := by
  classical
  let z := ndA5BandLower B branch j
  let W := ndA5TubeWidth B C
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  let P (M nu : ℕ) : ℝ :=
    ∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandRawQTerm B branch
        (ndA5PhysicalPhase z M) W nu r
  simp only [ndA5HarmonicReferenceFixedTimeProfile]
  change
    (∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
      ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((3 : ℝ) ^ m / ((M : ℝ) * H)) *
            P M (n.1 - Tao.taoSection5M0 B))) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _hM
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  have hreindex := sum_ndA5PaddedBandWindow_eq_physicalNuWindow
    (B := B) (branch := branch) (C := C) (j := j) htime (P M)
  rw [hreindex]
  unfold ndA5ReferenceEndpointKernel
  dsimp only [z, W, H, P]
  ring

/-- Summing the fixed-time flat references gives the exact physical profile,
without moving the exponential out of its original raw-Q term. -/
theorem sum_ndA5FlatReferenceFixedTimeProfile_eq_physicalProfile
    {B m : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n) :
    (∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ndA5FlatReferenceFixedTimeProfile B m branch C j E n) =
      ndA5FlatReferencePhysicalProfile B m branch C j E := by
  classical
  let z := ndA5BandLower B branch j
  let W := ndA5TubeWidth B C
  let card := ((ndA5OddBand B branch j).card : ℝ)
  let P (M nu : ℕ) : ℝ :=
    ∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandFlatRawQTerm B branch
        (ndA5PhysicalPhase z M) W nu r
  simp only [ndA5FlatReferenceFixedTimeProfile]
  change
    (∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
      ∑ M ∈ Tao.taoSection5EPrime B E,
        (Tao.syracPMF m (M : ZMod (3 ^ m))).toReal *
          (((z * (3 : ℝ) ^ m) / ((M : ℝ) * card)) *
            P M (n.1 - Tao.taoSection5M0 B))) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _hM
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  have hreindex := sum_ndA5PaddedBandWindow_eq_physicalNuWindow
    (B := B) (branch := branch) (C := C) (j := j) htime (P M)
  rw [hreindex]
  unfold ndA5ReferenceEndpointKernel
  dsimp only [z, W, card, P]
  ring

private theorem sum_fixedTimeMass_eq_harmonicTerminalAtoms
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ} :
    (∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ndA5HarmonicNominalFixedTimeMass B branch C j E n) =
      ∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomNominalIdealMass i := by
  rw [sum_ndA5TerminalAtomIndex_eq_fixedCells]
  rfl

private theorem sum_fixedTimeMass_eq_flatTerminalAtoms
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ} :
    (∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ndA5FlatNominalFixedTimeMass B branch C j E n) =
      ∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5FlatTerminalAtomNominalIdealMass i := by
  rw [sum_ndA5TerminalAtomIndex_eq_fixedCells]
  rfl

private theorem card_paddedBandWindow_eq_physicalNuWindow
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n) :
    ((ndA5PaddedBandWindow B branch C j).card : ℝ) =
      ((ndA5PhysicalNuWindow B branch C j).card : ℝ) := by
  have h := sum_ndA5PaddedBandWindow_eq_physicalNuWindow
    (B := B) (branch := branch) (C := C) (j := j)
      htime (fun _ => (1 : ℝ))
  simpa using h

private theorem abs_sum_fixedTime_sub_reference_le
    {ι : Type*} [Fintype ι] (Y R : ι → ℝ)
    (aBar e : ℝ)
    (hpoint : ∀ i : ι,
      |Y i - R i| ≤ 2 * aBar * Y i + 2 * e) :
    |(∑ i, Y i) - ∑ i, R i| ≤
      2 * aBar * (∑ i, Y i) + 2 * (Fintype.card ι : ℝ) * e := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (Y i - R i)| ≤ ∑ i, |Y i - R i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (2 * aBar * Y i + 2 * e) :=
      Finset.sum_le_sum fun i _hi => hpoint i
    _ = 2 * aBar * (∑ i, Y i) + 2 * (Fintype.card ι : ℝ) * e := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp
      ring

/-- Paired finite whole-band absorption.  The proportional row uses the
complete nominal cap once; only nonproportional rows pay the physical-time
bound `7*W`. -/
theorem abs_sum_ndA5TerminalAtomNominalIdealMass_sub_referenceProfiles_le
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {Cband : ℝ} {j : ℕ} {E : Set ℕ}
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hCband : (1 / 2 : ℝ) ≤ Cband)
    (hpadding : 3 * ndA5TubeWidth B Cband ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch)
    (hdiam : ∀ n ∈ ndA5PaddedBandWindow B branch Cband j,
      ∀ n' ∈ ndA5PaddedBandWindow B branch Cband j,
        n ≤ n' → n' - n ≤ Tao.taoSection5M0 B)
    {Cfm1 : ℝ} (hCfm1 : 0 ≤ Cfm1)
    (hFM1 : ndSection7ConditionedFM1NatAt 11
      ((771 / 100 : ℝ) * Cband) Cfm1)
    (hschedule : NDA5ReferenceTerminalCellPacketAt B Cband) :
    let m := ndA5ReferenceLevel B
    let W := ndA5TubeWidth B Cband
    let cap := 1 + 11 * (B : ℝ) ^ (-(9 / 10 : ℝ))
    (|(∑ i : NDA5TerminalAtomIndex B branch Cband j E,
          ndA5HarmonicTerminalAtomNominalIdealMass i) -
        ndA5HarmonicReferencePhysicalProfile B m branch Cband j E| ≤
      2 * ndA5ReferenceAbsorbBar B Cband * cap +
        14 * W * ndA5HarmonicReferenceNonproportionalError m Cfm1) ∧
    (|(∑ i : NDA5TerminalAtomIndex B branch Cband j E,
          ndA5FlatTerminalAtomNominalIdealMass i) -
        ndA5FlatReferencePhysicalProfile B m branch Cband j E| ≤
      2 * ndA5ReferenceAbsorbBar B Cband * cap +
        14 * W * ndA5FlatReferenceNonproportionalError m Cfm1) := by
  classical
  dsimp only
  let m := ndA5ReferenceLevel B
  let W := ndA5TubeWidth B Cband
  let cap := 1 + 11 * (B : ℝ) ^ (-(9 / 10 : ℝ))
  let J := ndA5PaddedBandWindow B branch Cband j
  let YH : {n // n ∈ J} → ℝ := fun n =>
    ndA5HarmonicNominalFixedTimeMass B branch Cband j E n
  let YF : {n // n ∈ J} → ℝ := fun n =>
    ndA5FlatNominalFixedTimeMass B branch Cband j E n
  let RH : {n // n ∈ J} → ℝ := fun n =>
    ndA5HarmonicReferenceFixedTimeProfile B m branch Cband j E n
  let RF : {n // n ∈ J} → ℝ := fun n =>
    ndA5FlatReferenceFixedTimeProfile B m branch Cband j E n
  let eH := ndA5HarmonicReferenceNonproportionalError m Cfm1
  let eF := ndA5FlatReferenceNonproportionalError m Cfm1
  have hcount : 0 < ndA5BandCount B branch := Nat.zero_lt_of_lt hj
  have ht2 (n : {n // n ∈ J}) : NDA5T2ScaleFacts B n.1 Cband := by
    exact ndA5PaddedBandWindow_t2_of_guards
      facts.schedule.one_le_B hlogB hpadding hj n.2
  have htime : ∀ n ∈ J, Tao.taoSection5M0 B < n := by
    intro n hn
    have hnu := (ndA5PaddedBandWindow_t2_of_guards
      facts.schedule.one_le_B hlogB hpadding hj hn).nu_pos
    omega
  have hcaps := ndA5NominalTerminalIdealMass_sums_le_commonCap
    (E := E) facts hlogB hcount
      (fun i : NDA5TerminalAtomIndex B branch Cband j E => by
        simpa only [J] using ht2 i.1)
      htime hdiam
  have hbar0 : 0 ≤ ndA5ReferenceAbsorbBar B Cband := by
    have h := hschedule
    rw [NDA5ReferenceTerminalCellPacketAt] at h
    exact h.2.2.1
  have heH0 : 0 ≤ eH := by
    dsimp [eH, ndA5HarmonicReferenceNonproportionalError, m]
    have hm0 : (0 : ℝ) < ndA5ReferenceLevel B := by
      have h := hschedule
      rw [NDA5ReferenceTerminalCellPacketAt] at h
      exact_mod_cast (by omega : 0 < ndA5ReferenceLevel B)
    positivity
  have heF0 : 0 ≤ eF := by
    dsimp [eF, ndA5FlatReferenceNonproportionalError, m]
    have hm0 : (0 : ℝ) < ndA5ReferenceLevel B := by
      have h := hschedule
      rw [NDA5ReferenceTerminalCellPacketAt] at h
      exact_mod_cast (by omega : 0 < ndA5ReferenceLevel B)
    positivity
  have hcardPhysical := ndA5PhysicalNuWindow_card_le_seven_mul_width
    facts.schedule.one_le_B hlogB hCband hpadding hj
  have hcard := card_paddedBandWindow_eq_physicalNuWindow htime
  have hcardJ : (Fintype.card {n // n ∈ J} : ℝ) ≤ 7 * W := by
    have hbound : ((ndA5PaddedBandWindow B branch Cband j).card : ℝ) ≤
        7 * ndA5TubeWidth B Cband := by
      calc
        ((ndA5PaddedBandWindow B branch Cband j).card : ℝ) =
            ((ndA5PhysicalNuWindow B branch Cband j).card : ℝ) := hcard
        _ ≤ 7 * ndA5TubeWidth B Cband := hcardPhysical
    simpa only [J, W, Fintype.card_coe] using hbound
  have hpointH : ∀ n : {n // n ∈ J},
      |YH n - RH n| ≤
        2 * ndA5ReferenceAbsorbBar B Cband * YH n + 2 * eH := by
    intro n
    simpa only [YH, RH, eH, m, J] using
      abs_ndA5HarmonicNominalFixedTimeMass_sub_reference_le_trueAbsorb
        facts lost hlogB hcount hCfm1 hFM1 hschedule n (ht2 n)
  have hpointF : ∀ n : {n // n ∈ J},
      |YF n - RF n| ≤
        2 * ndA5ReferenceAbsorbBar B Cband * YF n + 2 * eF := by
    intro n
    simpa only [YF, RF, eF, m, J] using
      abs_ndA5FlatNominalFixedTimeMass_sub_reference_le_trueAbsorb
        facts lost hlogB hcount hCfm1 hFM1 hschedule n (ht2 n)
  have hsumH := abs_sum_fixedTime_sub_reference_le YH RH
    (ndA5ReferenceAbsorbBar B Cband) eH hpointH
  have hsumF := abs_sum_fixedTime_sub_reference_le YF RF
    (ndA5ReferenceAbsorbBar B Cband) eF hpointF
  have hmassH : (∑ n, YH n) ≤ cap := by
    simpa only [YH, J, cap, sum_fixedTimeMass_eq_harmonicTerminalAtoms]
      using hcaps.1
  have hmassF : (∑ n, YF n) ≤ cap := by
    simpa only [YF, J, cap, sum_fixedTimeMass_eq_flatTerminalAtoms]
      using hcaps.2
  have hpropH :
      2 * ndA5ReferenceAbsorbBar B Cband * (∑ n, YH n) ≤
        2 * ndA5ReferenceAbsorbBar B Cband * cap := by
    exact mul_le_mul_of_nonneg_left hmassH (mul_nonneg (by norm_num) hbar0)
  have hpropF :
      2 * ndA5ReferenceAbsorbBar B Cband * (∑ n, YF n) ≤
        2 * ndA5ReferenceAbsorbBar B Cband * cap := by
    exact mul_le_mul_of_nonneg_left hmassF (mul_nonneg (by norm_num) hbar0)
  have htailH :
      2 * (Fintype.card {n // n ∈ J} : ℝ) * eH ≤ 14 * W * eH := by
    have := mul_le_mul_of_nonneg_right hcardJ heH0
    nlinarith
  have htailF :
      2 * (Fintype.card {n // n ∈ J} : ℝ) * eF ≤ 14 * W * eF := by
    have := mul_le_mul_of_nonneg_right hcardJ heF0
    nlinarith
  have hrefH :=
    sum_ndA5HarmonicReferenceFixedTimeProfile_eq_physicalProfile
      (B := B) (m := m) (branch := branch) (C := Cband)
      (j := j) (E := E) htime
  have hrefF :=
    sum_ndA5FlatReferenceFixedTimeProfile_eq_physicalProfile
      (B := B) (m := m) (branch := branch) (C := Cband)
      (j := j) (E := E) htime
  have hactualH :=
    sum_fixedTimeMass_eq_harmonicTerminalAtoms
      (B := B) (branch := branch) (C := Cband) (j := j) (E := E)
  have hactualF :=
    sum_fixedTimeMass_eq_flatTerminalAtoms
      (B := B) (branch := branch) (C := Cband) (j := j) (E := E)
  constructor
  · rw [← hactualH, ← hrefH]
    simpa only [YH, RH, J, m, W, cap, eH] using
      hsumH.trans (by linarith)
  · rw [← hactualF, ← hrefF]
    simpa only [YF, RF, J, m, W, cap, eF] using
      hsumF.trans (by linarith)

end
end ND
end Erdos1135
