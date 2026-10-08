import Erdos1135.Tao.Section5.IdealPassageCenter
import Erdos1135.Tao.Section5.GenuinePassageApprox
import Erdos1135.Tao.Section5.PassTotalizerBridge

/-!
# Section 5 Branch Passage-Event Comparison

This leaf cancels the branch-independent Common-Z center before comparing the
two Section 5 source branches. It first obtains a signed comparison of genuine
passage masses. Bounded endpoint complements then remove the artificial no-hit
mass from the corresponding totalized passage-law comparison.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- The upper genuine passage mass pays one genuine-event defect, while both
ideal sums pay their branch-independent center error. -/
theorem taoSection5_genuinePassageMass_sub_genuinePassageMass_le_capped_of_mixing
    {A B : ℕ} {Cmix : ℝ}
    (partitionFacts : TaoSection5PassEventPartitionFacts B)
    (affineFacts : TaoSection5AffineSourceScaleFacts B)
    (boundaryFacts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (failureFacts : TaoSection5PassTypicalFailureFacts B)
    (upper lower : TaoSection5SourceBranch)
    (Aevent : Set {M : ℕ // M ≤ B})
    (hmix : syracFineScaleMixingAt A Cmix) (hCmix : 0 ≤ Cmix)
    (hratioUpper :
      (Fintype.card {n // n ∈ taoSection5PassTimes B upper} : ℝ) /
          logFinsetMass
            (oddLogWindow (taoSection5SourceLo B upper)
              (taoSection5SourceHi B upper)) ≤ 9)
    (hratioLower :
      (Fintype.card {n // n ∈ taoSection5PassTimes B lower} : ℝ) /
          logFinsetMass
            (oddLogWindow (taoSection5SourceLo B lower)
              (taoSection5SourceHi B lower)) ≤ 9) :
    let hmassUpper := boundaryFacts.residue.mass_pos upper
    let hmassLower := boundaryFacts.residue.mass_pos lower
    let E := Subtype.val '' Aevent
    let Gupper :=
      ((oddLogWindowOddNatPMF
        (taoSection5SourceLo B upper)
        (taoSection5SourceHi B upper) hmassUpper).toOuterMeasure
          (taoSection5PassEvent B E)).toReal
    let Glower :=
      ((oddLogWindowOddNatPMF
        (taoSection5SourceLo B lower)
        (taoSection5SourceHi B lower) hmassLower).toOuterMeasure
          (taoSection5PassEvent B E)).toReal
    Gupper - Glower ≤
      32092 * taoSection5PowerInteriorDelta B +
        90 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
        1840000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
        (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
  classical
  dsimp only
  let E : Set ℕ := Subtype.val '' Aevent
  let hmassUpper := boundaryFacts.residue.mass_pos upper
  let hmassLower := boundaryFacts.residue.mass_pos lower
  let Gupper :=
    ((oddLogWindowOddNatPMF
      (taoSection5SourceLo B upper)
      (taoSection5SourceHi B upper) hmassUpper).toOuterMeasure
        (taoSection5PassEvent B E)).toReal
  let Glower :=
    ((oddLogWindowOddNatPMF
      (taoSection5SourceLo B lower)
      (taoSection5SourceHi B lower) hmassLower).toOuterMeasure
        (taoSection5PassEvent B E)).toReal
  let Iupper :=
    ∑ i : TaoSection5ClosedAffineAtomIndex B upper E,
      taoSection5IdealAffineAtomMass hmassUpper i
  let Ilower :=
    ∑ i : TaoSection5ClosedAffineAtomIndex B lower E,
      taoSection5IdealAffineAtomMass hmassLower i
  let C := (2 / Real.log (4 / 3 : ℝ)) *
    taoSection5PayloadFreeCommonZ (taoSection5M0 B)
      (taoSection5EPrime B E)
  let e := 45 * taoSection5PowerInteriorDelta B +
    45 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
    920000 * Real.rpow (Real.log B) (-1 / 5 : ℝ)
  let g := 32002 * taoSection5PowerInteriorDelta B +
    (B : ℝ) ^ (-(4 / 5 : ℝ))
  change Gupper - Glower ≤
    32092 * taoSection5PowerInteriorDelta B +
      90 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
      1840000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
      (B : ℝ) ^ (-(4 / 5 : ℝ))
  have hcenterUpper : |Iupper - C| ≤ e := by
    simpa only [Iupper, C, e, E, hmassUpper] using
      (abs_taoSection5_idealAffineAtomSum_sub_two_div_log_mul_commonZ_le_capped_of_mixing
        boundaryFacts partitionFacts.lost failureFacts upper E hmix hCmix
        hratioUpper)
  have hcenterLower : |Ilower - C| ≤ e := by
    simpa only [Ilower, C, e, E, hmassLower] using
      (abs_taoSection5_idealAffineAtomSum_sub_two_div_log_mul_commonZ_le_capped_of_mixing
        boundaryFacts partitionFacts.lost failureFacts lower E hmix hCmix
        hratioLower)
  have hgenuineUpper : 0 ≤ Gupper - Iupper ∧ Gupper - Iupper ≤ g := by
    simpa only [Gupper, Iupper, g, E, hmassUpper] using
      (taoSection5_genuinePassageMass_sub_idealSum_nonneg_le
        partitionFacts affineFacts boundaryFacts failureFacts upper E)
  have hgenuineLower : 0 ≤ Glower - Ilower ∧ Glower - Ilower ≤ g := by
    simpa only [Glower, Ilower, g, E, hmassLower] using
      (taoSection5_genuinePassageMass_sub_idealSum_nonneg_le
        partitionFacts affineFacts boundaryFacts failureFacts lower E)
  have hIlowerGlower : Ilower ≤ Glower :=
    sub_nonneg.mp hgenuineLower.1
  have hIupperC : Iupper - C ≤ e :=
    (abs_le.mp hcenterUpper).2
  have hCIlower : C - Ilower ≤ e := by
    calc
      C - Ilower ≤ |C - Ilower| := le_abs_self _
      _ = |Ilower - C| := abs_sub_comm _ _
      _ ≤ e := hcenterLower
  calc
    Gupper - Glower ≤ Gupper - Ilower :=
      sub_le_sub_left hIlowerGlower Gupper
    _ = ((Gupper - Iupper) + (Iupper - C)) + (C - Ilower) := by ring
    _ ≤ (g + e) + e :=
      add_le_add (add_le_add hgenuineUpper.2 hIupperC) hCIlower
    _ = 32092 * taoSection5PowerInteriorDelta B +
        90 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
        1840000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
        (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
      dsimp only [e, g]
      ring

/-- Applying the oriented genuine comparison in both directions gives a
uniform event discrepancy without an artificial no-hit term. -/
theorem abs_taoSection5_genuinePassageMass_sub_genuinePassageMass_le_capped_of_mixing
    {A B : ℕ} {Cmix : ℝ}
    (partitionFacts : TaoSection5PassEventPartitionFacts B)
    (affineFacts : TaoSection5AffineSourceScaleFacts B)
    (boundaryFacts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (failureFacts : TaoSection5PassTypicalFailureFacts B)
    (branch₁ branch₂ : TaoSection5SourceBranch)
    (Aevent : Set {M : ℕ // M ≤ B})
    (hmix : syracFineScaleMixingAt A Cmix) (hCmix : 0 ≤ Cmix)
    (hratio₁ :
      (Fintype.card {n // n ∈ taoSection5PassTimes B branch₁} : ℝ) /
          logFinsetMass
            (oddLogWindow (taoSection5SourceLo B branch₁)
              (taoSection5SourceHi B branch₁)) ≤ 9)
    (hratio₂ :
      (Fintype.card {n // n ∈ taoSection5PassTimes B branch₂} : ℝ) /
          logFinsetMass
            (oddLogWindow (taoSection5SourceLo B branch₂)
              (taoSection5SourceHi B branch₂)) ≤ 9) :
    let hmass₁ := boundaryFacts.residue.mass_pos branch₁
    let hmass₂ := boundaryFacts.residue.mass_pos branch₂
    let E := Subtype.val '' Aevent
    let G₁ :=
      ((oddLogWindowOddNatPMF
        (taoSection5SourceLo B branch₁)
        (taoSection5SourceHi B branch₁) hmass₁).toOuterMeasure
          (taoSection5PassEvent B E)).toReal
    let G₂ :=
      ((oddLogWindowOddNatPMF
        (taoSection5SourceLo B branch₂)
        (taoSection5SourceHi B branch₂) hmass₂).toOuterMeasure
          (taoSection5PassEvent B E)).toReal
    |G₁ - G₂| ≤
      32092 * taoSection5PowerInteriorDelta B +
        90 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
        1840000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
        (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
  dsimp only
  rw [abs_le]
  constructor
  · have hreverse :=
      taoSection5_genuinePassageMass_sub_genuinePassageMass_le_capped_of_mixing
        partitionFacts affineFacts boundaryFacts failureFacts branch₂ branch₁
        Aevent hmix hCmix hratio₂ hratio₁
    dsimp only at hreverse
    linarith
  · exact
      taoSection5_genuinePassageMass_sub_genuinePassageMass_le_capped_of_mixing
        partitionFacts affineFacts boundaryFacts failureFacts branch₁ branch₂
        Aevent hmix hCmix hratio₁ hratio₂

/-- On the bounded endpoint carrier, complementing an event containing `1`
turns it into an event where totalized and genuine masses agree. Therefore the
totalized branch discrepancy has the same bound as the genuine discrepancy,
with no no-hit error. -/
theorem abs_taoSection5_totalPassMass_sub_totalPassMass_le_capped_of_mixing
    {A B : ℕ} {Cmix : ℝ}
    (partitionFacts : TaoSection5PassEventPartitionFacts B)
    (affineFacts : TaoSection5AffineSourceScaleFacts B)
    (boundaryFacts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (failureFacts : TaoSection5PassTypicalFailureFacts B)
    (branch₁ branch₂ : TaoSection5SourceBranch)
    (Aevent : Set {M : ℕ // M ≤ B})
    (hmix : syracFineScaleMixingAt A Cmix) (hCmix : 0 ≤ Cmix)
    (hratio₁ :
      (Fintype.card {n // n ∈ taoSection5PassTimes B branch₁} : ℝ) /
          logFinsetMass
            (oddLogWindow (taoSection5SourceLo B branch₁)
              (taoSection5SourceHi B branch₁)) ≤ 9)
    (hratio₂ :
      (Fintype.card {n // n ∈ taoSection5PassTimes B branch₂} : ℝ) /
          logFinsetMass
            (oddLogWindow (taoSection5SourceLo B branch₂)
              (taoSection5SourceHi B branch₂)) ≤ 9) :
    let hB := boundaryFacts.residue.one_le_B
    let hmass₁ := boundaryFacts.residue.mass_pos branch₁
    let hmass₂ := boundaryFacts.residue.mass_pos branch₂
    let T₁ := pmfProb
      (syracusePassLocationLaw
        (taoSection5SourceLo B branch₁)
        (taoSection5SourceHi B branch₁) B hB hmass₁) Aevent
    let T₂ := pmfProb
      (syracusePassLocationLaw
        (taoSection5SourceLo B branch₂)
        (taoSection5SourceHi B branch₂) B hB hmass₂) Aevent
    |T₁ - T₂| ≤
      32092 * taoSection5PowerInteriorDelta B +
        90 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
        1840000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
        (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
  classical
  dsimp only
  let hB := boundaryFacts.residue.one_le_B
  let hmass₁ := boundaryFacts.residue.mass_pos branch₁
  let hmass₂ := boundaryFacts.residue.mass_pos branch₂
  let T₁ := fun event : Set {M : ℕ // M ≤ B} =>
    pmfProb
      (syracusePassLocationLaw
        (taoSection5SourceLo B branch₁)
        (taoSection5SourceHi B branch₁) B hB hmass₁) event
  let T₂ := fun event : Set {M : ℕ // M ≤ B} =>
    pmfProb
      (syracusePassLocationLaw
        (taoSection5SourceLo B branch₂)
        (taoSection5SourceHi B branch₂) B hB hmass₂) event
  let G₁ := fun event : Set {M : ℕ // M ≤ B} =>
    ((oddLogWindowOddNatPMF
      (taoSection5SourceLo B branch₁)
      (taoSection5SourceHi B branch₁) hmass₁).toOuterMeasure
        (taoSection5PassEvent B (Subtype.val '' event))).toReal
  let G₂ := fun event : Set {M : ℕ // M ≤ B} =>
    ((oddLogWindowOddNatPMF
      (taoSection5SourceLo B branch₂)
      (taoSection5SourceHi B branch₂) hmass₂).toOuterMeasure
        (taoSection5PassEvent B (Subtype.val '' event))).toReal
  let eps := 32092 * taoSection5PowerInteriorDelta B +
    90 * (Cmix / (taoSection5M0 B : ℝ) ^ A) +
    1840000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) +
    (B : ℝ) ^ (-(4 / 5 : ℝ))
  change |T₁ Aevent - T₂ Aevent| ≤ eps
  have hgenuine (event : Set {M : ℕ // M ≤ B}) :
      |G₁ event - G₂ event| ≤ eps := by
    simpa only [G₁, G₂, eps, hmass₁, hmass₂] using
      (abs_taoSection5_genuinePassageMass_sub_genuinePassageMass_le_capped_of_mixing
        partitionFacts affineFacts boundaryFacts failureFacts branch₁ branch₂
        event hmix hCmix hratio₁ hratio₂)
  by_cases hone : (⟨1, hB⟩ : {M : ℕ // M ≤ B}) ∈ Aevent
  · have honeCompl :
        (⟨1, hB⟩ : {M : ℕ // M ≤ B}) ∉ Aeventᶜ := by
      simpa using hone
    have heq₁ : T₁ Aeventᶜ = G₁ Aeventᶜ := by
      simpa only [T₁, G₁, hB, hmass₁] using
        (taoSection5_totalPassMass_eq_genuinePassageMass_of_one_not_mem
          hB hmass₁ Aeventᶜ honeCompl)
    have heq₂ : T₂ Aeventᶜ = G₂ Aeventᶜ := by
      simpa only [T₂, G₂, hB, hmass₂] using
        (taoSection5_totalPassMass_eq_genuinePassageMass_of_one_not_mem
          hB hmass₂ Aeventᶜ honeCompl)
    have hcompl₁ : T₁ Aevent = 1 - T₁ Aeventᶜ := by
      simpa only [T₁, compl_compl] using
        (pmfProb_compl
          (syracusePassLocationLaw
            (taoSection5SourceLo B branch₁)
            (taoSection5SourceHi B branch₁) B hB hmass₁) Aeventᶜ)
    have hcompl₂ : T₂ Aevent = 1 - T₂ Aeventᶜ := by
      simpa only [T₂, compl_compl] using
        (pmfProb_compl
          (syracusePassLocationLaw
            (taoSection5SourceLo B branch₂)
            (taoSection5SourceHi B branch₂) B hB hmass₂) Aeventᶜ)
    calc
      |T₁ Aevent - T₂ Aevent| =
          |(1 - T₁ Aeventᶜ) - (1 - T₂ Aeventᶜ)| := by
            rw [hcompl₁, hcompl₂]
      _ = |T₁ Aeventᶜ - T₂ Aeventᶜ| := by
        rw [show (1 - T₁ Aeventᶜ) - (1 - T₂ Aeventᶜ) =
          -(T₁ Aeventᶜ - T₂ Aeventᶜ) by ring, abs_neg]
      _ = |G₁ Aeventᶜ - G₂ Aeventᶜ| := by rw [heq₁, heq₂]
      _ ≤ eps := hgenuine Aeventᶜ
  · have heq₁ : T₁ Aevent = G₁ Aevent := by
      simpa only [T₁, G₁, hB, hmass₁] using
        (taoSection5_totalPassMass_eq_genuinePassageMass_of_one_not_mem
          hB hmass₁ Aevent hone)
    have heq₂ : T₂ Aevent = G₂ Aevent := by
      simpa only [T₂, G₂, hB, hmass₂] using
        (taoSection5_totalPassMass_eq_genuinePassageMass_of_one_not_mem
          hB hmass₂ Aevent hone)
    rw [heq₁, heq₂]
    exact hgenuine Aevent

end

end Tao
end Erdos1135
