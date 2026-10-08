import Erdos1135.Tao.Section5.PassTotalizerBridge

/-!
# Common-target natural passage totalizer

This neutral ND leaf maps an arbitrary law on Tao's odd-source type to the
finite passage carrier at one common natural target.  Pairwise genuine-event
comparison is preserved by complementing finite output events containing the
artificial no-hit value `1`; finite Hahn is then applied exactly once.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Totalize first passage at the common natural target `B` for an arbitrary
law on Tao's odd-source type. -/
noncomputable def ndTotalizedPassLaw
    (B : ℕ) (hB : 1 ≤ B) (μ : PMF Tao.TaoOddNat) :
    PMF {M : ℕ // M ≤ B} :=
  μ.map fun N ↦ Tao.syracusePassLocationOrOne B N.1 hB

/-- Away from the artificial value `1`, totalized event mass is exactly the
genuine first-passage mass.  The source carrier need not be finite. -/
theorem ndTotalizedPassLaw_eventMass_eq_genuine_of_one_not_mem
    {B : ℕ} (hB : 1 ≤ B) (μ : PMF Tao.TaoOddNat)
    (A : Set {M : ℕ // M ≤ B})
    (hone : (⟨1, hB⟩ : {M : ℕ // M ≤ B}) ∉ A) :
    Tao.pmfProb (ndTotalizedPassLaw B hB μ) A =
      (μ.toOuterMeasure
        (Tao.taoSection5PassEvent B (Subtype.val '' A))).toReal := by
  rw [ndTotalizedPassLaw, Tao.pmfProb_eq_toOuterMeasure_toReal,
    PMF.toOuterMeasure_map_apply]
  apply congrArg (fun S : Set Tao.TaoOddNat ↦ (μ.toOuterMeasure S).toReal)
  ext N
  change Tao.syracusePassLocationOrOne B N.1 hB ∈ A ↔
    N ∈ Tao.taoSection5PassEvent B (Subtype.val '' A)
  exact
    (Tao.mem_taoSection5PassEvent_subtypeVal_image_iff_totalized_of_one_not_mem
      hB N A hone).symm

/-- A uniform genuine passage-event discrepancy gives the same discrepancy
for every totalized output event.  Events containing `1` are handled through
their complement on the finite output carrier. -/
theorem abs_pmfProb_ndTotalizedPassLaw_sub_le_of_genuine
    {B : ℕ} (hB : 1 ≤ B) (μ ν : PMF Tao.TaoOddNat) {ε : ℝ}
    (hgen : ∀ E : Set ℕ,
      |(μ.toOuterMeasure (Tao.taoSection5PassEvent B E)).toReal -
        (ν.toOuterMeasure (Tao.taoSection5PassEvent B E)).toReal| ≤ ε)
    (A : Set {M : ℕ // M ≤ B}) :
    |Tao.pmfProb (ndTotalizedPassLaw B hB μ) A -
      Tao.pmfProb (ndTotalizedPassLaw B hB ν) A| ≤ ε := by
  classical
  by_cases hone : (⟨1, hB⟩ : {M : ℕ // M ≤ B}) ∈ A
  · have honeCompl :
        (⟨1, hB⟩ : {M : ℕ // M ≤ B}) ∉ Aᶜ := by
      simpa using hone
    have heqμ :
        Tao.pmfProb (ndTotalizedPassLaw B hB μ) Aᶜ =
          (μ.toOuterMeasure
            (Tao.taoSection5PassEvent B (Subtype.val '' Aᶜ))).toReal :=
      ndTotalizedPassLaw_eventMass_eq_genuine_of_one_not_mem
        hB μ Aᶜ honeCompl
    have heqν :
        Tao.pmfProb (ndTotalizedPassLaw B hB ν) Aᶜ =
          (ν.toOuterMeasure
            (Tao.taoSection5PassEvent B (Subtype.val '' Aᶜ))).toReal :=
      ndTotalizedPassLaw_eventMass_eq_genuine_of_one_not_mem
        hB ν Aᶜ honeCompl
    have hcomplμ :
        Tao.pmfProb (ndTotalizedPassLaw B hB μ) A =
          1 - Tao.pmfProb (ndTotalizedPassLaw B hB μ) Aᶜ := by
      simpa only [compl_compl] using
        (Tao.pmfProb_compl (ndTotalizedPassLaw B hB μ) Aᶜ)
    have hcomplν :
        Tao.pmfProb (ndTotalizedPassLaw B hB ν) A =
          1 - Tao.pmfProb (ndTotalizedPassLaw B hB ν) Aᶜ := by
      simpa only [compl_compl] using
        (Tao.pmfProb_compl (ndTotalizedPassLaw B hB ν) Aᶜ)
    calc
      |Tao.pmfProb (ndTotalizedPassLaw B hB μ) A -
          Tao.pmfProb (ndTotalizedPassLaw B hB ν) A| =
          |(1 - Tao.pmfProb (ndTotalizedPassLaw B hB μ) Aᶜ) -
            (1 - Tao.pmfProb (ndTotalizedPassLaw B hB ν) Aᶜ)| := by
        rw [hcomplμ, hcomplν]
      _ = |Tao.pmfProb (ndTotalizedPassLaw B hB μ) Aᶜ -
          Tao.pmfProb (ndTotalizedPassLaw B hB ν) Aᶜ| := by
        rw [show
          (1 - Tao.pmfProb (ndTotalizedPassLaw B hB μ) Aᶜ) -
              (1 - Tao.pmfProb (ndTotalizedPassLaw B hB ν) Aᶜ) =
            -(Tao.pmfProb (ndTotalizedPassLaw B hB μ) Aᶜ -
              Tao.pmfProb (ndTotalizedPassLaw B hB ν) Aᶜ) by ring,
          abs_neg]
      _ = |(μ.toOuterMeasure
              (Tao.taoSection5PassEvent B (Subtype.val '' Aᶜ))).toReal -
            (ν.toOuterMeasure
              (Tao.taoSection5PassEvent B (Subtype.val '' Aᶜ))).toReal| := by
        rw [heqμ, heqν]
      _ ≤ ε := hgen (Subtype.val '' Aᶜ)
  · have heqμ :=
      ndTotalizedPassLaw_eventMass_eq_genuine_of_one_not_mem hB μ A hone
    have heqν :=
      ndTotalizedPassLaw_eventMass_eq_genuine_of_one_not_mem hB ν A hone
    rw [heqμ, heqν]
    exact hgen (Subtype.val '' A)

/-- Finite Hahn contributes the single factor two after pairwise complement
totalization. -/
theorem taoTV_ndTotalizedPassLaw_le_two_mul_of_genuine
    {B : ℕ} (hB : 1 ≤ B) (μ ν : PMF Tao.TaoOddNat) {ε : ℝ}
    (hgen : ∀ E : Set ℕ,
      |(μ.toOuterMeasure (Tao.taoSection5PassEvent B E)).toReal -
        (ν.toOuterMeasure (Tao.taoSection5PassEvent B E)).toReal| ≤ ε) :
    Tao.taoTV (ndTotalizedPassLaw B hB μ)
        (ndTotalizedPassLaw B hB ν) ≤ 2 * ε := by
  apply Tao.taoTV_le_two_mul_of_event_discrepancy
  exact abs_pmfProb_ndTotalizedPassLaw_sub_le_of_genuine hB μ ν hgen

end
end ND
end Erdos1135
