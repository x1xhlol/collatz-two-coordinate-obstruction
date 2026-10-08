import Erdos1135.Tao.Section3
import Erdos1135.Tao.Probability.LogSupportPerturbation

/-!
# Section 3 Log-Window Source Perturbation

This leaf converts a uniform event discrepancy between two normalized
logarithmic source windows into no-hit and totalized passage-law bounds. It
keeps the endpoint geometry abstract so the later real-floor boundary leaf can
supply the sharp `O(1 / (B * log B))` estimate without reopening Section 5.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Uniform event discrepancy between two normalized odd logarithmic source
windows. Both probabilities are stated on ambient naturals, avoiding a false
identification of their finite subtype carriers. -/
def TaoLogWindowSourcePerturbation
    (lo₁ hi₁ lo₂ hi₂ : ℕ) (err : ℝ) : Prop :=
  ∀ E : Set ℕ,
    |logFinsetProb (oddLogWindow lo₁ hi₁) E -
        logFinsetProb (oddLogWindow lo₂ hi₂) E| ≤ err

/-- Build the Section 3 source perturbation socket from a weighted
symmetric-difference estimate and the two positive normalizing masses. -/
theorem TaoLogWindowSourcePerturbation.of_symmDiffMass
    {lo₁ hi₁ lo₂ hi₂ : ℕ} {err : ℝ}
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂))
    (hbound :
      2 * logFinsetSymmDiffMass
          (oddLogWindow lo₁ hi₁) (oddLogWindow lo₂ hi₂) /
          min (logFinsetMass (oddLogWindow lo₁ hi₁))
            (logFinsetMass (oddLogWindow lo₂ hi₂)) ≤ err) :
    TaoLogWindowSourcePerturbation lo₁ hi₁ lo₂ hi₂ err := by
  intro E
  exact (abs_logFinsetProb_sub_le_two_symmDiffMass_div_min
    hmass₁ hmass₂ E).trans hbound

theorem TaoLogWindowSourcePerturbation.symm
    {lo₁ hi₁ lo₂ hi₂ : ℕ} {err : ℝ}
    (h : TaoLogWindowSourcePerturbation lo₁ hi₁ lo₂ hi₂ err) :
    TaoLogWindowSourcePerturbation lo₂ hi₂ lo₁ hi₁ err := by
  intro E
  simpa only [abs_sub_comm] using h E

/-- A source-window perturbation controls the discrepancy of any common
ambient event under the two finite source PMFs. -/
theorem abs_pmfProb_oddLogWindowPMF_sub_le_of_sourcePerturbation
    {lo₁ hi₁ lo₂ hi₂ : ℕ} {err : ℝ}
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂))
    (hperturb : TaoLogWindowSourcePerturbation lo₁ hi₁ lo₂ hi₂ err)
    (E : Set ℕ) :
    |pmfProb (oddLogWindowPMF lo₁ hi₁ hmass₁)
          {N | (N : ℕ) ∈ E} -
        pmfProb (oddLogWindowPMF lo₂ hi₂ hmass₂)
          {N | (N : ℕ) ∈ E}| ≤ err := by
  rw [pmfProb_oddLogWindowPMF, pmfProb_oddLogWindowPMF]
  exact hperturb E

/-- In particular, changing the source window perturbs the no-hit
probability by at most the same arbitrary-event error. -/
theorem abs_syracuseNoHitWindowProb_sub_le_of_sourcePerturbation
    {B lo₁ hi₁ lo₂ hi₂ : ℕ} {err : ℝ}
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂))
    (hperturb : TaoLogWindowSourcePerturbation lo₁ hi₁ lo₂ hi₂ err) :
    |syracuseNoHitWindowProb B lo₁ hi₁ hmass₁ -
        syracuseNoHitWindowProb B lo₂ hi₂ hmass₂| ≤ err := by
  exact abs_pmfProb_oddLogWindowPMF_sub_le_of_sourcePerturbation
    hmass₁ hmass₂ hperturb (syracuseNoHitAtMost B)

/-- Finite Hahn converts arbitrary source-event discrepancy into full-L1
distance between the corresponding totalized passage laws. The factor `2`
is the project's full-L1 convention, not a hidden half-TV normalization. -/
theorem taoTV_syracusePassLocationLaw_le_two_mul_of_sourcePerturbation
    {B lo₁ hi₁ lo₂ hi₂ : ℕ} {err : ℝ} (hB : 1 ≤ B)
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂))
    (hperturb : TaoLogWindowSourcePerturbation lo₁ hi₁ lo₂ hi₂ err) :
    taoTV (syracusePassLocationLaw lo₁ hi₁ B hB hmass₁)
        (syracusePassLocationLaw lo₂ hi₂ B hB hmass₂) ≤ 2 * err := by
  apply taoTV_le_two_mul_of_event_discrepancy
  intro A
  rw [pmfProb_syracusePassLocationLaw_preimage,
    pmfProb_syracusePassLocationLaw_preimage]
  exact abs_pmfProb_oddLogWindowPMF_sub_le_of_sourcePerturbation
    hmass₁ hmass₂ hperturb
      {N : ℕ | syracusePassLocationOrOne B N hB ∈ A}

/-- Transfer a two-window passage comparison across independent source-window
perturbations. Each endpoint branch pays one finite-Hahn factor `2`, and the
middle term is the original passage-law distance. -/
theorem taoTV_syracusePassLocationLaw_pair_le_of_sourcePerturbation
    {B rlo₁ rhi₁ nlo₁ nhi₁ nlo₂ nhi₂ rlo₂ rhi₂ : ℕ}
    {err₁ err₂ : ℝ} (hB : 1 ≤ B)
    (hrmass₁ : 0 < logFinsetMass (oddLogWindow rlo₁ rhi₁))
    (hnmass₁ : 0 < logFinsetMass (oddLogWindow nlo₁ nhi₁))
    (hnmass₂ : 0 < logFinsetMass (oddLogWindow nlo₂ nhi₂))
    (hrmass₂ : 0 < logFinsetMass (oddLogWindow rlo₂ rhi₂))
    (hperturb₁ :
      TaoLogWindowSourcePerturbation rlo₁ rhi₁ nlo₁ nhi₁ err₁)
    (hperturb₂ :
      TaoLogWindowSourcePerturbation rlo₂ rhi₂ nlo₂ nhi₂ err₂) :
    taoTV (syracusePassLocationLaw rlo₁ rhi₁ B hB hrmass₁)
        (syracusePassLocationLaw rlo₂ rhi₂ B hB hrmass₂) ≤
      2 * err₁ +
        taoTV (syracusePassLocationLaw nlo₁ nhi₁ B hB hnmass₁)
          (syracusePassLocationLaw nlo₂ nhi₂ B hB hnmass₂) +
        2 * err₂ := by
  let real₁ := syracusePassLocationLaw rlo₁ rhi₁ B hB hrmass₁
  let natural₁ := syracusePassLocationLaw nlo₁ nhi₁ B hB hnmass₁
  let natural₂ := syracusePassLocationLaw nlo₂ nhi₂ B hB hnmass₂
  let real₂ := syracusePassLocationLaw rlo₂ rhi₂ B hB hrmass₂
  have hleft : taoTV real₁ natural₁ ≤ 2 * err₁ :=
    taoTV_syracusePassLocationLaw_le_two_mul_of_sourcePerturbation
      hB hrmass₁ hnmass₁ hperturb₁
  have hright : taoTV natural₂ real₂ ≤ 2 * err₂ := by
    rw [taoTV_comm]
    exact taoTV_syracusePassLocationLaw_le_two_mul_of_sourcePerturbation
      hB hrmass₂ hnmass₂ hperturb₂
  calc
    taoTV real₁ real₂ ≤ taoTV real₁ natural₁ + taoTV natural₁ real₂ :=
      taoTV_triangle real₁ natural₁ real₂
    _ ≤ 2 * err₁ + taoTV natural₁ real₂ :=
      add_le_add hleft (le_refl _)
    _ ≤ 2 * err₁ + (taoTV natural₁ natural₂ + taoTV natural₂ real₂) :=
      add_le_add (le_refl _) (taoTV_triangle natural₁ natural₂ real₂)
    _ ≤ 2 * err₁ + (taoTV natural₁ natural₂ + 2 * err₂) :=
      add_le_add (le_refl _) (add_le_add (le_refl _) hright)
    _ = 2 * err₁ + taoTV natural₁ natural₂ + 2 * err₂ := by ring

end

end Tao
end Erdos1135
