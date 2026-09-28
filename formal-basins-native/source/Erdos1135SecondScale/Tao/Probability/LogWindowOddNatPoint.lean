/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.LogWindowResidue

/-!
# Point Values Of The Odd Log-Window Source PMF

This neutral leaf evaluates the mapped odd-source PMF both on and off its
finite support.  The unsupported formula is kept in native `ENNReal` form.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The supported-value embedding into odd naturals is injective. -/
theorem oddLogWindowValueToOddNat_injective {lo hi : ℕ} :
    Function.Injective (@oddLogWindowValueToOddNat lo hi) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun N : TaoOddNat => N.1) hab

/-- A supported odd source has its original native logarithmic-window mass. -/
theorem oddLogWindowOddNatPMF_apply_of_mem
    {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (N : TaoOddNat) (hN : N.1 ∈ oddLogWindow lo hi) :
    oddLogWindowOddNatPMF lo hi hmass N =
      ENNReal.ofReal
        (logNatWeight N.1 / logFinsetMass (oddLogWindow lo hi)) := by
  classical
  let Nwin : {n : ℕ // n ∈ oddLogWindow lo hi} := ⟨N.1, hN⟩
  have hmap : N = oddLogWindowValueToOddNat Nwin := by
    apply Subtype.ext
    rfl
  rw [oddLogWindowOddNatPMF, PMF.map_apply]
  rw [tsum_eq_single Nwin]
  · rw [if_pos hmap]
    rw [oddLogWindowPMF, logFinsetPMF, PMF.ofFintype_apply]
  · intro a ha
    rw [if_neg]
    intro hEq
    apply ha
    apply Subtype.ext
    have hval := congrArg Subtype.val hEq
    simpa only [oddLogWindowValueToOddNat, Nwin] using hval.symm

/-- Real projection of the supported point formula. -/
theorem oddLogWindowOddNatPMF_apply_toReal_of_mem
    {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (N : TaoOddNat) (hN : N.1 ∈ oddLogWindow lo hi) :
    (oddLogWindowOddNatPMF lo hi hmass N).toReal =
      logNatWeight N.1 / logFinsetMass (oddLogWindow lo hi) := by
  rw [oddLogWindowOddNatPMF_apply_of_mem hmass N hN]
  exact ENNReal.toReal_ofReal
    (div_nonneg (logNatWeight_nonneg N.1) hmass.le)

/-- An odd source outside the finite window has zero native PMF mass. -/
theorem oddLogWindowOddNatPMF_apply_eq_zero_of_not_mem
    {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (N : TaoOddNat) (hN : N.1 ∉ oddLogWindow lo hi) :
    oddLogWindowOddNatPMF lo hi hmass N = 0 := by
  classical
  rw [oddLogWindowOddNatPMF, PMF.map_apply, ENNReal.tsum_eq_zero]
  intro a
  have hne : N ≠ oddLogWindowValueToOddNat a := by
    intro hEq
    apply hN
    have hval := congrArg Subtype.val hEq
    simpa only [oddLogWindowValueToOddNat, hval] using a.2
  simp only [if_neg hne]

/-- Real projection of the unsupported zero formula. -/
theorem oddLogWindowOddNatPMF_apply_toReal_eq_zero_of_not_mem
    {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (N : TaoOddNat) (hN : N.1 ∉ oddLogWindow lo hi) :
    (oddLogWindowOddNatPMF lo hi hmass N).toReal = 0 := by
  rw [oddLogWindowOddNatPMF_apply_eq_zero_of_not_mem hmass N hN]
  rfl

/-- Totalized real point formula, with the support branch explicit. -/
theorem oddLogWindowOddNatPMF_apply_toReal
    {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (N : TaoOddNat) :
    (oddLogWindowOddNatPMF lo hi hmass N).toReal =
      if N.1 ∈ oddLogWindow lo hi then
        logNatWeight N.1 / logFinsetMass (oddLogWindow lo hi)
      else 0 := by
  classical
  by_cases hN : N.1 ∈ oddLogWindow lo hi
  · rw [if_pos hN]
    exact oddLogWindowOddNatPMF_apply_toReal_of_mem hmass N hN
  · rw [if_neg hN]
    exact oddLogWindowOddNatPMF_apply_toReal_eq_zero_of_not_mem hmass N hN

end

end Tao
end Erdos1135SecondScale
