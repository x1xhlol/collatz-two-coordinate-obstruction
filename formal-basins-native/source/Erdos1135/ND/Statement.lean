import Erdos1135.ND.Conventions

/-!
# Frozen V10 Natural-Density Statement Surface

This module records the source-facing targets `ND-M2`, `ND-3.1`, `ND-1.6`,
and `ND-1.3`.  These are `Prop` definitions, not asserted theorems.
-/

namespace Erdos1135
namespace ND

/-- ND-M2 with fixed positive hit and transport exponents.

The hidden constants and the sufficiently-large threshold are explicit
witnesses. Both source blocks are quantified. Clause (ii) uses full L1. -/
def NDM2Bounds (cHit cTr : ℝ) : Prop :=
  ∃ CHit CTr x0 : ℝ,
    0 ≤ CHit ∧ 0 ≤ CTr ∧ 2 ≤ x0 ∧
      ∀ (x : ℝ), x0 ≤ x →
        ∀ (hx : 1 ≤ x) (branch : Tao.TaoSection5SourceBranch),
          let y := transportSourceY x branch
          ∃ hwindow : (oddBlock y).Nonempty,
          ∃ hmass : 0 < Tao.logFinsetMass (oddBlock y),
            uniformNoHitProbability x y hwindow ≤
                CHit * Real.rpow x (-cHit) ∧
              passFullL1 x y hx hwindow hmass ≤
                CTr * Real.rpow (Real.log x) (-cTr)

/-- The v10 two-block transport theorem ND-M2. -/
def NDM2Statement : Prop :=
  ∃ cHit cTr : ℝ, 0 < cHit ∧ 0 < cTr ∧ NDM2Bounds cHit cTr

/-- Positive odd inputs whose Syracuse orbit minimum is above `N0`. -/
def oddSyracuseBadSet (N0 : ℕ) : Set ℕ :=
  {N : ℕ | 0 < N ∧ Odd N ∧ ¬ Tao.syracuseHitsAtMost N N0}

/-- The natural-endpoint specialization of the ND-3.1 bad ratio. -/
noncomputable def oddSyracuseBadRatioNat (N0 X : ℕ) : ℝ :=
  (natCountLE (oddSyracuseBadSet N0) X : ℝ) / (X : ℝ)

/-- The exact real-endpoint ND-3.1 bad ratio. The numerator counts the
inclusive interval `[1,floor x]`; the odd guard removes zero. -/
noncomputable def oddSyracuseBadRatio (N0 : ℕ) (x : ℝ) : ℝ :=
  (natCountLEReal (oddSyracuseBadSet N0) x : ℝ) / x

/-- ND-3.1 at a fixed logarithmic exponent `c`.

Both `N0 ≥ 2` and the positive real counting endpoint `x ≥ 2` remain
visible. -/
def ND31Bounds (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (N0 : ℕ) (x : ℝ), 2 ≤ N0 → 2 ≤ x →
      oddSyracuseBadRatio N0 x ≤
        C * Real.rpow (Real.log (N0 : ℝ)) (-c)

/-- The v10 natural-counting theorem ND-3.1. -/
def ND31Statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ND31Bounds c

/-- Relative natural density one on the positive odd naturals, represented by
ambient natural density `1/2` of the odd-supported set. -/
def HasOddRelativeNatDensityOne (S : Set ℕ) : Prop :=
  Terras.HasNatDensity {N : ℕ | Odd N ∧ N ∈ S} (1 / 2 : ℝ)

/-- The v10 theorem ND-1.6: strict almost-boundedness relative to positive
odd naturals in natural density. -/
def ND16Statement : Prop :=
  ∀ f : ℕ → ℝ,
    Tao.GrowsOnOddsToInfinity f →
      HasOddRelativeNatDensityOne
        {N : ℕ | Tao.syracuseHitsBelowReal N (f N)}

/-- The v10 theorem ND-1.3: strict almost-boundedness on all positive
naturals in natural density. -/
def ND13Statement : Prop :=
  ∀ f : ℕ → ℝ,
    Tao.GrowsToInfinity f →
      Terras.HasNatDensity
        {N : ℕ | 0 < N ∧ Tao.collatzHitsBelowReal N (f N)} 1

/-- The complete v10 chain, retaining the equality of the ND-M2 transport
exponent and the ND-3.1 exponent. -/
def NDChainStatement : Prop :=
  ∃ cHit cTr : ℝ,
    0 < cHit ∧ 0 < cTr ∧
      NDM2Bounds cHit cTr ∧
      ND31Bounds cTr ∧
      ND16Statement ∧
      ND13Statement

end ND
end Erdos1135
