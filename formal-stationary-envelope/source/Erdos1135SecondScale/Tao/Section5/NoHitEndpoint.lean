/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section5.NoHitRate

/-!
# Section 5 Canonical No-Hit Endpoint

This leaf patches the finite threshold prefix of the eventual native no-hit
output and exposes the two canonical Proposition 1.11 source windows.  It does
not import the broad Section 5 facade or mention pass-event payload scales.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open Filter

/-- Every finite logarithmic-window no-hit probability is at most one. -/
theorem syracuseNoHitWindowProb_le_one
    (B lo hi : ℕ)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) :
    syracuseNoHitWindowProb B lo hi hmass ≤ 1 := by
  unfold syracuseNoHitWindowProb
  calc
    pmfProb (oddLogWindowPMF lo hi hmass)
        {N : {N : ℕ // N ∈ oddLogWindow lo hi} |
          (N : ℕ) ∈ syracuseNoHitAtMost B} ≤
      pmfProb (oddLogWindowPMF lo hi hmass) Set.univ :=
        pmfProb_mono _ (Set.subset_univ _)
    _ = 1 := pmfProb_univ _

@[simp]
theorem taoSection5SourceLo_alpha_eq_prop111Y1 (B : ℕ) :
    taoSection5SourceLo B .alpha = taoNyLo (taoProp111Y1 B) :=
  rfl

@[simp]
theorem taoSection5SourceHi_alpha_eq_prop111Y1 (B : ℕ) :
    taoSection5SourceHi B .alpha = taoNyHi (taoProp111Y1 B) taoAlpha :=
  rfl

@[simp]
theorem taoSection5SourceLo_alphaSq_eq_prop111Y2 (B : ℕ) :
    taoSection5SourceLo B .alphaSq = taoNyLo (taoProp111Y2 B) :=
  rfl

@[simp]
theorem taoSection5SourceHi_alphaSq_eq_prop111Y2 (B : ℕ) :
    taoSection5SourceHi B .alphaSq = taoNyHi (taoProp111Y2 B) taoAlpha :=
  rfl

/-- All-threshold rate statement for the two canonical source branches. -/
def TaoSection5CanonicalNoHitRateStatement : Prop :=
  ∃ noHitErr : ℕ → ℝ, ∃ C c : ℝ,
    0 ≤ C ∧ 0 < c ∧
      (∀ᶠ B : ℕ in atTop,
        0 ≤ noHitErr B ∧
          noHitErr B ≤ C * (B : ℝ) ^ (-c)) ∧
        ∀ B : ℕ, ∀ branch : TaoSection5SourceBranch,
          ∀ hmass : 0 < logFinsetMass
            (oddLogWindow (taoSection5SourceLo B branch)
              (taoSection5SourceHi B branch)),
            syracuseNoHitWindowProb B
                (taoSection5SourceLo B branch)
                (taoSection5SourceHi B branch) hmass ≤
              noHitErr B

/-- One cutoff patches the finite prefix by the universal probability bound;
above it the error is literally the checked raw error. -/
theorem taoSection5CanonicalNoHitRateStatement_checked :
    TaoSection5CanonicalNoHitRateStatement := by
  rcases eventually_atTop.1 eventually_taoSection5NoHitRateOutput with
    ⟨B0, hB0⟩
  let noHitErr : ℕ → ℝ := fun B =>
    if B0 ≤ B then taoSection5NoHitError B else 1
  refine ⟨noHitErr, 10, (1 / 32000 : ℝ), by norm_num, by norm_num, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop B0] with B hB
    rw [show noHitErr B = taoSection5NoHitError B by simp [noHitErr, hB]]
    exact ⟨(hB0 B hB).error_nonneg, (hB0 B hB).error_le⟩
  · intro B branch hmass
    by_cases hB : B0 ≤ B
    · rw [show noHitErr B = taoSection5NoHitError B by simp [noHitErr, hB]]
      exact (hB0 B hB).output.noHit_le branch hmass
    · rw [show noHitErr B = 1 by simp [noHitErr, hB]]
      exact syracuseNoHitWindowProb_le_one B _ _ hmass

/-- Direct no-hit rate statement over the endpoint relation consumed by the
Proposition 1.11 socket, with no auxiliary payload scales. -/
def TaoSection5CanonicalPairNoHitRateStatement : Prop :=
  ∃ noHitErr : ℕ → ℝ, ∃ C c : ℝ,
    0 ≤ C ∧ 0 < c ∧
      (∀ᶠ B : ℕ in atTop,
        0 ≤ noHitErr B ∧
          noHitErr B ≤ C * (B : ℝ) ^ (-c)) ∧
        ∀ B lo1 hi1 lo2 hi2 : ℕ,
          TaoProp111WindowPair B lo1 hi1 lo2 hi2 →
            ∀ (hmass1 : 0 < logFinsetMass (oddLogWindow lo1 hi1))
              (hmass2 : 0 < logFinsetMass (oddLogWindow lo2 hi2)),
                syracuseNoHitWindowProb B lo1 hi1 hmass1 ≤ noHitErr B ∧
                  syracuseNoHitWindowProb B lo2 hi2 hmass2 ≤ noHitErr B

theorem TaoSection5CanonicalNoHitRateStatement.to_pair
    (h : TaoSection5CanonicalNoHitRateStatement) :
    TaoSection5CanonicalPairNoHitRateStatement := by
  rcases h with ⟨noHitErr, C, c, hC, hc, hrate, hbranch⟩
  refine ⟨noHitErr, C, c, hC, hc, hrate, ?_⟩
  intro B lo1 hi1 lo2 hi2 hpair hmass1 hmass2
  rcases hpair with ⟨rfl, rfl, rfl, rfl⟩
  constructor
  · simpa only [taoSection5SourceLo_alpha_eq_prop111Y1,
      taoSection5SourceHi_alpha_eq_prop111Y1] using
      hbranch B .alpha hmass1
  · simpa only [taoSection5SourceLo_alphaSq_eq_prop111Y2,
      taoSection5SourceHi_alphaSq_eq_prop111Y2] using
      hbranch B .alphaSq hmass2

theorem taoSection5CanonicalPairNoHitRateStatement_checked :
    TaoSection5CanonicalPairNoHitRateStatement :=
  TaoSection5CanonicalNoHitRateStatement.to_pair
    taoSection5CanonicalNoHitRateStatement_checked

end

end Tao
end Erdos1135SecondScale
