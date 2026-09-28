import Erdos1135.Tao.Section5.AffineSourceScale
import Erdos1135.Tao.Syracuse.AffineResidue

/-!
# Section 5 Affine Source Support

This thin integration leaf identifies scheduled affine-residue compatibility
with exactly one odd source in the actual rounded Section 5 source window.  It
contains no source PMF evaluation, reciprocal rewrite, tuple reversal, or
common-normalizer argument.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- A scheduled tuple and lost-window endpoint are residue-compatible exactly
when they have one odd affine source in the original branch source window. -/
theorem taoSection5_affineOffsetZMod_eq_iff_existsUnique_mem_sourceWindow
    {B n q M : ℕ} {branch : TaoSection5SourceBranch} {as : List ℕ+}
    (facts : TaoSection5AffineSourceScaleFacts B)
    (hn : n ∈ taoSection5PassTimes B branch)
    (hq : q = n - taoSection5M0 B)
    (htyp : taoSection5TypicalTuple B q as)
    (hM : M ∈ taoSection5CanonicalLostWindow B)
    (hModd : Odd M) :
    (M : ZMod (3 ^ q)) = taoAffineOffsetZMod q as ↔
      ∃! N : TaoOddNat,
        N.1 ∈ oddLogWindow
            (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch) ∧
          taoAffList as (N.1 : ℚ) = (M : ℚ) := by
  constructor
  · intro hcompat
    have hqle : q ≤ taoSection5N0 B := by
      rw [hq]
      exact facts.schedule.sub_le_n0 hn
    have hroom : 2 * 3 ^ q < M := facts.endpoint_room hqle hM
    rcases existsUnique_taoAffList_eq_of_affineOffsetZMod
        htyp.1 hModd hroom hcompat with ⟨N, hAff, hunique⟩
    have hbounds :=
      taoSection5_scheduledAffineSource_real_bounds
        facts hn hq htyp hM hAff
    have hsourceNonneg : 0 ≤ taoSection5SourceY B branch := by
      rw [taoSection5SourceY_eq_branch_rpow]
      exact Real.rpow_nonneg (Nat.cast_nonneg B) _
    have hwindowY :
        N.1 ∈ taoNyOddWindow (taoSection5SourceY B branch) taoAlpha :=
      (taoNyOddWindow_mem hsourceNonneg).2
        ⟨hbounds.1, hbounds.2, Nat.odd_iff.mp N.2⟩
    have hwindow :
        N.1 ∈ oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch) := by
      simpa only [taoNyOddWindow, taoSection5SourceLo,
        taoSection5SourceHi] using hwindowY
    refine ⟨N, ⟨hwindow, hAff⟩, ?_⟩
    intro N' hN'
    exact hunique N' hN'.2
  · rintro ⟨N, ⟨_window, hAff⟩, _hunique⟩
    exact taoAffineOffsetZMod_eq_of_taoAffList_eq htyp.1 hAff

/-- Forward projection used by the later singleton affine-fiber theorem. -/
theorem existsUnique_taoSection5_scheduledAffineSource_mem_sourceWindow
    {B n q M : ℕ} {branch : TaoSection5SourceBranch} {as : List ℕ+}
    (facts : TaoSection5AffineSourceScaleFacts B)
    (hn : n ∈ taoSection5PassTimes B branch)
    (hq : q = n - taoSection5M0 B)
    (htyp : taoSection5TypicalTuple B q as)
    (hM : M ∈ taoSection5CanonicalLostWindow B)
    (hModd : Odd M)
    (hcompat : (M : ZMod (3 ^ q)) = taoAffineOffsetZMod q as) :
    ∃! N : TaoOddNat,
      N.1 ∈ oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch) ∧
        taoAffList as (N.1 : ℚ) = (M : ℚ) :=
  (taoSection5_affineOffsetZMod_eq_iff_existsUnique_mem_sourceWindow
    facts hn hq htyp hM hModd).mp hcompat

/-- Endpoints in `EPrime` use only its canonical-window and oddness fields for
the same exact supported-source equivalence. -/
theorem taoSection5_affineOffsetZMod_eq_iff_existsUnique_mem_sourceWindow_of_mem_EPrime
    {B n q M : ℕ} {branch : TaoSection5SourceBranch} {as : List ℕ+}
    {E : Set ℕ}
    (facts : TaoSection5AffineSourceScaleFacts B)
    (hn : n ∈ taoSection5PassTimes B branch)
    (hq : q = n - taoSection5M0 B)
    (htyp : taoSection5TypicalTuple B q as)
    (hM : M ∈ taoSection5EPrime B E) :
    (M : ZMod (3 ^ q)) = taoAffineOffsetZMod q as ↔
      ∃! N : TaoOddNat,
        N.1 ∈ oddLogWindow
            (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch) ∧
          taoAffList as (N.1 : ℚ) = (M : ℚ) := by
  have hM' := mem_taoSection5EPrime_iff.mp hM
  have hwindow : M ∈ taoSection5CanonicalLostWindow B := by
    apply Finset.mem_Icc.mpr
    exact ⟨hM'.1, hM'.2.1⟩
  exact taoSection5_affineOffsetZMod_eq_iff_existsUnique_mem_sourceWindow
    facts hn hq htyp hwindow hM'.2.2.1

end

end Tao
end Erdos1135
