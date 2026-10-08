/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section5.AffineSourceSupport
import Erdos1135SecondScale.Tao.Section5.PassEventPartition

/-!
# Section 5 Affine Atom Fibers

This leaf identifies each scheduled affine source fiber as a supported
singleton when its residue is compatible and as empty otherwise.  Probability
evaluation and reciprocal algebra remain in later leaves.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- A compatible scheduled affine atom is the singleton containing its unique
supported odd source. -/
theorem exists_taoSection5ClosedAffineAtom_eq_singleton_of_compatible
    {B : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    (facts : TaoSection5AffineSourceScaleFacts B)
    (i : TaoSection5ClosedAffineAtomIndex B branch E)
    (hcompat :
      (i.2.2.1 : ZMod (3 ^ (i.1.1 - taoSection5M0 B))) =
        taoAffineOffsetZMod (i.1.1 - taoSection5M0 B) i.2.1.1) :
    ∃ N : TaoOddNat,
      N.1 ∈ oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch) ∧
        taoSection5ClosedAffineAtom i = {N} := by
  have htyp := mem_taoSection5TypicalTuples_iff.mp i.2.1.2
  have hsupport :=
    (taoSection5_affineOffsetZMod_eq_iff_existsUnique_mem_sourceWindow_of_mem_EPrime
      facts i.1.2 rfl htyp i.2.2.2).mp hcompat
  rcases hsupport with ⟨N, ⟨hwindow, hAff⟩, _hunique⟩
  refine ⟨N, hwindow, ?_⟩
  ext N'
  simp only [taoSection5ClosedAffineAtom, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · intro hAff'
    exact taoAffList_oddNat_injective i.2.1.1 i.2.2.1 hAff' hAff
  · rintro rfl
    exact hAff

/-- An incompatible scheduled affine atom has no odd source at all. -/
theorem taoSection5ClosedAffineAtom_eq_empty_of_incompatible
    {B : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    (i : TaoSection5ClosedAffineAtomIndex B branch E)
    (hincompat :
      ¬ (i.2.2.1 : ZMod (3 ^ (i.1.1 - taoSection5M0 B))) =
        taoAffineOffsetZMod (i.1.1 - taoSection5M0 B) i.2.1.1) :
    taoSection5ClosedAffineAtom i = ∅ := by
  have htyp := mem_taoSection5TypicalTuples_iff.mp i.2.1.2
  ext N
  simp only [taoSection5ClosedAffineAtom, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  intro hAff
  apply hincompat
  exact taoAffineOffsetZMod_eq_of_taoAffList_eq htyp.1 hAff

end

end Tao
end Erdos1135SecondScale
