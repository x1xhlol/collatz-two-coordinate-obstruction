import Erdos1135.Tao.Syracuse.ParityBridge
import Erdos1135.Terras.Parity.Residue
import Mathlib.Data.List.OfFn

/-!
# Syracuse Cylinder Residue Adapter

This module packages Tao valuation-cylinder parity lists as Terras parity words and reuses the
checked Terras residue theorem.  It is a deterministic residue-class adapter only: no PMFs,
Fourier analysis, renewal estimates, or Proposition 1.9 bounds are introduced here.
-/

namespace Erdos1135
namespace Tao

/-- Turn a Boolean list into the length-indexed Terras parity word with the same entries. -/
def parityWordOfList (ps : List Bool) : Terras.ParityWord ps.length :=
  ps.get

theorem parityWordToList_parityWordOfList (ps : List Bool) :
    Terras.parityWordToList (parityWordOfList ps) = ps := by
  simp [parityWordOfList, Terras.parityWordToList]

theorem parityPrefix_eq_parityWordOfList_iff (ps : List Bool) (N : ℕ) :
    Terras.parityPrefix ps.length N = parityWordOfList ps ↔
      Terras.parityPrefixList ps.length N = ps := by
  constructor
  · intro h
    have hlist := congrArg Terras.parityWordToList h
    simpa [parityWordToList_parityWordOfList ps,
      Terras.parityWordToList_parityPrefix_eq_parityPrefixList ps.length N] using hlist
  · intro h
    apply List.ofFn_injective
    change Terras.parityWordToList (Terras.parityPrefix ps.length N) =
      Terras.parityWordToList (parityWordOfList ps)
    simpa [parityWordToList_parityWordOfList ps,
      Terras.parityWordToList_parityPrefix_eq_parityPrefixList ps.length N] using h

theorem existsUnique_residue_syracuseValuationCylinderWord
    (as : List ℕ+) :
    ∃! r : ZMod (2 ^ (syracuseValuationCylinderWord as).length),
      ∀ N : ℕ,
        (N : ZMod (2 ^ (syracuseValuationCylinderWord as).length)) = r ↔
          Terras.parityPrefixList
              (syracuseValuationCylinderWord as).length N =
            syracuseValuationCylinderWord as := by
  classical
  let ps := syracuseValuationCylinderWord as
  rcases Terras.unique_residue_for_word (parityWordOfList ps) with ⟨r, hr, huniq⟩
  refine ⟨r, ?_, ?_⟩
  · intro N
    exact (hr N).trans (parityPrefix_eq_parityWordOfList_iff ps N)
  · intro s hs
    apply huniq s
    intro N
    exact (hs N).trans (parityPrefix_eq_parityWordOfList_iff ps N).symm

theorem existsUnique_residue_syracuseValuationCylinderWord_weight
    (as : List ℕ+) :
    ∃! r : ZMod (2 ^ (taoTupleWeight as + 1)),
      ∀ N : ℕ,
        (N : ZMod (2 ^ (taoTupleWeight as + 1))) = r ↔
          Terras.parityPrefixList (taoTupleWeight as + 1) N =
            syracuseValuationCylinderWord as := by
  rw [← syracuseValuationCylinderWord_length as]
  exact existsUnique_residue_syracuseValuationCylinderWord as

end Tao
end Erdos1135
