/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.Geom
import Erdos1135Predecessor.Tao.Syracuse.Affine
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Sym.Card

namespace Erdos1135Predecessor

namespace Tao

abbrev PNatBelow (M : ℕ) : Type :=
  {a : Fin M // 0 < (a : ℕ)}

namespace PNatBelow

def toPNat {M : ℕ} (a : PNatBelow M) : ℕ+ :=
  ⟨a.1, a.2⟩

instance (M : ℕ) : Fintype (PNatBelow M) := inferInstance

end PNatBelow

abbrev BoundedValuationTuple (n M : ℕ) : Type :=
  {v : Fin n → PNatBelow M //
    (Finset.univ.sum fun i => (PNatBelow.toPNat (v i) : ℕ)) < M}

namespace BoundedValuationTuple

instance (n M : ℕ) : Fintype (BoundedValuationTuple n M) := inferInstance

def toList {n M : ℕ} (v : BoundedValuationTuple n M) : List ℕ+ :=
  List.ofFn fun i : Fin n => PNatBelow.toPNat (v.1 i)

theorem toList_length {n M : ℕ} (v : BoundedValuationTuple n M) :
    (toList v).length = n := by
  simp [toList]

end BoundedValuationTuple

end Tao

end Erdos1135Predecessor
