/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUniformFloorUnitChildState

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

theorem ndGeom2PredictableRootSideUnitChildIncidence_ext
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    {z w : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K}
    (hlabel :
      ndGeom2PredictableRootSideUnitChildIncidenceLabel z =
        ndGeom2PredictableRootSideUnitChildIncidenceLabel w)
    (hdepth :
      ndGeom2PredictableRootSideUnitChildIncidenceDepth z =
        ndGeom2PredictableRootSideUnitChildIncidenceDepth w)
    (hdigit :
      ndGeom2PredictableRootSideUnitChildIncidenceDigit z =
        ndGeom2PredictableRootSideUnitChildIncidenceDigit w)
    (hword :
      ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z =
        ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord w) :
    z = w := by
  rcases z with ⟨i, s, u, zword⟩
  rcases w with ⟨j, t, v, wword⟩
  change i.1 = j.1 at hlabel
  have hij : i = j := Subtype.ext hlabel
  subst j
  change s.1 = t.1 at hdepth
  have hst : s = t := Subtype.ext hdepth
  subst t
  change u.1 = v.1 at hdigit
  have huv : u = v := Subtype.ext hdigit
  subst v
  change zword.1 = wword.1 at hword
  have hzw : zword = wword := Subtype.ext hword
  subst wword
  rfl

theorem ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_injective
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i) :
    Function.Injective
      (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical
        (Labels := Labels) (root := root) (b := b) (a := a) (K := K)) := by
  intro z w hphysical
  have hlabel :
      ndGeom2PredictableRootSideUnitChildIncidenceLabel z =
        ndGeom2PredictableRootSideUnitChildIncidenceLabel w := by
    simpa only [ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_label]
      using congrArg ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel hphysical
  have hdepth :
      ndGeom2PredictableRootSideUnitChildIncidenceDepth z =
        ndGeom2PredictableRootSideUnitChildIncidenceDepth w := by
    simpa only [ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_depth]
      using congrArg ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth hphysical
  have hsource :
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
          (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z) =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
          (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical w) :=
    congrArg ndGeom2PredictableRootSideBoundedOvershootIncidenceSource hphysical
  have hdigit :
      ndGeom2PredictableRootSideUnitChildIncidenceDigit z =
        ndGeom2PredictableRootSideUnitChildIncidenceDigit w := by
    calc
      ndGeom2PredictableRootSideUnitChildIncidenceDigit z =
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
            (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z) :
              ZMod (3 ^ 1)) :=
        (ndGeom2PredictableRootSideUnitChildIncidence_sourceDigit_eq
          hrootOdd hb hrootLower z).symm
      _ =
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
            (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical w) :
              ZMod (3 ^ 1)) := by rw [hsource]
      _ = ndGeom2PredictableRootSideUnitChildIncidenceDigit w :=
        ndGeom2PredictableRootSideUnitChildIncidence_sourceDigit_eq
          hrootOdd hb hrootLower w
  have hword :
      ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z =
        ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord w := by
    simpa only [ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_word]
      using congrArg
        ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord hphysical
  exact ndGeom2PredictableRootSideUnitChildIncidence_ext
    hlabel hdepth hdigit hword

theorem
    ndGeom2PredictableRootSideUnitChildIncidence_eq_of_label_eq_of_commonPrefix
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    {z w : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K}
    (hlabel :
      ndGeom2PredictableRootSideUnitChildIncidenceLabel z =
        ndGeom2PredictableRootSideUnitChildIncidenceLabel w)
    {fullRootSide : List ℕ+}
    (hzPrefix :
      ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z =
        fullRootSide.take
          (ndGeom2PredictableRootSideUnitChildIncidenceDepth z))
    (hwPrefix :
      ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord w =
        fullRootSide.take
          (ndGeom2PredictableRootSideUnitChildIncidenceDepth w)) :
    z = w := by
  apply ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_injective
    hrootOdd hb hrootLower
  apply
    ndGeom2PredictableRootSideBoundedOvershootIncidence_eq_of_label_eq_of_commonPrefix
  · simpa only [ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_label]
      using hlabel
  · simpa only [
      ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_word,
      ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_depth] using hzPrefix
  · simpa only [
      ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_word,
      ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_depth] using hwPrefix

theorem
    ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) :
    (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z).length =
      ndGeom2PredictableRootSideUnitChildIncidenceDepth z := by
  simpa only [
    ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_word,
    ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_depth] using
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_word_length
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z))

end

end PositiveDensity

end ND

end Erdos1135Predecessor
