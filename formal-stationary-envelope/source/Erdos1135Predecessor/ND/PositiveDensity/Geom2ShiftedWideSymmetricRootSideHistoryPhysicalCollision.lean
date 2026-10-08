/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideHistoryInjectivity

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

structure NDGeom2RootSideSyracusePath (source terminal : ℕ) where
  sourceOdd : Odd source
  depth : ℕ
  word : List ℕ+
  word_length : word.length = depth
  valuation_eq :
    Tao.syracuseValuationPNatList depth source sourceOdd = word
  terminal_eq : (Tao.syracuse^[depth]) source = terminal

def NDGeom2RootSideSyracusePath.nil (N : ℕ) (hN : Odd N) :
    NDGeom2RootSideSyracusePath N N where
  sourceOdd := hN
  depth := 0
  word := []
  word_length := rfl
  valuation_eq := rfl
  terminal_eq := by simp

private theorem rootSideSyracuseValuationPNatList_congr_source
    {n M N : ℕ} (hM : Odd M) (hN : Odd N) (hMN : M = N) :
    Tao.syracuseValuationPNatList n M hM =
      Tao.syracuseValuationPNatList n N hN := by
  subst N
  rfl

noncomputable def NDGeom2RootSideSyracusePath.appendRootSideIncidence
    {Label : Type*} {root base shift : Label → ℕ} {K source : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K)
    (p : NDGeom2RootSideSyracusePath source
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)) :
    NDGeom2RootSideSyracusePath source
      (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)) where
  sourceOdd := p.sourceOdd
  depth := p.depth +
    ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z
  word := p.word ++
    ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z
  word_length := by
    rw [List.length_append, p.word_length,
      ndGeom2PredictableRootSideBoundedOvershootIncidence_chronologicalWord_length]
  valuation_eq := by
    have htail :
        Tao.syracuseValuationPNatList
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)
            ((Tao.syracuse^[p.depth]) source)
            (Tao.syracuse_iterate_odd_trajectory
              p.depth source p.sourceOdd) =
          ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z := by
      exact
        (rootSideSyracuseValuationPNatList_congr_source
          (Tao.syracuse_iterate_odd_trajectory p.depth source p.sourceOdd)
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd
            hrootOdd hbaseNine hrootLower z)
          p.terminal_eq).trans
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_valuation
              hrootOdd hbaseNine hrootLower z)
    rw [Tao.syracuseValuationPNatList_add, p.valuation_eq, htail]
  terminal_eq := by
    rw [Nat.add_comm, Function.iterate_add_apply, p.terminal_eq,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_iterate
        hrootOdd hbaseNine hrootLower z]

@[simp] theorem NDGeom2RootSideSyracusePath.appendRootSideIncidence_depth
    {Label : Type*} {root base shift : Label → ℕ} {K source : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K)
    (p : NDGeom2RootSideSyracusePath source
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)) :
    (p.appendRootSideIncidence hrootOdd hbaseNine hrootLower z).depth =
      p.depth + ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z :=
  rfl

theorem NDGeom2RootSideSyracusePath.word_eq_of_source_depth_eq
    {source₁ source₂ terminal₁ terminal₂ : ℕ}
    (p : NDGeom2RootSideSyracusePath source₁ terminal₁)
    (q : NDGeom2RootSideSyracusePath source₂ terminal₂)
    (hsource : source₁ = source₂) (hdepth : p.depth = q.depth) :
    p.word = q.word := by
  have hp := p.valuation_eq
  have hq := q.valuation_eq
  subst source₂
  rw [hdepth] at hp
  exact hp.symm.trans hq

end

end PositiveDensity

end ND

end Erdos1135Predecessor
