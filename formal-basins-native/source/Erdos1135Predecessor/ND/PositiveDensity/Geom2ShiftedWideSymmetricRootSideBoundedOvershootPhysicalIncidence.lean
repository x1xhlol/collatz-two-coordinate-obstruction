/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideBoundedOvershootRate

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

noncomputable def
    ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset
    (b a s K : ℕ) (x : ZMod (3 ^ s)) : Finset (List ℕ+) := by
  classical
  exact
    (Tao.shortValuationLists s
      (ndGeom2ShiftedWideSymmetricBoundedOvershootWordCutoff b a s K)).filter
        fun rootSide =>
          ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt
              b a s K rootSide ∧
            Tao.taoSection7OffsetZMod s rootSide = x

theorem
    mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff
    {b a s K : ℕ} {x : ZMod (3 ^ s)} {rootSide : List ℕ+} :
    rootSide ∈
        ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset
          b a s K x ↔
      rootSide.length = s ∧
        ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt
            b a s K rootSide ∧
          Tao.taoSection7OffsetZMod s rootSide = x := by
  classical
  constructor
  · intro hword
    rcases Finset.mem_filter.mp hword with ⟨hshort, hevent, hoffset⟩
    rcases Tao.mem_shortValuationLists_iff.mp hshort with ⟨v, rfl⟩
    exact ⟨Tao.BoundedValuationTuple.toList_length v, hevent, hoffset⟩
  · rintro ⟨hlen, hevent, hoffset⟩
    have hweight :
        Tao.taoTupleWeight rootSide <
          ndGeom2ShiftedWideSymmetricBoundedOvershootWordCutoff
            b a s K := by
      have hover := hevent.2
      unfold ndGeom2ShiftedWideSymmetricBoundedOvershoot at hover
      unfold ndGeom2ShiftedWideSymmetricBoundedOvershootWordCutoff
      omega
    let v : Tao.BoundedValuationTuple s
        (ndGeom2ShiftedWideSymmetricBoundedOvershootWordCutoff b a s K) :=
      Tao.BoundedValuationTuple.ofList rootSide hlen hweight
    apply Finset.mem_filter.mpr
    refine ⟨?_, hevent, hoffset⟩
    rw [Tao.mem_shortValuationLists_iff]
    exact ⟨v, (Tao.BoundedValuationTuple.toList_ofList
      rootSide hlen hweight).symm⟩

abbrev NDGeom2ShiftedWideSymmetricRootSideBoundedOvershootWord
    (root b a K : ℕ)
    (s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b) :=
  {rootSide : List ℕ+ // rootSide ∈
    ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset
      b a s.1 K (root : ZMod (3 ^ s.1))}

noncomputable instance instFintypeShiftedWideSymmetricRootSideBoundedOvershootWord
    (root b a K : ℕ)
    (s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b) :
    Fintype
      (NDGeom2ShiftedWideSymmetricRootSideBoundedOvershootWord
        root b a K s) :=
  Fintype.ofFinset
    (ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset
      b a s.1 K (root : ZMod (3 ^ s.1))) (by intro rootSide; rfl)

abbrev NDGeom2PredictableRootSideBoundedOvershootIncidence
    (Label : Type*) (root base shift : Label → ℕ) (K : ℕ) :=
  Σ i : Label,
    Σ s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth (base i),
      NDGeom2ShiftedWideSymmetricRootSideBoundedOvershootWord
        (root i) (base i) (shift i) K s

def ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) : Label :=
  z.1

def ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) : ℕ :=
  z.2.1.1

def ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) : List ℕ+ :=
  z.2.2.1

def ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) : List ℕ+ :=
  (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z).reverse

theorem ndGeom2PredictableRootSideBoundedOvershootIncidence_depth_mem
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z ∈
      ndGeom2ShiftedWideSymmetricCrossingSelectedDepths
        (base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)) :=
  z.2.1.2

theorem ndGeom2PredictableRootSideBoundedOvershootIncidence_word_mem
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z ∈
      ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset
        (base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
        (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z) K
        (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) :
          ZMod (3 ^
            ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)) :=
  z.2.2.2

theorem ndGeom2PredictableRootSideBoundedOvershootIncidence_word_length
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z).length =
      ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z :=
  (mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mp
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_word_mem z)).1

theorem
    ndGeom2PredictableRootSideBoundedOvershootIncidence_chronologicalWord_length
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z).length =
      ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z := by
  unfold ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord
  rw [List.length_reverse,
    ndGeom2PredictableRootSideBoundedOvershootIncidence_word_length]

theorem ndGeom2PredictableRootSideBoundedOvershootIncidence_firstCrossing
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    ndGeom2ShiftedWideSymmetricFirstCrossingAt
      (base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z) :=
  (mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mp
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_word_mem z)).2.1.1

theorem ndGeom2PredictableRootSideBoundedOvershootIncidence_boundedOvershoot
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    ndGeom2ShiftedWideSymmetricBoundedOvershoot
      (base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z) K
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z) :=
  (mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mp
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_word_mem z)).2.1.2

theorem ndGeom2PredictableRootSideBoundedOvershootIncidence_section7Compatible
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) :
        ZMod (3 ^ ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)) =
      Tao.taoSection7OffsetZMod
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z) :=
  (mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mp
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_word_mem z)).2.2.symm

theorem ndGeom2PredictableRootSideBoundedOvershootIncidence_affineCompatible
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) :
        ZMod (3 ^ ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)) =
      Tao.taoAffineOffsetZMod
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z) := by
  rw [ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord]
  rw [Tao.taoAffineOffsetZMod_reverse_eq_taoSection7OffsetZMod
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_word_length z)]
  exact ndGeom2PredictableRootSideBoundedOvershootIncidence_section7Compatible z

noncomputable def ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) : ℝ :=
  (3 : ℝ) ^ ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z *
    ((Tao.geom2PNatListPMF
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z))
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z)).toReal

noncomputable def ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (outerWeight : Label → ℝ)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) : ℝ :=
  outerWeight (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) *
    ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom z

noncomputable def ndGeom2PredictableRootSideBoundedOvershootIncidenceMass
    {Label : Type*} [Fintype Label]
    (outerWeight : Label → ℝ) (root base shift : Label → ℕ) (K : ℕ) : ℝ :=
  ∑ z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K,
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z

theorem ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom_nonneg
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    0 ≤ ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom z := by
  unfold ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom
  exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

theorem ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (outerWeight : Label → ℝ) (hweight : ∀ i, 0 ≤ outerWeight i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    0 ≤ ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      outerWeight z := by
  unfold ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
  exact mul_nonneg (hweight _)
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom_nonneg z)

def ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) : ℕ :=
  Tao.taoAffineSourceCandidate
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z)
    (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))

theorem ndGeom2PredictableRootSideBoundedOvershootIncidence_room
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    2 * 3 ^ ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z <
      root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) := by
  let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z
  exact ndGeom2ShiftedWideSymmetric_two_mul_three_pow_lt_root
    (hbaseNine i)
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_depth_mem z)
    (hrootLower i)

theorem ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd_and_affine
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    Odd (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) ∧
      Tao.taoAffList
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z)
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℚ) =
        (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) : ℚ) := by
  let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z
  obtain ⟨source, hAff, _hunique⟩ :=
    Tao.existsUnique_taoAffList_eq_of_affineOffsetZMod
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_chronologicalWord_length z)
      (hrootOdd i)
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_room
        hbaseNine hrootLower z)
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_affineCompatible z)
  have hsource :
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z =
        source.1 := by
    unfold ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
    exact Tao.taoAffineSourceCandidate_eq_of_taoAffList_eq
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_chronologicalWord_length z)
      hAff
  rw [hsource]
  exact ⟨source.2, hAff⟩

theorem ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    Odd (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) :=
  (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd_and_affine
    hrootOdd hbaseNine hrootLower z).1

theorem ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_valuation
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    Tao.syracuseValuationPNatList
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd
          hrootOdd hbaseNine hrootLower z) =
      ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z := by
  rcases Tao.taoAffList_oddNat_decode
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z)
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
      (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (hrootOdd _)
      ((ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd_and_affine
        hrootOdd hbaseNine hrootLower z).2) with
    ⟨_hodd, hvalues, _hiterate⟩
  simpa only [
    ndGeom2PredictableRootSideBoundedOvershootIncidence_chronologicalWord_length z]
    using hvalues

theorem ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_iterate
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    (Tao.syracuse^[
        ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z])
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) =
      root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) := by
  rcases Tao.taoAffList_oddNat_decode
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z)
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
      (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (hrootOdd _)
      ((ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd_and_affine
        hrootOdd hbaseNine hrootLower z).2) with
    ⟨_hodd, _hvalues, hiterate⟩
  simpa only [
    ndGeom2PredictableRootSideBoundedOvershootIncidence_chronologicalWord_length z]
    using hiterate

theorem ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_shell
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hbaseNine : ∀ i, 9 ≤ base i)
    (hrootLower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K) :
    2 ^ shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) *
          4 ^ base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) *
          root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) ≤
        4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius
            (base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)) *
          3 ^ base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) *
          ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z ∧
      2 ^ ndGeom2ShiftedWideSymmetricShiftRadius
            (base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)) *
          3 ^ base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) *
          ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z ≤
        2 * 2 ^ K *
          2 ^ shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) *
          4 ^ base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) *
          root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) := by
  let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z
  let b := base i
  let a := shift i
  let s := ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z
  let rootSide :=
    ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z
  let word :=
    ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord z
  have hhitRootSide : ndGeom2ShiftedWideSymmetricHit b a s rootSide :=
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_firstCrossing z).2.1.2
  have hhitWord : ndGeom2ShiftedWideSymmetricHit b a s word := by
    exact ndGeom2ShiftedWideSymmetricHit_reverse_of_length
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_word_length z)
      hhitRootSide
  have hoverWord : ndGeom2ShiftedWideSymmetricBoundedOvershoot b a s K word := by
    exact (ndGeom2ShiftedWideSymmetricBoundedOvershoot_reverse
      b a s K rootSide).2
        (ndGeom2PredictableRootSideBoundedOvershootIncidence_boundedOvershoot z)
  exact shiftedWideSymmetric_affineSource_crossBounds_of_boundedOvershoot
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_chronologicalWord_length z)
    hhitWord hoverWord
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_room
      hbaseNine hrootLower z)
    ((ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd_and_affine
      hrootOdd hbaseNine hrootLower z).2)

theorem ndGeom2PredictableRootSideBoundedOvershootIncidence_ext
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    {z w : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K}
    (hlabel :
      ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel w)
    (hdepth :
      ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth w)
    (hword :
      ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord w) :
    z = w := by
  rcases z with ⟨i, s, zword⟩
  rcases w with ⟨j, t, wword⟩
  change i = j at hlabel
  subst j
  change (s : ℕ) = (t : ℕ) at hdepth
  have hst : s = t := Subtype.ext hdepth
  subst t
  change zword.1 = wword.1 at hword
  have hzw : zword = wword := Subtype.ext hword
  subst wword
  rfl

private theorem ndFiniteFirstHitAt_unique_depth
    {I : Finset ℕ} {Hit : ℕ → List ℕ+ → Prop}
    {s t : ℕ} {full : List ℕ+}
    (hs : ndFiniteFirstHitAt I Hit s full)
    (ht : ndFiniteFirstHitAt I Hit t full) :
    s = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact (ht.2.2 s hs.1 hst) hs.2.1
  · exact (hs.2.2 t ht.1 hts) ht.2.1

theorem
    ndGeom2PredictableRootSideBoundedOvershootIncidence_eq_of_label_eq_of_commonPrefix
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    {z w : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root base shift K}
    (hlabel :
      ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel w)
    {fullRootSide : List ℕ+}
    (hzPrefix :
      ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z =
        fullRootSide.take
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z))
    (hwPrefix :
      ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord w =
        fullRootSide.take
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth w)) :
    z = w := by
  let iz := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z
  let iw := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel w
  let sz := ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z
  let sw := ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth w
  have hzFirstTake :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base iz))
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit
          (base iz) (shift iz)) sz
        (fullRootSide.take sz) := by
    simpa only [iz, sz, ← hzPrefix] using
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_firstCrossing z)
  have hzFirst :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base iz))
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit
          (base iz) (shift iz)) sz fullRootSide :=
    (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff
      (base iz) (shift iz) sz fullRootSide).mp hzFirstTake
  have hwFirstTake :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base iw))
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit
          (base iw) (shift iw)) sw
        (fullRootSide.take sw) := by
    simpa only [iw, sw, ← hwPrefix] using
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_firstCrossing w)
  have hwFirst :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base iw))
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit
          (base iw) (shift iw)) sw fullRootSide :=
    (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff
      (base iw) (shift iw) sw fullRootSide).mp hwFirstTake
  have hi : iz = iw := hlabel
  have hwFirst' :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths (base iz))
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit
          (base iz) (shift iz)) sw fullRootSide := by
    simpa only [hi] using hwFirst
  have hdepth : sz = sw := ndFiniteFirstHitAt_unique_depth hzFirst hwFirst'
  have hdepth' :
      ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth w := by
    simpa only [sz, sw] using hdepth
  have hword :
      ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord w := by
    rw [hzPrefix, hwPrefix, hdepth']
  exact ndGeom2PredictableRootSideBoundedOvershootIncidence_ext
    hlabel hdepth' hword

end

end PositiveDensity

end ND

end Erdos1135Predecessor
