/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUniformFloorPhysical

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

universe u

noncomputable def
    ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset
    (b a s K : ℕ) (u : ZMod (3 ^ 1))
    (x : ZMod (3 ^ (1 + s))) : Finset (List ℕ+) := by
  classical
  exact
    (Tao.shortValuationLists s
      (ndGeom2ShiftedWideSymmetricBoundedOvershootWordCutoff b a s K)).filter
        fun rootSide =>
          ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt
              b a s K rootSide ∧
            ndReversedPrefixAmbientChild s rootSide u = x

theorem
    mem_ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset_iff
    {b a s K : ℕ} {u : ZMod (3 ^ 1)} {x : ZMod (3 ^ (1 + s))}
    {rootSide : List ℕ+} :
    rootSide ∈
        ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset
          b a s K u x ↔
      rootSide.length = s ∧
        ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt
            b a s K rootSide ∧
          ndReversedPrefixAmbientChild s rootSide u = x := by
  classical
  constructor
  · intro hword
    rcases Finset.mem_filter.mp hword with ⟨hshort, hevent, hchild⟩
    rcases Tao.mem_shortValuationLists_iff.mp hshort with ⟨v, rfl⟩
    exact ⟨Tao.BoundedValuationTuple.toList_length v, hevent, hchild⟩
  · rintro ⟨hlen, hevent, hchild⟩
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
    refine ⟨?_, hevent, hchild⟩
    rw [Tao.mem_shortValuationLists_iff]
    exact ⟨v, (Tao.BoundedValuationTuple.toList_ofList
      rootSide hlen hweight).symm⟩

abbrev NDGeom2RootSideUnitDigit :=
  {u : ZMod (3 ^ 1) // IsUnit u}

abbrev NDGeom2ShiftedWideSymmetricRootSideUnitChildWord
    (root b a K : ℕ)
    (s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b)
    (u : NDGeom2RootSideUnitDigit) :=
  {rootSide : List ℕ+ // rootSide ∈
    ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset
      b a s.1 K u.1 (root : ZMod (3 ^ (1 + s.1)))}

noncomputable instance instFintypeShiftedWideSymmetricRootSideUnitChildWord
    (root b a K : ℕ)
    (s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b)
    (u : NDGeom2RootSideUnitDigit) :
    Fintype
      (NDGeom2ShiftedWideSymmetricRootSideUnitChildWord root b a K s u) :=
  Fintype.ofFinset
    (ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset
      b a s.1 K u.1 (root : ZMod (3 ^ (1 + s.1))))
    (by intro rootSide; rfl)

abbrev NDGeom2PredictableRootSideUnitChildIncidence
    {Label : Type*} (Labels : Finset Label) (root : Label → ℕ)
    (b a K : ℕ) :=
  Σ i : {i : Label // i ∈ Labels},
    Σ s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b,
      Σ u : NDGeom2RootSideUnitDigit,
        NDGeom2ShiftedWideSymmetricRootSideUnitChildWord
          (root i.1) b a K s u

def ndGeom2PredictableRootSideUnitChildIncidenceLabel
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) : Label :=
  z.1.1

def ndGeom2PredictableRootSideUnitChildIncidenceDepth
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) : ℕ :=
  z.2.1.1

def ndGeom2PredictableRootSideUnitChildIncidenceDigit
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) : ZMod (3 ^ 1) :=
  z.2.2.1.1

def ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) : List ℕ+ :=
  z.2.2.2.1

noncomputable def ndGeom2PredictableRootSideUnitChildIncidenceAtom
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) : ℝ :=
  (3 : ℝ) ^ ndGeom2PredictableRootSideUnitChildIncidenceDepth z *
    ((Tao.geom2PNatListPMF
      (ndGeom2PredictableRootSideUnitChildIncidenceDepth z))
      (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z)).toReal

noncomputable def ndGeom2PredictableRootSideUnitChildIncidenceWeight
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ} (outerWeight : Label → ℝ)
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) : ℝ :=
  outerWeight (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) *
    ndGeom2PredictableRootSideUnitChildIncidenceAtom z

noncomputable def ndGeom2PredictableRootSideUnitChildIncidenceMass
    {Label : Type*} (Labels : Finset Label)
    (outerWeight : Label → ℝ) (root : Label → ℕ)
    (b a K : ℕ) : ℝ :=
  ∑ z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K,
    ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z

theorem ndGeom2PredictableRootSideUnitChildIncidenceAtom_nonneg
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) :
    0 ≤ ndGeom2PredictableRootSideUnitChildIncidenceAtom z := by
  unfold ndGeom2PredictableRootSideUnitChildIncidenceAtom
  exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

theorem ndGeom2PredictableRootSideUnitChildIncidenceWeight_nonneg
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ} (outerWeight : Label → ℝ)
    (hweight : ∀ i ∈ Labels, 0 ≤ outerWeight i)
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) :
    0 ≤ ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z := by
  unfold ndGeom2PredictableRootSideUnitChildIncidenceWeight
  exact mul_nonneg (hweight z.1.1 z.1.2)
    (ndGeom2PredictableRootSideUnitChildIncidenceAtom_nonneg z)

def ndGeom2PredictableRootSideUnitChildIncidence.toPhysical
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) :
    NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root (fun _ => b) (fun _ => a) K := by
  let i := ndGeom2PredictableRootSideUnitChildIncidenceLabel z
  let s := z.2.1
  let u := z.2.2.1
  let rootSide := ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z
  have hunit :=
    (mem_ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset_iff).1
      z.2.2.2.2
  have hprojection :=
    ndReversedPrefixAmbientChild_projection s.1 rootSide u.1
  have hchild :
      ndReversedPrefixAmbientChild s.1 rootSide u.1 =
        (root i : ZMod (3 ^ (1 + s.1))) := by
    simpa only [i, s, u, rootSide] using hunit.2.2
  have hoffset :
      Tao.taoSection7OffsetZMod s.1 rootSide =
        (root i : ZMod (3 ^ s.1)) := by
    calc
      Tao.taoSection7OffsetZMod s.1 rootSide =
          Tao.taoZModThreeProjection (show s.1 ≤ 1 + s.1 by omega)
            (ndReversedPrefixAmbientChild s.1 rootSide u.1) :=
        hprojection.symm
      _ = Tao.taoZModThreeProjection (show s.1 ≤ 1 + s.1 by omega)
            (root i : ZMod (3 ^ (1 + s.1))) := by rw [hchild]
      _ = (root i : ZMod (3 ^ s.1)) :=
        Tao.taoZModThreeProjection_natCast
          (show s.1 ≤ 1 + s.1 by omega) (root i)
  refine ⟨i, s, ⟨rootSide, ?_⟩⟩
  exact
    (mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff).2
      ⟨hunit.1, hunit.2.1, hoffset⟩

@[simp] theorem ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_label
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z) =
      ndGeom2PredictableRootSideUnitChildIncidenceLabel z := by
  rfl

@[simp] theorem ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_depth
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z) =
      ndGeom2PredictableRootSideUnitChildIncidenceDepth z := by
  rfl

@[simp] theorem ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_word
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z) =
      ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z := by
  rfl

theorem ndGeom2PredictableRootSideUnitChildIncidence_sourceDigit_eq
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) :
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z) :
        ZMod (3 ^ 1)) =
      ndGeom2PredictableRootSideUnitChildIncidenceDigit z := by
  let physical := ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z
  let s := ndGeom2PredictableRootSideUnitChildIncidenceDepth z
  let rootSide := ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z
  let u := z.2.2.1
  have hword :=
    (mem_ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset_iff).1
      z.2.2.2.2
  have hrootActual :
      (root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) :
          ZMod (3 ^ (1 + s))) =
        ndReversedPrefixAmbientChild s rootSide u.1 := by
    simpa only [s, rootSide, u] using hword.2.2.symm
  have hsource :
      (root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) :
          ZMod (3 ^ (1 + s))) =
        ndReversedPrefixAmbientChild s rootSide
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource physical :
            ZMod (3 ^ 1)) := by
    simpa only [physical, s, rootSide] using
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_root_eq_ambientChild_sourceDigit
        hrootOdd (fun _ => hb) hrootLower physical)
  apply ndReversedPrefixAmbientChild_injective s rootSide
  exact hsource.symm.trans hrootActual

def ndGeom2PredictableRootSideUnitChildIncidenceSource
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) : ℕ :=
  ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
    (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z)

theorem ndGeom2PredictableRootSideUnitChildIncidenceSource_odd
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) :
    Odd (ndGeom2PredictableRootSideUnitChildIncidenceSource z) := by
  unfold ndGeom2PredictableRootSideUnitChildIncidenceSource
  exact
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd
      hrootOdd (fun _ => hb) hrootLower
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z)

noncomputable def
    NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorAllLabels
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState) : Finset S.Label :=
  @Finset.univ S.Label S.labelFintype

def NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNextRoot
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState) {b K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      S.rootSideUniformFloorAllLabels S.root b
        (ndGeom2ShiftedWideSymmetricShiftRadius b) K) : ℕ :=
  ndGeom2PredictableRootSideUnitChildIncidenceSource z

def NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNextBase
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState) {b K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      S.rootSideUniformFloorAllLabels S.root b
        (ndGeom2ShiftedWideSymmetricShiftRadius b) K) : ℕ :=
  ndA5QOneRootDyadicBase (S.rootSideUniformFloorUnitNextRoot z)

noncomputable def
    NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNextWeight
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState) {b K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      S.rootSideUniformFloorAllLabels S.root b
        (ndGeom2ShiftedWideSymmetricShiftRadius b) K) : ℝ :=
  ndGeom2PredictableRootSideUnitChildIncidenceWeight S.outerWeight z

noncomputable def
    NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNext
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState)
    (b K : ℕ) (hb : 200 ≤ b) (hfloor : ∀ i, b ≤ S.base i) :
    NDGeom2ShiftedWideSymmetricRegenerativeState := by
  letI := S.labelFintype
  have hpacketRootLower : ∀ i, 16 ^ b ≤ S.root i := by
    intro i
    exact
      (Nat.pow_le_pow_right (by norm_num) (hfloor i)).trans
        (S.rootLower i)
  exact {
    Label := NDGeom2PredictableRootSideUnitChildIncidence
      S.rootSideUniformFloorAllLabels S.root b
        (ndGeom2ShiftedWideSymmetricShiftRadius b) K
    labelFintype := inferInstance
    root := S.rootSideUniformFloorUnitNextRoot
    base := S.rootSideUniformFloorUnitNextBase
    outerWeight := S.rootSideUniformFloorUnitNextWeight
    weight_nonneg := fun z => by
      unfold
        NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNextWeight
      exact ndGeom2PredictableRootSideUnitChildIncidenceWeight_nonneg
        S.outerWeight (fun i _hi => S.weight_nonneg i) z
    root_odd := fun z => by
      unfold
        NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNextRoot
      exact ndGeom2PredictableRootSideUnitChildIncidenceSource_odd
        S.root_odd (by omega) hpacketRootLower z
    base_eq := fun _z => rfl
    base_twoHundred := fun z => by
      have hgrowth :=
        ndGeom2PredictableRootSideUniformFloorIncidence_floor_add_oneHundredth_le_sourceBase
          S.root_odd hb hfloor S.rootLower
            (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z)
      change 200 ≤ ndA5QOneRootDyadicBase
        (ndGeom2PredictableRootSideUnitChildIncidenceSource z)
      simpa only [ndGeom2PredictableRootSideUnitChildIncidenceSource]
        using hb.trans (show b ≤
          ndA5QOneRootDyadicBase
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
              (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z)) by
                omega) }

theorem
    NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNext_floor_add_oneHundredth_le_base
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState)
    (b K : ℕ) (hb : 200 ≤ b) (hfloor : ∀ i, b ≤ S.base i)
    (z : (S.rootSideUniformFloorUnitNext b K hb hfloor).Label) :
    b + b / 100 ≤
      (S.rootSideUniformFloorUnitNext b K hb hfloor).base z := by
  change NDGeom2PredictableRootSideUnitChildIncidence
    S.rootSideUniformFloorAllLabels S.root b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) K at z
  change b + b / 100 ≤
    ndA5QOneRootDyadicBase
      (ndGeom2PredictableRootSideUnitChildIncidenceSource z)
  simpa only [ndGeom2PredictableRootSideUnitChildIncidenceSource] using
    (ndGeom2PredictableRootSideUniformFloorIncidence_floor_add_oneHundredth_le_sourceBase
      S.root_odd hb hfloor S.rootLower
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z))

theorem
    NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNext_root_mem_same_target
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState)
    (b K : ℕ) (hb : 200 ≤ b) (hfloor : ∀ i, b ≤ S.base i)
    {C : ℝ} (hC : 250 ≤ C)
    (hrootTarget : ∀ i, S.root i ∈ oddSyracuseLogTimeOneSet C) :
    ∀ z : (S.rootSideUniformFloorUnitNext b K hb hfloor).Label,
      (S.rootSideUniformFloorUnitNext b K hb hfloor).root z ∈
        oddSyracuseLogTimeOneSet C := by
  intro z
  change NDGeom2PredictableRootSideUnitChildIncidence
    S.rootSideUniformFloorAllLabels S.root b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) K at z
  change ndGeom2PredictableRootSideUnitChildIncidenceSource z ∈
    oddSyracuseLogTimeOneSet C
  unfold ndGeom2PredictableRootSideUnitChildIncidenceSource
  exact
    (ndGeom2PredictableRootSideUniformFloorIncidenceSource_mem_same_oddSyracuseLogTimeOneSet
      S.root_odd hb hfloor S.rootLower S.rootSideRootUpper hC hrootTarget
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z))

structure NDGeom2ShiftedWideSymmetricRootSideUniformFloorState where
  state : NDGeom2ShiftedWideSymmetricRegenerativeState
  floor : ℕ
  floor_twoHundred : 200 ≤ floor
  floor_le_base : ∀ i, floor ≤ state.base i

noncomputable def
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.denominator
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) : ℝ :=
  U.state.denominator

noncomputable def
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.parentSourcePotential
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) : ℝ :=
  ndGeom2PredictableRootSideParentSourcePotential
    U.state.rootSideUniformFloorAllLabels U.state.outerWeight U.state.root

noncomputable def
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.next
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ) :
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState :=
  { state := U.state.rootSideUniformFloorUnitNext
      U.floor K U.floor_twoHundred U.floor_le_base
    floor := U.floor + U.floor / 100
    floor_twoHundred := by
      have hfloor := U.floor_twoHundred
      omega
    floor_le_base := fun z =>
      U.state.rootSideUniformFloorUnitNext_floor_add_oneHundredth_le_base
        U.floor K U.floor_twoHundred U.floor_le_base z }

theorem
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.twoHundredOne_mul_floor_le_twoHundred_mul_next_floor
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ) :
    201 * U.floor ≤ 200 * (U.next K).floor := by
  simp only [NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.next]
  have hfloor := U.floor_twoHundred
  have hdiv := Nat.div_add_mod U.floor 100
  omega

noncomputable def
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.iterate
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : ℕ →
      NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
  | 0 => U
  | n + 1 => (U.iterate cap n).next (cap n)

theorem
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.iterate_twoHundredOne_mul_floor_le_twoHundred_mul_next_floor
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    201 * (U.iterate cap n).floor ≤
      200 * (U.iterate cap (n + 1)).floor := by
  simpa only [NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.iterate]
    using
      (U.iterate cap n).twoHundredOne_mul_floor_le_twoHundred_mul_next_floor
        (cap n)

theorem
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.iterate_root_mem_same_target
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) {C : ℝ} (hC : 250 ≤ C)
    (hrootTarget : ∀ i, U.state.root i ∈ oddSyracuseLogTimeOneSet C) :
    ∀ n, ∀ z : (U.iterate cap n).state.Label,
      (U.iterate cap n).state.root z ∈ oddSyracuseLogTimeOneSet C := by
  intro n
  induction n with
  | zero =>
      simpa only [NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.iterate]
        using hrootTarget
  | succ n ih =>
      simpa only [NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.iterate]
        using
          (U.iterate cap n).state.rootSideUniformFloorUnitNext_root_mem_same_target
            (U.iterate cap n).floor (cap n)
            (U.iterate cap n).floor_twoHundred
            (U.iterate cap n).floor_le_base hC ih

end

end PositiveDensity

end ND

end Erdos1135Predecessor
