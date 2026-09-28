/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricReferenceDensityTransport

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem ndNatCast_eq_referencePrefixParent_source_of_affine
    {d N M : ℕ} (t : ℕ) {word : List ℕ+}
    (hlen : word.length = d)
    (hAff : Tao.taoAffList word.reverse (N : ℚ) = (M : ℚ)) :
    (M : ZMod (3 ^ (t + d))) =
      ndReferencePrefixParent d t word (N : ZMod (3 ^ t)) := by
  let R := ZMod (3 ^ (t + d))
  have hhead : Tao.taoSection7OffsetPrefix (t + d) d word =
      Tao.taoAffineOffsetZModAt (t + d) word.reverse := by
    rw [Tao.taoAffineOffsetZModAt_reverse_eq_offsetPrefix, hlen]
  have hprojection := Tao.taoZModThreeProjection_natCast
    (show t ≤ t + d by omega) N
  have hscaled :=
    Tao.taoSection6_three_pow_mul_val_eq_three_pow_mul_of_projection_eq
      t d (N : ZMod (3 ^ (t + d))) (N : ZMod (3 ^ t)) hprojection
  have htail : Tao.taoSection6AmbientTailEmbed d t (Tao.taoTupleWeight word)
      (N : ZMod (3 ^ t)) =
        (3 : R) ^ d * (((2 : R) ^ Tao.taoTupleWeight word)⁻¹) * (N : R) := by
    unfold Tao.taoSection6AmbientTailEmbed
    rw [← ZMod.inv_coe_unit, Tao.taoCor63TwoPowUnit_coe]
    calc
      (3 : R) ^ d * (((2 : R) ^ Tao.taoTupleWeight word)⁻¹) *
          (((N : ZMod (3 ^ t)).val : ℕ) : R) =
        (((2 : R) ^ Tao.taoTupleWeight word)⁻¹) *
          ((3 : R) ^ d * (((N : ZMod (3 ^ t)).val : ℕ) : R)) := by ring
      _ = (((2 : R) ^ Tao.taoTupleWeight word)⁻¹) *
          ((3 : R) ^ d * (N : R)) := by rw [hscaled]
      _ = _ := by ring
  have hclear := (Tao.taoAffList_eq_nat_iff_cleared word.reverse N M).mp hAff
  have hcast := congrArg (fun x : ℕ => (x : R)) hclear
  have hcast' : (3 : R) ^ d * (N : R) + (Tao.taoOffsetNum word.reverse : R) =
      (2 : R) ^ Tao.taoTupleWeight word * (M : R) := by
    dsimp only [R] at hcast ⊢
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast ⊢
    simpa only [List.length_reverse, hlen, Tao.taoTupleWeight_reverse] using hcast
  have hinv := Tao.taoZModThreePow_inv_two_pow_mul (t + d) (Tao.taoTupleWeight word)
  unfold ndReferencePrefixParent ndCommonZAmbientTailFiberPoint
  rw [hhead, htail]
  unfold Tao.taoAffineOffsetZModAt
  calc
    (M : R) = 1 * (M : R) := by ring
    _ = ((((2 : R) ^ Tao.taoTupleWeight word)⁻¹) *
          ((2 : R) ^ Tao.taoTupleWeight word)) * (M : R) := by rw [hinv]
    _ = (((2 : R) ^ Tao.taoTupleWeight word)⁻¹) *
          (((2 : R) ^ Tao.taoTupleWeight word) * (M : R)) := by ring
    _ = (((2 : R) ^ Tao.taoTupleWeight word)⁻¹) *
          ((3 : R) ^ d * (N : R) + (Tao.taoOffsetNum word.reverse : R)) := by
      rw [hcast']
    _ = (Tao.taoOffsetNum word.reverse : R) *
          (((2 : R) ^ Tao.taoTupleWeight word.reverse)⁻¹) +
        (3 : R) ^ d * (((2 : R) ^ Tao.taoTupleWeight word)⁻¹) * (N : R) := by
      rw [Tao.taoTupleWeight_reverse]
      ring

theorem referenceWordTransport_apply_parent
    (d t : ℕ) (word : List ℕ+) (g : ZMod (3 ^ t) → ℝ) (z : ZMod (3 ^ t)) :
    ndReferenceWordTransport d t word g (ndReferencePrefixParent d t word z) =
      (3 : ℝ) ^ d * (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) * g z := by
  classical
  rw [referenceWordTransport_eq_sum]
  simp [(ndReferencePrefixParent_injective d t word).eq_iff]

theorem referenceWordTransport_apply_physical_source
    {d N M : ℕ} (t : ℕ) {word : List ℕ+}
    (hlen : word.length = d)
    (hAff : Tao.taoAffList word.reverse (N : ℚ) = (M : ℚ))
    (g : ZMod (3 ^ t) → ℝ) :
    ndReferenceWordTransport d t word g (M : ZMod (3 ^ (t + d))) =
      (3 : ℝ) ^ d * (Tao.geom2PNatListPMF d word).toReal *
        g (N : ZMod (3 ^ t)) := by
  rw [ndNatCast_eq_referencePrefixParent_source_of_affine t hlen hAff,
    referenceWordTransport_apply_parent]
  rw [show (Tao.geom2PNatListPMF d word).toReal =
      (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) by
    simpa only [hlen] using referencePrefix_atom_eq word]

theorem referencePrefixTransportAt_apply_physical_source
    {N M : ℕ} (q k : ℕ) (word : List ℕ+)
    (hlen : word.length ≤ q) (hk : k ≤ q - word.length)
    (hAff : Tao.taoAffList word.reverse (N : ℚ) = (M : ℚ))
    (g : ZMod (3 ^ k) → ℝ) :
    ndReferencePrefixTransportAt q word hlen
        (fun z => g (Tao.taoZModThreeProjection hk z)) (M : ZMod (3 ^ q)) =
      (3 : ℝ) ^ word.length * (Tao.geom2PNatListPMF word.length word).toReal *
        g (N : ZMod (3 ^ k)) := by
  rw [referencePrefixTransportAt_apply_natCast,
    referenceWordTransport_apply_physical_source _ rfl hAff,
    Tao.taoZModThreeProjection_natCast]

theorem referencePrefixTransportAt_apply_unitIncidence
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K)
    (q k : ℕ)
    (hlen : (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z).length ≤ q)
    (hk : k ≤ q - (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z).length)
    (g : ZMod (3 ^ k) → ℝ) :
    ndReferencePrefixTransportAt q
        (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z) hlen
        (fun v => g (Tao.taoZModThreeProjection hk v))
        (root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) : ZMod (3 ^ q)) =
      ndGeom2PredictableRootSideUnitChildIncidenceAtom z *
        g (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ZMod (3 ^ k)) := by
  have ha := (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd_and_affine
    hrootOdd (fun _ => hb) hrootLower
    (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z)).2
  change Tao.taoAffList (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z).reverse
    (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ℚ) =
      (root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) : ℚ) at ha
  rw [referencePrefixTransportAt_apply_physical_source _ _ _ _ _ ha]
  unfold ndGeom2PredictableRootSideUnitChildIncidenceAtom
  rw [ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length]

def unitIncidenceSelectedWord
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K) :
    {i : Label // i ∈ Labels} × ndShiftedReferenceSelectedWords b a K := by
  refine ⟨z.1, ⟨ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z, ?_⟩⟩
  rw [mem_shiftedReferenceSelectedWords_iff,
    ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length]
  exact (mem_ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset_iff.mp z.2.2.2.2).2.1

theorem unitIncidenceSelectedWord_injective
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i) :
    Function.Injective
      (unitIncidenceSelectedWord (Labels := Labels) (root := root) (b := b) (a := a) (K := K)) := by
  intro z w heq
  have hl : ndGeom2PredictableRootSideUnitChildIncidenceLabel z =
      ndGeom2PredictableRootSideUnitChildIncidenceLabel w :=
    congrArg (fun p => p.1.val) heq
  have hw : ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z =
      ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord w :=
    congrArg (fun p => p.2.val) heq
  have hz := ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length z
  have hwlen := ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length w
  apply ndGeom2PredictableRootSideUnitChildIncidence_eq_of_label_eq_of_commonPrefix
    hrootOdd hb hrootLower hl (fullRootSide := ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z)
  · rw [← hz, List.take_length]
  · rw [hw, ← hwlen, List.take_length]

theorem referencePrefixParent_projection (d t : ℕ) (word : List ℕ+)
    (v : ZMod (3 ^ t)) :
    Tao.taoZModThreeProjection (show d ≤ t + d by omega)
        (ndReferencePrefixParent d t word v) = Tao.taoSection7OffsetZMod d word := by
  unfold ndReferencePrefixParent
  rw [ndCommonZAmbientTailFiberPoint_projection, ndCommonZHeadPrefix_projection_eq_offset]

theorem exists_unitIncidence_of_referencePrefixTransportAt_ne_zero
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (q k : ℕ) (g : ZMod (3 ^ k) → ℝ)
    (hunit : ∀ N : ℕ, ¬ IsUnit (N : ZMod (3 ^ 1)) → g (N : ZMod (3 ^ k)) = 0)
    (x : {i : Label // i ∈ Labels} × ndShiftedReferenceSelectedWords b a K)
    (hlen : x.2.val.length ≤ q) (hk : k ≤ q - x.2.val.length)
    (hne : ndReferencePrefixTransportAt q x.2.val hlen
      (fun v => g (Tao.taoZModThreeProjection hk v)) (root x.1.val : ZMod (3 ^ q)) ≠ 0) :
    ∃ z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K,
      unitIncidenceSelectedWord z = x := by
  classical
  let w := x.2.val
  let d := w.length
  let t := q - d
  have hevent := (mem_shiftedReferenceSelectedWords_iff b a K w).mp x.2.property
  have hsum : (∑ v : ZMod (3 ^ t),
      if ndReferencePrefixParent d t w v = (root x.1.val : ZMod (3 ^ (t + d)))
      then g (Tao.taoZModThreeProjection hk v) else 0) ≠ 0 := by
    intro hh
    apply hne
    rw [referencePrefixTransportAt_apply_natCast, referenceWordTransport_eq_sum]
    change (3 : ℝ) ^ d * (2 : ℝ) ^ (-(Tao.taoTupleWeight w : ℤ)) * _ = 0
    rw [hh, mul_zero]
  obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hp : ndReferencePrefixParent d t w v =
      (root x.1.val : ZMod (3 ^ (t + d))) := by
    by_contra hh
    simp [hh] at hv
  have hoffset : Tao.taoSection7OffsetZMod d w = (root x.1.val : ZMod (3 ^ d)) := by
    have hh := referencePrefixParent_projection d t w v
    rw [hp, Tao.taoZModThreeProjection_natCast] at hh
    exact hh.symm
  let s : NDGeom2ShiftedWideSymmetricBoundedOvershootDepth b := ⟨d, hevent.1.1⟩
  let p : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root
      (fun _ => b) (fun _ => a) K :=
    ⟨x.1.val, s, ⟨w, mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mpr
      ⟨rfl, hevent, hoffset⟩⟩⟩
  let N := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource p
  have ha := (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd_and_affine
    hrootOdd (fun _ => hb) hrootLower p).2
  change Tao.taoAffList w.reverse (N : ℚ) = (root x.1.val : ℚ) at ha
  have hu : IsUnit (N : ZMod (3 ^ 1)) := by
    by_contra hh
    apply hne
    rw [referencePrefixTransportAt_apply_physical_source _ _ _ _ _ ha, hunit N hh, mul_zero]
  have hc : ndReversedPrefixAmbientChild d w (N : ZMod (3 ^ 1)) =
      (root x.1.val : ZMod (3 ^ (1 + d))) :=
    (ndNatCast_eq_reversedPrefixAmbientChild_sourceDigit_of_affine rfl ha).symm
  let z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K :=
    ⟨x.1, s, ⟨N, hu⟩, ⟨w,
      mem_ndGeom2ShiftedWideSymmetricRootSideUnitChildWordFinset_iff.mpr ⟨rfl, hevent, hc⟩⟩⟩
  exact ⟨z, by apply Prod.ext <;> rfl⟩

private def shiftedReferenceWordMark (b a K k : ℕ)
    (g : ZMod (3 ^ k) → ℝ) (w : ndShiftedReferenceSelectedWords b a K) (M : ℕ) : ℝ :=
  ndReferencePrefixTransportAt (ndGeom2ShiftedWideSymmetricHorizon b + k) w.val
    (by have h := shiftedReferenceSelectedWords_length_le_horizon b a K w; omega)
    (fun v => g (Tao.taoZModThreeProjection
      (by have h := shiftedReferenceSelectedWords_length_le_horizon b a K w; omega) v))
    (M : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k)))

theorem sum_unitIncidence_mark_eq_selectedWordTransport
    {Label : Type*} (Labels : Finset Label) (root : Label → ℕ)
    (outerWeight : Label → ℝ) (b a K k : ℕ)
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (g : ZMod (3 ^ k) → ℝ)
    (hunit : ∀ N : ℕ, ¬ IsUnit (N : ZMod (3 ^ 1)) → g (N : ZMod (3 ^ k)) = 0) :
    (∑ z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K,
      ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z *
        g (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ZMod (3 ^ k))) =
      ∑ i : {i : Label // i ∈ Labels}, outerWeight i.val *
        ∑ w : ndShiftedReferenceSelectedWords b a K,
          shiftedReferenceWordMark b a K k g w (root i.val) := by
  classical
  let I := NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K
  let J := {i : Label // i ∈ Labels} × ndShiftedReferenceSelectedWords b a K
  let e : I → J := unitIncidenceSelectedWord
  let f (z : I) := ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z *
    g (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ZMod (3 ^ k))
  let h (x : J) := outerWeight x.1.val * shiftedReferenceWordMark b a K k g x.2 (root x.1.val)
  have hzero : ∀ x ∉ Set.range e, h x = 0 := by
    intro x hx
    have hz : shiftedReferenceWordMark b a K k g x.2 (root x.1.val) = 0 := by
      by_contra hn
      have hh := exists_unitIncidence_of_referencePrefixTransportAt_ne_zero
        hrootOdd hb hrootLower (ndGeom2ShiftedWideSymmetricHorizon b + k) k g hunit x
        (by have h := shiftedReferenceSelectedWords_length_le_horizon b a K x.2; omega)
        (by have h := shiftedReferenceSelectedWords_length_le_horizon b a K x.2; omega) hn
      exact hx hh
    simp only [h, hz, mul_zero]
  have hmatch : ∀ z, f z = h (e z) := by
    intro z
    have hw := shiftedReferenceSelectedWords_length_le_horizon b a K (e z).2
    change (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z).length ≤
      ndGeom2ShiftedWideSymmetricHorizon b at hw
    have heval := referencePrefixTransportAt_apply_unitIncidence hrootOdd hb hrootLower z
      (ndGeom2ShiftedWideSymmetricHorizon b + k) k (by omega) (by omega) g
    change _ = outerWeight (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) * _
    exact (mul_assoc _ _ _).trans
      (congrArg (fun v => outerWeight (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) * v)
        heval.symm)
  calc
    (∑ z : I, f z) = ∑ x : J, h x :=
      Fintype.sum_of_injective e
        (unitIncidenceSelectedWord_injective hrootOdd hb hrootLower) f h hzero hmatch
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [h, Finset.mul_sum]

theorem unitReferenceDensity_natCast_eq_zero_of_not_unit
    {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : ¬ IsUnit (N : ZMod (3 ^ 1))) :
    ndSyracuseUnitReferenceDensity k (N : ZMod (3 ^ k)) = 0 := by
  have hnot : ¬ ndThreeUnitResidue (N : ZMod (3 ^ k)) := by
    intro hh
    have hlow := (ndThreeUnitResidue_projection_iff (by omega : 0 < 1) hk _).mp hh
    rw [Tao.taoZModThreeProjection_natCast] at hlow
    exact hN ((ndThreeUnitResidue_iff_isUnit (by omega : 0 < 1) _).mp hlow)
  unfold ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity Tao.syracPMFMassVector
  rw [syracPMF_toReal_eq_zero_of_not_unit (by omega) _ hnot]
  simp

theorem sum_unitIncidence_referenceMark_eq_original_parent_kernel
    {Label : Type*} (Labels : Finset Label) (root : Label → ℕ)
    (outerWeight : Label → ℝ) (b a K k : ℕ)
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i) (hk : 1 ≤ k) :
    (∑ z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K,
      ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z *
        ndSyracuseUnitReferenceDensity k
          (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ZMod (3 ^ k))) =
      ∑ i : {i : Label // i ∈ Labels}, outerWeight i.val *
        ndShiftedReferenceMarkedKernel b a K k
          (root i.val : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))) := by
  exact sum_unitIncidence_mark_eq_selectedWordTransport Labels root outerWeight b a K k
    hrootOdd hb hrootLower (ndSyracuseUnitReferenceDensity k)
    (unitReferenceDensity_natCast_eq_zero_of_not_unit hk)

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem forwardIterate_succ_eq_next
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    U.forwardIterate cap (n + 1) = (U.forwardIterate cap n).next (cap n) := by
  rw [forwardIterate_eq_iterate, forwardIterate_eq_iterate]
  rfl

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
