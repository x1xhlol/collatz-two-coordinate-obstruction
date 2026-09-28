/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreStripRate
import Erdos1135Predecessor.ND.PositiveDensity.SuccessfulRootTernaryResidueCoverage

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

def ndRootCoreTransportWord (b a K k : ℕ) (g : ZMod (3 ^ k) → ℝ)
    (w : ndShiftedReferenceSelectedWords b a K) :
    ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k)) → ℝ :=
  ndReferencePrefixTransportAt (ndGeom2ShiftedWideSymmetricHorizon b + k) w.val
    (by have h := shiftedReferenceSelectedWords_length_le_horizon b a K w; omega)
    (fun z => g (Tao.taoZModThreeProjection
      (by have h := shiftedReferenceSelectedWords_length_le_horizon b a K w; omega) z))

def ndRootCoreFilteredKernel (b a K k : ℕ) (psi : List ℕ+ → ℝ)
    (g : ZMod (3 ^ k) → ℝ) :
    ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k)) → ℝ :=
  fun y => ∑ w : ndShiftedReferenceSelectedWords b a K,
    psi w.val * ndRootCoreTransportWord b a K k g w y

theorem sum_unitIncidence_word_mark_eq_filteredKernel
    {Label : Type*} (Labels : Finset Label) (root : Label → ℕ)
    (outerWeight : Label → ℝ) (b a K k : ℕ)
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (psi : List ℕ+ → ℝ) (g : ZMod (3 ^ k) → ℝ)
    (hunit : ∀ N : ℕ, ¬ IsUnit (N : ZMod (3 ^ 1)) → g (N : ZMod (3 ^ k)) = 0) :
    (∑ z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K,
      ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z *
        psi (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z) *
        g (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ZMod (3 ^ k))) =
      ∑ i : {i : Label // i ∈ Labels}, outerWeight i.val *
        ndRootCoreFilteredKernel b a K k psi g
          (root i.val : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))) := by
  classical
  let I := NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K
  let J := {i : Label // i ∈ Labels} × ndShiftedReferenceSelectedWords b a K
  let e : I → J := unitIncidenceSelectedWord
  let f (z : I) := ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z *
    psi (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z) *
    g (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ZMod (3 ^ k))
  let h (x : J) := outerWeight x.1.val *
    (psi x.2.val * ndRootCoreTransportWord b a K k g x.2
      (root x.1.val : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))))
  have hzero : ∀ x ∉ Set.range e, h x = 0 := by
    intro x hx
    have hz : ndRootCoreTransportWord b a K k g x.2
        (root x.1.val : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))) = 0 := by
      by_contra hn
      exact hx (exists_unitIncidence_of_referencePrefixTransportAt_ne_zero
        hrootOdd hb hrootLower (ndGeom2ShiftedWideSymmetricHorizon b + k) k g hunit x
        (by have h := shiftedReferenceSelectedWords_length_le_horizon b a K x.2; omega)
        (by have h := shiftedReferenceSelectedWords_length_le_horizon b a K x.2; omega) hn)
    simp only [h, hz, mul_zero]
  have hmatch : ∀ z, f z = h (e z) := by
    intro z
    have hw := shiftedReferenceSelectedWords_length_le_horizon b a K (e z).2
    change (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z).length ≤
      ndGeom2ShiftedWideSymmetricHorizon b at hw
    have heval := referencePrefixTransportAt_apply_unitIncidence hrootOdd hb hrootLower z
      (ndGeom2ShiftedWideSymmetricHorizon b + k) k (by omega) (by omega) g
    change _ = outerWeight (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) *
      (psi (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z) * _)
    change ndRootCoreTransportWord b a K k g (e z).2
      (root (e z).1.val : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))) = _ at heval
    rw [heval]
    dsimp only [f, ndGeom2PredictableRootSideUnitChildIncidenceWeight]
    ring
  calc
    (∑ z : I, f z) = ∑ x : J, h x := Fintype.sum_of_injective e
      (unitIncidenceSelectedWord_injective hrootOdd hb hrootLower) f h hzero hmatch
    _ = _ := by rw [Fintype.sum_prod_type]; simp only [h, ndRootCoreFilteredKernel, Finset.mul_sum]

theorem referenceWordTransport_nonneg (d t : ℕ) (word : List ℕ+)
    (g : ZMod (3 ^ t) → ℝ) (hg : ∀ z, 0 ≤ g z) (y : ZMod (3 ^ (t + d))) :
    0 ≤ ndReferenceWordTransport d t word g y := by
  classical
  rw [referenceWordTransport_eq_sum]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun z _ => by split_ifs <;> simp only [hg z, le_refl]

theorem referencePrefixTransportAt_nonneg (q : ℕ) (word : List ℕ+) (hlen : word.length ≤ q)
    (g : ZMod (3 ^ (q - word.length)) → ℝ) (hg : ∀ z, 0 ≤ g z) (y : ZMod (3 ^ q)) :
    0 ≤ ndReferencePrefixTransportAt q word hlen g y := by
  have h := referenceWordTransport_nonneg word.length (q - word.length) word g hg
    (y.val : ZMod (3 ^ ((q - word.length) + word.length)))
  rw [← referencePrefixTransportAt_apply_natCast] at h
  simpa only [ZMod.natCast_zmod_val] using h

private theorem rootCore_uniformMean_lift {k q : ℕ} (hkq : k ≤ q)
    (g : ZMod (3 ^ k) → ℝ) :
    ndTernaryUniformMean q (fun z => g (Tao.taoZModThreeProjection hkq z)) =
      ndTernaryUniformMean k g := by
  classical
  let p : ZMod (3 ^ q) → ZMod (3 ^ k) := Tao.taoZModThreeProjection hkq
  have hs : (∑ y : ZMod (3 ^ q), g (p y)) =
      ((3 ^ (q - k) : ℕ) : ℝ) * ∑ z : ZMod (3 ^ k), g z := by
    rw [← Fintype.sum_fiberwise p (fun y => g (p y)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    calc
      (∑ y : {y : ZMod (3 ^ q) // p y = z}, g (p y.1)) =
          ∑ _y : {y : ZMod (3 ^ q) // p y = z}, g z := by
        apply Finset.sum_congr rfl
        intro y _
        rw [y.2]
      _ = _ := by
        have hc : Fintype.card {y : ZMod (3 ^ q) // p y = z} = 3 ^ (q - k) :=
          Tao.taoZModThreeProjection_fiber_card hkq z
        rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
  unfold ndTernaryUniformMean ndTernaryUniformScale
  change _ * (∑ y, g (p y)) = _
  rw [hs]
  have hp : (3 : ℝ) ^ q = 3 ^ (q - k) * 3 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkq]
  push_cast
  rw [hp]
  field_simp

theorem rootCoreTransportWord_nonneg (b a K k : ℕ) (g : ZMod (3 ^ k) → ℝ)
    (hg : ∀ z, 0 ≤ g z) (w : ndShiftedReferenceSelectedWords b a K)
    (y : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))) :
    0 ≤ ndRootCoreTransportWord b a K k g w y :=
  referencePrefixTransportAt_nonneg _ _ _ _ (fun _ => hg _) y

theorem rootCoreTransportWord_fullMean_eq (b a K k : ℕ) (g : ZMod (3 ^ k) → ℝ)
    (hg : ∀ z, 0 ≤ g z) (w : ndShiftedReferenceSelectedWords b a K) :
    ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + k)
        (ndRootCoreTransportWord b a K k g w) =
      (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ)) * ndTernaryUniformMean k g := by
  have hw := shiftedReferenceSelectedWords_length_le_horizon b a K w
  have h := referencePrefixTransportAt_fullL1_eq
    (ndGeom2ShiftedWideSymmetricHorizon b + k) w.val (by omega)
    (fun z => g (Tao.taoZModThreeProjection (by omega : k ≤
      ndGeom2ShiftedWideSymmetricHorizon b + k - w.val.length) z))
  change ndTernaryUniformMean _ (fun y => |ndRootCoreTransportWord b a K k g w y|) = _ at h
  simp_rw [abs_of_nonneg (rootCoreTransportWord_nonneg b a K k g hg w _), abs_of_nonneg (hg _)] at h
  rwa [rootCore_uniformMean_lift] at h

theorem rootCoreFilteredKernel_nonneg (b a K k : ℕ) (psi : List ℕ+ → ℝ)
    (hpsi : ∀ w, 0 ≤ psi w) (g : ZMod (3 ^ k) → ℝ) (hg : ∀ z, 0 ≤ g z)
    (y : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))) :
    0 ≤ ndRootCoreFilteredKernel b a K k psi g y :=
  Finset.sum_nonneg fun w _ => mul_nonneg (hpsi _) (rootCoreTransportWord_nonneg b a K k g hg w y)

theorem rootCoreFilteredKernel_fullMean_eq (b a K k : ℕ) (psi : List ℕ+ → ℝ)
    (g : ZMod (3 ^ k) → ℝ) (hg : ∀ z, 0 ≤ g z) :
    ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + k)
        (ndRootCoreFilteredKernel b a K k psi g) =
      (∑ w : ndShiftedReferenceSelectedWords b a K,
        psi w.val * (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ))) *
          ndTernaryUniformMean k g := by
  unfold ndTernaryUniformMean ndRootCoreFilteredKernel
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Finset.mul_sum]
  have h := rootCoreTransportWord_fullMean_eq b a K k g hg w
  unfold ndTernaryUniformMean at h
  calc
    _ = psi w.val * (ndTernaryUniformScale _ * ∑ y, ndRootCoreTransportWord b a K k g w y) := by ring
    _ = _ := by rw [h]; ring

theorem referencePrefixParent_isUnit {d : ℕ} (hd : 0 < d)
    (t : ℕ) (word : List ℕ+) (z : ZMod (3 ^ t)) :
    IsUnit (ndReferencePrefixParent d t word z) := by
  have hp : ndThreeUnitResidue (Tao.taoZModThreeProjection (show d ≤ t + d by omega)
      (ndReferencePrefixParent d t word z)) := by
    rw [referencePrefixParent_projection]
    exact ndThreeUnitResidue_taoSection7OffsetZMod hd word
  have hu := (ndThreeUnitResidue_projection_iff hd (show d ≤ t + d by omega) _).2 hp
  exact (ndThreeUnitResidue_iff_isUnit (by omega : 0 < t + d) _).mp hu

theorem rootCoreTransportWord_natCast_eq_zero_of_not_unit
    (b a K k : ℕ) (g : ZMod (3 ^ k) → ℝ)
    (w : ndShiftedReferenceSelectedWords b a K) (N : ℕ)
    (hN : ¬ IsUnit (N : ZMod (3 ^ 1))) :
    ndRootCoreTransportWord b a K k g w
      (N : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))) = 0 := by
  classical
  have he := (mem_shiftedReferenceSelectedWords_iff b a K w.val).mp w.property
  have hd : 0 < w.val.length := by
    have h := (Finset.mem_Icc.mp he.1.1).1
    unfold ndGeom2ShiftedWideSymmetricLower ndGeom2ShiftedWideSymmetricWidth at h
    omega
  unfold ndRootCoreTransportWord
  rw [referencePrefixTransportAt_apply_natCast, referenceWordTransport_eq_sum]
  have hz : ∀ z : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k - w.val.length)),
      ndReferencePrefixParent w.val.length _ w.val z ≠
        (N : ZMod (3 ^ ((ndGeom2ShiftedWideSymmetricHorizon b + k - w.val.length) + w.val.length))) := by
    intro z hh
    have hu := referencePrefixParent_isUnit hd _ w.val z
    rw [hh] at hu
    have hup := (ndThreeUnitResidue_iff_isUnit (by omega) _).mpr hu
    have hlow := (ndThreeUnitResidue_projection_iff (by omega : 0 < 1)
      (by omega : 1 ≤ (ndGeom2ShiftedWideSymmetricHorizon b + k - w.val.length) + w.val.length) _).mp hup
    rw [Tao.taoZModThreeProjection_natCast] at hlow
    exact hN ((ndThreeUnitResidue_iff_isUnit (by omega : 0 < 1) _).mp hlow)
  simp only [hz, if_false, Finset.sum_const_zero, mul_zero]

theorem rootCoreFilteredKernel_natCast_eq_zero_of_not_unit
    (b a K k : ℕ) (psi : List ℕ+ → ℝ)
    (g : ZMod (3 ^ k) → ℝ) (N : ℕ) (hN : ¬ IsUnit (N : ZMod (3 ^ 1))) :
    ndRootCoreFilteredKernel b a K k psi g
      (N : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))) = 0 := by
  unfold ndRootCoreFilteredKernel
  apply Finset.sum_eq_zero
  intro w _
  rw [rootCoreTransportWord_natCast_eq_zero_of_not_unit b a K k g w N hN, mul_zero]

private theorem rootCore_prefix_submass_sum (q : ℕ) (w : List ℕ+) (hw : w.length ≤ q) :
    (∑ y : ZMod (3 ^ q), Tao.taoGatedSubmass (Tao.geom2PNatListPMF q)
      (fun full => full.take w.length = w) (Tao.taoSection7OffsetZMod q) y) =
      (2 : ℝ) ^ (-(Tao.taoTupleWeight w : ℤ)) := by
  rw [sum_taoGatedSubmass_eq_sourceEventProbability]
  change ((Tao.geom2PNatListPMF q).toOuterMeasure
    ((fun full => full.take w.length) ⁻¹' {w})).toReal = _
  rw [geom2PNatListPMF_take_event_outerMeasure_toReal hw,
    (Tao.geom2PNatListPMF w.length).toOuterMeasure_apply_singleton]
  exact referencePrefix_atom_eq w

theorem rootCoreSelectedWords_atom_sum_eq_probability (b m K : ℕ) :
    (∑ w : ndRootCoreSelectedWords b m K,
      (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ))) =
      ndRootCoreStripBoundedCrossingProbability b m K := by
  classical
  let q := ndGeom2ShiftedWideSymmetricHorizon b
  let S := ndRootCoreSelectedWords b m K
  let E : List ℕ+ → Prop := fun full => ∃ w : S, full.take w.val.length = w.val
  have hdis (w v : S) (hne : w ≠ v) (full : List ℕ+)
      (hw : full.take w.val.length = w.val) (hv : full.take v.val.length = v.val) : False := by
    let w' : ndShiftedReferenceSelectedWords b (ndGeom2ShiftedWideSymmetricShiftRadius b) K :=
      ⟨w.val, (Finset.mem_filter.mp w.property).1⟩
    let v' : ndShiftedReferenceSelectedWords b (ndGeom2ShiftedWideSymmetricShiftRadius b) K :=
      ⟨v.val, (Finset.mem_filter.mp v.property).1⟩
    apply shiftedReferenceSelectedWords_prefix_disjoint b _ K w' v' _ full hw hv
    intro he
    have hv : w.val = v.val := congrArg (fun z => z.val) he
    exact hne (Subtype.ext hv)
  have hsel (y : ZMod (3 ^ q)) :
      Tao.taoGatedSubmass (Tao.geom2PNatListPMF q) E (Tao.taoSection7OffsetZMod q) y =
        ∑ w : S, Tao.taoGatedSubmass (Tao.geom2PNatListPMF q)
          (fun full => full.take w.val.length = w.val) (Tao.taoSection7OffsetZMod q) y := by
    simpa only [E, Finset.mem_univ, true_and] using
      Tao.taoGatedSubmass_finset_union_eq_sum (Tao.geom2PNatListPMF q)
        (Finset.univ : Finset S) (fun w full => full.take w.val.length = w.val)
        (Tao.taoSection7OffsetZMod q) (fun w _ v _ hne full hw hv => hdis w v hne full hw hv) y
  have h := Tao.taoGatedSubmass_sum_add_rejected_eq_one
    (Tao.geom2PNatListPMF q) E (Tao.taoSection7OffsetZMod q)
  simp_rw [hsel] at h
  rw [Finset.sum_comm] at h
  have hlen (w : S) : w.val.length ≤ q :=
    shiftedReferenceSelectedWords_length_le_horizon b _ K
      ⟨w.val, (Finset.mem_filter.mp w.property).1⟩
  simp_rw [rootCore_prefix_submass_sum q _ (hlen _)] at h
  rw [show Tao.taoGatedRejectedMass (Tao.geom2PNatListPMF q) E
      (Tao.taoSection7OffsetZMod q) = 1 - ndRootCoreStripBoundedCrossingProbability b m K from
    rootCore_rejectedMass_eq_one_sub_probability b m K q le_rfl] at h
  linarith only [h]

def ndRootCoreWordFilter (b m : ℕ) (w : List ℕ+) : ℝ :=
  if b ≤ w.length + m ∧ w.length ≤ b + m then 1 else 0

theorem rootCoreWordFilter_nonneg (b m : ℕ) (w : List ℕ+) : 0 ≤ ndRootCoreWordFilter b m w := by
  unfold ndRootCoreWordFilter
  split_ifs <;> norm_num

theorem rootCoreWordFilter_atom_sum_eq_probability (b m K : ℕ) :
    (∑ w : ndShiftedReferenceSelectedWords b (ndGeom2ShiftedWideSymmetricShiftRadius b) K,
      ndRootCoreWordFilter b m w.val * (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ))) =
        ndRootCoreStripBoundedCrossingProbability b m K := by
  classical
  rw [← rootCoreSelectedWords_atom_sum_eq_probability]
  rw [← Finset.sum_subtype
    (ndShiftedReferenceSelectedWords b (ndGeom2ShiftedWideSymmetricShiftRadius b) K)
    (fun _ => Iff.rfl) (fun w => ndRootCoreWordFilter b m w *
      (2 : ℝ) ^ (-(Tao.taoTupleWeight w : ℤ))),
    ← Finset.sum_subtype (ndRootCoreSelectedWords b m K) (fun _ => Iff.rfl)
      (fun w => (2 : ℝ) ^ (-(Tao.taoTupleWeight w : ℤ)))]
  simp only [ndRootCoreSelectedWords, Finset.sum_filter,
    ndRootCoreWordFilter, ite_mul, one_mul, zero_mul]

def ndRootCoreBackwardConductor (b k : ℕ) : ℕ → ℕ
  | 0 => k
  | n + 1 => ndGeom2ShiftedWideSymmetricHorizon b + ndRootCoreBackwardConductor (b + b / 100) k n

def ndRootCoreBackwardMark (b : ℕ) (cap width : ℕ → ℕ) (k : ℕ) :
    (n : ℕ) → ZMod (3 ^ ndRootCoreBackwardConductor b k n) → ℝ
  | 0 => ndSyracuseUnitReferenceDensity k
  | n + 1 => ndRootCoreFilteredKernel b (ndGeom2ShiftedWideSymmetricShiftRadius b) (cap 0)
      (ndRootCoreBackwardConductor (b + b / 100) k n) (ndRootCoreWordFilter b (width b))
      (ndRootCoreBackwardMark (b + b / 100) (ndGeom2RootSideCapTail cap) width k n)

def ndRootCoreProbabilityProduct (b : ℕ) (cap width : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ndRootCoreStripBoundedCrossingProbability b (width b) (cap 0) *
      ndRootCoreProbabilityProduct (b + b / 100) (ndGeom2RootSideCapTail cap) width n

theorem rootCoreBackwardMark_nonneg (b : ℕ) (cap width : ℕ → ℕ) (k n : ℕ)
    (y : ZMod (3 ^ ndRootCoreBackwardConductor b k n)) :
    0 ≤ ndRootCoreBackwardMark b cap width k n y := by
  induction n generalizing b cap with
  | zero => exact ndSyracuseUnitReferenceDensity_nonneg k y
  | succ n ih =>
      exact rootCoreFilteredKernel_nonneg _ _ _ _ _
        (rootCoreWordFilter_nonneg _ _) _ (fun z => ih _ _ z) y

theorem rootCoreBackwardMark_natCast_eq_zero_of_not_unit (b : ℕ) (cap width : ℕ → ℕ)
    {k : ℕ} (hk : 1 ≤ k) (n N : ℕ) (hN : ¬ IsUnit (N : ZMod (3 ^ 1))) :
    ndRootCoreBackwardMark b cap width k n (N : ZMod (3 ^ ndRootCoreBackwardConductor b k n)) = 0 := by
  cases n with
  | zero => exact unitReferenceDensity_natCast_eq_zero_of_not_unit hk N hN
  | succ n => exact rootCoreFilteredKernel_natCast_eq_zero_of_not_unit _ _ _ _ _ _ N hN

theorem rootCoreBackwardMark_fullMean_eq (b : ℕ) (cap width : ℕ → ℕ) (k n : ℕ) :
    ndTernaryUniformMean (ndRootCoreBackwardConductor b k n)
        (ndRootCoreBackwardMark b cap width k n) =
      (2 / 3 : ℝ) * ndRootCoreProbabilityProduct b cap width n := by
  induction n generalizing b cap with
  | zero => simpa only [ndRootCoreBackwardMark, ndRootCoreBackwardConductor,
      ndRootCoreProbabilityProduct, mul_one] using unitReferenceDensity_fullMean_eq k
  | succ n ih =>
      change ndTernaryUniformMean _ (ndRootCoreFilteredKernel _ _ _ _ _ _) = _
      rw [rootCoreFilteredKernel_fullMean_eq _ _ _ _ _ _ (rootCoreBackwardMark_nonneg _ _ _ _ _),
        rootCoreWordFilter_atom_sum_eq_probability, ih]
      simp only [ndRootCoreProbabilityProduct]
      ring

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

def forwardCoreMarkedMass (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n k : ℕ) (theta : U.state.Label → ℝ) : ℝ := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  exact ∑ z, if U.forwardCore cap width n z then
    (U.forwardIterate cap n).state.outerWeight z * theta (U.forwardAncestor cap n z) *
      ndSyracuseUnitReferenceDensity k ((U.forwardIterate cap n).state.root z : ZMod (3 ^ k)) else 0

theorem forwardCoreMarkedMass_eq_backwardMark
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n k : ℕ) (hk : 1 ≤ k) (theta : U.state.Label → ℝ) :
    U.forwardCoreMarkedMass cap width n k theta =
      letI := U.state.labelFintype;
      ∑ i, U.state.outerWeight i * theta i * ndRootCoreBackwardMark U.floor cap width k n
        (U.state.root i : ZMod (3 ^ ndRootCoreBackwardConductor U.floor k n)) := by
  classical
  induction n generalizing U cap with
  | zero =>
      simp only [forwardCoreMarkedMass, forwardCore, forwardIterate, forwardAncestor,
        if_true, ndRootCoreBackwardMark, ndRootCoreBackwardConductor]
      apply Finset.sum_congr
      · ext; simp
      · intro i _; rfl
  | succ n ih =>
      letI := U.state.labelFintype
      let V := U.next (cap 0)
      letI := V.state.labelFintype
      let theta' (z : V.state.Label) := theta (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) *
        ndRootCoreWordFilter U.floor (width U.floor)
          (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z)
      have hstep : U.forwardCoreMarkedMass cap width (n + 1) k theta =
          V.forwardCoreMarkedMass (ndGeom2RootSideCapTail cap) width n k theta' := by
        unfold forwardCoreMarkedMass
        apply Finset.sum_congr rfl
        intro z _
        simp only [forwardCore, forwardAncestor, forwardIterate,
          theta', ndRootCoreWordFilter, ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length,
          forwardFirstIncidence, V]
        split_ifs <;> simp_all
      rw [hstep, ih V (ndGeom2RootSideCapTail cap) theta']
      let q := ndRootCoreBackwardConductor V.floor k n
      let g := ndRootCoreBackwardMark V.floor (ndGeom2RootSideCapTail cap) width k n
      have h := sum_unitIncidence_word_mark_eq_filteredKernel
        U.state.rootSideUniformFloorAllLabels U.state.root (fun i => U.state.outerWeight i * theta i)
        U.floor (ndGeom2ShiftedWideSymmetricShiftRadius U.floor) (cap 0) q U.state.root_odd
        (by have h := U.floor_twoHundred; omega)
        (fun i => (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i))
        (ndRootCoreWordFilter U.floor (width U.floor)) g
        (rootCoreBackwardMark_natCast_eq_zero_of_not_unit V.floor (ndGeom2RootSideCapTail cap) width hk n)
      have heq : (∑ i : V.state.Label, V.state.outerWeight i * theta' i *
          g (V.state.root i : ZMod (3 ^ q))) =
          ∑ i : {i : U.state.Label // i ∈ U.state.rootSideUniformFloorAllLabels},
            U.state.outerWeight i.val * theta i.val *
              ndRootCoreFilteredKernel U.floor (ndGeom2ShiftedWideSymmetricShiftRadius U.floor) (cap 0) q
                (ndRootCoreWordFilter U.floor (width U.floor)) g
                (U.state.root i.val : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon U.floor + q))) := by
        rw [← h]
        apply Finset.sum_congr rfl
        intro z _
        dsimp only [V, next, NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNext,
          NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNextWeight,
          NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorUnitNextRoot,
          theta', ndGeom2PredictableRootSideUnitChildIncidenceWeight]
        ring
      change (∑ i : V.state.Label, V.state.outerWeight i * theta' i *
        g (V.state.root i : ZMod (3 ^ q))) = _
      rw [heq]
      change (∑ i : {i : U.state.Label // i ∈ (Finset.univ : Finset U.state.Label)}, _) = _
      exact (Finset.sum_subtype Finset.univ (fun _ => Iff.rfl) (fun i =>
        U.state.outerWeight i * theta i * ndRootCoreBackwardMark U.floor cap width k (n + 1)
          (U.state.root i : ZMod (3 ^ ndRootCoreBackwardConductor U.floor k (n + 1))))).symm

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

private theorem rootCore_floor_le_rootBase {b M : ℕ} (hM : Odd M) (hl : 16 ^ b ≤ M) :
    b ≤ ndA5QOneRootDyadicBase M := by
  have h := hl.trans_lt (rootDyadicBase_bounds hM.pos).2
  have h' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 16)).mp h
  omega

def ndRootCoreSingletonState (b M : ℕ) (hb : 200 ≤ b) (hM : Odd M) (hl : 16 ^ b ≤ M) :
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState where
  state := {
    Label := Unit
    labelFintype := inferInstance
    root := fun _ => M
    base := fun _ => ndA5QOneRootDyadicBase M
    outerWeight := fun _ => 1
    weight_nonneg := fun _ => by norm_num
    root_odd := fun _ => hM
    base_eq := fun _ => rfl
    base_twoHundred := fun _ => hb.trans (rootCore_floor_le_rootBase hM hl) }
  floor := b
  floor_twoHundred := hb
  floor_le_base := fun _ => rootCore_floor_le_rootBase hM hl

theorem rootCoreSingletonState_denominator_eq_one
    (b M : ℕ) (hb : 200 ≤ b) (hM : Odd M) (hl : 16 ^ b ≤ M) :
    (ndRootCoreSingletonState b M hb hM hl).denominator = 1 := by
  change ndGeom2PredictableOuterDenominator (Finset.univ : Finset Unit) (fun _ => (1 : ℝ)) = 1
  simp [ndGeom2PredictableOuterDenominator]

theorem rootCoreSingletonState_markedMass_eq_backwardMark
    (b M : ℕ) (hb : 200 ≤ b) (hM : Odd M) (hl : 16 ^ b ≤ M)
    (cap width : ℕ → ℕ) (n k : ℕ) (hk : 1 ≤ k) :
    (ndRootCoreSingletonState b M hb hM hl).forwardCoreMarkedMass cap width n k (fun _ => 1) =
      ndRootCoreBackwardMark b cap width k n (M : ZMod (3 ^ ndRootCoreBackwardConductor b k n)) := by
  rw [NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.forwardCoreMarkedMass_eq_backwardMark
    _ _ _ _ _ hk]
  change (∑ _i : Unit, (1 : ℝ) * 1 * ndRootCoreBackwardMark b cap width k n
    (M : ZMod (3 ^ ndRootCoreBackwardConductor b k n))) = _
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_unique,
    one_smul]

end

end Erdos1135Predecessor.ND.PositiveDensity
