/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.CommonZKCapLongTailFiberCentering
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideGeometricHistogramCapacity
import Erdos1135Predecessor.Tao.Fourier.Section7SChiActualQ
import Erdos1135Predecessor.Tao.Fourier.Section7SourceLaw
import Erdos1135Predecessor.Tao.Renewal.Outer736HoldExpectation
import Erdos1135Predecessor.Tao.Renewal.Prop78Pointwise737
import Erdos1135Predecessor.Tao.Section6.AdjacentOneStep
import Erdos1135Predecessor.Tao.Section6.Prop114Assembly

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

def ndSyracuseUnitReferenceDensity (q : ℕ) (x : ZMod (3 ^ q)) : ℝ :=
  (2 / 3 : ℝ) * ndSyracuseUniformDensity q x

theorem ndSyracuseUnitReferenceDensity_nonneg (q : ℕ) (x : ZMod (3 ^ q)) :
    0 ≤ ndSyracuseUnitReferenceDensity q x := by
  unfold ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity Tao.syracPMFMassVector
  positivity

theorem unitReferenceDensity_fullL1_eq_twoThirds_oscillation
    {m q : ℕ} (hmq : m ≤ q) :
    ndTernaryUniformMean q (fun x =>
      |ndSyracuseUnitReferenceDensity q x -
        ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmq x)|) =
      (2 / 3 : ℝ) * Tao.syracFineScaleOscillation m q := by
  rw [Tao.syracFineScaleOscillation_eq_sum_abs_sub_uniformLift hmq]
  have hq : (0 : ℝ) < ((3 ^ q : ℕ) : ℝ) := by positivity
  have hpoint (x : ZMod (3 ^ q)) :
      ndSyracuseUnitReferenceDensity q x -
          ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmq x) =
        ((2 / 3 : ℝ) * ((3 ^ q : ℕ) : ℝ)) *
          (Tao.syracPMFMassVector q x -
            Tao.taoZModPowUniformLift hmq (Tao.syracPMFMassVector m) x) := by
    unfold ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity
      Tao.taoZModPowUniformLift Tao.zmodPowFiberAverageScale
    field_simp
  unfold ndTernaryUniformMean ndTernaryUniformScale
  simp_rw [hpoint, abs_mul, abs_of_nonneg hq.le]
  norm_num only [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  rw [← Finset.mul_sum]
  field_simp

def ndReferencePrefixParent (d t : ℕ) (word : List ℕ+)
    (z : ZMod (3 ^ t)) : ZMod (3 ^ (t + d)) :=
  ndCommonZAmbientTailFiberPoint d t (Tao.taoTupleWeight word)
    (Tao.taoSection7OffsetPrefix (t + d) d word) z

theorem ndReferencePrefixParent_injective (d t : ℕ) (word : List ℕ+) :
    Function.Injective (ndReferencePrefixParent d t word) :=
  ndCommonZAmbientTailFiberPoint_injective d t (Tao.taoTupleWeight word) _

theorem ndReferencePrefixParent_offset_append
    (d t : ℕ) (word tail : List ℕ+) (hlen : word.length = d) :
    Tao.taoSection7OffsetZMod (t + d) (word ++ tail) =
      ndReferencePrefixParent d t word (Tao.taoSection7OffsetZMod t tail) := by
  exact Tao.taoSection6OffsetZMod_append_eq_head_add_ambientTail
    d t (Tao.taoTupleWeight word) word tail hlen rfl

private def referenceFinitePush {α β : Type*} [Fintype α]
    (f : α → β) (g : α → ℝ) (y : β) : ℝ := by
  classical
  exact ∑ z, if f z = y then g z else 0

private theorem referenceFinitePush_apply {α β : Type*} [Fintype α]
    (f : α → β) (hf : Function.Injective f) (g : α → ℝ) (z : α) :
    referenceFinitePush f g (f z) = g z := by
  classical
  simp [referenceFinitePush, hf.eq_iff]

private theorem referenceFinitePush_abs {α β : Type*} [Fintype α]
    (f : α → β) (hf : Function.Injective f) (g : α → ℝ) (y : β) :
    |referenceFinitePush f g y| = referenceFinitePush f (fun z => |g z|) y := by
  classical
  by_cases h : ∃ z, f z = y
  · obtain ⟨z, rfl⟩ := h
    rw [referenceFinitePush_apply f hf, referenceFinitePush_apply f hf]
  · have hn : ∀ z, f z ≠ y := by simpa using h
    simp [referenceFinitePush, hn]

private theorem referenceFinitePush_sum {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (g : α → ℝ) :
    (∑ y, referenceFinitePush f g y) = ∑ z, g z := by
  classical
  unfold referenceFinitePush
  rw [Finset.sum_comm]
  simp

private theorem referenceFinitePush_sub {α β : Type*} [Fintype α]
    (f : α → β) (g h : α → ℝ) (y : β) :
    referenceFinitePush f (fun z => g z - h z) y =
      referenceFinitePush f g y - referenceFinitePush f h y := by
  classical
  unfold referenceFinitePush
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> ring

private theorem referenceFinitePush_mul {α β : Type*} [Fintype α]
    (f : α → β) (g : α → ℝ) (c : ℝ) (y : β) :
    referenceFinitePush f (fun z => c * g z) y =
      c * referenceFinitePush f g y := by
  classical
  unfold referenceFinitePush
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> ring

def ndReferenceWordTransport (d t : ℕ) (word : List ℕ+)
    (g : ZMod (3 ^ t) → ℝ) (y : ZMod (3 ^ (t + d))) : ℝ :=
  (3 : ℝ) ^ d * (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) *
    referenceFinitePush (ndReferencePrefixParent d t word) g y

theorem referenceWordTransport_eq_sum
    (d t : ℕ) (word : List ℕ+) (g : ZMod (3 ^ t) → ℝ)
    (y : ZMod (3 ^ (t + d))) :
    ndReferenceWordTransport d t word g y =
      (3 : ℝ) ^ d * (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) *
        ∑ z, if ndReferencePrefixParent d t word z = y then g z else 0 := by
  classical
  simp only [ndReferenceWordTransport, referenceFinitePush]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

theorem referenceWordTransport_fullL1_eq
    (d t : ℕ) (word : List ℕ+) (g : ZMod (3 ^ t) → ℝ) :
    ndTernaryUniformMean (t + d) (fun y => |ndReferenceWordTransport d t word g y|) =
      (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) *
        ndTernaryUniformMean t (fun z => |g z|) := by
  unfold ndTernaryUniformMean ndTernaryUniformScale ndReferenceWordTransport
  simp_rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (3 : ℝ) ^ d by positivity),
    abs_of_nonneg (show (0 : ℝ) ≤ (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) by positivity),
    referenceFinitePush_abs _ (ndReferencePrefixParent_injective d t word)]
  rw [← Finset.mul_sum, referenceFinitePush_sum]
  push_cast
  rw [pow_add]
  field_simp

theorem referenceWordTransport_sub
    (d t : ℕ) (word : List ℕ+) (g h : ZMod (3 ^ t) → ℝ)
    (y : ZMod (3 ^ (t + d))) :
    ndReferenceWordTransport d t word (fun z => g z - h z) y =
      ndReferenceWordTransport d t word g y - ndReferenceWordTransport d t word h y := by
  unfold ndReferenceWordTransport
  rw [referenceFinitePush_sub, mul_sub]

theorem referencePrefix_gatedOptionPMF_apply
    (d t : ℕ) (word : List ℕ+) (hlen : word.length = d)
    (y : ZMod (3 ^ (t + d))) :
    Tao.taoGatedOptionPMF (Tao.geom2PNatListPMF (t + d))
        (fun full => full.take d = word)
        (Tao.taoSection7OffsetZMod (t + d)) (some y) =
      Tao.geom2PNatListPMF d word *
        ((Tao.syracPMF t).map (ndReferencePrefixParent d t word)) y := by
  classical
  let key : List ℕ+ × List ℕ+ → Option (ZMod (3 ^ (t + d))) :=
    fun pair => if pair.1 = word then
      some (ndReferencePrefixParent d t word (Tao.taoSection7OffsetZMod t pair.2))
    else none
  have hkey (full : List ℕ+) :
      Tao.taoGatedOptionKey (fun full => full.take d = word)
          (Tao.taoSection7OffsetZMod (t + d)) full =
        key (full.take d, full.drop d) := by
    unfold Tao.taoGatedOptionKey
    dsimp only [key]
    split_ifs with h
    · congr 1
      calc
        Tao.taoSection7OffsetZMod (t + d) full =
            Tao.taoSection7OffsetZMod (t + d) (word ++ full.drop d) := by
          rw [← h, List.take_append_drop]
        _ = _ := ndReferencePrefixParent_offset_append d t word _ hlen
    · rfl
  have hmap :
      Tao.taoGatedOptionPMF (Tao.geom2PNatListPMF (t + d))
          (fun full => full.take d = word) (Tao.taoSection7OffsetZMod (t + d)) =
        ((Tao.geom2PNatListPMF d).bind fun head =>
          (Tao.geom2PNatListPMF t).map fun tail => (head, tail)).map key := by
    unfold Tao.taoGatedOptionPMF
    have hk : Tao.taoGatedOptionKey (fun full => full.take d = word)
        (Tao.taoSection7OffsetZMod (t + d)) =
        key ∘ (fun full => (full.take d, full.drop d)) := funext hkey
    rw [hk, ← PMF.map_comp]
    have hs := Tao.geom2PNatListPMF_map_take_drop_eq d t
    rw [Nat.add_comm d t] at hs
    rw [hs]
  rw [hmap, PMF.map_bind, PMF.bind_apply, tsum_eq_single word]
  · congr 1
    rw [PMF.map_comp]
    have hk : key ∘ (fun tail => (word, tail)) =
        (fun z => some (ndReferencePrefixParent d t word z)) ∘
          Tao.taoSection7OffsetZMod t := by
      funext tail
      simp [key]
    rw [hk, ← PMF.map_comp,
      ← Tao.syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod]
    have hk' : (fun z => some (ndReferencePrefixParent d t word z)) =
        some ∘ ndReferencePrefixParent d t word := rfl
    rw [hk', ← PMF.map_comp, PMF.map_apply]
    simp
  · intro head hne
    rw [PMF.map_comp]
    have hk : key ∘ (fun tail => (head, tail)) = fun _ => none := by
      funext tail
      simp [key, hne]
    rw [hk]
    simp [PMF.map_apply]

theorem referencePrefix_gatedSubmass_eq
    (d t : ℕ) (word : List ℕ+) (hlen : word.length = d)
    (y : ZMod (3 ^ (t + d))) :
    Tao.taoGatedSubmass (Tao.geom2PNatListPMF (t + d))
        (fun full => full.take d = word) (Tao.taoSection7OffsetZMod (t + d)) y =
      (Tao.geom2PNatListPMF d word).toReal *
        referenceFinitePush (ndReferencePrefixParent d t word)
          (Tao.syracPMFMassVector t) y := by
  classical
  unfold Tao.taoGatedSubmass
  rw [referencePrefix_gatedOptionPMF_apply d t word hlen, ENNReal.toReal_mul,
    PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · congr 1
    unfold referenceFinitePush Tao.syracPMFMassVector
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : ndReferencePrefixParent d t word z = y
    · simp [h]
    · simp [h, Ne.symm h]
  · intro z _
    split_ifs
    · exact (Tao.syracPMF t).apply_ne_top z
    · exact ENNReal.zero_ne_top

theorem referencePrefix_atom_eq (word : List ℕ+) :
    (Tao.geom2PNatListPMF word.length word).toReal =
      (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) := by
  rw [Tao.geom2PNatListPMF_apply_length_toReal_eq_weight]
  simp [zpow_neg, zpow_natCast, one_div, inv_pow]

theorem referenceWordTransport_density_eq_prefixDensity
    (d t : ℕ) (word : List ℕ+) (hlen : word.length = d)
    (y : ZMod (3 ^ (t + d))) :
    ndReferenceWordTransport d t word (ndSyracuseUnitReferenceDensity t) y =
      ((2 / 3 : ℝ) * ((3 ^ (t + d) : ℕ) : ℝ)) *
        Tao.taoGatedSubmass (Tao.geom2PNatListPMF (t + d))
          (fun full => full.take d = word) (Tao.taoSection7OffsetZMod (t + d)) y := by
  rw [referencePrefix_gatedSubmass_eq d t word hlen]
  have hp : (Tao.geom2PNatListPMF d word).toReal =
      (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) := by
    simpa only [hlen] using referencePrefix_atom_eq word
  rw [hp]
  unfold ndReferenceWordTransport ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity
  simp_rw [← mul_assoc]
  rw [referenceFinitePush_mul]
  push_cast
  rw [show (3 : ℝ) ^ (t + d) = (3 : ℝ) ^ t * (3 : ℝ) ^ d from pow_add 3 t d]
  ring

private def referenceTransportCast (q d t : ℕ) (hq : t + d = q)
    (word : List ℕ+) (g : ZMod (3 ^ t) → ℝ) : ZMod (3 ^ q) → ℝ :=
  hq ▸ ndReferenceWordTransport d t word g

private theorem referenceTransportCast_fullL1_eq
    (q d t : ℕ) (hq : t + d = q) (word : List ℕ+) (g : ZMod (3 ^ t) → ℝ) :
    ndTernaryUniformMean q (fun y => |referenceTransportCast q d t hq word g y|) =
      (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) *
        ndTernaryUniformMean t (fun z => |g z|) := by
  subst q
  exact referenceWordTransport_fullL1_eq d t word g

private theorem referenceTransportCast_sub
    (q d t : ℕ) (hq : t + d = q) (word : List ℕ+)
    (g h : ZMod (3 ^ t) → ℝ) (y : ZMod (3 ^ q)) :
    referenceTransportCast q d t hq word (fun z => g z - h z) y =
      referenceTransportCast q d t hq word g y - referenceTransportCast q d t hq word h y := by
  subst q
  exact referenceWordTransport_sub d t word g h y

private theorem referenceTransportCast_density_eq
    (q d t : ℕ) (hq : t + d = q) (word : List ℕ+) (hlen : word.length = d)
    (y : ZMod (3 ^ q)) :
    referenceTransportCast q d t hq word (ndSyracuseUnitReferenceDensity t) y =
      ((2 / 3 : ℝ) * ((3 ^ q : ℕ) : ℝ)) *
        Tao.taoGatedSubmass (Tao.geom2PNatListPMF q)
          (fun full => full.take d = word) (Tao.taoSection7OffsetZMod q) y := by
  subst q
  exact referenceWordTransport_density_eq_prefixDensity d t word hlen y

def ndReferencePrefixTransportAt (q : ℕ) (word : List ℕ+)
    (hlen : word.length ≤ q) (g : ZMod (3 ^ (q - word.length)) → ℝ) :
    ZMod (3 ^ q) → ℝ :=
  referenceTransportCast q word.length (q - word.length) (Nat.sub_add_cancel hlen) word g

theorem referencePrefixTransportAt_apply_natCast
    (q : ℕ) (word : List ℕ+) (hlen : word.length ≤ q)
    (g : ZMod (3 ^ (q - word.length)) → ℝ) (M : ℕ) :
    ndReferencePrefixTransportAt q word hlen g (M : ZMod (3 ^ q)) =
      ndReferenceWordTransport word.length (q - word.length) word g
        (M : ZMod (3 ^ ((q - word.length) + word.length))) := by
  have hcast (d t q : ℕ) (hq : t + d = q)
      (w : List ℕ+) (f : ZMod (3 ^ t) → ℝ) :
      referenceTransportCast q d t hq w f (M : ZMod (3 ^ q)) =
        ndReferenceWordTransport d t w f (M : ZMod (3 ^ (t + d))) := by
    subst q
    rfl
  exact hcast _ _ _ _ _ _

theorem referencePrefixTransportAt_fullL1_eq
    (q : ℕ) (word : List ℕ+) (hlen : word.length ≤ q)
    (g : ZMod (3 ^ (q - word.length)) → ℝ) :
    ndTernaryUniformMean q (fun y => |ndReferencePrefixTransportAt q word hlen g y|) =
      (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) *
        ndTernaryUniformMean (q - word.length) (fun z => |g z|) := by
  exact referenceTransportCast_fullL1_eq q word.length (q - word.length)
    (Nat.sub_add_cancel hlen) word g

theorem referencePrefixTransportAt_sub
    (q : ℕ) (word : List ℕ+) (hlen : word.length ≤ q)
    (g h : ZMod (3 ^ (q - word.length)) → ℝ) (y : ZMod (3 ^ q)) :
    ndReferencePrefixTransportAt q word hlen (fun z => g z - h z) y =
      ndReferencePrefixTransportAt q word hlen g y -
        ndReferencePrefixTransportAt q word hlen h y := by
  exact referenceTransportCast_sub q word.length (q - word.length)
    (Nat.sub_add_cancel hlen) word g h y

theorem referencePrefixTransportAt_density_eq
    (q : ℕ) (word : List ℕ+) (hlen : word.length ≤ q) (y : ZMod (3 ^ q)) :
    ndReferencePrefixTransportAt q word hlen
        (ndSyracuseUnitReferenceDensity (q - word.length)) y =
      ((2 / 3 : ℝ) * ((3 ^ q : ℕ) : ℝ)) *
        Tao.taoGatedSubmass (Tao.geom2PNatListPMF q)
          (fun full => full.take word.length = word) (Tao.taoSection7OffsetZMod q) y := by
  exact referenceTransportCast_density_eq q word.length (q - word.length)
    (Nat.sub_add_cancel hlen) word rfl y

theorem referencePrefixFamily_density_eq_selected
    {ι : Type*} [Fintype ι] (q : ℕ) (word : ι → List ℕ+)
    (hlen : ∀ i, (word i).length ≤ q)
    (hdisjoint : ∀ i j, i ≠ j → ∀ full : List ℕ+,
      full.take (word i).length = word i → full.take (word j).length = word j → False)
    (y : ZMod (3 ^ q)) :
    (∑ i, ndReferencePrefixTransportAt q (word i) (hlen i)
        (ndSyracuseUnitReferenceDensity (q - (word i).length)) y) =
      ((2 / 3 : ℝ) * ((3 ^ q : ℕ) : ℝ)) *
        Tao.taoGatedSubmass (Tao.geom2PNatListPMF q)
          (fun full => ∃ i, full.take (word i).length = word i)
          (Tao.taoSection7OffsetZMod q) y := by
  classical
  simp_rw [referencePrefixTransportAt_density_eq]
  rw [← Finset.mul_sum]
  congr 1
  symm
  simpa only [Finset.mem_univ, true_and] using
    Tao.taoGatedSubmass_finset_union_eq_sum (Tao.geom2PNatListPMF q)
      (Finset.univ : Finset ι)
      (fun i full => full.take (word i).length = word i)
      (Tao.taoSection7OffsetZMod q)
      (fun i _ j _ hij full hi hj => hdisjoint i j hij full hi hj) y

private theorem referenceUniform_abs_sub_triangle (q : ℕ)
    (f g h : ZMod (3 ^ q) → ℝ) :
    ndTernaryUniformMean q (fun y => |f y - h y|) ≤
      ndTernaryUniformMean q (fun y => |f y - g y|) +
        ndTernaryUniformMean q (fun y => |g y - h y|) := by
  unfold ndTernaryUniformMean
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by unfold ndTernaryUniformScale; positivity)
  exact Finset.sum_le_sum fun y _ => abs_sub_le (f y) (g y) (h y)

private theorem referenceUniform_abs_sum_le {ι : Type*} [Fintype ι]
    (q : ℕ) (f : ι → ZMod (3 ^ q) → ℝ) :
    ndTernaryUniformMean q (fun y => |∑ i, f i y|) ≤
      ∑ i, ndTernaryUniformMean q (fun y => |f i y|) := by
  unfold ndTernaryUniformMean
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply mul_le_mul_of_nonneg_left _ (by unfold ndTernaryUniformScale; positivity)
  exact Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _

theorem unitReferenceDensity_fullMean_eq (q : ℕ) :
    ndTernaryUniformMean q (ndSyracuseUnitReferenceDensity q) = 2 / 3 := by
  unfold ndTernaryUniformMean ndTernaryUniformScale ndSyracuseUnitReferenceDensity
    ndSyracuseUniformDensity Tao.syracPMFMassVector
  rw [← Finset.mul_sum, ← Finset.mul_sum, Tao.pmf_sum_toReal]
  field_simp

private theorem referencePrefix_sum_submass_eq_atom
    (q : ℕ) (word : List ℕ+) (hlen : word.length ≤ q) :
    (∑ y : ZMod (3 ^ q), Tao.taoGatedSubmass (Tao.geom2PNatListPMF q)
      (fun full => full.take word.length = word) (Tao.taoSection7OffsetZMod q) y) =
      (2 : ℝ) ^ (-(Tao.taoTupleWeight word : ℤ)) := by
  have h := referencePrefixTransportAt_fullL1_eq q word hlen
    (ndSyracuseUnitReferenceDensity (q - word.length))
  simp_rw [referencePrefixTransportAt_density_eq,
    abs_of_nonneg (mul_nonneg
      (show (0 : ℝ) ≤ (2 / 3 : ℝ) * ((3 ^ q : ℕ) : ℝ) by positivity)
      (Tao.taoGatedSubmass_nonneg _ _ _ _))] at h
  have ht : ndTernaryUniformMean (q - word.length)
      (fun z => |ndSyracuseUnitReferenceDensity (q - word.length) z|) = 2 / 3 := by
    simp_rw [abs_of_nonneg (ndSyracuseUnitReferenceDensity_nonneg _ _)]
    exact unitReferenceDensity_fullMean_eq _
  rw [ht] at h
  unfold ndTernaryUniformMean ndTernaryUniformScale at h
  rw [← Finset.mul_sum] at h
  have hq : ((3 ^ q : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp at h
  nlinarith

theorem referencePrefixFamily_atom_sum_le_one
    {ι : Type*} [Fintype ι] (q : ℕ) (word : ι → List ℕ+)
    (hlen : ∀ i, (word i).length ≤ q)
    (hdisjoint : ∀ i j, i ≠ j → ∀ full : List ℕ+,
      full.take (word i).length = word i → full.take (word j).length = word j → False) :
    (∑ i, (2 : ℝ) ^ (-(Tao.taoTupleWeight (word i) : ℤ))) ≤ 1 := by
  classical
  let E : List ℕ+ → Prop := fun full => ∃ i, full.take (word i).length = word i
  have hsel (y : ZMod (3 ^ q)) :
      Tao.taoGatedSubmass (Tao.geom2PNatListPMF q) E (Tao.taoSection7OffsetZMod q) y =
        ∑ i, Tao.taoGatedSubmass (Tao.geom2PNatListPMF q)
          (fun full => full.take (word i).length = word i) (Tao.taoSection7OffsetZMod q) y := by
    simpa only [E, Finset.mem_univ, true_and] using
      Tao.taoGatedSubmass_finset_union_eq_sum (Tao.geom2PNatListPMF q)
        (Finset.univ : Finset ι) (fun i full => full.take (word i).length = word i)
        (Tao.taoSection7OffsetZMod q)
        (fun i _ j _ hij full hi hj => hdisjoint i j hij full hi hj) y
  have h := Tao.taoGatedSubmass_sum_le_one (Tao.geom2PNatListPMF q) E
    (Tao.taoSection7OffsetZMod q)
  simp_rw [hsel] at h
  rw [Finset.sum_comm] at h
  simpa only [referencePrefix_sum_submass_eq_atom q _ (hlen _)] using h

theorem referenceDensity_selected_defect_fullL1_eq
    (q : ℕ) (E : List ℕ+ → Prop) :
    ndTernaryUniformMean q (fun y =>
      |((2 / 3 : ℝ) * ((3 ^ q : ℕ) : ℝ)) *
          Tao.taoGatedSubmass (Tao.geom2PNatListPMF q) E (Tao.taoSection7OffsetZMod q) y -
        ndSyracuseUnitReferenceDensity q y|) =
      (2 / 3 : ℝ) * Tao.taoGatedRejectedMass (Tao.geom2PNatListPMF q)
        E (Tao.taoSection7OffsetZMod q) := by
  let p := Tao.geom2PNatListPMF q
  let f := Tao.taoSection7OffsetZMod q
  let A : ℝ := (2 / 3 : ℝ) * ((3 ^ q : ℕ) : ℝ)
  have hpoint (y : ZMod (3 ^ q)) :
      A * Tao.taoGatedSubmass p E f y - ndSyracuseUnitReferenceDensity q y =
        -(A * Tao.taoGatedSubmass p (fun full => ¬E full) f y) := by
    have hs := Tao.taoGatedSubmass_map_apply_split p E f y
    have hm : ((p.map f) y).toReal = Tao.syracPMFMassVector q y := by
      rw [← Tao.syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod]
      rfl
    rw [hm] at hs
    unfold ndSyracuseUnitReferenceDensity ndSyracuseUniformDensity
    dsimp only [A]
    rw [hs]
    ring
  change ndTernaryUniformMean q (fun y =>
    |A * Tao.taoGatedSubmass p E f y - ndSyracuseUnitReferenceDensity q y|) = _
  simp_rw [hpoint, abs_neg,
    abs_of_nonneg (mul_nonneg (show 0 ≤ A by dsimp [A]; positivity)
      (Tao.taoGatedSubmass_nonneg _ _ _ _))]
  unfold ndTernaryUniformMean ndTernaryUniformScale
  rw [← Finset.mul_sum, Tao.taoGatedSubmass_complement_sum_eq_rejectedMass]
  dsimp only [A, p, f]
  field_simp

theorem referencePrefixFamily_lowerTail_fullL1_le
    {ι : Type*} [Fintype ι] (q k ell : ℕ) (word : ι → List ℕ+)
    (hlen : ∀ i, (word i).length ≤ q)
    (hk : ∀ i, k ≤ q - (word i).length) (hell : ell ≤ q)
    (hdisjoint : ∀ i j, i ≠ j → ∀ full : List ℕ+,
      full.take (word i).length = word i → full.take (word j).length = word j → False)
    (eta epsilon : ℝ) (heta : 0 ≤ eta)
    (hmix : ∀ i, Tao.syracFineScaleOscillation k (q - (word i).length) ≤ eta)
    (hellmix : Tao.syracFineScaleOscillation ell q ≤ epsilon) :
    ndTernaryUniformMean q (fun y =>
      |(∑ i, ndReferencePrefixTransportAt q (word i) (hlen i)
          (fun z => ndSyracuseUnitReferenceDensity k
            (Tao.taoZModThreeProjection (hk i) z)) y) -
        ndSyracuseUnitReferenceDensity ell (Tao.taoZModThreeProjection hell y)|) ≤
      (2 / 3 : ℝ) * (eta + epsilon +
        Tao.taoGatedRejectedMass (Tao.geom2PNatListPMF q)
          (fun full => ∃ i, full.take (word i).length = word i)
          (Tao.taoSection7OffsetZMod q)) := by
  classical
  let low (i : ι) := ndReferencePrefixTransportAt q (word i) (hlen i)
    (fun z => ndSyracuseUnitReferenceDensity k (Tao.taoZModThreeProjection (hk i) z))
  let full (i : ι) := ndReferencePrefixTransportAt q (word i) (hlen i)
    (ndSyracuseUnitReferenceDensity (q - (word i).length))
  let atom (i : ι) := (2 : ℝ) ^ (-(Tao.taoTupleWeight (word i) : ℤ))
  let E : List ℕ+ → Prop := fun w => ∃ i, w.take (word i).length = word i
  let bad := Tao.taoGatedRejectedMass (Tao.geom2PNatListPMF q) E (Tao.taoSection7OffsetZMod q)
  have hedge (i : ι) :
      ndTernaryUniformMean q (fun y => |low i y - full i y|) ≤ atom i * ((2 / 3 : ℝ) * eta) := by
    simp only [low, full]
    simp_rw [abs_sub_comm, ← referencePrefixTransportAt_sub]
    rw [referencePrefixTransportAt_fullL1_eq,
      unitReferenceDensity_fullL1_eq_twoThirds_oscillation (hk i)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left (hmix i) (by norm_num)
  have hsum : (∑ i, atom i) ≤ 1 := referencePrefixFamily_atom_sum_le_one q word hlen hdisjoint
  have hreplace :
      ndTernaryUniformMean q (fun y => |(∑ i, low i y) - ∑ i, full i y|) ≤
        (2 / 3 : ℝ) * eta := by
    simp_rw [← Finset.sum_sub_distrib]
    calc
      ndTernaryUniformMean q (fun y => |∑ i, (low i y - full i y)|) ≤
          ∑ i, ndTernaryUniformMean q (fun y => |low i y - full i y|) :=
        referenceUniform_abs_sum_le q _
      _ ≤ ∑ i, atom i * ((2 / 3 : ℝ) * eta) := Finset.sum_le_sum fun i _ => hedge i
      _ = (∑ i, atom i) * ((2 / 3 : ℝ) * eta) := by rw [Finset.sum_mul]
      _ ≤ 1 * ((2 / 3 : ℝ) * eta) :=
        mul_le_mul_of_nonneg_right hsum (mul_nonneg (by norm_num) heta)
      _ = _ := one_mul _
  have hreject :
      ndTernaryUniformMean q (fun y => |(∑ i, full i y) - ndSyracuseUnitReferenceDensity q y|) =
        (2 / 3 : ℝ) * bad := by
    simp only [full, referencePrefixFamily_density_eq_selected q word hlen hdisjoint]
    exact referenceDensity_selected_defect_fullL1_eq q E
  have hterminal :
      ndTernaryUniformMean q (fun y => |ndSyracuseUnitReferenceDensity q y -
        ndSyracuseUnitReferenceDensity ell (Tao.taoZModThreeProjection hell y)|) ≤
      (2 / 3 : ℝ) * epsilon := by
    rw [unitReferenceDensity_fullL1_eq_twoThirds_oscillation hell]
    exact mul_le_mul_of_nonneg_left hellmix (by norm_num)
  have h1 := referenceUniform_abs_sub_triangle q
    (fun y => ∑ i, low i y) (fun y => ∑ i, full i y)
    (fun y => ndSyracuseUnitReferenceDensity ell (Tao.taoZModThreeProjection hell y))
  have h2 := referenceUniform_abs_sub_triangle q
    (fun y => ∑ i, full i y) (ndSyracuseUnitReferenceDensity q)
    (fun y => ndSyracuseUnitReferenceDensity ell (Tao.taoZModThreeProjection hell y))
  rw [hreject] at h2
  change ndTernaryUniformMean q (fun y => |(∑ i, low i y) -
    ndSyracuseUnitReferenceDensity ell (Tao.taoZModThreeProjection hell y)|) ≤ _
  change _ ≤ (2 / 3 : ℝ) * (eta + epsilon + bad)
  linarith

def ndShiftedReferenceSelectedWords (b a K : ℕ) : Finset (List ℕ+) := by
  classical
  exact (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b).biUnion fun s =>
    (Finset.univ : Finset (ZMod (3 ^ s))).biUnion fun x =>
      ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset b a s K x

theorem mem_shiftedReferenceSelectedWords_iff (b a K : ℕ) (word : List ℕ+) :
    word ∈ ndShiftedReferenceSelectedWords b a K ↔
      ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt b a word.length K word := by
  classical
  simp only [ndShiftedReferenceSelectedWords, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff]
  constructor
  · rintro ⟨s, _, x, hlen, hevent, _⟩
    simpa only [hlen] using hevent
  · intro h
    exact ⟨word.length, h.1.1, Tao.taoSection7OffsetZMod word.length word, rfl, h, rfl⟩

theorem shiftedReferenceSelectedWords_length_le_horizon
    (b a K : ℕ) (i : ndShiftedReferenceSelectedWords b a K) :
    i.val.length ≤ ndGeom2ShiftedWideSymmetricHorizon b := by
  have h := (mem_shiftedReferenceSelectedWords_iff b a K i.val).mp i.property
  exact (Finset.mem_Icc.mp h.1.1).2

theorem shiftedReferenceSelectedWords_prefix_disjoint (b a K : ℕ)
    (i j : ndShiftedReferenceSelectedWords b a K) (hij : i ≠ j)
    (full : List ℕ+) (hi : full.take i.val.length = i.val)
    (hj : full.take j.val.length = j.val) : False := by
  have hi0 := ((mem_shiftedReferenceSelectedWords_iff b a K i.val).mp i.property).1
  have hj0 := ((mem_shiftedReferenceSelectedWords_iff b a K j.val).mp j.property).1
  have hi1 := (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff b a i.val.length full).mp
    (by simpa only [hi] using hi0)
  have hj1 := (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff b a j.val.length full).mp
    (by simpa only [hj] using hj0)
  have heq : i.val.length = j.val.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hj1.2.2 _ hi1.1 hlt hi1.2.1
    · exact hi1.2.2 _ hj1.1 hgt hj1.2.1
  apply hij
  apply Subtype.ext
  rw [heq] at hi
  exact hi.symm.trans hj

def ndShiftedReferenceMarkedKernel (b a K k : ℕ) :
    ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k)) → ℝ :=
  fun y => ∑ i : ndShiftedReferenceSelectedWords b a K,
    ndReferencePrefixTransportAt (ndGeom2ShiftedWideSymmetricHorizon b + k) i.val
      (by have h := shiftedReferenceSelectedWords_length_le_horizon b a K i; omega)
      (fun z => ndSyracuseUnitReferenceDensity k
        (Tao.taoZModThreeProjection
          (by have h := shiftedReferenceSelectedWords_length_le_horizon b a K i; omega) z)) y

theorem shiftedReference_quarter_next_conductor_le_two_mul (b : ℕ) :
    ndGeom2ShiftedWideSymmetricHorizon b + (b + b / 100) / 4 ≤ 2 * b := by
  unfold ndGeom2ShiftedWideSymmetricHorizon ndGeom2ShiftedWideSymmetricWidth
  omega

theorem shiftedReference_rejectedMass_eq_one_sub_probability
    (b a K q : ℕ) (hq : ndGeom2ShiftedWideSymmetricHorizon b ≤ q) :
    Tao.taoGatedRejectedMass (Tao.geom2PNatListPMF q)
        (fun full => ∃ i : ndShiftedReferenceSelectedWords b a K,
          full.take i.val.length = i.val) (Tao.taoSection7OffsetZMod q) =
      1 - ndGeom2ShiftedWideSymmetricBoundedOvershootCrossingProbability b a K := by
  classical
  let p := Tao.geom2PNatListPMF q
  let I := ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b
  let E : List ℕ+ → Prop := fun full => ∃ i : ndShiftedReferenceSelectedWords b a K,
    full.take i.val.length = i.val
  let G : ℕ → List ℕ+ → Prop := fun s full =>
    (full.take s).length = s ∧
      ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt b a s K (full.take s)
  have hgate : {full | E full} = ⋃ s ∈ I, {full | G s full} := by
    ext full
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      have he := (mem_shiftedReferenceSelectedWords_iff b a K i.val).mp i.property
      refine ⟨i.val.length, he.1.1, ?_⟩
      dsimp only [G]
      rw [hi]
      exact ⟨rfl, he⟩
    · rintro ⟨s, _, hl, he⟩
      have hw : full.take s ∈ ndShiftedReferenceSelectedWords b a K := by
        rw [mem_shiftedReferenceSelectedWords_iff, hl]
        exact he
      exact ⟨⟨full.take s, hw⟩, by simp only [hl]⟩
  have hdis : Set.PairwiseDisjoint (I : Set ℕ) (fun s => {full | G s full}) := by
    intro s _ t _ hne
    change Disjoint {full | G s full} {full | G t full}
    rw [Set.disjoint_left]
    intro full hs ht
    have hs' := (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff b a s full).mp hs.2.1
    have ht' := (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff b a t full).mp ht.2.1
    rcases lt_or_gt_of_ne hne with hst | hts
    · exact ht'.2.2 _ hs'.1 hst hs'.2.1
    · exact hs'.2.2 _ ht'.1 hts ht'.2.1
  have hfinite (s : ℕ) : p.toOuterMeasure {full | G s full} ≠ ⊤ := by
    apply ne_of_lt
    calc
      p.toOuterMeasure {full | G s full} ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 := (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  have hmass (s : ℕ) (hs : s ∈ I) :
      (p.toOuterMeasure {full | G s full}).toReal =
        ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass b a s K := by
    have hsq : s ≤ q := (Finset.mem_Icc.mp hs).2.trans hq
    let J : Set (List ℕ+) := {word | word.length = s ∧
      ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt b a s K word}
    change (p.toOuterMeasure ((fun full => full.take s) ⁻¹' J)).toReal = _
    rw [geom2PNatListPMF_take_event_outerMeasure_toReal hsq J]
    unfold ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass
    congr 1
    apply (Tao.geom2PNatListPMF s).toOuterMeasure_apply_eq_of_inter_support_eq
    ext word
    constructor
    · rintro ⟨⟨_, he⟩, hp⟩
      exact ⟨he, hp⟩
    · rintro ⟨he, hp⟩
      exact ⟨⟨Tao.geom2PNatListPMF_support_length_eq hp, he⟩, hp⟩
  have hprob : (p.toOuterMeasure {full | E full}).toReal =
      ndGeom2ShiftedWideSymmetricBoundedOvershootCrossingProbability b a K := by
    rw [hgate, Tao.taoPMFToOuterMeasure_biUnion_finset_eq_sum p I _ hdis,
      ENNReal.toReal_sum (fun s _ => hfinite s)]
    exact Finset.sum_congr rfl hmass
  have htotal := Tao.taoGatedSubmass_sum_add_rejected_eq_one p E (Tao.taoSection7OffsetZMod q)
  rw [sum_taoGatedSubmass_eq_sourceEventProbability p E (Tao.taoSection7OffsetZMod q), hprob] at htotal
  change Tao.taoGatedRejectedMass p E (Tao.taoSection7OffsetZMod q) = _
  linarith

end

end Erdos1135Predecessor.ND.PositiveDensity
