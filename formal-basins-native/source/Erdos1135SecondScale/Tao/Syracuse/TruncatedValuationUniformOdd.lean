/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.TruncatedValuationDecoder
import Erdos1135SecondScale.Tao.Syracuse.ValuationDistribution

/-!
# Canonical uniform odd-residue decoder law

For the positive modulus `2^(K+1)`, head-true parity words parameterize the
canonical uniform law on odd residue classes.  This leaf pushes that law
through the strict valuation decoder without conditioning on short tuples.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Odd canonical representatives correspond exactly to parity words whose
first bit is the odd branch. -/
theorem odd_val_iff_parityPrefixZModEquiv_head_true
    (K : ℕ) (r : ZMod (2 ^ (K + 1))) :
    Odd r.val ↔ (Terras.parityPrefixZModEquiv (K + 1) r) 0 = true := by
  change Odd r.val ↔ Terras.parityBit r.val = true
  constructor
  · intro hr
    exact (Terras.parityBit_eq_true_iff_not_even r.val).2
      (Nat.not_even_iff_odd.2 hr)
  · intro hr
    exact Nat.not_even_iff_odd.1
      ((Terras.parityBit_eq_true_iff_not_even r.val).1 hr)

noncomputable def oddResiduesEquivHeadTrueParityWords (K : ℕ) :
    {r : ZMod (2 ^ (K + 1)) // Odd r.val} ≃ HeadTrueParityWords K :=
  (Terras.parityPrefixZModEquiv (K + 1)).subtypeEquiv
    (odd_val_iff_parityPrefixZModEquiv_head_true K)

/-- The residue modulo `2^(K+1)` whose full parity prefix is the supplied
head-true word. -/
noncomputable def headTrueParityWordResidue
    (K : ℕ) (w : HeadTrueParityWords K) : ZMod (2 ^ (K + 1)) :=
  (Terras.parityPrefixZModEquiv (K + 1)).symm w.1

theorem parityPrefixOfResidue_headTrueParityWordResidue
    (K : ℕ) (w : HeadTrueParityWords K) :
    Terras.parityPrefixOfResidue (K + 1)
        (headTrueParityWordResidue K w) = w.1 := by
  exact (Terras.parityPrefixZModEquiv (K + 1)).apply_symm_apply w.1

theorem headTrueParityWordResidue_val_odd
    (K : ℕ) (w : HeadTrueParityWords K) :
    Odd (headTrueParityWordResidue K w).val := by
  have hprefix := congrFun
    (parityPrefixOfResidue_headTrueParityWordResidue K w) (0 : Fin (K + 1))
  have hbit : Terras.parityBit (headTrueParityWordResidue K w).val = true := by
    simpa [Terras.parityPrefixOfResidue, Terras.parityPrefix] using hprefix.trans w.2
  exact Nat.not_even_iff_odd.mp
    ((Terras.parityBit_eq_true_iff_not_even _).mp hbit)

theorem headTrueParityWordResidue_injective (K : ℕ) :
    Function.Injective (headTrueParityWordResidue K) := by
  intro w v h
  apply Subtype.ext
  exact (Terras.parityPrefixZModEquiv (K + 1)).symm.injective h

/-- Canonical uniform probability law on odd residue classes modulo
`2^(K+1)`, represented as the pushforward of uniform head-true words. -/
noncomputable def taoUniformOddResiduePMF
    (K : ℕ) : PMF (ZMod (2 ^ (K + 1))) :=
  (PMF.uniformOfFintype (HeadTrueParityWords K)).map
    (headTrueParityWordResidue K)

def taoHeadTrueValuationPrefix
    (K : ℕ) (as : List ℕ+) (hweight : taoTupleWeight as ≤ K)
    (w : HeadTrueParityWords K) : Prop :=
  ∀ i : Fin (syracuseValuationCylinderTail as).length,
    (headTrueParityWordsEquivTail K w)
        ⟨i.1, Nat.lt_of_lt_of_le i.2 (by
          rw [syracuseValuationCylinderTail_length]
          exact hweight)⟩ =
      (syracuseValuationCylinderTail as).get i

private theorem headTrueValuationPrefix_iff_parityPrefixList_cylinder
    (K : ℕ) (as : List ℕ+) (w : HeadTrueParityWords K)
    (hweight : taoTupleWeight as ≤ K) :
    taoHeadTrueValuationPrefix K as hweight w ↔
      Terras.parityPrefixList (taoTupleWeight as + 1)
          (headTrueParityWordResidue K w).val =
        syracuseValuationCylinderWord as := by
  have hfull :
      Terras.parityPrefix (K + 1) (headTrueParityWordResidue K w).val = w.1 := by
    exact parityPrefixOfResidue_headTrueParityWordResidue K w
  constructor
  · intro htail
    have hcylLength : (syracuseValuationCylinderWord as).length =
        taoTupleWeight as + 1 := syracuseValuationCylinderWord_length as
    have hwordWeight :
        Terras.parityPrefix (taoTupleWeight as + 1)
            (headTrueParityWordResidue K w).val =
          fun i => (syracuseValuationCylinderWord as).get
            (Fin.cast hcylLength.symm i) := by
      funext i
      cases i using Fin.cases with
      | zero =>
          have hzero := congrFun hfull (0 : Fin (K + 1))
          simpa [Terras.parityPrefix, parityWordOfList,
            syracuseValuationCylinderWord_eq_true_cons_tail] using hzero.trans w.2
      | succ j =>
          let jt : Fin (syracuseValuationCylinderTail as).length :=
            ⟨j.1, by simpa [syracuseValuationCylinderTail_length] using j.2⟩
          let jK : Fin K := ⟨j.1, lt_of_lt_of_le j.2 hweight⟩
          have hfullj := congrFun hfull (Fin.succ jK)
          have htailj := htail jt
          calc
            Terras.parityPrefix (taoTupleWeight as + 1)
                (headTrueParityWordResidue K w).val (Fin.succ j) =
                w.1 (Fin.succ jK) := by
                  simpa [Terras.parityPrefix, jK] using hfullj
            _ = (syracuseValuationCylinderTail as).get jt := by
                  simpa [headTrueParityWordsEquivTail, Fin.tail, jK, jt] using htailj
            _ = (syracuseValuationCylinderWord as).get
                (Fin.cast hcylLength.symm (Fin.succ j)) := by
                  simp [syracuseValuationCylinderWord_eq_true_cons_tail, jt]
    have hword :
        Terras.parityPrefix (syracuseValuationCylinderWord as).length
            (headTrueParityWordResidue K w).val =
          parityWordOfList (syracuseValuationCylinderWord as) := by
      funext i
      have hi := congrFun hwordWeight (Fin.cast hcylLength i)
      simpa [Terras.parityPrefix, parityWordOfList] using hi
    have hresult := (parityPrefix_eq_parityWordOfList_iff
      (syracuseValuationCylinderWord as)
      (headTrueParityWordResidue K w).val).mp hword
    simpa [syracuseValuationCylinderWord_length] using hresult
  · intro hprefix
    have hprefix' :
        Terras.parityPrefixList (syracuseValuationCylinderWord as).length
            (headTrueParityWordResidue K w).val =
          syracuseValuationCylinderWord as := by
      simpa [syracuseValuationCylinderWord_length] using hprefix
    have hword := (parityPrefix_eq_parityWordOfList_iff
      (syracuseValuationCylinderWord as)
      (headTrueParityWordResidue K w).val).mpr hprefix'
    intro i
    let j : Fin (taoTupleWeight as) :=
      ⟨i.1, by simpa [syracuseValuationCylinderTail_length] using i.2⟩
    let jK : Fin K := ⟨i.1, lt_of_lt_of_le j.2 hweight⟩
    have hiWeight : i.1 < taoTupleWeight as := by
      simpa [syracuseValuationCylinderTail_length] using i.2
    let jC : Fin (syracuseValuationCylinderWord as).length :=
      ⟨i.1 + 1, by rw [syracuseValuationCylinderWord_length]; omega⟩
    have hfullj := congrFun hfull (Fin.succ jK)
    have hwordj := congrFun hword jC
    calc
      (headTrueParityWordsEquivTail K w) jK = w.1 (Fin.succ jK) := by
        rfl
      _ = Terras.parityPrefix (taoTupleWeight as + 1)
          (headTrueParityWordResidue K w).val (Fin.succ j) := by
            simpa [Terras.parityPrefix, jK] using hfullj.symm
      _ = parityWordOfList (syracuseValuationCylinderWord as) jC := by
        simpa [Terras.parityPrefix, jC, j] using hwordj
      _ = (syracuseValuationCylinderTail as).get i := by
        simp [parityWordOfList,
          syracuseValuationCylinderWord_eq_true_cons_tail, jC]

theorem taoProp19ResidueDecoder_headTrue_eq_some_iff
    {n K : ℕ} (w : HeadTrueParityWords K)
    (v : BoundedValuationTuple n (K + 1)) :
    taoProp19ResidueDecoder n (K + 1) (headTrueParityWordResidue K w) = some v ↔
      taoHeadTrueValuationPrefix K (BoundedValuationTuple.toList v)
        (Nat.lt_succ_iff.mp (BoundedValuationTuple.taoTupleWeight_toList_lt v)) w := by
  have hodd := headTrueParityWordResidue_val_odd K w
  have hweight :
      taoTupleWeight (BoundedValuationTuple.toList v) ≤ K := by
    have hv := BoundedValuationTuple.taoTupleWeight_toList_lt v
    omega
  rw [taoProp19ResidueDecoder, dif_pos hodd]
  unfold taoTruncatedActualValuation
  rw [truncateValuationList_eq_some_iff]
  rw [headTrueValuationPrefix_iff_parityPrefixList_cylinder K
    (BoundedValuationTuple.toList v) w hweight]
  simpa only [BoundedValuationTuple.toList_length v] using
    valuation_eq_iff_parityPrefixList_cylinder
      (BoundedValuationTuple.toList v) hodd

theorem taoUniformOddResiduePMF_map_decoder_apply_some_toReal
    {n K : ℕ} (v : BoundedValuationTuple n (K + 1)) :
    (((taoUniformOddResiduePMF K).map
      (taoProp19ResidueDecoder n (K + 1))) (some v)).toReal =
      (truncatedValuationTupleGeom2PMF n (K + 1) (some v)).toReal := by
  rw [taoUniformOddResiduePMF, PMF.map_comp]
  rw [← pmfProb_singleton_eq_map_apply_toReal]
  let hweight : taoTupleWeight (BoundedValuationTuple.toList v) ≤ K :=
    Nat.lt_succ_iff.mp (BoundedValuationTuple.taoTupleWeight_toList_lt v)
  rw [show {w : HeadTrueParityWords K |
      (taoProp19ResidueDecoder n (K + 1) ∘ headTrueParityWordResidue K) w = some v} =
      {w : HeadTrueParityWords K |
        taoHeadTrueValuationPrefix K (BoundedValuationTuple.toList v) hweight w} by
    ext w
    exact taoProp19ResidueDecoder_headTrue_eq_some_iff w v]
  unfold taoHeadTrueValuationPrefix
  rw [← boundedValuationTuple_geom2PNatListMass_eq_headTrue_syracuseCylinderPrefix
    (K := K) v hweight]
  rw [truncatedValuationTupleGeom2PMF_apply_some]
  simpa [boundedValuationTupleGeom2Mass] using
    (boundedValuationTupleGeom2MassENNReal_toReal v).symm

/-- The canonical uniform odd-residue law at every positive power-of-two
modulus pushes through the strict decoder to the ideal finite overflow law. -/
theorem taoUniformOddResiduePMF_map_decoder
    (n K : ℕ) :
    (taoUniformOddResiduePMF K).map
        (taoProp19ResidueDecoder n (K + 1)) =
      truncatedValuationTupleGeom2PMF n (K + 1) := by
  classical
  let p := (taoUniformOddResiduePMF K).map
    (taoProp19ResidueDecoder n (K + 1))
  let q := truncatedValuationTupleGeom2PMF n (K + 1)
  have hsome : ∀ v : BoundedValuationTuple n (K + 1), p (some v) = q (some v) := by
    intro v
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top p (some v)) (PMF.apply_ne_top q (some v))).mp
    exact taoUniformOddResiduePMF_map_decoder_apply_some_toReal v
  apply PMF.ext
  intro x
  cases x with
  | some v => exact hsome v
  | none =>
      have hp := PMF.tsum_coe p
      have hq := PMF.tsum_coe q
      rw [tsum_fintype, Fintype.sum_option] at hp hq
      have hsum : (∑ v, p (some v)) = ∑ v, q (some v) := by
        apply Finset.sum_congr rfl
        intro v _hv
        exact hsome v
      have hpnone : p none = 1 - ∑ v, p (some v) :=
        ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top hp
      have hqnone : q none = 1 - ∑ v, q (some v) :=
        ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top hq
      rw [hpnone, hqnone, hsum]

theorem taoUniformOddResiduePMF_map_decoder_mod_two (n : ℕ) :
    (taoUniformOddResiduePMF 0).map (taoProp19ResidueDecoder n 1) =
      truncatedValuationTupleGeom2PMF n 1 :=
  taoUniformOddResiduePMF_map_decoder n 0

theorem taoUniformOddResiduePMF_map_decoder_zero_length (K : ℕ) :
    (taoUniformOddResiduePMF K).map (taoProp19ResidueDecoder 0 (K + 1)) =
      truncatedValuationTupleGeom2PMF 0 (K + 1) :=
  taoUniformOddResiduePMF_map_decoder 0 K

theorem taoUniformOddResiduePMF_map_decoder_mod_four_one :
    (taoUniformOddResiduePMF 1).map (taoProp19ResidueDecoder 1 2) =
      truncatedValuationTupleGeom2PMF 1 2 :=
  taoUniformOddResiduePMF_map_decoder 1 1

end

end Tao
end Erdos1135SecondScale
