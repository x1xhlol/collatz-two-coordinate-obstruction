import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Syracuse.ValuationCylinderResidue

/-!
# Finite Cylinder Mass For Syracuse Valuation Words

This module records exact finite masses for terminal valuation-cylinder parity words.  The
head-true sample space isolates Tao's odd-relative denominator convention before any finite
`Syrac`, Fourier, renewal, or Proposition 1.9 estimates are introduced.
-/

namespace Erdos1135
namespace Tao

/-- Parity words whose first bit is the odd branch. -/
abbrev HeadTrueParityWords (k : ℕ) : Type :=
  {w : Terras.ParityWord (k + 1) // w 0 = true}

instance (k : ℕ) : Nonempty (HeadTrueParityWords k) :=
  ⟨⟨fun _ => true, rfl⟩⟩

instance (k : ℕ) : Fintype (HeadTrueParityWords k) := inferInstance
instance (k : ℕ) : DecidableEq (HeadTrueParityWords k) := inferInstance

/-- Drop the forced first odd bit, leaving the free tail word. -/
noncomputable def headTrueParityWordsEquivTail (k : ℕ) :
    HeadTrueParityWords k ≃ Terras.ParityWord k where
  toFun w := Fin.tail w.1
  invFun u := ⟨Fin.cons true u, by simp⟩
  left_inv := by
    intro w
    apply Subtype.ext
    funext i
    cases i using Fin.cases with
    | zero => exact w.2.symm
    | succ i => simp [Fin.tail]
  right_inv := by
    intro u
    funext i
    simp [Fin.tail]

theorem card_headTrueParityWords (k : ℕ) :
    Fintype.card (HeadTrueParityWords k) = 2 ^ k := by
  rw [Fintype.card_congr (headTrueParityWordsEquivTail k)]
  exact Terras.card_parityWord k

noncomputable def parityWordPrefixEquivTail
    (K : ℕ) (ps : List Bool) (hps : ps.length ≤ K) :
    {w : Terras.ParityWord K //
      ∀ i : Fin ps.length,
        w ⟨i.1, Nat.lt_of_lt_of_le i.2 hps⟩ = ps.get i} ≃
      Terras.ParityWord (K - ps.length) where
  toFun w := fun j => w.1 ⟨ps.length + j.1, by omega⟩
  invFun tail := ⟨fun i =>
      if h : i.1 < ps.length then ps.get ⟨i.1, h⟩
      else tail ⟨i.1 - ps.length, by omega⟩, by
    intro i
    simp [i.2]⟩
  left_inv := by
    intro w
    apply Subtype.ext
    funext i
    by_cases h : i.1 < ps.length
    · have hi_eq : (⟨i.1, Nat.lt_of_lt_of_le h hps⟩ : Fin K) = i := Fin.ext rfl
      have hw := w.2 ⟨i.1, h⟩
      simp [h]
      simpa [hi_eq] using hw.symm
    · have hidx : ps.length + (i.1 - ps.length) = i.1 := by omega
      simp [h, hidx]
  right_inv := by
    intro tail
    funext j
    have hnot : ¬ps.length + j.1 < ps.length := by omega
    have hsub : ps.length + j.1 - ps.length = j.1 := by omega
    simp [hnot, hsub]

theorem card_parityWord_prefix
    (K : ℕ) (ps : List Bool) (hps : ps.length ≤ K) :
    Fintype.card {w : Terras.ParityWord K //
      ∀ i : Fin ps.length,
        w ⟨i.1, Nat.lt_of_lt_of_le i.2 hps⟩ = ps.get i} =
      2 ^ (K - ps.length) := by
  rw [Fintype.card_congr (parityWordPrefixEquivTail K ps hps)]
  exact Terras.card_parityWord (K - ps.length)

noncomputable def headTruePrefixEquivParityPrefix
    (K : ℕ) (ps : List Bool) (hps : ps.length ≤ K) :
    {w : HeadTrueParityWords K //
      ∀ i : Fin ps.length,
        (headTrueParityWordsEquivTail K w)
          ⟨i.1, Nat.lt_of_lt_of_le i.2 hps⟩ = ps.get i} ≃
    {u : Terras.ParityWord K //
      ∀ i : Fin ps.length,
        u ⟨i.1, Nat.lt_of_lt_of_le i.2 hps⟩ = ps.get i} where
  toFun w := ⟨(headTrueParityWordsEquivTail K) w.1, w.2⟩
  invFun u := ⟨(headTrueParityWordsEquivTail K).symm u.1, by
    simpa using u.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    exact (headTrueParityWordsEquivTail K).left_inv w.1
  right_inv := by
    intro u
    apply Subtype.ext
    exact (headTrueParityWordsEquivTail K).right_inv u.1

theorem card_headTrue_prefix
    (K : ℕ) (ps : List Bool) (hps : ps.length ≤ K) :
    Fintype.card {w : HeadTrueParityWords K //
      ∀ i : Fin ps.length,
        (headTrueParityWordsEquivTail K w)
          ⟨i.1, Nat.lt_of_lt_of_le i.2 hps⟩ = ps.get i} =
      2 ^ (K - ps.length) := by
  rw [Fintype.card_congr (headTruePrefixEquivParityPrefix K ps hps)]
  exact card_parityWord_prefix K ps hps

theorem pmfProb_uniform_headTrue_prefix
    (K : ℕ) (ps : List Bool) (hps : ps.length ≤ K) :
    pmfProb (PMF.uniformOfFintype (HeadTrueParityWords K))
      {w : HeadTrueParityWords K |
        ∀ i : Fin ps.length,
          (headTrueParityWordsEquivTail K w)
            ⟨i.1, Nat.lt_of_lt_of_le i.2 hps⟩ = ps.get i} =
      (1 : ℝ) / (2 ^ ps.length : ℝ) := by
  classical
  rw [pmfProb_uniformOfFintype]
  change ((Fintype.card {w : HeadTrueParityWords K //
        ∀ i : Fin ps.length,
          (headTrueParityWordsEquivTail K w)
            ⟨i.1, Nat.lt_of_lt_of_le i.2 hps⟩ = ps.get i} : ℕ) : ℝ) /
      ((Fintype.card (HeadTrueParityWords K) : ℕ) : ℝ) =
    (1 : ℝ) / (2 ^ ps.length : ℝ)
  rw [card_headTrue_prefix K ps hps, card_headTrueParityWords]
  have hpow : 2 ^ K = 2 ^ (K - ps.length) * 2 ^ ps.length := by
    have hK : K = K - ps.length + ps.length := by omega
    nth_rw 1 [hK]
    rw [pow_add]
  rw [hpow]
  norm_num [Nat.cast_mul]
  field_simp [pow_ne_zero]

noncomputable def parityWordEqListEquivUnit (ps : List Bool) :
    {w : Terras.ParityWord ps.length // Terras.parityWordToList w = ps} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨parityWordOfList ps, parityWordToList_parityWordOfList ps⟩
  left_inv := by
    intro w
    apply Subtype.ext
    apply List.ofFn_injective
    change Terras.parityWordToList (parityWordOfList ps) =
      Terras.parityWordToList w.1
    rw [parityWordToList_parityWordOfList, w.2]
  right_inv := by
    intro u
    cases u
    rfl

theorem card_parityWord_eq_list (ps : List Bool) :
    Fintype.card {w : Terras.ParityWord ps.length //
      Terras.parityWordToList w = ps} = 1 := by
  rw [Fintype.card_congr (parityWordEqListEquivUnit ps)]
  simp

theorem pmfProb_uniform_parityWord_eq_list (ps : List Bool) :
    pmfProb (PMF.uniformOfFintype (Terras.ParityWord ps.length))
      {w : Terras.ParityWord ps.length | Terras.parityWordToList w = ps} =
        (1 : ℝ) / (2 ^ ps.length : ℝ) := by
  classical
  rw [pmfProb_uniformOfFintype]
  change ((Fintype.card {w : Terras.ParityWord ps.length //
        Terras.parityWordToList w = ps} : ℕ) : ℝ) /
      ((Fintype.card (Terras.ParityWord ps.length) : ℕ) : ℝ) =
    (1 : ℝ) / (2 ^ ps.length : ℝ)
  rw [card_parityWord_eq_list, Terras.card_parityWord]
  norm_num

theorem pmfProb_uniform_syracuseValuationCylinderWord (as : List ℕ+) :
    pmfProb (PMF.uniformOfFintype (Terras.ParityWord (taoTupleWeight as + 1)))
      {w : Terras.ParityWord (taoTupleWeight as + 1) |
        Terras.parityWordToList w = syracuseValuationCylinderWord as} =
      (1 : ℝ) / (2 ^ (taoTupleWeight as + 1) : ℝ) := by
  rw [← syracuseValuationCylinderWord_length as]
  exact pmfProb_uniform_parityWord_eq_list (syracuseValuationCylinderWord as)

noncomputable def headTrueTailEqListEquiv (ps : List Bool) :
    {w : HeadTrueParityWords ps.length //
      Terras.parityWordToList ((headTrueParityWordsEquivTail ps.length) w) = ps} ≃
    {u : Terras.ParityWord ps.length // Terras.parityWordToList u = ps} where
  toFun w := ⟨(headTrueParityWordsEquivTail ps.length) w.1, w.2⟩
  invFun u := ⟨(headTrueParityWordsEquivTail ps.length).symm u.1, by
    simpa using u.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    exact (headTrueParityWordsEquivTail ps.length).left_inv w.1
  right_inv := by
    intro u
    apply Subtype.ext
    exact (headTrueParityWordsEquivTail ps.length).right_inv u.1

theorem card_headTrue_tail_eq_list (ps : List Bool) :
    Fintype.card {w : HeadTrueParityWords ps.length //
      Terras.parityWordToList ((headTrueParityWordsEquivTail ps.length) w) = ps} = 1 := by
  rw [Fintype.card_congr (headTrueTailEqListEquiv ps)]
  exact card_parityWord_eq_list ps

theorem pmfProb_uniform_headTrue_tail_eq_list (ps : List Bool) :
    pmfProb (PMF.uniformOfFintype (HeadTrueParityWords ps.length))
      {w : HeadTrueParityWords ps.length |
        Terras.parityWordToList ((headTrueParityWordsEquivTail ps.length) w) = ps} =
      (1 : ℝ) / (2 ^ ps.length : ℝ) := by
  classical
  rw [pmfProb_uniformOfFintype]
  change ((Fintype.card {w : HeadTrueParityWords ps.length //
        Terras.parityWordToList ((headTrueParityWordsEquivTail ps.length) w) = ps} : ℕ) :
      ℝ) / ((Fintype.card (HeadTrueParityWords ps.length) : ℕ) : ℝ) =
    (1 : ℝ) / (2 ^ ps.length : ℝ)
  rw [card_headTrue_tail_eq_list, card_headTrueParityWords]
  norm_num

/-- The valuation-cylinder word with the initial odd bit removed. -/
def syracuseValuationCylinderTail (as : List ℕ+) : List Bool :=
  (syracuseValuationCylinderWord as).drop 1

theorem syracuseValuationCylinderWord_eq_true_cons_tail (as : List ℕ+) :
    syracuseValuationCylinderWord as = true :: syracuseValuationCylinderTail as := by
  cases as with
  | nil =>
      simp [syracuseValuationCylinderTail]
  | cons a as =>
      simp [syracuseValuationCylinderTail, syracuseValuationCylinderWord_cons,
        syracuseParityBlock]

theorem syracuseValuationCylinderTail_length (as : List ℕ+) :
    (syracuseValuationCylinderTail as).length = taoTupleWeight as := by
  rw [syracuseValuationCylinderTail, List.length_drop]
  rw [syracuseValuationCylinderWord_length]
  omega

noncomputable def cylinderWitness (as : List ℕ+) : ℕ :=
  (Classical.choose
    (existsUnique_residue_syracuseValuationCylinderWord_weight as)).val

theorem parityPrefixList_cylinderWitness (as : List ℕ+) :
    Terras.parityPrefixList (taoTupleWeight as + 1) (cylinderWitness as) =
      syracuseValuationCylinderWord as := by
  classical
  unfold cylinderWitness
  let h := existsUnique_residue_syracuseValuationCylinderWord_weight as
  let r : ZMod (2 ^ (taoTupleWeight as + 1)) := Classical.choose h
  have hr : ∀ N : ℕ,
      (N : ZMod (2 ^ (taoTupleWeight as + 1))) = r ↔
        Terras.parityPrefixList (taoTupleWeight as + 1) N =
          syracuseValuationCylinderWord as :=
    (Classical.choose_spec h).1
  exact (hr r.val).mp (ZMod.natCast_zmod_val r)

theorem syracuseValuationCylinderWord_length_injective {as bs : List ℕ+}
    (h : syracuseValuationCylinderWord as = syracuseValuationCylinderWord bs) :
    as.length = bs.length := by
  have hcount := congrArg (fun ps : List Bool => ps.count true) h
  simp [syracuseValuationCylinderWord_count_true] at hcount
  omega

theorem syracuseValuationCylinderWord_weight_eq {as bs : List ℕ+}
    (h : syracuseValuationCylinderWord as = syracuseValuationCylinderWord bs) :
    taoTupleWeight as = taoTupleWeight bs := by
  have hlen := congrArg List.length h
  simp [syracuseValuationCylinderWord_length] at hlen
  omega

theorem syracuseValuationCylinderWord_injective :
    Function.Injective syracuseValuationCylinderWord := by
  intro as bs h
  let N := cylinderWitness as
  have hlen : as.length = bs.length := syracuseValuationCylinderWord_length_injective h
  have hweight : taoTupleWeight as = taoTupleWeight bs :=
    syracuseValuationCylinderWord_weight_eq h
  have hpref_as :
      Terras.parityPrefixList (taoTupleWeight as + 1) N =
        syracuseValuationCylinderWord as := by
    exact parityPrefixList_cylinderWitness as
  have hpref_bs :
      Terras.parityPrefixList (taoTupleWeight bs + 1) N =
        syracuseValuationCylinderWord bs := by
    rw [← hweight]
    exact hpref_as.trans h
  have hf0_as := Terras.followsParityList_parityPrefixList (taoTupleWeight as + 1) N
  have hf_as : Terras.FollowsParityList (syracuseValuationCylinderWord as) N := by
    simpa [hpref_as] using hf0_as
  have hN : Odd N := odd_of_follows_syracuseValuationCylinderWord hf_as
  have hdecode_as := syracuseValuationPNatList_eq_of_follows_cylinder as hN hf_as
  have hf0_bs := Terras.followsParityList_parityPrefixList (taoTupleWeight bs + 1) N
  have hf_bs : Terras.FollowsParityList (syracuseValuationCylinderWord bs) N := by
    simpa [hpref_bs] using hf0_bs
  have hdecode_bs := syracuseValuationPNatList_eq_of_follows_cylinder bs hN hf_bs
  rw [← hlen] at hdecode_bs
  exact hdecode_as.symm.trans hdecode_bs

theorem syracuseValuationCylinderTail_injective :
    Function.Injective syracuseValuationCylinderTail := by
  intro as bs h
  apply syracuseValuationCylinderWord_injective
  rw [syracuseValuationCylinderWord_eq_true_cons_tail as,
    syracuseValuationCylinderWord_eq_true_cons_tail bs, h]

theorem pmfProb_uniform_headTrue_syracuseValuationCylinderTail (as : List ℕ+) :
    pmfProb (PMF.uniformOfFintype (HeadTrueParityWords (taoTupleWeight as)))
      {w : HeadTrueParityWords (taoTupleWeight as) |
        Terras.parityWordToList ((headTrueParityWordsEquivTail (taoTupleWeight as)) w) =
          syracuseValuationCylinderTail as} =
      (1 : ℝ) / (2 ^ taoTupleWeight as : ℝ) := by
  rw [← syracuseValuationCylinderTail_length as]
  exact pmfProb_uniform_headTrue_tail_eq_list (syracuseValuationCylinderTail as)

theorem pmfProb_uniformOfFintype_singleton
    {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] (a : α) :
    pmfProb (PMF.uniformOfFintype α) {x : α | x = a} =
      (1 : ℝ) / (Fintype.card α : ℝ) := by
  classical
  simpa using pmfProb_uniformOfFintype_finset ({a} : Finset α)

theorem pmfProb_uniform_syracuseValuationCylinderResidue (as : List ℕ+) :
    pmfProb (PMF.uniformOfFintype (ZMod (2 ^ (taoTupleWeight as + 1))))
      {r : ZMod (2 ^ (taoTupleWeight as + 1)) |
        r = syracuseValuationCylinderResidue as} =
      (1 : ℝ) / (2 ^ (taoTupleWeight as + 1) : ℝ) := by
  rw [pmfProb_uniformOfFintype_singleton]
  simp [ZMod.card]

theorem pmfProb_uniform_headTrue_syracuseCylinderPrefix
    (K : ℕ) (as : List ℕ+) (hK : taoTupleWeight as ≤ K) :
    pmfProb (PMF.uniformOfFintype (HeadTrueParityWords K))
      {w : HeadTrueParityWords K |
        ∀ i : Fin (syracuseValuationCylinderTail as).length,
          (headTrueParityWordsEquivTail K w)
            ⟨i.1, Nat.lt_of_lt_of_le i.2 (by
              rw [syracuseValuationCylinderTail_length]
              exact hK)⟩ = (syracuseValuationCylinderTail as).get i} =
      (1 : ℝ) / (2 ^ taoTupleWeight as : ℝ) := by
  have htail : (syracuseValuationCylinderTail as).length ≤ K := by
    rw [syracuseValuationCylinderTail_length]
    exact hK
  simpa [syracuseValuationCylinderTail_length] using
    pmfProb_uniform_headTrue_prefix K (syracuseValuationCylinderTail as) htail

end Tao
end Erdos1135
