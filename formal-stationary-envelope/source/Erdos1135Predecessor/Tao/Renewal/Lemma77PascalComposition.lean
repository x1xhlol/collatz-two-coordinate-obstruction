/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma77PascalPotential
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

namespace Erdos1135Predecessor

namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

def Lemma77RawPrefixFiber (r t : ℕ) :=
  {pre : List ℕ //
    pre.length = r ∧ pre.sum = t ∧ taoSection7AllGeTwo pre}

noncomputable def lemma77RawTerminalDropLastEquiv (r t : ℕ) :
    Lemma77RawTerminalFiber (r + 1) (t + 3) ≃
      Lemma77RawPrefixFiber r t where
  toFun bs := by
    have hflat : bs.1.dropLast ++ [3] = bs.1 := by
      apply List.dropLast_append_getLast?
      simp [bs.2.2.2.2]
    refine ⟨bs.1.dropLast, ?_, ?_, ?_⟩
    · simp [List.length_dropLast, bs.2.1]
    · have hsum := congrArg List.sum hflat
      have hbst := bs.2.2.1
      simp at hsum
      omega
    · intro b hb
      exact bs.2.2.2.1 b (List.mem_of_mem_dropLast hb)
  invFun pre := by
    refine ⟨pre.1 ++ [3], ?_, ?_, ?_, ?_⟩
    · simp [pre.2.1]
    · simp [pre.2.2.1]
    · intro b hb
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact pre.2.2.2 b hb
      · norm_num
    · simp
  left_inv bs := by
    apply Subtype.ext
    apply List.dropLast_append_getLast?
    simp [bs.2.2.2.2]
  right_inv pre := by
    apply Subtype.ext
    simp

theorem lemma77RawPascalWordMass_singleton_three :
    lemma77RawPascalWordMass [3] = (1 / 4 : ℝ) := by
  simp [lemma77RawPascalWordMass, pascalGeom2PairMass_three]

theorem lemma77RawPascalWordMass_eq_dropLast_mul_quarter
    {r t : ℕ} (bs : Lemma77RawTerminalFiber (r + 1) (t + 3)) :
    lemma77RawPascalWordMass bs.1 =
      lemma77RawPascalWordMass bs.1.dropLast * (1 / 4 : ℝ) := by
  have hflat : bs.1.dropLast ++ [3] = bs.1 := by
    apply List.dropLast_append_getLast?
    simp [bs.2.2.2.2]
  calc
    lemma77RawPascalWordMass bs.1 =
        lemma77RawPascalWordMass (bs.1.dropLast ++ [3]) := by rw [hflat]
    _ = lemma77RawPascalWordMass bs.1.dropLast * (1 / 4 : ℝ) := by
      rw [lemma77RawPascalWordMass_append,
        lemma77RawPascalWordMass_singleton_three]

abbrev Lemma77OrderedPairRefinement (pre : List ℕ) :=
  (i : Fin pre.length) → Fin (pre.get i - 1)

theorem lemma77_card_orderedPairRefinement (pre : List ℕ) :
    Fintype.card (Lemma77OrderedPairRefinement pre) =
      (pre.map fun b => b - 1).prod := by
  rw [show Fintype.card (Lemma77OrderedPairRefinement pre) =
      ∏ i : Fin pre.length, (pre.get i - 1) by
    rw [Fintype.card_pi]
    simp]
  rw [← List.prod_ofFn]
  have h := List.ofFn_get (pre.map fun b => b - 1)
  simpa using congrArg List.prod h

theorem lemma77RawPascalWordMass_eq_predProd_mul_pow_sum
    (pre : List ℕ) (h2 : taoSection7AllGeTwo pre) :
    lemma77RawPascalWordMass pre =
      (((pre.map fun b => b - 1).prod : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ pre.sum := by
  induction pre with
  | nil => simp
  | cons b pre ih =>
      have hb : 2 ≤ b := h2 b (by simp)
      have htail : taoSection7AllGeTwo pre := by
        intro x hx
        exact h2 x (by simp [hx])
      rw [show lemma77RawPascalWordMass (b :: pre) =
          pascalGeom2PairMass b * lemma77RawPascalWordMass pre by
        simp [lemma77RawPascalWordMass]]
      rw [pascalGeom2PairMass_eq b hb, ih htail]
      simp only [List.map_cons, List.prod_cons, List.sum_cons,
        Nat.cast_mul, pow_add]
      ring

theorem lemma77RawPascalWordMass_eq_refinementCard_mul_pow
    (r t : ℕ) (pre : Lemma77RawPrefixFiber r t) :
    lemma77RawPascalWordMass pre.1 =
      (Fintype.card (Lemma77OrderedPairRefinement pre.1) : ℝ) *
        (1 / 2 : ℝ) ^ t := by
  rw [lemma77RawPascalWordMass_eq_predProd_mul_pow_sum pre.1 pre.2.2.2,
    lemma77_card_orderedPairRefinement, pre.2.2.1]

theorem lemma77RawPascalWordMass_mul_quarter_eq_refinementCard_mul_pow
    (r t : ℕ) (pre : Lemma77RawPrefixFiber r t) :
    lemma77RawPascalWordMass pre.1 * (1 / 4 : ℝ) =
      (Fintype.card (Lemma77OrderedPairRefinement pre.1) : ℝ) *
        (1 / 2 : ℝ) ^ (t + 2) := by
  rw [lemma77RawPascalWordMass_eq_refinementCard_mul_pow r t pre, pow_add]
  norm_num
  ring

theorem lemma77RawTerminalMass_eq_tsum_refinementCard
    (r t : ℕ) :
    (∑' bs : Lemma77RawTerminalFiber (r + 1) (t + 3),
      lemma77RawPascalWordMass bs.1) =
      ∑' pre : Lemma77RawPrefixFiber r t,
        (Fintype.card (Lemma77OrderedPairRefinement pre.1) : ℝ) *
          (1 / 2 : ℝ) ^ (t + 2) := by
  calc
    (∑' bs : Lemma77RawTerminalFiber (r + 1) (t + 3),
        lemma77RawPascalWordMass bs.1) =
        ∑' bs : Lemma77RawTerminalFiber (r + 1) (t + 3),
          lemma77RawPascalWordMass
              (lemma77RawTerminalDropLastEquiv r t bs).1 *
            (1 / 4 : ℝ) := by
              apply tsum_congr
              intro bs
              exact lemma77RawPascalWordMass_eq_dropLast_mul_quarter bs
    _ = ∑' pre : Lemma77RawPrefixFiber r t,
          lemma77RawPascalWordMass pre.1 * (1 / 4 : ℝ) := by
            exact (lemma77RawTerminalDropLastEquiv r t).tsum_eq
              (fun pre : Lemma77RawPrefixFiber r t =>
                lemma77RawPascalWordMass pre.1 * (1 / 4 : ℝ))
    _ = ∑' pre : Lemma77RawPrefixFiber r t,
          (Fintype.card (Lemma77OrderedPairRefinement pre.1) : ℝ) *
            (1 / 2 : ℝ) ^ (t + 2) := by
              apply tsum_congr
              intro pre
              exact lemma77RawPascalWordMass_mul_quarter_eq_refinementCard_mul_pow
                r t pre

def lemma77RawPrefixTuple (r t : ℕ)
    (pre : Lemma77RawPrefixFiber r t) : Fin r → ℕ :=
  fun i => pre.1.get (Fin.cast pre.2.1.symm i)

theorem lemma77RawPrefixTuple_ofFn (r t : ℕ)
    (pre : Lemma77RawPrefixFiber r t) :
    List.ofFn (lemma77RawPrefixTuple r t pre) = pre.1 := by
  apply List.ext_get
  · simp [pre.2.1]
  · intro n hleft hright
    simp [lemma77RawPrefixTuple]

def lemma77RawPrefixToAntidiagonal (r t : ℕ) :
    Lemma77RawPrefixFiber r t →
      {x // x ∈ Finset.Nat.antidiagonalTuple r t} := fun pre =>
  ⟨lemma77RawPrefixTuple r t pre,
    Finset.Nat.mem_antidiagonalTuple.mpr (by
      rw [← List.sum_ofFn, lemma77RawPrefixTuple_ofFn, pre.2.2.1])⟩

theorem lemma77RawPrefixToAntidiagonal_injective (r t : ℕ) :
    Function.Injective (lemma77RawPrefixToAntidiagonal r t) := by
  intro pre qs h
  apply Subtype.ext
  have htuple := congrArg Subtype.val h
  calc
    pre.1 = List.ofFn (lemma77RawPrefixTuple r t pre) :=
      (lemma77RawPrefixTuple_ofFn r t pre).symm
    _ = List.ofFn (lemma77RawPrefixTuple r t qs) := congrArg List.ofFn htuple
    _ = qs.1 := lemma77RawPrefixTuple_ofFn r t qs

noncomputable instance lemma77RawPrefixFiberFinite (r t : ℕ) :
    Finite (Lemma77RawPrefixFiber r t) :=
  Finite.of_injective (lemma77RawPrefixToAntidiagonal r t)
    (lemma77RawPrefixToAntidiagonal_injective r t)

noncomputable instance lemma77RawPrefixFiberFintype (r t : ℕ) :
    Fintype (Lemma77RawPrefixFiber r t) :=
  Fintype.ofFinite _

abbrev Lemma77TerminalPairRefinementFiber (r t : ℕ) :=
  (pre : Lemma77RawPrefixFiber r t) ×
    Lemma77OrderedPairRefinement pre.1

theorem lemma77_card_terminalPairRefinementFiber (r t : ℕ) :
    Fintype.card (Lemma77TerminalPairRefinementFiber r t) =
      ∑ pre : Lemma77RawPrefixFiber r t,
        Fintype.card (Lemma77OrderedPairRefinement pre.1) := by
  rw [Fintype.card_sigma]

theorem lemma77RawTerminalMass_eq_refinementFiberCard_mul_pow
    (r t : ℕ) :
    (∑' bs : Lemma77RawTerminalFiber (r + 1) (t + 3),
      lemma77RawPascalWordMass bs.1) =
      (Fintype.card (Lemma77TerminalPairRefinementFiber r t) : ℝ) *
        (1 / 2 : ℝ) ^ (t + 2) := by
  rw [lemma77RawTerminalMass_eq_tsum_refinementCard, tsum_fintype]
  rw [← Finset.sum_mul]
  congr 1
  rw [lemma77_card_terminalPairRefinementFiber]
  norm_cast

theorem lemma77HeightPotentialMass_eq_refinementFiberCard_mul_pow
    (start : TaoSection7RenewalPoint) (r t : ℕ) :
    lemma77HeightPotentialMass start ((r + 1 : ℕ) : ℤ) (t + 3) =
      (Fintype.card (Lemma77TerminalPairRefinementFiber r t) : ℝ) *
        (1 / 2 : ℝ) ^ (t + 2) := by
  rw [lemma77HeightPotentialMass_eq_rawTerminalMass start (by omega)]
  exact lemma77RawTerminalMass_eq_refinementFiberCard_mul_pow r t

def Lemma77MarkedPascalPrefix (r t : ℕ) :=
  {z : (Fin r → ℕ) × (Fin r → ℕ) //
    (∀ i, 2 ≤ z.1 i) ∧
      (∑ i, z.1 i) = t ∧
      ∀ i, 0 < z.2 i ∧ z.2 i < z.1 i}

def lemma77TerminalPairRefinementToMarked (r t : ℕ) :
    Lemma77TerminalPairRefinementFiber r t →
      Lemma77MarkedPascalPrefix r t := fun x => by
  let pre := x.1
  let q := x.2
  let b : Fin r → ℕ := lemma77RawPrefixTuple r t pre
  let a : Fin r → ℕ := fun i =>
    q (Fin.cast pre.2.1.symm i) + 1
  refine ⟨(b, a), ?_, ?_, ?_⟩
  · intro i
    exact pre.2.2.2 _ (List.get_mem pre.1 _)
  · exact Finset.Nat.mem_antidiagonalTuple.mp
      (lemma77RawPrefixToAntidiagonal r t pre).2
  · intro i
    constructor
    · simp [a]
    · have hq := (q (Fin.cast pre.2.1.symm i)).2
      dsimp [pre, q] at hq
      simp only [a, b, lemma77RawPrefixTuple]
      dsimp [pre, q]
      omega

theorem lemma77TerminalPairRefinementToMarked_bijective (r t : ℕ) :
    Function.Bijective (lemma77TerminalPairRefinementToMarked r t) := by
  constructor
  · rintro ⟨pre, q⟩ ⟨pre', q'⟩ h
    have hp := congrArg Subtype.val h
    have hb :
        lemma77RawPrefixTuple r t pre =
          lemma77RawPrefixTuple r t pre' := congrArg Prod.fst hp
    have ha := congrArg Prod.snd hp
    have hpre : pre = pre' := by
      apply Subtype.ext
      calc
        pre.1 = List.ofFn (lemma77RawPrefixTuple r t pre) :=
          (lemma77RawPrefixTuple_ofFn r t pre).symm
        _ = List.ofFn (lemma77RawPrefixTuple r t pre') :=
          congrArg List.ofFn hb
        _ = pre'.1 := lemma77RawPrefixTuple_ofFn r t pre'
    subst pre'
    have hq : q = q' := by
      funext i
      apply Fin.ext
      let k : Fin r := Fin.cast pre.2.1 i
      have hi := congrFun ha k
      simp [lemma77TerminalPairRefinementToMarked, k] at hi
      omega
    subst q'
    rfl
  · intro z
    let preList : List ℕ := List.ofFn z.1.1
    let pre : Lemma77RawPrefixFiber r t := by
      refine ⟨preList, ?_, ?_, ?_⟩
      · simp [preList]
      · simpa [preList, List.sum_ofFn] using z.2.2.1
      · intro b hb
        rw [List.mem_iff_get] at hb
        rcases hb with ⟨i, rfl⟩
        simpa [preList] using z.2.1 (Fin.cast (by simp [preList]) i)
    let q : Lemma77OrderedPairRefinement pre.1 := fun i => by
      let k : Fin r := Fin.cast pre.2.1 i
      refine ⟨z.1.2 k - 1, ?_⟩
      have hpos := (z.2.2.2 k).1
      have hlt := (z.2.2.2 k).2
      have hget : pre.1.get i = z.1.1 k := by
        simp only [pre, preList, List.get_ofFn]
        congr 1
      omega
    refine ⟨⟨pre, q⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · funext i
      simp [lemma77TerminalPairRefinementToMarked,
        pre, preList, lemma77RawPrefixTuple]
    · funext i
      have hpos := (z.2.2.2 i).1
      simp [lemma77TerminalPairRefinementToMarked, q, pre, preList]
      omega

noncomputable def lemma77TerminalPairRefinementEquivMarked (r t : ℕ) :
    Lemma77TerminalPairRefinementFiber r t ≃
      Lemma77MarkedPascalPrefix r t :=
  Equiv.ofBijective (lemma77TerminalPairRefinementToMarked r t)
    (lemma77TerminalPairRefinementToMarked_bijective r t)

def Lemma77PositivePairComposition (r t : ℕ) :=
  {x : Fin r × Fin 2 → ℕ //
    (∀ z, 0 < x z) ∧ ∑ z, x z = t}

noncomputable def lemma77MarkedPascalPrefixEquivPositivePairComposition
    (r t : ℕ) :
    Lemma77MarkedPascalPrefix r t ≃
      Lemma77PositivePairComposition r t where
  toFun z := by
    let x : Fin r × Fin 2 → ℕ := fun p =>
      if p.2 = 0 then z.1.2 p.1 else z.1.1 p.1 - z.1.2 p.1
    refine ⟨x, ?_, ?_⟩
    · intro p
      by_cases hp : p.2 = 0
      · simp [x, hp, (z.2.2.2 p.1).1]
      · have hlt := (z.2.2.2 p.1).2
        simp [x, hp]
        omega
    · rw [Fintype.sum_prod_type]
      simp_rw [Fin.sum_univ_two]
      calc
        (∑ i : Fin r, (x (i, 0) + x (i, 1))) =
            ∑ i : Fin r, z.1.1 i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hlt := (z.2.2.2 i).2
          simp [x]
          omega
        _ = t := z.2.2.1
  invFun x := by
    let b : Fin r → ℕ := fun i => x.1 (i, 0) + x.1 (i, 1)
    let a : Fin r → ℕ := fun i => x.1 (i, 0)
    refine ⟨(b, a), ?_, ?_, ?_⟩
    · intro i
      have h0 := x.2.1 (i, 0)
      have h1 := x.2.1 (i, 1)
      simp [b]
      omega
    · calc
        (∑ i : Fin r, b i) =
            ∑ i : Fin r, (x.1 (i, 0) + x.1 (i, 1)) := rfl
        _ = ∑ p : Fin r × Fin 2, x.1 p := by
          rw [Fintype.sum_prod_type]
          simp_rw [Fin.sum_univ_two]
        _ = t := x.2.2
    · intro i
      have h0 := x.2.1 (i, 0)
      have h1 := x.2.1 (i, 1)
      simp [a, b]
      omega
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hlt := (z.2.2.2 i).2
      simp
      omega
    · funext i
      simp
  right_inv x := by
    apply Subtype.ext
    funext p
    rcases p with ⟨i, k⟩
    fin_cases k
    · simp
    · have h0 := x.2.1 (i, 0)
      simp

noncomputable def lemma77TerminalPairRefinementEquivPositivePairComposition
    (r t : ℕ) :
    Lemma77TerminalPairRefinementFiber r t ≃
      Lemma77PositivePairComposition r t :=
  (lemma77TerminalPairRefinementEquivMarked r t).trans
    (lemma77MarkedPascalPrefixEquivPositivePairComposition r t)

noncomputable instance lemma77PositivePairCompositionFintype (r t : ℕ) :
    Fintype (Lemma77PositivePairComposition r t) :=
  Fintype.ofEquiv (Lemma77TerminalPairRefinementFiber r t)
    (lemma77TerminalPairRefinementEquivPositivePairComposition r t)

def Lemma77WeakPairComposition (r u : ℕ) :=
  {y : Fin r × Fin 2 → ℕ // ∑ z, y z = u}

private theorem lemma77_sum_one_pairIndex (r : ℕ) :
    (∑ _ : Fin r × Fin 2, (1 : ℕ)) = 2 * r := by
  simp [Fintype.card_prod, Nat.mul_comm]

noncomputable def lemma77PositivePairCompositionShiftEquiv (r u : ℕ) :
    Lemma77PositivePairComposition r (2 * r + u) ≃
      Lemma77WeakPairComposition r u where
  toFun x := ⟨fun z => x.1 z - 1, by
    have hpred :
        (∑ z, (x.1 z - 1)) =
          (∑ z, x.1 z) - ∑ _ : Fin r × Fin 2, 1 := by
      apply Finset.sum_tsub_distrib
      intro z hz
      have hzpos := x.2.1 z
      omega
    rw [hpred, x.2.2, lemma77_sum_one_pairIndex]
    omega⟩
  invFun y := ⟨fun z => y.1 z + 1, fun z => by simp, by
    rw [Finset.sum_add_distrib, y.2, lemma77_sum_one_pairIndex]
    omega⟩
  left_inv x := by
    apply Subtype.ext
    funext z
    have hz := x.2.1 z
    change (x.1 z - 1) + 1 = x.1 z
    omega
  right_inv y := by
    apply Subtype.ext
    funext z
    change (y.1 z + 1) - 1 = y.1 z
    omega

noncomputable def lemma77WeakPairCompositionEquivSym (r u : ℕ) :
    Lemma77WeakPairComposition r u ≃ Sym (Fin r × Fin 2) u :=
  (Sym.equivNatSumOfFintype (Fin r × Fin 2) u).symm

noncomputable instance lemma77WeakPairCompositionFintype (r u : ℕ) :
    Fintype (Lemma77WeakPairComposition r u) :=
  Fintype.ofEquiv (Sym (Fin r × Fin 2) u)
    (lemma77WeakPairCompositionEquivSym r u).symm

theorem lemma77_card_weakPairComposition (r u : ℕ) :
    Fintype.card (Lemma77WeakPairComposition r u) =
      Nat.multichoose (2 * r) u := by
  calc
    Fintype.card (Lemma77WeakPairComposition r u) =
        Fintype.card (Sym (Fin r × Fin 2) u) :=
      Fintype.card_congr (lemma77WeakPairCompositionEquivSym r u)
    _ = Nat.multichoose (Fintype.card (Fin r × Fin 2)) u :=
      Sym.card_sym_eq_multichoose _ _
    _ = Nat.multichoose (2 * r) u := by
      simp [Fintype.card_prod, Nat.mul_comm]

theorem lemma77_card_terminalPairRefinementFiber_eq_multichoose (r u : ℕ) :
    Fintype.card
        (Lemma77TerminalPairRefinementFiber r (2 * r + u)) =
      Nat.multichoose (2 * r) u := by
  calc
    Fintype.card (Lemma77TerminalPairRefinementFiber r (2 * r + u)) =
        Fintype.card (Lemma77PositivePairComposition r (2 * r + u)) :=
      Fintype.card_congr
        (lemma77TerminalPairRefinementEquivPositivePairComposition
          r (2 * r + u))
    _ = Fintype.card (Lemma77WeakPairComposition r u) :=
      Fintype.card_congr (lemma77PositivePairCompositionShiftEquiv r u)
    _ = Nat.multichoose (2 * r) u :=
      lemma77_card_weakPairComposition r u

theorem lemma77HeightPotentialMass_eq_multichoose
    (start : TaoSection7RenewalPoint) (r u : ℕ) :
    lemma77HeightPotentialMass start ((r + 1 : ℕ) : ℤ)
        (2 * r + u + 3) =
      (Nat.multichoose (2 * r) u : ℝ) *
        (1 / 2 : ℝ) ^ (2 * r + u + 2) := by
  rw [lemma77HeightPotentialMass_eq_refinementFiberCard_mul_pow,
    lemma77_card_terminalPairRefinementFiber_eq_multichoose]

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
