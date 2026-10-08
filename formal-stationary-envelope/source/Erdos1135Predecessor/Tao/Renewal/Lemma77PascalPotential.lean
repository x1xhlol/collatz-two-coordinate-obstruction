/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.PascalPrime
import Erdos1135Predecessor.Tao.Renewal.Lemma77PotentialCore
import Erdos1135Predecessor.Tao.Renewal.SourceListBridge

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Lemma77

def lemma77SplitAfterThree : List ℕ → List (List ℕ)
  | [] => []
  | b :: bs =>
      if b = 3 then
        [] :: lemma77SplitAfterThree bs
      else
        match lemma77SplitAfterThree bs with
        | [] => []
        | pre :: pres => (b :: pre) :: pres

@[simp]
theorem lemma77SplitAfterThree_cons_three (bs : List ℕ) :
    lemma77SplitAfterThree (3 :: bs) =
      [] :: lemma77SplitAfterThree bs := by
  simp [lemma77SplitAfterThree]

theorem lemma77SplitAfterThree_cons_of_ne_three
    {b : ℕ} (hb : b ≠ 3) (bs : List ℕ) :
    lemma77SplitAfterThree (b :: bs) =
      match lemma77SplitAfterThree bs with
      | [] => []
      | pre :: pres => (b :: pre) :: pres := by
  simp [lemma77SplitAfterThree, hb]

theorem lemma77SplitAfterThree_append_three
    (pre tail : List ℕ) (hpre : taoSection7NoThree pre) :
    lemma77SplitAfterThree (pre ++ 3 :: tail) =
      pre :: lemma77SplitAfterThree tail := by
  induction pre with
  | nil =>
      simp
  | cons b pre ih =>
      have hb : b ≠ 3 := hpre b (by simp)
      have htail : taoSection7NoThree pre := by
        intro x hx
        exact hpre x (by simp [hx])
      simp [lemma77SplitAfterThree, hb, ih htail]

theorem lemma77SplitAfterThree_sourceBlocks
    (pres : List (List ℕ))
    (hno : ∀ pre ∈ pres, taoSection7NoThree pre) :
    lemma77SplitAfterThree (taoSection7SourceBlocks pres) = pres := by
  induction pres with
  | nil =>
      rfl
  | cons pre pres ih =>
      have hpre : taoSection7NoThree pre := hno pre (by simp)
      have htail : ∀ q ∈ pres, taoSection7NoThree q := by
        intro q hq
        exact hno q (by simp [hq])
      rw [taoSection7SourceBlocks,
        lemma77SplitAfterThree_append_three pre
          (taoSection7SourceBlocks pres) hpre,
        ih htail]

theorem lemma77SplitAfterThree_noThree
    (bs : List ℕ) :
    ∀ pre ∈ lemma77SplitAfterThree bs, taoSection7NoThree pre := by
  induction bs with
  | nil =>
      simp [lemma77SplitAfterThree]
  | cons b bs ih =>
      by_cases hb : b = 3
      · subst b
        intro pre hpre
        simp only [lemma77SplitAfterThree_cons_three, List.mem_cons] at hpre
        rcases hpre with rfl | hpre
        · simp [taoSection7NoThree]
        · exact ih pre hpre
      · rw [lemma77SplitAfterThree_cons_of_ne_three hb]
        cases hs : lemma77SplitAfterThree bs with
        | nil =>
            simp
        | cons first rest =>
            intro pre hpre
            simp only [List.mem_cons] at hpre
            rcases hpre with rfl | hpre
            · have hfirst : taoSection7NoThree first :=
                ih first (by simp [hs])
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact hb
              · exact hfirst x hx
            · exact ih pre (by simp [hs, hpre])

theorem lemma77SplitAfterThree_allGeTwo
    (bs : List ℕ) (h2 : taoSection7AllGeTwo bs) :
    ∀ pre ∈ lemma77SplitAfterThree bs, taoSection7AllGeTwo pre := by
  induction bs with
  | nil =>
      simp [lemma77SplitAfterThree]
  | cons b bs ih =>
      have hb2 : 2 ≤ b := h2 b (by simp)
      have htail : taoSection7AllGeTwo bs := by
        intro x hx
        exact h2 x (by simp [hx])
      by_cases hb3 : b = 3
      · subst b
        intro pre hpre
        simp only [lemma77SplitAfterThree_cons_three, List.mem_cons] at hpre
        rcases hpre with rfl | hpre
        · simp [taoSection7AllGeTwo]
        · exact ih htail pre hpre
      · rw [lemma77SplitAfterThree_cons_of_ne_three hb3]
        cases hs : lemma77SplitAfterThree bs with
        | nil =>
            simp
        | cons first rest =>
            intro pre hpre
            simp only [List.mem_cons] at hpre
            rcases hpre with rfl | hpre
            · have hfirst : taoSection7AllGeTwo first :=
                ih htail first (by simp [hs])
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact hb2
              · exact hfirst x hx
            · exact ih htail pre (by simp [hs, hpre])

theorem lemma77_sourceBlocks_splitAfterThree_of_getLast?_eq_three :
    ∀ bs : List ℕ,
      bs.getLast? = some 3 →
        taoSection7SourceBlocks (lemma77SplitAfterThree bs) = bs := by
  intro bs
  induction bs with
  | nil =>
      simp
  | cons b bs ih =>
      cases bs with
      | nil =>
          intro hlast
          simp at hlast
          subst b
          rfl
      | cons c cs =>
          intro hlast
          have htail : (c :: cs).getLast? = some 3 := by
            simpa using hlast
          have hrec := ih htail
          have hsplit_ne : lemma77SplitAfterThree (c :: cs) ≠ [] := by
            intro hzero
            rw [hzero] at hrec
            simp [taoSection7SourceBlocks] at hrec
          by_cases hb : b = 3
          · subst b
            rw [lemma77SplitAfterThree_cons_three]
            change
              3 :: taoSection7SourceBlocks
                  (lemma77SplitAfterThree (c :: cs)) =
                3 :: c :: cs
            rw [hrec]
          · rw [lemma77SplitAfterThree_cons_of_ne_three hb]
            cases hs : lemma77SplitAfterThree (c :: cs) with
            | nil =>
                exact (hsplit_ne hs).elim
            | cons pre pres =>
                have hrec' :
                    taoSection7SourceBlocks (pre :: pres) = c :: cs := by
                  simpa [hs] using hrec
                change
                  b :: (pre ++ 3 :: taoSection7SourceBlocks pres) =
                    b :: c :: cs
                rw [← taoSection7SourceBlocks, hrec']

theorem lemma77_sourceBlocks_allGeTwo
    (pres : List (List ℕ))
    (h2 : ∀ pre ∈ pres, taoSection7AllGeTwo pre) :
    taoSection7AllGeTwo (taoSection7SourceBlocks pres) := by
  induction pres with
  | nil =>
      simp [taoSection7SourceBlocks, taoSection7AllGeTwo]
  | cons pre pres ih =>
      have hpre : taoSection7AllGeTwo pre := h2 pre (by simp)
      have htail : ∀ q ∈ pres, taoSection7AllGeTwo q := by
        intro q hq
        exact h2 q (by simp [hq])
      intro x hx
      simp only [taoSection7SourceBlocks, List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact hpre x hx
      · norm_num
      · exact ih htail x hx

theorem lemma77_sourceBlocks_count_three
    (pres : List (List ℕ))
    (hno : ∀ pre ∈ pres, taoSection7NoThree pre) :
    (taoSection7SourceBlocks pres).count 3 = pres.length := by
  induction pres with
  | nil =>
      rfl
  | cons pre pres ih =>
      have hpre : taoSection7NoThree pre := hno pre (by simp)
      have htail : ∀ q ∈ pres, taoSection7NoThree q := by
        intro q hq
        exact hno q (by simp [hq])
      have hthree : 3 ∉ pre := by
        intro hmem
        exact hpre 3 hmem rfl
      have hcount : pre.count 3 = 0 :=
        List.count_eq_zero_of_not_mem hthree
      simp [taoSection7SourceBlocks, List.count_append, hcount, ih htail]

theorem lemma77SplitAfterThree_length_eq_count_three
    {bs : List ℕ} (hlast : bs.getLast? = some 3) :
    (lemma77SplitAfterThree bs).length = bs.count 3 := by
  have hno := lemma77SplitAfterThree_noThree bs
  have hflat := lemma77_sourceBlocks_splitAfterThree_of_getLast?_eq_three bs hlast
  calc
    (lemma77SplitAfterThree bs).length =
        (taoSection7SourceBlocks (lemma77SplitAfterThree bs)).count 3 := by
          symm
          exact lemma77_sourceBlocks_count_three
            (lemma77SplitAfterThree bs) hno
    _ = bs.count 3 := by rw [hflat]

theorem lemma77_sourceBlocks_cons_getLast?_eq_three
    (pre : List ℕ) (pres : List (List ℕ)) :
    (taoSection7SourceBlocks (pre :: pres)).getLast? = some 3 := by
  induction pres generalizing pre with
  | nil =>
      simp [taoSection7SourceBlocks]
  | cons next pres ih =>
      have hne : taoSection7SourceBlocks (next :: pres) ≠ [] := by
        simp [taoSection7SourceBlocks]
      rw [show taoSection7SourceBlocks (pre :: next :: pres) =
          (pre ++ [3]) ++ taoSection7SourceBlocks (next :: pres) by
        simp [taoSection7SourceBlocks, List.append_assoc]]
      rw [List.getLast?_append_of_ne_nil _ hne]
      exact ih next

theorem lemma77_sourceBlocks_getLast?_eq_three_of_ne_nil
    (pres : List (List ℕ)) (hne : pres ≠ []) :
    (taoSection7SourceBlocks pres).getLast? = some 3 := by
  cases pres with
  | nil => exact (hne rfl).elim
  | cons pre pres =>
      exact lemma77_sourceBlocks_cons_getLast?_eq_three pre pres

noncomputable def lemma77RawPascalWordMass (bs : List ℕ) : ℝ :=
  (bs.map pascalGeom2PairMass).prod

@[simp]
theorem lemma77RawPascalWordMass_nil :
    lemma77RawPascalWordMass [] = 1 := by
  simp [lemma77RawPascalWordMass]

theorem lemma77RawPascalWordMass_nonneg (bs : List ℕ) :
    0 ≤ lemma77RawPascalWordMass bs := by
  unfold lemma77RawPascalWordMass
  apply List.prod_nonneg
  intro x hx
  rcases List.mem_map.mp hx with ⟨b, _hb, rfl⟩
  unfold pascalGeom2PairMass
  apply Finset.sum_nonneg
  intro a ha
  positivity

theorem lemma77RawPascalWordMass_append (xs ys : List ℕ) :
    lemma77RawPascalWordMass (xs ++ ys) =
      lemma77RawPascalWordMass xs * lemma77RawPascalWordMass ys := by
  simp [lemma77RawPascalWordMass, List.map_append]

theorem lemma77_finitePreHitBlockMass_prod_eq_rawPascalWordMass
    (pres : List (List ℕ))
    (h2 : ∀ pre ∈ pres, taoSection7AllGeTwo pre)
    (hno : ∀ pre ∈ pres, taoSection7NoThree pre) :
    (pres.map taoSection7FinitePreHitBlockPMFMass).prod =
      lemma77RawPascalWordMass (taoSection7SourceBlocks pres) := by
  induction pres with
  | nil =>
      simp [lemma77RawPascalWordMass, taoSection7SourceBlocks]
  | cons pre pres ih =>
      have h2pre : taoSection7AllGeTwo pre := h2 pre (by simp)
      have hnopre : taoSection7NoThree pre := hno pre (by simp)
      have h2tail : ∀ q ∈ pres, taoSection7AllGeTwo q := by
        intro q hq
        exact h2 q (by simp [hq])
      have hnotail : ∀ q ∈ pres, taoSection7NoThree q := by
        intro q hq
        exact hno q (by simp [hq])
      rw [List.map_cons, List.prod_cons,
        taoSection7FinitePreHitBlockPMFMass_eq_unconditioned h2pre hnopre,
        ih h2tail hnotail]
      simp [lemma77RawPascalWordMass, taoSection7SourceBlocks,
        taoSection7UnconditionedPreHitPathMass, List.map_append, mul_assoc]

def lemma77SourceHistory (pres : List (List ℕ)) : List (ℕ × List ℕ) :=
  pres.map fun pre => (pre.length, pre)

@[simp]
theorem lemma77SourceHistory_length (pres : List (List ℕ)) :
    (lemma77SourceHistory pres).length = pres.length := by
  simp [lemma77SourceHistory]

@[simp]
theorem lemma77SourceHistory_map_snd (pres : List (List ℕ)) :
    (lemma77SourceHistory pres).map Prod.snd = pres := by
  simp [lemma77SourceHistory, Function.comp_def]

theorem lemma77SourceHistory_map_holdPoint (pres : List (List ℕ)) :
    (lemma77SourceHistory pres).map
        (fun x => taoSection7HoldPointOfPrefix x.1 x.2) =
      taoSection7HoldIncrementsOfPrefixes pres := by
  induction pres with
  | nil => rfl
  | cons pre pres ih =>
      simp only [lemma77SourceHistory, List.map_cons,
        taoSection7HoldIncrementsOfPrefixes]
      congr 1
      ext
      · apply Subtype.ext
        simp [taoSection7HoldPointOfPrefix,
          taoSection7HoldIncrementOfPrefix, taoSection7ShiftIndex]
        omega
      · simp [taoSection7HoldPointOfPrefix,
          taoSection7HoldIncrementOfPrefix, taoSection7HoldTerminalSum]

theorem lemma77HoldPrefixHorizontalDelta_sourceHistory
    (pres : List (List ℕ)) :
    lemma77HoldPrefixHorizontalDelta pres.length
        (taoSection7HoldIncrementsOfPrefixes pres) =
      (taoSection7SourceBlocks pres).length := by
  induction pres with
  | nil => rfl
  | cons pre pres ih =>
      have ih' :
          lemma77HoldPrefixHorizontalDelta pres.length
              (pres.map taoSection7HoldIncrementOfPrefix) =
            (taoSection7SourceBlocks pres).length := by
        simpa [taoSection7HoldIncrementsOfPrefixes] using ih
      simp only [List.length_cons, taoSection7HoldIncrementsOfPrefixes,
        List.map_cons, lemma77HoldPrefixHorizontalDelta,
        taoSection7SourceBlocks, List.length_append]
      rw [ih']
      simp [taoSection7HoldIncrementOfPrefix, taoSection7ShiftIndex]
      omega

theorem lemma77HoldPrefixVerticalIncrement_sourceHistory
    (start : TaoSection7RenewalPoint) :
    ∀ pres : List (List ℕ),
      lemma77HoldPrefixVerticalIncrement start pres.length
          (taoSection7HoldIncrementsOfPrefixes pres) =
        ((taoSection7SourceBlocks pres).sum : ℤ) := by
  intro pres
  induction pres generalizing start with
  | nil =>
      simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement,
        taoSection7SourceBlocks]
  | cons pre pres ih =>
      have htail := ih
        (start + taoSection7HoldIncrementOfPrefix pre)
      simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement,
        taoSection7HoldIncrementsOfPrefixes, taoSection7SourceBlocks,
        taoSection7HoldIncrementOfPrefix] at htail ⊢
      omega

theorem lemma77HoldSourcePrefixPMF_length_toReal_eq_blockMass
    (pre : List ℕ) (h2 : taoSection7AllGeTwo pre) :
    (taoSection7HoldSourcePrefixPMF (pre.length, pre)).toReal =
      taoSection7FinitePreHitBlockPMFMass pre := by
  rw [taoSection7HoldSourcePrefixPMF_apply_toReal,
    taoSection7PascalPrimeSourceListPMF_apply_length_toReal_eq_sourcePathMass,
    taoSection7FinitePreHitBlockPMFMass,
    taoSection7PascalPrimePMFSourcePathMass_eq_source h2]

theorem lemma77HoldSourcePrefixListPMF_sourceHistory_toReal
    (pres : List (List ℕ))
    (h2 : ∀ pre ∈ pres, taoSection7AllGeTwo pre) :
    (taoSection7HoldSourcePrefixListPMF pres.length
        (lemma77SourceHistory pres)).toReal =
      (pres.map taoSection7FinitePreHitBlockPMFMass).prod := by
  induction pres with
  | nil =>
      simp [lemma77SourceHistory, taoSection7HoldSourcePrefixListPMF]
  | cons pre pres ih =>
      have hpre : taoSection7AllGeTwo pre := h2 pre (by simp)
      have htail : ∀ q ∈ pres, taoSection7AllGeTwo q := by
        intro q hq
        exact h2 q (by simp [hq])
      rw [List.length_cons]
      change
        (taoSection7HoldSourcePrefixListPMF (pres.length + 1)
          ((pre.length, pre) :: lemma77SourceHistory pres)).toReal = _
      rw [taoSection7HoldSourcePrefixListPMF_succ_apply_cons,
        ENNReal.toReal_mul,
        lemma77HoldSourcePrefixPMF_length_toReal_eq_blockMass pre hpre,
        ih htail]
      rfl

theorem lemma77HoldSourcePrefixListPMF_sourceHistory_toReal_eq_rawWordMass
    (pres : List (List ℕ))
    (h2 : ∀ pre ∈ pres, taoSection7AllGeTwo pre)
    (hno : ∀ pre ∈ pres, taoSection7NoThree pre) :
    (taoSection7HoldSourcePrefixListPMF pres.length
        (lemma77SourceHistory pres)).toReal =
      lemma77RawPascalWordMass (taoSection7SourceBlocks pres) := by
  rw [lemma77HoldSourcePrefixListPMF_sourceHistory_toReal pres h2,
    lemma77_finitePreHitBlockMass_prod_eq_rawPascalWordMass pres h2 hno]

theorem lemma77HoldSourcePrefixPMF_toReal_ne_zero_support
    {m : ℕ} {pre : List ℕ}
    (h : (taoSection7HoldSourcePrefixPMF (m, pre)).toReal ≠ 0) :
    m = pre.length ∧
      taoSection7AllGeTwo pre ∧ taoSection7NoThree pre := by
  have hinner :
      (taoSection7PascalPrimeSourceListPMF m pre).toReal ≠ 0 := by
    intro hzero
    rw [taoSection7HoldSourcePrefixPMF_apply_toReal, hzero, mul_zero] at h
    exact h rfl
  have hpmf : taoSection7PascalPrimeSourceListPMF m pre ≠ 0 := by
    intro hzero
    rw [hzero] at hinner
    exact hinner rfl
  have hlen : m = pre.length := by
    by_contra hne
    exact hpmf (taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_length_ne
      m pre (fun h => hne h.symm))
  exact ⟨hlen,
    taoSection7PascalPrimeSourceListPMF_apply_ne_zero_allGeTwo hpmf,
    taoSection7PascalPrimeSourceListPMF_apply_ne_zero_noThree hpmf⟩

theorem lemma77HoldSourcePrefixListPMF_toReal_ne_zero_support
    {n : ℕ} {xs : List (ℕ × List ℕ)}
    (h : (taoSection7HoldSourcePrefixListPMF n xs).toReal ≠ 0) :
    xs.length = n ∧
      ∀ x ∈ xs,
        x.1 = x.2.length ∧
          taoSection7AllGeTwo x.2 ∧ taoSection7NoThree x.2 := by
  have hlen : xs.length = n := by
    by_contra hne
    have hzero := taoSection7HoldSourcePrefixListPMF_apply_eq_zero_of_length_ne
      n xs hne
    rw [hzero] at h
    exact h rfl
  refine ⟨hlen, ?_⟩
  induction n generalizing xs with
  | zero =>
      have hnil : xs = [] := by simpa using hlen
      subst xs
      simp
  | succ n ih =>
      cases xs with
      | nil =>
          simp at hlen
      | cons x xs =>
          have hprod :
              (taoSection7HoldSourcePrefixPMF x).toReal *
                  (taoSection7HoldSourcePrefixListPMF n xs).toReal ≠ 0 := by
            simpa [taoSection7HoldSourcePrefixListPMF_succ_apply_cons,
              ENNReal.toReal_mul] using h
          have hhead : (taoSection7HoldSourcePrefixPMF x).toReal ≠ 0 := by
            intro hzero
            exact hprod (by rw [hzero, zero_mul])
          have htail :
              (taoSection7HoldSourcePrefixListPMF n xs).toReal ≠ 0 := by
            intro hzero
            exact hprod (by rw [hzero, mul_zero])
          have hlenTail : xs.length = n := by simpa using hlen
          have hsTail :=
            ih htail hlenTail
          intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact lemma77HoldSourcePrefixPMF_toReal_ne_zero_support hhead
          · exact hsTail y hy

theorem lemma77_eq_sourceHistory_map_snd_of_fst_eq_length
    (xs : List (ℕ × List ℕ))
    (hcanonical : ∀ x ∈ xs, x.1 = x.2.length) :
    xs = lemma77SourceHistory (xs.map Prod.snd) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := hcanonical x (by simp)
      have htail : ∀ y ∈ xs, y.1 = y.2.length := by
        intro y hy
        exact hcanonical y (by simp [hy])
      rcases x with ⟨m, pre⟩
      change
        (m, pre) :: xs =
          (pre.length, pre) :: lemma77SourceHistory (xs.map Prod.snd)
      rw [← ih htail]
      simpa using hx

theorem lemma77SourceHistory_injective :
    Function.Injective lemma77SourceHistory := by
  intro pres qs h
  have hsnd := congrArg (List.map Prod.snd) h
  simpa using hsnd

theorem lemma77HoldSourcePrefixListPMF_eq_sourceHistory_of_toReal_ne_zero
    {n : ℕ} {xs : List (ℕ × List ℕ)}
    (h : (taoSection7HoldSourcePrefixListPMF n xs).toReal ≠ 0) :
    xs = lemma77SourceHistory (xs.map Prod.snd) := by
  exact lemma77_eq_sourceHistory_map_snd_of_fst_eq_length xs
    (fun x hx =>
      (lemma77HoldSourcePrefixListPMF_toReal_ne_zero_support h).2 x hx |>.1)

def Lemma77SupportedSourceHistoryFiber (n j s : ℕ) :=
  {pres : List (List ℕ) //
    pres.length = n ∧
      (∀ pre ∈ pres,
        taoSection7AllGeTwo pre ∧ taoSection7NoThree pre) ∧
      (taoSection7SourceBlocks pres).length = j ∧
      (taoSection7SourceBlocks pres).sum = s}

def Lemma77RawTerminalEpochFiber (n j s : ℕ) :=
  {bs : List ℕ //
    bs.length = j ∧ bs.sum = s ∧
      taoSection7AllGeTwo bs ∧ bs.getLast? = some 3 ∧
      (lemma77SplitAfterThree bs).length = n}

def Lemma77RawTerminalFiber (j s : ℕ) :=
  {bs : List ℕ //
    bs.length = j ∧ bs.sum = s ∧
      taoSection7AllGeTwo bs ∧ bs.getLast? = some 3}

def lemma77RawTerminalEpochSigmaToFiber (j s : ℕ) :
    ((n : Fin j) × Lemma77RawTerminalEpochFiber (n.1 + 1) j s) →
      Lemma77RawTerminalFiber j s := fun x =>
  ⟨x.2.1, ⟨x.2.2.1, ⟨x.2.2.2.1,
    ⟨x.2.2.2.2.1, x.2.2.2.2.2.1⟩⟩⟩⟩

theorem lemma77RawTerminalEpochSigmaToFiber_bijective (j s : ℕ) :
    Function.Bijective (lemma77RawTerminalEpochSigmaToFiber j s) := by
  constructor
  · rintro ⟨n, x⟩ ⟨m, y⟩ h
    have hxy : x.1 = y.1 := congrArg Subtype.val h
    have hn : n = m := by
      apply Fin.ext
      have hx := x.2.2.2.2.2
      have hy := y.2.2.2.2.2
      rw [hxy] at hx
      omega
    subst m
    have hsub : x = y := Subtype.ext hxy
    subst y
    rfl
  · intro bs
    let k := (lemma77SplitAfterThree bs.1).length
    have hmem : 3 ∈ bs.1 := by
      apply List.mem_of_mem_getLast?
      simp [bs.2.2.2.2]
    have hkpos : 0 < k := by
      rw [show k = bs.1.count 3 by
        exact lemma77SplitAfterThree_length_eq_count_three bs.2.2.2.2]
      exact List.count_pos_iff.mpr hmem
    have hkle : k ≤ j := by
      rw [show k = bs.1.count 3 by
        exact lemma77SplitAfterThree_length_eq_count_three bs.2.2.2.2]
      simpa [bs.2.1] using
        (List.count_le_length (a := 3) (l := bs.1))
    let n : Fin j := ⟨k - 1, by omega⟩
    let word : Lemma77RawTerminalEpochFiber (n.1 + 1) j s :=
      ⟨bs.1, ⟨bs.2.1, ⟨bs.2.2.1, ⟨bs.2.2.2.1,
        ⟨bs.2.2.2.2, by
          change k = k - 1 + 1
          omega⟩⟩⟩⟩⟩
    refine ⟨⟨n, word⟩, ?_⟩
    apply Subtype.ext
    rfl

noncomputable def lemma77RawTerminalEpochSigmaEquiv (j s : ℕ) :
    ((n : Fin j) × Lemma77RawTerminalEpochFiber (n.1 + 1) j s) ≃
      Lemma77RawTerminalFiber j s :=
  Equiv.ofBijective (lemma77RawTerminalEpochSigmaToFiber j s)
    (lemma77RawTerminalEpochSigmaToFiber_bijective j s)

def lemma77PositiveSourceRawHistoryEquiv (n j s : ℕ) :
    Lemma77SupportedSourceHistoryFiber (n + 1) j s ≃
      Lemma77RawTerminalEpochFiber (n + 1) j s where
  toFun pres := by
    let blocks := pres.1
    have hlen := pres.2.1
    have hsupp := pres.2.2.1
    have hj := pres.2.2.2.1
    have hs := pres.2.2.2.2
    have h2 : ∀ pre ∈ blocks, taoSection7AllGeTwo pre :=
      fun pre hp => (hsupp pre hp).1
    have hno : ∀ pre ∈ blocks, taoSection7NoThree pre :=
      fun pre hp => (hsupp pre hp).2
    have hlenBlocks : blocks.length = n + 1 := by
      simpa [blocks] using hlen
    have hne : blocks ≠ [] := by
      intro hnil
      have hzero : blocks.length = 0 := by simp [hnil]
      omega
    refine ⟨taoSection7SourceBlocks blocks, hj, hs,
      lemma77_sourceBlocks_allGeTwo blocks h2, ?_, ?_⟩
    · exact lemma77_sourceBlocks_getLast?_eq_three_of_ne_nil blocks hne
    · rw [lemma77SplitAfterThree_sourceBlocks blocks hno]
      exact hlen
  invFun bs := by
    let blocks := lemma77SplitAfterThree bs.1
    have hj := bs.2.1
    have hs := bs.2.2.1
    have h2 := bs.2.2.2.1
    have hlast := bs.2.2.2.2.1
    have hlen := bs.2.2.2.2.2
    have hflat :=
      lemma77_sourceBlocks_splitAfterThree_of_getLast?_eq_three bs.1 hlast
    refine ⟨blocks, hlen, ?_, ?_, ?_⟩
    · intro pre hp
      exact ⟨lemma77SplitAfterThree_allGeTwo bs.1 h2 pre hp,
        lemma77SplitAfterThree_noThree bs.1 pre hp⟩
    · rw [hflat]
      exact hj
    · rw [hflat]
      exact hs
  left_inv pres := by
    apply Subtype.ext
    exact lemma77SplitAfterThree_sourceBlocks pres.1
      (fun pre hp => (pres.2.2.1 pre hp).2)
  right_inv bs := by
    apply Subtype.ext
    exact lemma77_sourceBlocks_splitAfterThree_of_getLast?_eq_three
      bs.1 bs.2.2.2.2.1

def lemma77HoldSourcePrefixSignedEndpointEvent
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    Set (List (ℕ × List ℕ)) :=
  {xs |
    xs.map (fun x => taoSection7HoldPointOfPrefix x.1 x.2) ∈
      lemma77HoldPrefixSignedEndpointEvent start n j ell}

theorem lemma77SourceHistory_mem_signedEndpointEvent_iff
    (start : TaoSection7RenewalPoint) (pres : List (List ℕ))
    (j s : ℕ) :
    lemma77SourceHistory pres ∈
        lemma77HoldSourcePrefixSignedEndpointEvent
          start pres.length (j : ℤ) (s : ℤ) ↔
      (taoSection7SourceBlocks pres).length = j ∧
        (taoSection7SourceBlocks pres).sum = s := by
  change
    (lemma77SourceHistory pres).map
        (fun x => taoSection7HoldPointOfPrefix x.1 x.2) ∈
      lemma77HoldPrefixSignedEndpointEvent
        start pres.length (j : ℤ) (s : ℤ) ↔ _
  rw [lemma77SourceHistory_map_holdPoint]
  change
    (lemma77HoldPrefixIncrement start pres.length
        (taoSection7HoldIncrementsOfPrefixes pres) : ℤ) = (j : ℤ) ∧
      lemma77HoldPrefixVerticalIncrement start pres.length
        (taoSection7HoldIncrementsOfPrefixes pres) = (s : ℤ) ↔ _
  rw [lemma77HoldPrefixIncrement_eq_horizontalDelta,
    lemma77HoldPrefixHorizontalDelta_sourceHistory,
    lemma77HoldPrefixVerticalIncrement_sourceHistory]
  constructor
  · intro h
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · intro h
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

def lemma77HoldSourcePrefixSignedEndpointMassSummand
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ)
    (xs : List (ℕ × List ℕ)) : ℝ := by
  classical
  exact
    if xs ∈ lemma77HoldSourcePrefixSignedEndpointEvent start n j ell then
      (taoSection7HoldSourcePrefixListPMF n xs).toReal
    else
      0

theorem lemma77HoldPrefixSignedEndpointMass_eq_sourcePrefixEventMass
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    lemma77HoldPrefixSignedEndpointMass start n j ell =
      ((taoSection7HoldSourcePrefixListPMF n).toOuterMeasure
        (lemma77HoldSourcePrefixSignedEndpointEvent start n j ell)).toReal := by
  rw [lemma77HoldPrefixSignedEndpointMass,
    ← taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq n,
    PMF.toOuterMeasure_map_apply]
  rfl

theorem lemma77HoldPrefixSignedEndpointMass_eq_tsum_sourcePrefix
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    lemma77HoldPrefixSignedEndpointMass start n j ell =
      ∑' xs : List (ℕ × List ℕ),
        lemma77HoldSourcePrefixSignedEndpointMassSummand
          start n j ell xs := by
  rw [lemma77HoldPrefixSignedEndpointMass_eq_sourcePrefixEventMass,
    pmf_toOuterMeasure_toReal_eq_tsum_indicator]
  apply tsum_congr
  intro xs
  by_cases hmem :
      xs ∈ lemma77HoldSourcePrefixSignedEndpointEvent start n j ell
  · simp [lemma77HoldSourcePrefixSignedEndpointMassSummand,
      Set.indicator, hmem]
  · simp [lemma77HoldSourcePrefixSignedEndpointMassSummand,
      Set.indicator, hmem]

theorem lemma77SourcePrefixSummand_support_subset_sourceHistory_range
    (start : TaoSection7RenewalPoint) (n j s : ℕ) :
    Function.support
        (lemma77HoldSourcePrefixSignedEndpointMassSummand
          start n (j : ℤ) (s : ℤ)) ⊆
      Set.range lemma77SourceHistory := by
  intro xs hxs
  by_cases hmem :
      xs ∈ lemma77HoldSourcePrefixSignedEndpointEvent
        start n (j : ℤ) (s : ℤ)
  · have hmass :
        (taoSection7HoldSourcePrefixListPMF n xs).toReal ≠ 0 := by
      simpa [lemma77HoldSourcePrefixSignedEndpointMassSummand, hmem] using hxs
    refine ⟨xs.map Prod.snd, ?_⟩
    exact (lemma77HoldSourcePrefixListPMF_eq_sourceHistory_of_toReal_ne_zero
      hmass).symm
  · exfalso
    exact hxs (by simp [lemma77HoldSourcePrefixSignedEndpointMassSummand, hmem])

theorem lemma77CanonicalSourceSummand_support_subset_fiber
    (start : TaoSection7RenewalPoint) (n j s : ℕ) :
    Function.support
        (fun pres : List (List ℕ) =>
          lemma77HoldSourcePrefixSignedEndpointMassSummand
            start n (j : ℤ) (s : ℤ) (lemma77SourceHistory pres)) ⊆
      {pres |
        pres.length = n ∧
          (∀ pre ∈ pres,
            taoSection7AllGeTwo pre ∧ taoSection7NoThree pre) ∧
          (taoSection7SourceBlocks pres).length = j ∧
          (taoSection7SourceBlocks pres).sum = s} := by
  intro pres hpres
  by_cases hmem :
      lemma77SourceHistory pres ∈
        lemma77HoldSourcePrefixSignedEndpointEvent
          start n (j : ℤ) (s : ℤ)
  · have hmass :
        (taoSection7HoldSourcePrefixListPMF n
          (lemma77SourceHistory pres)).toReal ≠ 0 := by
      simpa [lemma77HoldSourcePrefixSignedEndpointMassSummand, hmem] using hpres
    have hsupp :=
      lemma77HoldSourcePrefixListPMF_toReal_ne_zero_support hmass
    have hlen : pres.length = n := by
      simpa using hsupp.1
    have hblocks :
        ∀ pre ∈ pres,
          taoSection7AllGeTwo pre ∧ taoSection7NoThree pre := by
      intro pre hp
      have hxmem : (pre.length, pre) ∈ lemma77SourceHistory pres := by
        simp [lemma77SourceHistory, hp]
      exact (hsupp.2 (pre.length, pre) hxmem).2
    have hmem' :
        lemma77SourceHistory pres ∈
          lemma77HoldSourcePrefixSignedEndpointEvent
            start pres.length (j : ℤ) (s : ℤ) := by
      simpa [hlen] using hmem
    have hcoords :=
      (lemma77SourceHistory_mem_signedEndpointEvent_iff start pres j s).1 hmem'
    exact ⟨hlen, hblocks, hcoords⟩
  · exfalso
    exact hpres (by
      simp [lemma77HoldSourcePrefixSignedEndpointMassSummand, hmem])

theorem lemma77CanonicalSourceSummand_eq_rawWordMass
    (start : TaoSection7RenewalPoint) (n j s : ℕ)
    (pres : Lemma77SupportedSourceHistoryFiber n j s) :
    lemma77HoldSourcePrefixSignedEndpointMassSummand
        start n (j : ℤ) (s : ℤ) (lemma77SourceHistory pres.1) =
      lemma77RawPascalWordMass (taoSection7SourceBlocks pres.1) := by
  have hlen := pres.2.1
  have hsupp := pres.2.2.1
  have hcoords :
      (taoSection7SourceBlocks pres.1).length = j ∧
        (taoSection7SourceBlocks pres.1).sum = s :=
    ⟨pres.2.2.2.1, pres.2.2.2.2⟩
  have hmem' :=
    (lemma77SourceHistory_mem_signedEndpointEvent_iff
      start pres.1 j s).2 hcoords
  have hmem :
      lemma77SourceHistory pres.1 ∈
        lemma77HoldSourcePrefixSignedEndpointEvent
          start n (j : ℤ) (s : ℤ) := by
    simpa [hlen] using hmem'
  rw [lemma77HoldSourcePrefixSignedEndpointMassSummand, if_pos hmem]
  calc
    (taoSection7HoldSourcePrefixListPMF n
        (lemma77SourceHistory pres.1)).toReal =
        (taoSection7HoldSourcePrefixListPMF pres.1.length
          (lemma77SourceHistory pres.1)).toReal := by rw [hlen]
    _ = lemma77RawPascalWordMass (taoSection7SourceBlocks pres.1) :=
      lemma77HoldSourcePrefixListPMF_sourceHistory_toReal_eq_rawWordMass
        pres.1 (fun pre hp => (hsupp pre hp).1)
          (fun pre hp => (hsupp pre hp).2)

theorem lemma77HoldPrefixSignedEndpointMass_eq_rawTerminalEpochMass
    (start : TaoSection7RenewalPoint) (n j s : ℕ) :
    lemma77HoldPrefixSignedEndpointMass start (n + 1) (j : ℤ) (s : ℤ) =
      ∑' bs : Lemma77RawTerminalEpochFiber (n + 1) j s,
        lemma77RawPascalWordMass bs.1 := by
  let f : List (ℕ × List ℕ) → ℝ :=
    lemma77HoldSourcePrefixSignedEndpointMassSummand
      start (n + 1) (j : ℤ) (s : ℤ)
  let g : List (List ℕ) → ℝ := fun pres => f (lemma77SourceHistory pres)
  calc
    lemma77HoldPrefixSignedEndpointMass start (n + 1) (j : ℤ) (s : ℤ) =
        ∑' xs : List (ℕ × List ℕ), f xs := by
          exact lemma77HoldPrefixSignedEndpointMass_eq_tsum_sourcePrefix
            start (n + 1) (j : ℤ) (s : ℤ)
    _ = ∑' pres : List (List ℕ), g pres := by
          symm
          exact lemma77SourceHistory_injective.tsum_eq
            (lemma77SourcePrefixSummand_support_subset_sourceHistory_range
              start (n + 1) j s)
    _ = ∑' pres : Lemma77SupportedSourceHistoryFiber (n + 1) j s,
          g pres.1 := by
          symm
          exact tsum_subtype_eq_of_support_subset
            (lemma77CanonicalSourceSummand_support_subset_fiber
              start (n + 1) j s)
    _ = ∑' pres : Lemma77SupportedSourceHistoryFiber (n + 1) j s,
          lemma77RawPascalWordMass
            (taoSection7SourceBlocks pres.1) := by
          apply tsum_congr
          intro pres
          exact lemma77CanonicalSourceSummand_eq_rawWordMass
            start (n + 1) j s pres
    _ = ∑' bs : Lemma77RawTerminalEpochFiber (n + 1) j s,
          lemma77RawPascalWordMass bs.1 := by
          simpa using
            (lemma77PositiveSourceRawHistoryEquiv n j s).tsum_eq
              (fun bs : Lemma77RawTerminalEpochFiber (n + 1) j s =>
                lemma77RawPascalWordMass bs.1)

theorem summable_lemma77RawPascalWordMass_rawTerminalEpochFiber
    (start : TaoSection7RenewalPoint) (n j s : ℕ) :
    Summable (fun bs : Lemma77RawTerminalEpochFiber (n + 1) j s =>
      lemma77RawPascalWordMass bs.1) := by
  let f : List (ℕ × List ℕ) → ℝ :=
    lemma77HoldSourcePrefixSignedEndpointMassSummand
      start (n + 1) (j : ℤ) (s : ℤ)
  have hpmf : Summable (fun xs : List (ℕ × List ℕ) =>
      (taoSection7HoldSourcePrefixListPMF (n + 1) xs).toReal) :=
    ENNReal.summable_toReal
      (taoSection7HoldSourcePrefixListPMF (n + 1)).tsum_coe_ne_top
  have hf : Summable f := by
    have hind := hpmf.indicator
      (lemma77HoldSourcePrefixSignedEndpointEvent
        start (n + 1) (j : ℤ) (s : ℤ))
    refine hind.congr ?_
    intro xs
    by_cases hmem : xs ∈ lemma77HoldSourcePrefixSignedEndpointEvent
        start (n + 1) (j : ℤ) (s : ℤ)
    · simp [f, lemma77HoldSourcePrefixSignedEndpointMassSummand,
        Set.indicator, hmem]
    · simp [f, lemma77HoldSourcePrefixSignedEndpointMassSummand,
        Set.indicator, hmem]
  have hg : Summable (fun pres : List (List ℕ) =>
      f (lemma77SourceHistory pres)) := by
    have hiff := Function.Injective.summable_iff
      lemma77SourceHistory_injective
      (fun xs hnot => by
        by_contra hne
        exact hnot
          (lemma77SourcePrefixSummand_support_subset_sourceHistory_range
            start (n + 1) j s hne))
    exact hiff.mpr hf
  have hsub := hg.subtype
    {pres : List (List ℕ) |
      pres.length = n + 1 ∧
        (∀ pre ∈ pres,
          taoSection7AllGeTwo pre ∧ taoSection7NoThree pre) ∧
        (taoSection7SourceBlocks pres).length = j ∧
        (taoSection7SourceBlocks pres).sum = s}
  have hsourceraw : Summable
      (fun pres : Lemma77SupportedSourceHistoryFiber (n + 1) j s =>
        lemma77RawPascalWordMass (taoSection7SourceBlocks pres.1)) := by
    refine hsub.congr ?_
    intro pres
    exact lemma77CanonicalSourceSummand_eq_rawWordMass
      start (n + 1) j s pres
  apply (lemma77PositiveSourceRawHistoryEquiv n j s).summable_iff.mp
  simpa [Function.comp_apply] using hsourceraw

theorem lemma77_sum_rawTerminalEpochMass_eq_rawTerminalMass
    (start : TaoSection7RenewalPoint) (j s : ℕ) :
    (∑ n ∈ Finset.range j,
      ∑' bs : Lemma77RawTerminalEpochFiber (n + 1) j s,
        lemma77RawPascalWordMass bs.1) =
      ∑' bs : Lemma77RawTerminalFiber j s,
        lemma77RawPascalWordMass bs.1 := by
  let F : ((n : Fin j) ×
      Lemma77RawTerminalEpochFiber (n.1 + 1) j s) → ℝ :=
    fun x => lemma77RawPascalWordMass x.2.1
  have hF : Summable F := by
    change Summable (fun x : ((n : Fin j) ×
      Lemma77RawTerminalEpochFiber (n.1 + 1) j s) =>
        lemma77RawPascalWordMass x.2.1)
    rw [summable_sigma_of_nonneg (fun x : ((n : Fin j) ×
      Lemma77RawTerminalEpochFiber (n.1 + 1) j s) =>
        lemma77RawPascalWordMass_nonneg x.2.1)]
    constructor
    · intro n
      exact summable_lemma77RawPascalWordMass_rawTerminalEpochFiber
        start n.1 j s
    · apply summable_of_hasFiniteSupport
      exact Set.toFinite _
  calc
    (∑ n ∈ Finset.range j,
        ∑' bs : Lemma77RawTerminalEpochFiber (n + 1) j s,
          lemma77RawPascalWordMass bs.1) =
        ∑ n : Fin j,
          ∑' bs : Lemma77RawTerminalEpochFiber (n.1 + 1) j s,
            lemma77RawPascalWordMass bs.1 := by
              rw [Finset.sum_range]
    _ = ∑' n : Fin j,
          ∑' bs : Lemma77RawTerminalEpochFiber (n.1 + 1) j s,
            lemma77RawPascalWordMass bs.1 := by
              rw [tsum_fintype]
    _ = ∑' x : ((n : Fin j) ×
          Lemma77RawTerminalEpochFiber (n.1 + 1) j s), F x := by
            exact hF.tsum_sigma.symm
    _ = ∑' bs : Lemma77RawTerminalFiber j s,
          lemma77RawPascalWordMass bs.1 := by
            simpa [F, lemma77RawTerminalEpochSigmaEquiv,
              lemma77RawTerminalEpochSigmaToFiber] using
              (lemma77RawTerminalEpochSigmaEquiv j s).tsum_eq
                (fun bs : Lemma77RawTerminalFiber j s =>
                  lemma77RawPascalWordMass bs.1)

@[simp]
theorem lemma77HoldPrefixSignedEndpointMass_zero
    (start : TaoSection7RenewalPoint) (j s : ℤ) :
    lemma77HoldPrefixSignedEndpointMass start 0 j s =
      if j = 0 ∧ s = 0 then 1 else 0 := by
  by_cases h : j = 0 ∧ s = 0
  · rcases h with ⟨rfl, rfl⟩
    simp [lemma77HoldPrefixSignedEndpointMass,
      lemma77HoldPrefixSignedEndpointEvent,
      taoSection7HoldListPMF,
      lemma77HoldPrefixIncrement,
      lemma77HoldPrefixVerticalIncrement,
      prefixIncrement, prefixVerticalIncrement]
  · have h' : ¬(0 = j ∧ 0 = s) := by
      intro hz
      exact h ⟨hz.1.symm, hz.2.symm⟩
    simp [lemma77HoldPrefixSignedEndpointMass,
      lemma77HoldPrefixSignedEndpointEvent,
      taoSection7HoldListPMF,
      lemma77HoldPrefixIncrement,
      lemma77HoldPrefixVerticalIncrement,
      prefixIncrement, prefixVerticalIncrement, h, h']

@[simp]
theorem lemma77HoldPrefixSignedEndpointMass_zero_nat
    (start : TaoSection7RenewalPoint) (j s : ℕ) :
    lemma77HoldPrefixSignedEndpointMass start 0 (j : ℤ) (s : ℤ) =
      if j = 0 ∧ s = 0 then 1 else 0 := by
  rw [lemma77HoldPrefixSignedEndpointMass_zero]
  by_cases h : j = 0 ∧ s = 0
  · rcases h with ⟨rfl, rfl⟩
    simp
  · simp [h]

theorem lemma77HoldPrefixSignedEndpointMass_eq_zero_of_nat_j_lt_n
    (start : TaoSection7RenewalPoint) {n j s : ℕ} (hjn : j < n) :
    lemma77HoldPrefixSignedEndpointMass start n (j : ℤ) (s : ℤ) = 0 := by
  rw [lemma77HoldPrefixSignedEndpointMass_eq_tsum_length_fiber]
  letI : IsEmpty
      {hs : List TaoSection7RenewalPoint //
        hs ∈ lemma77HoldPrefixSignedEndpointLengthEvent
          start n (j : ℤ) (s : ℤ)} :=
    ⟨by
      intro hs
      have hlen : hs.1.length = n := hs.2.2
      have hendpoint :
          lemma77HoldPrefixIncrement start n hs.1 = j := by
        exact_mod_cast hs.2.1.1
      rw [lemma77HoldPrefixIncrement_eq_horizontalDelta] at hendpoint
      have hge := lemma77HoldPrefixHorizontalDelta_ge_steps
        (q := n) (full := hs.1) (by omega)
      omega⟩
  simp

theorem lemma77HeightPotentialMass_eq_zero_of_j_neg
    (start : TaoSection7RenewalPoint) {j : ℤ} (hj : j < 0) (s : ℕ) :
    lemma77HeightPotentialMass start j s = 0 := by
  unfold lemma77HeightPotentialMass
  calc
    (∑' n : ℕ,
        lemma77HoldPrefixSignedEndpointMass start n j (s : ℤ)) =
        ∑' _n : ℕ, (0 : ℝ) := by
          apply tsum_congr
          intro n
          exact lemma77HoldPrefixSignedEndpointMass_eq_zero_of_j_neg hj
    _ = 0 := by simp

theorem lemma77HeightPotentialMass_eq_sum_range
    (start : TaoSection7RenewalPoint) (j s : ℕ) :
    lemma77HeightPotentialMass start (j : ℤ) s =
      ∑ n ∈ Finset.range (j + 1),
        lemma77HoldPrefixSignedEndpointMass start n (j : ℤ) (s : ℤ) := by
  unfold lemma77HeightPotentialMass
  rw [tsum_eq_sum (s := Finset.range (j + 1))]
  intro n hn
  have hjn : j < n := by
    simpa [Finset.mem_range] using hn
  exact lemma77HoldPrefixSignedEndpointMass_eq_zero_of_nat_j_lt_n start hjn

theorem lemma77HeightPotentialMass_eq_zeroAtom_add_rawTerminalEpochMass
    (start : TaoSection7RenewalPoint) (j s : ℕ) :
    lemma77HeightPotentialMass start (j : ℤ) s =
      (if j = 0 ∧ s = 0 then 1 else 0) +
        ∑ n ∈ Finset.range j,
          ∑' bs : Lemma77RawTerminalEpochFiber (n + 1) j s,
            lemma77RawPascalWordMass bs.1 := by
  rw [lemma77HeightPotentialMass_eq_sum_range,
    Finset.sum_range_succ', add_comm,
    lemma77HoldPrefixSignedEndpointMass_zero_nat]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact lemma77HoldPrefixSignedEndpointMass_eq_rawTerminalEpochMass
    start n j s

theorem lemma77HeightPotentialMass_eq_zeroAtom_add_rawTerminalMass
    (start : TaoSection7RenewalPoint) (j s : ℕ) :
    lemma77HeightPotentialMass start (j : ℤ) s =
      (if j = 0 ∧ s = 0 then 1 else 0) +
        ∑' bs : Lemma77RawTerminalFiber j s,
          lemma77RawPascalWordMass bs.1 := by
  rw [lemma77HeightPotentialMass_eq_zeroAtom_add_rawTerminalEpochMass,
    lemma77_sum_rawTerminalEpochMass_eq_rawTerminalMass
      (start := start) j s]

theorem lemma77HeightPotentialMass_eq_rawTerminalMass
    (start : TaoSection7RenewalPoint) {j : ℕ} (hj : 0 < j) (s : ℕ) :
    lemma77HeightPotentialMass start (j : ℤ) s =
      ∑' bs : Lemma77RawTerminalFiber j s,
        lemma77RawPascalWordMass bs.1 := by
  rw [lemma77HeightPotentialMass_eq_zeroAtom_add_rawTerminalMass]
  simp [hj.ne']

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
