/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7PairExpansion

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable def taoSection7PairExpansionExpectation
    (N : ℕ) (xi : ZMod (3 ^ N)) (k : ℕ) (j : ℕ+) (s : ℕ) : ℂ :=
  ∑' as : List ℕ+,
    ((geom2PNatListPMF k as).toReal : ℂ) *
      taoSection7PairExpansionFrom N xi j s as

noncomputable def taoSection7PairSourceEnvelope
    (N : ℕ) (xi : ZMod (3 ^ N)) (m : ℕ) (j s : ℕ) : ℝ :=
  ∑' bs : List ℕ,
    (taoSection7PascalSourceListPMF m bs).toReal *
      taoSection7FactorProductFrom
        (taoSection7SourceFThreeFactor N xi) j s bs

private theorem taoSection7PairExpansionExpectation_summable
    (N : ℕ) (xi : ZMod (3 ^ N)) (k : ℕ) (j : ℕ+) (s : ℕ) :
    Summable fun as : List ℕ+ =>
      ((geom2PNatListPMF k as).toReal : ℂ) *
        taoSection7PairExpansionFrom N xi j s as := by
  refine Summable.of_norm_bounded
    (pmf_summable_toReal (geom2PNatListPMF k)) ?_
  intro as
  rw [norm_mul, norm_taoSection7PairExpansionFrom_eq_one]
  simp

private theorem pmf_tsum_toReal_eq_one
    {α : Type*} (p : PMF α) :
    (∑' a : α, (p a).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq]
  · rw [PMF.tsum_coe]
    norm_num
  · intro a
    exact PMF.apply_ne_top p a

private theorem taoSection7PairSourceEnvelope_summable
    (N : ℕ) (xi : ZMod (3 ^ N)) (m j s : ℕ) :
    Summable fun bs : List ℕ =>
      (taoSection7PascalSourceListPMF m bs).toReal *
        taoSection7FactorProductFrom
          (taoSection7SourceFThreeFactor N xi) j s bs := by
  refine Summable.of_norm_bounded
    (pmf_summable_toReal (taoSection7PascalSourceListPMF m)) ?_
  intro bs
  have hnonneg := taoSection7FactorProductFrom_nonneg
    (taoSection7SourceFThreeFactor_nonneg N xi) j s bs
  have hle := taoSection7FactorProductFrom_le_one
    (taoSection7SourceFThreeFactor_nonneg N xi)
    (taoSection7SourceFThreeFactor_le_one N xi) j s bs
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg ENNReal.toReal_nonneg hnonneg)]
  simpa using mul_le_of_le_one_right ENNReal.toReal_nonneg hle

private theorem tsum_list_eq_tsum_twoCons_of_nil_singleton_zero
    {α E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E]
    (f : List α → E) (h0 : f [] = 0) (h1 : ∀ a, f [a] = 0) :
    (∑' as : List α, f as) =
      ∑' x : (α × α) × List α,
        f (x.1.1 :: x.1.2 :: x.2) := by
  classical
  let g : (α × α) × List α → List α :=
    fun x => x.1.1 :: x.1.2 :: x.2
  have hg : Function.Injective g := by
    rintro ⟨⟨a₁, a₂⟩, as⟩ ⟨⟨b₁, b₂⟩, bs⟩ hab
    simp [g] at hab ⊢
    exact ⟨⟨hab.1, hab.2.1⟩, hab.2.2⟩
  have hsupp : Function.support f ⊆ Set.range g := by
    intro as has
    cases as with
    | nil => exact False.elim (has h0)
    | cons a tail =>
        cases tail with
        | nil => exact False.elim (has (h1 a))
        | cons b bs => exact ⟨((a, b), bs), rfl⟩
  exact (hg.tsum_eq (f := f) hsupp).symm

private theorem tsum_list_eq_tsum_cons_of_nil_zero
    {α E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E]
    (f : List α → E) (h0 : f [] = 0) :
    (∑' as : List α, f as) =
      ∑' x : α × List α, f (x.1 :: x.2) := by
  classical
  let g : α × List α → List α := fun x => x.1 :: x.2
  have hg : Function.Injective g := by
    rintro ⟨a, as⟩ ⟨b, bs⟩ hab
    simp [g] at hab ⊢
    exact hab
  have hsupp : Function.support f ⊆ Set.range g := by
    intro as has
    cases as with
    | nil => exact False.elim (has h0)
    | cons a tail => exact ⟨(a, tail), rfl⟩
  exact (hg.tsum_eq (f := f) hsupp).symm

private theorem taoSection7PairSourceEnvelope_succ
    (N : ℕ) (xi : ZMod (3 ^ N)) (m : ℕ) (j s : ℕ) :
    taoSection7PairSourceEnvelope N xi (m + 1) j s =
      ∑' b : ℕ,
        (taoSection7PascalSourcePMF b).toReal *
          taoSection7SourceFThreeFactor N xi j s b *
          taoSection7PairSourceEnvelope N xi m (j + 1) (s + b) := by
  unfold taoSection7PairSourceEnvelope
  have hnil :
      (taoSection7PascalSourceListPMF (m + 1) []).toReal *
          taoSection7FactorProductFrom
            (taoSection7SourceFThreeFactor N xi) j s [] = 0 := by
    rw [taoSection7PascalSourceListPMF_succ_apply_nil]
    simp
  calc
    (∑' bs : List ℕ,
        (taoSection7PascalSourceListPMF (m + 1) bs).toReal *
          taoSection7FactorProductFrom
            (taoSection7SourceFThreeFactor N xi) j s bs) =
        ∑' x : ℕ × List ℕ,
          (taoSection7PascalSourceListPMF (m + 1)
              (x.1 :: x.2)).toReal *
            taoSection7FactorProductFrom
              (taoSection7SourceFThreeFactor N xi) j s
              (x.1 :: x.2) := by
      exact tsum_list_eq_tsum_cons_of_nil_zero _ hnil
    _ = ∑' x : ℕ × List ℕ,
          (taoSection7PascalSourcePMF x.1).toReal *
            taoSection7SourceFThreeFactor N xi j s x.1 *
            ((taoSection7PascalSourceListPMF m x.2).toReal *
              taoSection7FactorProductFrom
                (taoSection7SourceFThreeFactor N xi)
                (j + 1) (s + x.1) x.2) := by
      apply tsum_congr
      intro x
      rw [taoSection7PascalSourceListPMF_succ_apply_cons,
        ENNReal.toReal_mul, taoSection7FactorProductFrom]
      ring
    _ = ∑' b : ℕ,
          (taoSection7PascalSourcePMF b).toReal *
            taoSection7SourceFThreeFactor N xi j s b *
            (∑' bs : List ℕ,
              (taoSection7PascalSourceListPMF m bs).toReal *
                taoSection7FactorProductFrom
                  (taoSection7SourceFThreeFactor N xi)
                  (j + 1) (s + b) bs) := by
      have hmass : Summable fun x : ℕ × List ℕ =>
          (taoSection7PascalSourcePMF x.1).toReal *
            (taoSection7PascalSourceListPMF m x.2).toReal :=
        Summable.mul_of_nonneg
          (f := fun b : ℕ => (taoSection7PascalSourcePMF b).toReal)
          (g := fun bs : List ℕ =>
            (taoSection7PascalSourceListPMF m bs).toReal)
          (pmf_summable_toReal taoSection7PascalSourcePMF)
          (pmf_summable_toReal (taoSection7PascalSourceListPMF m))
          (fun _ => ENNReal.toReal_nonneg)
          (fun _ => ENNReal.toReal_nonneg)
      have hsum : Summable fun x : ℕ × List ℕ =>
          (taoSection7PascalSourcePMF x.1).toReal *
            taoSection7SourceFThreeFactor N xi j s x.1 *
            ((taoSection7PascalSourceListPMF m x.2).toReal *
              taoSection7FactorProductFrom
                (taoSection7SourceFThreeFactor N xi)
                (j + 1) (s + x.1) x.2) := by
        refine Summable.of_norm_bounded hmass ?_
        intro x
        have hF0 := taoSection7SourceFThreeFactor_nonneg N xi j s x.1
        have hF1 := taoSection7SourceFThreeFactor_le_one N xi j s x.1
        have hP0 := taoSection7FactorProductFrom_nonneg
          (taoSection7SourceFThreeFactor_nonneg N xi)
          (j + 1) (s + x.1) x.2
        have hP1 := taoSection7FactorProductFrom_le_one
          (taoSection7SourceFThreeFactor_nonneg N xi)
          (taoSection7SourceFThreeFactor_le_one N xi)
          (j + 1) (s + x.1) x.2
        have hp0 : 0 ≤ (taoSection7PascalSourcePMF x.1).toReal :=
          ENNReal.toReal_nonneg
        have hq0 :
            0 ≤ (taoSection7PascalSourceListPMF m x.2).toReal :=
          ENNReal.toReal_nonneg
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc
          (taoSection7PascalSourcePMF x.1).toReal *
                taoSection7SourceFThreeFactor N xi j s x.1 *
              ((taoSection7PascalSourceListPMF m x.2).toReal *
                taoSection7FactorProductFrom
                  (taoSection7SourceFThreeFactor N xi)
                  (j + 1) (s + x.1) x.2) ≤
              (taoSection7PascalSourcePMF x.1).toReal * 1 *
                ((taoSection7PascalSourceListPMF m x.2).toReal * 1) := by
            gcongr
          _ = (taoSection7PascalSourcePMF x.1).toReal *
                (taoSection7PascalSourceListPMF m x.2).toReal := by ring
      have hfiber : ∀ b : ℕ, Summable fun bs : List ℕ =>
          (taoSection7PascalSourcePMF b).toReal *
            taoSection7SourceFThreeFactor N xi j s b *
            ((taoSection7PascalSourceListPMF m bs).toReal *
              taoSection7FactorProductFrom
                (taoSection7SourceFThreeFactor N xi)
                (j + 1) (s + b) bs) := by
        intro b
        exact (taoSection7PairSourceEnvelope_summable
          N xi m (j + 1) (s + b)).mul_left
            ((taoSection7PascalSourcePMF b).toReal *
              taoSection7SourceFThreeFactor N xi j s b)
      rw [Summable.tsum_prod' hsum hfiber]
      apply tsum_congr
      intro b
      simp only [Prod.fst, Prod.snd]
      rw [tsum_mul_left]

private theorem taoSection7PairExpansionExpectation_add_two_eq_pair_tsum
    (N : ℕ) (xi : ZMod (3 ^ N)) (k : ℕ) (j : ℕ+) (s : ℕ) :
    taoSection7PairExpansionExpectation N xi (k + 2) j s =
      ∑' a : ℕ+ × ℕ+,
        ((taoSection7Geom2PairPMF a).toReal : ℂ) *
          taoSection7PairPhase N xi
            (taoSection7PairX N j
              (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
          taoSection7PairExpansionExpectation N xi k
            ⟨(j : ℕ) + 1, by omega⟩
            (s + (a.1 : ℕ) + (a.2 : ℕ)) := by
  unfold taoSection7PairExpansionExpectation
  have hnil :
      ((geom2PNatListPMF (k + 2) []).toReal : ℂ) *
          taoSection7PairExpansionFrom N xi j s [] = 0 := by
    rw [show k + 2 = (k + 1) + 1 by omega,
      geom2PNatListPMF_succ_apply_nil]
    simp
  have hsingle : ∀ a : ℕ+,
      ((geom2PNatListPMF (k + 2) [a]).toReal : ℂ) *
          taoSection7PairExpansionFrom N xi j s [a] = 0 := by
    intro a
    rw [show k + 2 = (k + 1) + 1 by omega,
      geom2PNatListPMF_succ_apply_cons,
      geom2PNatListPMF_succ_apply_nil]
    simp
  calc
    (∑' as : List ℕ+,
        ((geom2PNatListPMF (k + 2) as).toReal : ℂ) *
          taoSection7PairExpansionFrom N xi j s as) =
        ∑' x : (ℕ+ × ℕ+) × List ℕ+,
          ((geom2PNatListPMF (k + 2)
            (x.1.1 :: x.1.2 :: x.2)).toReal : ℂ) *
            taoSection7PairExpansionFrom N xi j s
              (x.1.1 :: x.1.2 :: x.2) := by
      exact tsum_list_eq_tsum_twoCons_of_nil_singleton_zero _ hnil hsingle
    _ = ∑' x : (ℕ+ × ℕ+) × List ℕ+,
          ((taoSection7Geom2PairPMF x.1).toReal : ℂ) *
            taoSection7PairPhase N xi
              (taoSection7PairX N j
                (Int.ofNat
                  (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)))) x.1.2 *
            (((geom2PNatListPMF k x.2).toReal : ℂ) *
              taoSection7PairExpansionFrom N xi
                ⟨(j : ℕ) + 1, by omega⟩
                (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)) x.2) := by
      apply tsum_congr
      rintro ⟨⟨a₁, a₂⟩, tail⟩
      rw [show k + 2 = (k + 1) + 1 by omega,
        geom2PNatListPMF_succ_apply_cons,
        geom2PNatListPMF_succ_apply_cons,
        ENNReal.toReal_mul, ENNReal.toReal_mul,
        taoSection7PairExpansionFrom]
      rw [taoSection7Geom2PairPMF_apply_toReal]
      unfold geom2PNatPairMass
      push_cast
      ring
    _ = ∑' a : ℕ+ × ℕ+,
          ((taoSection7Geom2PairPMF a).toReal : ℂ) *
            taoSection7PairPhase N xi
              (taoSection7PairX N j
                (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
            (∑' tail : List ℕ+,
              ((geom2PNatListPMF k tail).toReal : ℂ) *
                taoSection7PairExpansionFrom N xi
                  ⟨(j : ℕ) + 1, by omega⟩
                  (s + (a.1 : ℕ) + (a.2 : ℕ)) tail) := by
      have hmass : Summable fun x : (ℕ+ × ℕ+) × List ℕ+ =>
          (taoSection7Geom2PairPMF x.1).toReal *
            (geom2PNatListPMF k x.2).toReal :=
        Summable.mul_of_nonneg
          (f := fun a : ℕ+ × ℕ+ =>
            (taoSection7Geom2PairPMF a).toReal)
          (g := fun tail : List ℕ+ =>
            (geom2PNatListPMF k tail).toReal)
          (pmf_summable_toReal taoSection7Geom2PairPMF)
          (pmf_summable_toReal (geom2PNatListPMF k))
          (fun _ => ENNReal.toReal_nonneg)
          (fun _ => ENNReal.toReal_nonneg)
      have hsum : Summable fun x : (ℕ+ × ℕ+) × List ℕ+ =>
          ((taoSection7Geom2PairPMF x.1).toReal : ℂ) *
            taoSection7PairPhase N xi
              (taoSection7PairX N j
                (Int.ofNat
                  (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)))) x.1.2 *
            (((geom2PNatListPMF k x.2).toReal : ℂ) *
              taoSection7PairExpansionFrom N xi
                ⟨(j : ℕ) + 1, by omega⟩
                (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)) x.2) := by
        refine Summable.of_norm_bounded hmass ?_
        intro x
        rw [norm_mul, norm_mul, norm_mul,
          norm_taoSection7PairExpansionFrom_eq_one]
        have hphase : ‖taoSection7PairPhase N xi
            (taoSection7PairX N j
              (Int.ofNat (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)))) x.1.2‖ = 1 := by
          unfold taoSection7PairPhase
          exact norm_taoForwardDFTKernel_eq_one _ _
        rw [hphase]
        simp
      have hfiber : ∀ a : ℕ+ × ℕ+,
          Summable fun tail : List ℕ+ =>
            ((taoSection7Geom2PairPMF a).toReal : ℂ) *
              taoSection7PairPhase N xi
                (taoSection7PairX N j
                  (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
              (((geom2PNatListPMF k tail).toReal : ℂ) *
                taoSection7PairExpansionFrom N xi
                  ⟨(j : ℕ) + 1, by omega⟩
                  (s + (a.1 : ℕ) + (a.2 : ℕ)) tail) := by
        intro a
        exact (taoSection7PairExpansionExpectation_summable N xi k
          ⟨(j : ℕ) + 1, by omega⟩
          (s + (a.1 : ℕ) + (a.2 : ℕ))).mul_left
            (((taoSection7Geom2PairPMF a).toReal : ℂ) *
              taoSection7PairPhase N xi
                (taoSection7PairX N j
                  (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2)
      rw [Summable.tsum_prod' hsum hfiber]
      apply tsum_congr
      intro a
      simp only [Prod.fst, Prod.snd]
      rw [tsum_mul_left]

private theorem taoSection7Pair_tsum_eq_fiber_tsum
    (N : ℕ) (xi : ZMod (3 ^ N)) (j : ℕ+) (s : ℕ)
    (G : ℕ → ℂ) (hG : ∀ b, ‖G b‖ ≤ 1) :
    (∑' a : ℕ+ × ℕ+,
        ((taoSection7Geom2PairPMF a).toReal : ℂ) *
          taoSection7PairPhase N xi
            (taoSection7PairX N j
              (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
          G ((a.1 : ℕ) + (a.2 : ℕ))) =
      ∑' b : ℕ,
        taoSection7PairFiberCharacterMass N xi
          (taoSection7PairX N j (Int.ofNat (s + b))) b * G b := by
  classical
  let F : ℕ → (ℕ+ × ℕ+) → ℂ := fun b a =>
    if b = (a.1 : ℕ) + (a.2 : ℕ) then
      ((taoSection7Geom2PairPMF a).toReal : ℂ) *
        taoSection7PairPhase N xi
          (taoSection7PairX N j (Int.ofNat (s + b))) a.2 * G b
    else
      0
  let M : ℕ × (ℕ+ × ℕ+) → ℝ := fun x =>
    if x.1 = (x.2.1 : ℕ) + (x.2.2 : ℕ) then
      (taoSection7Geom2PairPMF x.2).toReal
    else
      0
  have hM : Summable M := by
    rw [summable_prod_of_nonneg (by
      intro x
      simp only [M]
      split <;> positivity)]
    constructor
    · intro b
      refine Summable.of_norm_bounded
        (pmf_summable_toReal taoSection7Geom2PairPMF) ?_
      intro a
      simp only [M]
      by_cases h : b = (a.1 : ℕ) + (a.2 : ℕ) <;>
        simp [h, ENNReal.toReal_nonneg]
    · have hmap := pmf_summable_toReal
        (taoSection7Geom2PairPMF.map
          (fun a => (a.1 : ℕ) + (a.2 : ℕ)))
      refine hmap.congr ?_
      intro b
      rw [pmf_map_apply_toReal_tsum]
  have hF : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded hM ?_
    rintro ⟨b, a⟩
    simp only [Function.uncurry_apply_pair, F, M]
    by_cases h : b = (a.1 : ℕ) + (a.2 : ℕ)
    · rw [if_pos h, if_pos h, norm_mul, norm_mul]
      have hphase : ‖taoSection7PairPhase N xi
          (taoSection7PairX N j (Int.ofNat (s + b))) a.2‖ = 1 := by
        unfold taoSection7PairPhase
        exact norm_taoForwardDFTKernel_eq_one _ _
      rw [hphase, mul_one]
      simpa [ENNReal.toReal_nonneg] using
        mul_le_of_le_one_right
          (show 0 ≤ (taoSection7Geom2PairPMF a).toReal from
            ENNReal.toReal_nonneg) (hG b)
    · simp [h]
  have hrow : ∀ b, Summable (F b) := by
    intro b
    refine Summable.of_norm_bounded
      (pmf_summable_toReal taoSection7Geom2PairPMF) ?_
    intro a
    simp only [F]
    by_cases h : b = (a.1 : ℕ) + (a.2 : ℕ)
    · rw [if_pos h, norm_mul, norm_mul]
      have hphase : ‖taoSection7PairPhase N xi
          (taoSection7PairX N j (Int.ofNat (s + b))) a.2‖ = 1 := by
        unfold taoSection7PairPhase
        exact norm_taoForwardDFTKernel_eq_one _ _
      rw [hphase, mul_one]
      simpa [ENNReal.toReal_nonneg] using
        mul_le_of_le_one_right
          (show 0 ≤ (taoSection7Geom2PairPMF a).toReal from
            ENNReal.toReal_nonneg) (hG b)
    · simp [h]
  have hcol : ∀ a : ℕ+ × ℕ+, Summable fun b => F b a := by
    intro a
    refine summable_of_ne_finset_zero
      (s := {(a.1 : ℕ) + (a.2 : ℕ)}) ?_
    intro b hb
    simp only [Finset.mem_singleton] at hb
    simp [F, hb]
  calc
    (∑' a : ℕ+ × ℕ+,
        ((taoSection7Geom2PairPMF a).toReal : ℂ) *
          taoSection7PairPhase N xi
            (taoSection7PairX N j
              (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
          G ((a.1 : ℕ) + (a.2 : ℕ))) =
        ∑' a : ℕ+ × ℕ+, ∑' b : ℕ, F b a := by
      apply tsum_congr
      intro a
      rw [tsum_eq_single ((a.1 : ℕ) + (a.2 : ℕ))]
      · simp [F, add_assoc]
      · intro b hb
        simp [F, hb]
    _ = ∑' b : ℕ, ∑' a : ℕ+ × ℕ+, F b a := by
      exact hF.tsum_comm' hrow hcol
    _ = ∑' b : ℕ,
        taoSection7PairFiberCharacterMass N xi
          (taoSection7PairX N j (Int.ofNat (s + b))) b * G b := by
      apply tsum_congr
      intro b
      unfold taoSection7PairFiberCharacterMass
      symm
      rw [← tsum_mul_right]
      apply tsum_congr
      intro a
      by_cases h : (a.1 : ℕ) + (a.2 : ℕ) = b
      · have h' : b = (a.1 : ℕ) + (a.2 : ℕ) := h.symm
        simp only [F]
        rw [if_pos h, if_pos h']
      · have h' : ¬b = (a.1 : ℕ) + (a.2 : ℕ) := by omega
        simp only [F]
        rw [if_neg h, if_neg h']
        simp

theorem norm_taoSection7PairExpansionExpectation_le_one
    (N : ℕ) (xi : ZMod (3 ^ N)) (k : ℕ) (j : ℕ+) (s : ℕ) :
    ‖taoSection7PairExpansionExpectation N xi k j s‖ ≤ 1 := by
  unfold taoSection7PairExpansionExpectation
  calc
    ‖∑' as : List ℕ+,
        ((geom2PNatListPMF k as).toReal : ℂ) *
          taoSection7PairExpansionFrom N xi j s as‖ ≤
        ∑' as : List ℕ+,
          ‖((geom2PNatListPMF k as).toReal : ℂ) *
            taoSection7PairExpansionFrom N xi j s as‖ :=
      norm_tsum_le_tsum_norm
        (taoSection7PairExpansionExpectation_summable N xi k j s).norm
    _ = ∑' as : List ℕ+, (geom2PNatListPMF k as).toReal := by
      apply tsum_congr
      intro as
      rw [norm_mul, norm_taoSection7PairExpansionFrom_eq_one]
      simp
    _ = 1 := by
      exact pmf_tsum_toReal_eq_one (geom2PNatListPMF k)

private theorem taoSection7PairExpansionExpectation_add_two_eq_fiber_tsum
    (N : ℕ) (xi : ZMod (3 ^ N)) (k : ℕ) (j : ℕ+) (s : ℕ) :
    taoSection7PairExpansionExpectation N xi (k + 2) j s =
      ∑' b : ℕ,
        taoSection7PairFiberCharacterMass N xi
            (taoSection7PairX N j (Int.ofNat (s + b))) b *
          taoSection7PairExpansionExpectation N xi k
            ⟨(j : ℕ) + 1, by omega⟩ (s + b) := by
  rw [taoSection7PairExpansionExpectation_add_two_eq_pair_tsum]
  simpa [add_assoc] using
    taoSection7Pair_tsum_eq_fiber_tsum N xi j s
      (fun b => taoSection7PairExpansionExpectation N xi k
        ⟨(j : ℕ) + 1, by omega⟩ (s + b))
      (fun b => norm_taoSection7PairExpansionExpectation_le_one
        N xi k ⟨(j : ℕ) + 1, by omega⟩ (s + b))

private theorem taoSection7PairSourceEnvelope_nonneg
    (N : ℕ) (xi : ZMod (3 ^ N)) (m j s : ℕ) :
    0 ≤ taoSection7PairSourceEnvelope N xi m j s := by
  unfold taoSection7PairSourceEnvelope
  exact tsum_nonneg fun bs => mul_nonneg ENNReal.toReal_nonneg
    (taoSection7FactorProductFrom_nonneg
      (taoSection7SourceFThreeFactor_nonneg N xi) j s bs)

private theorem taoSection7PairSourceEnvelope_le_one
    (N : ℕ) (xi : ZMod (3 ^ N)) (m j s : ℕ) :
    taoSection7PairSourceEnvelope N xi m j s ≤ 1 := by
  unfold taoSection7PairSourceEnvelope
  calc
    (∑' bs : List ℕ,
        (taoSection7PascalSourceListPMF m bs).toReal *
          taoSection7FactorProductFrom
            (taoSection7SourceFThreeFactor N xi) j s bs) ≤
        ∑' bs : List ℕ,
          (taoSection7PascalSourceListPMF m bs).toReal := by
      exact (taoSection7PairSourceEnvelope_summable N xi m j s).tsum_le_tsum
        (fun bs => mul_le_of_le_one_right ENNReal.toReal_nonneg
          (taoSection7FactorProductFrom_le_one
            (taoSection7SourceFThreeFactor_nonneg N xi)
            (taoSection7SourceFThreeFactor_le_one N xi) j s bs))
        (pmf_summable_toReal (taoSection7PascalSourceListPMF m))
    _ = 1 := pmf_tsum_toReal_eq_one _

private theorem taoSection7PairSourceEnvelope_zero
    (N : ℕ) (xi : ZMod (3 ^ N)) (j s : ℕ) :
    taoSection7PairSourceEnvelope N xi 0 j s = 1 := by
  unfold taoSection7PairSourceEnvelope
  rw [tsum_eq_single ([] : List ℕ)]
  · simp [taoSection7PascalSourceListPMF,
      taoSection7FactorProductFrom]
  · intro bs hbs
    simp [taoSection7PascalSourceListPMF, hbs]

theorem norm_taoSection7PairExpansionExpectation_le_sourceEnvelope
    (N : ℕ) (xi : ZMod (3 ^ N)) :
    ∀ (k : ℕ) (j : ℕ+) (s : ℕ),
      ‖taoSection7PairExpansionExpectation N xi k j s‖ ≤
        taoSection7PairSourceEnvelope N xi (k / 2) (j : ℕ) s := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro j s
      rw [taoSection7PairSourceEnvelope_zero]
      exact norm_taoSection7PairExpansionExpectation_le_one N xi 0 j s
  | one =>
      intro j s
      rw [taoSection7PairSourceEnvelope_zero]
      exact norm_taoSection7PairExpansionExpectation_le_one N xi 1 j s
  | more k ih _ihSucc =>
      intro j s
      rw [taoSection7PairExpansionExpectation_add_two_eq_fiber_tsum]
      rw [show (k + 2) / 2 = k / 2 + 1 by omega]
      rw [taoSection7PairSourceEnvelope_succ]
      let T : ℕ → ℂ := fun b =>
        taoSection7PairFiberCharacterMass N xi
            (taoSection7PairX N j (Int.ofNat (s + b))) b *
          taoSection7PairExpansionExpectation N xi k
            ⟨(j : ℕ) + 1, by omega⟩ (s + b)
      let R : ℕ → ℝ := fun b =>
        (taoSection7PascalSourcePMF b).toReal *
          taoSection7SourceFThreeFactor N xi (j : ℕ) s b *
          taoSection7PairSourceEnvelope N xi (k / 2)
            ((j : ℕ) + 1) (s + b)
      have hT : Summable T := by
        refine Summable.of_norm_bounded
          (pmf_summable_toReal taoSection7PascalSourcePMF) ?_
        intro b
        simp only [T, norm_mul]
        calc
          ‖taoSection7PairFiberCharacterMass N xi
                (taoSection7PairX N j (Int.ofNat (s + b))) b‖ *
              ‖taoSection7PairExpansionExpectation N xi k
                ⟨(j : ℕ) + 1, by omega⟩ (s + b)‖ ≤
              ((taoSection7PascalSourcePMF b).toReal *
                taoSection7SourceFThreeFactor N xi (j : ℕ) s b) * 1 := by
            exact mul_le_mul
              (norm_taoSection7PairFiberCharacterMass_le_sourceFactor
                N xi j s b)
              (norm_taoSection7PairExpansionExpectation_le_one N xi k
                ⟨(j : ℕ) + 1, by omega⟩ (s + b))
              (norm_nonneg _)
              (mul_nonneg ENNReal.toReal_nonneg
                (taoSection7SourceFThreeFactor_nonneg
                  N xi (j : ℕ) s b))
          _ ≤ (taoSection7PascalSourcePMF b).toReal * 1 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_of_le_one_right ENNReal.toReal_nonneg
                (taoSection7SourceFThreeFactor_le_one
                  N xi (j : ℕ) s b)) (by norm_num)
          _ = (taoSection7PascalSourcePMF b).toReal := by ring
      have hR : Summable R := by
        refine Summable.of_norm_bounded
          (pmf_summable_toReal taoSection7PascalSourcePMF) ?_
        intro b
        have hF0 := taoSection7SourceFThreeFactor_nonneg N xi (j : ℕ) s b
        have hF1 := taoSection7SourceFThreeFactor_le_one N xi (j : ℕ) s b
        have hE0 := taoSection7PairSourceEnvelope_nonneg
          N xi (k / 2) ((j : ℕ) + 1) (s + b)
        have hE1 := taoSection7PairSourceEnvelope_le_one
          N xi (k / 2) ((j : ℕ) + 1) (s + b)
        simp only [R, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        calc
          (taoSection7PascalSourcePMF b).toReal *
                taoSection7SourceFThreeFactor N xi (j : ℕ) s b *
              taoSection7PairSourceEnvelope N xi (k / 2)
                ((j : ℕ) + 1) (s + b) ≤
              (taoSection7PascalSourcePMF b).toReal * 1 * 1 := by
            gcongr
          _ = (taoSection7PascalSourcePMF b).toReal := by ring
      calc
        ‖∑' b : ℕ, T b‖ ≤ ∑' b : ℕ, ‖T b‖ :=
          norm_tsum_le_tsum_norm hT.norm
        _ ≤ ∑' b : ℕ, R b := by
          exact hT.norm.tsum_le_tsum (fun b => by
            simp only [T, R, norm_mul]
            exact mul_le_mul
              (norm_taoSection7PairFiberCharacterMass_le_sourceFactor
                N xi j s b)
              (ih ⟨(j : ℕ) + 1, by omega⟩ (s + b))
              (norm_nonneg _)
              (mul_nonneg ENNReal.toReal_nonneg
                (taoSection7SourceFThreeFactor_nonneg
                  N xi (j : ℕ) s b))) hR
        _ = ∑' b : ℕ,
            (taoSection7PascalSourcePMF b).toReal *
              taoSection7SourceFThreeFactor N xi (j : ℕ) s b *
              taoSection7PairSourceEnvelope N xi (k / 2)
                ((j : ℕ) + 1) (s + b) := by rfl

theorem norm_taoSection7SChi_le_pascalSource_expectation
    (n : ℕ) (xi : ZMod (3 ^ n)) :
    ‖taoSection7SChi n xi‖ ≤
      ∑' bs : List ℕ,
        (taoSection7PascalSourceListPMF (n / 2) bs).toReal *
          taoSection7FactorProduct
            (taoSection7SourceFThreeFactor n xi) bs := by
  have hschi : taoSection7SChi n xi =
      taoSection7PairExpansionExpectation n xi n 1 0 := by
    unfold taoSection7SChi taoSection7PairExpansionExpectation
    apply tsum_congr
    intro as
    by_cases hlen : as.length = n
    · rw [taoSection7CharacterTerm_eq_pairExpansionFrom n xi as hlen]
    · rw [geom2PNatListPMF_apply_eq_zero_of_length_ne n as hlen]
      simp
  rw [hschi]
  simpa [taoSection7PairSourceEnvelope, taoSection7FactorProduct] using
    norm_taoSection7PairExpansionExpectation_le_sourceEnvelope
      n xi n 1 0

end Tao

end Erdos1135Predecessor
