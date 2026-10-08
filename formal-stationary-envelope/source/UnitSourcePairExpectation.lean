import UnitSourceTerminalPhase

/-!
# Unit-source terminal-phase expectation

This proof leaf integrates the fixed-modulus adjacent-pair expansion against
the exact Geom(2) source law, with a unit terminal phase retained. Each pair
is grouped by its raw Pascal sum before taking norms, so the checked `b = 3`
cancellation factor is retained. Private recursion and summability arguments
adapt native `Section7PairExpectation`; the source envelope is unchanged.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

/-- Character expectation of the recursive pair expansion from state `(j,s)`. -/
noncomputable def unitSourcePairExpectation
    (N : ℕ) (xi : ZMod (3 ^ N)) (τ : UnitSourceTerminalPhase) (k : ℕ) (j : ℕ+) (s : ℕ) : ℂ :=
  ∑' as : List ℕ+,
    ((geom2PNatListPMF k as).toReal : ℂ) *
      unitSourcePairExpansionFrom N xi τ j s as

private theorem unitSourcePairExpectation_summable
    (N : ℕ) (xi : ZMod (3 ^ N)) (τ : UnitSourceTerminalPhase) (k : ℕ) (j : ℕ+) (s : ℕ) :
    Summable fun as : List ℕ+ =>
      ((geom2PNatListPMF k as).toReal : ℂ) *
        unitSourcePairExpansionFrom N xi τ j s as := by
  refine Summable.of_norm_bounded
    (pmf_summable_toReal (geom2PNatListPMF k)) ?_
  intro as
  rw [norm_mul, norm_unitSourcePairExpansionFrom_eq_one]
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
      dsimp only
      rw [tsum_mul_left]

private theorem unitSourcePairExpectation_add_two_eq_pair_tsum
    (N : ℕ) (xi : ZMod (3 ^ N)) (τ : UnitSourceTerminalPhase) (k : ℕ) (j : ℕ+) (s : ℕ) :
    unitSourcePairExpectation N xi τ (k + 2) j s =
      ∑' a : ℕ+ × ℕ+,
        ((taoSection7Geom2PairPMF a).toReal : ℂ) *
          taoSection7PairPhase N xi
            (taoSection7PairX N j
              (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
          unitSourcePairExpectation N xi τ k
            ⟨(j : ℕ) + 1, by omega⟩
            (s + (a.1 : ℕ) + (a.2 : ℕ)) := by
  unfold unitSourcePairExpectation
  have hnil :
      ((geom2PNatListPMF (k + 2) []).toReal : ℂ) *
          unitSourcePairExpansionFrom N xi τ j s [] = 0 := by
    rw [show k + 2 = (k + 1) + 1 by omega,
      geom2PNatListPMF_succ_apply_nil]
    simp
  have hsingle : ∀ a : ℕ+,
      ((geom2PNatListPMF (k + 2) [a]).toReal : ℂ) *
          unitSourcePairExpansionFrom N xi τ j s [a] = 0 := by
    intro a
    rw [show k + 2 = (k + 1) + 1 by omega,
      geom2PNatListPMF_succ_apply_cons,
      geom2PNatListPMF_succ_apply_nil]
    simp
  calc
    (∑' as : List ℕ+,
        ((geom2PNatListPMF (k + 2) as).toReal : ℂ) *
          unitSourcePairExpansionFrom N xi τ j s as) =
        ∑' x : (ℕ+ × ℕ+) × List ℕ+,
          ((geom2PNatListPMF (k + 2)
            (x.1.1 :: x.1.2 :: x.2)).toReal : ℂ) *
            unitSourcePairExpansionFrom N xi τ j s
              (x.1.1 :: x.1.2 :: x.2) := by
      exact tsum_list_eq_tsum_twoCons_of_nil_singleton_zero _ hnil hsingle
    _ = ∑' x : (ℕ+ × ℕ+) × List ℕ+,
          ((taoSection7Geom2PairPMF x.1).toReal : ℂ) *
            taoSection7PairPhase N xi
              (taoSection7PairX N j
                (Int.ofNat
                  (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)))) x.1.2 *
            (((geom2PNatListPMF k x.2).toReal : ℂ) *
              unitSourcePairExpansionFrom N xi τ
                ⟨(j : ℕ) + 1, by omega⟩
                (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)) x.2) := by
      apply tsum_congr
      rintro ⟨⟨a₁, a₂⟩, tail⟩
      rw [show k + 2 = (k + 1) + 1 by omega,
        geom2PNatListPMF_succ_apply_cons,
        geom2PNatListPMF_succ_apply_cons,
        ENNReal.toReal_mul, ENNReal.toReal_mul,
        unitSourcePairExpansionFrom]
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
                unitSourcePairExpansionFrom N xi τ
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
              unitSourcePairExpansionFrom N xi τ
                ⟨(j : ℕ) + 1, by omega⟩
                (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)) x.2) := by
        refine Summable.of_norm_bounded hmass ?_
        intro x
        rw [norm_mul, norm_mul, norm_mul,
          norm_unitSourcePairExpansionFrom_eq_one]
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
                unitSourcePairExpansionFrom N xi τ
                  ⟨(j : ℕ) + 1, by omega⟩
                  (s + (a.1 : ℕ) + (a.2 : ℕ)) tail) := by
        intro a
        exact (unitSourcePairExpectation_summable N xi τ k
          ⟨(j : ℕ) + 1, by omega⟩
          (s + (a.1 : ℕ) + (a.2 : ℕ))).mul_left
            (((taoSection7Geom2PairPMF a).toReal : ℂ) *
              taoSection7PairPhase N xi
                (taoSection7PairX N j
                  (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2)
      rw [Summable.tsum_prod' hsum hfiber]
      apply tsum_congr
      intro a
      dsimp only
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

theorem norm_unitSourcePairExpectation_le_one
    (N : ℕ) (xi : ZMod (3 ^ N)) (τ : UnitSourceTerminalPhase) (k : ℕ) (j : ℕ+) (s : ℕ) :
    ‖unitSourcePairExpectation N xi τ k j s‖ ≤ 1 := by
  unfold unitSourcePairExpectation
  calc
    ‖∑' as : List ℕ+,
        ((geom2PNatListPMF k as).toReal : ℂ) *
          unitSourcePairExpansionFrom N xi τ j s as‖ ≤
        ∑' as : List ℕ+,
          ‖((geom2PNatListPMF k as).toReal : ℂ) *
            unitSourcePairExpansionFrom N xi τ j s as‖ :=
      norm_tsum_le_tsum_norm
        (unitSourcePairExpectation_summable N xi τ k j s).norm
    _ = ∑' as : List ℕ+, (geom2PNatListPMF k as).toReal := by
      apply tsum_congr
      intro as
      rw [norm_mul, norm_unitSourcePairExpansionFrom_eq_one]
      simp
    _ = 1 := by
      exact pmf_tsum_toReal_eq_one (geom2PNatListPMF k)

private theorem unitSourcePairExpectation_add_two_eq_fiber_tsum
    (N : ℕ) (xi : ZMod (3 ^ N)) (τ : UnitSourceTerminalPhase) (k : ℕ) (j : ℕ+) (s : ℕ) :
    unitSourcePairExpectation N xi τ (k + 2) j s =
      ∑' b : ℕ,
        taoSection7PairFiberCharacterMass N xi
            (taoSection7PairX N j (Int.ofNat (s + b))) b *
          unitSourcePairExpectation N xi τ k
            ⟨(j : ℕ) + 1, by omega⟩ (s + b) := by
  rw [unitSourcePairExpectation_add_two_eq_pair_tsum]
  simpa [add_assoc] using
    taoSection7Pair_tsum_eq_fiber_tsum N xi j s
      (fun b => unitSourcePairExpectation N xi τ k
        ⟨(j : ℕ) + 1, by omega⟩ (s + b))
      (fun b => norm_unitSourcePairExpectation_le_one
        N xi τ k ⟨(j : ℕ) + 1, by omega⟩ (s + b))

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

theorem norm_unitSourcePairExpectation_le_sourceEnvelope
    (N : ℕ) (xi : ZMod (3 ^ N)) (τ : UnitSourceTerminalPhase) :
    ∀ (k : ℕ) (j : ℕ+) (s : ℕ),
      ‖unitSourcePairExpectation N xi τ k j s‖ ≤
        taoSection7PairSourceEnvelope N xi (k / 2) (j : ℕ) s := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro j s
      rw [taoSection7PairSourceEnvelope_zero]
      exact norm_unitSourcePairExpectation_le_one N xi τ 0 j s
  | one =>
      intro j s
      rw [taoSection7PairSourceEnvelope_zero]
      exact norm_unitSourcePairExpectation_le_one N xi τ 1 j s
  | more k ih _ihSucc =>
      intro j s
      rw [unitSourcePairExpectation_add_two_eq_fiber_tsum]
      rw [show (k + 2) / 2 = k / 2 + 1 by omega]
      rw [taoSection7PairSourceEnvelope_succ]
      let T : ℕ → ℂ := fun b =>
        taoSection7PairFiberCharacterMass N xi
            (taoSection7PairX N j (Int.ofNat (s + b))) b *
          unitSourcePairExpectation N xi τ k
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
              ‖unitSourcePairExpectation N xi τ k
                ⟨(j : ℕ) + 1, by omega⟩ (s + b)‖ ≤
              ((taoSection7PascalSourcePMF b).toReal *
                taoSection7SourceFThreeFactor N xi (j : ℕ) s b) * 1 := by
            exact mul_le_mul
              (norm_taoSection7PairFiberCharacterMass_le_sourceFactor
                N xi j s b)
              (norm_unitSourcePairExpectation_le_one N xi τ k
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


private theorem unitSourcePairEnvelope_row_summable
    (N : ℕ) (xi : ZMod (3 ^ N)) (m j s : ℕ) :
    Summable fun b : ℕ =>
      (taoSection7PascalSourcePMF b).toReal *
        taoSection7SourceFThreeFactor N xi j s b *
        taoSection7PairSourceEnvelope N xi m (j + 1) (s + b) := by
  refine Summable.of_norm_bounded
    (pmf_summable_toReal taoSection7PascalSourcePMF) ?_
  intro b
  have hF0 := taoSection7SourceFThreeFactor_nonneg N xi j s b
  have hF1 := taoSection7SourceFThreeFactor_le_one N xi j s b
  have hE0 := taoSection7PairSourceEnvelope_nonneg N xi m (j + 1) (s + b)
  have hE1 := taoSection7PairSourceEnvelope_le_one N xi m (j + 1) (s + b)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (taoSection7PascalSourcePMF b).toReal * 1 * 1 := by gcongr
    _ = _ := by ring

/-- An extra pair has expected raw cancellation factor at least 3/4,
uniformly in the current state, because only the Pascal atom b=3 can reduce it. -/
theorem unitSourcePairEnvelope_one_ge_three_quarters
    (N : ℕ) (xi : ZMod (3 ^ N)) (j s : ℕ) :
    (3 / 4 : ℝ) ≤ taoSection7PairSourceEnvelope N xi 1 j s := by
  let F : ℕ → ℝ := fun b =>
    (taoSection7PascalSourcePMF b).toReal *
      taoSection7SourceFThreeFactor N xi j s b
  let G : ℕ → ℝ := fun b => if b = 3 then (taoSection7PascalSourcePMF b).toReal else 0
  have hF : Summable F := by
    simpa only [F, taoSection7PairSourceEnvelope_zero, mul_one] using
      unitSourcePairEnvelope_row_summable N xi 0 j s
  have hG : Summable G := by
    apply summable_of_ne_finset_zero (s := {3})
    intro b hb
    simp only [Finset.mem_singleton] at hb
    simp [G, hb]
  have hpoint : ∀ b, (taoSection7PascalSourcePMF b).toReal ≤ F b + G b := by
    intro b
    by_cases hb : b = 3
    · have hnonneg := mul_nonneg (ENNReal.toReal_nonneg (a := taoSection7PascalSourcePMF b))
        (taoSection7SourceFThreeFactor_nonneg N xi j s b)
      simp only [F, G, if_pos hb]
      linarith
    · have hf : taoSection7SourceFThreeFactor N xi j s b = 1 := by
        unfold taoSection7SourceFThreeFactor
        rw [dif_neg (by intro h; exact hb h.1)]
      simp [F, G, hb, hf]
  have hsum := (pmf_summable_toReal taoSection7PascalSourcePMF).tsum_le_tsum
    hpoint (hF.add hG)
  rw [pmf_tsum_toReal_eq_one, hF.tsum_add hG] at hsum
  have hGsum : (∑' b, G b) = (1 / 4 : ℝ) := by
    rw [tsum_eq_single 3]
    · simp [G, taoSection7PascalSourcePMF_three_toReal]
    · intro b hb
      simp [G, hb]
  have hE : taoSection7PairSourceEnvelope N xi 1 j s = ∑' b, F b := by
    rw [show 1 = 0 + 1 by omega, taoSection7PairSourceEnvelope_succ]
    simp only [taoSection7PairSourceEnvelope_zero, mul_one]
    rfl
  rw [hGsum, ← hE] at hsum
  linarith

/-- Appending one raw Pascal pair costs at most 4/3, uniformly in all
source-history coordinates. This compares continuation envelopes, not
individual possibly zero character factors. -/
theorem unitSourcePairEnvelope_le_four_thirds_succ
    (N : ℕ) (xi : ZMod (3 ^ N)) :
    ∀ (m j s : ℕ), taoSection7PairSourceEnvelope N xi m j s ≤
      (4 / 3 : ℝ) * taoSection7PairSourceEnvelope N xi (m + 1) j s := by
  intro m
  induction m with
  | zero =>
      intro j s
      rw [taoSection7PairSourceEnvelope_zero]
      have h := unitSourcePairEnvelope_one_ge_three_quarters N xi j s
      norm_num at ⊢
      linarith
  | succ m ih =>
      intro j s
      calc
        taoSection7PairSourceEnvelope N xi (m + 1) j s =
            ∑' b : ℕ, (taoSection7PascalSourcePMF b).toReal *
              taoSection7SourceFThreeFactor N xi j s b *
              taoSection7PairSourceEnvelope N xi m (j + 1) (s + b) :=
          taoSection7PairSourceEnvelope_succ N xi m j s
        _ ≤ ∑' b : ℕ, (4 / 3 : ℝ) *
              ((taoSection7PascalSourcePMF b).toReal *
                taoSection7SourceFThreeFactor N xi j s b *
                taoSection7PairSourceEnvelope N xi (m + 1) (j + 1) (s + b)) := by
          apply (unitSourcePairEnvelope_row_summable N xi m j s).tsum_le_tsum
          · intro b
            have h := mul_le_mul_of_nonneg_left (ih (j + 1) (s + b))
              (mul_nonneg (ENNReal.toReal_nonneg (a := taoSection7PascalSourcePMF b))
                (taoSection7SourceFThreeFactor_nonneg N xi j s b))
            convert h using 1
            ring
          · exact (unitSourcePairEnvelope_row_summable N xi (m + 1) j s).mul_left _
        _ = (4 / 3 : ℝ) * taoSection7PairSourceEnvelope N xi (m + 1 + 1) j s := by
          rw [tsum_mul_left, ← taoSection7PairSourceEnvelope_succ]

theorem unitSourcePairEnvelope_deficit_one
    (N : ℕ) (xi : ZMod (3 ^ N)) (j s : ℕ) :
    taoSection7PairSourceEnvelope N xi ((N - 1) / 2) j s ≤
      (4 / 3 : ℝ) * taoSection7PairSourceEnvelope N xi (N / 2) j s := by
  by_cases he : (N - 1) / 2 = N / 2
  · rw [he]
    have h := taoSection7PairSourceEnvelope_nonneg N xi (N / 2) j s
    nlinarith
  · have hs : N / 2 = (N - 1) / 2 + 1 := by omega
    rw [hs]
    exact unitSourcePairEnvelope_le_four_thirds_succ N xi ((N - 1) / 2) j s

end Tao
end Erdos1135
