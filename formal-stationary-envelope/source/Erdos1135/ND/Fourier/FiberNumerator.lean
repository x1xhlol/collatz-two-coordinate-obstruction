import Erdos1135.ND.Statement
import Erdos1135.Tao.Fourier.Section7SChiActualQ

/-!
# Fixed-Total Section 7 Numerator

This leaf inserts the fixed-total selector before any absolute value is
taken. It retains the ambient modulus while the remaining valuation length
drops, so the checked adjacent-pair cancellation can be reused without
conditioning the public Proposition 1.17 conclusion.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

/-- Unnormalized Section 7 character numerator from source state `(j,s)`,
restricted to valuation tails whose remaining total is exactly `R`.

The accumulated total `s` is deliberately separate from `R`: after removing
a pair of total `b`, later phases start from `s+b` while the selector becomes
`R-b`. -/
noncomputable def ndSection7FiberNumeratorFrom
    (N : ℕ) (xi : ZMod (3 ^ N)) (k : ℕ)
    (j : ℕ+) (s R : ℕ) : ℂ :=
  ∑' as : List ℕ+,
    if Tao.taoTupleWeight as = R then
      ((Tao.geom2PNatListPMF k as).toReal : ℂ) *
        Tao.taoSection7PairExpansionFrom N xi j s as
    else
      0

private theorem pmf_tsum_toReal_eq_one
    {alpha : Type*} (p : PMF alpha) :
    (∑' a : alpha, (p a).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq]
  · rw [PMF.tsum_coe]
    norm_num
  · intro a
    exact PMF.apply_ne_top p a

theorem ndSection7FiberNumeratorFrom_summable
    (N : ℕ) (xi : ZMod (3 ^ N)) (k : ℕ)
    (j : ℕ+) (s R : ℕ) :
    Summable fun as : List ℕ+ =>
      if Tao.taoTupleWeight as = R then
        ((Tao.geom2PNatListPMF k as).toReal : ℂ) *
          Tao.taoSection7PairExpansionFrom N xi j s as
      else
        0 := by
  refine Summable.of_norm_bounded
    (Tao.pmf_summable_toReal (Tao.geom2PNatListPMF k)) ?_
  intro as
  by_cases htotal : Tao.taoTupleWeight as = R
  · rw [if_pos htotal, norm_mul,
      Tao.norm_taoSection7PairExpansionFrom_eq_one]
    simp
  · simp [htotal]

/-- A selected numerator is bounded by total source mass one. This is the
base estimate for both `k = 0` and the odd singleton `k = 1`; the singleton's
pinned terminal character has norm exactly one. -/
theorem norm_ndSection7FiberNumeratorFrom_le_one
    (N : ℕ) (xi : ZMod (3 ^ N)) (k : ℕ)
    (j : ℕ+) (s R : ℕ) :
    ‖ndSection7FiberNumeratorFrom N xi k j s R‖ ≤ 1 := by
  unfold ndSection7FiberNumeratorFrom
  calc
    ‖∑' as : List ℕ+,
        if Tao.taoTupleWeight as = R then
          ((Tao.geom2PNatListPMF k as).toReal : ℂ) *
            Tao.taoSection7PairExpansionFrom N xi j s as
        else 0‖ ≤
        ∑' as : List ℕ+,
          ‖if Tao.taoTupleWeight as = R then
            ((Tao.geom2PNatListPMF k as).toReal : ℂ) *
              Tao.taoSection7PairExpansionFrom N xi j s as
          else 0‖ :=
      norm_tsum_le_tsum_norm
        (ndSection7FiberNumeratorFrom_summable N xi k j s R).norm
    _ ≤ ∑' as : List ℕ+,
          (Tao.geom2PNatListPMF k as).toReal := by
      exact (ndSection7FiberNumeratorFrom_summable N xi k j s R).norm.tsum_le_tsum
        (fun as => by
          by_cases htotal : Tao.taoTupleWeight as = R
          · rw [if_pos htotal, norm_mul,
              Tao.norm_taoSection7PairExpansionFrom_eq_one]
            simp
          · simp [htotal])
        (Tao.pmf_summable_toReal (Tao.geom2PNatListPMF k))
    _ = 1 := pmf_tsum_toReal_eq_one _

private theorem tsum_list_eq_tsum_twoCons_of_nil_singleton_zero
    {alpha E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E]
    (f : List alpha → E) (h0 : f [] = 0) (h1 : ∀ a, f [a] = 0) :
    (∑' as : List alpha, f as) =
      ∑' x : (alpha × alpha) × List alpha,
        f (x.1.1 :: x.1.2 :: x.2) := by
  classical
  let g : (alpha × alpha) × List alpha → List alpha :=
    fun x => x.1.1 :: x.1.2 :: x.2
  have hg : Function.Injective g := by
    rintro ⟨⟨a1, a2⟩, as⟩ ⟨⟨b1, b2⟩, bs⟩ hab
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

/-- Before grouping ordered pairs by their total, the selected numerator
splits into the first pair and a selected tail. The guard `b ≤ R` is retained
explicitly so natural subtraction never creates a false fiber. -/
theorem ndSection7FiberNumeratorFrom_add_two_eq_pair_tsum
    (N : ℕ) (xi : ZMod (3 ^ N)) (k : ℕ)
    (j : ℕ+) (s R : ℕ) :
    ndSection7FiberNumeratorFrom N xi (k + 2) j s R =
      ∑' a : ℕ+ × ℕ+,
        if (a.1 : ℕ) + (a.2 : ℕ) ≤ R then
          ((Tao.taoSection7Geom2PairPMF a).toReal : ℂ) *
            Tao.taoSection7PairPhase N xi
              (Tao.taoSection7PairX N j
                (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
            ndSection7FiberNumeratorFrom N xi k
              ⟨(j : ℕ) + 1, by omega⟩
              (s + (a.1 : ℕ) + (a.2 : ℕ))
              (R - ((a.1 : ℕ) + (a.2 : ℕ)))
        else
          0 := by
  unfold ndSection7FiberNumeratorFrom
  have hnil :
      (if Tao.taoTupleWeight [] = R then
        ((Tao.geom2PNatListPMF (k + 2) []).toReal : ℂ) *
          Tao.taoSection7PairExpansionFrom N xi j s []
      else 0) = 0 := by
    by_cases htotal : Tao.taoTupleWeight [] = R
    · rw [if_pos htotal, show k + 2 = (k + 1) + 1 by omega,
        Tao.geom2PNatListPMF_succ_apply_nil]
      simp
    · simp [htotal]
  have hsingle : ∀ a : ℕ+,
      (if Tao.taoTupleWeight [a] = R then
        ((Tao.geom2PNatListPMF (k + 2) [a]).toReal : ℂ) *
          Tao.taoSection7PairExpansionFrom N xi j s [a]
      else 0) = 0 := by
    intro a
    by_cases htotal : Tao.taoTupleWeight [a] = R
    · rw [if_pos htotal, show k + 2 = (k + 1) + 1 by omega,
        Tao.geom2PNatListPMF_succ_apply_cons,
        Tao.geom2PNatListPMF_succ_apply_nil]
      simp
    · simp [htotal]
  calc
    (∑' as : List ℕ+,
        if Tao.taoTupleWeight as = R then
          ((Tao.geom2PNatListPMF (k + 2) as).toReal : ℂ) *
            Tao.taoSection7PairExpansionFrom N xi j s as
        else 0) =
        ∑' x : (ℕ+ × ℕ+) × List ℕ+,
          if Tao.taoTupleWeight (x.1.1 :: x.1.2 :: x.2) = R then
            ((Tao.geom2PNatListPMF (k + 2)
              (x.1.1 :: x.1.2 :: x.2)).toReal : ℂ) *
              Tao.taoSection7PairExpansionFrom N xi j s
                (x.1.1 :: x.1.2 :: x.2)
          else 0 := by
      exact tsum_list_eq_tsum_twoCons_of_nil_singleton_zero _ hnil hsingle
    _ = ∑' x : (ℕ+ × ℕ+) × List ℕ+,
        if (x.1.1 : ℕ) + (x.1.2 : ℕ) ≤ R then
          ((Tao.taoSection7Geom2PairPMF x.1).toReal : ℂ) *
            Tao.taoSection7PairPhase N xi
              (Tao.taoSection7PairX N j
                (Int.ofNat
                  (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)))) x.1.2 *
            (if Tao.taoTupleWeight x.2 =
                R - ((x.1.1 : ℕ) + (x.1.2 : ℕ)) then
              ((Tao.geom2PNatListPMF k x.2).toReal : ℂ) *
                Tao.taoSection7PairExpansionFrom N xi
                  ⟨(j : ℕ) + 1, by omega⟩
                  (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)) x.2
            else 0)
        else 0 := by
      apply tsum_congr
      rintro ⟨⟨a1, a2⟩, tail⟩
      have hweight :
          Tao.taoTupleWeight (a1 :: a2 :: tail) =
            (a1 : ℕ) + (a2 : ℕ) + Tao.taoTupleWeight tail := by
        simp [Tao.taoTupleWeight, add_assoc]
      rw [show k + 2 = (k + 1) + 1 by omega,
        Tao.geom2PNatListPMF_succ_apply_cons,
        Tao.geom2PNatListPMF_succ_apply_cons,
        ENNReal.toReal_mul, ENNReal.toReal_mul,
        Tao.taoSection7PairExpansionFrom,
        Tao.taoSection7Geom2PairPMF_apply_toReal,
        hweight]
      unfold Tao.geom2PNatPairMass
      by_cases hpair : (a1 : ℕ) + (a2 : ℕ) ≤ R
      · by_cases htail : Tao.taoTupleWeight tail =
            R - ((a1 : ℕ) + (a2 : ℕ))
        · have htotal :
              (a1 : ℕ) + (a2 : ℕ) + Tao.taoTupleWeight tail = R := by
            omega
          rw [if_pos htotal, if_pos hpair, if_pos htail]
          push_cast
          ring
        · have htotal :
              (a1 : ℕ) + (a2 : ℕ) + Tao.taoTupleWeight tail ≠ R := by
            intro h
            apply htail
            omega
          rw [if_neg htotal, if_pos hpair, if_neg htail]
          simp
      · have htotal :
            (a1 : ℕ) + (a2 : ℕ) + Tao.taoTupleWeight tail ≠ R := by
          omega
        rw [if_neg htotal, if_neg hpair]
    _ = ∑' a : ℕ+ × ℕ+,
        if (a.1 : ℕ) + (a.2 : ℕ) ≤ R then
          ((Tao.taoSection7Geom2PairPMF a).toReal : ℂ) *
            Tao.taoSection7PairPhase N xi
              (Tao.taoSection7PairX N j
                (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
            ndSection7FiberNumeratorFrom N xi k
              ⟨(j : ℕ) + 1, by omega⟩
              (s + (a.1 : ℕ) + (a.2 : ℕ))
              (R - ((a.1 : ℕ) + (a.2 : ℕ)))
        else 0 := by
      have hmass : Summable fun x : (ℕ+ × ℕ+) × List ℕ+ =>
          (Tao.taoSection7Geom2PairPMF x.1).toReal *
            (Tao.geom2PNatListPMF k x.2).toReal :=
        Summable.mul_of_nonneg
          (f := fun a : ℕ+ × ℕ+ =>
            (Tao.taoSection7Geom2PairPMF a).toReal)
          (g := fun tail : List ℕ+ =>
            (Tao.geom2PNatListPMF k tail).toReal)
          (Tao.pmf_summable_toReal Tao.taoSection7Geom2PairPMF)
          (Tao.pmf_summable_toReal (Tao.geom2PNatListPMF k))
          (fun _ => ENNReal.toReal_nonneg)
          (fun _ => ENNReal.toReal_nonneg)
      have hsum : Summable fun x : (ℕ+ × ℕ+) × List ℕ+ =>
          if (x.1.1 : ℕ) + (x.1.2 : ℕ) ≤ R then
            ((Tao.taoSection7Geom2PairPMF x.1).toReal : ℂ) *
              Tao.taoSection7PairPhase N xi
                (Tao.taoSection7PairX N j
                  (Int.ofNat
                    (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)))) x.1.2 *
              (if Tao.taoTupleWeight x.2 =
                  R - ((x.1.1 : ℕ) + (x.1.2 : ℕ)) then
                ((Tao.geom2PNatListPMF k x.2).toReal : ℂ) *
                  Tao.taoSection7PairExpansionFrom N xi
                    ⟨(j : ℕ) + 1, by omega⟩
                    (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)) x.2
              else 0)
          else 0 := by
        refine Summable.of_norm_bounded hmass ?_
        intro x
        by_cases hpair : (x.1.1 : ℕ) + (x.1.2 : ℕ) ≤ R
        · by_cases htail : Tao.taoTupleWeight x.2 =
              R - ((x.1.1 : ℕ) + (x.1.2 : ℕ))
          · rw [if_pos hpair, if_pos htail, norm_mul, norm_mul, norm_mul,
              Tao.norm_taoSection7PairExpansionFrom_eq_one]
            have hphase : ‖Tao.taoSection7PairPhase N xi
                (Tao.taoSection7PairX N j
                  (Int.ofNat
                    (s + (x.1.1 : ℕ) + (x.1.2 : ℕ)))) x.1.2‖ = 1 := by
              unfold Tao.taoSection7PairPhase
              exact Tao.norm_taoForwardDFTKernel_eq_one _ _
            rw [hphase]
            simp
          · rw [if_pos hpair, if_neg htail, mul_zero, norm_zero]
            exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        · rw [if_neg hpair, norm_zero]
          exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have hfiber : ∀ a : ℕ+ × ℕ+,
          Summable fun tail : List ℕ+ =>
            if (a.1 : ℕ) + (a.2 : ℕ) ≤ R then
              ((Tao.taoSection7Geom2PairPMF a).toReal : ℂ) *
                Tao.taoSection7PairPhase N xi
                  (Tao.taoSection7PairX N j
                    (Int.ofNat
                      (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
                (if Tao.taoTupleWeight tail =
                    R - ((a.1 : ℕ) + (a.2 : ℕ)) then
                  ((Tao.geom2PNatListPMF k tail).toReal : ℂ) *
                    Tao.taoSection7PairExpansionFrom N xi
                      ⟨(j : ℕ) + 1, by omega⟩
                      (s + (a.1 : ℕ) + (a.2 : ℕ)) tail
                else 0)
            else 0 := by
        intro a
        by_cases hpair : (a.1 : ℕ) + (a.2 : ℕ) ≤ R
        · rw [show (fun tail : List ℕ+ =>
              if (a.1 : ℕ) + (a.2 : ℕ) ≤ R then
                ((Tao.taoSection7Geom2PairPMF a).toReal : ℂ) *
                  Tao.taoSection7PairPhase N xi
                    (Tao.taoSection7PairX N j
                      (Int.ofNat
                        (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
                  (if Tao.taoTupleWeight tail =
                      R - ((a.1 : ℕ) + (a.2 : ℕ)) then
                    ((Tao.geom2PNatListPMF k tail).toReal : ℂ) *
                      Tao.taoSection7PairExpansionFrom N xi
                        ⟨(j : ℕ) + 1, by omega⟩
                        (s + (a.1 : ℕ) + (a.2 : ℕ)) tail
                  else 0)
              else 0) = fun tail =>
                ((Tao.taoSection7Geom2PairPMF a).toReal : ℂ) *
                  Tao.taoSection7PairPhase N xi
                    (Tao.taoSection7PairX N j
                      (Int.ofNat
                        (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
                  (if Tao.taoTupleWeight tail =
                      R - ((a.1 : ℕ) + (a.2 : ℕ)) then
                    ((Tao.geom2PNatListPMF k tail).toReal : ℂ) *
                      Tao.taoSection7PairExpansionFrom N xi
                        ⟨(j : ℕ) + 1, by omega⟩
                        (s + (a.1 : ℕ) + (a.2 : ℕ)) tail
                  else 0) by funext tail; rw [if_pos hpair]]
          exact (ndSection7FiberNumeratorFrom_summable N xi k
            ⟨(j : ℕ) + 1, by omega⟩
            (s + (a.1 : ℕ) + (a.2 : ℕ))
            (R - ((a.1 : ℕ) + (a.2 : ℕ)))).mul_left
              (((Tao.taoSection7Geom2PairPMF a).toReal : ℂ) *
                Tao.taoSection7PairPhase N xi
                  (Tao.taoSection7PairX N j
                    (Int.ofNat
                      (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2)
        · simp [hpair]
      rw [Summable.tsum_prod' hsum hfiber]
      apply tsum_congr
      intro a
      simp only
      by_cases hpair : (a.1 : ℕ) + (a.2 : ℕ) ≤ R
      · simp_rw [if_pos hpair]
        rw [tsum_mul_left]
        rfl
      · simp [hpair]

private theorem ndSection7Pair_tsum_eq_fiber_tsum
    (N : ℕ) (xi : ZMod (3 ^ N)) (j : ℕ+) (s : ℕ)
    (G : ℕ → ℂ) (hG : ∀ b, ‖G b‖ ≤ 1) :
    (∑' a : ℕ+ × ℕ+,
        ((Tao.taoSection7Geom2PairPMF a).toReal : ℂ) *
          Tao.taoSection7PairPhase N xi
            (Tao.taoSection7PairX N j
              (Int.ofNat (s + (a.1 : ℕ) + (a.2 : ℕ)))) a.2 *
          G ((a.1 : ℕ) + (a.2 : ℕ))) =
      ∑' b : ℕ,
        Tao.taoSection7PairFiberCharacterMass N xi
          (Tao.taoSection7PairX N j (Int.ofNat (s + b))) b * G b := by
  classical
  let F : ℕ → (ℕ+ × ℕ+) → ℂ := fun b a =>
    if b = (a.1 : ℕ) + (a.2 : ℕ) then
      ((Tao.taoSection7Geom2PairPMF a).toReal : ℂ) *
        Tao.taoSection7PairPhase N xi
          (Tao.taoSection7PairX N j (Int.ofNat (s + b))) a.2 * G b
    else
      0
  let M : ℕ × (ℕ+ × ℕ+) → ℝ := fun x =>
    if x.1 = (x.2.1 : ℕ) + (x.2.2 : ℕ) then
      (Tao.taoSection7Geom2PairPMF x.2).toReal
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
        (Tao.pmf_summable_toReal Tao.taoSection7Geom2PairPMF) ?_
      intro a
      simp only [M]
      by_cases h : b = (a.1 : ℕ) + (a.2 : ℕ) <;>
        simp [h, ENNReal.toReal_nonneg]
    · have hmap := Tao.pmf_summable_toReal
        (Tao.taoSection7Geom2PairPMF.map
          (fun a => (a.1 : ℕ) + (a.2 : ℕ)))
      refine hmap.congr ?_
      intro b
      rw [Tao.pmf_map_apply_toReal_tsum]
  have hF : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded hM ?_
    rintro ⟨b, a⟩
    simp only [Function.uncurry_apply_pair, F, M]
    by_cases h : b = (a.1 : ℕ) + (a.2 : ℕ)
    · rw [if_pos h, if_pos h, norm_mul, norm_mul]
      have hphase : ‖Tao.taoSection7PairPhase N xi
          (Tao.taoSection7PairX N j (Int.ofNat (s + b))) a.2‖ = 1 := by
        unfold Tao.taoSection7PairPhase
        exact Tao.norm_taoForwardDFTKernel_eq_one _ _
      rw [hphase, mul_one]
      simpa [ENNReal.toReal_nonneg] using
        mul_le_of_le_one_right
          (show 0 ≤ (Tao.taoSection7Geom2PairPMF a).toReal from
            ENNReal.toReal_nonneg) (hG b)
    · simp [h]
  have hrow : ∀ b, Summable (F b) := by
    intro b
    refine Summable.of_norm_bounded
      (Tao.pmf_summable_toReal Tao.taoSection7Geom2PairPMF) ?_
    intro a
    simp only [F]
    by_cases h : b = (a.1 : ℕ) + (a.2 : ℕ)
    · rw [if_pos h, norm_mul, norm_mul]
      have hphase : ‖Tao.taoSection7PairPhase N xi
          (Tao.taoSection7PairX N j (Int.ofNat (s + b))) a.2‖ = 1 := by
        unfold Tao.taoSection7PairPhase
        exact Tao.norm_taoForwardDFTKernel_eq_one _ _
      rw [hphase, mul_one]
      simpa [ENNReal.toReal_nonneg] using
        mul_le_of_le_one_right
          (show 0 ≤ (Tao.taoSection7Geom2PairPMF a).toReal from
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
        ((Tao.taoSection7Geom2PairPMF a).toReal : ℂ) *
          Tao.taoSection7PairPhase N xi
            (Tao.taoSection7PairX N j
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
        Tao.taoSection7PairFiberCharacterMass N xi
          (Tao.taoSection7PairX N j (Int.ofNat (s + b))) b * G b := by
      apply tsum_congr
      intro b
      unfold Tao.taoSection7PairFiberCharacterMass
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

/-- Exact selector-preserving recurrence after grouping the first ordered
pair by its total. This is the fixed-fiber analogue of the private inherited
Section 7 recurrence. -/
theorem ndSection7FiberNumeratorFrom_add_two
    (N : ℕ) (xi : ZMod (3 ^ N)) (k : ℕ)
    (j : ℕ+) (s R : ℕ) :
    ndSection7FiberNumeratorFrom N xi (k + 2) j s R =
      ∑' b : ℕ,
        if b ≤ R then
          Tao.taoSection7PairFiberCharacterMass N xi
              (Tao.taoSection7PairX N j (Int.ofNat (s + b))) b *
            ndSection7FiberNumeratorFrom N xi k
              ⟨(j : ℕ) + 1, by omega⟩ (s + b) (R - b)
        else
          0 := by
  rw [ndSection7FiberNumeratorFrom_add_two_eq_pair_tsum]
  let G : ℕ → ℂ := fun b =>
    if b ≤ R then
      ndSection7FiberNumeratorFrom N xi k
        ⟨(j : ℕ) + 1, by omega⟩ (s + b) (R - b)
    else
      0
  have hG : ∀ b, ‖G b‖ ≤ 1 := by
    intro b
    by_cases hb : b ≤ R
    · simpa [G, hb] using
        norm_ndSection7FiberNumeratorFrom_le_one N xi k
          ⟨(j : ℕ) + 1, by omega⟩ (s + b) (R - b)
    · simp [G, hb]
  simpa [G, mul_ite, Nat.add_assoc] using
    ndSection7Pair_tsum_eq_fiber_tsum N xi j s G hG

private theorem tsum_list_eq_tsum_cons_of_nil_zero
    {alpha E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E]
    (f : List alpha → E) (h0 : f [] = 0) :
    (∑' as : List alpha, f as) =
      ∑' x : alpha × List alpha, f (x.1 :: x.2) := by
  classical
  let g : alpha × List alpha → List alpha := fun x => x.1 :: x.2
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

private theorem ndSection7PairSourceEnvelope_summable
    (N : ℕ) (xi : ZMod (3 ^ N)) (m j s : ℕ) :
    Summable fun bs : List ℕ =>
      (Tao.taoSection7PascalSourceListPMF m bs).toReal *
        Tao.taoSection7FactorProductFrom
          (Tao.taoSection7SourceFThreeFactor N xi) j s bs := by
  refine Summable.of_norm_bounded
    (Tao.pmf_summable_toReal (Tao.taoSection7PascalSourceListPMF m)) ?_
  intro bs
  have hnonneg := Tao.taoSection7FactorProductFrom_nonneg
    (Tao.taoSection7SourceFThreeFactor_nonneg N xi) j s bs
  have hle := Tao.taoSection7FactorProductFrom_le_one
    (Tao.taoSection7SourceFThreeFactor_nonneg N xi)
    (Tao.taoSection7SourceFThreeFactor_le_one N xi) j s bs
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg ENNReal.toReal_nonneg hnonneg)]
  simpa using mul_le_of_le_one_right ENNReal.toReal_nonneg hle

private theorem ndSection7PairSourceEnvelope_succ
    (N : ℕ) (xi : ZMod (3 ^ N)) (m j s : ℕ) :
    Tao.taoSection7PairSourceEnvelope N xi (m + 1) j s =
      ∑' b : ℕ,
        (Tao.taoSection7PascalSourcePMF b).toReal *
          Tao.taoSection7SourceFThreeFactor N xi j s b *
          Tao.taoSection7PairSourceEnvelope N xi m (j + 1) (s + b) := by
  unfold Tao.taoSection7PairSourceEnvelope
  have hnil :
      (Tao.taoSection7PascalSourceListPMF (m + 1) []).toReal *
          Tao.taoSection7FactorProductFrom
            (Tao.taoSection7SourceFThreeFactor N xi) j s [] = 0 := by
    rw [Tao.taoSection7PascalSourceListPMF_succ_apply_nil]
    simp
  calc
    (∑' bs : List ℕ,
        (Tao.taoSection7PascalSourceListPMF (m + 1) bs).toReal *
          Tao.taoSection7FactorProductFrom
            (Tao.taoSection7SourceFThreeFactor N xi) j s bs) =
        ∑' x : ℕ × List ℕ,
          (Tao.taoSection7PascalSourceListPMF (m + 1)
              (x.1 :: x.2)).toReal *
            Tao.taoSection7FactorProductFrom
              (Tao.taoSection7SourceFThreeFactor N xi) j s
              (x.1 :: x.2) := by
      exact tsum_list_eq_tsum_cons_of_nil_zero _ hnil
    _ = ∑' x : ℕ × List ℕ,
          (Tao.taoSection7PascalSourcePMF x.1).toReal *
            Tao.taoSection7SourceFThreeFactor N xi j s x.1 *
            ((Tao.taoSection7PascalSourceListPMF m x.2).toReal *
              Tao.taoSection7FactorProductFrom
                (Tao.taoSection7SourceFThreeFactor N xi)
                (j + 1) (s + x.1) x.2) := by
      apply tsum_congr
      intro x
      rw [Tao.taoSection7PascalSourceListPMF_succ_apply_cons,
        ENNReal.toReal_mul, Tao.taoSection7FactorProductFrom]
      ring
    _ = ∑' b : ℕ,
          (Tao.taoSection7PascalSourcePMF b).toReal *
            Tao.taoSection7SourceFThreeFactor N xi j s b *
            (∑' bs : List ℕ,
              (Tao.taoSection7PascalSourceListPMF m bs).toReal *
                Tao.taoSection7FactorProductFrom
                  (Tao.taoSection7SourceFThreeFactor N xi)
                  (j + 1) (s + b) bs) := by
      have hmass : Summable fun x : ℕ × List ℕ =>
          (Tao.taoSection7PascalSourcePMF x.1).toReal *
            (Tao.taoSection7PascalSourceListPMF m x.2).toReal :=
        Summable.mul_of_nonneg
          (f := fun b : ℕ => (Tao.taoSection7PascalSourcePMF b).toReal)
          (g := fun bs : List ℕ =>
            (Tao.taoSection7PascalSourceListPMF m bs).toReal)
          (Tao.pmf_summable_toReal Tao.taoSection7PascalSourcePMF)
          (Tao.pmf_summable_toReal (Tao.taoSection7PascalSourceListPMF m))
          (fun _ => ENNReal.toReal_nonneg)
          (fun _ => ENNReal.toReal_nonneg)
      have hsum : Summable fun x : ℕ × List ℕ =>
          (Tao.taoSection7PascalSourcePMF x.1).toReal *
            Tao.taoSection7SourceFThreeFactor N xi j s x.1 *
            ((Tao.taoSection7PascalSourceListPMF m x.2).toReal *
              Tao.taoSection7FactorProductFrom
                (Tao.taoSection7SourceFThreeFactor N xi)
                (j + 1) (s + x.1) x.2) := by
        refine Summable.of_norm_bounded hmass ?_
        intro x
        have hF0 := Tao.taoSection7SourceFThreeFactor_nonneg N xi j s x.1
        have hF1 := Tao.taoSection7SourceFThreeFactor_le_one N xi j s x.1
        have hP0 := Tao.taoSection7FactorProductFrom_nonneg
          (Tao.taoSection7SourceFThreeFactor_nonneg N xi)
          (j + 1) (s + x.1) x.2
        have hP1 := Tao.taoSection7FactorProductFrom_le_one
          (Tao.taoSection7SourceFThreeFactor_nonneg N xi)
          (Tao.taoSection7SourceFThreeFactor_le_one N xi)
          (j + 1) (s + x.1) x.2
        have hp0 : 0 ≤ (Tao.taoSection7PascalSourcePMF x.1).toReal :=
          ENNReal.toReal_nonneg
        have hq0 : 0 ≤ (Tao.taoSection7PascalSourceListPMF m x.2).toReal :=
          ENNReal.toReal_nonneg
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc
          (Tao.taoSection7PascalSourcePMF x.1).toReal *
                Tao.taoSection7SourceFThreeFactor N xi j s x.1 *
              ((Tao.taoSection7PascalSourceListPMF m x.2).toReal *
                Tao.taoSection7FactorProductFrom
                  (Tao.taoSection7SourceFThreeFactor N xi)
                  (j + 1) (s + x.1) x.2) ≤
              (Tao.taoSection7PascalSourcePMF x.1).toReal * 1 *
                ((Tao.taoSection7PascalSourceListPMF m x.2).toReal * 1) := by
            gcongr
          _ = (Tao.taoSection7PascalSourcePMF x.1).toReal *
                (Tao.taoSection7PascalSourceListPMF m x.2).toReal := by ring
      have hfiber : ∀ b : ℕ, Summable fun bs : List ℕ =>
          (Tao.taoSection7PascalSourcePMF b).toReal *
            Tao.taoSection7SourceFThreeFactor N xi j s b *
            ((Tao.taoSection7PascalSourceListPMF m bs).toReal *
              Tao.taoSection7FactorProductFrom
                (Tao.taoSection7SourceFThreeFactor N xi)
                (j + 1) (s + b) bs) := by
        intro b
        exact (ndSection7PairSourceEnvelope_summable
          N xi m (j + 1) (s + b)).mul_left
            ((Tao.taoSection7PascalSourcePMF b).toReal *
              Tao.taoSection7SourceFThreeFactor N xi j s b)
      rw [Summable.tsum_prod' hsum hfiber]
      apply tsum_congr
      intro b
      simp only
      rw [tsum_mul_left]

private theorem ndSection7PairSourceEnvelope_nonneg
    (N : ℕ) (xi : ZMod (3 ^ N)) (m j s : ℕ) :
    0 ≤ Tao.taoSection7PairSourceEnvelope N xi m j s := by
  unfold Tao.taoSection7PairSourceEnvelope
  exact tsum_nonneg fun bs => mul_nonneg ENNReal.toReal_nonneg
    (Tao.taoSection7FactorProductFrom_nonneg
      (Tao.taoSection7SourceFThreeFactor_nonneg N xi) j s bs)

private theorem ndSection7PairSourceEnvelope_le_one
    (N : ℕ) (xi : ZMod (3 ^ N)) (m j s : ℕ) :
    Tao.taoSection7PairSourceEnvelope N xi m j s ≤ 1 := by
  unfold Tao.taoSection7PairSourceEnvelope
  calc
    (∑' bs : List ℕ,
        (Tao.taoSection7PascalSourceListPMF m bs).toReal *
          Tao.taoSection7FactorProductFrom
            (Tao.taoSection7SourceFThreeFactor N xi) j s bs) ≤
        ∑' bs : List ℕ,
          (Tao.taoSection7PascalSourceListPMF m bs).toReal := by
      exact (ndSection7PairSourceEnvelope_summable N xi m j s).tsum_le_tsum
        (fun bs => mul_le_of_le_one_right ENNReal.toReal_nonneg
          (Tao.taoSection7FactorProductFrom_le_one
            (Tao.taoSection7SourceFThreeFactor_nonneg N xi)
            (Tao.taoSection7SourceFThreeFactor_le_one N xi) j s bs))
        (Tao.pmf_summable_toReal (Tao.taoSection7PascalSourceListPMF m))
    _ = 1 := pmf_tsum_toReal_eq_one _

private theorem ndSection7PairSourceEnvelope_zero
    (N : ℕ) (xi : ZMod (3 ^ N)) (j s : ℕ) :
    Tao.taoSection7PairSourceEnvelope N xi 0 j s = 1 := by
  unfold Tao.taoSection7PairSourceEnvelope
  rw [tsum_eq_single ([] : List ℕ)]
  · simp [Tao.taoSection7PascalSourceListPMF,
      Tao.taoSection7FactorProductFrom]
  · intro bs hbs
    simp [Tao.taoSection7PascalSourceListPMF, hbs]

/-- The fixed-total numerator is dominated by the same raw-Pascal source
envelope as the unrestricted Section 7 expectation. The guard in the
recurrence makes the comparison honest at every residual total. -/
theorem norm_ndSection7FiberNumeratorFrom_le_sourceEnvelope
    (N : ℕ) (xi : ZMod (3 ^ N)) :
    ∀ (k : ℕ) (j : ℕ+) (s R : ℕ),
      ‖ndSection7FiberNumeratorFrom N xi k j s R‖ ≤
        Tao.taoSection7PairSourceEnvelope N xi (k / 2) (j : ℕ) s := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro j s R
      rw [ndSection7PairSourceEnvelope_zero]
      exact norm_ndSection7FiberNumeratorFrom_le_one N xi 0 j s R
  | one =>
      intro j s R
      rw [ndSection7PairSourceEnvelope_zero]
      exact norm_ndSection7FiberNumeratorFrom_le_one N xi 1 j s R
  | more k ih _ihSucc =>
      intro j s R
      rw [ndSection7FiberNumeratorFrom_add_two]
      rw [show (k + 2) / 2 = k / 2 + 1 by omega]
      rw [ndSection7PairSourceEnvelope_succ]
      let T : ℕ → ℂ := fun b =>
        if b ≤ R then
          Tao.taoSection7PairFiberCharacterMass N xi
              (Tao.taoSection7PairX N j (Int.ofNat (s + b))) b *
            ndSection7FiberNumeratorFrom N xi k
              ⟨(j : ℕ) + 1, by omega⟩ (s + b) (R - b)
        else
          0
      let M : ℕ → ℝ := fun b =>
        (Tao.taoSection7PascalSourcePMF b).toReal *
          Tao.taoSection7SourceFThreeFactor N xi (j : ℕ) s b *
          Tao.taoSection7PairSourceEnvelope N xi (k / 2)
            ((j : ℕ) + 1) (s + b)
      have hT : Summable T := by
        refine Summable.of_norm_bounded
          (Tao.pmf_summable_toReal Tao.taoSection7PascalSourcePMF) ?_
        intro b
        by_cases hb : b ≤ R
        · simp only [T, if_pos hb, norm_mul]
          calc
            ‖Tao.taoSection7PairFiberCharacterMass N xi
                  (Tao.taoSection7PairX N j (Int.ofNat (s + b))) b‖ *
                ‖ndSection7FiberNumeratorFrom N xi k
                  ⟨(j : ℕ) + 1, by omega⟩ (s + b) (R - b)‖ ≤
                ((Tao.taoSection7PascalSourcePMF b).toReal *
                  Tao.taoSection7SourceFThreeFactor N xi (j : ℕ) s b) * 1 := by
              exact mul_le_mul
                (Tao.norm_taoSection7PairFiberCharacterMass_le_sourceFactor
                  N xi j s b)
                (norm_ndSection7FiberNumeratorFrom_le_one N xi k
                  ⟨(j : ℕ) + 1, by omega⟩ (s + b) (R - b))
                (norm_nonneg _)
                (mul_nonneg ENNReal.toReal_nonneg
                  (Tao.taoSection7SourceFThreeFactor_nonneg
                    N xi (j : ℕ) s b))
            _ ≤ (Tao.taoSection7PascalSourcePMF b).toReal * 1 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_of_le_one_right ENNReal.toReal_nonneg
                  (Tao.taoSection7SourceFThreeFactor_le_one
                    N xi (j : ℕ) s b)) (by norm_num)
            _ = (Tao.taoSection7PascalSourcePMF b).toReal := by ring
        · simp [T, hb, ENNReal.toReal_nonneg]
      have hM : Summable M := by
        refine Summable.of_norm_bounded
          (Tao.pmf_summable_toReal Tao.taoSection7PascalSourcePMF) ?_
        intro b
        have hF0 := Tao.taoSection7SourceFThreeFactor_nonneg
          N xi (j : ℕ) s b
        have hF1 := Tao.taoSection7SourceFThreeFactor_le_one
          N xi (j : ℕ) s b
        have hE0 := ndSection7PairSourceEnvelope_nonneg
          N xi (k / 2) ((j : ℕ) + 1) (s + b)
        have hE1 := ndSection7PairSourceEnvelope_le_one
          N xi (k / 2) ((j : ℕ) + 1) (s + b)
        simp only [M, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        calc
          (Tao.taoSection7PascalSourcePMF b).toReal *
                Tao.taoSection7SourceFThreeFactor N xi (j : ℕ) s b *
              Tao.taoSection7PairSourceEnvelope N xi (k / 2)
                ((j : ℕ) + 1) (s + b) ≤
              (Tao.taoSection7PascalSourcePMF b).toReal * 1 * 1 := by
            gcongr
          _ = (Tao.taoSection7PascalSourcePMF b).toReal := by ring
      change ‖∑' b : ℕ, T b‖ ≤ ∑' b : ℕ, M b
      calc
        ‖∑' b : ℕ, T b‖ ≤ ∑' b : ℕ, ‖T b‖ :=
          norm_tsum_le_tsum_norm hT.norm
        _ ≤ ∑' b : ℕ, M b := by
          exact hT.norm.tsum_le_tsum (fun b => by
            by_cases hb : b ≤ R
            · simp only [T, M, if_pos hb, norm_mul]
              exact mul_le_mul
                (Tao.norm_taoSection7PairFiberCharacterMass_le_sourceFactor
                  N xi j s b)
                (ih ⟨(j : ℕ) + 1, by omega⟩ (s + b) (R - b))
                (norm_nonneg _)
                (mul_nonneg ENNReal.toReal_nonneg
                  (Tao.taoSection7SourceFThreeFactor_nonneg
                    N xi (j : ℕ) s b))
            · simp only [T, if_neg hb, norm_zero, M]
              exact mul_nonneg
                (mul_nonneg ENNReal.toReal_nonneg
                  (Tao.taoSection7SourceFThreeFactor_nonneg
                    N xi (j : ℕ) s b))
                (ndSection7PairSourceEnvelope_nonneg
                  N xi (k / 2) ((j : ℕ) + 1) (s + b))) hM

/-- Top-level unnormalized numerator on the fiber `taoTupleWeight = L`. -/
noncomputable def ndSection7FiberNumerator
    (n L : ℕ) (xi : ZMod (3 ^ n)) : ℂ :=
  ndSection7FiberNumeratorFrom n xi n 1 0 L

/-- The recursive numerator is exactly the fixed-total restriction of the
original Section 7 character sum. The public parity bridge handles even and
odd lengths uniformly. -/
theorem ndSection7FiberNumerator_eq_restrictedCharacterSum
    (n L : ℕ) (xi : ZMod (3 ^ n)) :
    ndSection7FiberNumerator n L xi =
      ∑' as : List ℕ+,
        if Tao.taoTupleWeight as = L then
          ((Tao.geom2PNatListPMF n as).toReal : ℂ) *
            Tao.taoSection7CharacterTerm n xi as
        else 0 := by
  unfold ndSection7FiberNumerator ndSection7FiberNumeratorFrom
  apply tsum_congr
  intro as
  by_cases htotal : Tao.taoTupleWeight as = L
  · rw [if_pos htotal, if_pos htotal]
    by_cases hlength : as.length = n
    · rw [Tao.taoSection7CharacterTerm_eq_pairExpansionFrom
        n xi as hlength]
    · rw [Tao.geom2PNatListPMF_apply_eq_zero_of_length_ne
        n as hlength]
      simp
  · rw [if_neg htotal, if_neg htotal]

/-- Endpoint form of the fixed-fiber source-envelope bound. -/
theorem norm_ndSection7FiberNumerator_le_sourceEnvelope
    (n L : ℕ) (xi : ZMod (3 ^ n)) :
    ‖ndSection7FiberNumerator n L xi‖ ≤
      Tao.taoSection7PairSourceEnvelope n xi (n / 2) 1 0 := by
  exact norm_ndSection7FiberNumeratorFrom_le_sourceEnvelope
    n xi n 1 0 L

theorem norm_ndSection7FiberNumerator_le_one
    (n L : ℕ) (xi : ZMod (3 ^ n)) :
    ‖ndSection7FiberNumerator n L xi‖ ≤ 1 :=
  norm_ndSection7FiberNumeratorFrom_le_one n xi n 1 0 L

end ND
end Erdos1135
