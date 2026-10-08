import Erdos1135.Tao.Probability.PascalPrimeList
import Erdos1135.Tao.Probability.HoldMass
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Section 7 Hold Exponential Weights

This module records finite exponential-weight algebra for Tao's pre-Hold
decomposition.  It packages pathwise and finite-family identities only; it does
not construct the `Hold` distribution or justify an infinite expectation.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

theorem pascalGeom2PairMass_eq_three_fourths_mul_pascalPrimeSourceMass
    {b : ℕ} (hb : b ≠ 3) :
    pascalGeom2PairMass b =
      (3 / 4 : ℝ) * taoSection7PascalPrimeSourceMass b := by
  rw [taoSection7PascalPrimeSourceMass_of_ne_three hb]
  ring

/--
Exponential weight of the concrete pre-Hold point determined by a pre-hit list:
`(pre.length + 1, pre.sum + 3)`.
-/
noncomputable def taoSection7PreHoldExpWeight
    (k1 k2 : ℝ) (pre : List ℕ) : ℝ :=
  Real.exp (((pre.length + 1 : ℕ) : ℝ) * k1 +
    ((pre.sum + 3 : ℕ) : ℝ) * k2)

/-- Exponential weight of one conditioned Pascal-prime pre-hit step `(1, b)`. -/
noncomputable def taoSection7PascalPrimeStepExpWeight
    (k1 k2 : ℝ) (b : ℕ) : ℝ :=
  Real.exp (k1 + (b : ℝ) * k2)

/-- Product of conditioned Pascal-prime source masses with exponential step weights. -/
noncomputable def taoSection7PascalPrimeWeightedPathMass
    (k1 k2 : ℝ) (pre : List ℕ) : ℝ :=
  (pre.map fun b =>
    taoSection7PascalPrimeSourceMass b *
      taoSection7PascalPrimeStepExpWeight k1 k2 b).prod

/-- Unconditioned pre-hit path mass with the exponential pre-Hold point weight. -/
noncomputable def taoSection7PreHoldWeightedMass
    (k1 k2 : ℝ) (pre : List ℕ) : ℝ :=
  taoSection7UnconditionedPreHitPathMass pre *
    taoSection7PreHoldExpWeight k1 k2 pre

theorem taoSection7PascalPrimeWeightedPathMass_nil
    (k1 k2 : ℝ) :
    taoSection7PascalPrimeWeightedPathMass k1 k2 [] = 1 := by
  simp [taoSection7PascalPrimeWeightedPathMass]

theorem taoSection7PascalPrimeWeightedPathMass_cons
    (k1 k2 : ℝ) (b : ℕ) (pre : List ℕ) :
    taoSection7PascalPrimeWeightedPathMass k1 k2 (b :: pre) =
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight k1 k2 b *
          taoSection7PascalPrimeWeightedPathMass k1 k2 pre := by
  simp [taoSection7PascalPrimeWeightedPathMass, mul_assoc]

theorem taoSection7PascalPrimeSourceMass_nonneg (b : ℕ) :
    0 ≤ taoSection7PascalPrimeSourceMass b := by
  unfold taoSection7PascalPrimeSourceMass
  split_ifs
  · norm_num
  · exact mul_nonneg (by norm_num) (by
      unfold pascalGeom2PairMass
      exact Finset.sum_nonneg (by
        intro a _ha
        positivity))

theorem taoSection7PascalPrimeStepExpWeight_nonneg
    (k1 k2 : ℝ) (b : ℕ) :
    0 ≤ taoSection7PascalPrimeStepExpWeight k1 k2 b := by
  unfold taoSection7PascalPrimeStepExpWeight
  exact Real.exp_nonneg _

theorem taoSection7PascalPrimeWeightedPathMass_nonneg
    (k1 k2 : ℝ) :
    ∀ pre : List ℕ, 0 ≤ taoSection7PascalPrimeWeightedPathMass k1 k2 pre
  | [] => by
      rw [taoSection7PascalPrimeWeightedPathMass_nil]
      norm_num
  | b :: pre => by
      rw [taoSection7PascalPrimeWeightedPathMass_cons]
      exact mul_nonneg
        (mul_nonneg (taoSection7PascalPrimeSourceMass_nonneg b)
          (taoSection7PascalPrimeStepExpWeight_nonneg k1 k2 b))
        (taoSection7PascalPrimeWeightedPathMass_nonneg k1 k2 pre)

theorem taoSection7_tsum_nat_list_eq_tsum_cons_of_nil_zero
    {f : List ℕ → ℝ} (h0 : f [] = 0) :
    (∑' xs : List ℕ, f xs) =
      ∑' x : ℕ × List ℕ, f (x.1 :: x.2) := by
  classical
  let g : ℕ × List ℕ → List ℕ := fun x => x.1 :: x.2
  have hg : Function.Injective g := by
    intro x y hxy
    cases x with
    | mk xh xt =>
        cases y with
        | mk yh yt =>
            simp [g] at hxy ⊢
            exact hxy
  have hsupp : Function.support f ⊆ Set.range g := by
    intro hs hhs
    cases hs with
    | nil =>
        exfalso
        exact hhs h0
    | cons h hs =>
        exact ⟨(h, hs), rfl⟩
  exact (hg.tsum_eq (f := f) hsupp).symm

theorem taoSection7_summable_nat_list_of_summable_cons
    {f : List ℕ → ℝ}
    (h0 : f [] = 0)
    (hcons : Summable fun x : ℕ × List ℕ => f (x.1 :: x.2)) :
    Summable f := by
  classical
  let g : ℕ × List ℕ → List ℕ := fun x => x.1 :: x.2
  have hg : Function.Injective g := by
    intro x y hxy
    cases x with
    | mk xh xt =>
        cases y with
        | mk yh yt =>
            simp [g] at hxy ⊢
            exact hxy
  have hzero : ∀ xs ∉ Set.range g, f xs = 0 := by
    intro xs hxs
    cases xs with
    | nil => exact h0
    | cons b bs =>
        exfalso
        exact hxs ⟨(b, bs), rfl⟩
  exact (hg.summable_iff (f := f) hzero).mp hcons

theorem taoSection7_list_prod_nonneg_of_nonneg
    {f : ℕ → ℝ} (hf0 : ∀ b, 0 ≤ f b) :
    ∀ xs : List ℕ, 0 ≤ (xs.map f).prod
  | [] => by simp
  | b :: xs => by
      simp [mul_nonneg (hf0 b)
        (taoSection7_list_prod_nonneg_of_nonneg hf0 xs)]

/-- The product term restricted to lists of a fixed length. -/
noncomputable def taoSection7ListProductLengthTerm
    (f : ℕ → ℝ) (m : ℕ) (xs : List ℕ) : ℝ :=
  if xs.length = m then (xs.map f).prod else 0

theorem taoSection7ListProductLengthTerm_nonneg
    {f : ℕ → ℝ} (hf0 : ∀ b, 0 ≤ f b) (m : ℕ) :
    ∀ xs : List ℕ, 0 ≤ taoSection7ListProductLengthTerm f m xs := by
  intro xs
  unfold taoSection7ListProductLengthTerm
  split_ifs
  · exact taoSection7_list_prod_nonneg_of_nonneg hf0 xs
  · simp

theorem taoSection7ListProductLengthTerm_zero_of_length_ne
    {f : ℕ → ℝ} {m : ℕ} {xs : List ℕ}
    (h : xs.length ≠ m) :
    taoSection7ListProductLengthTerm f m xs = 0 := by
  simp [taoSection7ListProductLengthTerm, h]

theorem taoSection7ListProductLengthTerm_cons
    {f : ℕ → ℝ} (m b : ℕ) (xs : List ℕ) :
    taoSection7ListProductLengthTerm f (m + 1) (b :: xs) =
      f b * taoSection7ListProductLengthTerm f m xs := by
  unfold taoSection7ListProductLengthTerm
  by_cases h : xs.length = m
  · have hsucc : (b :: xs).length = m + 1 := by simp [h]
    simp [h, hsucc]
  · have hsucc : (b :: xs).length ≠ m + 1 := by
      intro hs
      exact h (Nat.succ.inj hs)
    simp [h]

theorem summable_taoSection7ListProductLengthTerm
    {f : ℕ → ℝ} (hf : Summable f) (hf0 : ∀ b, 0 ≤ f b) :
    ∀ m : ℕ, Summable (taoSection7ListProductLengthTerm f m) := by
  intro m
  induction m with
  | zero =>
      refine summable_of_hasFiniteSupport ?_
      refine (Set.finite_singleton ([] : List ℕ)).subset ?_
      intro xs hxs
      have hlen : xs.length = 0 := by
        by_contra hlen
        exact hxs
          (taoSection7ListProductLengthTerm_zero_of_length_ne
            (f := f) (m := 0) hlen)
      cases xs with
      | nil => simp
      | cons b bs => simp at hlen
  | succ m ih =>
      have hg : Summable (taoSection7ListProductLengthTerm f m) := ih
      have hprod : Summable fun x : ℕ × List ℕ =>
          f x.1 * taoSection7ListProductLengthTerm f m x.2 :=
        Summable.mul_of_nonneg hf hg hf0
          (taoSection7ListProductLengthTerm_nonneg hf0 m)
      refine taoSection7_summable_nat_list_of_summable_cons ?_ ?_
      · simp [taoSection7ListProductLengthTerm]
      · refine hprod.congr ?_
        intro x
        rw [taoSection7ListProductLengthTerm_cons]

theorem tsum_taoSection7ListProductLengthTerm_eq_tsum_pow
    {f : ℕ → ℝ} (hf : Summable f) (hf0 : ∀ b, 0 ≤ f b) :
    ∀ m : ℕ,
      (∑' xs : List ℕ, taoSection7ListProductLengthTerm f m xs) =
        (∑' b : ℕ, f b) ^ m := by
  intro m
  induction m with
  | zero =>
      rw [tsum_eq_single ([] : List ℕ)]
      · simp [taoSection7ListProductLengthTerm]
      · intro xs hxs
        have hlen : xs.length ≠ 0 := by
          intro hzero
          cases xs with
          | nil => exact hxs rfl
          | cons b bs => simp at hzero
        exact taoSection7ListProductLengthTerm_zero_of_length_ne
          (f := f) (m := 0) hlen
  | succ m ih =>
      have hg : Summable (taoSection7ListProductLengthTerm f m) :=
        summable_taoSection7ListProductLengthTerm hf hf0 m
      have hprod : Summable fun x : ℕ × List ℕ =>
          f x.1 * taoSection7ListProductLengthTerm f m x.2 :=
        Summable.mul_of_nonneg hf hg hf0
          (taoSection7ListProductLengthTerm_nonneg hf0 m)
      calc
        (∑' xs : List ℕ, taoSection7ListProductLengthTerm f (m + 1) xs)
            =
          ∑' x : ℕ × List ℕ,
            taoSection7ListProductLengthTerm f (m + 1) (x.1 :: x.2) := by
              apply taoSection7_tsum_nat_list_eq_tsum_cons_of_nil_zero
              simp [taoSection7ListProductLengthTerm]
        _ =
          ∑' x : ℕ × List ℕ,
            f x.1 * taoSection7ListProductLengthTerm f m x.2 := by
              apply tsum_congr
              intro x
              rw [taoSection7ListProductLengthTerm_cons]
        _ =
          (∑' b : ℕ, f b) *
            (∑' xs : List ℕ, taoSection7ListProductLengthTerm f m xs) := by
              exact (hf.tsum_mul_tsum hg hprod).symm
        _ = (∑' b : ℕ, f b) ^ (m + 1) := by
              rw [ih]
              ring

theorem taoSection7PreHoldExpWeight_nil (k1 k2 : ℝ) :
    taoSection7PreHoldExpWeight k1 k2 [] =
      Real.exp (k1 + 3 * k2) := by
  simp [taoSection7PreHoldExpWeight]

theorem taoSection7PreHoldExpWeight_cons
    (k1 k2 : ℝ) (b : ℕ) (pre : List ℕ) :
    taoSection7PreHoldExpWeight k1 k2 (b :: pre) =
      taoSection7PascalPrimeStepExpWeight k1 k2 b *
        taoSection7PreHoldExpWeight k1 k2 pre := by
  rw [taoSection7PreHoldExpWeight, taoSection7PascalPrimeStepExpWeight,
    taoSection7PreHoldExpWeight, ← Real.exp_add]
  congr 1
  simp
  ring

/--
Finite exponential-weight version of the source decomposition before equation
`(7.30)`.  The `pre.length` conditioned Pascal-prime factors precede the final
successful hit `(1, 3)`.
-/
theorem taoSection7PreHoldWeightedMass_eq_geom4_exp_mul_primeWeighted
    {pre : List ℕ} (hpre : taoSection7NoThree pre) (k1 k2 : ℝ) :
    taoSection7PreHoldWeightedMass k1 k2 pre =
      taoSection7Geom4FirstHitMass ⟨pre.length + 1, Nat.succ_pos pre.length⟩ *
        Real.exp (k1 + 3 * k2) *
          taoSection7PascalPrimeWeightedPathMass k1 k2 pre := by
  induction pre with
  | nil =>
      rw [taoSection7PreHoldWeightedMass,
        taoSection7UnconditionedPreHitPathMass_nil,
        taoSection7PreHoldExpWeight_nil,
        taoSection7PascalPrimeWeightedPathMass_nil]
      have hfirst :
          taoSection7Geom4FirstHitMass
              ⟨([] : List ℕ).length + 1, Nat.succ_pos ([] : List ℕ).length⟩ =
            (1 / 4 : ℝ) := by
        simpa using taoSection7Geom4FirstHitMass_one
      rw [hfirst]
      ring
  | cons b pre ih =>
      have hb : b ≠ 3 := hpre b (by simp)
      have htail : taoSection7NoThree pre := by
        intro x hx
        exact hpre x (by simp [hx])
      have hgeom :
          taoSection7Geom4FirstHitMass
              ⟨List.length (b :: pre) + 1, Nat.succ_pos (List.length (b :: pre))⟩ =
            (3 / 4 : ℝ) *
              taoSection7Geom4FirstHitMass
                ⟨pre.length + 1, Nat.succ_pos pre.length⟩ := by
        exact
          taoSection7Geom4FirstHitMass_succ
            ⟨pre.length + 1, Nat.succ_pos pre.length⟩
      rw [taoSection7PreHoldWeightedMass,
        taoSection7UnconditionedPreHitPathMass_cons,
        taoSection7PreHoldExpWeight_cons]
      rw [pascalGeom2PairMass_eq_three_fourths_mul_pascalPrimeSourceMass hb]
      calc
        (3 / 4 : ℝ) * taoSection7PascalPrimeSourceMass b *
              taoSection7UnconditionedPreHitPathMass pre *
              (taoSection7PascalPrimeStepExpWeight k1 k2 b *
                taoSection7PreHoldExpWeight k1 k2 pre)
            =
          (3 / 4 : ℝ) * taoSection7PascalPrimeSourceMass b *
            taoSection7PascalPrimeStepExpWeight k1 k2 b *
              (taoSection7UnconditionedPreHitPathMass pre *
                taoSection7PreHoldExpWeight k1 k2 pre) := by
              ring
        _ =
          (3 / 4 : ℝ) * taoSection7PascalPrimeSourceMass b *
            taoSection7PascalPrimeStepExpWeight k1 k2 b *
              taoSection7PreHoldWeightedMass k1 k2 pre := by
              rfl
        _ =
          (3 / 4 : ℝ) * taoSection7PascalPrimeSourceMass b *
            taoSection7PascalPrimeStepExpWeight k1 k2 b *
              (taoSection7Geom4FirstHitMass
                  ⟨pre.length + 1, Nat.succ_pos pre.length⟩ *
                Real.exp (k1 + 3 * k2) *
                  taoSection7PascalPrimeWeightedPathMass k1 k2 pre) := by
              rw [ih htail]
        _ =
          ((3 / 4 : ℝ) *
              taoSection7Geom4FirstHitMass
                ⟨pre.length + 1, Nat.succ_pos pre.length⟩) *
            Real.exp (k1 + 3 * k2) *
              (taoSection7PascalPrimeSourceMass b *
                taoSection7PascalPrimeStepExpWeight k1 k2 b *
                  taoSection7PascalPrimeWeightedPathMass k1 k2 pre) := by
              ring
        _ =
          taoSection7Geom4FirstHitMass
              ⟨List.length (b :: pre) + 1, Nat.succ_pos (List.length (b :: pre))⟩ *
            Real.exp (k1 + 3 * k2) *
              taoSection7PascalPrimeWeightedPathMass k1 k2 (b :: pre) := by
              rw [← hgeom]
              rw [taoSection7PascalPrimeWeightedPathMass_cons]

/--
Finite-family consumer of the pathwise exponential-weight factorization.  This
is a finite-sum approximation to the expectation identity before Tao's
equation `(7.30)`, not an infinite expectation theorem.
-/
theorem taoSection7PreHoldWeightedMass_sum_eq_geom4_exp_mul_primeWeighted_sum
    (S : Finset (List ℕ)) (hno : ∀ pre ∈ S, taoSection7NoThree pre)
    (k1 k2 : ℝ) :
    (∑ pre ∈ S, taoSection7PreHoldWeightedMass k1 k2 pre) =
      Real.exp (k1 + 3 * k2) *
        ∑ pre ∈ S,
          taoSection7Geom4FirstHitMass
              ⟨pre.length + 1, Nat.succ_pos pre.length⟩ *
            taoSection7PascalPrimeWeightedPathMass k1 k2 pre := by
  calc
    (∑ pre ∈ S, taoSection7PreHoldWeightedMass k1 k2 pre)
        =
      ∑ pre ∈ S,
        taoSection7Geom4FirstHitMass
            ⟨pre.length + 1, Nat.succ_pos pre.length⟩ *
          Real.exp (k1 + 3 * k2) *
            taoSection7PascalPrimeWeightedPathMass k1 k2 pre := by
          apply Finset.sum_congr rfl
          intro pre hpre
          exact taoSection7PreHoldWeightedMass_eq_geom4_exp_mul_primeWeighted
            (hno pre hpre) k1 k2
    _ =
      ∑ pre ∈ S,
        Real.exp (k1 + 3 * k2) *
          (taoSection7Geom4FirstHitMass
              ⟨pre.length + 1, Nat.succ_pos pre.length⟩ *
            taoSection7PascalPrimeWeightedPathMass k1 k2 pre) := by
          apply Finset.sum_congr rfl
          intro pre _hpre
          ring
    _ =
      Real.exp (k1 + 3 * k2) *
        ∑ pre ∈ S,
          taoSection7Geom4FirstHitMass
              ⟨pre.length + 1, Nat.succ_pos pre.length⟩ *
            taoSection7PascalPrimeWeightedPathMass k1 k2 pre := by
          rw [Finset.mul_sum]

/--
Pathwise source-list exponential-weight factorization for the terminal `Hold`
MGF route.  The prefactor is the final successful hit `(1, 3)`; the remaining
product is the Pascal-prime one-step weighted path mass.
-/
theorem taoSection7PascalPrimeSourcePathMass_mul_preHoldExpWeight_eq_exp_mul_weightedPathMass
    (alpha : ℝ) :
    ∀ pre : List ℕ,
      taoSection7PascalPrimeSourcePathMass pre *
        taoSection7PreHoldExpWeight alpha alpha pre =
      Real.exp (4 * alpha) *
        taoSection7PascalPrimeWeightedPathMass alpha alpha pre
  | [] => by
      rw [taoSection7PreHoldExpWeight_nil,
        taoSection7PascalPrimeWeightedPathMass_nil]
      simp [taoSection7PascalPrimeSourcePathMass]
      rw [show alpha + 3 * alpha = 4 * alpha by ring]
  | b :: pre => by
      have ih :=
        taoSection7PascalPrimeSourcePathMass_mul_preHoldExpWeight_eq_exp_mul_weightedPathMass
          alpha pre
      rw [taoSection7PreHoldExpWeight_cons]
      rw [taoSection7PascalPrimeWeightedPathMass_cons]
      simp [taoSection7PascalPrimeSourcePathMass] at ih ⊢
      calc
        taoSection7PascalPrimeSourceMass b *
              (List.map taoSection7PascalPrimeSourceMass pre).prod *
              (taoSection7PascalPrimeStepExpWeight alpha alpha b *
                taoSection7PreHoldExpWeight alpha alpha pre)
            = taoSection7PascalPrimeSourceMass b *
                taoSection7PascalPrimeStepExpWeight alpha alpha b *
                  ((List.map taoSection7PascalPrimeSourceMass pre).prod *
                    taoSection7PreHoldExpWeight alpha alpha pre) := by
                ring
        _ = taoSection7PascalPrimeSourceMass b *
                taoSection7PascalPrimeStepExpWeight alpha alpha b *
                  (Real.exp (4 * alpha) *
                    taoSection7PascalPrimeWeightedPathMass alpha alpha pre) := by
                rw [ih]
        _ = Real.exp (4 * alpha) *
              (taoSection7PascalPrimeSourceMass b *
                taoSection7PascalPrimeStepExpWeight alpha alpha b *
                  taoSection7PascalPrimeWeightedPathMass alpha alpha pre) := by
                ring

/-- One-step Pascal-prime exponential moment using the step weight from the finite path algebra. -/
noncomputable def taoSection7PascalPrimeStepMoment (alpha : ℝ) : ℝ :=
  ∑' b : ℕ,
    taoSection7PascalPrimeSourceMass b *
      taoSection7PascalPrimeStepExpWeight alpha alpha b

theorem summable_taoSection7PascalPrimeWeightedPathMass_length
    {alpha : ℝ}
    (hs : Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b)
    (m : ℕ) :
    Summable fun pre : List ℕ =>
      if pre.length = m then
        taoSection7PascalPrimeWeightedPathMass alpha alpha pre
      else 0 := by
  have hnonneg : ∀ b : ℕ,
      0 ≤ taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b := by
    intro b
    exact mul_nonneg (taoSection7PascalPrimeSourceMass_nonneg b)
      (taoSection7PascalPrimeStepExpWeight_nonneg alpha alpha b)
  change Summable (taoSection7ListProductLengthTerm
    (fun b : ℕ => taoSection7PascalPrimeSourceMass b *
      taoSection7PascalPrimeStepExpWeight alpha alpha b) m)
  exact summable_taoSection7ListProductLengthTerm hs hnonneg m

theorem tsum_taoSection7PascalPrimeWeightedPathMass_length_eq_stepMoment_pow
    {alpha : ℝ}
    (hs : Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b)
    (m : ℕ) :
    (∑' pre : List ℕ,
      if pre.length = m then
        taoSection7PascalPrimeWeightedPathMass alpha alpha pre
      else 0) =
    (taoSection7PascalPrimeStepMoment alpha) ^ m := by
  have hnonneg : ∀ b : ℕ,
      0 ≤ taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b := by
    intro b
    exact mul_nonneg (taoSection7PascalPrimeSourceMass_nonneg b)
      (taoSection7PascalPrimeStepExpWeight_nonneg alpha alpha b)
  change (∑' pre : List ℕ, taoSection7ListProductLengthTerm
    (fun b : ℕ => taoSection7PascalPrimeSourceMass b *
      taoSection7PascalPrimeStepExpWeight alpha alpha b) m pre) =
    (taoSection7PascalPrimeStepMoment alpha) ^ m
  simpa [taoSection7PascalPrimeStepMoment] using
    tsum_taoSection7ListProductLengthTerm_eq_tsum_pow hs hnonneg m

theorem tsum_taoSection7PascalPrimeSourceListPMF_preHoldExpWeight_eq_exp_mul_stepMoment_pow
    {alpha : ℝ}
    (hs : Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b)
    (m : ℕ) :
    (∑' pre : List ℕ,
      (taoSection7PascalPrimeSourceListPMF m pre).toReal *
        taoSection7PreHoldExpWeight alpha alpha pre) =
      Real.exp (4 * alpha) *
        (taoSection7PascalPrimeStepMoment alpha) ^ m := by
  calc
    (∑' pre : List ℕ,
      (taoSection7PascalPrimeSourceListPMF m pre).toReal *
        taoSection7PreHoldExpWeight alpha alpha pre)
        =
      ∑' pre : List ℕ,
        if pre.length = m then
          taoSection7PascalPrimeSourcePathMass pre *
            taoSection7PreHoldExpWeight alpha alpha pre
        else 0 := by
          apply tsum_congr
          intro pre
          by_cases hlen : pre.length = m
          · have hpmf :
                (taoSection7PascalPrimeSourceListPMF m pre).toReal =
                  taoSection7PascalPrimeSourcePathMass pre := by
              rw [← hlen]
              exact
                taoSection7PascalPrimeSourceListPMF_apply_length_toReal_eq_sourcePathMass
                  pre
            simp [hlen, hpmf]
          · have hpmf :
                (taoSection7PascalPrimeSourceListPMF m pre).toReal = 0 := by
              rw [taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_length_ne
                m pre hlen]
              simp
            simp [hlen, hpmf]
    _ =
      ∑' pre : List ℕ,
        if pre.length = m then
          Real.exp (4 * alpha) *
            taoSection7PascalPrimeWeightedPathMass alpha alpha pre
        else 0 := by
          apply tsum_congr
          intro pre
          by_cases hlen : pre.length = m
          · rw [ite_eq_left hlen]
            rw [ite_eq_left hlen]
            rw [taoSection7PascalPrimeSourcePathMass_mul_preHoldExpWeight_eq_exp_mul_weightedPathMass]
          · simp [hlen]
    _ =
      Real.exp (4 * alpha) *
        (∑' pre : List ℕ,
          if pre.length = m then
            taoSection7PascalPrimeWeightedPathMass alpha alpha pre
          else 0) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro pre
          by_cases hlen : pre.length = m
          · simp [hlen]
          · simp [hlen]
    _ =
      Real.exp (4 * alpha) *
        (taoSection7PascalPrimeStepMoment alpha) ^ m := by
          rw [tsum_taoSection7PascalPrimeWeightedPathMass_length_eq_stepMoment_pow
            hs m]

theorem taoSection7PascalPrimeStepExpWeight_log_21_div_20
    (b : ℕ) :
    taoSection7PascalPrimeStepExpWeight
        (Real.log (21 / 20 : ℝ)) (Real.log (21 / 20 : ℝ)) b =
      (21 / 20 : ℝ) ^ (b + 1) := by
  unfold taoSection7PascalPrimeStepExpWeight
  rw [show Real.log (21 / 20 : ℝ) + (b : ℝ) * Real.log (21 / 20 : ℝ) =
      ((b + 1 : ℕ) : ℝ) * Real.log (21 / 20 : ℝ) by
    norm_num
    ring]
  rw [Real.exp_nat_mul]
  rw [Real.exp_log]
  norm_num

/-- Summability of the one-step Pascal-prime moment at `alpha = log (21/20)`. -/
theorem summable_taoSection7PascalPrimeStepMoment_log_21_div_20 :
    Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight
          (Real.log (21 / 20 : ℝ)) (Real.log (21 / 20 : ℝ)) b := by
  refine
    (summable_taoSection7PascalPrimeSourceMass_pow_21_div_20.mul_right
      (21 / 20 : ℝ)).congr ?_
  intro b
  rw [taoSection7PascalPrimeStepExpWeight_log_21_div_20]
  rw [show (21 / 20 : ℝ) ^ (b + 1) =
      (21 / 20 : ℝ) ^ b * (21 / 20 : ℝ) by rw [pow_succ]]
  ring

/-- Exact one-step Pascal-prime moment at `alpha = log (21/20)`. -/
theorem taoSection7PascalPrimeStepMoment_log_21_div_20_eq :
    taoSection7PascalPrimeStepMoment (Real.log (21 / 20 : ℝ)) =
      75381453 / 57760000 := by
  unfold taoSection7PascalPrimeStepMoment
  calc
    (∑' b : ℕ,
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight
          (Real.log (21 / 20 : ℝ)) (Real.log (21 / 20 : ℝ)) b)
        = ∑' b : ℕ,
            (taoSection7PascalPrimeSourceMass b * (21 / 20 : ℝ) ^ b) *
              (21 / 20 : ℝ) := by
          apply tsum_congr
          intro b
          rw [taoSection7PascalPrimeStepExpWeight_log_21_div_20]
          rw [show (21 / 20 : ℝ) ^ (b + 1) =
              (21 / 20 : ℝ) ^ b * (21 / 20 : ℝ) by rw [pow_succ]]
          ring
    _ = (∑' b : ℕ,
          taoSection7PascalPrimeSourceMass b * (21 / 20 : ℝ) ^ b) *
          (21 / 20 : ℝ) := by
          rw [tsum_mul_right]
    _ = 75381453 / 57760000 := by
          rw [tsum_taoSection7PascalPrimeSourceMass_pow_21_div_20]
          norm_num

/-- Bound form of the one-step Pascal-prime moment used for the Hold-MGF contraction. -/
theorem taoSection7PascalPrimeStepMoment_log_21_div_20_le_47_36 :
    taoSection7PascalPrimeStepMoment (Real.log (21 / 20 : ℝ)) ≤
      47 / 36 := by
  rw [taoSection7PascalPrimeStepMoment_log_21_div_20_eq]
  norm_num

end Tao
end Erdos1135
