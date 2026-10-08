/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.HoldExpectation
import Erdos1135Predecessor.Tao.Renewal.HoldIID
import Mathlib.Tactic

open scoped BigOperators Topology

namespace Erdos1135Predecessor

namespace Tao

private theorem pmf_toReal_summable {α : Type*} (p : PMF α) :
    Summable fun a : α => (p a).toReal := by
  refine ENNReal.summable_toReal ?_
  rw [PMF.tsum_coe p]
  norm_num

private theorem pmf_toReal_tsum {α : Type*} (p : PMF α) :
    (∑' a : α, (p a).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq]
  · rw [PMF.tsum_coe p]
    norm_num
  · intro a
    exact PMF.apply_ne_top p a

theorem taoSection7HoldListPMF_summable_toReal
    (K : ℕ) :
    Summable fun hs : List TaoSection7RenewalPoint =>
      (taoSection7HoldListPMF K hs).toReal :=
  pmf_toReal_summable (taoSection7HoldListPMF K)

theorem taoSection7HoldListPMF_tsum_toReal
    (K : ℕ) :
    (∑' hs : List TaoSection7RenewalPoint,
      (taoSection7HoldListPMF K hs).toReal) = 1 :=
  pmf_toReal_tsum (taoSection7HoldListPMF K)

noncomputable def taoSection7QFiniteTerminalOneApprox
    (K : ℕ) (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) : ℝ :=
  ∑' hs : List TaoSection7RenewalPoint,
    (taoSection7HoldListPMF K hs).toReal *
      taoSection7QFinite epsilon W p hs

theorem taoSection7QFiniteTerminalOneApprox_summable
    {K : ℕ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop) (p : TaoSection7RenewalPoint) :
    Summable fun hs : List TaoSection7RenewalPoint =>
      (taoSection7HoldListPMF K hs).toReal *
        taoSection7QFinite epsilon W p hs := by
  have hmass :
      Summable fun hs : List TaoSection7RenewalPoint =>
        (taoSection7HoldListPMF K hs).toReal :=
    taoSection7HoldListPMF_summable_toReal K
  refine Summable.of_norm_bounded hmass ?_
  intro hs
  have hm0 : 0 ≤ (taoSection7HoldListPMF K hs).toReal := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ taoSection7QFinite epsilon W p hs :=
    taoSection7QFinite_nonneg epsilon W p hs
  have hq1 : taoSection7QFinite epsilon W p hs ≤ 1 :=
    taoSection7QFinite_le_one hepsilon W p hs
  have hqabs : |taoSection7QFinite epsilon W p hs| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hq0], hq1⟩
  calc
    ‖(taoSection7HoldListPMF K hs).toReal *
        taoSection7QFinite epsilon W p hs‖
        = |(taoSection7HoldListPMF K hs).toReal *
            taoSection7QFinite epsilon W p hs| := Real.norm_eq_abs _
    _ = (taoSection7HoldListPMF K hs).toReal *
          |taoSection7QFinite epsilon W p hs| := by
        rw [abs_mul, abs_of_nonneg hm0]
    _ ≤ (taoSection7HoldListPMF K hs).toReal * 1 := by
        exact mul_le_mul_of_nonneg_left hqabs hm0
    _ = (taoSection7HoldListPMF K hs).toReal := by ring

theorem taoSection7QFiniteTerminalOneApprox_nonneg
    (K : ℕ) (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    0 ≤ taoSection7QFiniteTerminalOneApprox K epsilon W p := by
  unfold taoSection7QFiniteTerminalOneApprox
  exact tsum_nonneg fun hs =>
    mul_nonneg ENNReal.toReal_nonneg
      (taoSection7QFinite_nonneg epsilon W p hs)

theorem taoSection7QFiniteTerminalOneApprox_le_one
    {K : ℕ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop) (p : TaoSection7RenewalPoint) :
    taoSection7QFiniteTerminalOneApprox K epsilon W p ≤ 1 := by
  unfold taoSection7QFiniteTerminalOneApprox
  have hterm :
      Summable fun hs : List TaoSection7RenewalPoint =>
        (taoSection7HoldListPMF K hs).toReal *
          taoSection7QFinite epsilon W p hs :=
    taoSection7QFiniteTerminalOneApprox_summable hepsilon W p
  have hmass :
      Summable fun hs : List TaoSection7RenewalPoint =>
        (taoSection7HoldListPMF K hs).toReal :=
    taoSection7HoldListPMF_summable_toReal K
  calc
    (∑' hs : List TaoSection7RenewalPoint,
        (taoSection7HoldListPMF K hs).toReal *
          taoSection7QFinite epsilon W p hs)
        ≤ ∑' hs : List TaoSection7RenewalPoint,
            (taoSection7HoldListPMF K hs).toReal := by
          exact hterm.tsum_le_tsum
            (fun hs => by
              have hm0 : 0 ≤ (taoSection7HoldListPMF K hs).toReal :=
                ENNReal.toReal_nonneg
              have hq1 : taoSection7QFinite epsilon W p hs ≤ 1 :=
                taoSection7QFinite_le_one hepsilon W p hs
              calc
                (taoSection7HoldListPMF K hs).toReal *
                    taoSection7QFinite epsilon W p hs
                    ≤ (taoSection7HoldListPMF K hs).toReal * 1 := by
                    exact mul_le_mul_of_nonneg_left hq1 hm0
                _ = (taoSection7HoldListPMF K hs).toReal := by ring)
            hmass
    _ = 1 := taoSection7HoldListPMF_tsum_toReal K

theorem taoSection7QFiniteTerminalOneApprox_zero
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    taoSection7QFiniteTerminalOneApprox 0 epsilon W p =
      taoSection7QWhiteFactor epsilon W p := by
  unfold taoSection7QFiniteTerminalOneApprox
  rw [tsum_eq_single ([] : List TaoSection7RenewalPoint)]
  · simp [taoSection7HoldListPMF_zero_apply_nil, taoSection7QFinite_nil]
  · intro hs hne
    cases hs with
    | nil => exact (hne rfl).elim
    | cons h hs =>
        rw [taoSection7HoldListPMF_zero_apply_cons]
        simp

theorem taoSection7QFinite_append_le_left
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop) :
    ∀ (p : TaoSection7RenewalPoint)
      (xs ys : List TaoSection7RenewalPoint),
      taoSection7QFinite epsilon W p (xs ++ ys) ≤
        taoSection7QFinite epsilon W p xs := by
  intro p xs
  induction xs generalizing p with
  | nil =>
      intro ys
      cases ys with
      | nil =>
          rfl
      | cons h hs =>
          rw [List.nil_append, taoSection7QFinite_cons, taoSection7QFinite_nil]
          calc
            taoSection7QWhiteFactor epsilon W p *
                taoSection7QFinite epsilon W (p + h) hs
                ≤ taoSection7QWhiteFactor epsilon W p * 1 := by
                exact mul_le_mul_of_nonneg_left
                  (taoSection7QFinite_le_one hepsilon W (p + h) hs)
                  (taoSection7QWhiteFactor_nonneg epsilon W p)
            _ = taoSection7QWhiteFactor epsilon W p := by ring
  | cons h xs ih =>
      intro ys
      rw [List.cons_append, taoSection7QFinite_cons, taoSection7QFinite_cons]
      exact mul_le_mul_of_nonneg_left (ih (p + h) ys)
        (taoSection7QWhiteFactor_nonneg epsilon W p)

theorem taoSection7_tsum_list_eq_tsum_cons_of_nil_zero
    {f : List TaoSection7RenewalPoint → ℝ} (h0 : f [] = 0) :
    (∑' hs : List TaoSection7RenewalPoint, f hs) =
      ∑' x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint,
        f (x.1 :: x.2) := by
  classical
  let g : TaoSection7RenewalPoint × List TaoSection7RenewalPoint →
      List TaoSection7RenewalPoint := fun x => x.1 :: x.2
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

theorem taoSection7HoldPMF_mul_holdListPMF_summable_toReal
    (K : ℕ) :
    Summable fun x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint =>
      (taoSection7HoldPMF x.1).toReal *
        (taoSection7HoldListPMF K x.2).toReal := by
  have hf : Summable fun h : TaoSection7RenewalPoint =>
      (taoSection7HoldPMF h).toReal := taoSection7HoldPMF_summable_toReal
  have hg : Summable fun hs : List TaoSection7RenewalPoint =>
      (taoSection7HoldListPMF K hs).toReal :=
    taoSection7HoldListPMF_summable_toReal K
  exact Summable.mul_of_nonneg
    (f := fun h : TaoSection7RenewalPoint => (taoSection7HoldPMF h).toReal)
    (g := fun hs : List TaoSection7RenewalPoint =>
      (taoSection7HoldListPMF K hs).toReal)
    hf hg
    (fun _h => ENNReal.toReal_nonneg)
    (fun _hs => ENNReal.toReal_nonneg)

theorem taoSection7HoldPMF_mul_holdListPMF_mul_QFinite_summable
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (K : ℕ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    Summable fun x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint =>
      (taoSection7HoldPMF x.1).toReal *
        (taoSection7HoldListPMF K x.2).toReal *
        taoSection7QFinite epsilon W (p + x.1) x.2 := by
  have hmass :
      Summable fun x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint =>
        (taoSection7HoldPMF x.1).toReal *
          (taoSection7HoldListPMF K x.2).toReal :=
    taoSection7HoldPMF_mul_holdListPMF_summable_toReal K
  refine Summable.of_norm_bounded hmass ?_
  intro x
  have hm0 : 0 ≤ (taoSection7HoldPMF x.1).toReal *
      (taoSection7HoldListPMF K x.2).toReal :=
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hq0 : 0 ≤ taoSection7QFinite epsilon W (p + x.1) x.2 :=
    taoSection7QFinite_nonneg epsilon W (p + x.1) x.2
  have hq1 : taoSection7QFinite epsilon W (p + x.1) x.2 ≤ 1 :=
    taoSection7QFinite_le_one hepsilon W (p + x.1) x.2
  have hqabs : |taoSection7QFinite epsilon W (p + x.1) x.2| ≤ 1 := by
    rw [abs_of_nonneg hq0]
    exact hq1
  calc
    ‖(taoSection7HoldPMF x.1).toReal *
        (taoSection7HoldListPMF K x.2).toReal *
        taoSection7QFinite epsilon W (p + x.1) x.2‖
        = |((taoSection7HoldPMF x.1).toReal *
          (taoSection7HoldListPMF K x.2).toReal) *
          taoSection7QFinite epsilon W (p + x.1) x.2| := by
            rw [Real.norm_eq_abs]
    _ = ((taoSection7HoldPMF x.1).toReal *
          (taoSection7HoldListPMF K x.2).toReal) *
          |taoSection7QFinite epsilon W (p + x.1) x.2| := by
            rw [abs_mul, abs_of_nonneg hm0]
    _ ≤ ((taoSection7HoldPMF x.1).toReal *
          (taoSection7HoldListPMF K x.2).toReal) * 1 := by
            exact mul_le_mul_of_nonneg_left hqabs hm0
    _ = (taoSection7HoldPMF x.1).toReal *
          (taoSection7HoldListPMF K x.2).toReal := by ring

theorem taoSection7QFiniteTerminalOneApprox_succ
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (K : ℕ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    taoSection7QFiniteTerminalOneApprox (K + 1) epsilon W p =
      taoSection7QWhiteFactor epsilon W p *
        taoSection7HoldExpectationFull
          (fun h => taoSection7QFiniteTerminalOneApprox K epsilon W (p + h)) := by
  unfold taoSection7QFiniteTerminalOneApprox
  unfold taoSection7HoldExpectationFull
  have hnil :
      (taoSection7HoldListPMF (K + 1) ([] : List TaoSection7RenewalPoint)).toReal *
          taoSection7QFinite epsilon W p [] = 0 := by
    rw [taoSection7HoldListPMF_succ_apply_nil]
    simp
  calc
    (∑' hs : List TaoSection7RenewalPoint,
        (taoSection7HoldListPMF (K + 1) hs).toReal *
          taoSection7QFinite epsilon W p hs)
        = ∑' x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint,
            (taoSection7HoldListPMF (K + 1) (x.1 :: x.2)).toReal *
              taoSection7QFinite epsilon W p (x.1 :: x.2) := by
          exact taoSection7_tsum_list_eq_tsum_cons_of_nil_zero
            (f := fun hs : List TaoSection7RenewalPoint =>
              (taoSection7HoldListPMF (K + 1) hs).toReal *
                taoSection7QFinite epsilon W p hs)
            hnil
    _ = ∑' x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint,
          taoSection7QWhiteFactor epsilon W p *
            ((taoSection7HoldPMF x.1).toReal *
              (taoSection7HoldListPMF K x.2).toReal *
              taoSection7QFinite epsilon W (p + x.1) x.2) := by
          apply tsum_congr
          intro x
          rw [taoSection7HoldListPMF_succ_apply_cons]
          rw [taoSection7QFinite_cons]
          rw [ENNReal.toReal_mul]
          ring
    _ = taoSection7QWhiteFactor epsilon W p *
          (∑' x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint,
            (taoSection7HoldPMF x.1).toReal *
              (taoSection7HoldListPMF K x.2).toReal *
              taoSection7QFinite epsilon W (p + x.1) x.2) := by
          rw [tsum_mul_left]
    _ = taoSection7QWhiteFactor epsilon W p *
          (∑' h : TaoSection7RenewalPoint,
            (taoSection7HoldPMF h).toReal *
              (∑' hs : List TaoSection7RenewalPoint,
                (taoSection7HoldListPMF K hs).toReal *
                  taoSection7QFinite epsilon W (p + h) hs)) := by
          congr 1
          have hsum :=
            taoSection7HoldPMF_mul_holdListPMF_mul_QFinite_summable
              hepsilon K W p
          have hfiber :
              ∀ h : TaoSection7RenewalPoint,
              Summable fun hs : List TaoSection7RenewalPoint =>
                (taoSection7HoldPMF h).toReal *
                    (taoSection7HoldListPMF K hs).toReal *
                    taoSection7QFinite epsilon W (p + h) hs := by
            intro h
            have hterm :
                Summable fun hs : List TaoSection7RenewalPoint =>
                  (taoSection7HoldListPMF K hs).toReal *
                    taoSection7QFinite epsilon W (p + h) hs :=
              taoSection7QFiniteTerminalOneApprox_summable hepsilon W (p + h)
            simpa [mul_assoc] using hterm.mul_left (taoSection7HoldPMF h).toReal
          rw [Summable.tsum_prod' hsum hfiber]
          apply tsum_congr
          intro h
          simpa [mul_assoc] using
            (tsum_mul_left
              (a := (taoSection7HoldPMF h).toReal)
              (f := fun hs : List TaoSection7RenewalPoint =>
                (taoSection7HoldListPMF K hs).toReal *
                  taoSection7QFinite epsilon W (p + h) hs))
    _ = taoSection7QWhiteFactor epsilon W p *
          (∑' h : TaoSection7RenewalPoint,
            (taoSection7HoldPMF h).toReal *
              (∑' hs : List TaoSection7RenewalPoint,
                (taoSection7HoldListPMF K hs).toReal *
                  taoSection7QFinite epsilon W (p + h) hs)) := by
          rfl

theorem taoSection7QFiniteTerminalOneApprox_succ_le
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (K : ℕ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    taoSection7QFiniteTerminalOneApprox (K + 1) epsilon W p ≤
      taoSection7QFiniteTerminalOneApprox K epsilon W p := by
  induction K generalizing p with
  | zero =>
      rw [taoSection7QFiniteTerminalOneApprox_succ hepsilon 0 W p]
      rw [taoSection7QFiniteTerminalOneApprox_zero]
      have hExpLe :
          taoSection7HoldExpectationFull
              (fun h : TaoSection7RenewalPoint =>
                taoSection7QFiniteTerminalOneApprox 0 epsilon W (p + h)) ≤ 1 :=
        taoSection7HoldExpectationFull_le_one_of_bounded01
          (fun h =>
            taoSection7QFiniteTerminalOneApprox_nonneg 0 epsilon W (p + h))
          (fun h =>
            taoSection7QFiniteTerminalOneApprox_le_one (K := 0) hepsilon W (p + h))
      calc
        taoSection7QWhiteFactor epsilon W p *
            taoSection7HoldExpectationFull
              (fun h : TaoSection7RenewalPoint =>
                taoSection7QFiniteTerminalOneApprox 0 epsilon W (p + h))
            ≤ taoSection7QWhiteFactor epsilon W p * 1 := by
              exact mul_le_mul_of_nonneg_left hExpLe
                (taoSection7QWhiteFactor_nonneg epsilon W p)
        _ = taoSection7QWhiteFactor epsilon W p := by ring
  | succ K ih =>
      rw [taoSection7QFiniteTerminalOneApprox_succ hepsilon (K + 1) W p]
      rw [taoSection7QFiniteTerminalOneApprox_succ hepsilon K W p]
      exact mul_le_mul_of_nonneg_left
        (taoSection7HoldExpectationFull_mono_of_bounded01
          (fun h =>
            taoSection7QFiniteTerminalOneApprox_nonneg (K + 1) epsilon W (p + h))
          (fun h =>
            taoSection7QFiniteTerminalOneApprox_le_one (K := K + 1)
              hepsilon W (p + h))
          (fun h =>
            taoSection7QFiniteTerminalOneApprox_nonneg K epsilon W (p + h))
          (fun h =>
            taoSection7QFiniteTerminalOneApprox_le_one (K := K)
              hepsilon W (p + h))
          (fun h => ih (p + h)))
        (taoSection7QWhiteFactor_nonneg epsilon W p)

theorem taoSection7QFiniteTerminalOneApprox_add_le_left
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (K L : ℕ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    taoSection7QFiniteTerminalOneApprox (K + L) epsilon W p ≤
      taoSection7QFiniteTerminalOneApprox K epsilon W p := by
  induction L with
  | zero =>
      rw [Nat.add_zero]
  | succ L ih =>
      rw [Nat.add_succ]
      exact
        (taoSection7QFiniteTerminalOneApprox_succ_le
          hepsilon (K + L) W p).trans ih

def TaoSection7ActualQFiniteLimitStatement
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (Q : TaoSection7RenewalPoint → ℝ) : Prop :=
  ∀ p : TaoSection7RenewalPoint,
    Filter.Tendsto
      (fun K : ℕ => taoSection7QFiniteTerminalOneApprox K epsilon W p)
      Filter.atTop
      (𝓝 (Q p))

theorem taoSection7ActualQ_nonneg_of_finiteLimit
    {epsilon : ℝ} {W : TaoSection7RenewalPoint → Prop}
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (p : TaoSection7RenewalPoint) :
    0 ≤ Q p := by
  exact ge_of_tendsto (hQ p)
    (Filter.Eventually.of_forall fun K =>
      taoSection7QFiniteTerminalOneApprox_nonneg K epsilon W p)

theorem taoSection7ActualQ_le_one_of_finiteLimit
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {W : TaoSection7RenewalPoint → Prop}
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (p : TaoSection7RenewalPoint) :
    Q p ≤ 1 := by
  exact le_of_tendsto (hQ p)
    (Filter.Eventually.of_forall fun K =>
      taoSection7QFiniteTerminalOneApprox_le_one hepsilon W p)

end Tao

end Erdos1135Predecessor
