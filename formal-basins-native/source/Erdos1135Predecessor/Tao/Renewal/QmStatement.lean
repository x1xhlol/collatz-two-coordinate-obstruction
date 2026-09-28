/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.SourceActualQ
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

abbrev TaoSection7Q := TaoSection7RenewalPoint → ℝ

def taoSection7QDistanceToCutoff
    (J : ℕ) (p : TaoSection7RenewalPoint) : ℕ :=
  max (J - (p.j : ℕ)) 1

def taoSection7QmTail
    (J m : ℕ) (p : TaoSection7RenewalPoint) : Prop :=
  J - m ≤ (p.j : ℕ)

def taoSection7QmBoundary
    (J m : ℕ) (p : TaoSection7RenewalPoint) : Prop :=
  (p.j : ℕ) + m = J

noncomputable def taoSection7QmWeightedValue
    (J A : ℕ) (Q : TaoSection7Q)
    (p : TaoSection7RenewalPoint) : ℝ :=
  (taoSection7QDistanceToCutoff J p : ℝ) ^ A * Q p

noncomputable def taoSection7QmValueSet
    (J A : ℕ) (Q : TaoSection7Q) (m : ℕ) : Set ℝ :=
  {x | ∃ p : TaoSection7RenewalPoint,
      taoSection7QmTail J m p ∧
        x = taoSection7QmWeightedValue J A Q p}

noncomputable def taoSection7SourceQm
    (J A : ℕ) (Q : TaoSection7Q) (m : ℕ) : ℝ :=
  sSup (taoSection7QmValueSet J A Q m)

noncomputable def taoSection7SourceActualQm
    (n J A m : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) : ℝ :=
  taoSection7SourceQm J A (taoSection7SourceActualQ n xi epsilon) m

noncomputable def taoSection7SourceActualQmAtCutoff
    (n A m : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) : ℝ :=
  taoSection7SourceActualQm n (n / 2) A m xi epsilon

theorem taoSection7QmValueSet_nonempty
    (J A : ℕ) (Q : TaoSection7Q) (m : ℕ) :
    (taoSection7QmValueSet J A Q m).Nonempty := by
  let p : TaoSection7RenewalPoint :=
    { j := ⟨J + 1, by omega⟩, l := 0 }
  refine ⟨taoSection7QmWeightedValue J A Q p, ?_⟩
  refine ⟨p, ?_, rfl⟩
  unfold taoSection7QmTail
  dsimp [p]
  omega

theorem taoSection7QmValueSet_mono
    {J A a b : ℕ} {Q : TaoSection7Q}
    (hab : a ≤ b) :
    taoSection7QmValueSet J A Q a ⊆
      taoSection7QmValueSet J A Q b := by
  rintro x ⟨p, hp, rfl⟩
  refine ⟨p, ?_, rfl⟩
  unfold taoSection7QmTail at *
  omega

theorem taoSection7QDistanceToCutoff_le_max
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hp : taoSection7QmTail J m p) :
    taoSection7QDistanceToCutoff J p ≤ max m 1 := by
  unfold taoSection7QDistanceToCutoff taoSection7QmTail at *
  have hsub : J - (p.j : ℕ) ≤ m := by omega
  exact max_le (le_trans hsub (Nat.le_max_left m 1)) (Nat.le_max_right m 1)

theorem taoSection7QmWeightedValue_nonneg_of_nonneg
    {J A : ℕ} {Q : TaoSection7Q}
    (hQ : ∀ p : TaoSection7RenewalPoint, 0 ≤ Q p)
    (p : TaoSection7RenewalPoint) :
    0 ≤ taoSection7QmWeightedValue J A Q p := by
  unfold taoSection7QmWeightedValue
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) A) (hQ p)

theorem taoSection7QmWeightedValue_le_max_pow_of_bounded01
    {J A m : ℕ} {Q : TaoSection7Q}
    (hQ : TaoSection7QBounded01 Q)
    {p : TaoSection7RenewalPoint}
    (hp : taoSection7QmTail J m p) :
    taoSection7QmWeightedValue J A Q p ≤ ((max m 1 : ℕ) : ℝ) ^ A := by
  have hd := taoSection7QDistanceToCutoff_le_max
    (J := J) (m := m) (p := p) hp
  have hdReal :
      (taoSection7QDistanceToCutoff J p : ℝ) ≤ ((max m 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr hd
  have hpow :
      (taoSection7QDistanceToCutoff J p : ℝ) ^ A ≤
        ((max m 1 : ℕ) : ℝ) ^ A :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hdReal A
  have hweight0 : 0 ≤ (taoSection7QDistanceToCutoff J p : ℝ) ^ A :=
    pow_nonneg (Nat.cast_nonneg _) A
  unfold taoSection7QmWeightedValue
  calc
    (taoSection7QDistanceToCutoff J p : ℝ) ^ A * Q p
        ≤ (taoSection7QDistanceToCutoff J p : ℝ) ^ A * 1 := by
          exact mul_le_mul_of_nonneg_left (hQ p).2 hweight0
    _ = (taoSection7QDistanceToCutoff J p : ℝ) ^ A := by ring
    _ ≤ ((max m 1 : ℕ) : ℝ) ^ A := hpow

theorem taoSection7QmValueSet_bddAbove_of_bounded01
    {J A m : ℕ} {Q : TaoSection7Q}
    (hQ : TaoSection7QBounded01 Q) :
    BddAbove (taoSection7QmValueSet J A Q m) := by
  refine ⟨((max m 1 : ℕ) : ℝ) ^ A, ?_⟩
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  exact taoSection7QmWeightedValue_le_max_pow_of_bounded01
    (J := J) (A := A) (m := m) (Q := Q) hQ hp

theorem taoSection7SourceQm_mono_of_le
    {J A a b : ℕ} {Q : TaoSection7Q}
    (hab : a ≤ b)
    (hbdd : BddAbove (taoSection7QmValueSet J A Q b)) :
    taoSection7SourceQm J A Q a ≤
      taoSection7SourceQm J A Q b := by
  unfold taoSection7SourceQm
  exact csSup_le_csSup hbdd
    (taoSection7QmValueSet_nonempty J A Q a)
    (taoSection7QmValueSet_mono hab)

theorem taoSection7SourceQm_nonneg_of_nonneg_bddAbove
    {J A m : ℕ} {Q : TaoSection7Q}
    (hQ : ∀ p : TaoSection7RenewalPoint, 0 ≤ Q p)
    (hbdd : BddAbove (taoSection7QmValueSet J A Q m)) :
    0 ≤ taoSection7SourceQm J A Q m := by
  unfold taoSection7SourceQm
  rcases taoSection7QmValueSet_nonempty J A Q m with ⟨x, hx⟩
  have hx_nonneg : 0 ≤ x := by
    rcases hx with ⟨p, _hp, rfl⟩
    exact taoSection7QmWeightedValue_nonneg_of_nonneg
      (J := J) (A := A) (Q := Q) hQ p
  exact le_trans hx_nonneg (le_csSup hbdd hx)

theorem taoSection7SourceActualQm_nonneg
    {n J A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    0 ≤ taoSection7SourceActualQm n J A m xi epsilon := by
  unfold taoSection7SourceActualQm
  exact taoSection7SourceQm_nonneg_of_nonneg_bddAbove
    (J := J) (A := A) (m := m)
    (Q := taoSection7SourceActualQ n xi epsilon)
    (fun p => taoSection7SourceActualQ_nonneg
      (n := n) (xi := xi) hepsilon p)
    (taoSection7QmValueSet_bddAbove_of_bounded01
      (J := J) (A := A) (m := m)
      (Q := taoSection7SourceActualQ n xi epsilon)
      (taoSection7SourceActualQ_bounded01
        (n := n) (xi := xi) hepsilon))

theorem taoSection7SourceActualQmAtCutoff_nonneg
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    0 ≤ taoSection7SourceActualQmAtCutoff n A m xi epsilon := by
  unfold taoSection7SourceActualQmAtCutoff
  exact taoSection7SourceActualQm_nonneg
    (J := n / 2) (A := A) (m := m) (xi := xi) hepsilon

theorem taoSection7SourceActualQmAtCutoff_mono_of_le
    {n A a b : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hab : a ≤ b) :
    taoSection7SourceActualQmAtCutoff n A a xi epsilon ≤
      taoSection7SourceActualQmAtCutoff n A b xi epsilon := by
  unfold taoSection7SourceActualQmAtCutoff taoSection7SourceActualQm
  exact taoSection7SourceQm_mono_of_le hab
    (taoSection7QmValueSet_bddAbove_of_bounded01
      (taoSection7SourceActualQ_bounded01
        (n := n) (xi := xi) hepsilon))

theorem taoSection7QmTail_split_prev_or_boundary
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hm : 1 ≤ m)
    (hp : taoSection7QmTail J m p) :
    taoSection7QmTail J (m - 1) p ∨
      taoSection7QmBoundary J m p := by
  by_cases hprev : taoSection7QmTail J (m - 1) p
  · exact Or.inl hprev
  · right
    unfold taoSection7QmTail taoSection7QmBoundary at *
    omega

theorem taoSection7QDistanceToCutoff_eq_of_boundary
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hm : 1 ≤ m) (hboundary : taoSection7QmBoundary J m p) :
    taoSection7QDistanceToCutoff J p = m := by
  unfold taoSection7QDistanceToCutoff taoSection7QmBoundary at *
  have hsub : J - (p.j : ℕ) = m := by omega
  rw [hsub]
  exact max_eq_left hm

theorem taoSection7Prop78Monotonicity_of_boundary741
    {J A m : ℕ} {Q : TaoSection7Q}
    (hm : 1 ≤ m)
    (hprev_bdd : BddAbove (taoSection7QmValueSet J A Q (m - 1)))
    (hboundary : ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary J m p →
        Q p ≤ ((m : ℝ) ^ A)⁻¹ *
          taoSection7SourceQm J A Q (m - 1)) :
    taoSection7SourceQm J A Q m ≤
      taoSection7SourceQm J A Q (m - 1) := by
  unfold taoSection7SourceQm
  refine csSup_le (taoSection7QmValueSet_nonempty J A Q m) ?_
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  rcases taoSection7QmTail_split_prev_or_boundary (J := J) (m := m)
      (p := p) hm hp with hprev | hbd
  · exact le_csSup hprev_bdd ⟨p, hprev, rfl⟩
  · have hdist := taoSection7QDistanceToCutoff_eq_of_boundary
      (J := J) (m := m) (p := p) hm hbd
    have hpow_nonneg : 0 ≤ ((m : ℝ) ^ A) :=
      pow_nonneg (Nat.cast_nonneg m) A
    have hpow_ne : ((m : ℝ) ^ A) ≠ 0 := by
      exact ne_of_gt (pow_pos
        (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hm)) A)
    unfold taoSection7QmWeightedValue
    rw [hdist]
    calc
      (m : ℝ) ^ A * Q p
          ≤ (m : ℝ) ^ A *
              (((m : ℝ) ^ A)⁻¹ *
                sSup (taoSection7QmValueSet J A Q (m - 1))) := by
            exact mul_le_mul_of_nonneg_left (hboundary p hbd) hpow_nonneg
      _ = sSup (taoSection7QmValueSet J A Q (m - 1)) := by
            field_simp [hpow_ne]

theorem taoSection7SourceActualQm_monotonicity_of_boundary741
    {n J A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hm : 1 ≤ m)
    (hboundary : ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary J m p →
        taoSection7SourceActualQ n xi epsilon p ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQm n J A (m - 1) xi epsilon) :
    taoSection7SourceActualQm n J A m xi epsilon ≤
      taoSection7SourceActualQm n J A (m - 1) xi epsilon := by
  unfold taoSection7SourceActualQm
  exact taoSection7Prop78Monotonicity_of_boundary741
    (J := J) (A := A) (m := m)
    (Q := taoSection7SourceActualQ n xi epsilon)
    hm
    (taoSection7QmValueSet_bddAbove_of_bounded01
      (J := J) (A := A) (m := m - 1)
      (Q := taoSection7SourceActualQ n xi epsilon)
      (taoSection7SourceActualQ_bounded01
        (n := n) (xi := xi) hepsilon))
    hboundary

def taoSection7Prop78LowerThreshold : ℕ := 1

theorem taoSection7SourceProp78Monotonicity
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hm_low : taoSection7Prop78LowerThreshold ≤ m)
    (hm_hi : m ≤ n / 2)
    (hboundary : ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        taoSection7SourceActualQ n xi epsilon p ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) :
    taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
      taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  have hm : 1 ≤ m := by
    simpa [taoSection7Prop78LowerThreshold] using hm_low
  have _hm_hi : m ≤ n / 2 := hm_hi
  unfold taoSection7SourceActualQmAtCutoff at *
  exact taoSection7SourceActualQm_monotonicity_of_boundary741
    (n := n) (J := n / 2) (A := A) (m := m)
    (xi := xi) (epsilon := epsilon) hepsilon hm hboundary

end Tao

end Erdos1135Predecessor
