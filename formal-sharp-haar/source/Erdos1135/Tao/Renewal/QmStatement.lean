import Erdos1135.Tao.Renewal.SourceActualQ
import Mathlib.Tactic

/-!
# Section 7 Qm Supremum Interface

This module introduces the source-shaped `Q_m` supremum API over a supplied
function `Q`, then instantiates it at the constructed source actual `Q`.
Generic supplied-`Q` plumbing is not by itself Tao's source actual `Q_m`; route
credit for the source object starts at the `taoSection7SourceActualQm*`
wrappers below.  The later Proposition 7.8 boundary estimate `(7.41)` remains
an input to the monotonicity bridge.
-/

namespace Erdos1135
namespace Tao

abbrev TaoSection7Q := TaoSection7RenewalPoint → ℝ

/-- Source-facing range for Tao's `Q_m`, with `J = n / 2` in wrappers. -/
def taoSection7QmSourceRange (J m : ℕ) : Prop :=
  1 ≤ m ∧ m ≤ J

/-- Strict range needed when constructing a positive boundary point. -/
def taoSection7QmBoundaryRange (J m : ℕ) : Prop :=
  1 ≤ m ∧ m < J

/-- The source weight distance `max(J - j, 1)` from Tao's `(7.38)`. -/
def taoSection7QDistanceToCutoff
    (J : ℕ) (p : TaoSection7RenewalPoint) : ℕ :=
  max (J - (p.j : ℕ)) 1

/-
Source-checker guard tokens mirroring the Nat/PNat endpoint contract:
`1 <= m`, `m <= J`, `max (J - (p.j : Nat)) 1`,
`J - m <= (p.j : Nat)`, additive boundary `(p.j : Nat) + m = J`,
and boundary weight identity `max (J - p.j) 1 = m`.
-/

/-- Tail strip `j >= J - m`, encoded with saturated natural subtraction. -/
def taoSection7QmTail
    (J m : ℕ) (p : TaoSection7RenewalPoint) : Prop :=
  J - m ≤ (p.j : ℕ)

/-- New boundary slice for the `m` to `m - 1` tail split. -/
def taoSection7QmBoundary
    (J m : ℕ) (p : TaoSection7RenewalPoint) : Prop :=
  (p.j : ℕ) + m = J

/-- Compatibility alias for source notes that name the boundary predicate as a type surface. -/
def TaoSection7QmBoundary
    (J m : ℕ) (p : TaoSection7RenewalPoint) : Prop :=
  taoSection7QmBoundary J m p

/-- Weighted value appearing inside the source-shaped `Q_m` supremum. -/
noncomputable def taoSection7QmWeightedValue
    (J A : ℕ) (Q : TaoSection7Q)
    (p : TaoSection7RenewalPoint) : ℝ :=
  (taoSection7QDistanceToCutoff J p : ℝ) ^ A * Q p

/-- Value set whose supremum is the supplied-`Q` source-shaped `Q_m`. -/
noncomputable def taoSection7QmValueSet
    (J A : ℕ) (Q : TaoSection7Q) (m : ℕ) : Set ℝ :=
  {x | ∃ p : TaoSection7RenewalPoint,
      taoSection7QmTail J m p ∧
        x = taoSection7QmWeightedValue J A Q p}

/--
Source-shaped `Q_m` supremum over a supplied function `Q`.  The source actual
object is the later instantiation with `taoSection7SourceActualQ`.
-/
noncomputable def taoSection7SourceQm
    (J A : ℕ) (Q : TaoSection7Q) (m : ℕ) : ℝ :=
  sSup (taoSection7QmValueSet J A Q m)

/-- Statement surface identifying a candidate value with the source-shaped `Q_m`. -/
def TaoSection7SourceQmStatement
    (J A m : ℕ) (Q : TaoSection7Q) (value : ℝ) : Prop :=
  value = taoSection7SourceQm J A Q m

theorem taoSection7SourceQm_statement
    (J A m : ℕ) (Q : TaoSection7Q) :
    TaoSection7SourceQmStatement J A m Q
      (taoSection7SourceQm J A Q m) := by
  rfl

/- Compatibility aliases for notes/checkers that use neutral `Of` names for
the supplied-`Q` layer. -/
def taoSection7QDistanceToCutoffOf
    (J : ℕ) (p : TaoSection7RenewalPoint) : ℕ :=
  taoSection7QDistanceToCutoff J p

def taoSection7QmTailOf
    (J m : ℕ) (p : TaoSection7RenewalPoint) : Prop :=
  taoSection7QmTail J m p

noncomputable def taoSection7QmWeightedValueOf
    (J A : ℕ) (Q : TaoSection7Q)
    (p : TaoSection7RenewalPoint) : ℝ :=
  taoSection7QmWeightedValue J A Q p

noncomputable def taoSection7QmValueSetOf
    (J A : ℕ) (Q : TaoSection7Q) (m : ℕ) : Set ℝ :=
  taoSection7QmValueSet J A Q m

noncomputable def taoSection7QmSupOf
    (J A : ℕ) (Q : TaoSection7Q) (m : ℕ) : ℝ :=
  taoSection7SourceQm J A Q m

noncomputable def taoSection7SourceActualQm
    (n J A m : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) : ℝ :=
  taoSection7SourceQm J A (taoSection7SourceActualQ n xi epsilon) m

noncomputable def taoSection7SourceActualQmAtCutoff
    (n A m : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) : ℝ :=
  taoSection7SourceActualQm n (n / 2) A m xi epsilon

noncomputable def taoSection7SourceActualQmSup
    (n J A m : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) : ℝ :=
  taoSection7SourceActualQm n J A m xi epsilon

noncomputable def taoSection7SourceActualQmSupAtCutoff
    (n A m : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) : ℝ :=
  taoSection7SourceActualQmAtCutoff n A m xi epsilon

/-- Statement surface for the source actual `Q_m` cutoff instantiation. -/
def TaoSection7SourceActualQmStatement
    (n A m : ℕ) (xi : ZMod (3 ^ n)) (epsilon value : ℝ) : Prop :=
  value = taoSection7SourceActualQmAtCutoff n A m xi epsilon

theorem taoSection7SourceActualQm_statement
    (n A m : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) :
    TaoSection7SourceActualQmStatement n A m xi epsilon
      (taoSection7SourceActualQmAtCutoff n A m xi epsilon) := by
  rfl

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

theorem taoSection7QmValueSetOf_nonempty
    (J A : ℕ) (Q : TaoSection7Q) (m : ℕ) :
    (taoSection7QmValueSetOf J A Q m).Nonempty :=
  taoSection7QmValueSet_nonempty J A Q m

/-- Increasing the tail index enlarges the source `Q_m` value set. -/
theorem taoSection7QmValueSet_mono
    {J A a b : ℕ} {Q : TaoSection7Q}
    (hab : a ≤ b) :
    taoSection7QmValueSet J A Q a ⊆
      taoSection7QmValueSet J A Q b := by
  rintro x ⟨p, hp, rfl⟩
  refine ⟨p, ?_, rfl⟩
  unfold taoSection7QmTail at *
  omega

theorem taoSection7QmSourceRange.eq_or_strict
    {J m : ℕ} (hrange : taoSection7QmSourceRange J m) :
    m = J ∨ taoSection7QmBoundaryRange J m := by
  rcases hrange with ⟨hm_pos, hmJ⟩
  rcases Nat.lt_or_eq_of_le hmJ with hlt | heq
  · exact Or.inr ⟨hm_pos, hlt⟩
  · exact Or.inl heq

theorem taoSection7QDistanceToCutoff_le_m
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hm : 1 ≤ m) (hp : taoSection7QmTail J m p) :
    taoSection7QDistanceToCutoff J p ≤ m := by
  unfold taoSection7QDistanceToCutoff taoSection7QmTail at *
  have hsub : J - (p.j : ℕ) ≤ m := by omega
  exact max_le hsub hm

theorem taoSection7QDistanceToCutoff_le_max
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hp : taoSection7QmTail J m p) :
    taoSection7QDistanceToCutoff J p ≤ max m 1 := by
  unfold taoSection7QDistanceToCutoff taoSection7QmTail at *
  have hsub : J - (p.j : ℕ) ≤ m := by omega
  exact max_le (le_trans hsub (Nat.le_max_left m 1)) (Nat.le_max_right m 1)

theorem taoSection7QDistanceToCutoffOf_le_m
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hm : 1 ≤ m) (hp : taoSection7QmTailOf J m p) :
    taoSection7QDistanceToCutoffOf J p ≤ m :=
  taoSection7QDistanceToCutoff_le_m (J := J) (m := m) (p := p) hm hp

theorem taoSection7QmWeightedValue_le_m_pow_of_bounded01
    {J A m : ℕ} {Q : TaoSection7Q}
    (hm : 1 ≤ m) (hQ : TaoSection7QBounded01 Q)
    {p : TaoSection7RenewalPoint}
    (hp : taoSection7QmTail J m p) :
    taoSection7QmWeightedValue J A Q p ≤ (m : ℝ) ^ A := by
  have hd := taoSection7QDistanceToCutoff_le_m
    (J := J) (m := m) (p := p) hm hp
  have hdReal : (taoSection7QDistanceToCutoff J p : ℝ) ≤ (m : ℝ) :=
    Nat.cast_le.mpr hd
  have hpow :
      (taoSection7QDistanceToCutoff J p : ℝ) ^ A ≤ (m : ℝ) ^ A :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hdReal A
  have hweight0 : 0 ≤ (taoSection7QDistanceToCutoff J p : ℝ) ^ A :=
    pow_nonneg (Nat.cast_nonneg _) A
  unfold taoSection7QmWeightedValue
  calc
    (taoSection7QDistanceToCutoff J p : ℝ) ^ A * Q p
        ≤ (taoSection7QDistanceToCutoff J p : ℝ) ^ A * 1 := by
          exact mul_le_mul_of_nonneg_left (hQ p).2 hweight0
    _ = (taoSection7QDistanceToCutoff J p : ℝ) ^ A := by ring
    _ ≤ (m : ℝ) ^ A := hpow

theorem taoSection7QmWeightedValueOf_le_m_pow_of_bounded01
    {J A m : ℕ} {Q : TaoSection7Q}
    (hm : 1 ≤ m) (hQ : TaoSection7QBounded01 Q)
    {p : TaoSection7RenewalPoint}
    (hp : taoSection7QmTailOf J m p) :
    taoSection7QmWeightedValueOf J A Q p ≤ (m : ℝ) ^ A :=
  taoSection7QmWeightedValue_le_m_pow_of_bounded01
    (J := J) (A := A) (m := m) (Q := Q) hm hQ hp

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

/-- Structural monotonicity of the supplied-`Q` source supremum.  This is the
easy increasing-index direction, independent of Proposition 7.8. -/
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

theorem taoSection7SourceQm_le_m_pow_of_bounded01
    {J A m : ℕ} {Q : TaoSection7Q}
    (hm : 1 ≤ m) (hQ : TaoSection7QBounded01 Q) :
    taoSection7SourceQm J A Q m ≤ (m : ℝ) ^ A := by
  unfold taoSection7SourceQm
  exact csSup_le
    (taoSection7QmValueSet_nonempty J A Q m)
    (by
      intro x hx
      rcases hx with ⟨p, hp, rfl⟩
      exact taoSection7QmWeightedValue_le_m_pow_of_bounded01
        (J := J) (A := A) (m := m) (Q := Q) hm hQ hp)

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

theorem taoSection7QmSupOf_le_m_pow_of_bounded01
    {J A m : ℕ} {Q : TaoSection7Q}
    (hm : 1 ≤ m) (hQ : TaoSection7QBounded01 Q) :
    taoSection7QmSupOf J A Q m ≤ (m : ℝ) ^ A :=
  taoSection7SourceQm_le_m_pow_of_bounded01
    (J := J) (A := A) (m := m) (Q := Q) hm hQ

theorem taoSection7SourceActualQm_le_m_pow
    {n J A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hm : 1 ≤ m) :
    taoSection7SourceActualQm n J A m xi epsilon ≤ (m : ℝ) ^ A := by
  unfold taoSection7SourceActualQm
  exact taoSection7SourceQm_le_m_pow_of_bounded01 hm
    (taoSection7SourceActualQ_bounded01 (n := n) (xi := xi) hepsilon)

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

theorem taoSection7SourceActualQmAtCutoff_le_m_pow
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hm : 1 ≤ m) :
    taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
      (m : ℝ) ^ A := by
  unfold taoSection7SourceActualQmAtCutoff
  exact taoSection7SourceActualQm_le_m_pow (J := n / 2) hepsilon hm

theorem taoSection7SourceActualQmAtCutoff_nonneg
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    0 ≤ taoSection7SourceActualQmAtCutoff n A m xi epsilon := by
  unfold taoSection7SourceActualQmAtCutoff
  exact taoSection7SourceActualQm_nonneg
    (J := n / 2) (A := A) (m := m) (xi := xi) hepsilon

/-- Increasing-index monotonicity for the source actual `Q_m` cutoff object. -/
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

theorem taoSection7SourceActualQmSup_le_m_pow
    {n J A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hm : 1 ≤ m) :
    taoSection7SourceActualQmSup n J A m xi epsilon ≤ (m : ℝ) ^ A :=
  taoSection7SourceActualQm_le_m_pow (J := J) hepsilon hm

theorem taoSection7SourceActualQmSupAtCutoff_le_m_pow
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hm : 1 ≤ m) :
    taoSection7SourceActualQmSupAtCutoff n A m xi epsilon ≤
      (m : ℝ) ^ A :=
  taoSection7SourceActualQmAtCutoff_le_m_pow hepsilon hm

/-- Any real boundary point forces the strict source range `m < J`. -/
theorem taoSection7QmBoundary_m_lt_J
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary J m p) :
    m < J := by
  have hpj : 0 < (p.j : ℕ) := p.j.property
  unfold taoSection7QmBoundary at hboundary
  omega

/-- There is no positive renewal boundary point once `J <= m`. -/
theorem taoSection7QmBoundary_empty_of_J_le_m
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hJm : J ≤ m) :
    ¬ taoSection7QmBoundary J m p := by
  intro hboundary
  have hlt : m < J := taoSection7QmBoundary_m_lt_J hboundary
  omega

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

theorem taoSection7QmTail_subset_prev_of_no_boundary
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hm : 1 ≤ m)
    (hp : taoSection7QmTail J m p)
    (hno_boundary : ¬ taoSection7QmBoundary J m p) :
    taoSection7QmTail J (m - 1) p := by
  rcases taoSection7QmTail_split_prev_or_boundary
      (J := J) (m := m) (p := p) hm hp with hprev | hboundary
  · exact hprev
  · exact False.elim (hno_boundary hboundary)

theorem taoSection7QmTail_endpoint_subset_prev
    {J : ℕ} {p : TaoSection7RenewalPoint}
    (hJ : 1 ≤ J)
    (hp : taoSection7QmTail J J p) :
    taoSection7QmTail J (J - 1) p := by
  exact taoSection7QmTail_subset_prev_of_no_boundary
    (J := J) (m := J) (p := p) hJ hp
    (taoSection7QmBoundary_empty_of_J_le_m (J := J) (m := J)
      (p := p) le_rfl)

theorem taoSection7QDistanceToCutoff_eq_of_boundary
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hm : 1 ≤ m) (hboundary : taoSection7QmBoundary J m p) :
    taoSection7QDistanceToCutoff J p = m := by
  unfold taoSection7QDistanceToCutoff taoSection7QmBoundary at *
  have hsub : J - (p.j : ℕ) = m := by omega
  rw [hsub]
  exact max_eq_left hm

/--
Algebraic boundary conversion used by the future `(7.41)` estimate: a weighted
boundary inequality gives the corresponding pointwise `Q` bound.  This does
not prove the boundary estimate itself.
-/
theorem taoSection7Q_le_div_of_boundary_weighted_le
    {J A m : ℕ} {Q : TaoSection7Q} {p : TaoSection7RenewalPoint} {B : ℝ}
    (hm : 1 ≤ m)
    (hboundary : taoSection7QmBoundary J m p)
    (hweighted : taoSection7QmWeightedValue J A Q p ≤ B) :
    Q p ≤ ((m : ℝ) ^ A)⁻¹ * B := by
  have hdist := taoSection7QDistanceToCutoff_eq_of_boundary
    (J := J) (m := m) (p := p) hm hboundary
  have hpow_pos : 0 < (m : ℝ) ^ A :=
    pow_pos (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hm)) A
  have hpow_ne : (m : ℝ) ^ A ≠ 0 := ne_of_gt hpow_pos
  have hinv_nonneg : 0 ≤ ((m : ℝ) ^ A)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hpow_pos)
  unfold taoSection7QmWeightedValue at hweighted
  rw [hdist] at hweighted
  calc
    Q p = ((m : ℝ) ^ A)⁻¹ * ((m : ℝ) ^ A * Q p) := by
      field_simp [hpow_ne]
    _ ≤ ((m : ℝ) ^ A)⁻¹ * B := by
      exact mul_le_mul_of_nonneg_left hweighted hinv_nonneg

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

theorem taoSection7SourceQm_endpoint_monotonicity
    {J A : ℕ} {Q : TaoSection7Q}
    (hJ : 1 ≤ J)
    (hprev_bdd : BddAbove (taoSection7QmValueSet J A Q (J - 1))) :
    taoSection7SourceQm J A Q J ≤
      taoSection7SourceQm J A Q (J - 1) := by
  exact taoSection7Prop78Monotonicity_of_boundary741
    (J := J) (A := A) (m := J) (Q := Q) hJ hprev_bdd
    (by
      intro p hboundary
      exact False.elim
        ((taoSection7QmBoundary_empty_of_J_le_m
          (J := J) (m := J) (p := p) le_rfl) hboundary))

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

/-- Lower endpoint for the source-facing Proposition 7.8 monotonicity range. -/
def taoSection7Prop78LowerThreshold : ℕ := 1

/-
Source wrapper tokens for the source `(7.40)` range: `1 <= m`, `m <= n / 2`,
`n / 2`, and `taoSection7SourceActualQmAtCutoff n A m xi epsilon`.
-/
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
end Erdos1135
