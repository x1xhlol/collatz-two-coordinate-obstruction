import Erdos1135.Tao.Syracuse.AffineTrajectory
import Erdos1135.Tao.Syracuse.FirstPassage
import Mathlib.Tactic

/-!
# Cleared First-Passage Interval Bounds

This neutral leaf isolates the predecessor-indexed deterministic inequalities
behind the repaired Section 5 endpoint intervals.  All public bounds are in
`Nat`, so later consumers can form quotient endpoints without a real
floor/ceiling round trip.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- The positive valuation removed at the step after time `r`. -/
def syracuseTerminalExponentPNat
    (r M : ℕ) (hM : Odd M) : ℕ+ :=
  ⟨syracuseExponent ((syracuse^[r]) M),
    syracuseExponent_pos_of_odd
      (syracuse_iterate_odd_trajectory r M hM)⟩

/-- A valuation list through time `r+1` is its length-`r` prefix followed by
the valuation of the predecessor state. -/
theorem syracuseValuationPNatList_succ_eq_append_terminal
    (r M : ℕ) (hM : Odd M) :
    syracuseValuationPNatList (r + 1) M hM =
      syracuseValuationPNatList r M hM ++
        [syracuseTerminalExponentPNat r M hM] := by
  rw [syracuseValuationPNatList_add r 1 M hM]
  simp [syracuseValuationPNatList, syracuseTerminalExponentPNat]

/-- The full valuation weight is the prefix weight plus the terminal
valuation. -/
theorem taoTupleWeight_syracuseValuationPNatList_succ
    (r M : ℕ) (hM : Odd M) :
    taoTupleWeight (syracuseValuationPNatList (r + 1) M hM) =
      taoTupleWeight (syracuseValuationPNatList r M hM) +
        (syracuseTerminalExponentPNat r M hM : ℕ) := by
  rw [syracuseValuationPNatList_succ_eq_append_terminal,
    taoTupleWeight_append_trajectory]
  simp [taoTupleWeight]

private theorem predecessor_lt_twice_affine_main
    {B M r : ℕ} (hM : Odd M)
    (hroom : 2 * 3 ^ r ≤ B)
    (hfirst : syracuseFirstHitAtMost B M (r + 1)) :
    ((syracuse^[r]) M : ℚ) <
      2 * ((3 : ℚ) ^ r /
        (2 : ℚ) ^
          taoTupleWeight (syracuseValuationPNatList r M hM) * M) := by
  have hpreNat : B < (syracuse^[r]) M :=
    hfirst.2 r (by omega)
  have hpre : (B : ℚ) < ((syracuse^[r]) M : ℚ) := by
    exact_mod_cast hpreNat
  have hroomQ : 2 * (3 : ℚ) ^ r ≤ (B : ℚ) := by
    exact_mod_cast hroom
  have henvelopeQ := syracuse_iterate_le_affine_envelope r M hM
  linarith

/-- A strict first hit at time `r+1` gives the cleared lower endpoint
inequality for the predecessor prefix. -/
theorem syracuseFirstHitAtMost_prefix_lower_cleared
    {B M r : ℕ} (hM : Odd M)
    (hroom : 2 * 3 ^ r ≤ B)
    (hfirst : syracuseFirstHitAtMost B M (r + 1)) :
    B * 2 ^ taoTupleWeight (syracuseValuationPNatList r M hM) <
      2 * 3 ^ r * M := by
  let W := taoTupleWeight (syracuseValuationPNatList r M hM)
  have hpreNat : B < (syracuse^[r]) M :=
    hfirst.2 r (by omega)
  have hpre : (B : ℚ) < ((syracuse^[r]) M : ℚ) := by
    exact_mod_cast hpreNat
  have hmain := predecessor_lt_twice_affine_main hM hroom hfirst
  have hpowPos : 0 < (2 : ℚ) ^ W := by positivity
  have hclearPre :
      (((syracuse^[r]) M : ℚ) * (2 : ℚ) ^ W) <
        2 * (3 : ℚ) ^ r * M := by
    have h := mul_lt_mul_of_pos_right hmain hpowPos
    dsimp [W] at h ⊢
    field_simp at h
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hclearB :
      (B : ℚ) * (2 : ℚ) ^ W < 2 * (3 : ℚ) ^ r * M :=
    (mul_lt_mul_of_pos_right hpre hpowPos).trans hclearPre
  exact_mod_cast hclearB

/-- The terminal hit gives the cleared weak upper endpoint inequality using
the full valuation weight. -/
theorem syracuseFirstHitAtMost_terminal_upper_cleared
    {B M r : ℕ} (hM : Odd M)
    (hfirst : syracuseFirstHitAtMost B M (r + 1)) :
    3 ^ (r + 1) * M ≤
      B * 2 ^ taoTupleWeight
        (syracuseValuationPNatList (r + 1) M hM) := by
  let S := taoTupleWeight
    (syracuseValuationPNatList (r + 1) M hM)
  have hmainQ := affineMainTerm_le_syracuse_iterate (r + 1) M hM
  have hterminalQ :
      (((syracuse^[r + 1]) M : ℕ) : ℚ) ≤ (B : ℚ) := by
    exact_mod_cast hfirst.1
  have hboundQ :
      (3 : ℚ) ^ (r + 1) / (2 : ℚ) ^ S * M ≤ (B : ℚ) := by
    exact hmainQ.trans hterminalQ
  have hpowPos : 0 < (2 : ℚ) ^ S := by positivity
  have hclearQ :
      (3 : ℚ) ^ (r + 1) * M ≤ (B : ℚ) * (2 : ℚ) ^ S := by
    have h := mul_le_mul_of_nonneg_right hboundQ hpowPos.le
    dsimp [S] at h ⊢
    field_simp at h
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  exact_mod_cast hclearQ

/-- The terminal valuation itself supplies the second strict lower endpoint.
The constant `8` comes from `2^a ≤ 3P+1 ≤ 4P` and the predecessor affine
bound `P < 2 * main`. -/
theorem syracuseFirstHitAtMost_terminal_lower_cleared
    {B M r : ℕ} (hM : Odd M)
    (hroom : 2 * 3 ^ r ≤ B)
    (hfirst : syracuseFirstHitAtMost B M (r + 1)) :
    2 ^ taoTupleWeight
        (syracuseValuationPNatList (r + 1) M hM) <
      8 * 3 ^ r * M := by
  let P := (syracuse^[r]) M
  let W := taoTupleWeight (syracuseValuationPNatList r M hM)
  let a := syracuseTerminalExponentPNat r M hM
  have hpreNat : B < P := by
    exact hfirst.2 r (by omega)
  have hPPos : 0 < P := by omega
  have hfactor : 2 ^ (a : ℕ) * syracuse P = 3 * P + 1 := by
    simpa [a, syracuseTerminalExponentPNat, P] using
      two_pow_syracuseExponent_mul_syracuse P
  have haLe : 2 ^ (a : ℕ) ≤ 4 * P := by
    calc
      2 ^ (a : ℕ) ≤ 2 ^ (a : ℕ) * syracuse P := by
        exact Nat.le_mul_of_pos_right _ (syracuse_pos P)
      _ = 3 * P + 1 := hfactor
      _ ≤ 4 * P := by omega
  have hmain := predecessor_lt_twice_affine_main hM hroom hfirst
  have hpowPos : 0 < (2 : ℚ) ^ W := by positivity
  have hPclearQ :
      (P : ℚ) * (2 : ℚ) ^ W < 2 * (3 : ℚ) ^ r * M := by
    have h := mul_lt_mul_of_pos_right hmain hpowPos
    dsimp [P, W] at h ⊢
    field_simp at h
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hPclear : P * 2 ^ W < 2 * 3 ^ r * M := by
    exact_mod_cast hPclearQ
  rw [taoTupleWeight_syracuseValuationPNatList_succ r M hM,
    pow_add]
  calc
    2 ^ W * 2 ^ (a : ℕ) ≤ 2 ^ W * (4 * P) :=
      Nat.mul_le_mul_left _ haLe
    _ = 4 * (P * 2 ^ W) := by ring
    _ < 4 * (2 * 3 ^ r * M) :=
      (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hPclear
    _ = 8 * 3 ^ r * M := by ring

/-- Inclusive natural lower endpoint obtained from the strict predecessor
bound. -/
def syracuseFirstPassageLowerEndpoint (B r W : ℕ) : ℕ :=
  B * 2 ^ W / (2 * 3 ^ r) + 1

/-- Inclusive natural upper endpoint obtained from the weak terminal bound. -/
def syracuseFirstPassageUpperEndpoint (B r S : ℕ) : ℕ :=
  B * 2 ^ S / 3 ^ (r + 1)

/-- Inclusive natural lower endpoint obtained from the terminal valuation. -/
def syracuseFirstPassageHighLowerEndpoint (r S : ℕ) : ℕ :=
  2 ^ S / (8 * 3 ^ r) + 1

/-- The predecessor first-passage bound places the source above the inclusive
natural lower endpoint. -/
theorem syracuseFirstHitAtMost_lowerEndpoint_le
    {B M r : ℕ} (hM : Odd M)
    (hroom : 2 * 3 ^ r ≤ B)
    (hfirst : syracuseFirstHitAtMost B M (r + 1)) :
    syracuseFirstPassageLowerEndpoint B r
        (taoTupleWeight (syracuseValuationPNatList r M hM)) ≤ M := by
  have hcleared :=
    syracuseFirstHitAtMost_prefix_lower_cleared hM hroom hfirst
  have hden : 0 < 2 * 3 ^ r := by positivity
  have hdiv :
      B * 2 ^ taoTupleWeight (syracuseValuationPNatList r M hM) /
          (2 * 3 ^ r) < M := by
    apply (Nat.div_lt_iff_lt_mul hden).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcleared
  unfold syracuseFirstPassageLowerEndpoint
  omega

/-- The terminal first-passage bound places the source below the inclusive
natural upper endpoint. -/
theorem syracuseFirstHitAtMost_le_upperEndpoint
    {B M r : ℕ} (hM : Odd M)
    (hfirst : syracuseFirstHitAtMost B M (r + 1)) :
    M ≤ syracuseFirstPassageUpperEndpoint B r
      (taoTupleWeight (syracuseValuationPNatList (r + 1) M hM)) := by
  have hcleared :=
    syracuseFirstHitAtMost_terminal_upper_cleared hM hfirst
  have hden : 0 < 3 ^ (r + 1) := by positivity
  unfold syracuseFirstPassageUpperEndpoint
  apply (Nat.le_div_iff_mul_le hden).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcleared

/-- The terminal-valuation bound supplies the additional inclusive lower
endpoint used on the high-weight branch. -/
theorem syracuseFirstHitAtMost_highLowerEndpoint_le
    {B M r : ℕ} (hM : Odd M)
    (hroom : 2 * 3 ^ r ≤ B)
    (hfirst : syracuseFirstHitAtMost B M (r + 1)) :
    syracuseFirstPassageHighLowerEndpoint r
        (taoTupleWeight (syracuseValuationPNatList (r + 1) M hM)) ≤ M := by
  have hcleared :=
    syracuseFirstHitAtMost_terminal_lower_cleared hM hroom hfirst
  have hden : 0 < 8 * 3 ^ r := by positivity
  have hdiv :
      2 ^ taoTupleWeight (syracuseValuationPNatList (r + 1) M hM) /
          (8 * 3 ^ r) < M := by
    apply (Nat.div_lt_iff_lt_mul hden).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcleared
  unfold syracuseFirstPassageHighLowerEndpoint
  omega

/-- On the high-weight branch both strict lower endpoints hold
simultaneously. -/
theorem syracuseFirstHitAtMost_maxLowerEndpoint_le
    {B M r : ℕ} (hM : Odd M)
    (hroom : 2 * 3 ^ r ≤ B)
    (hfirst : syracuseFirstHitAtMost B M (r + 1)) :
    max
        (syracuseFirstPassageLowerEndpoint B r
          (taoTupleWeight (syracuseValuationPNatList r M hM)))
        (syracuseFirstPassageHighLowerEndpoint r
          (taoTupleWeight (syracuseValuationPNatList (r + 1) M hM))) ≤ M := by
  exact max_le
    (syracuseFirstHitAtMost_lowerEndpoint_le hM hroom hfirst)
    (syracuseFirstHitAtMost_highLowerEndpoint_le hM hroom hfirst)

end

end Tao
end Erdos1135
