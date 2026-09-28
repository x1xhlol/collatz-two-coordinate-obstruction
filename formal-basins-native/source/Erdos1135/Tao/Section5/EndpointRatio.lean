import Erdos1135.Tao.Section5.EndpointValuationFiber

/-!
# Section 5 First-Passage Endpoint Ratios

This leaf compares the rounded first-passage endpoints using the genuine
terminal valuation coordinate.  The natural-number comparison is independent
of residue classes and probability laws.  Its real-valued consumers bound the
low and high logarithmic progression terms only when the corresponding fiber
is nonempty.
-/

namespace Erdos1135
namespace Tao

noncomputable section

private theorem syracuseFirstPassageUpperEndpoint_lt_pow_mul_lowerEndpoint
    (B r W a : ℕ) :
    syracuseFirstPassageUpperEndpoint B r (W + a) <
      2 ^ a * syracuseFirstPassageLowerEndpoint B r W := by
  have hlowDen : 0 < 2 * 3 ^ r := by positivity
  have huppDen : 0 < 3 ^ (r + 1) := by positivity
  have hlow :
      B * 2 ^ W <
        (2 * 3 ^ r) * syracuseFirstPassageLowerEndpoint B r W := by
    have h := (Nat.div_lt_iff_lt_mul hlowDen).1
      (Nat.lt_succ_self (B * 2 ^ W / (2 * 3 ^ r)))
    simpa only [syracuseFirstPassageLowerEndpoint, mul_comm] using h
  have hupp :
      3 ^ (r + 1) * syracuseFirstPassageUpperEndpoint B r (W + a) ≤
        (B * 2 ^ W) * 2 ^ a := by
    have hdiv := Nat.div_mul_le_self (B * 2 ^ (W + a)) (3 ^ (r + 1))
    unfold syracuseFirstPassageUpperEndpoint
    calc
      3 ^ (r + 1) * (B * 2 ^ (W + a) / 3 ^ (r + 1)) =
          (B * 2 ^ (W + a) / 3 ^ (r + 1)) * 3 ^ (r + 1) := by ring
      _ ≤ B * 2 ^ (W + a) := hdiv
      _ = (B * 2 ^ W) * 2 ^ a := by rw [pow_add]; ring
  have hden : 2 * 3 ^ r ≤ 3 ^ (r + 1) := by
    rw [pow_succ, mul_comm (3 ^ r) 3]
    exact Nat.mul_le_mul_right (3 ^ r) (by norm_num : 2 ≤ 3)
  have hclear :
      3 ^ (r + 1) * syracuseFirstPassageUpperEndpoint B r (W + a) <
        3 ^ (r + 1) *
          (2 ^ a * syracuseFirstPassageLowerEndpoint B r W) := by
    calc
      3 ^ (r + 1) * syracuseFirstPassageUpperEndpoint B r (W + a) ≤
          (B * 2 ^ W) * 2 ^ a := hupp
      _ < ((2 * 3 ^ r) * syracuseFirstPassageLowerEndpoint B r W) *
          2 ^ a := (Nat.mul_lt_mul_right (by positivity)).2 hlow
      _ ≤ (3 ^ (r + 1) * syracuseFirstPassageLowerEndpoint B r W) *
          2 ^ a := by
        exact Nat.mul_le_mul_right (2 ^ a)
          (Nat.mul_le_mul_right
            (syracuseFirstPassageLowerEndpoint B r W) hden)
      _ = 3 ^ (r + 1) *
          (2 ^ a * syracuseFirstPassageLowerEndpoint B r W) := by ring
  exact (Nat.mul_lt_mul_left huppDen).1 hclear

/-- Every positive-natural list splits into its dropped prefix and terminal
coordinate at the level of tuple weights.  The empty list is covered by the
zero extension of `geom2PNatListTerminalValue`. -/
theorem taoTupleWeight_eq_dropLast_add_terminalValue (bs : List ℕ+) :
    taoTupleWeight bs =
      taoTupleWeight bs.dropLast + geom2PNatListTerminalValue bs := by
  by_cases hbs : bs = []
  · simp [hbs, taoTupleWeight]
  · calc
      taoTupleWeight bs =
          taoTupleWeight (bs.dropLast ++ [bs.getLast hbs]) := by
        rw [List.dropLast_append_getLast hbs]
      _ = taoTupleWeight bs.dropLast +
          taoTupleWeight [bs.getLast hbs] :=
        taoTupleWeight_append_trajectory _ _
      _ = taoTupleWeight bs.dropLast +
          geom2PNatListTerminalValue bs := by
        rw [geom2PNatListTerminalValue_eq_getLast hbs]
        simp [taoTupleWeight]

/-- The full endpoint is strictly below the lower endpoint multiplied by the
power of two in the terminal coordinate whenever the tuple weight splits into
prefix and terminal weights. -/
theorem taoSection5EndpointUpper_lt_pow_terminalValue_mul_lower_of_weight
    {B : ℕ} {bs : List ℕ+}
    (hweight : taoTupleWeight bs =
      taoTupleWeight bs.dropLast + geom2PNatListTerminalValue bs) :
    taoSection5EndpointUpper B bs <
      2 ^ geom2PNatListTerminalValue bs *
        taoSection5EndpointLower B bs := by
  unfold taoSection5EndpointUpper taoSection5EndpointLower
  rw [hweight]
  exact syracuseFirstPassageUpperEndpoint_lt_pow_mul_lowerEndpoint _ _ _ _

/-- Universal strict endpoint ratio.  It is pure tuple-and-quotient arithmetic:
there are no schedule, carrier, residue, or probability hypotheses. -/
theorem taoSection5EndpointUpper_lt_pow_terminalValue_mul_lower
    (B : ℕ) (bs : List ℕ+) :
    taoSection5EndpointUpper B bs <
      2 ^ geom2PNatListTerminalValue bs *
        taoSection5EndpointLower B bs := by
  exact taoSection5EndpointUpper_lt_pow_terminalValue_mul_lower_of_weight
    (taoTupleWeight_eq_dropLast_add_terminalValue bs)

/-- Weak form of the universal endpoint ratio used by later inequalities. -/
theorem taoSection5EndpointUpper_le_pow_terminalValue_mul_lower
    (B : ℕ) (bs : List ℕ+) :
    taoSection5EndpointUpper B bs ≤
      2 ^ geom2PNatListTerminalValue bs *
        taoSection5EndpointLower B bs := by
  exact (taoSection5EndpointUpper_lt_pow_terminalValue_mul_lower B bs).le

private theorem taoSection5EndpointLower_one_le
    (B : ℕ) (bs : List ℕ+) :
    1 ≤ taoSection5EndpointLower B bs := by
  unfold taoSection5EndpointLower syracuseFirstPassageLowerEndpoint
  exact Nat.succ_le_succ (Nat.zero_le _)

private theorem log_two_lt_one_endpointRatio :
    Real.log (2 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 2 by norm_num)
    (show (2 : ℝ) ≠ 1 by norm_num)
  norm_num at h ⊢
  exact h

/-- A rounded endpoint ratio controlled by `2^a` has logarithm at most `a`.
The intermediate lower endpoint `A0` lets the same lemma serve both the low
endpoint and the raised high endpoint. -/
private theorem log_nat_ratio_le_of_le_pow_mul
    {A0 A U a : ℕ} (hA0 : 1 ≤ A0) (hA0A : A0 ≤ A)
    (hAU : A ≤ U) (hU : U ≤ 2 ^ a * A0) :
    Real.log ((U : ℝ) / (A : ℝ)) ≤ (a : ℝ) := by
  have hA : 0 < A := hA0.trans hA0A
  have hUpos : 0 < U := hA.trans_le hAU
  have hUA : U ≤ 2 ^ a * A :=
    hU.trans (Nat.mul_le_mul_left (2 ^ a) hA0A)
  have hAReal : 0 < (A : ℝ) := by exact_mod_cast hA
  have hUReal : 0 < (U : ℝ) := by exact_mod_cast hUpos
  have hratioPos : 0 < (U : ℝ) / (A : ℝ) := div_pos hUReal hAReal
  have hratioLe : (U : ℝ) / (A : ℝ) ≤ (2 : ℝ) ^ a := by
    apply (div_le_iff₀ hAReal).2
    exact_mod_cast hUA
  calc
    Real.log ((U : ℝ) / (A : ℝ)) ≤ Real.log ((2 : ℝ) ^ a) :=
      Real.log_le_log hratioPos hratioLe
    _ = (a : ℝ) * Real.log 2 := by rw [Real.log_pow]
    _ ≤ (a : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left log_two_lt_one_endpointRatio.le
        (Nat.cast_nonneg a)

/-- Generic tuple-facing logarithmic ratio consumer. -/
theorem taoSection5Endpoint_log_ratio_le_terminalValue
    {B A : ℕ} {bs : List ℕ+}
    (hlower : taoSection5EndpointLower B bs ≤ A)
    (hupper : A ≤ taoSection5EndpointUpper B bs) :
    Real.log ((taoSection5EndpointUpper B bs : ℝ) / (A : ℝ)) ≤
      (geom2PNatListTerminalValue bs : ℝ) := by
  exact log_nat_ratio_le_of_le_pow_mul
    (taoSection5EndpointLower_one_le B bs) hlower hupper
    (taoSection5EndpointUpper_le_pow_terminalValue_mul_lower B bs)

/-- Low-progression logarithm controlled by the terminal coordinate of a
nonempty endpoint fiber. -/
theorem taoSection5Endpoint_low_log_ratio_le_terminalValue_of_nonempty
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hne : (taoSection5EndpointValuationFiber B E q X bs).Nonempty) :
    Real.log
        ((taoSection5EndpointUpper B bs : ℝ) /
          (taoSection5EndpointLower B bs : ℝ)) ≤
      (geom2PNatListTerminalValue bs : ℝ) := by
  exact taoSection5Endpoint_log_ratio_le_terminalValue
    le_rfl (taoSection5EndpointFiber_nonempty_lower_le_upper facts hne)

/-- High-progression logarithm obeys the same terminal-coordinate bound after
raising the lower endpoint. -/
theorem taoSection5Endpoint_high_log_ratio_le_terminalValue_of_nonempty
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hne : (taoSection5EndpointValuationFiber B E q X bs).Nonempty) :
    Real.log
        ((taoSection5EndpointUpper B bs : ℝ) /
          (taoSection5EndpointHighLower B bs : ℝ)) ≤
      (geom2PNatListTerminalValue bs : ℝ) := by
  exact taoSection5Endpoint_log_ratio_le_terminalValue
    (le_max_left _ _)
    (taoSection5EndpointFiber_nonempty_highLower_le_upper facts hne)

end

end Tao
end Erdos1135
