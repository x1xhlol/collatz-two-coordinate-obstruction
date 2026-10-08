/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Geom2HighWeight
import Erdos1135SecondScale.Tao.Section5.EndpointFiberProgression
import Erdos1135SecondScale.Tao.Section5.EndpointRatio

/-!
# Section 5 Low Endpoint Modulus Room

This leaf proves that the full endpoint CRT modulus fits below the rounded
lower endpoint on the low-weight branch.  The arithmetic core consumes an
explicit terminal-room premise.  A separate producer obtains that premise
from the complement of the strict high-weight event and the scheduled index
bound.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Subtraction-free natural arithmetic behind low endpoint room. -/
theorem syracuseFirstPassageModulus_le_quotient_of_terminal_room
    {B r q W a : ℕ}
    (hroom : 2 ^ (a + 2) * 3 ^ (r + q) ≤ B) :
    2 ^ (W + a + 1) * 3 ^ q ≤
      B * 2 ^ W / (2 * 3 ^ r) := by
  have hden : 0 < 2 * 3 ^ r := by positivity
  have htwoSplit : 2 ^ (W + a + 1) = 2 ^ W * 2 ^ (a + 1) := by
    rw [show W + a + 1 = W + (a + 1) by omega, pow_add]
  have htwoSucc : 2 ^ (a + 1) * 2 = 2 ^ (a + 2) := by
    calc
      2 ^ (a + 1) * 2 = 2 ^ ((a + 1) + 1) := (pow_succ _ _).symm
      _ = 2 ^ (a + 2) := by rfl
  have hthree : 3 ^ q * 3 ^ r = 3 ^ (r + q) := by
    rw [mul_comm, pow_add]
  have hclear :
      (2 ^ (W + a + 1) * 3 ^ q) * (2 * 3 ^ r) ≤
        B * 2 ^ W := by
    calc
      (2 ^ (W + a + 1) * 3 ^ q) * (2 * 3 ^ r) =
          2 ^ W * ((2 ^ (a + 1) * 2) *
            (3 ^ q * 3 ^ r)) := by rw [htwoSplit]; ring
      _ = 2 ^ W * (2 ^ (a + 2) * 3 ^ (r + q)) := by
        rw [htwoSucc, hthree]
      _ ≤ 2 ^ W * B := Nat.mul_le_mul_left _ hroom
      _ = B * 2 ^ W := by ring
  exact (Nat.le_div_iff_mul_le hden).2 hclear

/-- Tuple-facing strict room below the quotient-plus-one lower endpoint. -/
theorem taoSection5EndpointFiberModulus_lt_lower_of_terminal_room
    {B q : ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {bs : List ℕ+}
    (hroom :
      2 ^ (geom2PNatListTerminalValue bs + 2) *
          3 ^ (taoSection5M0 B + q - 1) ≤ B) :
    taoSection5EndpointFiberModulus q bs <
      taoSection5EndpointLower B bs := by
  have hexp :
      (taoSection5M0 B - 1) + q = taoSection5M0 B + q - 1 := by
    have hm := facts.one_le_m0
    omega
  have hroom' :
      2 ^ (geom2PNatListTerminalValue bs + 2) *
          3 ^ ((taoSection5M0 B - 1) + q) ≤ B := by
    simpa only [hexp] using hroom
  unfold taoSection5EndpointFiberModulus taoSection5EndpointLower
  rw [taoTupleWeight_eq_dropLast_add_terminalValue]
  exact (syracuseFirstPassageModulus_le_quotient_of_terminal_room
    hroom').trans_lt (Nat.lt_succ_self _)

theorem taoSection5EndpointFiberModulus_le_lower_of_terminal_room
    {B q : ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {bs : List ℕ+}
    (hroom :
      2 ^ (geom2PNatListTerminalValue bs + 2) *
          3 ^ (taoSection5M0 B + q - 1) ≤ B) :
    taoSection5EndpointFiberModulus q bs ≤
      taoSection5EndpointLower B bs :=
  (taoSection5EndpointFiberModulus_lt_lower_of_terminal_room facts hroom).le

private theorem mul_le_of_mul_self_le
    {x y B : ℕ} (hx : x * x ≤ B) (hy : y * y ≤ B) :
    x * y ≤ B := by
  by_cases hxy : x ≤ y
  · exact (Nat.mul_le_mul_right y hxy).trans hy
  · have hyx : y ≤ x := le_of_not_ge hxy
    exact (Nat.mul_le_mul_left x hyx).trans hx

/-- Two square-sized room estimates combine into the terminal room needed by
the cleared quotient theorem. -/
theorem terminal_room_of_four_pow_weight_le_and_four_mul_index_room
    {B m q S a : ℕ} (hm : 1 ≤ m) (haS : a ≤ S)
    (hweight : 4 ^ S ≤ B)
    (hindex : 2 ^ (4 * (m + q)) ≤ B) :
    2 ^ (a + 2) * 3 ^ (m + q - 1) ≤ B := by
  have hxSq : (2 ^ S) * (2 ^ S) ≤ B := by
    calc
      (2 ^ S) * (2 ^ S) = 4 ^ S := by
        rw [← pow_add, show S + S = 2 * S by omega,
          show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
      _ ≤ B := hweight
  have hySq : (2 ^ (2 * (m + q))) * (2 ^ (2 * (m + q))) ≤ B := by
    calc
      (2 ^ (2 * (m + q))) * (2 ^ (2 * (m + q))) =
          2 ^ (4 * (m + q)) := by
        rw [← pow_add]
        congr 1; omega
      _ ≤ B := hindex
  have hproduct : 2 ^ S * 2 ^ (2 * (m + q)) ≤ B :=
    mul_le_of_mul_self_le hxSq hySq
  calc
    2 ^ (a + 2) * 3 ^ (m + q - 1) ≤
        2 ^ (a + 2) * 4 ^ (m + q - 1) := by
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by norm_num : (3 : ℕ) ≤ 4) _)
    _ = 2 ^ ((a + 2) + 2 * (m + q - 1)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    _ ≤ 2 ^ (S + 2 * (m + q)) := by
      exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
    _ = 2 ^ S * 2 ^ (2 * (m + q)) := by rw [pow_add]
    _ ≤ B := hproduct

/-- The floor defining `n0` supplies more than the four-bits-per-index room
used by the low endpoint argument. -/
theorem two_pow_four_mul_le_of_le_taoSection5N0
    {B n : ℕ} (hB : 1 ≤ B) (hn : n ≤ taoSection5N0 B) :
    2 ^ (4 * n) ≤ B := by
  apply Nat.pow_le_of_le_log (Nat.ne_of_gt hB)
  unfold taoSection5N0 at hn
  omega

/-- Scheduled strict low-branch modulus room.  The index premise is the later
consumer's `m0+q` range guard; no endpoint carrier or residue value is needed.
-/
theorem taoSection5EndpointFiberModulus_lt_lower_of_not_highWeight
    {B q : ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {bs : List ℕ+}
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B)
    (hlow : bs ∉ taoGeom2HighWeightEvent B) :
    taoSection5EndpointFiberModulus q bs <
      taoSection5EndpointLower B bs := by
  have hpreterminal : 2 * 3 ^ (taoSection5M0 B - 1) ≤ B := by
    exact_mod_cast facts.preterminal_offset_room
  have hpowPos : 0 < 3 ^ (taoSection5M0 B - 1) := by positivity
  have hB : 1 ≤ B := by omega
  have hweight := four_pow_taoTupleWeight_le_of_not_mem_highWeightEvent hlow
  have hscale := two_pow_four_mul_le_of_le_taoSection5N0 hB hindex
  have hterminalLe :
      geom2PNatListTerminalValue bs ≤ taoTupleWeight bs := by
    have hsplit := taoTupleWeight_eq_dropLast_add_terminalValue bs
    omega
  have hroom := terminal_room_of_four_pow_weight_le_and_four_mul_index_room
    facts.one_le_m0 hterminalLe hweight hscale
  exact taoSection5EndpointFiberModulus_lt_lower_of_terminal_room facts hroom

theorem taoSection5EndpointFiberModulus_le_lower_of_not_highWeight
    {B q : ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {bs : List ℕ+}
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B)
    (hlow : bs ∉ taoGeom2HighWeightEvent B) :
    taoSection5EndpointFiberModulus q bs ≤
      taoSection5EndpointLower B bs :=
  (taoSection5EndpointFiberModulus_lt_lower_of_not_highWeight
    facts hindex hlow).le

end

end Tao
end Erdos1135SecondScale
