import Erdos1135.ND.Band.A5ReferenceExteriorTupleTail

/-!
# A5 retained-carrier terminal cap

This leaf bounds the terminal Geom(2) coordinate while an actual original
endpoint witness is still available.  Only after this bound is obtained may a
later consumer enlarge the exterior carrier to an ambient exact-length event.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Logarithmic budget for the terminal valuation coordinate of an endpoint
in the canonical lost window. -/
noncomputable def ndA5EndpointTerminalLogBudget (B : ℕ) : ℝ :=
  Real.log B + Tao.taoSection5CanonicalLostSlack B +
    2 * (Tao.taoSection5M0 B : ℝ) * Real.log 2 +
      Real.log (8 / 3 : ℝ)

/-- Scalar cap that converts the endpoint terminal budget into a multiple of
the ambient logarithm.  Its eventual truth is a later scalar-rate fact. -/
def NDA5EndpointTerminalCapBudget (B : ℕ) : Prop :=
  ndA5EndpointTerminalLogBudget B ≤
    2 * Real.log 2 * Real.log B

/-- Every tuple in a predicate-filtered carrier retains enough endpoint data
to bound its terminal coordinate before any ambient enlargement. -/
theorem terminalValue_mul_logTwo_lt_ndA5EndpointTerminalLogBudget
    {B q : ℕ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {P : ℕ → Prop} [DecidablePred P] {bs : List ℕ+}
    (facts : Tao.TaoSection5PassLostWindowFacts B)
    (hbs : bs ∈ ndA5EndpointValuationFilterCarrier B E q X P) :
    (Tao.geom2PNatListTerminalValue bs : ℝ) * Real.log 2 <
      ndA5EndpointTerminalLogBudget B := by
  rcases exists_endpoint_of_mem_ndA5EndpointValuationFilterCarrier hbs with
    ⟨M, hM, _hP⟩
  let m := Tao.taoSection5M0 B
  have hmOne : 1 ≤ m := by
    simpa only [m] using facts.one_le_m0
  have hm : m - 1 + 1 = m := Nat.sub_add_cancel hmOne
  have hodd := Tao.taoSection5Endpoint_odd M
  have hfirst : Tao.syracuseFirstHitAtMost B M.1 m := by
    simpa only [m] using
      (Tao.mem_taoSection5EPrime_iff.mp M.2).2.2.2.1
  have hfirst' :
      Tao.syracuseFirstHitAtMost B M.1 (m - 1 + 1) := by
    simpa only [hm] using hfirst
  have hroom : 2 * 3 ^ (m - 1) ≤ B := by
    exact_mod_cast facts.preterminal_offset_room
  have hMposNat : 0 < M.1 := Odd.pos hodd
  have hMpos : (0 : ℝ) < M.1 := by exact_mod_cast hMposNat
  have hBposNat : 0 < B :=
    (by positivity : 0 < 2 * 3 ^ (m - 1)).trans_le hroom
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hBposNat
  have hval := (Tao.mem_taoSection5EndpointValuationFiber_iff.mp hM).1
  have hfullNat :
      2 ^ Tao.taoTupleWeight bs < 8 * 3 ^ (m - 1) * M.1 := by
    have hfull := Tao.syracuseFirstHitAtMost_terminal_lower_cleared
      (r := m - 1) hodd hroom hfirst'
    have hfullVal :
        2 ^ Tao.taoTupleWeight (Tao.taoSection5EndpointValuation M) <
          8 * 3 ^ (m - 1) * M.1 := by
      simpa only [hm, Tao.taoSection5EndpointValuation] using hfull
    simpa only [hval] using hfullVal
  have hfull :
      (2 : ℝ) ^ Tao.taoTupleWeight bs <
        8 * (3 : ℝ) ^ (m - 1) * (M.1 : ℝ) := by
    exact_mod_cast hfullNat
  have hlogFull := Real.log_lt_log
    (pow_pos (by norm_num : (0 : ℝ) < 2) _) hfull
  rw [Real.log_pow,
    Real.log_mul
      (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0)
        (pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0))) hMpos.ne',
    Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
      (pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)),
    Real.log_pow] at hlogFull
  have hMupperNat :
      M.1 ≤ Nat.floor (Tao.taoSection5CanonicalLostUpper B) :=
    (Tao.mem_taoSection5EPrime_iff.mp M.2).2.1
  have hlostUpperNonneg :
      0 ≤ Tao.taoSection5CanonicalLostUpper B := by
    unfold Tao.taoSection5CanonicalLostUpper
      Tao.taoSection5CanonicalLostScale
    positivity
  have hMupper :
      (M.1 : ℝ) ≤ Tao.taoSection5CanonicalLostUpper B :=
    (Nat.le_floor_iff hlostUpperNonneg).mp hMupperNat
  have hlogM := Real.log_le_log hMpos hMupper
  unfold Tao.taoSection5CanonicalLostUpper
    Tao.taoSection5CanonicalLostScale at hlogM
  rw [Real.log_mul (Real.exp_ne_zero _)
      (mul_ne_zero (pow_ne_zero _ (by norm_num : (4 / 3 : ℝ) ≠ 0))
        hBpos.ne'),
    Real.log_exp,
    Real.log_mul (pow_ne_zero _ (by norm_num : (4 / 3 : ℝ) ≠ 0))
      hBpos.ne',
    Real.log_pow] at hlogM
  have hmCast : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by
    exact_mod_cast hm
  have hmCast' :
      (((Tao.taoSection5M0 B - 1 : ℕ) : ℝ) + 1) =
        (Tao.taoSection5M0 B : ℝ) := by
    simpa only [m] using hmCast
  have hlogFourThirds :
      Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  have hlogEight : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlogEightThirds :
      Real.log (8 / 3 : ℝ) = 3 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num : (8 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0), hlogEight]
  rw [hlogEight] at hlogFull
  rw [hlogFourThirds, ← hmCast'] at hlogM
  have hweightLog :
      (Tao.taoTupleWeight bs : ℝ) * Real.log 2 <
        ndA5EndpointTerminalLogBudget B := by
    unfold ndA5EndpointTerminalLogBudget
    rw [hlogEightThirds, ← hmCast']
    dsimp only [m] at hlogFull
    nlinarith [hlogFull, hlogM]
  have hterminalLe :
      Tao.geom2PNatListTerminalValue bs ≤ Tao.taoTupleWeight bs := by
    have hsplit := Tao.taoTupleWeight_eq_dropLast_add_terminalValue bs
    omega
  have hterminalLeReal :
      (Tao.geom2PNatListTerminalValue bs : ℝ) ≤
        (Tao.taoTupleWeight bs : ℝ) := by
    exact_mod_cast hterminalLe
  exact (mul_le_mul_of_nonneg_right hterminalLeReal
    (Real.log_nonneg (by norm_num))).trans_lt hweightLog

/-- Pure algebraic conversion from a terminal logarithmic cap to the native
base/mass comparison. -/
theorem geom2PNatListNativeBase_le_log_add_one_mul_mass
    {B : ℕ} {bs : List ℕ+} {budget : ℝ}
    (hterminal :
      (Tao.geom2PNatListTerminalValue bs : ℝ) * Real.log 2 < budget)
    (hcap : budget ≤ 2 * Real.log 2 * Real.log B) :
    Tao.geom2PNatListNativeBase bs ≤
      (Real.log B + 1) * Tao.geom2PNatListMass bs := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hterminalLt :
      (Tao.geom2PNatListTerminalValue bs : ℝ) < 2 * Real.log B := by
    have hmul :
        (Tao.geom2PNatListTerminalValue bs : ℝ) * Real.log 2 <
          (2 * Real.log B) * Real.log 2 := by
      calc
        (Tao.geom2PNatListTerminalValue bs : ℝ) * Real.log 2 < budget :=
          hterminal
        _ ≤ 2 * Real.log 2 * Real.log B := hcap
        _ = (2 * Real.log B) * Real.log 2 := by ring
    exact lt_of_mul_lt_mul_right hmul hlogTwo.le
  have hmass : 0 ≤ Tao.geom2PNatListMass bs := by
    rw [Tao.geom2PNatListMass_eq_pow]
    positivity
  rw [Tao.geom2PNatListNativeBase_eq_half_mass]
  calc
    (1 / 2 : ℝ) *
        (Tao.geom2PNatListMass bs *
            (Tao.geom2PNatListTerminalValue bs : ℝ) +
          2 * Tao.geom2PNatListMass bs) =
        ((Tao.geom2PNatListTerminalValue bs : ℝ) / 2 + 1) *
          Tao.geom2PNatListMass bs := by ring
    _ ≤ (Real.log B + 1) * Tao.geom2PNatListMass bs := by
      apply mul_le_mul_of_nonneg_right _ hmass
      linarith

/-- Predicate-carrier native-base cap, applied before ambient enlargement. -/
theorem geom2PNatListNativeBase_le_log_add_one_mul_mass_of_mem_filterCarrier
    {B q : ℕ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {P : ℕ → Prop} [DecidablePred P] {bs : List ℕ+}
    (facts : Tao.TaoSection5PassLostWindowFacts B)
    (hcap : NDA5EndpointTerminalCapBudget B)
    (hbs : bs ∈ ndA5EndpointValuationFilterCarrier B E q X P) :
    Tao.geom2PNatListNativeBase bs ≤
      (Real.log B + 1) * Tao.geom2PNatListMass bs := by
  exact geom2PNatListNativeBase_le_log_add_one_mul_mass
    (terminalValue_mul_logTwo_lt_ndA5EndpointTerminalLogBudget facts hbs)
    hcap

/-- Exterior specialization on the retained original-endpoint carrier. -/
theorem ndA5ReferenceExteriorCarrier_nativeBase_le_log_add_one_mul_mass
    {B q : ℕ} {C : ℝ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {bs : List ℕ+}
    (facts : Tao.TaoSection5PassLostWindowFacts B)
    (hcap : NDA5EndpointTerminalCapBudget B)
    (hbs : bs ∈
      ndA5ReferenceExteriorEndpointValuationCarrier B C E q X) :
    Tao.geom2PNatListNativeBase bs ≤
      (Real.log B + 1) * Tao.geom2PNatListMass bs := by
  classical
  exact
    geom2PNatListNativeBase_le_log_add_one_mul_mass_of_mem_filterCarrier
      (P := ndA5ReferenceEndpointExteriorAt B C) facts hcap
      (by
        simpa only [ndA5ReferenceExteriorEndpointValuationCarrier] using hbs)

end
end ND
end Erdos1135
