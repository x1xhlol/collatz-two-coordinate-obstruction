import Erdos1135.ND.Band.A5ReferenceFilteredCoefficient

/-!
# A5 exterior endpoint tuple tails

This leaf converts one retained strict exterior original endpoint into the
full-tuple upper tail or predecessor-prefix lower tail needed by exterior H.
The negative branch deliberately remains on `dropLast`; no assertion is made
that every endpoint in the enlarged Tao fiber is exterior.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Exact first-passage logarithmic corridor for an actual endpoint valuation
tuple.  The lower edge uses the predecessor prefix and retains the exact
`log (8/3)` buffer. -/
theorem ndA5ReferenceEndpoint_firstPassageCenteredCorridor
    {B q : ℕ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {bs : List ℕ+} {M : Tao.TaoSection5Endpoint B E}
    (facts : Tao.TaoSection5PassLostWindowFacts B)
    (hM : M ∈ Tao.taoSection5EndpointValuationFiber B E q X bs) :
    Tao.taoGeom2CenteredListWeight bs.dropLast * Real.log 2 -
          Real.log (8 / 3 : ℝ) <
        ndA5InteriorShift B (M.1 : ℝ) ∧
      ndA5InteriorShift B (M.1 : ℝ) ≤
        Tao.taoGeom2CenteredListWeight bs * Real.log 2 := by
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
  have hval := (Tao.mem_taoSection5EndpointValuationFiber_iff.mp hM).1
  have hlength : bs.length = m := by
    rw [← hval]
    simpa only [m] using Tao.taoSection5EndpointValuation_length M
  have hdropLength : bs.dropLast.length = m - 1 := by
    rw [List.length_dropLast, hlength]
  have hroom : 2 * 3 ^ (m - 1) ≤ B := by
    exact_mod_cast facts.preterminal_offset_room
  have hMposNat : 0 < M.1 := Odd.pos hodd
  have hMpos : (0 : ℝ) < M.1 := by exact_mod_cast hMposNat
  have hBposNat : 0 < B :=
    (by positivity : 0 < 2 * 3 ^ (m - 1)).trans_le hroom
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hBposNat
  have hupperNat :
      3 ^ m * M.1 ≤ B * 2 ^ Tao.taoTupleWeight bs := by
    have hupper := Tao.syracuseFirstHitAtMost_terminal_upper_cleared
      (r := m - 1) hodd hfirst'
    have hupperVal :
        3 ^ m * M.1 ≤
          B * 2 ^ Tao.taoTupleWeight
            (Tao.taoSection5EndpointValuation M) := by
      simpa only [hm, Tao.taoSection5EndpointValuation] using hupper
    simpa only [hval] using hupperVal
  have hlowerNat :
      B * 2 ^ Tao.taoTupleWeight bs.dropLast <
        2 * 3 ^ (m - 1) * M.1 := by
    have hlower := Tao.syracuseFirstHitAtMost_prefix_lower_cleared
      (r := m - 1) hodd hroom hfirst'
    rw [← Tao.taoSection5EndpointFiber_dropLast facts hM] at hlower
    exact hlower
  have hupper :
      (3 : ℝ) ^ m * (M.1 : ℝ) ≤
        (B : ℝ) * (2 : ℝ) ^ Tao.taoTupleWeight bs := by
    exact_mod_cast hupperNat
  have hlower :
      (B : ℝ) * (2 : ℝ) ^ Tao.taoTupleWeight bs.dropLast <
        2 * (3 : ℝ) ^ (m - 1) * (M.1 : ℝ) := by
    exact_mod_cast hlowerNat
  have hlogUpper := Real.log_le_log
    (mul_pos (pow_pos (by norm_num) m) hMpos) hupper
  rw [Real.log_mul (pow_ne_zero _ (by norm_num)) hMpos.ne',
    Real.log_mul hBpos.ne' (pow_ne_zero _ (by norm_num)),
    Real.log_pow, Real.log_pow] at hlogUpper
  have hlogLower := Real.log_lt_log
    (mul_pos hBpos (pow_pos (by norm_num) _)) hlower
  rw [Real.log_mul hBpos.ne' (pow_ne_zero _ (by norm_num)),
    Real.log_pow,
    Real.log_mul
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hMpos.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (pow_ne_zero _ (by norm_num)),
    Real.log_pow] at hlogLower
  have hmCast : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by
    exact_mod_cast hm
  have hmCast' :
      (((Tao.taoSection5M0 B - 1 : ℕ) : ℝ) + 1) =
        (Tao.taoSection5M0 B : ℝ) := by
    simpa only [m] using hmCast
  have hlogFourThirds :
      ndA5LogFourThirds = 2 * Real.log 2 - Real.log 3 := by
    unfold ndA5LogFourThirds
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  have hlogEightThirds :
      Real.log (8 / 3 : ℝ) = Real.log 2 + ndA5LogFourThirds := by
    unfold ndA5LogFourThirds
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (4 / 3 : ℝ) ≠ 0)]
    norm_num
  constructor
  · unfold Tao.taoGeom2CenteredListWeight ndA5InteriorShift
    rw [hdropLength, hlogEightThirds, hlogFourThirds]
    dsimp only [m] at hlogLower ⊢
    rw [← hmCast']
    nlinarith [hlogLower]
  · unfold Tao.taoGeom2CenteredListWeight ndA5InteriorShift
    rw [hlength, hlogFourThirds]
    dsimp only [m] at hlogUpper ⊢
    nlinarith [hlogUpper]

/-- A strict exterior endpoint yields either a positive full-tuple deviation
or a negative predecessor-prefix deviation.  The normalized negative buffer
is weakened from `log(8/3)/log 2` to the source-locked constant `3`. -/
theorem ndA5ReferenceEndpoint_exterior_centeredTail
    {B q : ℕ} {C : ℝ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {bs : List ℕ+} {M : Tao.TaoSection5Endpoint B E}
    (facts : Tao.TaoSection5PassLostWindowFacts B)
    (hM : M ∈ Tao.taoSection5EndpointValuationFiber B E q X bs)
    (hExt : ndA5ReferenceEndpointExteriorAt B C M.1) :
    ((4 / 25 : ℝ) * ndA5TubeWidth B C) / Real.log 2 <
        Tao.taoGeom2CenteredListWeight bs ∨
      Tao.taoGeom2CenteredListWeight bs.dropLast <
        -((((4 / 25 : ℝ) * ndA5TubeWidth B C) / Real.log 2) - 3) := by
  let R : ℝ := (4 / 25 : ℝ) * ndA5TubeWidth B C
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcorridor := ndA5ReferenceEndpoint_firstPassageCenteredCorridor
    facts hM
  have hExt' : R < |ndA5InteriorShift B (M.1 : ℝ)| := by
    simpa only [R, ndA5ReferenceEndpointExteriorAt] using hExt
  rcases (lt_abs.mp hExt') with hpos | hneg
  · left
    have hmul : R <
        Tao.taoGeom2CenteredListWeight bs * Real.log 2 :=
      hpos.trans_le hcorridor.2
    simpa only [R] using (div_lt_iff₀ hlogTwo).2 hmul
  · right
    have hlogEightThirdsLt :
        Real.log (8 / 3 : ℝ) < 3 * Real.log 2 := by
      calc
        Real.log (8 / 3 : ℝ) < Real.log (8 : ℝ) :=
          Real.log_lt_log (by norm_num) (by norm_num)
        _ = 3 * Real.log 2 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
          norm_num
    have hmul :
        Tao.taoGeom2CenteredListWeight bs.dropLast * Real.log 2 <
          -R + 3 * Real.log 2 := by
      nlinarith [hcorridor.1, hneg, hlogEightThirdsLt]
    calc
      Tao.taoGeom2CenteredListWeight bs.dropLast <
          (-R + 3 * Real.log 2) / Real.log 2 :=
        (lt_div_iff₀ hlogTwo).2 hmul
      _ = -(R / Real.log 2 - 3) := by
        field_simp [hlogTwo.ne']
        ring
      _ = -((((4 / 25 : ℝ) * ndA5TubeWidth B C) / Real.log 2) - 3) := by
        rfl

/-- Carrier-level exterior tail disjunction.  One retained original endpoint
witness is sufficient because both centered weights depend only on `bs`. -/
theorem ndA5ReferenceExteriorCarrier_centeredTail
    {B q : ℕ} {C : ℝ} {E : Set ℕ} {X : ZMod (3 ^ q)}
    {bs : List ℕ+}
    (facts : Tao.TaoSection5PassLostWindowFacts B)
    (hbs : bs ∈
      ndA5ReferenceExteriorEndpointValuationCarrier B C E q X) :
    ((4 / 25 : ℝ) * ndA5TubeWidth B C) / Real.log 2 <
        Tao.taoGeom2CenteredListWeight bs ∨
      Tao.taoGeom2CenteredListWeight bs.dropLast <
        -((((4 / 25 : ℝ) * ndA5TubeWidth B C) / Real.log 2) - 3) := by
  rcases exists_exterior_endpoint_of_mem_referenceExteriorCarrier hbs with
    ⟨M, hM, hExt⟩
  exact ndA5ReferenceEndpoint_exterior_centeredTail facts hM hExt

end
end ND
end Erdos1135
