import Erdos1135.Tao.Probability.Geom2TerminalMoment
import Erdos1135.Tao.Section5.EndpointLowRoom

/-!
# Section 5 Native Fixed-Fiber Envelope

This leaf keeps the inclusive reciprocal-progression majorant in its native
form.  It proves the rounded high-endpoint constant `3`, then combines the
low and high progression bounds into one pointwise fixed-fiber estimate.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- Raw quotient-plus-one comparison behind the rounded high endpoint. -/
theorem two_pow_lt_three_pow_mul_syracuseFirstPassageHighLowerEndpoint
    (r S : ℕ) :
    2 ^ S <
      3 ^ (r + 2) * syracuseFirstPassageHighLowerEndpoint r S := by
  have hden : 0 < 8 * 3 ^ r := by positivity
  have hquot :
      2 ^ S <
        (8 * 3 ^ r) * syracuseFirstPassageHighLowerEndpoint r S := by
    have h := (Nat.div_lt_iff_lt_mul hden).1
      (Nat.lt_succ_self (2 ^ S / (8 * 3 ^ r)))
    simpa only [syracuseFirstPassageHighLowerEndpoint, mul_comm] using h
  have hdenLt : 8 * 3 ^ r < 3 ^ (r + 2) := by
    rw [pow_add]
    have hp : 0 < 3 ^ r := by positivity
    norm_num
    nlinarith
  have hhighPos :
      0 < syracuseFirstPassageHighLowerEndpoint r S := by
    unfold syracuseFirstPassageHighLowerEndpoint
    exact Nat.zero_lt_succ _
  exact hquot.trans
    ((Nat.mul_lt_mul_right hhighPos).2 hdenLt)

/-- The rounded high lower endpoint absorbs its outer reciprocal with the
smallest uniform integer constant, `3`. -/
theorem taoSection5_three_pow_div_endpointHighLower_lt
    {B q : ℕ} (hm : 1 ≤ taoSection5M0 B) (bs : List ℕ+) :
    (3 : ℝ) ^ q / (taoSection5EndpointHighLower B bs : ℝ) <
      3 * (3 : ℝ) ^ (taoSection5M0 B + q) /
        (2 : ℝ) ^ taoTupleWeight bs := by
  have hexp :
      (taoSection5M0 B - 1) + 2 = taoSection5M0 B + 1 := by
    omega
  have hraw :=
    two_pow_lt_three_pow_mul_syracuseFirstPassageHighLowerEndpoint
      (taoSection5M0 B - 1) (taoTupleWeight bs)
  rw [hexp] at hraw
  have hhighArm :
      syracuseFirstPassageHighLowerEndpoint (taoSection5M0 B - 1)
          (taoTupleWeight bs) ≤
        taoSection5EndpointHighLower B bs := by
    exact le_max_right _ _
  have hnat :
      2 ^ taoTupleWeight bs <
        3 ^ (taoSection5M0 B + 1) *
          taoSection5EndpointHighLower B bs :=
    hraw.trans_le
      (Nat.mul_le_mul_left _ hhighArm)
  have hpow :
      3 ^ q * 3 ^ (taoSection5M0 B + 1) =
        3 * 3 ^ (taoSection5M0 B + q) := by
    calc
      3 ^ q * 3 ^ (taoSection5M0 B + 1) =
          3 ^ (q + (taoSection5M0 B + 1)) := (pow_add _ _ _).symm
      _ = 3 ^ (taoSection5M0 B + q + 1) := by
        congr 1
        omega
      _ = 3 ^ (taoSection5M0 B + q) * 3 := pow_succ _ _
      _ = 3 * 3 ^ (taoSection5M0 B + q) := by ring
  have hscaledNat :
      3 ^ q * 2 ^ taoTupleWeight bs <
        (3 * 3 ^ (taoSection5M0 B + q)) *
          taoSection5EndpointHighLower B bs := by
    calc
      3 ^ q * 2 ^ taoTupleWeight bs <
          3 ^ q *
            (3 ^ (taoSection5M0 B + 1) *
              taoSection5EndpointHighLower B bs) :=
        (Nat.mul_lt_mul_left (by positivity)).2 hnat
      _ = (3 * 3 ^ (taoSection5M0 B + q)) *
          taoSection5EndpointHighLower B bs := by rw [← hpow]; ring
  have hscaledReal :
      (3 : ℝ) ^ q * (2 : ℝ) ^ taoTupleWeight bs <
        (3 * (3 : ℝ) ^ (taoSection5M0 B + q)) *
          (taoSection5EndpointHighLower B bs : ℝ) := by
    exact_mod_cast hscaledNat
  have hhighPos : 0 < (taoSection5EndpointHighLower B bs : ℝ) := by
    have hnatPos : 0 < taoSection5EndpointHighLower B bs := by
      unfold taoSection5EndpointHighLower
      have hpos :
          0 < syracuseFirstPassageHighLowerEndpoint
            (taoSection5M0 B - 1) (taoTupleWeight bs) := by
        unfold syracuseFirstPassageHighLowerEndpoint
        exact Nat.zero_lt_succ _
      exact hpos.trans_le (le_max_right _ _)
    exact_mod_cast hnatPos
  exact (div_lt_div_iff₀ hhighPos (by positivity)).2 hscaledReal

private theorem taoSection5EndpointLower_one_le_real
    (B : ℕ) (bs : List ℕ+) :
    (1 : ℝ) ≤ taoSection5EndpointLower B bs := by
  have hnat : 1 ≤ taoSection5EndpointLower B bs := by
    unfold taoSection5EndpointLower syracuseFirstPassageLowerEndpoint
    exact Nat.succ_le_succ (Nat.zero_le _)
  exact_mod_cast hnat

private theorem taoSection5EndpointHighLower_one_le_real
    (B : ℕ) (bs : List ℕ+) :
    (1 : ℝ) ≤ taoSection5EndpointHighLower B bs := by
  exact (taoSection5EndpointLower_one_le_real B bs).trans
    (by exact_mod_cast (le_max_left
      (taoSection5EndpointLower B bs)
      (syracuseFirstPassageHighLowerEndpoint (taoSection5M0 B - 1)
        (taoTupleWeight bs))))

/-- Native-base estimate for a nonempty low endpoint fiber. -/
theorem taoSection5_lowEndpointFiber_scaled_reciprocal_le_nativeBase
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B)
    (hlow : bs ∉ taoGeom2HighWeightEvent B)
    (hne : (taoSection5EndpointValuationFiber B E q X bs).Nonempty) :
    (3 : ℝ) ^ q *
        (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
          1 / (M.1 : ℝ)) ≤
      geom2PNatListNativeBase bs := by
  have hprog :=
    sum_taoSection5EndpointFiber_reciprocal_le_low_of_nonempty facts hne
  have hlog :=
    taoSection5Endpoint_low_log_ratio_le_terminalValue_of_nonempty facts hne
  have hroom :=
    taoSection5EndpointFiberModulus_le_lower_of_not_highWeight
      facts hindex hlow
  have hQpos :
      0 < (taoSection5EndpointFiberModulus q bs : ℝ) := by
    unfold taoSection5EndpointFiberModulus
    positivity
  have hQA :
      (taoSection5EndpointFiberModulus q bs : ℝ) ≤
        taoSection5EndpointLower B bs := by
    exact_mod_cast hroom
  have hInvAQ :
      1 / (taoSection5EndpointLower B bs : ℝ) ≤
        1 / (taoSection5EndpointFiberModulus q bs : ℝ) :=
    one_div_le_one_div_of_le hQpos hQA
  have hInvAOne :
      1 / (taoSection5EndpointLower B bs : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (taoSection5EndpointLower_one_le_real B bs)
  calc
    (3 : ℝ) ^ q *
        (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
          1 / (M.1 : ℝ)) ≤
        (3 : ℝ) ^ q *
          (1 / (taoSection5EndpointLower B bs : ℝ) +
            (1 / (taoSection5EndpointFiberModulus q bs : ℝ)) *
              (1 / (taoSection5EndpointLower B bs : ℝ) +
                Real.log
                  ((taoSection5EndpointUpper B bs : ℝ) /
                    (taoSection5EndpointLower B bs : ℝ)))) :=
      mul_le_mul_of_nonneg_left hprog (by positivity)
    _ ≤ (3 : ℝ) ^ q *
        (1 / (taoSection5EndpointFiberModulus q bs : ℝ) +
          (1 / (taoSection5EndpointFiberModulus q bs : ℝ)) *
            (1 + (geom2PNatListTerminalValue bs : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add hInvAQ
        (mul_le_mul_of_nonneg_left
          (add_le_add hInvAOne hlog) (by positivity))
    _ = geom2PNatListNativeBase bs := by
      unfold taoSection5EndpointFiberModulus geom2PNatListNativeBase
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp [pow_ne_zero]
      ring

/-- Native-base plus high-outer-term estimate for a nonempty high fiber. -/
theorem taoSection5_highEndpointFiber_scaled_reciprocal_le_nativeBase_add
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hne : (taoSection5EndpointValuationFiber B E q X bs).Nonempty) :
    (3 : ℝ) ^ q *
        (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
          1 / (M.1 : ℝ)) ≤
      geom2PNatListNativeBase bs +
        3 * (3 : ℝ) ^ (taoSection5M0 B + q) /
          (2 : ℝ) ^ taoTupleWeight bs := by
  have hprog :=
    sum_taoSection5EndpointFiber_reciprocal_le_high_of_nonempty facts hne
  have hlog :=
    taoSection5Endpoint_high_log_ratio_le_terminalValue_of_nonempty facts hne
  have houter :=
    taoSection5_three_pow_div_endpointHighLower_lt
      facts.one_le_m0 (q := q) bs
  have hQpos :
      0 < (taoSection5EndpointFiberModulus q bs : ℝ) := by
    unfold taoSection5EndpointFiberModulus
    positivity
  have hInvHOne :
      1 / (taoSection5EndpointHighLower B bs : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (taoSection5EndpointHighLower_one_le_real B bs)
  have hbase :
      ((geom2PNatListTerminalValue bs : ℝ) + 1) /
          (2 : ℝ) ^ (taoTupleWeight bs + 1) ≤
        geom2PNatListNativeBase bs := by
    unfold geom2PNatListNativeBase
    gcongr
    norm_num
  calc
    (3 : ℝ) ^ q *
        (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
          1 / (M.1 : ℝ)) ≤
        (3 : ℝ) ^ q *
          (1 / (taoSection5EndpointHighLower B bs : ℝ) +
            (1 / (taoSection5EndpointFiberModulus q bs : ℝ)) *
              (1 / (taoSection5EndpointHighLower B bs : ℝ) +
                Real.log
                  ((taoSection5EndpointUpper B bs : ℝ) /
                    (taoSection5EndpointHighLower B bs : ℝ)))) :=
      mul_le_mul_of_nonneg_left hprog (by positivity)
    _ ≤ (3 : ℝ) ^ q *
        (1 / (taoSection5EndpointHighLower B bs : ℝ) +
          (1 / (taoSection5EndpointFiberModulus q bs : ℝ)) *
            (1 + (geom2PNatListTerminalValue bs : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (add_le_add hInvHOne hlog) (one_div_pos.mpr hQpos).le)
    _ = (3 : ℝ) ^ q /
          (taoSection5EndpointHighLower B bs : ℝ) +
        ((geom2PNatListTerminalValue bs : ℝ) + 1) /
          (2 : ℝ) ^ (taoTupleWeight bs + 1) := by
      unfold taoSection5EndpointFiberModulus
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp [pow_ne_zero]
      ring
    _ ≤ geom2PNatListNativeBase bs +
        3 * (3 : ℝ) ^ (taoSection5M0 B + q) /
          (2 : ℝ) ^ taoTupleWeight bs := by
      linarith [houter.le, hbase]

/-- High-event part of the native pointwise envelope. -/
noncomputable def taoSection5EndpointFiberHighEnvelope
    (B q : ℕ) (bs : List ℕ+) : ℝ := by
  classical
  exact if bs ∈ taoGeom2HighWeightEvent B then
    3 * (3 : ℝ) ^ (taoSection5M0 B + q) /
      (2 : ℝ) ^ taoTupleWeight bs
  else 0

/-- Total pointwise native envelope, including empty fibers and the strict
high/low split. -/
theorem taoSection5_endpointFiber_scaled_reciprocal_le_nativeEnvelope
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hindex : taoSection5M0 B + q ≤ taoSection5N0 B) :
    (3 : ℝ) ^ q *
        (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
          1 / (M.1 : ℝ)) ≤
      geom2PNatListNativeBase bs +
        taoSection5EndpointFiberHighEnvelope B q bs := by
  classical
  by_cases hne :
      (taoSection5EndpointValuationFiber B E q X bs).Nonempty
  · by_cases hhigh : bs ∈ taoGeom2HighWeightEvent B
    · simp only [taoSection5EndpointFiberHighEnvelope, if_pos hhigh]
      exact taoSection5_highEndpointFiber_scaled_reciprocal_le_nativeBase_add
        facts hne
    · simp only [taoSection5EndpointFiberHighEnvelope, if_neg hhigh, add_zero]
      exact taoSection5_lowEndpointFiber_scaled_reciprocal_le_nativeBase
        facts hindex hhigh hne
  · rw [sum_taoSection5EndpointFiber_reciprocal_eq_zero_of_not_nonempty hne]
    have hnative : 0 ≤ geom2PNatListNativeBase bs := by
      unfold geom2PNatListNativeBase
      positivity
    have hhighEnvelope :
        0 ≤ taoSection5EndpointFiberHighEnvelope B q bs := by
      unfold taoSection5EndpointFiberHighEnvelope
      by_cases hhigh : bs ∈ taoGeom2HighWeightEvent B
      · simp only [if_pos hhigh]
        positivity
      · simp only [if_neg hhigh]
        exact le_rfl
    simpa using add_nonneg hnative hhighEnvelope

end

end Tao
end Erdos1135
