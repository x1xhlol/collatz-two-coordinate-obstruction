import Erdos1135.Tao.Section6.HeadGate

/-!
# Section 6 Head-Gate Index Localization

This deterministic leaf derives Tao's eventual stopping-index bound
`20k <= 17n` from a nonempty fixed-head gate.  The threshold depends on the
fixed constant `CA`; no uniformity in unbounded `CA` is claimed.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Section 6-native rational upper bound for `log 3 / log 2`. -/
theorem taoSection6_log_three_div_log_two_lt_eight_fifths :
    Real.log 3 / Real.log 2 < (8 / 5 : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (3 : ℝ) ^ 5 < (2 : ℝ) ^ 8 := by norm_num
  have hlogpow : Real.log ((3 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 8) :=
    Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hlog : Real.log (3 : ℝ) < (8 / 5 : ℝ) * Real.log (2 : ℝ) := by
    calc
      Real.log (3 : ℝ) = (5 * Real.log (3 : ℝ)) / 5 := by ring
      _ < (8 * Real.log (2 : ℝ)) / 5 :=
        div_lt_div_of_pos_right hlogpow (by norm_num)
      _ = (8 / 5 : ℝ) * Real.log (2 : ℝ) := by ring
  exact (div_lt_iff₀ hlog2).2 hlog

/-- Any fixed positive multiple of `log n` is eventually below a prescribed
positive linear multiple of `n`. -/
theorem exists_taoSection6_const_mul_log_le
    (D epsilon : ℝ) (hD : 0 < D) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      D * Real.log (n : ℝ) ≤ epsilon * (n : ℝ) := by
  have hlo :
      (fun n : ℕ => Real.log (n : ℝ)) =o[Filter.atTop]
        (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto
      tendsto_natCast_atTop_atTop
  have heventually :=
    (Asymptotics.isLittleO_iff.mp hlo) (div_pos hepsilon hD)
  rcases Filter.eventually_atTop.1 heventually with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hbound := hN n hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hD0 : 0 ≤ D := le_of_lt hD
  calc
    D * Real.log (n : ℝ) ≤ D * |Real.log (n : ℝ)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hD0
    _ ≤ D * ((epsilon / D) * (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hD0
      simpa [Real.norm_eq_abs, abs_of_nonneg hn0] using hbound
    _ = epsilon * (n : ℝ) := by
      field_simp [hD.ne']

/-- Pointwise index localization once the logarithmic remainder has entered
its eventual linear budget.  The `k=0` branch is explicit. -/
theorem taoSection6HeadGate_index_le_of_log_budget
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (hlog : 0 < Real.log (n : ℝ))
    (hbudget :
      ((3 / 2 : ℝ) * CA ^ 2 + CA) * Real.log (n : ℝ) ≤
        (3 / 200 : ℝ) * (n : ℝ))
    (hgate : taoSection6HeadGate CA n k l head) :
    20 * k ≤ 17 * n := by
  by_cases hk0 : k = 0
  · omega
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hlength := taoSection6HeadGate_length hgate
  have htyp := taoSection6HeadGate_typical hgate
  have hcross := (taoSection6HeadGate_crossing hgate).1
  have hprefix :=
    taoCor63StarInclusiveTypical_prefix_lower
      htyp hkpos (by omega : k ≤ head.length)
  rw [taoSection6IntervalWeight_zero_eq_tupleWeight_take] at hprefix
  unfold taoCor63PrefixError at hprefix
  unfold taoCor63StarQ at hcross
  have hmain :
      2 * (k : ℝ) -
          CA * (Real.sqrt ((k : ℝ) * Real.log (n : ℝ)) +
            Real.log (n : ℝ)) ≤
        (n : ℝ) * (Real.log 3 / Real.log 2) -
          CA ^ 2 * Real.log (n : ℝ) :=
    hprefix.trans hcross
  have hx : 0 ≤ (k : ℝ) * Real.log (n : ℝ) := by positivity
  have hepsilon : 0 < (1 : ℝ) / (5 * Real.log (n : ℝ)) := by positivity
  have hyoung :=
    young_sqrt_le_epsilon
      (A := CA) (ε := (1 : ℝ) / (5 * Real.log (n : ℝ)))
      (x := (k : ℝ) * Real.log (n : ℝ)) hepsilon hx
  have hyoung' :
      CA * Real.sqrt ((k : ℝ) * Real.log (n : ℝ)) ≤
        (k : ℝ) / 10 +
          (5 / 2 : ℝ) * CA ^ 2 * Real.log (n : ℝ) := by
    calc
      CA * Real.sqrt ((k : ℝ) * Real.log (n : ℝ)) ≤
          (((1 : ℝ) / (5 * Real.log (n : ℝ))) / 2) *
              ((k : ℝ) * Real.log (n : ℝ)) +
            CA ^ 2 /
              (2 * ((1 : ℝ) / (5 * Real.log (n : ℝ)))) := hyoung
      _ = (k : ℝ) / 10 +
          (5 / 2 : ℝ) * CA ^ 2 * Real.log (n : ℝ) := by
        field_simp [hlog.ne']
        ring
  have hlinear :
      (19 / 10 : ℝ) * (k : ℝ) ≤
        (n : ℝ) * (Real.log 3 / Real.log 2) +
          ((3 / 2 : ℝ) * CA ^ 2 + CA) * Real.log (n : ℝ) := by
    nlinarith [hmain, hyoung']
  have hnpos : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [this] at hlog
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hratio :=
    mul_lt_mul_of_pos_left
      taoSection6_log_three_div_log_two_lt_eight_fifths hnreal
  have hupper :
      (n : ℝ) * (Real.log 3 / Real.log 2) +
          ((3 / 2 : ℝ) * CA ^ 2 + CA) * Real.log (n : ℝ) <
        (323 / 200 : ℝ) * (n : ℝ) := by
    nlinarith [hratio, hbudget]
  have hstrict : (20 : ℝ) * (k : ℝ) < 17 * (n : ℝ) := by
    nlinarith [hlinear.trans_lt hupper]
  exact_mod_cast hstrict.le

/-- For each fixed `CA`, every sufficiently large nonempty head gate obeys
Tao's stopping-index bound. -/
theorem exists_taoSection6HeadGate_index_le
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ Nindex : ℕ, ∀ n : ℕ, Nindex ≤ n →
      ∀ k l : ℕ, ∀ head : List ℕ+,
        taoSection6HeadGate CA n k l head →
          20 * k ≤ 17 * n := by
  let D : ℝ := (3 / 2 : ℝ) * CA ^ 2 + CA
  have hD : 0 < D := by
    dsimp [D]
    nlinarith
  obtain ⟨Nlog, hNlog⟩ :=
    exists_taoSection6_const_mul_log_le D (3 / 200 : ℝ)
      hD (by norm_num)
  refine ⟨max Nlog 2, ?_⟩
  intro n hn k l head hgate
  have hnlog : Nlog ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  apply taoSection6HeadGate_index_le_of_log_budget hlog
  simpa [D] using hNlog n hnlog
  exact hgate

/-- Pure arithmetic bridge from the high-regime bounds to `k+1 <= m`.  It is
independent of the conductor theorem that consumes this conclusion. -/
theorem taoSection6HeadIndex_le_m_of_bounds
    {n k m : ℕ} (hn : 1 ≤ n)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n) :
    k + 1 ≤ m := by
  omega

end

end Tao
end Erdos1135
