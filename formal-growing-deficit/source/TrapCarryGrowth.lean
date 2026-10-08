import TrapSlopeAsymptotics

set_option autoImplicit false
open Filter
open scoped Topology

namespace CollatzResearch

/-- The exact carry bound allows a signed gap; only the combined exponent
`D` is a natural number. -/
theorem trap_carry_abs_bound {a b z q0 q : ℤ}
    (D h hnext m u : ℕ) (g : ℤ) (epsilon : ℝ)
    (hq : 0 < q) (hmod : q0 = 9 ^ (m + u) * q)
    (hrec : a = 2 ^ D * b - z * q)
    (hD : (D : ℤ) = (hnext : ℤ) + g)
    (ha : |(a : ℝ)| ≤ epsilon * (q0 : ℝ) / (2 : ℝ) ^ h)
    (hb : |(b : ℝ)| ≤ epsilon * (q : ℝ) / (2 : ℝ) ^ hnext) :
    |(z : ℝ)| ≤ epsilon * (2 : ℝ) ^ g +
      epsilon * (9 : ℝ) ^ (m + u) / (2 : ℝ) ^ h := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrel : (z : ℝ) * (q : ℝ) = (2 : ℝ) ^ D * (b : ℝ) - (a : ℝ) := by
    exact_mod_cast (show z * q = 2 ^ D * b - a by linear_combination hrec)
  have hpow : (2 : ℝ) ^ D = (2 : ℝ) ^ hnext * (2 : ℝ) ^ g := by
    calc
      (2 : ℝ) ^ D = (2 : ℝ) ^ (D : ℤ) := by simp
      _ = (2 : ℝ) ^ ((hnext : ℤ) + g) := by rw [hD]
      _ = _ := by rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; simp
  have habs : |(z : ℝ)| * (q : ℝ) ≤
      (2 : ℝ) ^ D * |(b : ℝ)| + |(a : ℝ)| := by
    calc
      |(z : ℝ)| * (q : ℝ) = |(z : ℝ) * (q : ℝ)| := by
        rw [abs_mul, abs_of_pos hqR]
      _ = |(2 : ℝ) ^ D * (b : ℝ) - (a : ℝ)| := by rw [hrel]
      _ ≤ |(2 : ℝ) ^ D * (b : ℝ)| + |(a : ℝ)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le ((2 : ℝ) ^ D * (b : ℝ)) 0 (a : ℝ)
      _ = _ := by rw [abs_mul, abs_pow]; norm_num
  have hbound := habs.trans (add_le_add
    (mul_le_mul_of_nonneg_left hb (by positivity)) ha)
  have heq : (2 : ℝ) ^ D * (epsilon * (q : ℝ) / (2 : ℝ) ^ hnext) +
      epsilon * (q0 : ℝ) / (2 : ℝ) ^ h =
      (epsilon * (2 : ℝ) ^ g +
        epsilon * (9 : ℝ) ^ (m + u) / (2 : ℝ) ^ h) * (q : ℝ) := by
    rw [hpow, hmod]
    push_cast
    field_simp
  rw [heq] at hbound
  nlinarith

theorem trap_carry_abs_bound_mean_slope {a b z q0 q : ℤ}
    (D h hnext m u : ℕ) (g e : ℤ) (epsilon : ℝ)
    (hq : 0 < q) (hmod : q0 = 9 ^ (m + u) * q)
    (hrec : a = 2 ^ D * b - z * q)
    (hD : (D : ℤ) = (hnext : ℤ) + g)
    (hh : (h : ℤ) = 4 * (m : ℤ) + e)
    (ha : |(a : ℝ)| ≤ epsilon * (q0 : ℝ) / (2 : ℝ) ^ h)
    (hb : |(b : ℝ)| ≤ epsilon * (q : ℝ) / (2 : ℝ) ^ hnext) :
    |(z : ℝ)| ≤ epsilon * (2 : ℝ) ^ g +
      epsilon * ((9 : ℝ) ^ u * (2 : ℝ) ^ (-e) * (9 / 16 : ℝ) ^ m) := by
  have hpow : (2 : ℝ) ^ h = (16 : ℝ) ^ m * (2 : ℝ) ^ e := by
    calc
      (2 : ℝ) ^ h = (2 : ℝ) ^ (h : ℤ) := by simp
      _ = (2 : ℝ) ^ (4 * (m : ℤ) + e) := by rw [hh]
      _ = (2 : ℝ) ^ (4 * (m : ℤ)) * (2 : ℝ) ^ e := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = _ := by rw [zpow_mul]; norm_num
  have hfactor : (9 : ℝ) ^ (m + u) / (2 : ℝ) ^ h =
      (9 : ℝ) ^ u * (2 : ℝ) ^ (-e) * (9 / 16 : ℝ) ^ m := by
    rw [hpow, pow_add, div_pow, zpow_neg]
    field_simp
  have hbound := trap_carry_abs_bound D h hnext m u g epsilon hq hmod hrec hD ha hb
  simpa only [mul_div_assoc, hfactor] using hbound

/-- A fixed sum of the two carry contributions is subexponential when the
horizontal omissions and signed vertical errors are sublinear. -/
theorem eventually_trap_carry_subexponential
    (z g e : ℕ → ℤ) (m u : ℕ → ℕ) (N : ℕ → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hN : Tendsto N atTop atTop)
    (hbound : ∀ᶠ n in atTop, |(z n : ℝ)| ≤
      epsilon * (2 : ℝ) ^ g n +
        epsilon * ((9 : ℝ) ^ u n * (2 : ℝ) ^ (-e n) * (9 / 16 : ℝ) ^ m n))
    (hu : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, (u n : ℝ) ≤ gamma * N n)
    (hg : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, |(g n : ℝ)| ≤ gamma * N n)
    (he : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, |(e n : ℝ)| ≤ gamma * N n) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, |(z n : ℝ)| ≤ Real.exp (gamma * N n) := by
  have hN0 : ∀ᶠ n in atTop, 0 ≤ N n := hN.eventually (eventually_ge_atTop 0)
  have huabs : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop,
      |(u n : ℝ)| ≤ gamma * N n := by
    intro gamma hgamma
    simpa only [Nat.abs_cast] using hu gamma hgamma
  have hzero : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop,
      |(0 : ℝ)| ≤ gamma * N n := by
    intro gamma hgamma
    filter_upwards [hN0] with n hn
    simpa only [abs_zero] using mul_nonneg hgamma.le hn
  have hge := eventually_linear_error_bound (fun n => (g n : ℝ))
    (fun _ => (0 : ℝ)) N (Real.log 2) 0 hN0 hg hzero
  have hee := eventually_linear_error_bound (fun n => (u n : ℝ))
    (fun n => (e n : ℝ)) N (Real.log 9) (-Real.log 2) hN0 huabs he
  have hc : 0 < Real.log (16 / 9 : ℝ) := Real.log_pos (by norm_num)
  intro gamma hgamma
  have hhalf : 0 < gamma / 2 := by positivity
  let C : ℝ := max (2 * epsilon) 1
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hroom : ∀ᶠ n in atTop, 2 * Real.log C / gamma ≤ N n :=
    hN.eventually (eventually_ge_atTop _)
  filter_upwards [hbound, hge (gamma / 2) hhalf, hee (gamma / 2) hhalf, hroom]
    with n hzn hgn hen hroomn
  have hgrowth : (2 : ℝ) ^ g n ≤ Real.exp (gamma * N n / 2) := by
    have harg : (g n : ℝ) * Real.log 2 ≤ gamma * N n / 2 := by
      have h := (le_abs_self (Real.log 2 * (g n : ℝ) + 0 * 0)).trans hgn
      nlinarith
    calc
      (2 : ℝ) ^ g n = Real.exp ((g n : ℝ) * Real.log 2) := by
        rw [← Real.log_zpow, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr harg
  have eslope : (9 : ℝ) ^ u n * (2 : ℝ) ^ (-e n) * (9 / 16 : ℝ) ^ m n ≤
      Real.exp (gamma * N n / 2) := by
    rw [trap_slope_factor_eq_exp]
    apply Real.exp_le_exp.mpr
    have h := (le_abs_self (Real.log 9 * (u n : ℝ) + -Real.log 2 * (e n : ℝ))).trans hen
    have hm : (0 : ℝ) ≤ m n := by positivity
    nlinarith [mul_nonneg hc.le hm]
  have hconstant : 2 * epsilon ≤ Real.exp (gamma * N n / 2) := by
    have hlog : Real.log C ≤ gamma * N n / 2 := by
      have h := (div_le_iff₀ hgamma).mp hroomn
      nlinarith
    calc
      2 * epsilon ≤ C := le_max_left _ _
      _ = Real.exp (Real.log C) := (Real.exp_log hC).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  calc
    |(z n : ℝ)| ≤ epsilon * (2 : ℝ) ^ g n +
        epsilon * ((9 : ℝ) ^ u n * (2 : ℝ) ^ (-e n) * (9 / 16 : ℝ) ^ m n) := hzn
    _ ≤ epsilon * Real.exp (gamma * N n / 2) +
        epsilon * Real.exp (gamma * N n / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hgrowth hepsilon)
        (mul_le_mul_of_nonneg_left eslope hepsilon)
    _ = (2 * epsilon) * Real.exp (gamma * N n / 2) := by ring
    _ ≤ Real.exp (gamma * N n / 2) * Real.exp (gamma * N n / 2) :=
      mul_le_mul_of_nonneg_right hconstant (Real.exp_pos _).le
    _ = Real.exp (gamma * N n) := by rw [← Real.exp_add]; congr 1; ring

theorem eventually_trap_carry_subexponential_of_recurrences
    (a b z q0 q g e : ℕ → ℤ) (D h hnext m u : ℕ → ℕ) (N : ℕ → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hN : Tendsto N atTop atTop)
    (hq : ∀ᶠ n in atTop, 0 < q n)
    (hmod : ∀ᶠ n in atTop, q0 n = 9 ^ (m n + u n) * q n)
    (hrec : ∀ᶠ n in atTop, a n = 2 ^ D n * b n - z n * q n)
    (hD : ∀ᶠ n in atTop, (D n : ℤ) = (hnext n : ℤ) + g n)
    (hh : ∀ᶠ n in atTop, (h n : ℤ) = 4 * (m n : ℤ) + e n)
    (ha : ∀ᶠ n in atTop, |(a n : ℝ)| ≤ epsilon * (q0 n : ℝ) / (2 : ℝ) ^ h n)
    (hb : ∀ᶠ n in atTop, |(b n : ℝ)| ≤ epsilon * (q n : ℝ) / (2 : ℝ) ^ hnext n)
    (hu : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, (u n : ℝ) ≤ gamma * N n)
    (hg : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, |(g n : ℝ)| ≤ gamma * N n)
    (he : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, |(e n : ℝ)| ≤ gamma * N n) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, |(z n : ℝ)| ≤ Real.exp (gamma * N n) := by
  apply eventually_trap_carry_subexponential z g e m u N hepsilon hN ?_ hu hg he
  filter_upwards [hq, hmod, hrec, hD, hh, ha, hb]
    with n hqn hmodn hrecn hDn hhn han hbn
  exact trap_carry_abs_bound_mean_slope (D n) (h n) (hnext n) (m n) (u n)
    (g n) (e n) epsilon hqn hmodn hrecn hDn hhn han hbn

end CollatzResearch

#print axioms CollatzResearch.trap_carry_abs_bound
#print axioms CollatzResearch.trap_carry_abs_bound_mean_slope
#print axioms CollatzResearch.eventually_trap_carry_subexponential
#print axioms CollatzResearch.eventually_trap_carry_subexponential_of_recurrences
