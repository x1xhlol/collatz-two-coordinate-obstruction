import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace CollatzCylinderPacking.Arithmetic.InverseDoob.ClockGeometry

theorem bracket_height_bounds
    {Y : ℕ → ℕ} {k s t : ℕ} {A B beta L g : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hbeta : 0 < beta) (hL : 0 ≤ L)
    (hg : 0 ≤ g) (hk : 0 < k) (hsk : s < k) (hkt : k ≤ t)
    (hlow : A * L ≤ (s : ℝ)) (hhigh : (t : ℝ) ≤ B * (beta * L))
    (hy : L ≤ Real.log (Y k : ℝ))
    (hyt : (Y t : ℝ) ≤ Real.exp (beta * L))
    (hback : Real.log ((Y k : ℝ) + 1) ≤
      Real.log ((Y t : ℝ) + 1) + g * ((t - k : ℕ) : ℝ)) :
    1 / (B * beta) ≤ Real.log (Y k : ℝ) / (k : ℝ) ∧
    Real.log (Y k : ℝ) / (k : ℝ) ≤
      beta * (1 + g * B) / A - g + Real.log 2 / (k : ℝ) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsk' : (s : ℝ) < (k : ℝ) := by exact_mod_cast hsk
  have hkt' : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkt
  have hBb : 0 < B * beta := mul_pos hB hbeta
  have hLb : (k : ℝ) / (B * beta) ≤ L := by
    apply (div_le_iff₀ hBb).mpr
    nlinarith
  have hLu : L ≤ (k : ℝ) / A := (le_div_iff₀ hA).mpr (by nlinarith)
  have hlogY : Real.log (Y k : ℝ) ≤ Real.log ((Y k : ℝ) + 1) := by
    by_cases hy0 : Y k = 0
    · simp [hy0]
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hy0) (by linarith)
  have he : 1 ≤ Real.exp (beta * L) := Real.one_le_exp_iff.mpr (mul_nonneg hbeta.le hL)
  have hsum : (Y t : ℝ) + 1 ≤ 2 * Real.exp (beta * L) := by linarith
  have hlogt : Real.log ((Y t : ℝ) + 1) ≤ beta * L + Real.log 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < Y t + 1) hsum
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at h
    linarith
  have hsub : ((t - k : ℕ) : ℝ) = (t : ℝ) - (k : ℝ) := Nat.cast_sub hkt
  have hupper : Real.log (Y k : ℝ) ≤
      (beta * (1 + g * B) / A - g) * (k : ℝ) + Real.log 2 := by
    have hcoeff : 0 ≤ beta * (1 + g * B) := by positivity
    have hscale := mul_le_mul_of_nonneg_left hLu hcoeff
    have htime := mul_le_mul_of_nonneg_left hhigh hg
    rw [hsub] at hback
    calc
      Real.log (Y k : ℝ) ≤ beta * (1 + g * B) * L - g * (k : ℝ) + Real.log 2 := by
        nlinarith
      _ ≤ (beta * (1 + g * B) / A - g) * (k : ℝ) + Real.log 2 := by
        convert add_le_add_right (sub_le_sub_right hscale (g * (k : ℝ))) (Real.log 2) using 1 <;> ring
  constructor
  · apply (le_div_iff₀ hk0).mpr
    have h := hLb.trans hy
    convert h using 1
    ring
  · have h := div_le_div_of_nonneg_right hupper hk0.le
    convert h using 1
    field_simp

theorem height_bounds_of_uniform_last_clocks
    {Y sigma : ℕ → ℕ} {A B beta base g : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hbeta : 1 < beta) (hbase : 0 < base)
    (hg : 0 ≤ g)
    (hclock : ∀ j : ℕ,
      A * (base * beta ^ j) ≤ (sigma j : ℝ) ∧
      (sigma j : ℝ) ≤ B * (base * beta ^ j))
    (hcut : ∀ j : ℕ, (Y (sigma j) : ℝ) ≤ Real.exp (base * beta ^ j))
    (hafter : ∀ j k : ℕ, sigma j < k → Real.exp (base * beta ^ j) < (Y k : ℝ))
    (hback : ∀ k t : ℕ, k ≤ t → Real.log ((Y k : ℝ) + 1) ≤
      Real.log ((Y t : ℝ) + 1) + g * ((t - k : ℕ) : ℝ))
    {k : ℕ} (hk : sigma 0 < k) :
    1 / (B * beta) ≤ Real.log (Y k : ℝ) / (k : ℝ) ∧
    Real.log (Y k : ℝ) / (k : ℝ) ≤
      beta * (1 + g * B) / A - g + Real.log 2 / (k : ℝ) := by
  have hb : 0 < beta := zero_lt_one.trans hbeta
  have hpow : Tendsto (fun j : ℕ => A * (base * beta ^ j)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hA).mpr
      ((tendsto_const_mul_atTop_of_pos hbase).mpr (tendsto_pow_atTop_atTop_of_one_lt hbeta))
  have hex : ∃ j : ℕ, k ≤ sigma j := by
    obtain ⟨j, hj⟩ := (hpow.eventually_ge_atTop (k : ℝ)).exists
    refine ⟨j, ?_⟩
    exact_mod_cast hj.trans (hclock j).1
  have hkj := Nat.find_spec hex
  have hjpos : 0 < Nat.find hex := by
    by_contra hn
    have hz : Nat.find hex = 0 := by omega
    rw [hz] at hkj
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
  have hprev : sigma j < k := by
    have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    omega
  have hnext : k ≤ sigma (j + 1) := by simpa only [hj] using hkj
  have hlog : base * beta ^ j ≤ Real.log (Y k : ℝ) := by
    have ha := hafter j k hprev
    have hl := Real.log_lt_log (Real.exp_pos _) ha
    rw [Real.log_exp] at hl
    exact hl.le
  have hlevel : base * beta ^ (j + 1) = beta * (base * beta ^ j) := by
    rw [pow_succ]
    ring
  apply bracket_height_bounds hA hB hb (by positivity) hg
    (Nat.zero_le (sigma 0) |>.trans_lt hk) hprev hnext (hclock j).1
  · simpa only [hlevel] using (hclock (j + 1)).2
  · exact hlog
  · simpa only [hlevel] using hcut (j + 1)
  · exact hback _ _ hnext

theorem eventual_height_bounds_of_eventual_last_clocks
    {Y sigma : ℕ → ℕ} {A B beta base g : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hbeta : 1 < beta) (hbase : 0 < base)
    (hg : 0 ≤ g)
    (hclock : ∀ᶠ j : ℕ in atTop,
      A * (base * beta ^ j) ≤ (sigma j : ℝ) ∧
      (sigma j : ℝ) ≤ B * (base * beta ^ j))
    (hcut : ∀ j : ℕ, (Y (sigma j) : ℝ) ≤ Real.exp (base * beta ^ j))
    (hafter : ∀ j k : ℕ, sigma j < k → Real.exp (base * beta ^ j) < (Y k : ℝ))
    (hback : ∀ k t : ℕ, k ≤ t → Real.log ((Y k : ℝ) + 1) ≤
      Real.log ((Y t : ℝ) + 1) + g * ((t - k : ℕ) : ℝ)) :
    ∀ᶠ k : ℕ in atTop,
      1 / (B * beta) ≤ Real.log (Y k : ℝ) / (k : ℝ) ∧
      Real.log (Y k : ℝ) / (k : ℝ) ≤
        beta * (1 + g * B) / A - g + Real.log 2 / (k : ℝ) := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hclock
  have hb : 0 < beta := zero_lt_one.trans hbeta
  have hlevel (j : ℕ) : (base * beta ^ J) * beta ^ j = base * beta ^ (J + j) := by
    rw [pow_add]
    ring
  filter_upwards [eventually_gt_atTop (sigma J)] with k hk
  apply height_bounds_of_uniform_last_clocks (Y := Y) (sigma := fun j => sigma (J + j))
    hA hB hbeta (mul_pos hbase (pow_pos hb J)) hg
  · intro j
    simpa only [hlevel] using hJ (J + j) (by omega)
  · intro j
    simpa only [hlevel] using hcut (J + j)
  · intro j r hr
    simpa only [hlevel] using hafter (J + j) r hr
  · exact hback
  · simpa only [Nat.add_zero] using hk

theorem eventual_height_band_of_last_clock_limit
    {Y sigma : ℕ → ℕ} {q beta base g lower upper : ℝ}
    (hq : 0 < q) (hbeta : 1 < beta) (hbase : 0 < base) (hg : 0 ≤ g)
    (hclock : Tendsto (fun j : ℕ => (sigma j : ℝ) / (base * beta ^ j))
      atTop (𝓝 q))
    (hcut : ∀ j : ℕ, (Y (sigma j) : ℝ) ≤ Real.exp (base * beta ^ j))
    (hafter : ∀ j k : ℕ, sigma j < k → Real.exp (base * beta ^ j) < (Y k : ℝ))
    (hback : ∀ k t : ℕ, k ≤ t → Real.log ((Y k : ℝ) + 1) ≤
      Real.log ((Y t : ℝ) + 1) + g * ((t - k : ℕ) : ℝ))
    (hlower : lower < 1 / (q * beta))
    (hupper : beta * (1 + g * q) / q - g < upper) :
    ∀ᶠ k : ℕ in atTop,
      lower < Real.log (Y k : ℝ) / (k : ℝ) ∧
      Real.log (Y k : ℝ) / (k : ℝ) < upper := by
  have hb : 0 < beta := zero_lt_one.trans hbeta
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hA : Tendsto (fun m : ℕ => q - (m : ℝ)⁻¹) atTop (𝓝 q) := by
    simpa only [sub_zero] using hi.const_sub q
  have hB : Tendsto (fun m : ℕ => q + (m : ℝ)⁻¹) atTop (𝓝 q) := by
    simpa only [add_zero] using hi.const_add q
  have hlo : Tendsto (fun m : ℕ => 1 / ((q + (m : ℝ)⁻¹) * beta))
      atTop (𝓝 (1 / (q * beta))) :=
    tendsto_const_nhds.div (hB.mul_const beta) (mul_ne_zero hq.ne' hb.ne')
  have hup : Tendsto (fun m : ℕ => beta * (1 + g * (q + (m : ℝ)⁻¹)) /
      (q - (m : ℝ)⁻¹) - g) atTop (𝓝 (beta * (1 + g * q) / q - g)) :=
    ((((hB.const_mul g).const_add 1).const_mul beta).div hA hq.ne').sub_const g
  obtain ⟨m, hm, hAm, hlom, hupm⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    ((hA.eventually_const_lt hq).and ((hlo.eventually_const_lt hlower).and
      (hup.eventually_lt_const hupper)))).exists
  have hmpos : 0 < (m : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hm)
  have hBm : 0 < q + (m : ℝ)⁻¹ := add_pos hq hmpos
  have hclocks : ∀ᶠ j : ℕ in atTop,
      (q - (m : ℝ)⁻¹) * (base * beta ^ j) ≤ (sigma j : ℝ) ∧
      (sigma j : ℝ) ≤ (q + (m : ℝ)⁻¹) * (base * beta ^ j) := by
    filter_upwards [hclock.eventually_const_lt (by linarith : q - (m : ℝ)⁻¹ < q),
      hclock.eventually_lt_const (by linarith : q < q + (m : ℝ)⁻¹)] with j hjlo hjhi
    have hl : 0 < base * beta ^ j := mul_pos hbase (pow_pos hb j)
    constructor
    · exact ((lt_div_iff₀ hl).mp hjlo).le
    · have h := ((div_lt_iff₀ hl).mp hjhi).le
      nlinarith
  have hsmall : ∀ᶠ k : ℕ in atTop,
      Real.log 2 / (k : ℝ) < upper -
        (beta * (1 + g * (q + (m : ℝ)⁻¹)) / (q - (m : ℝ)⁻¹) - g) := by
    have ht := hi.const_mul (Real.log 2)
    have ht' : Tendsto (fun k : ℕ => Real.log 2 / (k : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using ht
    exact ht'.eventually_lt_const (by linarith)
  filter_upwards [eventual_height_bounds_of_eventual_last_clocks hAm hBm hbeta hbase hg
    hclocks hcut hafter hback, hsmall] with k hk hs
  exact ⟨hlom.trans_le hk.1, by linarith [hk.2]⟩

theorem height_clock_of_refining_last_clock_grids
    {Y : ℕ → ℕ} {sigma : ℕ → ℕ → ℕ} {beta base : ℕ → ℝ} {q g : ℝ}
    (hq : 0 < q) (hg : 0 ≤ g)
    (hbeta : ∀ r, 1 < beta r) (hbase : ∀ r, 0 < base r)
    (hbetalim : Tendsto beta atTop (𝓝 1))
    (hclock : ∀ r, Tendsto (fun j : ℕ => (sigma r j : ℝ) / (base r * beta r ^ j))
      atTop (𝓝 q))
    (hcut : ∀ r j : ℕ, (Y (sigma r j) : ℝ) ≤ Real.exp (base r * beta r ^ j))
    (hafter : ∀ r j k : ℕ, sigma r j < k →
      Real.exp (base r * beta r ^ j) < (Y k : ℝ))
    (hback : ∀ k t : ℕ, k ≤ t → Real.log ((Y k : ℝ) + 1) ≤
      Real.log ((Y t : ℝ) + 1) + g * ((t - k : ℕ) : ℝ)) :
    Tendsto (fun k : ℕ => Real.log (Y k : ℝ) / (k : ℝ)) atTop (𝓝 (1 / q)) := by
  have hlo : Tendsto (fun r : ℕ => 1 / (q * beta r)) atTop (𝓝 (1 / q)) := by
    simpa only [mul_one] using tendsto_const_nhds.div (hbetalim.const_mul q)
      (show q * 1 ≠ 0 by simpa only [mul_one] using hq.ne')
  have hup : Tendsto (fun r : ℕ => beta r * (1 + g * q) / q - g)
      atTop (𝓝 (1 / q)) := by
    have h := ((hbetalim.mul_const (1 + g * q)).div_const q).sub_const g
    convert h using 1
    congr 1
    field_simp
    ring
  have hband (lower upper : ℝ) (hlower : lower < 1 / q) (hupper : 1 / q < upper) :
      ∀ᶠ k : ℕ in atTop,
        lower < Real.log (Y k : ℝ) / (k : ℝ) ∧
        Real.log (Y k : ℝ) / (k : ℝ) < upper := by
    obtain ⟨r, hrlo, hrup⟩ := ((hlo.eventually_const_lt hlower).and
      (hup.eventually_lt_const hupper)).exists
    exact eventual_height_band_of_last_clock_limit hq (hbeta r) (hbase r) hg
      (hclock r) (hcut r) (hafter r) hback hrlo hrup
  apply tendsto_order.mpr
  constructor
  · intro lower hlower
    exact (hband lower (1 / q + 1) hlower (by linarith)).mono (fun _ h => h.1)
  · intro upper hupper
    exact (hband (1 / q - 1) upper (by linarith) hupper).mono (fun _ h => h.2)

#print axioms bracket_height_bounds
#print axioms height_bounds_of_uniform_last_clocks
#print axioms eventual_height_bounds_of_eventual_last_clocks
#print axioms eventual_height_band_of_last_clock_limit
#print axioms height_clock_of_refining_last_clock_grids

end CollatzCylinderPacking.Arithmetic.InverseDoob.ClockGeometry
