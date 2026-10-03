import BoundedBottomPassageClock
import Erdos1135.Tao.Syracuse.ParityBridge

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.RawOccupation
open Erdos1135.Tao CollatzClockAudit

theorem syracuse_add_one_growth {q : ℕ} (hq : Odd q) :
    (syracuse q : ℝ) + 1 ≤ (3 / 2 : ℝ) * ((q : ℝ) + 1) := by
  have hpow : (2 : ℕ) ≤ 2 ^ syracuseExponent q := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
      (syracuseExponent_pos_of_odd hq)
  have hsmall : 2 * syracuse q ≤ 3 * q + 1 := by
    calc
      2 * syracuse q ≤ 2 ^ syracuseExponent q * syracuse q :=
        Nat.mul_le_mul_right _ hpow
      _ = 3 * q + 1 := two_pow_syracuseExponent_mul_syracuse q
  have hr : (2 : ℝ) * syracuse q ≤ 3 * q + 1 := by exact_mod_cast hsmall
  linarith

theorem syracuse_iterate_add_one_growth {q : ℕ} (hq : Odd q) (n : ℕ) :
    ((syracuse^[n]) q : ℝ) + 1 ≤ (3 / 2 : ℝ) ^ n * ((q : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        (syracuse ((syracuse^[n]) q) : ℝ) + 1 ≤
            (3 / 2 : ℝ) * (((syracuse^[n]) q : ℝ) + 1) :=
          syracuse_add_one_growth (syracuse_iterate_odd n q hq)
        _ ≤ (3 / 2 : ℝ) * ((3 / 2 : ℝ) ^ n * ((q : ℝ) + 1)) := by gcongr
        _ = (3 / 2 : ℝ) ^ (n + 1) * ((q : ℝ) + 1) := by rw [pow_succ]; ring

theorem syracuse_segment_confinement {q a k : ℕ} {x R U : ℝ}
    (hq : Odd q) (hland : ((syracuse^[a]) q : ℝ) ≤ x) (hak : a ≤ k)
    (htime : ((k - a : ℕ) : ℝ) ≤ U)
    (hbudget : (3 / 2 : ℝ) ^ U * (x + 1) ≤ R + 1) :
    ((syracuse^[k]) q : ℝ) ≤ R := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg _).trans hland
  have hg := syracuse_iterate_add_one_growth (syracuse_iterate_odd a q hq) (k - a)
  have hiter : (syracuse^[k - a]) ((syracuse^[a]) q) = (syracuse^[k]) q := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hak]
  rw [hiter] at hg
  have hp : (3 / 2 : ℝ) ^ (k - a) ≤ (3 / 2 : ℝ) ^ U := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) htime
  have hland' : (3 / 2 : ℝ) ^ (k - a) * (((syracuse^[a]) q : ℝ) + 1) ≤
      (3 / 2 : ℝ) ^ (k - a) * (x + 1) := by gcongr
  have hbound := hg.trans (hland'.trans
    ((mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ x + 1)).trans hbudget))
  linarith

theorem exists_time_grid_interval (t : ℕ → ℕ) (n k : ℕ)
    (hfirst : t 0 ≤ k) (hlast : k < t n) :
    ∃ i < n, t i ≤ k ∧ k < t (i + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : k < t n
      · obtain ⟨i, hi, hlo, hhi⟩ := ih h
        exact ⟨i, by omega, hlo, hhi⟩
      · exact ⟨n, Nat.lt_succ_self n, by omega, hlast⟩

theorem finite_clock_grid_step_bound {M x y E : ℝ} {q t u T : ℕ}
    (hyx : y ≤ x) (hMy : M ≤ y)
    (ht : syracuseFirstHitAtMostReal x q t)
    (hu : syracuseFirstHitAtMostReal y q u)
    (hT : syracuseFirstHitAtMostReal M q T)
    (hct : |((T - t : ℕ) : ℝ) - Real.log x / clockDrift| ≤ E)
    (hcu : |((T - u : ℕ) : ℝ) - Real.log y / clockDrift| ≤ E) :
    ((u - t : ℕ) : ℝ) ≤ (Real.log x - Real.log y) / clockDrift + 2 * E := by
  have htu := real_first_hit_time_mono hyx ht hu
  have huT := real_first_hit_time_mono hMy hu hT
  have htT := htu.trans huT
  rw [Nat.cast_sub htT] at hct
  rw [Nat.cast_sub huT] at hcu
  rw [Nat.cast_sub htu]
  obtain ⟨hctlo, hcthi⟩ := abs_le.mp hct
  obtain ⟨hculo, hcuhi⟩ := abs_le.mp hcu
  calc
    (u : ℝ) - t ≤ Real.log x / clockDrift - Real.log y / clockDrift + 2 * E := by
      linarith
    _ = _ := by ring

/-- A finite family of actual barrier clocks controls every intermediate
height. The two displayed budgets retain all finite clock errors. -/
theorem finite_clock_grid_confinement (x : ℕ → ℝ) (t : ℕ → ℕ)
    {M R E : ℝ} {q T n : ℕ} (hq : Odd q)
    (hdown : ∀ i < n, x (i + 1) ≤ x i)
    (hbottom : ∀ i ≤ n, M ≤ x i)
    (hfirst : ∀ i ≤ n, syracuseFirstHitAtMostReal (x i) q (t i))
    (hT : syracuseFirstHitAtMostReal M q T)
    (hclock : ∀ i ≤ n,
      |((T - t i : ℕ) : ℝ) - Real.log (x i) / clockDrift| ≤ E)
    (hstageBudget : ∀ i < n,
      (3 / 2 : ℝ) ^ ((Real.log (x i) - Real.log (x (i + 1))) / clockDrift + 2 * E) *
        (x i + 1) ≤ R + 1)
    (hlastBudget : (3 / 2 : ℝ) ^ (Real.log (x n) / clockDrift + E) *
      (x n + 1) ≤ R + 1) :
    ∀ k, t 0 ≤ k → k < T → ((syracuse^[k]) q : ℝ) ≤ R := by
  intro k hk0 hkT
  by_cases hkn : t n ≤ k
  · apply syracuse_segment_confinement hq (hfirst n le_rfl).1 hkn _ hlastBudget
    have htime : ((k - t n : ℕ) : ℝ) ≤ ((T - t n : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right hkT.le (t n)
    exact htime.trans (by linarith [(abs_le.mp (hclock n le_rfl)).2])
  · obtain ⟨i, hin, hil, hih⟩ := exists_time_grid_interval t n k hk0 (by omega)
    apply syracuse_segment_confinement hq (hfirst i hin.le).1 hil _ (hstageBudget i hin)
    have htime : ((k - t i : ℕ) : ℝ) ≤ ((t (i + 1) - t i : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right hih.le (t i)
    exact htime.trans (finite_clock_grid_step_bound (hdown i hin)
      (hbottom (i + 1) (by omega)) (hfirst i hin.le) (hfirst (i + 1) (by omega))
      hT (hclock i hin.le) (hclock (i + 1) (by omega)))

#print axioms syracuse_iterate_add_one_growth
#print axioms finite_clock_grid_step_bound
#print axioms finite_clock_grid_confinement

end CollatzCanonical.RawOccupation
