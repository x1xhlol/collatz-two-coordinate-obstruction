import FirstHitWordWeights

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- The least shortcut hitting time, defined only when a hit exists. -/
noncomputable def firstHitTime {q N : ℕ} (hhit : ∃ A, iterate A q = N) : ℕ := Nat.find hhit

theorem firstHitTime_spec {q N : ℕ} (hhit : ∃ A, iterate A q = N) :
    FirstHit q N (firstHitTime hhit) := firstHit_find hhit

/-- Every hit occurs after the first hit. -/
theorem first_hit_le_of_hit {q N τ n : ℕ} (hfirst : FirstHit q N τ)
    (hhit : iterate n q = N) : τ ≤ n := by
  by_contra h
  exact hfirst.2 n (Nat.lt_of_not_ge h) hhit

/-- All later hits are exactly the first hit followed by a return of the target. -/
theorem hitting_time_iff_first_plus_return {q N τ n : ℕ} (hfirst : FirstHit q N τ) :
    iterate n q = N ↔ ∃ d : ℕ, n = τ + d ∧ iterate d N = N := by
  constructor
  · intro hhit
    have hle := first_hit_le_of_hit hfirst hhit
    refine ⟨n - τ, by omega, ?_⟩
    have he : τ + (n - τ) = n := by omega
    have hi := iterate_add τ (n - τ) q
    rw [he, hfirst.1, hhit] at hi
    exact hi.symm
  · rintro ⟨d, rfl, hd⟩
    rw [iterate_add, hfirst.1, hd]

/-- Equivalent form that identifies the elapsed return time by subtraction. -/
theorem hitting_time_iff_first_le_and_return {q N τ n : ℕ} (hfirst : FirstHit q N τ) :
    iterate n q = N ↔ τ ≤ n ∧ iterate (n - τ) N = N := by
  rw [hitting_time_iff_first_plus_return hfirst]
  constructor
  · rintro ⟨d, rfl, hd⟩
    exact ⟨by omega, by simpa using hd⟩
  · rintro ⟨hle, hd⟩
    exact ⟨n - τ, by omega, hd⟩

/-- A target with no positive return can be hit only once along a trajectory. -/
theorem hitting_time_iff_eq_first_of_no_return {q N τ n : ℕ}
    (hfirst : FirstHit q N τ)
    (hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N) :
    iterate n q = N ↔ n = τ := by
  rw [hitting_time_iff_first_plus_return hfirst]
  constructor
  · rintro ⟨d, he, hd⟩
    have hz : d = 0 := by
      by_contra h
      exact hno d (Nat.pos_of_ne_zero h) hd
    simpa only [hz, Nat.add_zero] using he
  · intro he
    exact ⟨0, by omega, rfl⟩

/-- A positive period with the actual least-return property. -/
structure LeastPositivePeriod (N r : ℕ) : Prop where
  positive : 0 < r
  returns : iterate r N = N
  minimal : ∀ d : ℕ, 0 < d → iterate d N = N → r ≤ d

/-- A least positive return period exists whenever a positive return exists. -/
theorem exists_least_positive_period {N : ℕ}
    (hreturn : ∃ r : ℕ, 0 < r ∧ iterate r N = N) :
    ∃ r : ℕ, LeastPositivePeriod N r := by
  let r := Nat.find hreturn
  have hr := Nat.find_spec hreturn
  refine ⟨r, hr.1, hr.2, ?_⟩
  intro d hd hret
  exact Nat.find_min' hreturn ⟨hd, hret⟩

/-- Every multiple of an actual return time is itself a return time. -/
theorem iterate_mul_period {N r : ℕ} (hperiod : iterate r N = N) (j : ℕ) :
    iterate (j * r) N = N := by
  induction j with
  | zero => simp [iterate]
  | succ j ih =>
    rw [Nat.succ_mul, iterate_add, ih, hperiod]

/-- Iteration at a periodic target reduces to the Euclidean remainder. -/
theorem iterate_eq_mod_period {N r : ℕ} (hperiod : iterate r N = N) (n : ℕ) :
    iterate n N = iterate (n % r) N := by
  have he : n = (n / r) * r + n % r := by
    have h := Nat.mod_add_div n r
    rw [Nat.mul_comm r (n / r)] at h
    omega
  conv_lhs => rw [he]
  rw [iterate_add, iterate_mul_period hperiod]

/-- At a least positive period, all target return times are exactly multiples. -/
theorem return_time_iff_multiple {N r n : ℕ} (hperiod : LeastPositivePeriod N r) :
    iterate n N = N ↔ ∃ j : ℕ, n = j * r := by
  constructor
  · intro hret
    have hmod : iterate (n % r) N = N := by
      rwa [iterate_eq_mod_period hperiod.returns] at hret
    have hzero : n % r = 0 := by
      by_contra hne
      have hge := hperiod.minimal (n % r) (Nat.pos_of_ne_zero hne) hmod
      exact Nat.not_le_of_gt (Nat.mod_lt n hperiod.positive) hge
    refine ⟨n / r, ?_⟩
    have h := Nat.mod_add_div n r
    rw [hzero, Nat.zero_add, Nat.mul_comm r (n / r)] at h
    exact h.symm
  · rintro ⟨j, rfl⟩
    exact iterate_mul_period hperiod.returns j

theorem return_time_iff_dvd {N r n : ℕ} (hperiod : LeastPositivePeriod N r) :
    iterate n N = N ↔ r ∣ n := by
  rw [return_time_iff_multiple hperiod]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, by simpa only [Nat.mul_comm] using hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, by simpa only [Nat.mul_comm] using hj⟩

/-- All hits of a periodic target are the first hit plus integral period loops. -/
theorem hitting_time_iff_first_plus_periods {q N τ n r : ℕ}
    (hfirst : FirstHit q N τ) (hperiod : LeastPositivePeriod N r) :
    iterate n q = N ↔ ∃ j : ℕ, n = τ + j * r := by
  rw [hitting_time_iff_first_plus_return hfirst]
  constructor
  · rintro ⟨d, hd, hret⟩
    obtain ⟨j, hj⟩ := (return_time_iff_multiple hperiod).mp hret
    exact ⟨j, by omega⟩
  · rintro ⟨j, hj⟩
    exact ⟨j * r, hj, iterate_mul_period hperiod.returns j⟩

/-- The canonical first-hit-time version of the periodic classification. -/
theorem hitting_time_iff_firstHitTime_plus_periods {q N n r : ℕ}
    (hhit : ∃ A, iterate A q = N) (hperiod : LeastPositivePeriod N r) :
    iterate n q = N ↔ ∃ j : ℕ, n = firstHitTime hhit + j * r :=
  hitting_time_iff_first_plus_periods (firstHitTime_spec hhit) hperiod

/-- The canonical first-hit-time version when the target has no positive return. -/
theorem hitting_time_iff_eq_firstHitTime_of_no_return {q N n : ℕ}
    (hhit : ∃ A, iterate A q = N)
    (hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N) :
    iterate n q = N ↔ n = firstHitTime hhit :=
  hitting_time_iff_eq_first_of_no_return (firstHitTime_spec hhit) hno

end CollatzCylinderPacking.Arithmetic
