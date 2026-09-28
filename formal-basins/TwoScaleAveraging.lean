import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

open Filter Set
open scoped Topology

namespace CollatzCanonical.TwoScale

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bounded bilateral solution of an expanding difference recurrence is zero. -/
theorem bounded_expanding_recurrence_eq_zero
    (D : ℝ → V) (b m C : ℝ) (hb : 1 < b)
    (hbound : ∀ u, ‖D u‖ ≤ C)
    (hrec : ∀ u, b • D (u + m) = D u) :
    ∀ u, D u = 0 := by
  intro u
  have hback (n : ℕ) : D (u - (n : ℝ) * m) = b ^ n • D u := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hrec (u - ((n + 1 : ℕ) : ℝ) * m)
      have he : u - ((n + 1 : ℕ) : ℝ) * m + m = u - (n : ℝ) * m := by
        push_cast
        ring
      rw [he, ih, smul_smul] at hh
      simpa [pow_succ, mul_comm] using hh.symm
  by_contra hne
  have hpos : 0 < ‖D u‖ := norm_pos_iff.mpr hne
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖D u‖) hb
  have hh := hbound (u - (n : ℝ) * m)
  rw [hback, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (by linarith) n)] at hh
  have hlt : C < b ^ n * ‖D u‖ := (div_lt_iff₀ hpos).mp hn
  linarith

omit [NormedSpace ℝ V] in
/-- A continuous function with two incommensurable real periods is constant. -/
theorem eq_const_of_continuous_two_periods
    (P : ℝ → V) (a b : ℝ) (hP : Continuous P)
    (ha : Function.Periodic P a) (hb : Function.Periodic P b)
    (hirr : Irrational (a / b)) :
    ∀ u, P u = P 0 := by
  let periods : AddSubgroup ℝ :=
    { carrier := {c | Function.Periodic P c}
      zero_mem' := Function.periodic_with_period_zero P
      add_mem' := fun hx hy => hx.add_period hy
      neg_mem' := fun hx => hx.neg }
  have hclosure : AddSubgroup.closure {a, b} ≤ periods := by
    apply (AddSubgroup.closure_le periods).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hdense : Dense (periods : Set ℝ) :=
    (dense_addSubgroupClosure_pair_iff.mpr hirr).mono hclosure
  have hclosed : IsClosed {u | P u = P 0} := isClosed_eq hP continuous_const
  have hsubset : (periods : Set ℝ) ⊆ {u | P u = P 0} := by
    intro u hu
    exact Function.Periodic.eq hu
  intro u
  exact closure_minimal hsubset hclosed (hdense u)

omit [NormedSpace ℝ V] in
/-- Summable translation errors produce a genuine periodic limiting profile. -/
theorem exists_periodic_profile_of_exp_shift [CompleteSpace V]
    (Q : ℝ → V) (h C c : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hshift : ∀ u, ‖Q (u + h) - Q u‖ ≤ C * Real.exp (-c * u)) :
    ∃ P : ℝ → V, Function.Periodic P h ∧
      (∀ u, Tendsto (fun n : ℕ => Q (u + n * h)) atTop (𝓝 (P u))) ∧
      (∀ u, ‖Q u - P u‖ ≤ C * Real.exp (-c * u) / (1 - Real.exp (-c * h))) := by
  have hr : Real.exp (-c * h) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hgeom (u : ℝ) (n : ℕ) :
      dist (Q (u + n * h)) (Q (u + (n + 1 : ℕ) * h)) ≤
        (C * Real.exp (-c * u)) * Real.exp (-c * h) ^ n := by
    have hs := hshift (u + n * h)
    have he : -c * (u + n * h) = -c * u + (n : ℝ) * (-c * h) := by ring
    rw [he, Real.exp_add, Real.exp_nat_mul] at hs
    have hu : u + ((n + 1 : ℕ) : ℝ) * h = (u + n * h) + h := by
      push_cast
      ring
    rw [hu, dist_eq_norm, norm_sub_rev]
    simpa only [mul_assoc] using hs
  have hex (u : ℝ) : ∃ p : V,
      Tendsto (fun n : ℕ => Q (u + n * h)) atTop (𝓝 p) :=
    cauchySeq_tendsto_of_complete
      (cauchySeq_of_le_geometric (Real.exp (-c * h))
        (C * Real.exp (-c * u)) hr (hgeom u))
  choose P hP using hex
  refine ⟨P, ?_, hP, ?_⟩
  · intro u
    have ht := (hP u).comp (tendsto_add_atTop_nat 1)
    have he : (fun n : ℕ => Q (u + (n + 1 : ℕ) * h)) =
        (fun n : ℕ => Q ((u + h) + n * h)) := by
      funext n
      congr 1
      push_cast
      ring
    change Tendsto (fun n : ℕ => Q (u + (n + 1 : ℕ) * h)) atTop (𝓝 (P u)) at ht
    rw [he] at ht
    exact tendsto_nhds_unique (hP (u + h)) ht
  · intro u
    have ht := dist_le_of_le_geometric_of_tendsto₀
      (Real.exp (-c * h)) (C * Real.exp (-c * u)) hr (hgeom u) (hP u)
    simpa [dist_eq_norm] using ht

/-- A stable affine recurrence inherits a geometric majorant for its forcing. -/
theorem stable_recurrence_geometric_bound
    (E Z : ℕ → V) (d r ρ K A : ℝ)
    (hd : 0 ≤ d) (hr : 0 ≤ r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hK : 0 ≤ K) (hA : ‖E 0‖ ≤ A) (hKA : K ≤ A * (ρ - d))
    (hrec : ∀ n, E (n + 1) = d • E n + Z n)
    (hZ : ∀ n, ‖Z n‖ ≤ K * r ^ n) :
    ∀ n, ‖E n‖ ≤ A * ρ ^ n := by
  intro n
  induction n with
  | zero => simpa using hA
  | succ n ih =>
    have hp : r ^ n ≤ ρ ^ n := pow_le_pow_left₀ hr hrρ n
    calc
      ‖E (n + 1)‖ = ‖d • E n + Z n‖ := by rw [hrec]
      _ ≤ ‖d • E n‖ + ‖Z n‖ := norm_add_le _ _
      _ = d * ‖E n‖ + ‖Z n‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]
      _ ≤ d * (A * ρ ^ n) + K * r ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left ih hd) (hZ n)
      _ ≤ d * (A * ρ ^ n) + K * ρ ^ n :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hK)
      _ ≤ A * ρ ^ (n + 1) := by
        have hh := mul_le_mul_of_nonneg_right hKA (pow_nonneg hρ n)
        rw [pow_succ]
        nlinarith

/-- Stable recurrences with geometrically vanishing forcing converge in norm. -/
theorem stable_recurrence_tendsto_zero
    (E Z : ℕ → V) (d r K : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hr : 0 ≤ r) (hr1 : r < 1)
    (hK : 0 ≤ K)
    (hrec : ∀ n, E (n + 1) = d • E n + Z n)
    (hZ : ∀ n, ‖Z n‖ ≤ K * r ^ n) :
    Tendsto E atTop (𝓝 0) := by
  obtain ⟨ρ, hmax, hρ1⟩ := exists_between (max_lt hd1 hr1)
  have hdρ : d < ρ := lt_of_le_of_lt (le_max_left _ _) hmax
  have hrρ : r ≤ ρ := (lt_of_le_of_lt (le_max_right _ _) hmax).le
  have hρ : 0 ≤ ρ := hr.trans hrρ
  have hden : 0 < ρ - d := sub_pos.mpr hdρ
  let A := ‖E 0‖ + K / (ρ - d)
  have hA : ‖E 0‖ ≤ A := le_add_of_nonneg_right (div_nonneg hK hden.le)
  have hKA : K ≤ A * (ρ - d) := by
    dsimp [A]
    rw [add_mul, div_mul_cancel₀ _ hden.ne']
    exact le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) hden.le)
  have hbound := stable_recurrence_geometric_bound E Z d r ρ K A
    hd hr hrρ hρ hK hA hKA hrec hZ
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul A

/-- A stable recurrence with bounded forcing has the usual geometric resolvent bound. -/
theorem stable_recurrence_const_bound
    (E Z : ℕ → V) (d K C : ℝ) (hd : 0 ≤ d) (hd1 : d < 1)
    (hK : 0 ≤ K) (hC : ‖E 0‖ ≤ C)
    (hrec : ∀ n, E (n + 1) = d • E n + Z n)
    (hZ : ∀ n, ‖Z n‖ ≤ K) :
    ∀ n, ‖E n‖ ≤ d ^ n * C + K / (1 - d) := by
  have hden : 0 < 1 - d := sub_pos.mpr hd1
  have hidentity : d * (K / (1 - d)) + K = K / (1 - d) := by
    field_simp
    ring
  intro n
  induction n with
  | zero =>
    simpa using hC.trans (le_add_of_nonneg_right (div_nonneg hK hden.le))
  | succ n ih =>
    calc
      ‖E (n + 1)‖ = ‖d • E n + Z n‖ := by rw [hrec]
      _ ≤ ‖d • E n‖ + ‖Z n‖ := norm_add_le _ _
      _ = d * ‖E n‖ + ‖Z n‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]
      _ ≤ d * (d ^ n * C + K / (1 - d)) + K :=
        add_le_add (mul_le_mul_of_nonneg_left ih hd) (hZ n)
      _ = d ^ (n + 1) * C + K / (1 - d) := by
        rw [mul_add, add_assoc, hidentity, pow_succ]
        ring

/-- Bounded solutions of a stable translation recurrence converge when their forcing does. -/
theorem stable_translation_tendsto_zero
    (E Z : ℝ → V) (d h C : ℝ) (hd : 0 ≤ d) (hd1 : d < 1) (hh : 0 ≤ h)
    (hbound : ∀ u, ‖E u‖ ≤ C)
    (hrec : ∀ u, E (u + h) = d • E u + Z u)
    (hZ : Tendsto Z atTop (𝓝 0)) :
    Tendsto E atTop (𝓝 0) := by
  have hC : 0 ≤ C := (norm_nonneg (E 0)).trans (hbound 0)
  have hden : 0 < 1 - d := sub_pos.mpr hd1
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hpow : Tendsto (fun n : ℕ => d ^ n * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hd hd1).mul_const C
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hpow (ε / 2) hhalf
  have hN' : d ^ N * C < ε / 2 := by
    have := hN N le_rfl
    change |d ^ N * C - 0| < ε / 2 at this
    rw [sub_zero, abs_of_nonneg (mul_nonneg (pow_nonneg hd _) hC)] at this
    exact this
  let K := (ε / 2) * (1 - d)
  have hK : 0 < K := mul_pos hhalf hden
  obtain ⟨U, hU⟩ := Metric.tendsto_atTop.mp hZ K hK
  refine ⟨U + N * h, ?_⟩
  intro u hu
  let v := u - N * h
  have hv : U ≤ v := by dsimp [v]; linarith
  have hrec' (n : ℕ) : E (v + (n + 1 : ℕ) * h) =
      d • E (v + n * h) + Z (v + n * h) := by
    have he : v + ((n + 1 : ℕ) : ℝ) * h = (v + n * h) + h := by
      push_cast
      ring
    rw [he, hrec]
  have hZ' (n : ℕ) : ‖Z (v + n * h)‖ ≤ K := by
    have harg : U ≤ v + n * h :=
      hv.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hh))
    simpa using (hU (v + n * h) harg).le
  have hb := stable_recurrence_const_bound
    (fun n : ℕ => E (v + n * h)) (fun n : ℕ => Z (v + n * h))
    d K C hd hd1 hK.le (by simpa using hbound v) hrec' hZ' N
  have he : v + (N : ℝ) * h = u := by dsimp [v]; ring
  have hKdiv : K / (1 - d) = ε / 2 := by
    dsimp [K]
    exact mul_div_cancel_right₀ _ hden.ne'
  rw [he, hKdiv] at hb
  simpa using hb.trans_lt (by linarith : d ^ N * C + ε / 2 < ε)

/-- Exponential decay is preserved under a positive real dilation. -/
theorem tendsto_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    Tendsto (fun u : ℝ => Real.exp (-c * u)) atTop (𝓝 0) := by
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop hc)
  simpa only [Function.comp_def, neg_mul] using ht

/-- A stable translation relation transfers the periodic profile to the original function. -/
theorem stable_translation_ray_limit
    (B Q P : ℝ → V) (d h C c : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hh : 0 < h) (hc : 0 < c) (hC : 0 ≤ C)
    (hP : Function.Periodic P h)
    (hlink : ∀ u, B (u + h) = d • B u + (1 - d) • Q u)
    (hprofile : ∀ u, ‖Q u - P u‖ ≤ C * Real.exp (-c * u)) :
    ∀ u, Tendsto (fun n : ℕ => B (u + n * h)) atTop (𝓝 (P u)) := by
  intro u
  let E : ℕ → V := fun n => B (u + n * h) - P u
  let Z : ℕ → V := fun n => (1 - d) • (Q (u + n * h) - P u)
  let r := Real.exp (-c * h)
  let K := (1 - d) * (C * Real.exp (-c * u))
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hK : 0 ≤ K := mul_nonneg (sub_nonneg.mpr hd1.le)
    (mul_nonneg hC (Real.exp_pos _).le)
  have hrec (n : ℕ) : E (n + 1) = d • E n + Z n := by
    dsimp [E, Z]
    have he : u + ((n + 1 : ℕ) : ℝ) * h = (u + n * h) + h := by
      push_cast
      ring
    rw [he, hlink]
    module
  have hZ (n : ℕ) : ‖Z n‖ ≤ K * r ^ n := by
    have hp := hprofile (u + n * h)
    rw [(hP.nat_mul n) u] at hp
    have he : -c * (u + n * h) = -c * u + (n : ℝ) * (-c * h) := by ring
    rw [he, Real.exp_add, Real.exp_nat_mul] at hp
    dsimp [Z, K, r]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hd1.le)]
    calc
      (1 - d) * ‖Q (u + n * h) - P u‖ ≤
          (1 - d) * (C * (Real.exp (-c * u) * Real.exp (-c * h) ^ n)) :=
        mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hd1.le)
      _ = _ := by ring
  have ht := stable_recurrence_tendsto_zero E Z d r K hd hd1 hr hr1 hK hrec hZ
  have ht' := ht.add_const (P u)
  simpa [E] using ht'

/-- Positive arithmetic rays in logarithmic time escape to infinity. -/
theorem tendsto_real_arithmetic_ray (u h : ℝ) (hh : 0 < h) :
    Tendsto (fun n : ℕ => u + n * h) atTop atTop :=
  tendsto_atTop_add_const_left _ u
    (Filter.Tendsto.atTop_mul_const hh
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

omit [NormedSpace ℝ V] in
/-- An asymptotic Lipschitz modulus passes to every arithmetic-ray profile. -/
theorem lipschitz_profile_of_asymptotic_modulus
    (B P : ℝ → V) (h L M : ℝ) (hh : 0 < h) (hL : 0 ≤ L)
    (hray : ∀ u, Tendsto (fun n : ℕ => B (u + n * h)) atTop (𝓝 (P u)))
    (hmod : ∀ u v, ‖B u - B v‖ ≤ L * |u - v| + M * Real.exp (-min u v)) :
    LipschitzWith ⟨L, hL⟩ P := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hleft := ((hray u).sub (hray v)).norm
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_real_arithmetic_ray (min u v) h hh)
  have hright : Tendsto
      (fun n : ℕ => L * |u - v| + M * Real.exp (-(min u v + n * h)))
      atTop (𝓝 (L * |u - v|)) := by
    simpa using (hexp.const_mul M).const_add (L * |u - v|)
  have hle : ‖P u - P v‖ ≤ L * |u - v| :=
    le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall (fun n => by
      simpa only [min_add_add_right, add_sub_add_right_eq_sub] using
        hmod (u + n * h) (v + n * h)))
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk] using hle

/-- A stable translation equation with exponential forcing has an explicit exponential bound. -/
theorem stable_translation_exp_bound
    (E Z : ℝ → V) (d h c η K CB : ℝ)
    (hd : 0 ≤ d) (hh : 0 < h) (hc : 0 < c) (hη : 0 < η)
    (hηc : η ≤ c) (hdρ : d < Real.exp (-η * h)) (hK : 0 ≤ K)
    (hbound : ∀ u, ‖E u‖ ≤ CB)
    (hrec : ∀ u, E (u + h) = d • E u + Z u)
    (hZ : ∀ u, ‖Z u‖ ≤ K * Real.exp (-c * u)) :
    ∀ u, 0 ≤ u → ‖E u‖ ≤
      (CB + K / (Real.exp (-η * h) - d)) * Real.exp (η * h) * Real.exp (-η * u) := by
  let ρ := Real.exp (-η * h)
  let r := Real.exp (-c * h)
  let A := CB + K / (ρ - d)
  have hden : 0 < ρ - d := sub_pos.mpr hdρ
  have hCB : 0 ≤ CB := (norm_nonneg (E 0)).trans (hbound 0)
  have hCBA : CB ≤ A := le_add_of_nonneg_right (div_nonneg hK hden.le)
  have hA0 : 0 ≤ A := hCB.trans hCBA
  have hKA : K ≤ A * (ρ - d) := by
    dsimp [A]
    rw [add_mul, div_mul_cancel₀ _ hden.ne']
    exact le_add_of_nonneg_left (mul_nonneg hCB hden.le)
  have hrρ : r ≤ ρ := Real.exp_le_exp.mpr (by nlinarith)
  intro u hu
  let n := Nat.floor (u / h)
  let v := u - n * h
  have hnfloor : (n : ℝ) ≤ u / h := Nat.floor_le (div_nonneg hu hh.le)
  have hnnext : u / h < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hv : 0 ≤ v := by
    dsimp [v]
    have := (le_div_iff₀ hh).mp hnfloor
    linarith
  have hvh : v < h := by
    dsimp [v]
    have := (div_lt_iff₀ hh).mp hnnext
    nlinarith
  have hrec' (j : ℕ) : E (v + (j + 1 : ℕ) * h) =
      d • E (v + j * h) + Z (v + j * h) := by
    have he : v + ((j + 1 : ℕ) : ℝ) * h = (v + j * h) + h := by
      push_cast
      ring
    rw [he, hrec]
  have hZ' (j : ℕ) : ‖Z (v + j * h)‖ ≤ K * r ^ j := by
    have he : -c * (v + j * h) = -c * v + (j : ℝ) * (-c * h) := by ring
    have he0 : Real.exp (-c * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      ‖Z (v + j * h)‖ ≤ K * Real.exp (-c * (v + j * h)) := hZ _
      _ = K * (Real.exp (-c * v) * r ^ j) := by
        rw [he, Real.exp_add, Real.exp_nat_mul]
      _ ≤ K * (1 * r ^ j) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right he0 (pow_nonneg (Real.exp_pos _).le _)) hK
      _ = K * r ^ j := by ring
  have hgeom := stable_recurrence_geometric_bound
    (fun j : ℕ => E (v + j * h)) (fun j : ℕ => Z (v + j * h))
    d r ρ K A hd (Real.exp_pos _).le hrρ (Real.exp_pos _).le hK
    (by simpa using (hbound v).trans hCBA) hKA hrec' hZ' n
  have he : v + (n : ℝ) * h = u := by dsimp [v]; ring
  rw [he] at hgeom
  have hpow : ρ ^ n ≤ Real.exp (η * h) * Real.exp (-η * u) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hvh' : u - (n : ℝ) * h < h := hvh
    nlinarith
  calc
    ‖E u‖ ≤ A * ρ ^ n := hgeom
    _ ≤ A * (Real.exp (η * h) * Real.exp (-η * u)) :=
      mul_le_mul_of_nonneg_left hpow hA0
    _ = _ := by dsimp [A, ρ]; ring

/-- Two independent dilation residuals force a bounded logarithmic-time mean to converge. -/
theorem exists_limit_of_two_scale_residuals_with_rate [CompleteSpace V]
    (B Q : ℝ → V) (d h b m C c CB L M : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hh : 0 < h) (hb : 1 < b)
    (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hirr : Irrational (h / m))
    (hbound : ∀ u, ‖B u‖ ≤ CB)
    (hmod : ∀ u v, ‖B u - B v‖ ≤ L * |u - v| + M * Real.exp (-min u v))
    (hlink : ∀ u, B (u + h) = d • B u + (1 - d) • Q u)
    (hfirst : ∀ u, ‖Q (u + h) - Q u‖ ≤ C * Real.exp (-c * u))
    (hsecond : Tendsto
      (fun u => b • B (u + 2 * m) - (b + 1) • B (u + m) + B u)
      atTop (𝓝 0)) :
    ∃ p : V, Tendsto B atTop (𝓝 p) ∧
      ∀ η : ℝ, 0 < η → η ≤ c → d < Real.exp (-η * h) →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u →
          ‖B u - p‖ ≤ K * Real.exp (-η * u) := by
  obtain ⟨P, hperiod, hQray, hprofile⟩ :=
    exists_periodic_profile_of_exp_shift Q h C c hh hc hfirst
  have hr1 : Real.exp (-c * h) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  let CP := C / (1 - Real.exp (-c * h))
  have hCP : 0 ≤ CP := div_nonneg hC (sub_nonneg.mpr hr1.le)
  have hprofile' (u : ℝ) : ‖Q u - P u‖ ≤ CP * Real.exp (-c * u) := by
    simpa [CP, div_mul_eq_mul_div] using hprofile u
  have hBray := stable_translation_ray_limit B Q P d h CP c
    hd hd1 hh hc hCP hperiod hlink hprofile'
  have hPbound (u : ℝ) : ‖P u‖ ≤ CB :=
    le_of_tendsto (hBray u).norm (Eventually.of_forall (fun n => hbound _))
  have hPcont : Continuous P :=
    (lipschitz_profile_of_asymptotic_modulus B P h L M hh hL hBray hmod).continuous
  have hPsecond (u : ℝ) :
      b • P (u + 2 * m) - (b + 1) • P (u + m) + P u = 0 := by
    have hleft := ((hBray (u + 2 * m)).const_smul b).sub
      ((hBray (u + m)).const_smul (b + 1)) |>.add (hBray u)
    have hright := hsecond.comp (tendsto_real_arithmetic_ray u h hh)
    have he : (fun n : ℕ => b • B ((u + 2 * m) + n * h) -
        (b + 1) • B ((u + m) + n * h) + B (u + n * h)) =
        (fun n : ℕ => b • B ((u + n * h) + 2 * m) -
        (b + 1) • B ((u + n * h) + m) + B (u + n * h)) := by
      funext n
      have he₁ : (u + 2 * m) + (n : ℝ) * h = (u + n * h) + 2 * m := by ring
      have he₂ : (u + m) + (n : ℝ) * h = (u + n * h) + m := by ring
      rw [he₁, he₂]
    rw [he] at hleft
    exact tendsto_nhds_unique hleft hright
  let D : ℝ → V := fun u => P (u + m) - P u
  have hDbound (u : ℝ) : ‖D u‖ ≤ 2 * CB :=
    (norm_sub_le _ _).trans (by linarith [hPbound (u + m), hPbound u])
  have hDrec (u : ℝ) : b • D (u + m) = D u := by
    have hs := hPsecond u
    have he : u + m + m = u + 2 * m := by ring
    dsimp [D]
    rw [he]
    calc
      b • (P (u + 2 * m) - P (u + m)) =
          (b • P (u + 2 * m) - (b + 1) • P (u + m) + P u) +
            (P (u + m) - P u) := by module
      _ = _ := by rw [hs, zero_add]
  have hDzero := bounded_expanding_recurrence_eq_zero D b m (2 * CB) hb hDbound hDrec
  have hperiod2 : Function.Periodic P m := fun u => sub_eq_zero.mp (hDzero u)
  have hconst := eq_const_of_continuous_two_periods P h m hPcont hperiod hperiod2 hirr
  have hQlimit : Tendsto (fun u => Q u - P 0) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (fun u => ?_)
    · simpa using (tendsto_exp_neg_mul c hc).const_mul CP
    · simpa only [hconst u, neg_mul] using hprofile' u
  let E : ℝ → V := fun u => B u - P 0
  let Z : ℝ → V := fun u => (1 - d) • (Q u - P 0)
  have hEbound (u : ℝ) : ‖E u‖ ≤ CB + ‖P 0‖ :=
    (norm_sub_le _ _).trans (add_le_add (hbound u) le_rfl)
  have hErec (u : ℝ) : E (u + h) = d • E u + Z u := by
    dsimp [E, Z]
    rw [hlink]
    module
  have hZlimit : Tendsto Z atTop (𝓝 0) := by
    simpa [Z] using hQlimit.const_smul (1 - d)
  have hElimit := stable_translation_tendsto_zero E Z d h (CB + ‖P 0‖)
    hd hd1 hh.le hEbound hErec hZlimit
  refine ⟨P 0, ?_, ?_⟩
  · simpa [E] using hElimit.add_const (P 0)
  · intro η hη hηc hdη
    let KZ := (1 - d) * CP
    have hKZ : 0 ≤ KZ := mul_nonneg (sub_nonneg.mpr hd1.le) hCP
    have hZbound (u : ℝ) : ‖Z u‖ ≤ KZ * Real.exp (-c * u) := by
      dsimp [Z, KZ]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hd1.le)]
      have hp := hprofile' u
      rw [hconst u] at hp
      exact (mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hd1.le)).trans_eq
        (mul_assoc _ _ _).symm
    let Kη := (CB + ‖P 0‖ + KZ / (Real.exp (-η * h) - d)) * Real.exp (η * h)
    have hKη : 0 ≤ Kη := mul_nonneg
      (add_nonneg ((norm_nonneg (E 0)).trans (hEbound 0))
        (div_nonneg hKZ (sub_nonneg.mpr hdη.le))) (Real.exp_pos _).le
    refine ⟨Kη, hKη, ?_⟩
    exact stable_translation_exp_bound E Z d h c η KZ (CB + ‖P 0‖)
      hd hh hc hη hηc hdη hKZ hEbound hErec hZbound

/-- Qualitative form of the two-scale theorem. -/
theorem exists_limit_of_two_scale_residuals [CompleteSpace V]
    (B Q : ℝ → V) (d h b m C c CB L M : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hh : 0 < h) (hb : 1 < b)
    (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hirr : Irrational (h / m))
    (hbound : ∀ u, ‖B u‖ ≤ CB)
    (hmod : ∀ u v, ‖B u - B v‖ ≤ L * |u - v| + M * Real.exp (-min u v))
    (hlink : ∀ u, B (u + h) = d • B u + (1 - d) • Q u)
    (hfirst : ∀ u, ‖Q (u + h) - Q u‖ ≤ C * Real.exp (-c * u))
    (hsecond : Tendsto
      (fun u => b • B (u + 2 * m) - (b + 1) • B (u + m) + B u)
      atTop (𝓝 0)) :
    ∃ p : V, Tendsto B atTop (𝓝 p) := by
  obtain ⟨p, hp, _⟩ := exists_limit_of_two_scale_residuals_with_rate B Q d h b m C c CB L M
    hd hd1 hh hb hc hC hL hirr hbound hmod hlink hfirst hsecond
  exact ⟨p, hp⟩

/-- The two-scale implication needs its quantitative hypotheses only on a terminal half-line. -/
theorem exists_limit_of_eventual_two_scale_residuals [CompleteSpace V]
    (B Q : ℝ → V) (d h b m C c CB L M U : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hh : 0 < h) (hb : 1 < b)
    (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hirr : Irrational (h / m))
    (hbound : ∀ u, U ≤ u → ‖B u‖ ≤ CB)
    (hmod : ∀ u v, U ≤ u → U ≤ v →
      ‖B u - B v‖ ≤ L * |u - v| + M * Real.exp (-min u v))
    (hlink : ∀ u, U ≤ u → B (u + h) = d • B u + (1 - d) • Q u)
    (hfirst : ∀ u, U ≤ u → ‖Q (u + h) - Q u‖ ≤ C * Real.exp (-c * u))
    (hsecond : Tendsto
      (fun u => b • B (u + 2 * m) - (b + 1) • B (u + m) + B u)
      atTop (𝓝 0)) :
    ∃ p : V, Tendsto B atTop (𝓝 p) ∧
      ∀ η : ℝ, 0 < η → η ≤ c → d < Real.exp (-η * h) →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ u : ℝ in atTop,
          ‖B u - p‖ ≤ K * Real.exp (-η * u) := by
  let Bt : ℝ → V := fun u => B (max u U)
  let Qt : ℝ → V := fun u => (1 - d)⁻¹ • (Bt (u + h) - d • Bt u)
  have hden : 0 < 1 - d := sub_pos.mpr hd1
  have hCB : 0 ≤ CB := (norm_nonneg (B U)).trans (hbound U le_rfl)
  have hBt (u : ℝ) (hu : U ≤ u) : Bt u = B u := by simp [Bt, max_eq_left hu]
  have hBtbound (u : ℝ) : ‖Bt u‖ ≤ CB := hbound _ (le_max_right _ _)
  have hQt (u : ℝ) (hu : U ≤ u) : Qt u = Q u := by
    dsimp [Qt]
    rw [hBt (u + h) (by linarith), hBt u hu, hlink u hu,
      add_sub_cancel_left, inv_smul_smul₀ hden.ne']
  have hBtlink (u : ℝ) : Bt (u + h) = d • Bt u + (1 - d) • Qt u := by
    dsimp [Qt]
    rw [smul_inv_smul₀ hden.ne']
    module
  let CQ := (1 - d)⁻¹ * (CB + d * CB)
  have hCQ : 0 ≤ CQ := mul_nonneg (inv_nonneg.mpr hden.le)
    (add_nonneg hCB (mul_nonneg hd hCB))
  have hQtbound (u : ℝ) : ‖Qt u‖ ≤ CQ := by
    dsimp [Qt, CQ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hden.le)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hden.le)
    calc
      ‖Bt (u + h) - d • Bt u‖ ≤ ‖Bt (u + h)‖ + ‖d • Bt u‖ := norm_sub_le _ _
      _ = ‖Bt (u + h)‖ + d * ‖Bt u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]
      _ ≤ CB + d * CB := add_le_add (hBtbound _) (mul_le_mul_of_nonneg_left (hBtbound _) hd)
  let Ct := max C (2 * CQ * Real.exp (c * U))
  have hCt : 0 ≤ Ct := hC.trans (le_max_left _ _)
  have hfirstt (u : ℝ) : ‖Qt (u + h) - Qt u‖ ≤ Ct * Real.exp (-c * u) := by
    by_cases hu : U ≤ u
    · rw [hQt u hu, hQt (u + h) (by linarith)]
      exact (hfirst u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · have hu' : u < U := lt_of_not_ge hu
      have he : 1 ≤ Real.exp (c * U) * Real.exp (-c * u) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        nlinarith
      calc
        ‖Qt (u + h) - Qt u‖ ≤ ‖Qt (u + h)‖ + ‖Qt u‖ := norm_sub_le _ _
        _ ≤ 2 * CQ := by linarith [hQtbound (u + h), hQtbound u]
        _ ≤ (2 * CQ * Real.exp (c * U)) * Real.exp (-c * u) := by
          have := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * CQ)
          nlinarith
        _ ≤ Ct * Real.exp (-c * u) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  have hmodt (u v : ℝ) :
      ‖Bt u - Bt v‖ ≤ L * |u - v| + M * Real.exp (-min u v) := by
    have he : Real.exp (-min (max u U) (max v U)) ≤ Real.exp (-min u v) :=
      Real.exp_le_exp.mpr (neg_le_neg (min_le_min (le_max_left _ _) (le_max_left _ _)))
    exact (hmod (max u U) (max v U) (le_max_right _ _) (le_max_right _ _)).trans
      (add_le_add (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs u v U) hL)
        (mul_le_mul_of_nonneg_left he hM))
  have hsecondt : Tendsto
      (fun u => b • Bt (u + 2 * m) - (b + 1) • Bt (u + m) + Bt u)
      atTop (𝓝 0) := by
    apply hsecond.congr'
    have h₁ := (tendsto_atTop_add_const_right atTop m tendsto_id).eventually
      (eventually_ge_atTop U)
    have h₂ := (tendsto_atTop_add_const_right atTop (2 * m) tendsto_id).eventually
      (eventually_ge_atTop U)
    filter_upwards [eventually_ge_atTop U, h₁, h₂] with u hu hu₁ hu₂
    rw [hBt u hu, hBt (u + m) hu₁, hBt (u + 2 * m) hu₂]
  obtain ⟨p, hp, hrate⟩ := exists_limit_of_two_scale_residuals_with_rate
    Bt Qt d h b m Ct c CB L M hd hd1 hh hb hc hCt hL hirr
    hBtbound hmodt hBtlink hfirstt hsecondt
  refine ⟨p, ?_, ?_⟩
  · apply hp.congr'
    filter_upwards [eventually_ge_atTop U] with u hu
    exact hBt u hu
  · intro η hη hηc hdη
    obtain ⟨K, hK, hKb⟩ := hrate η hη hηc hdη
    refine ⟨K, hK, ?_⟩
    filter_upwards [eventually_ge_atTop U, eventually_ge_atTop (0 : ℝ)] with u hu hu0
    simpa only [hBt u hu] using hKb u hu0

end CollatzCanonical.TwoScale
