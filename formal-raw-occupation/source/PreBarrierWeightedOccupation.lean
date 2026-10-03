import FiniteSyracuseClockConfinement
import ShortcutOddEndpoints
import ActualUnconditionalGreen

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.RawOccupation
open Erdos1135 CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao CollatzClockAudit

theorem firstHitWeight_self (q : ℕ) : firstHitWeight q q = 1 := by
  have hfirst : FirstHit q q 0 := ⟨rfl, by simp⟩
  rw [firstHitWeight_eq_pathWeight hfirst]
  simp [pathWeight, pathCorrection]

theorem syracuse_first_passage_prefix_injective {M : ℝ} {q T : ℕ}
    (hT : Tao.syracuseFirstHitAtMostReal M q T) :
    Set.InjOn (fun i => (Tao.syracuse^[i]) q) (Finset.range (T + 1)) := by
  have hstrict (i j : ℕ) (hj : j ≤ T) (hij : i < j)
      (he : (Tao.syracuse^[i]) q = (Tao.syracuse^[j]) q) : False := by
    have h := congrArg (Tao.syracuse^[T - j]) he
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      Nat.sub_add_cancel hj] at h
    have hpre := hT.2 (T - j + i) (by omega)
    rw [h] at hpre
    exact not_lt_of_ge hT.1 hpre
  intro i hi j hj he
  have hi' : i ≤ T := by simpa using hi
  have hj' : j ≤ T := by simpa using hj
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (hstrict i j hj' hij he)
  · exact hij
  · exact False.elim (hstrict j i hi' hij he.symm)

/-- The uniform correction error applies to every first visit before a
successful barrier passage, including all of the remote source prefix. -/
theorem exists_uniform_preBarrier_firstHitWeight_lower (theta : ℝ)
    (htheta : CollatzCanonical.PackingParameters.beta < theta) (htheta1 : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : ℝ}, 1 ≤ M → ∀ {q T i : ℕ}, Odd q →
      Tao.syracuseFirstHitAtMostReal M q T → i < T →
      max 0 (1 - C * M ^ (theta - 1)) ≤ firstHitWeight ((Tao.syracuse^[i]) q) q := by
  obtain ⟨C, hC, htransport⟩ := firstHitWeight_uniform_prefix_transport theta htheta htheta1
  refine ⟨C, hC, ?_⟩
  intro M hM q T i hq hT hiT
  let A := Tao.taoTupleWeight (Tao.syracuseValuationPNatList i q hq)
  let B := Tao.taoTupleWeight (Tao.syracuseValuationPNatList T q hq)
  have hAB : A < B := syracuse_clock_strictMono q hq hiT
  have hpass := native_real_first_passage_is_oddBarrier (zero_le_one.trans hM) hq hT
  change OddBarrierPassage q B M at hpass
  have hinj : Set.InjOn (fun k => iterate k q) (Finset.range A) := by
    apply hpass.prefix_injective.mono
    intro k hk
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans hAB)
  have havoid : ∀ k < A, iterate k q ≠ (Tao.syracuse^[i]) q := by
    intro k hk he
    have hland : iterate A q = (Tao.syracuse^[i]) q := syracuse_shortcut_landing i q hq
    have hki := hpass.prefix_injective
      (Finset.mem_range.mpr (hk.trans hAB)) (Finset.mem_range.mpr hAB) (he.trans hland.symm)
    omega
  have hw := htransport A q ((Tao.syracuse^[i]) q) hq.pos havoid hinj M hM
    (fun k hk ho => (hpass.prefix_high k (hk.trans hAB) ho).le)
  rw [show iterate A q = (Tao.syracuse^[i]) q from syracuse_shortcut_landing i q hq,
    firstHitWeight_self] at hw
  exact max_le (firstHitWeight_bounds _ _).1 (by linarith [(abs_le.mp hw).1])

noncomputable def oddTargetOccupation (R q : ℕ) : ℝ :=
  ∑ N ∈ (Finset.range (R + 1)).filter Odd, firstHitWeight N q

theorem oddTargetOccupation_nonneg (R q : ℕ) : 0 ≤ oddTargetOccupation R q :=
  Finset.sum_nonneg (fun N _ => (firstHitWeight_bounds N q).1)

theorem preBarrier_occupation_lower {M B : ℝ} {R q a T : ℕ}
    (hq : Odd q) (hT : Tao.syracuseFirstHitAtMostReal M q T)
    (hweight : ∀ i < T, B ≤ firstHitWeight ((Tao.syracuse^[i]) q) q)
    (hheight : ∀ i, a ≤ i → i < T → (Tao.syracuse^[i]) q ≤ R) :
    ((T - a : ℕ) : ℝ) * B ≤ oddTargetOccupation R q := by
  classical
  let I := Finset.Ico a T
  let Q := I.image (fun i => (Tao.syracuse^[i]) q)
  have hsub : Q ⊆ (Finset.range (R + 1)).filter Odd := by
    intro N hN
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hN
    have hi' := Finset.mem_Ico.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have hh := hheight i hi'.1 hi'.2
      omega), Tao.syracuse_iterate_odd i q hq⟩
  have hinj : Set.InjOn (fun i => (Tao.syracuse^[i]) q) I := by
    apply (syracuse_first_passage_prefix_injective hT).mono
    intro i hi
    exact Finset.mem_range.mpr (by have := (Finset.mem_Ico.mp hi).2; omega)
  calc
    ((T - a : ℕ) : ℝ) * B = ∑ i ∈ I, B := by simp [I]
    _ ≤ ∑ i ∈ I, firstHitWeight ((Tao.syracuse^[i]) q) q :=
      Finset.sum_le_sum (fun i hi => hweight i (Finset.mem_Ico.mp hi).2)
    _ = ∑ N ∈ Q, firstHitWeight N q := by
      symm
      apply Finset.sum_image
      exact hinj
    _ ≤ oddTargetOccupation R q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun N _ _ => (firstHitWeight_bounds N q).1)

/-- This is a finite occupation lower bound with explicit clock and height
budgets, before any source mean or asymptotic interchange. -/
theorem exists_finite_clock_grid_occupation_lower (theta : ℝ)
    (htheta : CollatzCanonical.PackingParameters.beta < theta) (htheta1 : theta < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℕ → ℝ) (t : ℕ → ℕ)
      {M E : ℝ} {R q T n : ℕ}, 1 ≤ M → Odd q →
      (∀ i < n, x (i + 1) ≤ x i) →
      (∀ i ≤ n, M ≤ x i) →
      (∀ i ≤ n, Tao.syracuseFirstHitAtMostReal (x i) q (t i)) →
      Tao.syracuseFirstHitAtMostReal M q T →
      (∀ i ≤ n, |((T - t i : ℕ) : ℝ) - Real.log (x i) / clockDrift| ≤ E) →
      (∀ i < n,
        (3 / 2 : ℝ) ^ ((Real.log (x i) - Real.log (x (i + 1))) / clockDrift + 2 * E) *
          (x i + 1) ≤ (R : ℝ) + 1) →
      (3 / 2 : ℝ) ^ (Real.log (x n) / clockDrift + E) * (x n + 1) ≤ (R : ℝ) + 1 →
      max 0 (1 - C * M ^ (theta - 1)) * (Real.log (x 0) / clockDrift - E) ≤
        oddTargetOccupation R q := by
  obtain ⟨C, hC, hweight⟩ := exists_uniform_preBarrier_firstHitWeight_lower theta htheta htheta1
  refine ⟨C, hC, ?_⟩
  intro x t M E R q T n hM hq hdown hbottom hfirst hT hclock hstage hlast
  have hheight := finite_clock_grid_confinement x t hq hdown hbottom hfirst hT hclock hstage hlast
  have hocc := preBarrier_occupation_lower hq hT (fun i hi => hweight hM hq hT hi)
    (fun i hi hiT => by exact_mod_cast hheight i hi hiT)
  have hcount : Real.log (x 0) / clockDrift - E ≤ ((T - t 0 : ℕ) : ℝ) := by
    linarith [(abs_le.mp (hclock 0 (Nat.zero_le n))).1]
  exact (mul_le_mul_of_nonneg_left hcount (le_max_left 0 _)).trans
    (by simpa only [mul_comm] using hocc)

#print axioms exists_uniform_preBarrier_firstHitWeight_lower
#print axioms preBarrier_occupation_lower
#print axioms exists_finite_clock_grid_occupation_lower

end CollatzCanonical.RawOccupation
