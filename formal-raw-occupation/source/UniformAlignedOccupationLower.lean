import AlignedLadderOccupation
import FixedLadderGoodCumulative
import FiniteOccupationEventLower
import FailureEnvelopeMonotonicity

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.RawOccupation
open Erdos1135.Tao CollatzClockAudit
open CollatzCanonical.DirichletAbelian CollatzCanonical.NativeTao

theorem fixed_ladder_good_bottom {M : ℝ} (hM : 1 ≤ M) {q : TaoOddNat}
    (hq : q ∈ fixedLadderGoodEvent M hM 0) : syracuseHitsAtMostReal q.1 M := by
  obtain ⟨j, _, hj⟩ := hq
  obtain ⟨t, ht, _⟩ := global_clock_good_first_hit hM j q hj
  exact ⟨t, ht.1⟩

/-- The scalar lower expression is clipped only because occupation itself is
nonnegative; every clock and packing error remains explicit. -/
noncomputable def finiteOccupationLowerValue (P theta M : ℝ) (R B : ℕ) (x : ℝ) : ℝ :=
  max 0 (max 0 (1 - P * M ^ (theta - 1)) *
    (Real.log x / clockDrift - commonBottomClockError M R B))

theorem finite_occupation_density_lower_from_ladders
    {P theta C c M : ℝ} {B R n : ℕ} (x : ℕ → ℝ)
    (hC : 0 ≤ C) (hc : 0 < c) (hM : 1 < M) (hMe : Real.exp 1 ≤ M)
    (hfacts : ∀ m : ℝ, M ≤ m → ∀ i : ℕ, RealClockScaleFacts C c (clockScale m i))
    (hMB : M ^ taoAlpha ≤ (B : ℝ))
    (hbot : ∀ i ≤ n, M ≤ x i)
    (hocc : ∀ q : TaoOddNat,
      (∀ i ≤ n, AlignedClockWitness M (x i) B q) → syracuseHitsAtMostReal q.1 M →
      max 0 (1 - P * M ^ (theta - 1)) *
        (Real.log (x 0) / clockDrift - commonBottomClockError M R B) ≤
          oddTargetOccupation R q.1) :
    finiteOccupationLowerValue P theta M R B (x 0) *
      (1 - 2 * (n + 2 : ℕ) * clockLadderFailureEnvelope C c M * taoAlpha) ≤
        oddTargetDensitySum R := by
  classical
  let y := fun i : ℕ => if i ≤ n then x i else M
  have hy : ∀ i, M ≤ y i := by
    intro i
    dsimp only [y]
    split_ifs with hi
    · exact hbot i hi
    · exact le_rfl
  choose m r hbase hupper halign using fun i => exists_aligned_clock_base hM (hy i)
  have hm (i : ℕ) : 1 < m i := hM.trans_le (hbase i)
  have hmB (i : ℕ) : m i ≤ (B : ℝ) := (hupper i).le.trans hMB
  let G : ℕ → Set TaoOddNat := fun i =>
    if i = 0 then fixedLadderGoodEvent M hM.le 0
    else fixedLadderGoodEvent (m (i - 1)) (hm (i - 1)).le (r (i - 1))
  let d : ℕ → ℝ := fun _ => clockLadderFailureEnvelope C c M * taoAlpha
  have hgood : ∀ q : TaoOddNat, (∀ i ∈ Finset.range (n + 2), q ∈ G i) →
      finiteOccupationLowerValue P theta M R B (x 0) ≤ oddTargetOccupation R q.1 := by
    intro q hq
    have hbottom : syracuseHitsAtMostReal q.1 M := by
      apply fixed_ladder_good_bottom hM.le
      simpa only [G, if_pos rfl] using hq 0 (Finset.mem_range.mpr (by omega))
    apply max_le (oddTargetOccupation_nonneg R q.1)
    apply hocc q _ hbottom
    intro i hi
    have hgi : q ∈ fixedLadderGoodEvent (m i) (hm i).le (r i) := by
      simpa only [G, Nat.add_sub_cancel, if_neg (show i + 1 ≠ 0 by omega)] using
        hq (i + 1) (Finset.mem_range.mpr (by omega))
    obtain ⟨j, hrj, hj⟩ := hgi
    refine ⟨m i, (hm i).le, j, r i, hbase i, hmB i, ?_, hrj, hj⟩
    simpa only [y, if_pos hi] using halign i
  have hbad : ∀ i ∈ Finset.range (n + 2), ∃ A : ℝ, ∀ᶠ t : ℝ in atTop,
      oddLogarithmicCumulative (oddEventWeight (G i)ᶜ) t ≤ A + d i * t := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simpa only [G, if_pos rfl, d] using
        fixedLadderGoodEvent_failure_cumulative_envelope hC hc hM hMe (hfacts M le_rfl) 0
    · obtain ⟨A, hA⟩ := fixedLadderGoodEvent_failure_cumulative_envelope hC hc
        (hm (i - 1)) (hMe.trans (hbase (i - 1)))
        (hfacts (m (i - 1)) (hbase (i - 1))) (r (i - 1))
      refine ⟨A, ?_⟩
      filter_upwards [hA, eventually_ge_atTop (0 : ℝ)] with t ht ht0
      have he := clock_failure_envelope_antitone hC hc hM (hbase (i - 1))
      have hs := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right he taoAlpha_pos.le) ht0
      change oddLogarithmicCumulative
        (oddEventWeight (if i = 0 then _ else _)ᶜ) t ≤ A + d i * t
      rw [if_neg hi0]
      change oddLogarithmicCumulative
        (oddEventWeight (fixedLadderGoodEvent (m (i - 1)) (hm (i - 1)).le (r (i - 1)))ᶜ) t ≤
          A + clockLadderFailureEnvelope C c M * taoAlpha * t
      linarith
  have h := finite_occupation_density_lower_of_bad_envelopes (Finset.range (n + 2)) G d
    (le_max_left 0 _) hgood hbad
  convert h using 1
  simp only [finiteOccupationLowerValue, d, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The native probability constants and all common-source bad-event bounds
are discharged. The remaining inputs are explicit finite height budgets. -/
theorem exists_uniform_finite_occupation_density_lower (theta : ℝ)
    (htheta : CollatzCanonical.PackingParameters.beta < theta) (htheta1 : theta < 1) :
    ∃ P C c M₀ : ℝ, 0 ≤ P ∧ 0 ≤ C ∧ 0 < c ∧ Real.exp 1 ≤ M₀ ∧
      ∀ (M : ℝ), M₀ ≤ M → ∀ (x : ℕ → ℝ) (R n : ℕ),
      (∀ i < n, x (i + 1) ≤ x i) →
      (∀ i ≤ n, M ≤ x i) → (∀ i ≤ n, x i ≤ (R : ℝ)) →
      (∀ i < n,
        (3 / 2 : ℝ) ^ ((Real.log (x i) - Real.log (x (i + 1))) / clockDrift +
          2 * commonBottomClockError M R ⌈M ^ taoAlpha⌉₊) *
            (x i + 1) ≤ (R : ℝ) + 1) →
      (3 / 2 : ℝ) ^ (Real.log (x n) / clockDrift + commonBottomClockError M R ⌈M ^ taoAlpha⌉₊) *
        (x n + 1) ≤ (R : ℝ) + 1 →
      finiteOccupationLowerValue P theta M R ⌈M ^ taoAlpha⌉₊ (x 0) *
        (1 - 2 * (n + 2 : ℕ) * clockLadderFailureEnvelope C c M * taoAlpha) ≤
          oddTargetDensitySum R := by
  obtain ⟨P, hP, hocc⟩ := exists_aligned_ladder_occupation_lower theta htheta htheta1
  obtain ⟨C, c, M₁, hC, hc, _, hfacts⟩ := exists_clock_scale_uniform_cutoff
  refine ⟨P, C, c, max M₁ (Real.exp 1), hP, hC, hc, le_max_right _ _, ?_⟩
  intro M hM x R n hdown hbot htop hstage hlast
  have hMe : Real.exp 1 ≤ M := (le_max_right _ _).trans hM
  have hM1 : 1 < M := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hMe
  apply finite_occupation_density_lower_from_ladders x hC hc hM1 hMe
    (fun m hm => hfacts m ((le_max_left _ _).trans (hM.trans hm)))
    (Nat.le_ceil _) hbot
  intro q hw hbottom
  exact hocc x q hM1.le hdown hbot htop hw hbottom hstage hlast

#print axioms fixed_ladder_good_bottom
#print axioms finite_occupation_density_lower_from_ladders
#print axioms exists_uniform_finite_occupation_density_lower

end CollatzCanonical.RawOccupation
