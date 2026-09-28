import OrbitPackingFiniteRecurrence
import FiniteBinomialTail
import DyadicPowerBounds

/-! The displayed power recurrence, derived for actual finite distinct trajectories. -/

set_option autoImplicit false

namespace CollatzOrbitPackingActualRecurrence

open CollatzCylinderPacking CollatzOrbitPackingFiniteRecurrence
open CollatzOrbitPackingPowerRecurrence

/-- The recurrence has no counting or entropy assumptions: its hypotheses
are the distinctness of the finite actual trajectory and the chosen numerical
parameters. -/
theorem prefixCount_power_recurrence (N L X : ℕ)
    (hinj : Set.InjOn (fun i => iterate i N) (Finset.range L))
    (hX : 1 ≤ X) (ρ b c : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1)
    (hb : 0 ≤ b)
    (hentropy : b = (-ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ)) / Real.log 2)
    (hc : c = ρ * Real.log 3 / Real.log 2) :
    (prefixCount N L X : ℝ) ≤ (prefixCount N L (packingNext c X) : ℝ) +
      2 * (X : ℝ) ^ b + (binaryLogFloor X : ℝ) := by
  let h := binaryLogFloor X
  let m := Nat.floor (ρ * h)
  have hρ0 : 0 ≤ ρ := by linarith
  have hρh : 0 ≤ ρ * h := mul_nonneg hρ0 (Nat.cast_nonneg _)
  have hdyad := CollatzCanonical.DyadicBounds.binaryLogFloor_bounds X hX
  have hrec := finite_counting_recurrence N L X h m hinj hdyad.2
  have hthree : (3 : ℝ) ^ m ≤ (X : ℝ) ^ c := by
    rw [hc]
    exact CollatzCanonical.DyadicBounds.three_power_le_nat_power X m ρ hX hρ0
      (Nat.floor_le hρh)
  have hnext : 3 * 3 ^ m ≤ packingNext c X := by
    apply Nat.le_floor
    have hh := mul_le_mul_of_nonneg_left hthree (by norm_num : (0 : ℝ) ≤ 3)
    exact_mod_cast hh
  have hcount := prefixCount_mono N L hnext
  have hcountR : (prefixCount N L (3 * 3 ^ m) : ℝ) ≤
      (prefixCount N L (packingNext c X) : ℝ) := by exact_mod_cast hcount
  have hfilter : (Finset.range (h + 1)).filter (fun j => m < j) =
      (Finset.range (h + 1)).filter (fun j : ℕ => ρ * h < (j : ℝ)) := by
    apply Finset.filter_congr
    intro j _
    exact Nat.floor_lt hρh
  have htail : (∑ j ∈ (Finset.range (h + 1)).filter (fun j => m < j),
      (h.choose j : ℝ)) ≤ (X : ℝ) ^ b := by
    rw [hfilter]
    have he := CollatzCanonical.BinomialTail.binary_entropy_binomial_tail h ρ hρ hρ1
    rw [← hentropy] at he
    exact he.trans (CollatzCanonical.DyadicBounds.two_power_le_nat_power X b hX hb)
  have hrecR : (prefixCount N L X : ℝ) ≤ (prefixCount N L (3 * 3 ^ m) : ℝ) +
      2 * (∑ j ∈ (Finset.range (h + 1)).filter (fun j => m < j), (h.choose j : ℝ)) +
      (h : ℝ) := by exact_mod_cast hrec
  change (prefixCount N L X : ℝ) ≤ (prefixCount N L (packingNext c X) : ℝ) +
    2 * (X : ℝ) ^ b + (h : ℝ)
  linarith

/-- A single constant works for every finite distinct positive shortcut
trajectory once admissible entropy parameters have been chosen. -/
theorem uniform_finite_distinct_packing_of_parameters
    (ρ b c : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hb : 0 < b) (hc1 : c < 1)
    (hentropy : b = (-ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ)) / Real.log 2)
    (hc : c = ρ * Real.log 3 / Real.log 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N L X : ℕ, 0 < N →
      Set.InjOn (fun i => iterate i N) (Finset.range L) →
      (prefixCount N L X : ℝ) ≤ K * (X : ℝ) ^ b := by
  let ι := {p : ℕ × ℕ // 0 < p.1 ∧
    Set.InjOn (fun i => iterate i p.1) (Finset.range p.2)}
  let A : ι → ℕ → ℝ := fun p X => prefixCount p.val.1 p.val.2 X
  have hcount : ∀ p X, A p X ≤ (X : ℝ) := by
    intro p X
    change (prefixCount p.val.1 p.val.2 X : ℝ) ≤ (X : ℝ)
    exact_mod_cast prefixCount_le p.val.1 p.val.2 X p.property.1 p.property.2
  have hrec : ∀ p X, 1 ≤ X →
      A p X ≤ A p (packingNext c X) + 2 * (X : ℝ) ^ b + (binaryLogFloor X : ℝ) := by
    intro p X hX
    exact prefixCount_power_recurrence p.val.1 p.val.2 X p.property.2 hX
      ρ b c hρ hρ1 hb.le hentropy hc
  obtain ⟨K, hK, hbound⟩ :=
    uniform_power_bound_of_packing_recurrence A b c hb hc1 hcount hrec
  refine ⟨K, hK, ?_⟩
  intro N L X hN hinj
  exact hbound ⟨(N, L), hN, hinj⟩ X

#print axioms prefixCount_power_recurrence
#print axioms uniform_finite_distinct_packing_of_parameters

end CollatzOrbitPackingActualRecurrence
