import BoundedFrozenSeed
import ArbitraryPowerMixingBudget
import Erdos1135Predecessor.ND.PositiveDensity.GeneralTargetPositiveDensity

/-
The seed/count assembly below adapts the argument in the imported
GeneralTargetPositiveDensity source attributed there to Lech Mazur. It retains
an arbitrary terminal mixing power and the new bounded inverse seed.
-/

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed
open Erdos1135Predecessor
open Erdos1135Predecessor.ND.PositiveDensity

/-- The terminal census works at any positive conductor depth satisfying the
terminal power budget, independently of the fixed sixth-power seed estimate. -/
theorem generalTarget_predecessors_seed_lower_density_at_power
    {a b C N : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a) (hb : 2 ^ 80 ≤ b)
    (hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ))
    (hN : explicitLogarithmicSeedGeneration b C ≤ N)
    {p : ℕ} {Cp : ℝ} (hCp : 0 ≤ Cp)
    (hmixp : Tao.syracFineScaleMixingAt p Cp)
    (depth : ℕ → ℕ) (hdepth : ∀ r, 1 ≤ depth r)
    (hbudget : ∀ r : ℕ, 88 * (r : ℝ) * Cp ≤ ((depth r : ℕ) : ℝ) ^ p) :
    ∃ r : ℕ, 0 < r ∧
      r ≤ frozenSeedHeightMultiplier b (explicitSeedFloor b N / 4) N * a ∧
      ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
        (3 / (256 * (r : ℝ) * ((3 ^ depth r : ℕ) : ℝ))) * (X : ℝ) ≤
          (Terras.natCount (ordinaryPredecessorSet a) X : ℝ) := by
  let Nmark := explicitLogarithmicGoodMarkedStart b C N
  obtain ⟨r, hr, hl, ht, hbound, hnonreturn, _hunit, hgood⟩ :=
    exists_bounded_generalTarget_uniform_twoThirds_seed ha hthree hb C hmix hN
  have hb200 : 200 ≤ b := (by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb
  let U := ndRootCoreSingletonState b r hb200 hr hl
  let cap := fun j : ℕ => 16 + j / 100
  have he : U.rootSpan 0 := by intro i j; change r ≤ 2 ^ 0 * r; simp
  have hcap : ∀ j, cap j ≤ 17 * (j + 1) := by
    intro j
    have hj := Nat.div_le_self j 100
    dsimp [cap]
    omega
  have hreach : ∀ i, Reaches (U.state.root i) a := fun _ => ht
  have hseed : ∀ i k, 0 < k → (Tao.syracuse^[k]) (U.state.root i) ≠ U.state.root i :=
    fun _ => hnonreturn
  have hP : U.parentSourcePotential = (r : ℝ) := by
    change ndGeom2PredictableRootSideParentSourcePotential (Finset.univ : Finset Unit)
      (fun _ => (1 : ℝ)) (fun _ => r) = _
    simp [ndGeom2PredictableRootSideParentSourcePotential]
  have hPpos : 0 < U.parentSourcePotential := by rw [hP]; exact_mod_cast hr.pos
  let m : ℕ := depth r
  have hm : 1 ≤ m := hdepth r
  let Ceff : ℝ := (2 / 3 : ℝ) * Cp * (m : ℝ) ^ 2 / (m : ℝ) ^ p
  have hCeff : 0 ≤ Ceff := by dsimp [Ceff]; positivity
  have hquadratic : ndExplicitQuadraticMixingAt Ceff m :=
    power_mixing_as_quadratic hmixp hm
  have hsquare : 88 * U.parentSourcePotential * Ceff ≤ (2 / 3 : ℝ) * (m : ℝ) ^ 2 := by
    rw [hP]
    exact power_mixing_square_budget hm (hbudget r)
  let J := Nmark + 2 * m + 20 * 10 ^ 9
  let H := ndExplicitRootIntervalHeight b 17 r J
  let eta : ℝ := 9 * (2 / 3 : ℝ) / (16 * ((3 ^ m : ℕ) : ℝ))
  have hcount : ∀ X : ℕ, 32 * (H + 1) ≤ X →
      eta / (32 * U.parentSourcePotential) * (X : ℝ) ≤
        (Terras.natCount (ordinaryPredecessorSet a) X : ℝ) := by
    apply U.generalTarget_publicCount_from_mass a hreach hseed cap he hcap hPpos J H
      (by dsimp [J]; omega)
      (fun i => U.iterate_physicalIntervalMax_le_explicit cap 17 r hcap (fun _ => le_rfl) J i)
    intro n hn V X hX hi
    have hroom := U.explicitConductor_quarter_room cap m n (by dsimp [J] at hn; omega)
    exact U.fullGoodCoreTerminalMass_ge_of_square_budget_and_height_of_nonreturningSeed
      cap ndRootCoreWidth n (cap n) m ((U.forwardIterate cap n).floor / 4)
      hm hroom.1 hroom.2 hseed hCeff hquadratic (by norm_num)
      hsquare (3 ^ m) (by positivity) (unitReferenceDensity_finite_upper m)
      X hX hi (hgood n (by dsimp [J] at hn; omega) X hX hi)
  have hconstant : eta / (32 * U.parentSourcePotential) =
      3 / (256 * (r : ℝ) * ((3 ^ m : ℕ) : ℝ)) := by
    rw [hP]
    dsimp [eta]
    ring
  refine ⟨r, hr.pos, hbound, 32 * (H + 1), ?_⟩
  intro X hX
  simpa only [hconstant] using hcount X hX


#print axioms generalTarget_predecessors_seed_lower_density_at_power

end CollatzCanonical.BoundedInverseSeed
