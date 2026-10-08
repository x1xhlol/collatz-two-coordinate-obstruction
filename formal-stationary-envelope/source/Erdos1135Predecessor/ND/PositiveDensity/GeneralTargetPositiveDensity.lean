/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.GeneralTargetPredecessorCount
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitNumericalSyracuseMixing

namespace Erdos1135Predecessor.ND.PositiveDensity
noncomputable section

theorem generalTarget_predecessors_positive_lower_density
    {a : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a) :
    ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      c * (X : ℝ) ≤ (Terras.natCount (ordinaryPredecessorSet a) X : ℝ) := by
  let b : ℕ := 2 ^ 80
  let C : ℕ := explicitSyracuseMixingCoefficient
  let N := explicitLogarithmicSeedGeneration b C
  let Nmark := explicitLogarithmicGoodMarkedStart b C N
  have hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ) := explicitSyracuseMixing_six
  obtain ⟨r, hr, hl, ht, hnonreturn, _hunit, hgood⟩ :=
    exists_generalTarget_uniform_twoThirds_seed ha hthree (b := b) le_rfl C hmix
      (N := N) le_rfl
  have hb200 : 200 ≤ b := by dsimp [b]; norm_num
  let U := ndRootCoreSingletonState b r hb200 hr hl
  let cap := fun j : ℕ => 16 + j / 100
  have he : U.rootSpan 0 := by intro i j; change r ≤ 2 ^ 0 * r; simp
  have hcap : ∀ j, cap j ≤ 17 * (j + 1) := by
    intro j
    have hj := Nat.div_le_self j 100
    dsimp [cap]
    omega
  have hreach : ∀ i, Erdos1135Predecessor.Reaches (U.state.root i) a := fun _ => ht
  have hseed : ∀ i k, 0 < k → (Tao.syracuse^[k]) (U.state.root i) ≠ U.state.root i :=
    fun _ => hnonreturn
  have hP : U.parentSourcePotential = (r : ℝ) := by
    change ndGeom2PredictableRootSideParentSourcePotential (Finset.univ : Finset Unit)
      (fun _ => (1 : ℝ)) (fun _ => r) = _
    simp [ndGeom2PredictableRootSideParentSourcePotential]
  have hPpos : 0 < U.parentSourcePotential := by rw [hP]; exact_mod_cast hr.pos
  let m : ℕ := 132 * r * C + 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmdef : (m : ℝ) = 132 * (r : ℝ) * (C : ℝ) + 1 := by
    dsimp [m]
    push_cast
    ring
  have hsquare : 88 * U.parentSourcePotential * (C : ℝ) ≤ (2 / 3 : ℝ) * (m : ℝ) ^ 2 := by
    rw [hP]
    nlinarith [sq_nonneg ((m : ℝ) - 1)]
  have hquadratic : ndExplicitQuadraticMixingAt (C : ℝ) m :=
    explicitMixing_quadratic (Nat.cast_nonneg C) hmix hm
  let J := Nmark + 2 * m + 20 * 10 ^ 9
  let H := ndExplicitRootIntervalHeight b 17 r J
  let eta : ℝ := 9 * (2 / 3 : ℝ) / (16 * ((3 ^ m : ℕ) : ℝ))
  have heta : 0 < eta := by dsimp [eta]; positivity
  refine ⟨eta / (32 * U.parentSourcePotential), by positivity, 32 * (H + 1), ?_⟩
  apply U.generalTarget_publicCount_from_mass a hreach hseed cap he hcap hPpos J H
    (by dsimp [J]; omega)
    (fun i => U.iterate_physicalIntervalMax_le_explicit cap 17 r hcap (fun _ => le_rfl) J i)
  intro n hn V X hX hi
  have hroom := U.explicitConductor_quarter_room cap m n (by dsimp [J] at hn; omega)
  exact U.fullGoodCoreTerminalMass_ge_of_square_budget_and_height_of_nonreturningSeed
    cap ndRootCoreWidth n (cap n) m ((U.forwardIterate cap n).floor / 4)
    hm hroom.1 hroom.2 hseed (Nat.cast_nonneg C) hquadratic (by norm_num)
    hsquare (3 ^ m) (by positivity) (unitReferenceDensity_finite_upper m)
    X hX hi (hgood n (by dsimp [J] at hn; omega) X hX hi)

end
end Erdos1135Predecessor.ND.PositiveDensity
