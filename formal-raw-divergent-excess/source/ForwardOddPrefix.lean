import DivergentPostBarrierOccupation
import ComponentWholeOrbitWeight

set_option autoImplicit false
open scoped BigOperators

namespace CollatzCanonical.RawOccupation
open Erdos1135 CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao CollatzCanonical.ForwardComponent

theorem syracuse_injective_of_shortcut_injective {u : ℕ} (hu : Odd u)
    (hinj : Function.Injective (fun i => iterate i u)) :
    Function.Injective (fun i => (Tao.syracuse^[i]) u) := by
  intro i j he
  apply (syracuse_clock_strictMono u hu).injective
  apply hinj
  simpa only [syracuse_shortcut_landing] using he

theorem forward_firstHitWeight_ge_wholeOrbit_inverse {u : ℕ} (hu : 0 < u)
    (hinj : Function.Injective (fun i => iterate i u)) (j : ℕ) :
    (wholeOrbitCorrection u)⁻¹ ≤ firstHitWeight (iterate j u) u := by
  have hfirst : FirstHit u (iterate j u) j := by
    refine ⟨rfl, ?_⟩
    intro i hi he
    exact (Nat.ne_of_lt hi) (hinj he)
  have htail : Function.Injective (fun i => iterate i (iterate j u)) :=
    shortcut_component_injective ⟨0, j, rfl⟩ hinj
  have hone := wholeOrbitCorrection_one_le
    (CollatzCanonical.Correction.iterate_pos j hu) htail
  have hfactor := wholeOrbitCorrection_at_hit hu hinj (rfl : iterate j u = iterate j u)
  have hpath : 0 < pathCorrection j u := lt_of_lt_of_le (by norm_num)
    (one_le_pathCorrection j u)
  have hle : pathCorrection j u ≤ wholeOrbitCorrection u := by nlinarith
  rw [firstHitWeight_eq_pathWeight hfirst, pathWeight]
  exact inv_anti₀ hpath hle

noncomputable def oddForwardPrefix (u J : ℕ) : Finset ℕ :=
  (Finset.range J).image (fun j => (Tao.syracuse^[j]) u)

theorem oddForwardPrefix_card {u : ℕ} (hu : Odd u)
    (hinj : Function.Injective (fun i => iterate i u)) (J : ℕ) :
    (oddForwardPrefix u J).card = J := by
  rw [oddForwardPrefix, Finset.card_image_of_injective _
    (syracuse_injective_of_shortcut_injective hu hinj), Finset.card_range]

theorem oddForwardPrefix_mem_properties {u R J : ℕ} (hu : Odd u)
    (hbudget : (3 / 2 : ℝ) ^ J * ((u : ℝ) + 1) ≤ (R : ℝ) + 1) :
    ∀ N ∈ oddForwardPrefix u J, Odd N ∧ N ≤ R ∧ ∃ j, iterate j u = N := by
  intro N hN
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hN
  have hjJ : j ≤ J := (Finset.mem_range.mp hj).le
  have hg := syracuse_iterate_add_one_growth hu j
  have hp : (3 / 2 : ℝ) ^ j ≤ (3 / 2 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2) hjJ
  have hR : ((Tao.syracuse^[j]) u : ℝ) ≤ (R : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ u + 1)
    linarith
  exact ⟨Tao.syracuse_iterate_odd j u hu, by exact_mod_cast hR,
    ⟨Tao.taoTupleWeight (Tao.syracuseValuationPNatList j u hu),
      syracuse_shortcut_landing j u hu⟩⟩

theorem oddForwardPrefix_weight_sum_lower {u : ℕ} (hu : Odd u)
    (hinj : Function.Injective (fun i => iterate i u)) (J : ℕ) :
    (J : ℝ) / wholeOrbitCorrection u ≤
      ∑ N ∈ oddForwardPrefix u J, firstHitWeight N u := by
  have hi := syracuse_injective_of_shortcut_injective hu hinj
  calc
    (J : ℝ) / wholeOrbitCorrection u =
        ∑ j ∈ Finset.range J, (wholeOrbitCorrection u)⁻¹ := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ j ∈ Finset.range J, firstHitWeight ((Tao.syracuse^[j]) u) u := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [syracuse_shortcut_landing] using
        forward_firstHitWeight_ge_wholeOrbit_inverse hu.pos hinj
          (Tao.taoTupleWeight (Tao.syracuseValuationPNatList j u hu))
    _ = ∑ N ∈ oddForwardPrefix u J, firstHitWeight N u := by
      symm
      exact Finset.sum_image (fun i _ j _ he => hi he)

#print axioms syracuse_injective_of_shortcut_injective
#print axioms forward_firstHitWeight_ge_wholeOrbit_inverse
#print axioms oddForwardPrefix_card
#print axioms oddForwardPrefix_mem_properties
#print axioms oddForwardPrefix_weight_sum_lower

end CollatzCanonical.RawOccupation
