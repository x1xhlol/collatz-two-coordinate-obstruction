import Erdos1135.ND.Fourier.FixedTotalAmbientAggregation
import Erdos1135.ND.Fourier.FixedSplitTailDFT
import Erdos1135.Tao.Section6.EventAggregation

/-!
# One-Time Raw Fixed-Total Event Replacement

This leaf compares the literal raw fixed-total residue vector with the checked
fixed-total local union.  The source is split before mapping, and the residual
fiber mass is dominated by rejection of the unweighted local-union gate.
Consequently the global failure event is charged exactly once.

No concentration rate, high-regime estimate, or endpoint normalization is
performed here.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Accepted target submass is monotone under source-gate inclusion. -/
private theorem nd_taoGatedSubmass_mono
    {α β : Type*} (p : PMF α) {E G : α → Prop} (f : α → β)
    (hEG : ∀ a, E a → G a) (y : β) :
    Tao.taoGatedSubmass p E f y ≤
      Tao.taoGatedSubmass p G f y := by
  unfold Tao.taoGatedSubmass
  apply ENNReal.toReal_mono
    ((Tao.taoGatedOptionPMF p G f).apply_ne_top (some y))
  rw [Tao.taoGatedOptionPMF_apply_some_eq_toOuterMeasure]
  rw [Tao.taoGatedOptionPMF_apply_some_eq_toOuterMeasure]
  apply p.toOuterMeasure.mono
  intro a ha
  exact ⟨hEG a ha.1, ha.2⟩

/-- A defective parent gate splits into its intersection with `G` and the
part of the same parent outside `G`. -/
private theorem nd_taoGatedSubmass_parent_split
    {α β : Type*} (p : PMF α) (E G : α → Prop)
    (f : α → β) (y : β) :
    Tao.taoGatedSubmass p E f y =
      Tao.taoGatedSubmass p (fun a => G a ∧ E a) f y +
        Tao.taoGatedSubmass p (fun a => ¬ G a ∧ E a) f y := by
  classical
  let H : Bool → α → Prop := fun b a =>
    if b then G a ∧ E a else ¬ G a ∧ E a
  have hdisjoint :
      ∀ i ∈ (Finset.univ : Finset Bool),
        ∀ j ∈ (Finset.univ : Finset Bool), i ≠ j →
          ∀ a, H i a → H j a → False := by
    intro i _hi j _hj hij a hia hja
    cases i <;> cases j
    · exact hij rfl
    · exact hia.1 hja.1
    · exact hja.1 hia.1
    · exact hij rfl
  have hunion :
      (fun a => ∃ b ∈ (Finset.univ : Finset Bool), H b a) = E := by
    funext a
    apply propext
    constructor
    · rintro ⟨b, _hb, hba⟩
      cases b <;> simpa [H] using hba.2
    · intro hEa
      by_cases hGa : G a
      · exact ⟨true, by simp [H, hGa, hEa]⟩
      · exact ⟨false, by simp [H, hGa, hEa]⟩
  have hpartition :=
    Tao.taoGatedSubmass_finset_union_eq_sum
      p (Finset.univ : Finset Bool) H f hdisjoint y
  rw [hunion] at hpartition
  simpa [H, add_comm] using hpartition

/-- Intersecting a defective parent with `G` changes its oscillation by at
most twice the rejection mass of `G` itself.  The rejected gate deliberately
does not contain the parent selector. -/
private theorem nd_taoZModPowOscillation_gated_le_inter_add_two_rejected
    {α : Type*} (p : PMF α) (E G : α → Prop)
    {m n : ℕ} (hmn : m ≤ n) (f : α → ZMod (3 ^ n)) :
    Tao.taoZModPowOscillation m n (Tao.taoGatedSubmass p E f) ≤
      Tao.taoZModPowOscillation m n
          (Tao.taoGatedSubmass p (fun a => G a ∧ E a) f) +
        2 * Tao.taoGatedRejectedMass p G f := by
  have hdiff :
      (∑ y : ZMod (3 ^ n),
        |Tao.taoGatedSubmass p E f y -
          Tao.taoGatedSubmass p (fun a => G a ∧ E a) f y|) ≤
        Tao.taoGatedRejectedMass p G f := by
    calc
      (∑ y : ZMod (3 ^ n),
          |Tao.taoGatedSubmass p E f y -
            Tao.taoGatedSubmass p (fun a => G a ∧ E a) f y|) =
        ∑ y : ZMod (3 ^ n),
          Tao.taoGatedSubmass p (fun a => ¬ G a ∧ E a) f y := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [nd_taoGatedSubmass_parent_split p E G f y]
        rw [add_sub_cancel_left]
        exact abs_of_nonneg
          (Tao.taoGatedSubmass_nonneg p
            (fun a => ¬ G a ∧ E a) f y)
      _ ≤ ∑ y : ZMod (3 ^ n),
          Tao.taoGatedSubmass p (fun a => ¬ G a) f y := by
        apply Finset.sum_le_sum
        intro y _hy
        exact nd_taoGatedSubmass_mono p f
          (E := fun a => ¬ G a ∧ E a)
          (G := fun a => ¬ G a)
          (fun _ ha => ha.1) y
      _ = Tao.taoGatedRejectedMass p G f :=
        Tao.taoGatedSubmass_complement_sum_eq_rejectedMass p G f
  calc
    Tao.taoZModPowOscillation m n (Tao.taoGatedSubmass p E f) ≤
        Tao.taoZModPowOscillation m n
            (Tao.taoGatedSubmass p (fun a => G a ∧ E a) f) +
          2 * ∑ y, |Tao.taoGatedSubmass p E f y -
            Tao.taoGatedSubmass p (fun a => G a ∧ E a) f y| :=
      Tao.taoZModPowOscillation_le_add_two_mul_sum_abs_sub hmn _ _
    _ ≤ Tao.taoZModPowOscillation m n
          (Tao.taoGatedSubmass p (fun a => G a ∧ E a) f) +
        2 * Tao.taoGatedRejectedMass p G f :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hdiff (by norm_num))

/-- The literal total-`L` raw vector is within one unconditional global
failure charge of the fixed-total local union. -/
theorem exists_ndSection6FixedTotalRawOscillation_le_localUnion_add_globalFailure
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ n : ℕ, N0 ≤ n → ∀ L m : ℕ, m ≤ n →
        Tao.taoZModPowOscillation m n
            (ndSection6FixedSplitTailSubmass 0 n 0 L) ≤
          Tao.taoZModPowOscillation m n
              (ndSection6FixedTotalLocalUnionSubmass CA n L) +
            2 * Tao.taoSection6GlobalFailureMass CA n := by
  obtain ⟨Nevent, hsubset⟩ :=
    Tao.exists_taoSection6GlobalTypical_subset_localUnionGate CA hCA
  refine ⟨max Nevent 2, le_max_right _ _, ?_⟩
  intro n hn L m hmn
  have hnEvent : Nevent ≤ n := (le_max_left _ _).trans hn
  let p := Tao.geom2PNatListPMF n
  let E : List ℕ+ → Prop := fun full => Tao.taoTupleWeight full = L
  let G : List ℕ+ → Prop := Tao.taoSection6LocalUnionGate CA n
  let f := Tao.taoSection7OffsetZMod n
  have hraw :
      ndSection6FixedSplitTailSubmass 0 n 0 L =
        Tao.taoGatedSubmass p E f := by
    funext y
    exact ndSection6FixedSplitTailSubmass_zero_head_zero_weight_eq_gatedSubmass
      n L y
  have hbridge :=
    nd_taoZModPowOscillation_gated_le_inter_add_two_rejected
      p E G hmn f
  have hrejected :
      Tao.taoGatedRejectedMass p G f ≤
        Tao.taoGatedRejectedMass p
          (Tao.taoSection6GlobalTypical CA n) f := by
    exact Tao.taoGatedRejectedMass_mono p f (hsubset n hnEvent)
  rw [hraw]
  calc
    Tao.taoZModPowOscillation m n (Tao.taoGatedSubmass p E f) ≤
        Tao.taoZModPowOscillation m n
            (Tao.taoGatedSubmass p (fun a => G a ∧ E a) f) +
          2 * Tao.taoGatedRejectedMass p G f := hbridge
    _ = Tao.taoZModPowOscillation m n
          (ndSection6FixedTotalLocalUnionSubmass CA n L) +
        2 * Tao.taoGatedRejectedMass p G f := rfl
    _ ≤ Tao.taoZModPowOscillation m n
          (ndSection6FixedTotalLocalUnionSubmass CA n L) +
        2 * Tao.taoGatedRejectedMass p
          (Tao.taoSection6GlobalTypical CA n) f := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hrejected (by norm_num))
    _ = Tao.taoZModPowOscillation m n
          (ndSection6FixedTotalLocalUnionSubmass CA n L) +
        2 * Tao.taoSection6GlobalFailureMass CA n := by
      rw [Tao.taoSection6GlobalFailureMass_eq_rejectedMass]

end

end ND
end Erdos1135
