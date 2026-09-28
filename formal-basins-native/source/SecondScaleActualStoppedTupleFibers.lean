import SecondScalePositiveValuationWordCount
import Erdos1135SecondScale.Tao.Syracuse.FirstPassageInterval

set_option autoImplicit false
open scoped BigOperators

namespace CollatzPassageAtomsSecondScale
open Erdos1135SecondScale.Tao

noncomputable def stoppedValuationWord (τ : ℕ → ℕ) (q : ℕ) : List ℕ := by
  classical
  exact if hq : Odd q then (syracuseValuationPNatList (τ q) q hq).map PNat.val else []

theorem stoppedValuationWord_pos (τ : ℕ → ℕ) (q a : ℕ)
    (ha : a ∈ stoppedValuationWord τ q) : 0 < a := by
  classical
  unfold stoppedValuationWord at ha
  split_ifs at ha with hq
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact b.pos
  · simp at ha

theorem stoppedValuationWord_weight (τ : ℕ → ℕ) {q : ℕ} (hq : Odd q) :
    (stoppedValuationWord τ q).sum = taoTupleWeight (syracuseValuationPNatList (τ q) q hq) := by
  simp [stoppedValuationWord, hq, taoTupleWeight, List.map_eq_flatMap]

theorem taoAffList_injective (as : List ℕ+) : Function.Injective (taoAffList as) := by
  intro x y h
  rw [taoAffList_closed, taoAffList_closed] at h
  have hc : (3 : ℚ) ^ as.length / (2 : ℚ) ^ taoTupleWeight as ≠ 0 := by positivity
  exact mul_left_cancel₀ hc (add_right_cancel h)

/-- A stopped valuation tuple and its endpoint determine the actual odd start,
without requiring a common stopping time. -/
theorem stopped_tuple_endpoint_injective (τ : ℕ → ℕ) {q r : ℕ}
    (hq : Odd q) (hr : Odd r)
    (hword : stoppedValuationWord τ q = stoppedValuationWord τ r)
    (hend : (syracuse^[τ q]) q = (syracuse^[τ r]) r) : q = r := by
  classical
  have hm : (syracuseValuationPNatList (τ q) q hq).map PNat.val =
      (syracuseValuationPNatList (τ r) r hr).map PNat.val := by
    simpa only [stoppedValuationWord, dif_pos hq, dif_pos hr] using hword
  have hw : syracuseValuationPNatList (τ q) q hq = syracuseValuationPNatList (τ r) r hr :=
    (List.map_inj_right (fun _ _ he => PNat.coe_injective he)).mp hm
  have hp := syracuse_iterate_eq_taoAffList (τ q) q hq
  have hs := syracuse_iterate_eq_taoAffList (τ r) r hr
  rw [hw] at hp
  have hh : taoAffList (syracuseValuationPNatList (τ r) r hr) (q : ℚ) =
      taoAffList (syracuseValuationPNatList (τ r) r hr) (r : ℚ) := by
    rw [← hp, ← hs, hend]
  exact_mod_cast taoAffList_injective _ hh

theorem actual_stopped_endpoint_card_le (s : Finset ℕ) (τ : ℕ → ℕ) (L m : ℕ)
    (hodd : ∀ q ∈ s, Odd q)
    (hcost : ∀ q ∈ s, (stoppedValuationWord τ q).sum ≤ L)
    (hend : ∀ q ∈ s, (syracuse^[τ q]) q = m) : s.card ≤ 2 ^ L := by
  apply finite_source_fiber_card_le s (stoppedValuationWord τ) L
    (fun q _ a ha => stoppedValuationWord_pos τ q a ha) hcost
  intro q hq r hr hword
  exact stopped_tuple_endpoint_injective τ (hodd q hq) (hodd r hr) hword
    ((hend q hq).trans (hend r hr).symm)

theorem actual_stopped_endpoint_mass_le (s : Finset ℕ) (τ : ℕ → ℕ) (L m : ℕ)
    (hodd : ∀ q ∈ s, Odd q)
    (hcost : ∀ q ∈ s, (stoppedValuationWord τ q).sum ≤ L)
    (hend : ∀ q ∈ s, (syracuse^[τ q]) q = m)
    (p : ℕ → ℝ) {pmax : ℝ} (hpmax : 0 ≤ pmax)
    (hp : ∀ q ∈ s, p q ≤ pmax) : (∑ q ∈ s, p q) ≤ (2 : ℝ) ^ L * pmax := by
  have hc := actual_stopped_endpoint_card_le s τ L m hodd hcost hend
  have hs := Finset.sum_le_card_nsmul s p pmax hp
  rw [nsmul_eq_mul] at hs
  have hcr : (s.card : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hc
  exact hs.trans (mul_le_mul_of_nonneg_right hcr hpmax)

end CollatzPassageAtomsSecondScale
