import TrapNativeQualitativeReduction
import TrapOriginalStartTail

/-! Splitting a few-white event into atypical paths and many canonical stops. -/

set_option autoImplicit false

open scoped BigOperators

namespace CollatzResearch

theorem trap_pmf_event_le_add_of_cover {α : Type*}
    (p : PMF α) (E B F : α → Prop) (hcover : ∀ x, E x → B x ∨ F x) :
    trapPMFEvent p E ≤ trapPMFEvent p B + trapPMFEvent p F := by
  classical
  let indicator := fun (S : α → Prop) x => if S x then (1 : ℝ) else 0
  have hsum : ∀ S, Summable fun x => (p x).toReal * indicator S x := by
    intro S
    apply trap_pmf_expectation_summable
    · intro x
      dsimp only [indicator]
      split_ifs <;> norm_num
    · intro x
      dsimp only [indicator]
      split_ifs <;> norm_num
  change (∑' x, (p x).toReal * indicator E x) ≤
    (∑' x, (p x).toReal * indicator B x) + (∑' x, (p x).toReal * indicator F x)
  rw [← (hsum B).tsum_add (hsum F)]
  apply (hsum E).tsum_le_tsum _ ((hsum B).add (hsum F))
  intro x
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  by_cases hx : E x
  · obtain hb | hf := hcover x hx
    · simp [indicator, hx, hb]
      split_ifs <;> norm_num
    · simp [indicator, hx, hf]
      split_ifs <;> norm_num
  · simp [indicator, hx]
    split_ifs <;> norm_num

end CollatzResearch

namespace Erdos1135.Tao

open CollatzResearch

theorem trap_native_few_white_le_bad_add_stops
    (n J R T : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (family : Set TaoSection7Triangle) (Good : List TaoSection7RenewalPoint → Prop)
    (hexclusion : ∀ hs, Good hs →
      trapHoldListWhiteCount
        (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J)) hs ≤ T →
      trapOriginalStartFewWhiteEvent n (n / 2) J R T xi epsilon family hs)
    (hstops : trapPMFEvent (taoSection7HoldListPMF (n / 2 + 1))
      (trapOriginalStartFewWhiteEvent n (n / 2) J R T xi epsilon family) ≤
      Real.exp ((T : ℝ) + epsilon - epsilon * (R : ℝ))) :
    trapNativeFewWhiteProbability n J T xi epsilon ≤
      trapPMFEvent (taoSection7HoldListPMF (n / 2 + 1)) (fun hs => ¬ Good hs) +
        Real.exp ((T : ℝ) + epsilon - epsilon * (R : ℝ)) := by
  classical
  apply le_trans (trap_pmf_event_le_add_of_cover _ _ (fun hs => ¬ Good hs)
    (trapOriginalStartFewWhiteEvent n (n / 2) J R T xi epsilon family) ?_)
    (add_le_add le_rfl hstops)
  intro hs hwhite
  by_cases hgood : Good hs
  · exact Or.inr (hexclusion hs hgood hwhite)
  · exact Or.inl hgood

end Erdos1135.Tao

#print axioms CollatzResearch.trap_pmf_event_le_add_of_cover
#print axioms Erdos1135.Tao.trap_native_few_white_le_bad_add_stops
