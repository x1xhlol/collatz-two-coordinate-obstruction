import TrapGoodPathFromTube
import TrapFewWhiteEventReduction
import TrapCanonicalStoppedWhiteTail

/-! Concrete good paths give the actual original-start event and its native probability bound. -/

set_option autoImplicit false
open CollatzResearch

namespace Erdos1135.Tao

theorem eventually_good_hold_list_few_white_event
    (R T : ℕ) (hRpos : 0 < R) (epsilon theta : ℝ)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon : epsilon < 1 / 4)
    (htheta : Real.log 3 < 2 * theta * Real.log 2)
    (H : ℕ → ℕ) (V D : ℕ → ℝ)
    (hV0 : ∀ n, 0 ≤ V n) (hD0 : ∀ n, 0 ≤ D n)
    (hH : TrapSublinearUpper (fun n => (H n : ℝ)))
    (hV : TrapSublinearUpper V) (hD : TrapSublinearUpper D) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ J : ℕ, 2 * J ≤ n → theta * (n : ℝ) ≤ (2 * J : ℕ) →
      ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
      ∀ family : Set TaoSection7Triangle,
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family →
      ∀ hs : List TaoSection7RenewalPoint, trapHoldListGood n J (H n) (V n) (D n) hs →
      trapHoldListWhiteCount
        (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteWCutoff n xi epsilon J)) hs ≤ T →
      trapOriginalStartFewWhiteEvent n (n / 2) J R T xi epsilon family hs := by
  obtain ⟨N, hN⟩ := eventually_good_hold_path_has_many_stops_of_tube R T hRpos
    epsilon theta hepsilon0 hepsilon htheta H V D hV0 hD0 hH hV hD
  refine ⟨N, ?_⟩
  intro n hn J hnJ hthetaJ xi hxi family hcover hs hgood hcount
  cases hs with
  | nil => exact hgood.elim
  | cons start full =>
      obtain ⟨hlen, hpath⟩ := hgood
      obtain ⟨t, ht, hj⟩ := hN n hn J hnJ hthetaJ xi hxi start full family
        hlen hcover hpath hcount
      exact ⟨hlen, t, ht, hj, hcount⟩

theorem eventually_native_few_white_le_bad_good_path_add_stops
    (parameters : TrapRenewalParameters) (R T : ℕ) (hRpos : 0 < R) (theta : ℝ)
    (htheta : Real.log 3 < 2 * theta * Real.log 2)
    (H : ℕ → ℕ) (V D : ℕ → ℝ)
    (hV0 : ∀ n, 0 ≤ V n) (hD0 : ∀ n, 0 ≤ D n)
    (hH : TrapSublinearUpper (fun n => (H n : ℝ)))
    (hV : TrapSublinearUpper V) (hD : TrapSublinearUpper D) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ J : ℕ, 2 * J ≤ n → theta * (n : ℝ) ≤ (2 * J : ℕ) →
      ∀ xi : ZMod (3 ^ n), zmodThreePrimitive n xi →
      trapNativeFewWhiteProbability n J T xi parameters.epsilon ≤
        trapPMFEvent (taoSection7HoldListPMF (n / 2 + 1))
          (fun hs => ¬ trapHoldListGood n J (H n) (V n) (D n) hs) +
        Real.exp ((T : ℝ) + parameters.epsilon - parameters.epsilon * (R : ℝ)) := by
  have hepsilon : parameters.epsilon < 1 / 4 :=
    parameters.scalar.epsilon_lt_one_hundredth.trans (by norm_num)
  obtain ⟨N, hN⟩ := eventually_good_hold_list_few_white_event R T hRpos
    parameters.epsilon theta parameters.scalar.epsilon_pos.le hepsilon htheta
    H V D hV0 hD0 hH hV hD
  refine ⟨N, ?_⟩
  intro n hn J hnJ hthetaJ xi hxi
  exact trap_native_few_white_le_bad_add_stops n J R T xi parameters.epsilon
    (taoSection7CanonicalTriangleFamily hxi parameters.scalar)
    (trapHoldListGood n J (H n) (V n) (D n))
    (hN n hn J hnJ hthetaJ xi hxi _
      (taoSection7CanonicalTriangleFamily_cover hxi parameters.scalar))
    (trap_canonical_original_start_few_white_le parameters n J R T xi hxi)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.eventually_good_hold_list_few_white_event
#print axioms Erdos1135.Tao.eventually_native_few_white_le_bad_good_path_add_stops
