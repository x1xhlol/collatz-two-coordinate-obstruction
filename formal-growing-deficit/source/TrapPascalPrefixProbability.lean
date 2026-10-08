import TrapPMFEventTransport
import Erdos1135.Tao.Probability.Geom2PrefixTypical
import Erdos1135.Tao.Fourier.Section7SourcePairing

/-! Raw Pascal prefix concentration through its exact paired Geom(2) law. -/

set_option autoImplicit false

namespace Erdos1135.Tao
open CollatzResearch

def TrapPascalPrefixGood (J : ℕ) (D : ℝ) (bs : List ℕ) : Prop :=
  ∀ j ≤ J, |(((bs.take j).sum : ℕ) : ℝ) - 4 * (j : ℝ)| ≤ D

theorem trap_pairSums_take_sum
    (as : List ℕ+) (j : ℕ) (hj : 2 * j ≤ as.length) :
    ((taoSection7PairSums as).take j).sum = taoTupleWeight (as.take (2 * j)) := by
  induction j generalizing as with
  | zero => simp [taoTupleWeight]
  | succ j ih =>
      cases as with
      | nil => simp at hj
      | cons a as =>
          cases as with
          | nil => simp at hj; omega
          | cons b as =>
              have htail : 2 * j ≤ as.length := by simp at hj; omega
              rw [show 2 * (j + 1) = 2 * j + 2 by omega]
              simp only [taoSection7PairSums_cons_cons, List.take_succ_cons,
                List.sum_cons]
              rw [ih as htail]
              simp [taoTupleWeight]
              omega

theorem trap_pascal_good_of_geom_prefix_good
    (J : ℕ) (D : ℝ) (hD : 0 ≤ D) (as : List ℕ+) (hlen : as.length = 2 * J)
    (hgood : as ∉ taoGeom2PrefixBadEvent D (2 * J)) :
    TrapPascalPrefixGood J D (taoSection7PairSums as) := by
  intro j hj
  by_cases hj0 : j = 0
  · simpa [hj0] using hD
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hjlen : 2 * j ≤ as.length := by omega
  have hprefix : |taoGeom2CenteredListWeight (as.take (2 * j))| ≤ D := by
    by_contra hnot
    apply hgood
    refine ⟨⟨2 * j - 1, by omega⟩, ?_⟩
    simpa [show 2 * j - 1 + 1 = 2 * j by omega] using (lt_of_not_ge hnot)
  rw [trap_pairSums_take_sum as j hjlen]
  simpa only [taoGeom2CenteredListWeight, List.length_take, min_eq_left hjlen,
    Nat.cast_mul, Nat.cast_ofNat, show (2 : ℝ) * (2 * (j : ℝ)) = 4 * (j : ℝ) by ring]
    using hprefix

theorem trap_pascal_bad_prefix_probability_le
    (J : ℕ) (hJ : 0 < J) (D : ℝ) (hD : 0 < D) :
    trapPMFEvent (taoSection7PascalSourceListPMF J)
        (fun bs => ¬ TrapPascalPrefixGood J D bs) ≤
      ((2 * J : ℕ) : ℝ) * (2 * Real.exp
        (-min (D ^ 2 / (32 * ((2 * J : ℕ) : ℝ))) (D / 8))) := by
  rw [← geom2PNatListPMF_map_pairSums_eq_pascalSourceListPMF J, trap_pmf_event_map]
  have hcover : trapPMFEvent (geom2PNatListPMF (2 * J))
      (fun as => ¬ TrapPascalPrefixGood J D (taoSection7PairSums as)) ≤
      trapPMFEvent (geom2PNatListPMF (2 * J))
        (fun as => as ∈ taoGeom2PrefixBadEvent D (2 * J)) := by
    apply trap_pmf_event_mono_on_support
    intro as hmass hbad
    have hlen : as.length = 2 * J := by
      by_contra hne
      rw [geom2PNatListPMF_apply_eq_zero_of_length_ne (2 * J) as hne] at hmass
      exact hmass rfl
    by_contra hgood
    exact hbad (trap_pascal_good_of_geom_prefix_good J D hD.le as hlen hgood)
  apply hcover.trans
  rw [trap_pmf_event_eq_outerMeasure]
  exact geom2PNatListPMF_prefixBad_le_nat_mul (by omega) hD

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_pascal_bad_prefix_probability_le
