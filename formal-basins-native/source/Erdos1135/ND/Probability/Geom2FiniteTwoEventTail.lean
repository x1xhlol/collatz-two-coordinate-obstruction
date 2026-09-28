import Erdos1135.Tao.Probability.FullL1
import Erdos1135.Tao.Probability.Geom2CenteredMoment
import Erdos1135.Tao.Probability.Geom2ListProjectivity

/-!
# Finite two-event tails for Geom(2) lists

This ND-local probability leaf bounds a finite exact-length carrier that is
covered by a full-list upper event and a predecessor-prefix lower event.  It
keeps the two event charges separate, so no additional union factor appears.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

private theorem pmfOuterMass_toReal_mono
    {α : Type*} (p : PMF α) {A D : Set α} (hAD : A ⊆ D) :
    (p.toOuterMeasure A).toReal ≤ (p.toOuterMeasure D).toReal := by
  have hfinite : p.toOuterMeasure D ≠ ⊤ := by
    apply ne_of_lt
    calc
      p.toOuterMeasure D ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ D)
      _ = 1 := (p.toOuterMeasure_apply_eq_one_iff Set.univ).2
        (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  exact ENNReal.toReal_mono hfinite (p.toOuterMeasure.mono hAD)

/-- Taking the first `r` entries of a length-`m` iid Geom(2) list transports
arbitrary event mass exactly to the length-`r` law. -/
theorem geom2PNatListPMF_take_event_outerMeasure_toReal
    {r m : ℕ} (hrm : r ≤ m) (A : Set (List ℕ+)) :
    ((Tao.geom2PNatListPMF m).toOuterMeasure
      ((fun bs => bs.take r) ⁻¹' A)).toReal =
    ((Tao.geom2PNatListPMF r).toOuterMeasure A).toReal := by
  rw [← Tao.geom2PNatListPMF_map_take_low_eq_of_le hrm]
  rw [PMF.toOuterMeasure_map_apply]

/-- A finite exact-length subcarrier inside an event has at most the ambient
Geom(2) event mass. -/
theorem sum_geom2PNatListMass_le_eventMass
    {m : ℕ} (S : Finset (List ℕ+)) (A : Set (List ℕ+))
    (hlen : ∀ bs ∈ S, bs.length = m)
    (hA : ∀ bs ∈ S, bs ∈ A) :
    (∑ bs ∈ S, Tao.geom2PNatListMass bs) ≤
      ((Tao.geom2PNatListPMF m).toOuterMeasure A).toReal := by
  classical
  let f : List ℕ+ → ℝ := fun bs =>
    A.indicator
      (fun cs => (Tao.geom2PNatListPMF m cs).toReal) bs
  have hf : Summable f :=
    (Tao.taoPMF_summable_toReal
      (Tao.geom2PNatListPMF m)).indicator A
  calc
    (∑ bs ∈ S, Tao.geom2PNatListMass bs) =
        ∑ bs ∈ S, f bs := by
      apply Finset.sum_congr rfl
      intro bs hbs
      dsimp only [f]
      rw [Set.indicator_of_mem (hA bs hbs)]
      have hmass := Tao.geom2PNatListPMF_apply_length_toReal bs
      rw [hlen bs hbs] at hmass
      exact hmass.symm
    _ ≤ ∑' bs : List ℕ+, f bs :=
      hf.sum_le_tsum S (fun bs _hbs => by
        dsimp only [f]
        by_cases hmem : bs ∈ A
        · simp only [Set.indicator_of_mem hmem]
          exact ENNReal.toReal_nonneg
        · simp only [Set.indicator_of_notMem hmem]
          exact le_rfl)
    _ = ((Tao.geom2PNatListPMF m).toOuterMeasure A).toReal := by
      rw [Tao.pmfOuterMass_toReal_eq_tsum_indicator]

/-- A finite exact-length carrier covered by a full centered upper tail or a
`dropLast` centered lower tail is charged by the two corresponding iid event
masses.  Each displayed factor two comes only from the checked absolute-tail
bound; there is no further union factor. -/
theorem sum_geom2PNatListMass_le_centeredUpper_add_dropLastLower_min
    {m : ℕ} (hm : 2 ≤ m) (S : Finset (List ℕ+)) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v)
    (hlen : ∀ bs ∈ S, bs.length = m)
    (htail : ∀ bs ∈ S,
      u < Tao.taoGeom2CenteredListWeight bs ∨
        Tao.taoGeom2CenteredListWeight bs.dropLast < -v) :
    (∑ bs ∈ S, Tao.geom2PNatListMass bs) ≤
      2 * Real.exp (-min (u ^ 2 / (32 * (m : ℝ))) (u / 8)) +
      2 * Real.exp
        (-min (v ^ 2 / (32 * ((m - 1 : ℕ) : ℝ))) (v / 8)) := by
  classical
  let upper : List ℕ+ → Prop := fun bs =>
    u < Tao.taoGeom2CenteredListWeight bs
  let upperEvent : Set (List ℕ+) :=
    {bs | u < Tao.taoGeom2CenteredListWeight bs}
  let upperAbsEvent : Set (List ℕ+) :=
    {bs | u < |Tao.taoGeom2CenteredListWeight bs|}
  let prefixLowerEvent : Set (List ℕ+) :=
    {pre | Tao.taoGeom2CenteredListWeight pre < -v}
  let prefixAbsEvent : Set (List ℕ+) :=
    {pre | v < |Tao.taoGeom2CenteredListWeight pre|}
  let takeLowerEvent : Set (List ℕ+) :=
    (fun bs => bs.take (m - 1)) ⁻¹' prefixLowerEvent
  have hsplit :
      (∑ bs ∈ S, Tao.geom2PNatListMass bs) =
        (∑ bs ∈ S.filter upper, Tao.geom2PNatListMass bs) +
          ∑ bs ∈ S.filter (fun bs => ¬ upper bs),
            Tao.geom2PNatListMass bs := by
    exact (Finset.sum_filter_add_sum_filter_not S upper
      Tao.geom2PNatListMass).symm
  have hupperMass :
      (∑ bs ∈ S.filter upper, Tao.geom2PNatListMass bs) ≤
        2 * Real.exp (-min (u ^ 2 / (32 * (m : ℝ))) (u / 8)) := by
    have hcarrier :
        (∑ bs ∈ S.filter upper, Tao.geom2PNatListMass bs) ≤
          ((Tao.geom2PNatListPMF m).toOuterMeasure upperEvent).toReal := by
      apply sum_geom2PNatListMass_le_eventMass
      · intro bs hbs
        exact hlen bs (Finset.mem_filter.mp hbs).1
      · intro bs hbs
        exact (Finset.mem_filter.mp hbs).2
    have hmono :
        ((Tao.geom2PNatListPMF m).toOuterMeasure upperEvent).toReal ≤
          ((Tao.geom2PNatListPMF m).toOuterMeasure upperAbsEvent).toReal := by
      apply pmfOuterMass_toReal_mono
      intro bs hbs
      change u < Tao.taoGeom2CenteredListWeight bs at hbs
      change u < |Tao.taoGeom2CenteredListWeight bs|
      exact lt_abs.mpr (Or.inl hbs)
    have hbernstein :
        ((Tao.geom2PNatListPMF m).toOuterMeasure upperAbsEvent).toReal ≤
          2 * Real.exp
            (-min (u ^ 2 / (32 * (m : ℝ))) (u / 8)) := by
      simpa only [upperAbsEvent] using
        Tao.geom2PNatListPMF_centeredWeight_absTail_le_min
          (show 0 < m by omega) hu
    exact hcarrier.trans (hmono.trans hbernstein)
  have hlowerMass :
      (∑ bs ∈ S.filter (fun bs => ¬ upper bs),
          Tao.geom2PNatListMass bs) ≤
        2 * Real.exp
          (-min (v ^ 2 / (32 * ((m - 1 : ℕ) : ℝ))) (v / 8)) := by
    have hcarrier :
        (∑ bs ∈ S.filter (fun bs => ¬ upper bs),
            Tao.geom2PNatListMass bs) ≤
          ((Tao.geom2PNatListPMF m).toOuterMeasure takeLowerEvent).toReal := by
      apply sum_geom2PNatListMass_le_eventMass
      · intro bs hbs
        exact hlen bs (Finset.mem_filter.mp hbs).1
      · intro bs hbs
        rcases Finset.mem_filter.mp hbs with ⟨hbsS, hnotUpper⟩
        rcases htail bs hbsS with hupper | hlower
        · exact (hnotUpper hupper).elim
        · change Tao.taoGeom2CenteredListWeight (bs.take (m - 1)) < -v
          have hdrop : bs.dropLast = bs.take (m - 1) := by
            rw [List.dropLast_eq_take, hlen bs hbsS]
          rw [← hdrop]
          exact hlower
    have hproject :
        ((Tao.geom2PNatListPMF m).toOuterMeasure takeLowerEvent).toReal =
          ((Tao.geom2PNatListPMF (m - 1)).toOuterMeasure
            prefixLowerEvent).toReal := by
      simpa only [takeLowerEvent] using
        geom2PNatListPMF_take_event_outerMeasure_toReal
          (Nat.sub_le m 1) prefixLowerEvent
    have hmono :
        ((Tao.geom2PNatListPMF (m - 1)).toOuterMeasure
            prefixLowerEvent).toReal ≤
          ((Tao.geom2PNatListPMF (m - 1)).toOuterMeasure
            prefixAbsEvent).toReal := by
      apply pmfOuterMass_toReal_mono
      intro pre hpre
      change Tao.taoGeom2CenteredListWeight pre < -v at hpre
      change v < |Tao.taoGeom2CenteredListWeight pre|
      exact lt_abs.mpr (Or.inr (by linarith))
    have hbernstein :
        ((Tao.geom2PNatListPMF (m - 1)).toOuterMeasure
            prefixAbsEvent).toReal ≤
          2 * Real.exp
            (-min (v ^ 2 / (32 * ((m - 1 : ℕ) : ℝ))) (v / 8)) := by
      simpa only [prefixAbsEvent] using
        Tao.geom2PNatListPMF_centeredWeight_absTail_le_min
          (show 0 < m - 1 by omega) hv
    exact hcarrier.trans_eq hproject |>.trans (hmono.trans hbernstein)
  calc
    (∑ bs ∈ S, Tao.geom2PNatListMass bs) =
        (∑ bs ∈ S.filter upper, Tao.geom2PNatListMass bs) +
          ∑ bs ∈ S.filter (fun bs => ¬ upper bs),
            Tao.geom2PNatListMass bs := hsplit
    _ ≤ 2 * Real.exp (-min (u ^ 2 / (32 * (m : ℝ))) (u / 8)) +
        2 * Real.exp
          (-min (v ^ 2 / (32 * ((m - 1 : ℕ) : ℝ))) (v / 8)) :=
      add_le_add hupperMass hlowerMass

end
end ND
end Erdos1135
