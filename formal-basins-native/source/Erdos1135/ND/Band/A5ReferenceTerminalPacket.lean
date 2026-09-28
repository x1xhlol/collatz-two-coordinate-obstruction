import Erdos1135.ND.Band.A5ReferenceEtaRate

/-!
# Uniform terminal-cell packet for the A5 reference schedule

This leaf assembles integer room, frozen WC-1, the fixed-total center window,
and the complete eta absorption guard with the scheduler's required quantifier
order: one reference level for every retained `(t2)` terminal cell.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

/-- For every fixed positive tube constant, one eventual reference schedule
simultaneously supplies the integer room, M1 window, center window, and full
eta absorption guard for every retained `(t2)` terminal cell. -/
theorem eventually_ndA5Reference_terminal_cell_packet
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ B : ℕ in atTop,
      150 ≤ ndA5ReferenceLevel B ∧
      ndA5ReferenceLevel B ≤ Tao.taoSection5M0 B ∧
      0 ≤ ndA5ReferenceAbsorbBar B C ∧
      ndA5ReferenceAbsorbBar B C ≤ 1 / 2 ∧
      ∀ {n : ℕ},
        NDA5T2ScaleFacts B n C →
        8 * ndA5ReferenceLevel B ≤ n - Tao.taoSection5M0 B ∧
        ∀ {L : ℕ}, L ∈ ndA5TerminalTotals B C n →
          ndSection7M1Window ((771 / 100 : ℝ) * C)
            (n - Tao.taoSection5M0 B) L ∧
          ndFixedTotalRatioCenterOffset (ndA5ReferenceLevel B)
              (n - Tao.taoSection5M0 B) L ≤
            ndFixedTotalRatioScale (ndA5ReferenceLevel B) ∧
          0 ≤ ndFixedTotalRatioEps (ndA5ReferenceLevel B)
                (n - Tao.taoSection5M0 B) L +
                8 / (ndA5ReferenceLevel B : ℝ) ^ 3 ∧
          ndFixedTotalRatioEps (ndA5ReferenceLevel B)
                (n - Tao.taoSection5M0 B) L +
                8 / (ndA5ReferenceLevel B : ℝ) ^ 3 ≤ 1 ∧
          (43 / 25 : ℝ) *
                (ndFixedTotalRatioEps (ndA5ReferenceLevel B)
                    (n - Tao.taoSection5M0 B) L +
                  8 / (ndA5ReferenceLevel B : ℝ) ^ 3) ≤
              ndA5ReferenceAbsorbBar B C := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_ndA5ReferenceLevel_integer_room,
      eventually_ndA5ReferenceEtaBar_le C hC,
      hlog.eventually_ge_atTop (4000000 : ℝ)]
      with B hroom hetaBar hlogLarge
  -- This one scalar cutoff supplies both positivity of the common floor and
  -- the finite `11800` threshold needed by frozen WC-1.
  have habsorb :=
    ndA5ReferenceAbsorbBar_bounds_of_etaBar_le hC hroom.1
      (by
        unfold ndA5ReferenceNuFloor
        positivity)
      hetaBar
  refine ⟨hroom.1, hroom.2.1, habsorb.1, habsorb.2, ?_⟩
  intro n ht2
  refine ⟨hroom.2.2 ht2, ?_⟩
  intro L hL
  have hnuLargeR :
      (11800 : ℝ) ≤ ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := by
    calc
      (11800 : ℝ) ≤ (340 / 100000 : ℝ) * 4000000 := by norm_num
      _ ≤ (340 / 100000 : ℝ) * Real.log B :=
        mul_le_mul_of_nonneg_left hlogLarge (by norm_num)
      _ ≤ ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := ht2.nu_lower
  have hnuLarge : 11800 ≤ n - Tao.taoSection5M0 B := by
    exact_mod_cast hnuLargeR
  have hfloor : 0 < ndA5ReferenceNuFloor B := by
    unfold ndA5ReferenceNuFloor
    positivity
  have hM1 :=
    ndA5ReferenceM1Window_of_t2_terminal hC.le ht2 hnuLarge hL
  have hcell :=
    ndA5Reference_cell_guards_of_etaBar_le hroom.1 ht2 hL hfloor hetaBar
  have hcenterBar :=
    ndA5ReferenceCenterBar_le_ratioScale_of_etaBar_le
      hC hroom.1 hfloor hetaBar
  exact ⟨hM1, hcell.1.trans hcenterBar,
    hcell.2.1, hcell.2.2.1, hcell.2.2.2.1⟩

/-- Named pointwise surface of the common reference scheduler, used by
downstream componentwise absorption without repeating the quantifier block. -/
def NDA5ReferenceTerminalCellPacketAt (B : ℕ) (C : ℝ) : Prop :=
  150 ≤ ndA5ReferenceLevel B ∧
  ndA5ReferenceLevel B ≤ Tao.taoSection5M0 B ∧
  0 ≤ ndA5ReferenceAbsorbBar B C ∧
  ndA5ReferenceAbsorbBar B C ≤ 1 / 2 ∧
  ∀ {n : ℕ},
    NDA5T2ScaleFacts B n C →
    8 * ndA5ReferenceLevel B ≤ n - Tao.taoSection5M0 B ∧
    ∀ {L : ℕ}, L ∈ ndA5TerminalTotals B C n →
      ndSection7M1Window ((771 / 100 : ℝ) * C)
        (n - Tao.taoSection5M0 B) L ∧
      ndFixedTotalRatioCenterOffset (ndA5ReferenceLevel B)
          (n - Tao.taoSection5M0 B) L ≤
        ndFixedTotalRatioScale (ndA5ReferenceLevel B) ∧
      0 ≤ ndFixedTotalRatioEps (ndA5ReferenceLevel B)
            (n - Tao.taoSection5M0 B) L +
            8 / (ndA5ReferenceLevel B : ℝ) ^ 3 ∧
      ndFixedTotalRatioEps (ndA5ReferenceLevel B)
            (n - Tao.taoSection5M0 B) L +
            8 / (ndA5ReferenceLevel B : ℝ) ^ 3 ≤ 1 ∧
      (43 / 25 : ℝ) *
            (ndFixedTotalRatioEps (ndA5ReferenceLevel B)
                (n - Tao.taoSection5M0 B) L +
              8 / (ndA5ReferenceLevel B : ℝ) ^ 3) ≤
          ndA5ReferenceAbsorbBar B C

/-- Filter-ready named form of the common reference terminal packet. -/
theorem eventually_ndA5ReferenceTerminalCellPacketAt
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ B : ℕ in atTop, NDA5ReferenceTerminalCellPacketAt B C := by
  filter_upwards [eventually_ndA5Reference_terminal_cell_packet C hC]
    with B hpacket
  simpa only [NDA5ReferenceTerminalCellPacketAt] using hpacket

end
end ND
end Erdos1135
