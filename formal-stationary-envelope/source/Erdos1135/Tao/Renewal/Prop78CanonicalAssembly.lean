/- This local copy renames unused bound variables in result types for the pinned toolchain linter.
   The logical statement is alpha-equivalent; see provenance/native-linter-patches.json. -/

import Erdos1135.Tao.Renewal.Prop78AbsolutePacket
import Erdos1135.Tao.Renewal.Prop78Case1White
import Erdos1135.Tao.Renewal.Prop78Case2Expectation
import Erdos1135.Tao.Renewal.Prop78Case3CanonicalFarBelow
import Erdos1135.Tao.Renewal.Prop78ActiveCover

/-!
# Canonical Proposition 7.8 Assembly

This leaf merges the three checked boundary cases at one threshold and one
canonical active triangle family.  Its public theorem fixes the absolute
packet and requested exponent before choosing the ambient-uniform threshold.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

/-- Assemble canonical Proposition 7.8 monotonicity from one fixed Case 3
packet while retaining each local threshold dominance proof explicitly. -/
theorem
    exists_taoSection7Prop78_canonical_monotonicity_740_threshold_of_fixedData
    (packet : TaoSection7Prop78AbsolutePacket)
    {A : ℕ}
    (fixed : TaoSection7Case3FixedParameters
      packet.constants A packet.epsilon)
    (S0 : ℕ)
    (hEStar : TaoSection7Case3CanonicalEStarData fixed S0) :
    ∃ C : ℕ,
      TaoSection7Prop78Threshold A packet.epsilon C ∧
      ∀ (n : ℕ) (xi : ZMod (3 ^ n))
        (_hxi : zmodThreePrimitive n xi) (m : ℕ),
        C ≤ m → m ≤ n / 2 →
        taoSection7SourceActualQmAtCutoff
            n A m xi packet.epsilon ≤
          taoSection7SourceActualQmAtCutoff
            n A (m - 1) xi packet.epsilon := by
  have hepsilon1 : packet.epsilon ≤ 1 :=
    fixed.scalar.epsilon_le_one_hundredth.trans (by norm_num)
  obtain ⟨C1, hcase1⟩ :=
    exists_taoSection7Prop78_case1_cutoffWhite_threshold_uniform
      A fixed.scalar.epsilon_pos
  obtain ⟨C2, hcase2⟩ :=
    exists_taoSection7Prop78_case2_nearTop_threshold
      packet.L packet.localizedMass fixed.scalar.epsilon_pos
      hepsilon1 packet.collar A
  obtain ⟨C3, hthreshold3, hcase3⟩ :=
    exists_taoSection7Prop78_case3_farBelow_canonical_threshold
      fixed S0 hEStar packet.L packet.localizedMass packet.collar
  let C := max C1 (max C2 C3)
  have hC1 : C1 ≤ C := by simp [C]
  have hC2 : C2 ≤ C := by simp [C]
  have hC3 : C3 ≤ C := by simp [C]
  have hthreshold :
      TaoSection7Prop78Threshold A packet.epsilon C :=
    ⟨hthreshold3.lowerThreshold_le.trans hC3⟩
  refine ⟨C, hthreshold, ?_⟩
  intro n xi hxi m hm hm_hi
  let hactive :=
    TaoSection7Prop78ActiveCoverData.of_canonical hxi fixed.scalar
  have hcases :
      TaoSection7Prop78BoundaryCaseBounds
        n A m xi packet.epsilon hactive.family :=
    { cutoffWhite := by
        intro p hp hwhite
        exact hcase1 n xi m (hC1.trans hm) p hp hwhite
      nearTop := by
        intro p hp hnear
        exact hcase2 n xi hactive m (hC2.trans hm) p hp hnear
      farBelow := by
        intro p hp hfar
        change TaoSection7QmBoundaryFarBelow
          (taoSection7Prop78BoundaryThreshold m)
          (taoSection7CanonicalTriangleFamily hxi fixed.scalar) p at hfar
        exact hcase3 n xi hxi m (hC3.trans hm) hm_hi p hp hfar }
  exact
    taoSection7_prop78_monotonicity_740_of_activeCover_caseBounds
      (n := n) (A := A) (C := C) (m := m)
      (xi := xi) (epsilon := packet.epsilon)
      fixed.scalar.epsilon_pos.le hthreshold hm hm_hi hactive hcases

/-- Source-facing canonical Proposition 7.8: one absolute packet and one
requested positive exponent determine a threshold before all ambient data. -/
theorem exists_taoSection7Prop78_canonical_monotonicity_740_threshold
    (packet : TaoSection7Prop78AbsolutePacket)
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C : ℕ,
      TaoSection7Prop78Threshold A packet.epsilon C ∧
      ∀ (n : ℕ) (xi : ZMod (3 ^ n))
        (_hxi : zmodThreePrimitive n xi) (m : ℕ),
        C ≤ m → m ≤ n / 2 →
        taoSection7SourceActualQmAtCutoff
            n A m xi packet.epsilon ≤
          taoSection7SourceActualQmAtCutoff
            n A (m - 1) xi packet.epsilon := by
  obtain ⟨fixed, S0, hEStar⟩ := packet.uniformEStar A hA
  exact
    exists_taoSection7Prop78_canonical_monotonicity_740_threshold_of_fixedData
      packet fixed S0 hEStar

end

end Tao
end Erdos1135
