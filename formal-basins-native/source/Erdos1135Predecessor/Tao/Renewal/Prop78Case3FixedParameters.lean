/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case3BaseKcutFiniteSum
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshSurvival
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

structure TaoSection7Case3FixedParameters
    (constants : TaoSection7Lemma710Constants)
    (A : ℕ) (epsilon : ℝ) where
  scalar : TaoSection7ClaimStarScalarPacket epsilon
  A_pos : 1 ≤ A
  Aweight : ℕ
  A_le_Aweight : A ≤ Aweight
  Aweight_ge_eight : 8 ≤ Aweight
  factorizedSlack :
    TaoSection7Case3BaseKcutFactorizedSlackSchedule
      Aweight 8 (4 * Aweight) constants
  T : ℕ
  priority_threshold :
    (10 : ℝ) * (A : ℝ) ≤ epsilon ^ 3 * ((T + 1 : ℕ) : ℝ)
  Amarkov : ℕ
  Amarkov_eq : Amarkov = Aweight + 1
  R : ℕ
  R_pos : 0 < R
  white_room :
    (T : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 + epsilon <
      epsilon * (R : ℝ)
  Pmax : ℕ
  Pmax_eq :
    Pmax = lemma79CanonicalSurvivalMaxTime 8 (4 * Aweight) T R
  P : ℕ
  P_eq : P = Pmax + 1
  iterate_room :
    taoSection7Case3BaseKcutNextBoundIterateRoom
      8 (4 * Aweight) T (R - 1) T P

theorem TaoSection7Case3FixedParameters.Pmax_lt_P
    {constants : TaoSection7Lemma710Constants}
    {A : ℕ} {epsilon : ℝ}
    (h : TaoSection7Case3FixedParameters constants A epsilon) :
    h.Pmax < h.P := by
  rw [h.P_eq]
  omega

def TaoSection7Case3FixedParameters.to_absorptionInputs
    {constants : TaoSection7Lemma710Constants}
    {A : ℕ} {epsilon : ℝ}
    (h : TaoSection7Case3FixedParameters constants A epsilon) :
    TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
      (Finset.range (h.Pmax + 1))
      h.Aweight 8 (4 * h.Aweight) constants :=
  TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs.of_scalarRows
    (TaoSection7Case3BaseKcutScalarRowInputs.of_factorizedSlackSchedule
      (allowed := Finset.range (h.Pmax + 1))
      (Aweight := h.Aweight) (base := 8)
      (Kcut := 4 * h.Aweight) (m := h.Pmax + 1)
      (constants := constants) h.factorizedSlack
      (lt_of_lt_of_le (by norm_num : 0 < 8) h.Aweight_ge_eight)
      (by
        intro p hp
        exact Finset.mem_range.1 hp))

end

end Tao

end Erdos1135Predecessor
