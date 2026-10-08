import Erdos1135.Tao.Renewal.Prop78Case3BaseKcutScheduleExistence
import Erdos1135.Tao.Renewal.QEndpointFreshSurvival

/-!
# Proposition 7.8 Case 3 Fixed Parameters

This leaf chooses the Case 3 recurrence and scalar parameters that must
precede the eventual source scale: `Aweight`, the exact factorized scalar
schedule, `T`, `Amarkov`, `R`, the survival cap, and the strict prefix horizon.
The earlier absolute geometry packet still owns `L`, localized mass, and the
collar condition that determines the admissible `epsilon`.  This packet
deliberately contains no ambient `m`, Fourier sample, boundary point, or
triangle.  Its ceiling selectors prove the exact inequalities consumed below;
they do not preserve Tao's particular floor formulas as data.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

/-- Source-independent Case 3 parameters selected before the eventual
boundary scale. -/
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

/-- The fixed factorized schedule supplies the scalar absorption record on
the exact inclusive survival range. -/
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

/-- Every positive requested exponent and Claim-Star scalar packet admits a
complete source-independent Case 3 parameter choice. -/
theorem nonempty_taoSection7Case3FixedParameters
    (constants : TaoSection7Lemma710Constants)
    (A : ℕ) {epsilon : ℝ}
    (hA : 1 ≤ A)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    Nonempty (TaoSection7Case3FixedParameters constants A epsilon) := by
  rcases
      exists_baseKcutFactorizedSlackSchedule_eight_four_mul constants A with
    ⟨Aweight, hAweight, hschedule⟩
  rcases hschedule with ⟨schedule⟩
  let T : ℕ := ⌈(10 : ℝ) * (A : ℝ) / epsilon ^ 3⌉₊
  have hepsilonCube : 0 < epsilon ^ 3 := pow_pos hscalar.epsilon_pos 3
  have hTceil :
      (10 : ℝ) * (A : ℝ) / epsilon ^ 3 ≤ (T : ℝ) := by
    dsimp [T]
    exact Nat.le_ceil _
  have hTcross :
      (10 : ℝ) * (A : ℝ) ≤ (T : ℝ) * epsilon ^ 3 :=
    (div_le_iff₀ hepsilonCube).1 hTceil
  have hpriority :
      (10 : ℝ) * (A : ℝ) ≤
        epsilon ^ 3 * ((T + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_nonneg hepsilonCube.le (by norm_num : (0 : ℝ) ≤ 1)]
  let Amarkov : ℕ := Aweight + 1
  let whiteNumerator : ℝ :=
    (T : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 + epsilon
  let R : ℕ := ⌈whiteNumerator / epsilon⌉₊ + 1
  have hRceil :
      whiteNumerator / epsilon ≤ (⌈whiteNumerator / epsilon⌉₊ : ℕ) :=
    Nat.le_ceil _
  have hRratio : whiteNumerator / epsilon < (R : ℝ) := by
    dsimp [R]
    push_cast
    nlinarith
  have hwhite : whiteNumerator < epsilon * (R : ℝ) := by
    have := (div_lt_iff₀ hscalar.epsilon_pos).1 hRratio
    nlinarith
  have hRpos : 0 < R := by
    dsimp [R]
    omega
  let Pmax : ℕ :=
    lemma79CanonicalSurvivalMaxTime 8 (4 * Aweight) T R
  let P : ℕ := Pmax + 1
  have hiterate :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        8 (4 * Aweight) T (R - 1) T P := by
    simp [taoSection7Case3BaseKcutNextBoundIterateRoom,
      taoSection7Case3IterateRoom, P, Pmax,
      lemma79CanonicalSurvivalMaxTime]
  refine ⟨{
      scalar := hscalar
      A_pos := hA
      Aweight := Aweight
      A_le_Aweight :=
        le_trans (Nat.le_max_left A 8) hAweight
      Aweight_ge_eight :=
        le_trans (Nat.le_max_right A 8) hAweight
      factorizedSlack := schedule
      T := T
      priority_threshold := hpriority
      Amarkov := Amarkov
      Amarkov_eq := rfl
      R := R
      R_pos := hRpos
      white_room := by simpa [whiteNumerator] using hwhite
      Pmax := Pmax
      Pmax_eq := rfl
      P := P
      P_eq := rfl
      iterate_room := hiterate }⟩

end

end Tao
end Erdos1135
