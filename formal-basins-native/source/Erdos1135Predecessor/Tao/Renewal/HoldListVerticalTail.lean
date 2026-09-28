/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma77TerminalHoldMoment
import Erdos1135Predecessor.Tao.Renewal.Lemma79NativeMarkov
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEprimeFourTail

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

private theorem lemma79PMFENNExpectation_bind
    {Alpha Beta : Type*} (mu : PMF Alpha) (nu : Alpha → PMF Beta)
    (F : Beta → ENNReal) :
    lemma79PMFENNExpectation (mu.bind nu) F =
      ∑' x, mu x * lemma79PMFENNExpectation (nu x) F := by
  classical
  unfold lemma79PMFENNExpectation
  calc
    (∑' y, (mu.bind nu) y * F y) =
        ∑' y, (∑' x, mu x * nu x y) * F y := by
      apply tsum_congr
      intro y
      rw [PMF.bind_apply]
    _ = ∑' y, ∑' x, (mu x * nu x y) * F y := by
      apply tsum_congr
      intro y
      rw [ENNReal.tsum_mul_right]
    _ = ∑' x, ∑' y, (mu x * nu x y) * F y := by
      rw [ENNReal.tsum_comm]
    _ = ∑' x, mu x * ∑' y, nu x y * F y := by
      apply tsum_congr
      intro x
      calc
        (∑' y, (mu x * nu x y) * F y) =
            ∑' y, mu x * (nu x y * F y) := by
          apply tsum_congr
          intro y
          ac_rfl
        _ = mu x * ∑' y, nu x y * F y :=
          ENNReal.tsum_mul_left

theorem lemma79HoldPMF_verticalExpMoment_ennreal_le
    {C alpha : ℝ}
    (hinput : Lemma77TerminalHoldExpMomentInput C alpha) :
    lemma79PMFENNExpectation taoSection7HoldPMF
        (fun h =>
          ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ)))) ≤
      ENNReal.ofReal C := by
  have hpoint :
      ∀ h : TaoSection7RenewalPoint,
        Real.exp (alpha * (h.l : ℝ)) ≤
          lemma77TerminalHoldExpWeight alpha h := by
    intro h
    unfold lemma77TerminalHoldExpWeight
    apply Real.exp_le_exp.mpr
    have hj : 0 ≤ (((h.j : ℕ) : ℝ)) := Nat.cast_nonneg _
    nlinarith [hinput.constants.2]
  calc
    lemma79PMFENNExpectation taoSection7HoldPMF
        (fun h =>
          ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ)))) ≤
        ∑' h, taoSection7HoldPMF h *
          ENNReal.ofReal (lemma77TerminalHoldExpWeight alpha h) := by
      unfold lemma79PMFENNExpectation
      apply ENNReal.tsum_le_tsum
      intro h
      exact mul_le_mul_right
        (ENNReal.ofReal_le_ofReal (hpoint h)) _
    _ = ENNReal.ofReal
        (∑' h,
          (taoSection7HoldPMF h).toReal *
            lemma77TerminalHoldExpWeight alpha h) := by
      rw [ENNReal.ofReal_tsum_of_nonneg]
      · apply tsum_congr
        intro h
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (PMF.apply_ne_top taoSection7HoldPMF h)]
      · intro h
        exact mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
      · exact hinput.summable_weighted
    _ ≤ ENNReal.ofReal C :=
      ENNReal.ofReal_le_ofReal hinput.moment_le

private theorem lemma79VerticalExpWeight_cons
    (alpha : ℝ) (start : TaoSection7RenewalPoint) (N : ℕ)
    (h : TaoSection7RenewalPoint)
    (hs : List TaoSection7RenewalPoint) :
    ENNReal.ofReal
        (Real.exp (alpha *
          (lemma77HoldPrefixVerticalIncrement start (N + 1) (h :: hs) :
            ℝ))) =
      ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ))) *
        ENNReal.ofReal
          (Real.exp (alpha *
            (lemma77HoldPrefixVerticalIncrement start N hs : ℝ))) := by
  have hstart :=
    lemma77HoldPrefixVerticalIncrement_start_eq
      (start + h) start N hs
  have hincrement :
      lemma77HoldPrefixVerticalIncrement start (N + 1) (h :: hs) =
        h.l + lemma77HoldPrefixVerticalIncrement start N hs := by
    simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement,
      taoSection7RenewalPathPoint] at hstart ⊢
    omega
  rw [hincrement, Int.cast_add, mul_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem lemma79HoldListPMF_verticalExpMoment_ennreal_le
    (N : ℕ) (start : TaoSection7RenewalPoint)
    {C alpha : ℝ}
    (hinput : Lemma77TerminalHoldExpMomentInput C alpha) :
    lemma79PMFENNExpectation (taoSection7HoldListPMF N)
        (fun hs =>
          ENNReal.ofReal
            (Real.exp (alpha *
              (lemma77HoldPrefixVerticalIncrement start N hs : ℝ)))) ≤
      ENNReal.ofReal C ^ N := by
  induction N with
  | zero =>
      unfold lemma79PMFENNExpectation
      rw [tsum_eq_single []]
      · simp [taoSection7HoldListPMF, lemma77HoldPrefixVerticalIncrement,
          prefixVerticalIncrement]
      · intro hs hne
        simp [taoSection7HoldListPMF, hne]
  | succ N ih =>
      let W : List TaoSection7RenewalPoint → ENNReal := fun hs =>
        ENNReal.ofReal
          (Real.exp (alpha *
            (lemma77HoldPrefixVerticalIncrement start (N + 1) hs : ℝ)))
      let WT : List TaoSection7RenewalPoint → ENNReal := fun hs =>
        ENNReal.ofReal
          (Real.exp (alpha *
            (lemma77HoldPrefixVerticalIncrement start N hs : ℝ)))
      calc
        lemma79PMFENNExpectation (taoSection7HoldListPMF (N + 1)) W =
            lemma79PMFENNExpectation
              (taoSection7HoldPMF.bind fun h =>
                (taoSection7HoldListPMF N).map fun hs => h :: hs) W := by
          rfl
        _ = ∑' h, taoSection7HoldPMF h *
            lemma79PMFENNExpectation
              ((taoSection7HoldListPMF N).map fun hs => h :: hs) W :=
          lemma79PMFENNExpectation_bind _ _ _
        _ = ∑' h, taoSection7HoldPMF h *
            lemma79PMFENNExpectation (taoSection7HoldListPMF N)
              (W ∘ fun hs => h :: hs) := by
          apply tsum_congr
          intro h
          rw [lemma79PMFENNExpectation_map]
        _ = ∑' h, taoSection7HoldPMF h *
            (ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ))) *
              lemma79PMFENNExpectation (taoSection7HoldListPMF N) WT) := by
          apply tsum_congr
          intro h
          congr 1
          unfold lemma79PMFENNExpectation
          calc
            (∑' hs, taoSection7HoldListPMF N hs *
                (W ∘ fun hs => h :: hs) hs) =
                ∑' hs, taoSection7HoldListPMF N hs *
                  (ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ))) *
                    WT hs) := by
              apply tsum_congr
              intro hs
              dsimp only [Function.comp_apply, W, WT]
              rw [lemma79VerticalExpWeight_cons]
            _ = ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ))) *
                ∑' hs, taoSection7HoldListPMF N hs * WT hs := by
              calc
                (∑' hs, taoSection7HoldListPMF N hs *
                    (ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ))) *
                      WT hs)) =
                    ∑' hs, ENNReal.ofReal
                      (Real.exp (alpha * (h.l : ℝ))) *
                        (taoSection7HoldListPMF N hs * WT hs) := by
                  apply tsum_congr
                  intro hs
                  ac_rfl
                _ = ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ))) *
                    ∑' hs, taoSection7HoldListPMF N hs * WT hs :=
                  ENNReal.tsum_mul_left
        _ = (∑' h, taoSection7HoldPMF h *
              ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ)))) *
            lemma79PMFENNExpectation (taoSection7HoldListPMF N) WT := by
          calc
            (∑' h, taoSection7HoldPMF h *
                (ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ))) *
                  lemma79PMFENNExpectation (taoSection7HoldListPMF N) WT)) =
                ∑' h, (taoSection7HoldPMF h *
                  ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ)))) *
                    lemma79PMFENNExpectation
                      (taoSection7HoldListPMF N) WT := by
              apply tsum_congr
              intro h
              ac_rfl
            _ = (∑' h, taoSection7HoldPMF h *
                  ENNReal.ofReal (Real.exp (alpha * (h.l : ℝ)))) *
                lemma79PMFENNExpectation (taoSection7HoldListPMF N) WT :=
              ENNReal.tsum_mul_right
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal C ^ N) := by
          apply mul_le_mul
          · simpa [lemma79PMFENNExpectation] using
              lemma79HoldPMF_verticalExpMoment_ennreal_le hinput
          · simpa [WT] using ih
          · exact bot_le
          · exact bot_le
        _ = ENNReal.ofReal C ^ (N + 1) := by
          rw [pow_succ']

theorem lemma79HoldListPMF_verticalTail_outerMeasure_le
    (P : ℕ) (start : TaoSection7RenewalPoint) (Y : ℝ) :
    (taoSection7HoldListPMF P).toOuterMeasure
        {fresh |
          Y ≤
            (lemma77HoldPrefixVerticalIncrement start P fresh : ℝ)} ≤
      ENNReal.ofReal
        ((15 : ℝ) ^ P *
          Real.exp
            (-(Real.log (21 / 20 : ℝ)) * Y)) := by
  let alpha : ℝ := Real.log (21 / 20 : ℝ)
  let F : List TaoSection7RenewalPoint → ENNReal := fun fresh =>
    ENNReal.ofReal
      (Real.exp
        (alpha *
          (lemma77HoldPrefixVerticalIncrement start P fresh : ℝ)))
  let cutoff : ENNReal := ENNReal.ofReal (Real.exp (alpha * Y))
  let Event : Set (List TaoSection7RenewalPoint) :=
    {fresh |
      Y ≤ (lemma77HoldPrefixVerticalIncrement start P fresh : ℝ)}
  have halpha : 0 < alpha := by
    dsimp [alpha]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 21 / 20)
  have hmean :
      lemma79PMFENNExpectation (taoSection7HoldListPMF P) F ≤
        ENNReal.ofReal (15 : ℝ) ^ P := by
    simpa [F, alpha] using
      (lemma79HoldListPMF_verticalExpMoment_ennreal_le
        P start lemma77TerminalHoldExpMomentInput_log_21_div_20)
  have hsubset :
      Event ⊆ {fresh | cutoff ≤ F fresh} := by
    intro fresh hfresh
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    dsimp [cutoff, F]
    exact mul_le_mul_of_nonneg_left hfresh halpha.le
  have hmarkov :=
    lemma79_pmfToOuterMeasure_le_mul_le_expectation
      (taoSection7HoldListPMF P) F cutoff
  have hmul :
      (taoSection7HoldListPMF P).toOuterMeasure Event * cutoff ≤
        ENNReal.ofReal (15 : ℝ) ^ P := by
    calc
      (taoSection7HoldListPMF P).toOuterMeasure Event * cutoff ≤
          (taoSection7HoldListPMF P).toOuterMeasure
              {fresh | cutoff ≤ F fresh} * cutoff :=
        mul_le_mul_left
          ((taoSection7HoldListPMF P).toOuterMeasure.mono hsubset) _
      _ ≤ lemma79PMFENNExpectation (taoSection7HoldListPMF P) F :=
        hmarkov
      _ ≤ ENNReal.ofReal (15 : ℝ) ^ P := hmean
  have hcutoff0 : cutoff ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hcutoffTop : cutoff ≠ ⊤ := ENNReal.ofReal_ne_top
  have htargetMul :
      ENNReal.ofReal
          ((15 : ℝ) ^ P * Real.exp (-alpha * Y)) * cutoff =
        ENNReal.ofReal (15 : ℝ) ^ P := by
    dsimp [cutoff]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (15 : ℝ) ^ P *
      Real.exp (-alpha * Y))]
    rw [← ENNReal.ofReal_pow (by norm_num : 0 ≤ (15 : ℝ))]
    congr 1
    calc
      (15 : ℝ) ^ P * Real.exp (-alpha * Y) * Real.exp (alpha * Y) =
          (15 : ℝ) ^ P *
            (Real.exp (-alpha * Y) * Real.exp (alpha * Y)) := by
        ring
      _ = (15 : ℝ) ^ P := by
        rw [← Real.exp_add]
        ring_nf
        simp
  apply (ENNReal.mul_le_mul_iff_right hcutoff0 hcutoffTop).mp
  change cutoff *
      (taoSection7HoldListPMF P).toOuterMeasure Event ≤
    cutoff * ENNReal.ofReal
      ((15 : ℝ) ^ P *
        Real.exp (-(Real.log (21 / 20 : ℝ)) * Y))
  calc
    cutoff * (taoSection7HoldListPMF P).toOuterMeasure Event =
        (taoSection7HoldListPMF P).toOuterMeasure Event * cutoff := by
      ac_rfl
    _ ≤ ENNReal.ofReal (15 : ℝ) ^ P := hmul
    _ = ENNReal.ofReal
          ((15 : ℝ) ^ P * Real.exp (-alpha * Y)) * cutoff :=
      htargetMul.symm
    _ = cutoff * ENNReal.ofReal
          ((15 : ℝ) ^ P *
            Real.exp (-(Real.log (21 / 20 : ℝ)) * Y)) := by
      dsimp [alpha]
      ac_rfl

theorem lemma79CanonicalFreshVerticalTailEvent_outerMeasure_le
    (P X : ℕ) (start : TaoSection7RenewalPoint) :
    (taoSection7HoldListPMF P).toOuterMeasure
        (lemma79CanonicalFreshVerticalTailEvent start P X) ≤
      ENNReal.ofReal
        ((15 : ℝ) ^ P *
          Real.exp
            (-(Real.log (21 / 20 : ℝ)) * (X : ℝ))) := by
  have hEvent :
      lemma79CanonicalFreshVerticalTailEvent start P X =
        {fresh |
          (X : ℝ) ≤
            (lemma77HoldPrefixVerticalIncrement start P fresh : ℝ)} := by
    ext fresh
    simp only [lemma79CanonicalFreshVerticalTailEvent, Set.mem_setOf_eq]
    constructor <;> intro h
    · exact_mod_cast h
    · exact_mod_cast h
  rw [hEvent]
  exact lemma79HoldListPMF_verticalTail_outerMeasure_le P start (X : ℝ)

theorem lemma79_verticalMoment_prefactor_le_alphaEighth
    (P Aweight : ℕ) (hAweight : 8 ≤ Aweight) :
    (15 : ℝ) ^ P *
        Real.exp
          (-(Real.log (21 / 20 : ℝ)) *
            ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1))) ≤
      Real.exp
        (-(Real.log (21 / 20 : ℝ) / 8) *
          ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1))) := by
  let alpha : ℝ := Real.log (21 / 20 : ℝ)
  have halpha : 0 < alpha := by
    dsimp [alpha]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 21 / 20)
  have hpow : (15 : ℝ) < (21 / 20 : ℝ) ^ 56 := by
    norm_num
  have hlog := Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  have hlog15 : Real.log (15 : ℝ) ≤ 56 * alpha := by
    simpa [alpha] using hlog.le
  have hAreal : (8 : ℝ) ≤ Aweight := by
    exact_mod_cast hAweight
  have hAsq : (64 : ℝ) ≤ (Aweight : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((Aweight : ℝ) - 8)]
  have hscale :
      64 * ((P : ℝ) + 1) ≤
        (Aweight : ℝ) ^ 2 * ((P : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hAsq (by positivity)
  have hpRate :
      56 * (P : ℝ) ≤
        (7 / 8 : ℝ) *
          ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1)) := by
    nlinarith
  have hlogRate :
      (P : ℝ) * Real.log (15 : ℝ) ≤
        (7 / 8 : ℝ) * alpha *
          ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1)) := by
    calc
      (P : ℝ) * Real.log (15 : ℝ) ≤
          (P : ℝ) * (56 * alpha) :=
        mul_le_mul_of_nonneg_left hlog15 (Nat.cast_nonneg P)
      _ = (56 * (P : ℝ)) * alpha := by ring
      _ ≤ ((7 / 8 : ℝ) *
          ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1))) * alpha :=
        mul_le_mul_of_nonneg_right hpRate halpha.le
      _ = (7 / 8 : ℝ) * alpha *
          ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1)) := by ring
  have h15pow :
      (15 : ℝ) ^ P =
        Real.exp ((P : ℝ) * Real.log (15 : ℝ)) := by
    calc
      (15 : ℝ) ^ P =
          (Real.exp (Real.log (15 : ℝ))) ^ P := by
        rw [Real.exp_log (by norm_num : 0 < (15 : ℝ))]
      _ = Real.exp ((P : ℝ) * Real.log (15 : ℝ)) := by
        rw [← Real.exp_nat_mul]
  rw [h15pow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem lemma79CanonicalFreshVerticalTailEvent_outerMeasure_le_alphaEighth
    (P Aweight : ℕ) (start : TaoSection7RenewalPoint)
    (hAweight : 8 ≤ Aweight) :
    (taoSection7HoldListPMF P).toOuterMeasure
        (lemma79CanonicalFreshVerticalTailEvent
          start P (Aweight ^ 2 * (P + 1))) ≤
      ENNReal.ofReal
        (Real.exp
          (-(Real.log (21 / 20 : ℝ) / 8) *
            ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1)))) := by
  calc
    (taoSection7HoldListPMF P).toOuterMeasure
        (lemma79CanonicalFreshVerticalTailEvent
          start P (Aweight ^ 2 * (P + 1))) ≤
        ENNReal.ofReal
          ((15 : ℝ) ^ P *
            Real.exp
              (-(Real.log (21 / 20 : ℝ)) *
                ((Aweight ^ 2 * (P + 1) : ℕ) : ℝ))) :=
      lemma79CanonicalFreshVerticalTailEvent_outerMeasure_le
        P (Aweight ^ 2 * (P + 1)) start
    _ = ENNReal.ofReal
          ((15 : ℝ) ^ P *
            Real.exp
              (-(Real.log (21 / 20 : ℝ)) *
                ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1)))) := by
      congr 2
      push_cast
      ring
    _ ≤ ENNReal.ofReal
          (Real.exp
            (-(Real.log (21 / 20 : ℝ) / 8) *
              ((Aweight : ℝ) ^ 2 * ((P : ℝ) + 1)))) :=
      ENNReal.ofReal_le_ofReal
        (lemma79_verticalMoment_prefactor_le_alphaEighth
          P Aweight hAweight)

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
