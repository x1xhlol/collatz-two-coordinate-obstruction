import Erdos1135.Tao.Renewal.Lemma79R2Scalar
import Erdos1135.Tao.Renewal.Lemma79TailExpectationCore

/-!
# Lemma 7.9 Killed R=2 Endpoint Contraction

This proof leaf integrates the two-valued first-exit weight in native
`ENNReal`.  It preserves the exact complementary mass identity, which is
essential for obtaining the contraction factor from white mass at least one
half.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Native two-valued endpoint weight: white exits pay `exp(-1)`, all others
pay one. -/
noncomputable def lemma79R2EndpointWeight
    {Omega : Type*} (White : Set Omega) (omega : Omega) : ENNReal :=
  by
    classical
    exact if omega ∈ White then ENNReal.ofReal (Real.exp (-1)) else 1

/-- Native nonnegative PMF expectation distributes over pointwise addition. -/
theorem lemma79PMFENNExpectation_add
    {Omega : Type*} (mu : PMF Omega) (F G : Omega -> ENNReal) :
    lemma79PMFENNExpectation mu (fun omega => F omega + G omega) =
      lemma79PMFENNExpectation mu F + lemma79PMFENNExpectation mu G := by
  unfold lemma79PMFENNExpectation
  calc
    (∑' omega, mu omega * (F omega + G omega)) =
        ∑' omega, (mu omega * F omega + mu omega * G omega) := by
      apply tsum_congr
      intro omega
      rw [mul_add]
    _ = (∑' omega, mu omega * F omega) +
        ∑' omega, mu omega * G omega := ENNReal.tsum_add

/-- Expectation of a constant on an event is event mass times that constant. -/
theorem lemma79PMFENNExpectation_indicator_const
    {Omega : Type*} (mu : PMF Omega) (Event : Set Omega) (C : ENNReal) :
    lemma79PMFENNExpectation mu (Event.indicator fun _ => C) =
      mu.toOuterMeasure Event * C := by
  classical
  calc
    lemma79PMFENNExpectation mu (Event.indicator fun _ => C) =
        lemma79PMFENNExpectation mu
          (fun omega => (Event.indicator (fun _ => 1) omega) * C) := by
      apply congrArg (lemma79PMFENNExpectation mu)
      funext omega
      by_cases hmem : omega ∈ Event <;>
        simp [Set.indicator, hmem]
    _ = lemma79PMFENNExpectation mu
          (Event.indicator fun _ => 1) * C :=
      lemma79PMFENNExpectation_mul_const
        mu (Event.indicator fun _ => 1) C
    _ = _ := by
      rw [lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure]

/-- Exact convex-combination formula for the two-valued endpoint weight. -/
theorem lemma79PMFENNExpectation_r2EndpointWeight_eq
    {Omega : Type*} (mu : PMF Omega) (White : Set Omega) :
    lemma79PMFENNExpectation mu (lemma79R2EndpointWeight White) =
      ENNReal.ofReal (Real.exp (-1)) +
        mu.toOuterMeasure Whiteᶜ *
          ENNReal.ofReal (1 - Real.exp (-1)) := by
  classical
  have hexp0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hexp1 : Real.exp (-1) ≤ 1 := by
    simp
  have hdiff0 : 0 ≤ 1 - Real.exp (-1) := sub_nonneg.mpr hexp1
  have hone :
      ENNReal.ofReal (Real.exp (-1)) +
          ENNReal.ofReal (1 - Real.exp (-1)) = 1 := by
    rw [← ENNReal.ofReal_add hexp0 hdiff0]
    rw [show Real.exp (-1) + (1 - Real.exp (-1)) = 1 by ring, ENNReal.ofReal_one]
  have hpoint :
      lemma79R2EndpointWeight White =
        fun omega =>
          ENNReal.ofReal (Real.exp (-1)) +
            Whiteᶜ.indicator
              (fun _ => ENNReal.ofReal (1 - Real.exp (-1))) omega := by
    funext omega
    by_cases hwhite : omega ∈ White
    · simp [lemma79R2EndpointWeight, Set.indicator, hwhite]
    · have hcomp : omega ∈ Whiteᶜ := hwhite
      simp [lemma79R2EndpointWeight, Set.indicator, hwhite, hcomp, hone]
  rw [hpoint, lemma79PMFENNExpectation_add]
  rw [lemma79PMFENNExpectation_indicator_const]
  have huniv :
      mu.toOuterMeasure Set.univ = 1 :=
    (mu.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hconst :
      lemma79PMFENNExpectation mu
          (fun _ => ENNReal.ofReal (Real.exp (-1))) =
        ENNReal.ofReal (Real.exp (-1)) := by
    calc
      _ = lemma79PMFENNExpectation mu
          (Set.univ.indicator
            fun _ => ENNReal.ofReal (Real.exp (-1))) := by
        apply congrArg (lemma79PMFENNExpectation mu)
        funext omega
        simp
      _ = mu.toOuterMeasure Set.univ *
          ENNReal.ofReal (Real.exp (-1)) :=
        lemma79PMFENNExpectation_indicator_const
          mu Set.univ (ENNReal.ofReal (Real.exp (-1)))
      _ = _ := by simp [huniv]
  rw [hconst]

/-- White endpoint mass at least one half gives the exact native `R=2`
contraction factor. -/
theorem lemma79PMFENNExpectation_r2EndpointWeight_le_contraction
    {Omega : Type*} (mu : PMF Omega) (White : Set Omega)
    (hmass : (1 / 2 : ℝ) ≤ (mu.toOuterMeasure White).toReal) :
    lemma79PMFENNExpectation mu (lemma79R2EndpointWeight White) ≤
      ENNReal.ofReal lemma79R2ContractionFactor := by
  have huniv :
      mu.toOuterMeasure Set.univ = 1 :=
    (mu.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hfinite (Event : Set Omega) : mu.toOuterMeasure Event ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      mu.toOuterMeasure Event ≤ mu.toOuterMeasure Set.univ :=
        mu.toOuterMeasure.mono (Set.subset_univ Event)
      _ = 1 := huniv
  have hcar : mu.toOuterMeasure.IsCaratheodory White := by
    change @MeasurableSet Omega mu.toOuterMeasure.caratheodory White
    rw [PMF.toOuterMeasure_caratheodory]
    trivial
  have hsplitENN :
      mu.toOuterMeasure Set.univ =
        mu.toOuterMeasure (Set.univ ∩ White) +
          mu.toOuterMeasure (Set.univ \ White) :=
    hcar Set.univ
  have hsplit :
      1 = (mu.toOuterMeasure White).toReal +
        (mu.toOuterMeasure Whiteᶜ).toReal := by
    have h := congrArg ENNReal.toReal hsplitENN
    simpa [huniv, ENNReal.toReal_add, hfinite, Set.sdiff_eq] using h
  have hcompReal :
      (mu.toOuterMeasure Whiteᶜ).toReal ≤ (1 / 2 : ℝ) := by
    linarith
  have hcomp :
      mu.toOuterMeasure Whiteᶜ ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    apply (ENNReal.toReal_le_toReal
      (hfinite Whiteᶜ) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact hcompReal
  rw [lemma79PMFENNExpectation_r2EndpointWeight_eq]
  calc
    ENNReal.ofReal (Real.exp (-1)) +
        mu.toOuterMeasure Whiteᶜ *
          ENNReal.ofReal (1 - Real.exp (-1)) ≤
      ENNReal.ofReal (Real.exp (-1)) +
        ENNReal.ofReal (1 / 2 : ℝ) *
          ENNReal.ofReal (1 - Real.exp (-1)) := by
      gcongr
    _ = ENNReal.ofReal lemma79R2ContractionFactor := by
      have hexp0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
      have hexp1 : Real.exp (-1) ≤ 1 := by
        simp
      have hdiff0 : 0 ≤ 1 - Real.exp (-1) := sub_nonneg.mpr hexp1
      rw [← ENNReal.ofReal_mul (p := (1 / 2 : ℝ))
        (q := 1 - Real.exp (-1)) (by norm_num)]
      rw [← ENNReal.ofReal_add hexp0
        (mul_nonneg (by norm_num) hdiff0)]
      congr 1
      unfold lemma79R2ContractionFactor
      ring

/-- Claim-Star scalar smallness absorbs the native endpoint contraction. -/
theorem lemma79PMFENNExpectation_r2EndpointWeight_le_exp_neg
    {Omega : Type*} (mu : PMF Omega) (White : Set Omega)
    {epsilon : ℝ}
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hmass : (1 / 2 : ℝ) ≤ (mu.toOuterMeasure White).toReal) :
    lemma79PMFENNExpectation mu (lemma79R2EndpointWeight White) ≤
      ENNReal.ofReal (Real.exp (-epsilon)) := by
  exact
    (lemma79PMFENNExpectation_r2EndpointWeight_le_contraction
      mu White hmass).trans
        (ENNReal.ofReal_le_ofReal
          (lemma79R2ContractionFactor_le_exp_neg hscalar))

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
