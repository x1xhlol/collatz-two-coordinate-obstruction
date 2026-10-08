import PadicHaarLift
import CanonicalHaarDensity
import CanonicalPadicCylinderRecursion

set_option autoImplicit false
set_option maxHeartbeats 300000
open MeasureTheory Filter
open scoped ENNReal Topology
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

theorem canonicalHaarDensity_measurable : Measurable canonicalHaarDensity := by
  simpa only [canonicalHaarDensity, Real.norm_eq_abs] using
    (Lp.stronglyMeasurable canonicalHaarLimit).norm.measurable

theorem padicAffineBranch_one_eq_syracuseJ (x : ℤ_[3]) :
    padicAffineBranch 1 x = syracuseJ x := by
  simp [padicAffineBranch, syracuseJ]

theorem canonicalPadicRho_oddLift (k : ℕ) (x : ℤ_[3]) :
    padicOddLift (canonicalPadicRho k) x =
      if PadicInt.toZModPow 1 x = 2 then canonicalPadicRho k (padicOddPredecessor x) else 0 := by
  by_cases hx : PadicInt.toZModPow 1 x = 2
  · rw [if_pos hx]
    have he : padicAffineBranch 1 (padicOddPredecessor x) = x := by
      rw [padicAffineBranch_one_eq_syracuseJ]
      exact syracuseJ_padicOddPredecessor hx
    calc
      _ = padicOddLift (canonicalPadicRho k)
          (padicAffineBranch 1 (padicOddPredecessor x)) := congrArg _ he.symm
      _ = _ := padicOddLift_apply_branch _ _
  · rw [if_neg hx]
    apply padicOddLift_eq_zero
    rintro ⟨y, rfl⟩
    exact hx (by rw [padicAffineBranch_one_eq_syracuseJ, syracuseJ_mod_three])

theorem canonicalPadicRho_lift_recursion (k : ℕ) (x : ℤ_[3]) :
    canonicalPadicRho (k + 1) x =
      (1 / 2 : ℝ) * canonicalPadicRho (k + 1) (2 * x) +
      (3 / 2 : ℝ) * padicOddLift (canonicalPadicRho k) x := by
  rw [canonicalPadicRho_oddLift]
  exact canonicalPadicRho_successor_recursion k x

theorem padicOddLift_abs_sub_integral (f g : ℤ_[3] → ℝ) :
    (∫ x : ℤ_[3], |padicOddLift f x - padicOddLift g x| ∂padicThreeHaar) =
      (1 / 3 : ℝ) * ∫ x : ℤ_[3], |f x - g x| ∂padicThreeHaar := by
  calc
    _ = ∫ x : ℤ_[3], padicOddLift (fun y => |f y - g y|) x ∂padicThreeHaar := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change |padicOddLift f x - padicOddLift g x| = _
        rw [congrFun (padicOddLift_sub f g) x]
        exact congrFun (padicOddLift_comp_zero (fun y => f y - g y) abs abs_zero) x
    _ = _ := padicOddLift_integral _

theorem canonicalHaarDensity_stationary :
    canonicalHaarDensity =ᵐ[padicThreeHaar] fun x =>
      (1 / 2 : ℝ) * canonicalHaarDensity (2 * x) +
      (3 / 2 : ℝ) * padicOddLift canonicalHaarDensity x := by
  let f := canonicalHaarDensity
  let R : ℤ_[3] → ℝ := fun x =>
    f x - (1 / 2 : ℝ) * f (2 * x) - (3 / 2 : ℝ) * padicOddLift f x
  let E : ℕ → ℝ := fun k =>
    ∫ x : ℤ_[3], |canonicalPadicRho k x - f x| ∂padicThreeHaar
  have hf : Integrable f padicThreeHaar := canonicalHaarDensity_integrable
  have hd := padicThreeHaar_doubling_preserving.integrable_comp_of_integrable (g := f) hf
  have hl := (padicOddLift_integrable_iff f).mpr hf
  have hR : Integrable R padicThreeHaar :=
    (hf.sub (hd.const_mul (1 / 2 : ℝ))).sub (hl.const_mul (3 / 2 : ℝ))
  have hbound (k : ℕ) :
      (∫ x : ℤ_[3], |R x| ∂padicThreeHaar) ≤ (3 / 2 : ℝ) * E (k + 1) + (1 / 2 : ℝ) * E k := by
    have h0 : Integrable (fun x => canonicalPadicRho (k + 1) x - f x) padicThreeHaar :=
      (canonicalPadicRho_integrable padicThreeHaar (k + 1)).sub hf
    have h1 := padicThreeHaar_doubling_preserving.integrable_comp_of_integrable
      (g := fun y => canonicalPadicRho (k + 1) y - f y) h0
    have h2 : Integrable (fun x => padicOddLift (canonicalPadicRho k) x - padicOddLift f x)
        padicThreeHaar := ((padicOddLift_integrable_iff (canonicalPadicRho k)).mpr
      (canonicalPadicRho_integrable padicThreeHaar k)).sub hl
    have hpt (x : ℤ_[3]) : |R x| ≤
        |canonicalPadicRho (k + 1) x - f x| +
        (1 / 2 : ℝ) * |canonicalPadicRho (k + 1) (2 * x) - f (2 * x)| +
        (3 / 2 : ℝ) * |padicOddLift (canonicalPadicRho k) x - padicOddLift f x| := by
      have he : R x =
          -(canonicalPadicRho (k + 1) x - f x) +
          (1 / 2 : ℝ) * (canonicalPadicRho (k + 1) (2 * x) - f (2 * x)) +
          (3 / 2 : ℝ) * (padicOddLift (canonicalPadicRho k) x - padicOddLift f x) := by
        dsimp [R]
        rw [canonicalPadicRho_lift_recursion]
        ring
      rw [he]
      calc
        _ ≤ |-(canonicalPadicRho (k + 1) x - f x)| +
            |(1 / 2 : ℝ) * (canonicalPadicRho (k + 1) (2 * x) - f (2 * x))| +
            |(3 / 2 : ℝ) * (padicOddLift (canonicalPadicRho k) x - padicOddLift f x)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ = _ := by rw [abs_neg, abs_mul, abs_mul]; norm_num
    calc
      _ ≤ ∫ x : ℤ_[3],
          |canonicalPadicRho (k + 1) x - f x| +
          (1 / 2 : ℝ) * |canonicalPadicRho (k + 1) (2 * x) - f (2 * x)| +
          (3 / 2 : ℝ) * |padicOddLift (canonicalPadicRho k) x - padicOddLift f x|
            ∂padicThreeHaar :=
        integral_mono hR.abs ((h0.abs.add (h1.abs.const_mul _)).add (h2.abs.const_mul _)) hpt
      _ = (3 / 2 : ℝ) * E (k + 1) + (1 / 2 : ℝ) * E k := by
        have hadd0 := integral_add h0.abs (h1.abs.const_mul (1 / 2 : ℝ))
        have hadd1 := integral_add (h0.abs.add (h1.abs.const_mul (1 / 2 : ℝ)))
          (h2.abs.const_mul (3 / 2 : ℝ))
        simp only [Pi.add_apply, Function.comp_apply] at hadd0 hadd1
        rw [hadd1, hadd0, integral_const_mul, integral_const_mul,
          padicThreeHaar_doubling_preserving.integral_comp padicThree_doubling_measurableEmbedding
            (fun y => |canonicalPadicRho (k + 1) y - f y|),
          padicOddLift_abs_sub_integral]
        dsimp [E]
        ring
  have hE : Tendsto E atTop (𝓝 0) := canonicalHaarDensity_L1_tendsto
  have ht : Tendsto (fun k => (3 / 2 : ℝ) * E (k + 1) + (1 / 2 : ℝ) * E k)
      atTop (𝓝 0) := by
    simpa using ((hE.comp (tendsto_add_atTop_nat 1)).const_mul (3 / 2 : ℝ)).add
      (hE.const_mul (1 / 2 : ℝ))
  have hz : (∫ x : ℤ_[3], |R x| ∂padicThreeHaar) = 0 :=
    le_antisymm (ge_of_tendsto' ht hbound) (integral_nonneg fun x => abs_nonneg (R x))
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ fun x => abs_nonneg (R x)) hR.abs).mp hz
  filter_upwards [hae] with x hx
  have hr := abs_eq_zero.mp hx
  dsimp [R, f] at hr
  linarith

#print axioms canonicalHaarDensity_measurable
#print axioms canonicalHaarDensity_stationary

end Erdos1135.Tao
