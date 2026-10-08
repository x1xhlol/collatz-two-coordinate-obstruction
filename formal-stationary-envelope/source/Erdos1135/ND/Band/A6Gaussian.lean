/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Band.A6StrictMultiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# A6 Centered Gaussian Rectangle

This neutral leaf connects the checked strict-level multiplicities to the
centered Gaussian used in frozen v10 A6.  It first owns the exact signed
`Icc`-to-`range` reindex and separates the multiplicity error from the
`1 / delta` rectangle term.  The later analytic declarations keep the
finite Gaussian tail visible.
-/

namespace Erdos1135
namespace ND

/-- The signed interval `[-R,R]` enumerated from left to right by a natural
range.  In particular, the formula remains exact when `R = 0`. -/
theorem sum_Icc_neg_nat_eq_sum_range (R : ℕ) (f : ℤ → ℝ) :
    ∑ d ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), f d =
      ∑ i ∈ Finset.range (2 * R + 1), f (-(R : ℤ) + (i : ℤ)) := by
  rw [Int.Icc_eq_finset_map]
  simp only [Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply]
  have hlength :
      (((R : ℤ) + 1 - (-(R : ℤ))).toNat) = 2 * R + 1 := by
    have hcast : (R : ℤ) + 1 - (-(R : ℤ)) = ((2 * R + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast]
    omega
  rw [hlength]

/-- Exact separation of a full-tube level sum into its mean-spacing term and
the checked strict-multiplicity errors.  This is algebraic and needs no
unclipped-tube hypothesis; `hlo` enters only when the error is bounded. -/
theorem sum_ndA5FullTube_sub_invDelta_mul_sum_Icc_eq_sum_strictError
    {A W : ℝ} (hW : 0 < W) (phi : ℤ → ℝ) :
    (∑ nu ∈ ndA5FullTube A W, phi (ndA5StrictAffineSweep A nu)) -
        (1 / ndA5PhaseDelta) *
          ∑ d ∈ Finset.Icc (-(ndA5TubeRadius W : ℤ))
            (ndA5TubeRadius W : ℤ), phi d =
      ∑ i ∈ Finset.range (2 * ndA5TubeRadius W + 1),
        ndA6StrictMultiplicityError A W
            (-(ndA5TubeRadius W : ℤ) + (i : ℤ)) *
          phi (-(ndA5TubeRadius W : ℤ) + (i : ℤ)) := by
  rw [sum_ndA5FullTube_eq_sum_ndA6StrictLevelMultiplicity hW]
  rw [sum_Icc_neg_nat_eq_sum_range, sum_Icc_neg_nat_eq_sum_range]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold ndA6StrictMultiplicityError
  ring

/-- The normalized centered Gaussian with scale parameter `S`. -/
noncomputable def ndA6Gaussian (S x : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * S))⁻¹ *
    Real.exp (-(x ^ 2 / (4 * S)))

/-- The centered Gaussian is nonnegative. -/
theorem ndA6Gaussian_nonneg (S x : ℝ) :
    0 ≤ ndA6Gaussian S x := by
  unfold ndA6Gaussian
  positivity

/-- The centered Gaussian is even. -/
theorem ndA6Gaussian_neg (S x : ℝ) :
    ndA6Gaussian S (-x) = ndA6Gaussian S x := by
  unfold ndA6Gaussian
  congr 2
  ring

/-- The Gaussian peak is its normalizing prefactor. -/
theorem ndA6Gaussian_zero (S : ℝ) :
    ndA6Gaussian S 0 = (Real.sqrt (4 * Real.pi * S))⁻¹ := by
  simp [ndA6Gaussian]

/-- For positive variance, the centered Gaussian increases on the negative
half-line. -/
theorem ndA6Gaussian_monotoneOn_Iic {S : ℝ} (hS : 0 < S) :
    MonotoneOn (ndA6Gaussian S) (Set.Iic 0) := by
  intro x hx y hy hxy
  have hprod : 0 ≤ (y - x) * (-(x + y)) :=
    mul_nonneg (sub_nonneg.mpr hxy) (neg_nonneg.mpr (add_nonpos hx hy))
  have hsq : y ^ 2 ≤ x ^ 2 := by
    nlinarith
  have hden : 0 < 4 * S := by positivity
  have hexp :
      Real.exp (-(x ^ 2 / (4 * S))) ≤
        Real.exp (-(y ^ 2 / (4 * S))) := by
    apply Real.exp_le_exp.mpr
    have := div_le_div_of_nonneg_right hsq hden.le
    linarith
  unfold ndA6Gaussian
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- For positive variance, the centered Gaussian decreases on the positive
half-line. -/
theorem ndA6Gaussian_antitoneOn_Ici {S : ℝ} (hS : 0 < S) :
    AntitoneOn (ndA6Gaussian S) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hprod : 0 ≤ (y - x) * (y + x) :=
    mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hy hx)
  have hsq : x ^ 2 ≤ y ^ 2 := by
    nlinarith
  have hden : 0 < 4 * S := by positivity
  have hexp :
      Real.exp (-(y ^ 2 / (4 * S))) ≤
        Real.exp (-(x ^ 2 / (4 * S))) := by
    apply Real.exp_le_exp.mpr
    have := div_le_div_of_nonneg_right hsq hden.le
    linarith
  unfold ndA6Gaussian
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- The normalized centered Gaussian is integrable at positive variance. -/
theorem ndA6Gaussian_integrable {S : ℝ} (hS : 0 < S) :
    MeasureTheory.Integrable (ndA6Gaussian S) := by
  have hb : 0 < 1 / (4 * S) := by positivity
  have h := (integrable_exp_neg_mul_sq hb).const_mul
    (Real.sqrt (4 * Real.pi * S))⁻¹
  convert h using 1
  ext x
  unfold ndA6Gaussian
  congr 2
  ring

/-- The normalized centered Gaussian has total integral one. -/
theorem integral_ndA6Gaussian_eq_one {S : ℝ} (hS : 0 < S) :
    ∫ x : ℝ, ndA6Gaussian S x = 1 := by
  have harg : Real.pi / (1 / (4 * S)) = 4 * Real.pi * S := by
    field_simp [hS.ne']
  have hfun : ndA6Gaussian S = fun x : ℝ =>
      (Real.sqrt (4 * Real.pi * S))⁻¹ *
        Real.exp (-(1 / (4 * S)) * x ^ 2) := by
    funext x
    unfold ndA6Gaussian
    congr 2
    ring
  rw [hfun, MeasureTheory.integral_const_mul, integral_gaussian, harg]
  have hpos : 0 < Real.sqrt (4 * Real.pi * S) := by positivity
  field_simp [hpos.ne']

/-- The positive Gaussian tail starting strictly after `r`. -/
noncomputable def ndA6GaussianTail (S r : ℝ) : ℝ :=
  ∫ x in Set.Ioi r, ndA6Gaussian S x

/-- Gaussian tails are nonnegative. -/
theorem ndA6GaussianTail_nonneg (S r : ℝ) :
    0 ≤ ndA6GaussianTail S r := by
  unfold ndA6GaussianTail
  exact MeasureTheory.integral_nonneg (fun x => ndA6Gaussian_nonneg S x)

/-- At positive variance, the positive half-line carries half of the
normalized Gaussian mass. -/
theorem ndA6GaussianTail_zero {S : ℝ} (hS : 0 < S) :
    ndA6GaussianTail S 0 = 1 / 2 := by
  have harg : Real.pi / (1 / (4 * S)) = 4 * Real.pi * S := by
    field_simp [hS.ne']
  have hfun : ndA6Gaussian S = fun x : ℝ =>
      (Real.sqrt (4 * Real.pi * S))⁻¹ *
        Real.exp (-(1 / (4 * S)) * x ^ 2) := by
    funext x
    unfold ndA6Gaussian
    congr 2
    ring
  unfold ndA6GaussianTail
  rw [hfun, MeasureTheory.integral_const_mul, integral_gaussian_Ioi, harg]
  have hpos : 0 < Real.sqrt (4 * Real.pi * S) := by positivity
  field_simp [hpos.ne']

/-- The elementary Gaussian tail bound obtained from the tangent exponential
at a positive radius. -/
theorem ndA6GaussianTail_le_two_mul_div_mul
    {S r : ℝ} (hS : 0 < S) (hr : 0 < r) :
    ndA6GaussianTail S r ≤
      (2 * S / r) * ndA6Gaussian S r := by
  let a : ℝ := r / (2 * S)
  let C : ℝ := ndA6Gaussian S r * Real.exp (a * r)
  let g : ℝ → ℝ := fun x => C * Real.exp ((-a) * x)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioi r) :
      ndA6Gaussian S x ≤ g x := by
    have hdiff :
        (-(r ^ 2 / (4 * S)) - a * (x - r)) -
            (-(x ^ 2 / (4 * S))) = (x - r) ^ 2 / (4 * S) := by
      dsimp [a]
      field_simp [hS.ne']
      ring
    have hexponent :
        -(x ^ 2 / (4 * S)) ≤ -(r ^ 2 / (4 * S)) - a * (x - r) := by
      have hnonneg : 0 ≤ (x - r) ^ 2 / (4 * S) := by positivity
      linarith [hdiff]
    have hexp := Real.exp_le_exp.mpr hexponent
    unfold ndA6Gaussian
    calc
      (Real.sqrt (4 * Real.pi * S))⁻¹ *
          Real.exp (-(x ^ 2 / (4 * S))) ≤
          (Real.sqrt (4 * Real.pi * S))⁻¹ *
            Real.exp (-(r ^ 2 / (4 * S)) - a * (x - r)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = g x := by
        dsimp [g, C]
        unfold ndA6Gaussian
        rw [show -(r ^ 2 / (4 * S)) - a * (x - r) =
            (-(r ^ 2 / (4 * S)) + a * r) + (-a) * x by ring,
          Real.exp_add, Real.exp_add]
        ring
  have hgauss : MeasureTheory.IntegrableOn
      (ndA6Gaussian S) (Set.Ioi r) :=
    (ndA6Gaussian_integrable hS).integrableOn
  have hexpInt : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.exp ((-a) * x)) (Set.Ioi r) :=
    integrableOn_exp_mul_Ioi (by linarith) r
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi r) := by
    dsimp [g]
    exact MeasureTheory.Integrable.const_mul hexpInt C
  have hintegral : ndA6GaussianTail S r ≤
      ∫ x in Set.Ioi r, g x := by
    unfold ndA6GaussianTail
    apply MeasureTheory.integral_mono_ae hgauss hg
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpoint x hx
  calc
    ndA6GaussianTail S r ≤ ∫ x in Set.Ioi r, g x := hintegral
    _ = C * (-Real.exp ((-a) * r) / (-a)) := by
      dsimp [g]
      rw [MeasureTheory.integral_const_mul,
        integral_exp_mul_Ioi (by linarith : -a < 0) r]
    _ = (2 * S / r) * ndA6Gaussian S r := by
      dsimp [C]
      rw [neg_div_neg_eq]
      calc
        ndA6Gaussian S r * Real.exp (a * r) *
              (Real.exp ((-a) * r) / a) =
            ndA6Gaussian S r *
              (Real.exp (a * r) * Real.exp ((-a) * r)) / a := by ring
        _ = ndA6Gaussian S r / a := by
          rw [← Real.exp_add]
          simp
        _ = (2 * S / r) * ndA6Gaussian S r := by
          dsimp [a]
          field_simp [hr.ne', hS.ne']

private theorem sum_Icc_ndA6Gaussian_eq_peak_add_two_sum_pos
    (S : ℝ) (R : ℕ) :
    (∑ d ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        ndA6Gaussian S (d : ℝ)) =
      ndA6Gaussian S 0 +
        2 * ∑ i ∈ Finset.range R, ndA6Gaussian S ((i + 1 : ℕ) : ℝ) := by
  let f : ℤ → ℝ := fun d => ndA6Gaussian S (d : ℝ)
  have heven : Function.Even f := by
    intro d
    dsimp [f]
    push_cast
    exact ndA6Gaussian_neg S (d : ℝ)
  rw [Finset.sum_Icc_of_even_eq_range heven R]
  simp only [nsmul_eq_mul]
  rw [Finset.sum_range_succ']
  dsimp [f]
  norm_num
  ring

/-- Finite centered Gaussian rectangles differ from total mass one by at most
one peak plus the two positive tails beyond the signed radius.  This form is
valid without a positive-radius assumption, including `R = 0`. -/
theorem abs_sum_Icc_ndA6Gaussian_sub_one_le_peak_add_two_tail
    {S : ℝ} (hS : 0 < S) (R : ℕ) :
    |(∑ d ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        ndA6Gaussian S (d : ℝ)) - 1| ≤
      ndA6Gaussian S 0 + 2 * ndA6GaussianTail S (R : ℝ) := by
  let phi : ℝ → ℝ := ndA6Gaussian S
  let P : ℝ :=
    ∑ i ∈ Finset.range R, phi ((i + 1 : ℕ) : ℝ)
  let I : ℝ := ∫ x in (0 : ℝ)..(R : ℝ), phi x
  let T : ℝ := ndA6GaussianTail S (R : ℝ)
  have hsum :
      (∑ d ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
          ndA6Gaussian S (d : ℝ)) = ndA6Gaussian S 0 + 2 * P := by
    simpa only [P, phi] using
      (sum_Icc_ndA6Gaussian_eq_peak_add_two_sum_pos S R)
  have hanti : AntitoneOn phi (Set.Icc 0 (0 + (R : ℝ))) := by
    apply (ndA6Gaussian_antitoneOn_Ici hS).mono
    intro x hx
    exact hx.1
  have hP_le_I : P ≤ I := by
    dsimp [P, I, phi]
    simpa only [zero_add] using hanti.sum_le_integral
  have hI_le_peak_add_P : I ≤ ndA6Gaussian S 0 + P := by
    have hleft := hanti.integral_le_sum
    dsimp [I, phi] at hleft
    calc
      I ≤ ∑ i ∈ Finset.range R, ndA6Gaussian S (i : ℝ) := by
        simpa only [I, phi, zero_add] using hleft
      _ ≤ ndA6Gaussian S 0 + P := by
        have hpeakP : ndA6Gaussian S 0 + P =
            ∑ i ∈ Finset.range (R + 1), ndA6Gaussian S (i : ℝ) := by
          rw [Finset.sum_range_succ']
          dsimp [P, phi]
          norm_num
          ring
        rw [hpeakP]
        rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_right (ndA6Gaussian_nonneg S (R : ℝ))
  have hsplit : I + T = 1 / 2 := by
    have hint := ndA6Gaussian_integrable hS
    have htailSplit := intervalIntegral.integral_interval_add_Ioi
      (a := (0 : ℝ)) (b := (R : ℝ))
      hint.integrableOn hint.integrableOn
    have hzeroTail := ndA6GaussianTail_zero hS
    unfold ndA6GaussianTail at hzeroTail
    dsimp [I, T, phi, ndA6GaussianTail]
    rw [hzeroTail] at htailSplit
    exact htailSplit
  have hT : 0 ≤ T := by
    dsimp [T]
    exact ndA6GaussianTail_nonneg S (R : ℝ)
  rw [hsum, abs_le]
  constructor
  · linarith
  · linarith

/-- At a positive natural radius, the finite Gaussian rectangle error has an
explicit endpoint tail. -/
theorem abs_sum_Icc_ndA6Gaussian_sub_one_le_peak_add_explicit_tail
    {S : ℝ} (hS : 0 < S) {R : ℕ} (hR : 0 < R) :
    |(∑ d ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        ndA6Gaussian S (d : ℝ)) - 1| ≤
      ndA6Gaussian S 0 +
        (4 * S / (R : ℝ)) * ndA6Gaussian S (R : ℝ) := by
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hrectangle :=
    abs_sum_Icc_ndA6Gaussian_sub_one_le_peak_add_two_tail hS R
  have htail := ndA6GaussianTail_le_two_mul_div_mul hS hRreal
  calc
    |(∑ d ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        ndA6Gaussian S (d : ℝ)) - 1| ≤
        ndA6Gaussian S 0 + 2 * ndA6GaussianTail S (R : ℝ) :=
      hrectangle
    _ ≤ ndA6Gaussian S 0 +
        (4 * S / (R : ℝ)) * ndA6Gaussian S (R : ℝ) := by
      apply add_le_add le_rfl
      calc
        2 * ndA6GaussianTail S (R : ℝ) ≤
            2 * ((2 * S / (R : ℝ)) *
              ndA6Gaussian S (R : ℝ)) :=
          mul_le_mul_of_nonneg_left htail (by norm_num)
        _ = (4 * S / (R : ℝ)) *
            ndA6Gaussian S (R : ℝ) := by ring

/-- The checked strict multiplicity errors contribute at most twice the
Gaussian peak.  This term deliberately carries neither a radius factor nor
`1 / delta`. -/
theorem abs_sum_ndA5FullTube_gaussian_sub_invDelta_mul_sum_Icc_le_two_peak
    {A W S : ℝ} (hW : 0 < W) (hlo : 0 < ndA5TubeLo A W)
    (hS : 0 < S) :
    |(∑ nu ∈ ndA5FullTube A W,
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)) -
        (1 / ndA5PhaseDelta) *
          ∑ d ∈ Finset.Icc (-(ndA5TubeRadius W : ℤ))
            (ndA5TubeRadius W : ℤ), ndA6Gaussian S (d : ℝ)| ≤
      2 * ndA6Gaussian S 0 := by
  let R : ℕ := ndA5TubeRadius W
  let omega : ℕ → ℝ := fun i =>
    ndA6Gaussian S ((i : ℝ) - (R : ℝ))
  rw [sum_ndA5FullTube_sub_invDelta_mul_sum_Icc_eq_sum_strictError
    hW (fun d => ndA6Gaussian S (d : ℝ))]
  have hsum :
      (∑ i ∈ Finset.range (2 * R + 1),
          ndA6StrictMultiplicityError A W (-(R : ℤ) + (i : ℤ)) *
            ndA6Gaussian S ((-(R : ℤ) + (i : ℤ) : ℤ) : ℝ)) =
        ∑ i ∈ Finset.range (2 * R + 1),
          omega i *
            ndA6StrictMultiplicityError A W (-(R : ℤ) + (i : ℤ)) := by
    apply Finset.sum_congr rfl
    intro i _
    have harg :
        ((-(R : ℤ) + (i : ℤ) : ℤ) : ℝ) =
          (i : ℝ) - (R : ℝ) := by
      push_cast
      ring
    rw [harg]
    dsimp [omega]
    ring
  rw [hsum]
  have hcenter :=
    abs_sum_range_mul_ndA6StrictMultiplicityError_le_two_center
      hW hlo omega
  have hzero : 0 ≤ omega 0 := ndA6Gaussian_nonneg _ _
  have hend : 0 ≤ omega (2 * ndA5TubeRadius W) :=
    ndA6Gaussian_nonneg _ _
  have hup : ∀ i, i < ndA5TubeRadius W → omega i ≤ omega (i + 1) := by
    intro i hi
    apply ndA6Gaussian_monotoneOn_Iic hS
    · dsimp [omega]
      simp only [Set.mem_Iic]
      have hiNat : i ≤ R := by
        dsimp [R]
        omega
      have hiReal : (i : ℝ) ≤ (R : ℝ) := by exact_mod_cast hiNat
      linarith
    · dsimp [omega]
      simp only [Set.mem_Iic]
      have hiNat : i + 1 ≤ R := by
        dsimp [R]
        omega
      have hiReal : ((i + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by
        exact_mod_cast hiNat
      push_cast at hiReal
      push_cast
      linarith
    · dsimp [omega]
      push_cast
      linarith
  have hdown : ∀ i, ndA5TubeRadius W ≤ i →
      i < 2 * ndA5TubeRadius W → omega (i + 1) ≤ omega i := by
    intro i hiR hi
    apply ndA6Gaussian_antitoneOn_Ici hS
    · dsimp [omega]
      simp only [Set.mem_Ici]
      have hiNat : R ≤ i := by
        dsimp [R]
        exact hiR
      have hiReal : (R : ℝ) ≤ (i : ℝ) := by exact_mod_cast hiNat
      linarith
    · dsimp [omega]
      simp only [Set.mem_Ici]
      have hiNat : R ≤ i + 1 := by
        dsimp [R]
        omega
      have hiReal : (R : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
        exact_mod_cast hiNat
      push_cast at hiReal
      push_cast
      linarith
    · dsimp [omega]
      push_cast
      linarith
  have hbound := hcenter hzero hend hup hdown
  simpa [R, omega] using hbound

/-- Combining the native multiplicity error with the finite rectangle error
gives the neutral Gaussian full-tube estimate.  Only the rectangle-and-tail
bracket is multiplied by `1 / delta`. -/
theorem abs_sum_ndA5FullTube_gaussian_sub_invDelta_le_peak_add_tail
    {A W S : ℝ} (hW : 0 < W) (hlo : 0 < ndA5TubeLo A W)
    (hS : 0 < S) :
    |(∑ nu ∈ ndA5FullTube A W,
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)) -
        1 / ndA5PhaseDelta| ≤
      2 * ndA6Gaussian S 0 +
        (1 / ndA5PhaseDelta) *
          (ndA6Gaussian S 0 +
            2 * ndA6GaussianTail S (ndA5TubeRadius W : ℝ)) := by
  let lattice : ℝ :=
    ∑ d ∈ Finset.Icc (-(ndA5TubeRadius W : ℤ))
      (ndA5TubeRadius W : ℤ), ndA6Gaussian S (d : ℝ)
  have hmultiplicity :=
    abs_sum_ndA5FullTube_gaussian_sub_invDelta_mul_sum_Icc_le_two_peak
      hW hlo hS
  have hrectangle :=
    abs_sum_Icc_ndA6Gaussian_sub_one_le_peak_add_two_tail
      hS (ndA5TubeRadius W)
  have hinv : 0 ≤ 1 / ndA5PhaseDelta := by
    exact one_div_nonneg.mpr ndA5PhaseDelta_mem_Ioo.1.le
  change
    |(∑ nu ∈ ndA5FullTube A W,
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)) -
        1 / ndA5PhaseDelta| ≤ _
  calc
    |(∑ nu ∈ ndA5FullTube A W,
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)) -
        1 / ndA5PhaseDelta| =
        |((∑ nu ∈ ndA5FullTube A W,
              ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)) -
            (1 / ndA5PhaseDelta) * lattice) +
          ((1 / ndA5PhaseDelta) * lattice -
            1 / ndA5PhaseDelta)| := by
              congr 1
              ring
    _ ≤
        |(∑ nu ∈ ndA5FullTube A W,
              ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)) -
            (1 / ndA5PhaseDelta) * lattice| +
          |(1 / ndA5PhaseDelta) * lattice -
            1 / ndA5PhaseDelta| := abs_add_le _ _
    _ ≤ 2 * ndA6Gaussian S 0 +
          (1 / ndA5PhaseDelta) * |lattice - 1| := by
      apply add_le_add
      · simpa only [lattice] using hmultiplicity
      · calc
          |(1 / ndA5PhaseDelta) * lattice - 1 / ndA5PhaseDelta| =
              |(1 / ndA5PhaseDelta) * (lattice - 1)| := by
                congr 1
                ring
          _ = (1 / ndA5PhaseDelta) * |lattice - 1| := by
            rw [abs_mul, abs_of_nonneg hinv]
          _ ≤ (1 / ndA5PhaseDelta) * |lattice - 1| := le_rfl
    _ ≤ 2 * ndA6Gaussian S 0 +
        (1 / ndA5PhaseDelta) *
          (ndA6Gaussian S 0 +
            2 * ndA6GaussianTail S (ndA5TubeRadius W : ℝ)) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left
          (by simpa only [lattice] using hrectangle) hinv)
        (2 * ndA6Gaussian S 0)

/-- The positive-radius neutral full-tube estimate with the Gaussian tail
made explicit.  The native multiplicity contribution remains independent of
`1 / delta`; only the finite rectangle contribution is scaled by it. -/
theorem abs_sum_ndA5FullTube_gaussian_sub_invDelta_le_explicit_tail
    {A W S : ℝ} (hW : 0 < W) (hlo : 0 < ndA5TubeLo A W)
    (hS : 0 < S) (hR : 0 < ndA5TubeRadius W) :
    |(∑ nu ∈ ndA5FullTube A W,
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)) -
        1 / ndA5PhaseDelta| ≤
      (2 + 1 / ndA5PhaseDelta) * ndA6Gaussian S 0 +
        (4 * S /
            (ndA5PhaseDelta * (ndA5TubeRadius W : ℝ))) *
          ndA6Gaussian S (ndA5TubeRadius W : ℝ) := by
  have hRreal : 0 < (ndA5TubeRadius W : ℝ) := by exact_mod_cast hR
  have hneutral :=
    abs_sum_ndA5FullTube_gaussian_sub_invDelta_le_peak_add_tail
      hW hlo hS
  have htail := ndA6GaussianTail_le_two_mul_div_mul hS hRreal
  have hinv : 0 ≤ 1 / ndA5PhaseDelta :=
    one_div_nonneg.mpr ndA5PhaseDelta_mem_Ioo.1.le
  have htwoTail :
      2 * ndA6GaussianTail S (ndA5TubeRadius W : ℝ) ≤
        (4 * S / (ndA5TubeRadius W : ℝ)) *
          ndA6Gaussian S (ndA5TubeRadius W : ℝ) := by
    calc
      2 * ndA6GaussianTail S (ndA5TubeRadius W : ℝ) ≤
          2 * ((2 * S / (ndA5TubeRadius W : ℝ)) *
            ndA6Gaussian S (ndA5TubeRadius W : ℝ)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = (4 * S / (ndA5TubeRadius W : ℝ)) *
          ndA6Gaussian S (ndA5TubeRadius W : ℝ) := by ring
  calc
    |(∑ nu ∈ ndA5FullTube A W,
          ndA6Gaussian S (ndA5StrictAffineSweep A nu : ℝ)) -
        1 / ndA5PhaseDelta| ≤
        2 * ndA6Gaussian S 0 +
          (1 / ndA5PhaseDelta) *
            (ndA6Gaussian S 0 +
              2 * ndA6GaussianTail S (ndA5TubeRadius W : ℝ)) :=
      hneutral
    _ ≤ 2 * ndA6Gaussian S 0 +
          (1 / ndA5PhaseDelta) *
            (ndA6Gaussian S 0 +
              (4 * S / (ndA5TubeRadius W : ℝ)) *
                ndA6Gaussian S (ndA5TubeRadius W : ℝ)) := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl htwoTail) hinv
    _ = (2 + 1 / ndA5PhaseDelta) * ndA6Gaussian S 0 +
        (4 * S /
            (ndA5PhaseDelta * (ndA5TubeRadius W : ℝ))) *
          ndA6Gaussian S (ndA5TubeRadius W : ℝ) := by
      field_simp [ndA5PhaseDelta_mem_Ioo.1.ne', hRreal.ne']
     ; ring

end ND
end Erdos1135
