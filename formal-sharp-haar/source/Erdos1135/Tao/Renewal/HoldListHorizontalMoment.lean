import Erdos1135.Tao.Renewal.Lemma77PotentialCore
import Erdos1135.Tao.Renewal.Prop78Case1Scalar

/-!
# Horizontal Exponential Moments of IID Hold Lists

This low leaf proves the exact horizontal MGF of a finite iid Hold list.  The
proof remains in `ENNReal` until the full countable expectation is known to be
finite, then projects the result to a summable real series.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Lemma77

private noncomputable def pmfENNExpectation
    {alpha : Type*} (p : PMF alpha) (F : alpha → ENNReal) : ENNReal :=
  ∑' x, p x * F x

private theorem pmfENNExpectation_map
    {alpha beta : Type*} (p : PMF alpha) (f : alpha → beta)
    (G : beta → ENNReal) :
    pmfENNExpectation (p.map f) G =
      pmfENNExpectation p (G ∘ f) := by
  classical
  unfold pmfENNExpectation
  calc
    (∑' y, (p.map f) y * G y) =
        ∑' y, (∑' x, if y = f x then p x else 0) * G y := by
      apply tsum_congr
      intro y
      rw [PMF.map_apply]
    _ = ∑' y, ∑' x, (if y = f x then p x else 0) * G y := by
      apply tsum_congr
      intro y
      rw [ENNReal.tsum_mul_right]
    _ = ∑' x, ∑' y, (if y = f x then p x else 0) * G y := by
      rw [ENNReal.tsum_comm]
    _ = ∑' x, p x * G (f x) := by
      apply tsum_congr
      intro x
      rw [tsum_eq_single (f x)]
      · simp
      · intro y hy
        simp [hy]
    _ = ∑' x, p x * (G ∘ f) x := by rfl

private theorem pmfENNExpectation_bind
    {alpha beta : Type*} (p : PMF alpha) (q : alpha → PMF beta)
    (G : beta → ENNReal) :
    pmfENNExpectation (p.bind q) G =
      ∑' x, p x * pmfENNExpectation (q x) G := by
  classical
  unfold pmfENNExpectation
  calc
    (∑' y, (p.bind q) y * G y) =
        ∑' y, (∑' x, p x * q x y) * G y := by
      apply tsum_congr
      intro y
      rw [PMF.bind_apply]
    _ = ∑' y, ∑' x, (p x * q x y) * G y := by
      apply tsum_congr
      intro y
      rw [ENNReal.tsum_mul_right]
    _ = ∑' x, ∑' y, (p x * q x y) * G y := by
      rw [ENNReal.tsum_comm]
    _ = ∑' x, p x * ∑' y, q x y * G y := by
      apply tsum_congr
      intro x
      calc
        (∑' y, (p x * q x y) * G y) =
            ∑' y, p x * (q x y * G y) := by
          apply tsum_congr
          intro y
          ac_rfl
        _ = p x * ∑' y, q x y * G y := ENNReal.tsum_mul_left

/-- The native one-Hold horizontal moment is the positive Geom(4) MGF. -/
theorem taoSection7HoldPMF_horizontalExpMoment_ennreal
    {t : ℝ} (hadm : 3 * Real.exp t < 4) :
    (∑' h : TaoSection7RenewalPoint,
      taoSection7HoldPMF h *
        ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ)))) =
      ENNReal.ofReal (taoSection7Geom4ExpMoment t) := by
  let W : ℕ+ → ENNReal := fun r =>
    ENNReal.ofReal (Real.exp (t * ((r : ℕ) : ℝ)))
  have hmap := taoSection7HoldPMF_map_j_eq_geom4PNat_checked
  unfold taoSection7HoldPMF_map_j_eq_geom4PNat at hmap
  calc
    (∑' h : TaoSection7RenewalPoint,
        taoSection7HoldPMF h *
          ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ)))) =
        pmfENNExpectation taoSection7HoldPMF (W ∘ fun h => h.j) := by
      rfl
    _ = pmfENNExpectation (taoSection7HoldPMF.map fun h => h.j) W :=
      (pmfENNExpectation_map taoSection7HoldPMF (fun h => h.j) W).symm
    _ = pmfENNExpectation geom4PNat W := by rw [hmap]
    _ = ENNReal.ofReal (taoSection7Geom4ExpMoment t) := by
      unfold pmfENNExpectation taoSection7Geom4ExpMoment W
      rw [ENNReal.ofReal_tsum_of_nonneg]
      · apply tsum_congr
        intro r
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (PMF.apply_ne_top geom4PNat r)]
      · intro r
        exact mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
      · exact summable_geom4PNat_mul_exp hadm

private theorem horizontalExpWeight_cons
    (t : ℝ) (N : ℕ) (h : TaoSection7RenewalPoint)
    (hs : List TaoSection7RenewalPoint) :
    ENNReal.ofReal
        (Real.exp (t *
          (lemma77HoldPrefixHorizontalDelta (N + 1) (h :: hs) : ℝ))) =
      ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ))) *
        ENNReal.ofReal
          (Real.exp (t * (lemma77HoldPrefixHorizontalDelta N hs : ℝ))) := by
  rw [show
    (lemma77HoldPrefixHorizontalDelta (N + 1) (h :: hs) : ℝ) =
      ((h.j : ℕ) : ℝ) +
        (lemma77HoldPrefixHorizontalDelta N hs : ℝ) by
      simp [lemma77HoldPrefixHorizontalDelta]]
  rw [mul_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Exact native horizontal MGF of a length-`N` iid Hold list. -/
theorem taoSection7HoldListPMF_horizontalExpMoment_ennreal
    (N : ℕ) {t : ℝ} (hadm : 3 * Real.exp t < 4) :
    (∑' hs : List TaoSection7RenewalPoint,
      taoSection7HoldListPMF N hs *
        ENNReal.ofReal
          (Real.exp
            (t * (lemma77HoldPrefixHorizontalDelta N hs : ℝ)))) =
      ENNReal.ofReal (taoSection7Geom4ExpMoment t) ^ N := by
  induction N with
  | zero =>
      rw [tsum_eq_single []]
      · simp [taoSection7HoldListPMF, lemma77HoldPrefixHorizontalDelta]
      · intro hs hne
        simp [taoSection7HoldListPMF, hne]
  | succ N ih =>
      let W : List TaoSection7RenewalPoint → ENNReal := fun hs =>
        ENNReal.ofReal
          (Real.exp
            (t * (lemma77HoldPrefixHorizontalDelta (N + 1) hs : ℝ)))
      let WT : List TaoSection7RenewalPoint → ENNReal := fun hs =>
        ENNReal.ofReal
          (Real.exp (t * (lemma77HoldPrefixHorizontalDelta N hs : ℝ)))
      calc
        (∑' hs : List TaoSection7RenewalPoint,
            taoSection7HoldListPMF (N + 1) hs * W hs) =
            pmfENNExpectation
              (taoSection7HoldPMF.bind fun h =>
                (taoSection7HoldListPMF N).map fun hs => h :: hs) W := by
          rfl
        _ = ∑' h, taoSection7HoldPMF h *
            pmfENNExpectation
              ((taoSection7HoldListPMF N).map fun hs => h :: hs) W :=
          pmfENNExpectation_bind _ _ _
        _ = ∑' h, taoSection7HoldPMF h *
            pmfENNExpectation (taoSection7HoldListPMF N)
              (W ∘ fun hs => h :: hs) := by
          apply tsum_congr
          intro h
          rw [pmfENNExpectation_map]
        _ = ∑' h, taoSection7HoldPMF h *
            (ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ))) *
              pmfENNExpectation (taoSection7HoldListPMF N) WT) := by
          apply tsum_congr
          intro h
          congr 1
          unfold pmfENNExpectation
          calc
            (∑' hs, taoSection7HoldListPMF N hs *
                (W ∘ fun hs => h :: hs) hs) =
                ∑' hs, taoSection7HoldListPMF N hs *
                  (ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ))) *
                    WT hs) := by
              apply tsum_congr
              intro hs
              dsimp only [Function.comp_apply, W, WT]
              rw [horizontalExpWeight_cons]
            _ = ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ))) *
                ∑' hs, taoSection7HoldListPMF N hs * WT hs := by
              calc
                (∑' hs, taoSection7HoldListPMF N hs *
                    (ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ))) *
                      WT hs)) =
                    ∑' hs, ENNReal.ofReal
                      (Real.exp (t * ((h.j : ℕ) : ℝ))) *
                        (taoSection7HoldListPMF N hs * WT hs) := by
                  apply tsum_congr
                  intro hs
                  ac_rfl
                _ = ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ))) *
                    ∑' hs, taoSection7HoldListPMF N hs * WT hs :=
                  ENNReal.tsum_mul_left
        _ = (∑' h, taoSection7HoldPMF h *
              ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ)))) *
            pmfENNExpectation (taoSection7HoldListPMF N) WT := by
          calc
            (∑' h, taoSection7HoldPMF h *
                (ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ))) *
                  pmfENNExpectation (taoSection7HoldListPMF N) WT)) =
                ∑' h, (taoSection7HoldPMF h *
                  ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ)))) *
                    pmfENNExpectation (taoSection7HoldListPMF N) WT := by
              apply tsum_congr
              intro h
              ac_rfl
            _ = (∑' h, taoSection7HoldPMF h *
                  ENNReal.ofReal (Real.exp (t * ((h.j : ℕ) : ℝ)))) *
                pmfENNExpectation (taoSection7HoldListPMF N) WT :=
              ENNReal.tsum_mul_right
        _ = ENNReal.ofReal (taoSection7Geom4ExpMoment t) *
            (ENNReal.ofReal (taoSection7Geom4ExpMoment t) ^ N) := by
          rw [taoSection7HoldPMF_horizontalExpMoment_ennreal hadm]
          rw [show pmfENNExpectation (taoSection7HoldListPMF N) WT =
              ENNReal.ofReal (taoSection7Geom4ExpMoment t) ^ N by
            simpa [pmfENNExpectation, WT] using ih]
        _ = ENNReal.ofReal (taoSection7Geom4ExpMoment t) ^ (N + 1) := by
          rw [pow_succ']

theorem taoSection7Geom4ExpMoment_nonneg (t : ℝ) :
    0 ≤ taoSection7Geom4ExpMoment t := by
  unfold taoSection7Geom4ExpMoment
  exact tsum_nonneg fun r =>
    mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le

/-- Real summability and exact value of the iid Hold-list horizontal MGF. -/
theorem taoSection7HoldListPMF_horizontalExpMoment
    (N : ℕ) {t : ℝ} (hadm : 3 * Real.exp t < 4) :
    Summable (fun hs : List TaoSection7RenewalPoint =>
      (taoSection7HoldListPMF N hs).toReal *
        Real.exp
          (t * (lemma77HoldPrefixHorizontalDelta N hs : ℝ))) ∧
    (∑' hs : List TaoSection7RenewalPoint,
      (taoSection7HoldListPMF N hs).toReal *
        Real.exp
          (t * (lemma77HoldPrefixHorizontalDelta N hs : ℝ))) =
      taoSection7Geom4ExpMoment t ^ N := by
  let g : List TaoSection7RenewalPoint → ENNReal := fun hs =>
    taoSection7HoldListPMF N hs *
      ENNReal.ofReal
        (Real.exp (t * (lemma77HoldPrefixHorizontalDelta N hs : ℝ)))
  have hnative := taoSection7HoldListPMF_horizontalExpMoment_ennreal N hadm
  have hfinite : (∑' hs, g hs) ≠ ⊤ := by
    rw [show (∑' hs, g hs) =
      ENNReal.ofReal (taoSection7Geom4ExpMoment t) ^ N by
        simpa [g] using hnative]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hsumToReal : Summable fun hs => (g hs).toReal :=
    ENNReal.summable_toReal hfinite
  have hterm : ∀ hs,
      (taoSection7HoldListPMF N hs).toReal *
          Real.exp (t * (lemma77HoldPrefixHorizontalDelta N hs : ℝ)) =
        (g hs).toReal := by
    intro hs
    simp [g, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hsum := hsumToReal.congr fun hs => (hterm hs).symm
  refine ⟨hsum, ?_⟩
  calc
    (∑' hs : List TaoSection7RenewalPoint,
        (taoSection7HoldListPMF N hs).toReal *
          Real.exp
            (t * (lemma77HoldPrefixHorizontalDelta N hs : ℝ))) =
        ∑' hs, (g hs).toReal := tsum_congr hterm
    _ = (∑' hs, g hs).toReal := by
      rw [ENNReal.tsum_toReal_eq]
      intro hs
      exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top
    _ = (ENNReal.ofReal (taoSection7Geom4ExpMoment t) ^ N).toReal := by
      rw [show (∑' hs, g hs) =
        ENNReal.ofReal (taoSection7Geom4ExpMoment t) ^ N by
          simpa [g] using hnative]
    _ = taoSection7Geom4ExpMoment t ^ N := by
      rw [ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (taoSection7Geom4ExpMoment_nonneg t)]

end TaoSection7Lemma77

end

end Tao
end Erdos1135
