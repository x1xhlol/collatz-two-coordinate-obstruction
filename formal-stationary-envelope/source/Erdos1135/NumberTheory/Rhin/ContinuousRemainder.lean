import Erdos1135.NumberTheory.Rhin.RemainderCells
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Continuous remainder bound for the literal Rhin polynomial

This module lifts the exact rational cell certificate to the real source
interval and consumes the production p. 162 polynomial directly.  The cells
partition the continuous integration variable; they are not a finite-height
phase table.  The 38-cell cover, raw base `239/1000`, and loss cap `20` are
derived exact G8 relaxations for Rhin's printed `-108` polynomial, not
parameters printed by Rhin and not a certificate for Wu's later `-104`
variant.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

open Polynomial MeasureTheory
open scoped BigOperators Interval

private theorem abs_le_of_between_abs
    {a x b M : ℝ} (hax : a ≤ x) (hxb : x ≤ b)
    (ha : |a| ≤ M) (hb : |b| ≤ M) : |x| ≤ M := by
  rw [abs_le]
  constructor
  · exact (neg_le_of_abs_le ha).trans hax
  · exact hxb.trans (le_of_abs_le hb)

private theorem abs_le_max_abs_of_between
    {a x b : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    |x| ≤ max |a| |b| := by
  exact abs_le_of_between_abs hax hxb (le_max_left _ _) (le_max_right _ _)

/-- An upward quadratic is trapped between its vertex and one endpoint, or
between the two endpoints when the vertex lies outside the cell. -/
private theorem quadratic_abs_le_cell
    (a v qv l x r M : ℝ)
    (ha : 0 < a) (hlx : l ≤ x) (hxr : x ≤ r)
    (hMl : |a * (l - v) ^ 2 + qv| ≤ M)
    (hMr : |a * (r - v) ^ 2 + qv| ≤ M)
    (hMv : l ≤ v → v ≤ r → |qv| ≤ M) :
    |a * (x - v) ^ 2 + qv| ≤ M := by
  by_cases hvl : v < l
  · have hL0 : 0 ≤ l - v := by linarith
    have hX0 : 0 ≤ x - v := by linarith
    have hR0 : 0 ≤ r - v := by linarith
    have hLX : (l - v) ^ 2 ≤ (x - v) ^ 2 :=
      (sq_le_sq₀ hL0 hX0).2 (by linarith)
    have hXR : (x - v) ^ 2 ≤ (r - v) ^ 2 :=
      (sq_le_sq₀ hX0 hR0).2 (by linarith)
    apply abs_le_of_between_abs
      (a := a * (l - v) ^ 2 + qv)
      (b := a * (r - v) ^ 2 + qv)
    · simpa [add_comm] using
        add_le_add_right (mul_le_mul_of_nonneg_left hLX ha.le) qv
    · simpa [add_comm] using
        add_le_add_right (mul_le_mul_of_nonneg_left hXR ha.le) qv
    · exact hMl
    · exact hMr
  · have hlv : l ≤ v := le_of_not_gt hvl
    by_cases hvr : r < v
    · have hR0 : 0 ≤ v - r := by linarith
      have hX0 : 0 ≤ v - x := by linarith
      have hL0 : 0 ≤ v - l := by linarith
      have hRX : (r - v) ^ 2 ≤ (x - v) ^ 2 := by
        calc
          (r - v) ^ 2 = (v - r) ^ 2 := by ring
          _ ≤ (v - x) ^ 2 := (sq_le_sq₀ hR0 hX0).2 (by linarith)
          _ = (x - v) ^ 2 := by ring
      have hXL : (x - v) ^ 2 ≤ (l - v) ^ 2 := by
        calc
          (x - v) ^ 2 = (v - x) ^ 2 := by ring
          _ ≤ (v - l) ^ 2 := (sq_le_sq₀ hX0 hL0).2 (by linarith)
          _ = (l - v) ^ 2 := by ring
      apply abs_le_of_between_abs
        (a := a * (r - v) ^ 2 + qv)
        (b := a * (l - v) ^ 2 + qv)
      · simpa [add_comm] using
          add_le_add_right (mul_le_mul_of_nonneg_left hRX ha.le) qv
      · simpa [add_comm] using
          add_le_add_right (mul_le_mul_of_nonneg_left hXL ha.le) qv
      · exact hMr
      · exact hMl
    · have hvr' : v ≤ r := le_of_not_gt hvr
      have hVertex := hMv hlv hvr'
      by_cases hxv : x ≤ v
      · have hX0 : 0 ≤ v - x := by linarith
        have hL0 : 0 ≤ v - l := by linarith
        have hXL : (x - v) ^ 2 ≤ (l - v) ^ 2 := by
          calc
            (x - v) ^ 2 = (v - x) ^ 2 := by ring
            _ ≤ (v - l) ^ 2 := (sq_le_sq₀ hX0 hL0).2 (by linarith)
            _ = (l - v) ^ 2 := by ring
        apply abs_le_of_between_abs
          (a := qv) (b := a * (l - v) ^ 2 + qv)
        · have hs : 0 ≤ (x - v) ^ 2 := sq_nonneg _
          nlinarith
        · simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left hXL ha.le) qv
        · simpa using hVertex
        · exact hMl
      · have hvx : v ≤ x := le_of_not_ge hxv
        have hX0 : 0 ≤ x - v := by linarith
        have hR0 : 0 ≤ r - v := by linarith
        have hXR : (x - v) ^ 2 ≤ (r - v) ^ 2 :=
          (sq_le_sq₀ hX0 hR0).2 (by linarith)
        apply abs_le_of_between_abs
          (a := qv) (b := a * (r - v) ^ 2 + qv)
        · have hs : 0 ≤ (x - v) ^ 2 := sq_nonneg _
          nlinarith
        · simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left hXR ha.le) qv
        · simpa using hVertex
        · exact hMr

/-- Each literal real factor is bounded by the exact endpoint/vertex maximum
stored in a containing certificate cell. -/
theorem literalRhinFactorReal_abs_le_cellMax
    (c : RhinCell) (x : ℝ)
    (hlx : (c.left : ℝ) ≤ x) (hxr : x ≤ (c.right : ℝ))
    (i : Fin 6) :
    |literalRhinFactorReal x i| ≤ (rhinCellMax c i : ℝ) := by
  fin_cases i
  · have h := abs_le_max_abs_of_between
      (a := (c.left : ℝ) - 3) (x := x - 3)
      (b := (c.right : ℝ) - 3) (by linarith) (by linarith)
    simpa [literalRhinFactorReal, rhinCellMax] using h
  · have h := abs_le_max_abs_of_between
      (a := (c.left : ℝ) - 2) (x := x - 2)
      (b := (c.right : ℝ) - 2) (by linarith) (by linarith)
    simpa [literalRhinFactorReal, rhinCellMax] using h
  · have h := abs_le_max_abs_of_between
      (a := (c.left : ℝ) - 4) (x := x - 4)
      (b := (c.right : ℝ) - 4) (by linarith) (by linarith)
    simpa [literalRhinFactorReal, rhinCellMax] using h
  · have h := abs_le_max_abs_of_between
      (a := 5 * (c.left : ℝ) - 12) (x := 5 * x - 12)
      (b := 5 * (c.right : ℝ) - 12) (by linarith) (by linarith)
    simpa [literalRhinFactorReal, rhinCellMax] using h
  · have hMlQ :
        |rhinQ5Rat c.left| ≤ rhinCellMax c (4 : Fin 6) := by
      simp [rhinCellMax]
    have hMrQ :
        |rhinQ5Rat c.right| ≤ rhinCellMax c (4 : Fin 6) := by
      simp [rhinCellMax]
    have hMlR :
        |17 * (c.left : ℝ) ^ 2 - 102 * (c.left : ℝ) + 144| ≤
          (rhinCellMax c (4 : Fin 6) : ℝ) := by
      exact_mod_cast hMlQ
    have hMrR :
        |17 * (c.right : ℝ) ^ 2 - 102 * (c.right : ℝ) + 144| ≤
          (rhinCellMax c (4 : Fin 6) : ℝ) := by
      exact_mod_cast hMrQ
    have hQuad := quadratic_abs_le_cell
      17 3 (-9) (c.left : ℝ) x (c.right : ℝ)
      (rhinCellMax c (4 : Fin 6) : ℝ)
      (by norm_num) hlx hxr
      (by
        rw [show 17 * ((c.left : ℝ) - 3) ^ 2 + (-9) =
          17 * (c.left : ℝ) ^ 2 - 102 * (c.left : ℝ) + 144 by ring]
        exact hMlR)
      (by
        rw [show 17 * ((c.right : ℝ) - 3) ^ 2 + (-9) =
          17 * (c.right : ℝ) ^ 2 - 102 * (c.right : ℝ) + 144 by ring]
        exact hMrR)
      (by
        intro hlv hvr
        have hlvQ : c.left ≤ (3 : ℚ) := by exact_mod_cast hlv
        have hvrQ : (3 : ℚ) ≤ c.right := by exact_mod_cast hvr
        have hNineQ : (9 : ℚ) ≤ rhinCellMax c (4 : Fin 6) := by
          simp [rhinCellMax, hlvQ, hvrQ]
        have hNineR : (9 : ℝ) ≤ (rhinCellMax c (4 : Fin 6) : ℝ) := by
          exact_mod_cast hNineQ
        simpa using hNineR)
    simpa [literalRhinFactorReal] using
      (show |17 * x ^ 2 - 102 * x + 144| ≤
          (rhinCellMax c (4 : Fin 6) : ℝ) by
        rw [show 17 * x ^ 2 - 102 * x + 144 =
          17 * (x - 3) ^ 2 + (-9) by ring]
        exact hQuad)
  · have hMlQ :
        |rhinQ6Rat c.left| ≤ rhinCellMax c (5 : Fin 6) := by
      simp [rhinCellMax]
    have hMrQ :
        |rhinQ6Rat c.right| ≤ rhinCellMax c (5 : Fin 6) := by
      simp [rhinCellMax]
    have hMlR :
        |19 * (c.left : ℝ) ^ 2 - 108 * (c.left : ℝ) + 144| ≤
          (rhinCellMax c (5 : Fin 6) : ℝ) := by
      exact_mod_cast hMlQ
    have hMrR :
        |19 * (c.right : ℝ) ^ 2 - 108 * (c.right : ℝ) + 144| ≤
          (rhinCellMax c (5 : Fin 6) : ℝ) := by
      exact_mod_cast hMrQ
    have hQuad := quadratic_abs_le_cell
      19 (54 / 19) (-180 / 19) (c.left : ℝ) x (c.right : ℝ)
      (rhinCellMax c (5 : Fin 6) : ℝ)
      (by norm_num) hlx hxr
      (by
        rw [show 19 * ((c.left : ℝ) - 54 / 19) ^ 2 + (-180 / 19) =
          19 * (c.left : ℝ) ^ 2 - 108 * (c.left : ℝ) + 144 by ring]
        exact hMlR)
      (by
        rw [show 19 * ((c.right : ℝ) - 54 / 19) ^ 2 + (-180 / 19) =
          19 * (c.right : ℝ) ^ 2 - 108 * (c.right : ℝ) + 144 by ring]
        exact hMrR)
      (by
        intro hlv hvr
        have hlvCast :
            (c.left : ℝ) ≤ ((54 / 19 : ℚ) : ℝ) := by
          norm_num
          exact hlv
        have hvrCast :
            ((54 / 19 : ℚ) : ℝ) ≤ (c.right : ℝ) := by
          norm_num
          exact hvr
        have hlvQ : c.left ≤ (54 / 19 : ℚ) :=
          (Rat.cast_le (K := ℝ)).mp hlvCast
        have hvrQ : (54 / 19 : ℚ) ≤ c.right :=
          (Rat.cast_le (K := ℝ)).mp hvrCast
        have hVertexQ : (180 / 19 : ℚ) ≤ rhinCellMax c (5 : Fin 6) := by
          simp [rhinCellMax, hlvQ, hvrQ]
        have hVertexR :
            (180 / 19 : ℝ) ≤ (rhinCellMax c (5 : Fin 6) : ℝ) := by
          have hCast := (Rat.cast_le (K := ℝ)).mpr hVertexQ
          norm_num at hCast ⊢
          exact hCast
        norm_num at hVertexR ⊢
        exact hVertexR)
    simpa [literalRhinFactorReal] using
      (show |19 * x ^ 2 - 108 * x + 144| ≤
          (rhinCellMax c (5 : Fin 6) : ℝ) by
        rw [show 19 * x ^ 2 - 108 * x + 144 =
          19 * (x - 54 / 19) ^ 2 + (-180 / 19) by ring]
        exact hQuad)

/-- The exact cell arithmetic and the generic floor-loss lemma give the
all-`n` local product estimate for the production multiplicities. -/
theorem literalRhinCell_product_bound
    (c : RhinCell) (hc : rhinCellValid c) (n : ℕ) :
    (∏ i : Fin 6, (rhinCellMax c i : ℝ) ^ literalRhinMultiplicity i n) ≤
      (rhinCellCost c : ℝ) *
        (((239 : ℝ) / 1000) * (c.left : ℝ)) ^ n := by
  have hLeft : 0 ≤ (c.left : ℝ) := by
    have hZeroTwo : (0 : ℚ) ≤ 2 := by norm_num
    have hLeftQ : (0 : ℚ) ≤ c.left := hZeroTwo.trans hc.2.1
    exact_mod_cast hLeftQ
  have hM : ∀ i ∈ (Finset.univ : Finset (Fin 6)),
      0 < (rhinCellMax c i : ℝ) := by
    intro i hi
    exact_mod_cast rhinCellMax_pos_of_valid hc i
  have hUpper : ∀ i ∈ (Finset.univ : Finset (Fin 6)),
      1 ≤ (rhinCellMax c i : ℝ) →
        1000 * literalRhinMultiplicity i n ≤ rhinCellExponent c i * n := by
    intro i hi hOne
    have hOneQ : (1 : ℚ) ≤ rhinCellMax c i := by
      apply (Rat.cast_le (K := ℝ)).mp
      simpa using hOne
    have he : rhinCellExponent c i = literalRhinUpperExponent i := by
      simp [rhinCellExponent, hOneQ]
    rw [he]
    exact literalRhinMultiplicity_upper n i
  have hLower : ∀ i ∈ (Finset.univ : Finset (Fin 6)),
      (rhinCellMax c i : ℝ) < 1 →
        rhinCellExponent c i * n ≤ 1000 * literalRhinMultiplicity i n + 1000 := by
    intro i hi hOne
    have hOneQ : rhinCellMax c i < (1 : ℚ) := by
      apply (Rat.cast_lt (K := ℝ)).mp
      simpa using hOne
    have he : rhinCellExponent c i = literalRhinLowerExponent i := by
      simp [rhinCellExponent, not_le.mpr hOneQ]
    rw [he]
    exact literalRhinMultiplicity_lower n i
  have hCellQ := hc.2.2.2.2
  have hCellR :
      (∏ i : Fin 6, (rhinCellMax c i : ℝ) ^ rhinCellExponent c i) ≤
        (((239 : ℝ) / 1000) * (c.left : ℝ)) ^ 1000 := by
    have hCast :
        (((∏ i : Fin 6, rhinCellMax c i ^ rhinCellExponent c i) : ℚ) : ℝ) ≤
          (((((239 : ℚ) / 1000) * c.left) ^ 1000 : ℚ) : ℝ) := by
      exact_mod_cast hCellQ.le
    simpa using hCast
  have h := cellProductBound
    (Finset.univ : Finset (Fin 6))
    (fun i ↦ (rhinCellMax c i : ℝ))
    (fun i ↦ literalRhinMultiplicity i n) (rhinCellExponent c) n
    ((239 : ℝ) / 1000) (c.left : ℝ)
    hM hUpper hLower (by norm_num) hLeft (by simpa using hCellR)
  have hCost :
      (rhinCellCost c : ℝ) =
        ∏ i : Fin 6,
          if (rhinCellMax c i : ℝ) < 1 then
            (rhinCellMax c i : ℝ)⁻¹ else 1 := by
    unfold rhinCellCost
    push_cast
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hSmall : rhinCellMax c i < (1 : ℚ)
    · have hSmallR : (rhinCellMax c i : ℝ) < 1 := by exact_mod_cast hSmall
      simp [hSmall, hSmallR]
    · have hSmallR : ¬ (rhinCellMax c i : ℝ) < 1 := by
        intro hR
        apply hSmall
        exact_mod_cast hR
      simp [hSmall, hSmallR]
  rw [hCost]
  exact h

/-- Local continuous bound for the production literal polynomial. -/
theorem literalRhinPolynomial_eval₂_abs_le_cell
    (c : RhinCell) (hc : rhinCellValid c) (hCost : rhinCellCost c ≤ 20)
    (n : ℕ) (x : ℝ)
    (hlx : (c.left : ℝ) ≤ x) (hxr : x ≤ (c.right : ℝ)) :
    |(literalRhinPolynomial n).eval₂ (Int.castRingHom ℝ) x| ≤
      (12 : ℝ) ^ 7 * 20 * (((239 : ℝ) / 1000) * x) ^ n := by
  have hFactors :
      (∏ i : Fin 6, |literalRhinFactorReal x i| ^ literalRhinMultiplicity i n) ≤
        ∏ i : Fin 6, (rhinCellMax c i : ℝ) ^ literalRhinMultiplicity i n := by
    apply Finset.prod_le_prod
    · intro i hi
      positivity
    · intro i hi
      exact pow_le_pow_left₀ (abs_nonneg _)
        (literalRhinFactorReal_abs_le_cellMax c x hlx hxr i) _
  have hCell := literalRhinCell_product_bound c hc n
  have hCostR : (rhinCellCost c : ℝ) ≤ 20 := by exact_mod_cast hCost
  have hLeftNonneg : 0 ≤ (c.left : ℝ) := by
    have hZeroTwo : (0 : ℚ) ≤ 2 := by norm_num
    exact_mod_cast hZeroTwo.trans hc.2.1
  have hBaseNonneg : 0 ≤ (239 / 1000 : ℝ) := by norm_num
  have hBaseLeft :
      ((239 : ℝ) / 1000) * (c.left : ℝ) ≤
        ((239 : ℝ) / 1000) * x :=
    mul_le_mul_of_nonneg_left hlx hBaseNonneg
  calc
    |(literalRhinPolynomial n).eval₂ (Int.castRingHom ℝ) x| =
        (12 : ℝ) ^ 7 *
          (∏ i : Fin 6,
            |literalRhinFactorReal x i| ^ literalRhinMultiplicity i n) := by
      rw [literalRhinPolynomial_eval₂_eq_factorProduct]
      simp only [abs_mul, abs_pow, Finset.abs_prod]
      norm_num
    _ ≤ (12 : ℝ) ^ 7 *
          (∏ i : Fin 6,
            (rhinCellMax c i : ℝ) ^ literalRhinMultiplicity i n) :=
      mul_le_mul_of_nonneg_left hFactors (by positivity)
    _ ≤ (12 : ℝ) ^ 7 *
          ((rhinCellCost c : ℝ) *
            (((239 : ℝ) / 1000) * (c.left : ℝ)) ^ n) :=
      mul_le_mul_of_nonneg_left hCell (by positivity)
    _ ≤ (12 : ℝ) ^ 7 *
          (20 * (((239 : ℝ) / 1000) * (c.left : ℝ)) ^ n) := by
      gcongr
    _ ≤ (12 : ℝ) ^ 7 *
          (20 * (((239 : ℝ) / 1000) * x) ^ n) := by
      gcongr
    _ = (12 : ℝ) ^ 7 * 20 *
          (((239 : ℝ) / 1000) * x) ^ n := by ring

/-- Uniform continuous bound for the production literal polynomial on the
full source interval. -/
theorem literalRhinPolynomial_eval₂_abs_le_Icc
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (2 : ℝ) 4) :
    |(literalRhinPolynomial n).eval₂ (Int.castRingHom ℝ) x| ≤
      (12 : ℝ) ^ 7 * 20 * (((239 : ℝ) / 1000) * x) ^ n := by
  by_cases hxThree : x ≤ 3
  · obtain ⟨c, hmem, hcell⟩ := exists_rhinCell23 ⟨hx.1, hxThree⟩
    exact literalRhinPolynomial_eval₂_abs_le_cell c
      (rhinCells23_valid c hmem) (rhinCells23_cost_le c hmem)
      n x hcell.1 hcell.2
  · have hThree : 3 ≤ x := le_of_not_ge hxThree
    obtain ⟨c, hmem, hcell⟩ := exists_rhinCell34 ⟨hThree, hx.2⟩
    exact literalRhinPolynomial_eval₂_abs_le_cell c
      (rhinCells34_valid c hmem) (rhinCells34_cost_le c hmem)
      n x hcell.1 hcell.2

/-- The square-and-shift integrand at the production common scale
`N = 2*m+2`. -/
def literalRhinSquareIntegrand (m j : ℕ) (x : ℝ) : ℝ :=
  144 * x ^ j *
      ((literalRhinPolynomial m).eval₂ (Int.castRingHom ℝ) x) ^ 2 /
    x ^ (2 * m + 3)

private theorem pow_ratio_le_one
    {x : ℝ} (hx : 1 ≤ x) (m j : ℕ) (hj : j ≤ 2) :
    x ^ (2 * m + j) / x ^ (2 * m + 3) ≤ 1 := by
  have hExp : 2 * m + j ≤ 2 * m + 3 := by omega
  have hPow := pow_le_pow_right₀ hx hExp
  exact (div_le_one₀ (pow_pos (zero_lt_one.trans_le hx) _)).2 hPow

/-- Uniform pointwise decay for every one of the three production shifts. -/
theorem literalRhinSquareIntegrand_abs_le
    (m j : ℕ) (hj : j ≤ 2) (x : ℝ) (hx : x ∈ Set.Icc (2 : ℝ) 4) :
    |literalRhinSquareIntegrand m j x| ≤
      144 * (((12 : ℝ) ^ 7 * 20) ^ 2) *
        ((239 : ℝ) / 1000) ^ (2 * m) := by
  let A : ℝ := (12 : ℝ) ^ 7 * 20
  let base : ℝ := (239 : ℝ) / 1000
  have hxPos : 0 < x := by linarith [hx.1]
  have hxOne : 1 ≤ x := by linarith [hx.1]
  have hH := literalRhinPolynomial_eval₂_abs_le_Icc m x hx
  have hHSq :
      |(literalRhinPolynomial m).eval₂ (Int.castRingHom ℝ) x| ^ 2 ≤
        (A * (base * x) ^ m) ^ 2 := by
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [A, base] using hH) 2
  have hNumerator :
      144 * x ^ j *
          |(literalRhinPolynomial m).eval₂ (Int.castRingHom ℝ) x| ^ 2 ≤
        144 * x ^ j * (A * (base * x) ^ m) ^ 2 := by
    gcongr
  have hRatio := pow_ratio_le_one hxOne m j hj
  calc
    |literalRhinSquareIntegrand m j x| =
        (144 * x ^ j *
          |(literalRhinPolynomial m).eval₂ (Int.castRingHom ℝ) x| ^ 2) /
            x ^ (2 * m + 3) := by
      simp only [literalRhinSquareIntegrand, abs_div, abs_mul, abs_pow,
        abs_of_nonneg hxPos.le]
      norm_num
    _ ≤ (144 * x ^ j * (A * (base * x) ^ m) ^ 2) /
          x ^ (2 * m + 3) :=
      div_le_div_of_nonneg_right hNumerator (pow_nonneg hxPos.le _)
    _ = 144 * A ^ 2 * base ^ (2 * m) *
          (x ^ (2 * m + j) / x ^ (2 * m + 3)) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      field_simp [hxPos.ne']
      ring
    _ ≤ 144 * A ^ 2 * base ^ (2 * m) * 1 := by
      gcongr
    _ = 144 * (((12 : ℝ) ^ 7 * 20) ^ 2) *
        ((239 : ℝ) / 1000) ^ (2 * m) := by
      simp only [A, base, mul_one]

/-- The `[2,3]` production square-shift integral has the same geometric
decay as its pointwise envelope because the interval has width one. -/
theorem literalRhinSquareIntegrand_integral23_abs_le
    (m j : ℕ) (hj : j ≤ 2) :
    |∫ x in (2 : ℝ)..3, literalRhinSquareIntegrand m j x| ≤
      144 * (((12 : ℝ) ^ 7 * 20) ^ 2) *
        ((239 : ℝ) / 1000) ^ (2 * m) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (2 : ℝ)) (b := 3)
    (C := 144 * (((12 : ℝ) ^ 7 * 20) ^ 2) *
      ((239 : ℝ) / 1000) ^ (2 * m))
    (f := fun x : ℝ ↦ literalRhinSquareIntegrand m j x)
    (by
      intro x hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      simpa only [Real.norm_eq_abs] using
        literalRhinSquareIntegrand_abs_le m j hj x
          ⟨hx.1.le, hx.2.trans (by norm_num)⟩)
  have hWidth : |(3 : ℝ) - 2| = 1 := by norm_num
  rw [hWidth, mul_one] at h
  simpa only [Real.norm_eq_abs] using h

/-- The `[3,4]` production square-shift integral has the same geometric
decay as its pointwise envelope because the interval has width one. -/
theorem literalRhinSquareIntegrand_integral34_abs_le
    (m j : ℕ) (hj : j ≤ 2) :
    |∫ x in (3 : ℝ)..4, literalRhinSquareIntegrand m j x| ≤
      144 * (((12 : ℝ) ^ 7 * 20) ^ 2) *
        ((239 : ℝ) / 1000) ^ (2 * m) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (3 : ℝ)) (b := 4)
    (C := 144 * (((12 : ℝ) ^ 7 * 20) ^ 2) *
      ((239 : ℝ) / 1000) ^ (2 * m))
    (f := fun x : ℝ ↦ literalRhinSquareIntegrand m j x)
    (by
      intro x hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      simpa only [Real.norm_eq_abs] using
        literalRhinSquareIntegrand_abs_le m j hj x
          ⟨(by linarith [hx.1]), hx.2⟩)
  have hWidth : |(4 : ℝ) - 3| = 1 := by norm_num
  rw [hWidth, mul_one] at h
  simpa only [Real.norm_eq_abs] using h

end

end Rhin
end NumberTheory
end Erdos1135
