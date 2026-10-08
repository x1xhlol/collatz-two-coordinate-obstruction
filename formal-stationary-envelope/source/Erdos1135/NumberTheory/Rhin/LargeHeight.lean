/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.NumberTheory.Rhin.Statement
import Erdos1135.NumberTheory.Rhin.RangeLCM
import Erdos1135.NumberTheory.Rhin.LiteralCoefficientBound
import Erdos1135.NumberTheory.Rhin.ContinuousRemainder
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Topology.Algebra.Polynomial

/-!
# Simultaneous-approximation transference for Rhin's large-height bound

This file first isolates the load-bearing generic transference step and then
implements the p. 159 row, integrality, ordered-moment determinant, and literal
square-shift construction that feed it.  A certificate supplies, at every
sufficiently large height, three integral simultaneous-approximation rows with:

* a denominator bound of order `H^(133/10)`;
* a combined error budget adapted to the change of logarithmic basis; and
* exact separation of every nonzero integer coefficient triple.

The concrete declarations later in this file prove the literal row identities,
determinant, and local coefficient/moment estimates.  `LiteralLargeHeight.lean`
joins them with the independent table-free LCM producer and fills the final
grouped bounds.  Row separation is never inferred from `LargeHeightBound`, and
no finite low-height phase table appears here.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

open Polynomial
open scoped BigOperators Interval

/-- The first logarithmic coordinate used by Rhin's simultaneous integrals. -/
def logTwoDivThree : ℝ :=
  Real.log 2 - Real.log 3

/-- The second logarithmic coordinate used by Rhin's simultaneous integrals. -/
def logFourDivThree : ℝ :=
  2 * Real.log 2 - Real.log 3

/-- The corrected common endpoint ideal for Rhin's two p. 159 integrals.
Membership in its `N`th power supplies powers of both endpoint products,
not merely the modulus `4` printed in the later generic sentence. -/
def twelveXIdeal : Ideal ℤ[X] :=
  Ideal.span {(X : ℤ[X]), C (12 : ℤ)}

/-- The exact low-coefficient divisibility consumed by the p. 159 row
construction.  It is stated in the offset `d` used by the antiderivative
terms, so later arithmetic does not need to transport a saturated
subtraction predicate. -/
def HasTwelveEndpointDivisibility (G : ℤ[X]) (N : ℕ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → d ≤ N →
    (12 : ℤ) ^ d ∣ G.coeff (N - d)

/-- Multiplying by an arbitrary integer polynomial preserves the weighted
low-coefficient divisibility at a fixed order. -/
private theorem lowCoeffDvd_mul_left
    {N : ℕ} {G : ℤ[X]}
    (hG : ∀ k : ℕ, k < N →
      (12 : ℤ) ^ (N - k) ∣ G.coeff k)
    (P : ℤ[X]) :
    ∀ k : ℕ, k < N →
      (12 : ℤ) ^ (N - k) ∣ (P * G).coeff k := by
  intro k hk
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  intro ij hij
  have hjk : ij.2 ≤ k :=
    Finset.antidiagonal.snd_le hij
  have hjN : ij.2 < N :=
    hjk.trans_lt hk
  have hPow :
      (12 : ℤ) ^ (N - k) ∣
        (12 : ℤ) ^ (N - ij.2) :=
    pow_dvd_pow (12 : ℤ) (Nat.sub_le_sub_left hjk N)
  exact dvd_mul_of_dvd_right (hPow.trans (hG ij.2 hjN)) _

/-- Every member of `(X,12)^N` has the coefficientwise endpoint powers
needed in the source-faithful termwise p. 159 argument. -/
theorem lowCoeffDvd_of_mem_twelveXIdeal_pow
    (N : ℕ) (G : ℤ[X])
    (hG : G ∈ twelveXIdeal ^ N) :
    ∀ k : ℕ, k < N →
      (12 : ℤ) ^ (N - k) ∣ G.coeff k := by
  induction hG using Submodule.pow_induction_on_left' with
  | algebraMap P =>
      intro k hk
      omega
  | add P Q n hP hQ ihP ihQ =>
      intro k hk
      rw [Polynomial.coeff_add]
      exact (ihP k hk).add (ihQ k hk)
  | mem_mul M hM n G hG ih =>
      obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hM
      intro k hk
      have hProduct :
          M * G = X * (A * G) + C (12 : ℤ) * (B * G) := by
        rw [← hAB]
        ring
      rw [hProduct, Polynomial.coeff_add]
      apply dvd_add
      · cases k with
        | zero => simp
        | succ k =>
            have hkN : k < n := by omega
            simpa only [Polynomial.coeff_X_mul,
              Nat.succ_sub_succ_eq_sub] using
              lowCoeffDvd_mul_left ih A k hkN
      · rw [Polynomial.coeff_C_mul]
        by_cases hkN : k < n
        · obtain ⟨z, hz⟩ := lowCoeffDvd_mul_left ih B k hkN
          refine ⟨z, ?_⟩
          rw [hz, Nat.succ_sub hkN.le, pow_succ]
          ring
        · have hkn : k = n := by omega
          subst k
          simp

/-- Ideal-power membership feeds the offset form used by the deterministic
integer row. -/
theorem hasTwelveEndpointDivisibility_of_mem_twelveXIdeal_pow
    (N : ℕ) (G : ℤ[X]) (hG : G ∈ twelveXIdeal ^ N) :
    HasTwelveEndpointDivisibility G N := by
  intro d hd hdN
  have hLow := lowCoeffDvd_of_mem_twelveXIdeal_pow N G hG (N - d) (by omega)
  convert hLow using 1
  congr 1
  omega

/-! ## Literal p. 162 common-endpoint certificate -/

/-- The endpoint ideal `(X,d)` used separately at `d=3` and `d=4` before
combining the coprime certificates into `(X,12)`. -/
private def endpointXIdeal (d : ℤ) : Ideal ℤ[X] :=
  Ideal.span {(X : ℤ[X]), C d}

private theorem endpointXIdeal_X_mem (d : ℤ) :
    (X : ℤ[X]) ∈ endpointXIdeal d := by
  apply Ideal.subset_span
  simp

private theorem endpointXIdeal_C_mem (d : ℤ) :
    C d ∈ endpointXIdeal d := by
  apply Ideal.subset_span
  simp

private theorem mul_mem_pow_add
    {I : Ideal ℤ[X]} {f g : ℤ[X]} {a b : ℕ}
    (hf : f ∈ I ^ a) (hg : g ∈ I ^ b) :
    f * g ∈ I ^ (a + b) := by
  simpa only [pow_add] using Ideal.mul_mem_mul hf hg

private theorem power_mem_scaled_power
    {I : Ideal ℤ[X]} {f : ℤ[X]} {a m : ℕ}
    (hf : f ∈ I ^ a) :
    f ^ m ∈ I ^ (a * m) := by
  simpa only [pow_mul] using Ideal.pow_mem_pow hf m

private theorem pow_mem_half_of_sq_mem
    {I : Ideal ℤ[X]} {f : ℤ[X]}
    (hf : f ^ 2 ∈ I) (m : ℕ) :
    f ^ m ∈ I ^ (m / 2) := by
  have hMain : (f ^ 2) ^ (m / 2) ∈ I ^ (m / 2) :=
    Ideal.pow_mem_pow hf (m / 2)
  have hMul :
      (f ^ 2) ^ (m / 2) * f ^ (m % 2) ∈ I ^ (m / 2) :=
    Ideal.mul_mem_right (f ^ (m % 2)) (I ^ (m / 2)) hMain
  convert hMul using 1
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

private theorem pow_mem_one_plus_half_of_sq_mem_cube
    {I : Ideal ℤ[X]} {f : ℤ[X]}
    (hf : f ∈ I) (hfSq : f ^ 2 ∈ I ^ 3) (m : ℕ) :
    f ^ m ∈ I ^ (m + m / 2) := by
  have hRem : f ^ (m % 2) ∈ I ^ (m % 2) :=
    Ideal.pow_mem_pow hf (m % 2)
  have hMain : (f ^ 2) ^ (m / 2) ∈ (I ^ 3) ^ (m / 2) :=
    Ideal.pow_mem_pow hfSq (m / 2)
  have hMul := Ideal.mul_mem_mul hMain hRem
  have hMem :
      (f ^ 2) ^ (m / 2) * f ^ (m % 2) ∈
        I ^ (3 * (m / 2) + m % 2) := by
    simpa only [← pow_mul, pow_add] using hMul
  have hExponent : m + m / 2 = 3 * (m / 2) + m % 2 := by
    omega
  rw [hExponent]
  convert hMem using 1
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

private theorem finset_prod_mem_pow_sum
    {I : Ideal ℤ[X]} {S : Type*} [DecidableEq S]
    (s : Finset S) (f : S → ℤ[X]) (order : S → ℕ)
    (h : ∀ i ∈ s, f i ∈ I ^ order i) :
    ∏ i ∈ s, f i ∈ I ^ (∑ i ∈ s, order i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hiMem := h i (by simp)
      have hsMem : ∏ j ∈ s, f j ∈ I ^ (∑ j ∈ s, order j) := by
        apply ih
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.prod_insert hi, Finset.sum_insert hi, pow_add] using
        Ideal.mul_mem_mul hiMem hsMem

private theorem quadratic_mem_endpointXIdeal_sq
    (d a b c : ℤ) :
    (C a * X ^ 2 + C (b * d) * X + C (c * d * d) : ℤ[X]) ∈
      endpointXIdeal d ^ 2 := by
  let I := endpointXIdeal d
  have hx : (X : ℤ[X]) ∈ I := endpointXIdeal_X_mem d
  have hd : C d ∈ I := endpointXIdeal_C_mem d
  have hxx : (X : ℤ[X]) * X ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hx hx
  have hdx : C d * X ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hd hx
  have hdd : C d * C d ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hd hd
  have h1 := Ideal.mul_mem_left (I ^ 2) (C a) hxx
  have h2 := Ideal.mul_mem_left (I ^ 2) (C b) hdx
  have h3 := Ideal.mul_mem_left (I ^ 2) (C c) hdd
  have hSum := (I ^ 2).add_mem ((I ^ 2).add_mem h1 h2) h3
  change _ ∈ I ^ 2
  convert hSum using 1; simp only [map_mul]; ring

private theorem cubic_generator_expansion_mem_endpointXIdeal_cube
    (d : ℤ) (A : ℤ[X]) (b c e : ℤ) :
    A * X ^ 3 + C (b * d) * X ^ 2 + C (c * d * d) * X +
        C (e * d * d * d) ∈ endpointXIdeal d ^ 3 := by
  let I := endpointXIdeal d
  have hx : (X : ℤ[X]) ∈ I := endpointXIdeal_X_mem d
  have hd : C d ∈ I := endpointXIdeal_C_mem d
  have hx1 : (X : ℤ[X]) ∈ I ^ 1 := by simpa using hx
  have hd1 : C d ∈ I ^ 1 := by simpa using hd
  have hxx : (X : ℤ[X]) ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow hx 2
  have hdd : (C d) ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow hd 2
  have hxxx : (X : ℤ[X]) ^ 3 ∈ I ^ 3 := Ideal.pow_mem_pow hx 3
  have hdxx : C d * X ^ 2 ∈ I ^ 3 := by
    simpa only [show 1 + 2 = 3 by omega] using mul_mem_pow_add hd1 hxx
  have hddx : (C d) ^ 2 * X ∈ I ^ 3 := by
    simpa only [Nat.reduceAdd] using mul_mem_pow_add hdd hx1
  have hddd : (C d) ^ 3 ∈ I ^ 3 := Ideal.pow_mem_pow hd 3
  have h1 := Ideal.mul_mem_left (I ^ 3) A hxxx
  have h2 := Ideal.mul_mem_left (I ^ 3) (C b) hdxx
  have h3 := Ideal.mul_mem_left (I ^ 3) (C c) hddx
  have h4 := Ideal.mul_mem_left (I ^ 3) (C e) hddd
  have hSum :=
    (I ^ 3).add_mem ((I ^ 3).add_mem ((I ^ 3).add_mem h1 h2) h3) h4
  change _ ∈ I ^ 3
  convert hSum using 1; simp only [map_mul]; ring

private theorem literalRhinFactor1_mem_three :
    literalRhinFactor1 ∈ endpointXIdeal 3 := by
  rw [endpointXIdeal, Ideal.mem_span_pair]
  refine ⟨1, -1, ?_⟩
  unfold literalRhinFactor1
  ring

private theorem literalRhinFactor2_sq_mem_four :
    literalRhinFactor2 ^ 2 ∈ endpointXIdeal 4 := by
  rw [endpointXIdeal, Ideal.mem_span_pair]
  refine ⟨X - C 4, 1, ?_⟩
  unfold literalRhinFactor2
  norm_num [map_mul]
  ring

private theorem literalRhinFactor3_mem_four :
    literalRhinFactor3 ∈ endpointXIdeal 4 := by
  rw [endpointXIdeal, Ideal.mem_span_pair]
  refine ⟨1, -1, ?_⟩
  unfold literalRhinFactor3
  ring

private theorem literalRhinFactor4_mem_three :
    literalRhinFactor4 ∈ endpointXIdeal 3 := by
  rw [endpointXIdeal, Ideal.mem_span_pair]
  refine ⟨C 5, -4, ?_⟩
  unfold literalRhinFactor4
  norm_num [map_mul]
  ring

private theorem literalRhinFactor4_mem_four :
    literalRhinFactor4 ∈ endpointXIdeal 4 := by
  rw [endpointXIdeal, Ideal.mem_span_pair]
  refine ⟨C 5, -3, ?_⟩
  unfold literalRhinFactor4
  norm_num [map_mul]
  ring

private theorem literalRhinFactor5_mem_three_sq :
    literalRhinFactor5 ∈ endpointXIdeal 3 ^ 2 := by
  have h := quadratic_mem_endpointXIdeal_sq 3 17 (-34) 16
  norm_num [map_mul] at h ⊢
  convert h using 1

private theorem literalRhinFactor5_mem_four :
    literalRhinFactor5 ∈ endpointXIdeal 4 := by
  rw [endpointXIdeal, Ideal.mem_span_pair]
  refine ⟨C 17 * X - C 102, C 36, ?_⟩
  unfold literalRhinFactor5
  norm_num [map_mul]
  ring

private theorem literalRhinFactor5_sq_mem_four_cube :
    literalRhinFactor5 ^ 2 ∈ endpointXIdeal 4 ^ 3 := by
  have h := cubic_generator_expansion_mem_endpointXIdeal_cube
    4 (C 289 * X - C 3468) 3825 (-1836) 324
  unfold literalRhinFactor5
  norm_num [map_mul] at h ⊢
  convert h using 1; ring

private theorem literalRhinFactor6_mem_three_sq :
    literalRhinFactor6 ∈ endpointXIdeal 3 ^ 2 := by
  have h := quadratic_mem_endpointXIdeal_sq 3 19 (-36) 16
  norm_num [map_mul] at h ⊢
  convert h using 1

private theorem literalRhinFactor6_mem_four_sq :
    literalRhinFactor6 ∈ endpointXIdeal 4 ^ 2 := by
  have h := quadratic_mem_endpointXIdeal_sq 4 19 (-27) 9
  norm_num [map_mul] at h ⊢
  convert h using 1

private def literalRhinThreeOrderAt (i : Fin 6) (n : ℕ) : ℕ :=
  ![literalRhinMultiplicity 0 n, 0, 0, literalRhinMultiplicity 3 n,
    2 * literalRhinMultiplicity 4 n, 2 * literalRhinMultiplicity 5 n] i

private def literalRhinFourOrderAt (i : Fin 6) (n : ℕ) : ℕ :=
  ![0, literalRhinMultiplicity 1 n / 2, literalRhinMultiplicity 2 n,
    literalRhinMultiplicity 3 n,
    literalRhinMultiplicity 4 n + literalRhinMultiplicity 4 n / 2,
    2 * literalRhinMultiplicity 5 n] i

private theorem literalRhinFactor_pow_mem_three
    (i : Fin 6) (n : ℕ) :
    literalRhinFactor i ^ literalRhinMultiplicity i n ∈
      endpointXIdeal 3 ^ literalRhinThreeOrderAt i n := by
  fin_cases i
  · simpa [literalRhinThreeOrderAt] using
      Ideal.pow_mem_pow literalRhinFactor1_mem_three
        (literalRhinMultiplicity 0 n)
  · simp [literalRhinThreeOrderAt]
  · simp [literalRhinThreeOrderAt]
  · simpa [literalRhinThreeOrderAt] using
      Ideal.pow_mem_pow literalRhinFactor4_mem_three
        (literalRhinMultiplicity 3 n)
  · simpa [literalRhinThreeOrderAt] using
      power_mem_scaled_power (m := literalRhinMultiplicity 4 n)
        literalRhinFactor5_mem_three_sq
  · simpa [literalRhinThreeOrderAt] using
      power_mem_scaled_power (m := literalRhinMultiplicity 5 n)
        literalRhinFactor6_mem_three_sq

private theorem literalRhinFactor_pow_mem_four
    (i : Fin 6) (n : ℕ) :
    literalRhinFactor i ^ literalRhinMultiplicity i n ∈
      endpointXIdeal 4 ^ literalRhinFourOrderAt i n := by
  fin_cases i
  · simp [literalRhinFourOrderAt]
  · simpa [literalRhinFourOrderAt] using
      pow_mem_half_of_sq_mem literalRhinFactor2_sq_mem_four
        (literalRhinMultiplicity 1 n)
  · simpa [literalRhinFourOrderAt] using
      Ideal.pow_mem_pow literalRhinFactor3_mem_four
        (literalRhinMultiplicity 2 n)
  · simpa [literalRhinFourOrderAt] using
      Ideal.pow_mem_pow literalRhinFactor4_mem_four
        (literalRhinMultiplicity 3 n)
  · simpa [literalRhinFourOrderAt] using
      pow_mem_one_plus_half_of_sq_mem_cube literalRhinFactor5_mem_four
        literalRhinFactor5_sq_mem_four_cube (literalRhinMultiplicity 4 n)
  · simpa [literalRhinFourOrderAt] using
      power_mem_scaled_power (m := literalRhinMultiplicity 5 n)
        literalRhinFactor6_mem_four_sq

private theorem literalRhinFixedScalar_mem_endpoint_seven (d : ℤ)
    (hd : d ∣ (12 : ℤ)) :
    C ((12 : ℤ) ^ 7) ∈ endpointXIdeal d ^ 7 := by
  obtain ⟨k, hk⟩ := hd
  have h12 : C (12 : ℤ) ∈ endpointXIdeal d := by
    rw [endpointXIdeal, Ideal.mem_span_pair]
    refine ⟨0, C k, ?_⟩
    simp only [zero_mul, zero_add, ← map_mul]
    rw [mul_comm, ← hk]
  simpa only [map_pow] using Ideal.pow_mem_pow h12 7

private theorem literalRhinPolynomial_mem_endpoint_strong
    (d : ℤ) (order : Fin 6 → ℕ) (n : ℕ)
    (hd : d ∣ (12 : ℤ))
    (hFactor : ∀ i : Fin 6,
      literalRhinFactor i ^ literalRhinMultiplicity i n ∈
        endpointXIdeal d ^ order i) :
    literalRhinPolynomial n ∈
      endpointXIdeal d ^ ((∑ i : Fin 6, order i) + 7) := by
  have hProduct :
      ∏ i : Fin 6,
          literalRhinFactor i ^ literalRhinMultiplicity i n ∈
        endpointXIdeal d ^ (∑ i : Fin 6, order i) := by
    simpa only using
      finset_prod_mem_pow_sum Finset.univ
        (fun i : Fin 6 ↦
          literalRhinFactor i ^ literalRhinMultiplicity i n)
        order (by
          intro i _hi
          exact hFactor i)
  have hScalar := literalRhinFixedScalar_mem_endpoint_seven d hd
  have hMul := mul_mem_pow_add hScalar hProduct
  simpa only [literalRhinPolynomial, Nat.add_comm] using hMul

private theorem literalRhinThreeOrder_floor_loss (n : ℕ) :
    n ≤ (∑ i : Fin 6, literalRhinThreeOrderAt i n) + 7 := by
  simp [literalRhinThreeOrderAt, literalRhinMultiplicity,
    literalRhinWeightNumerator, Fin.sum_univ_succ]
  omega

private theorem literalRhinFourOrder_floor_loss (n : ℕ) :
    n ≤ (∑ i : Fin 6, literalRhinFourOrderAt i n) + 7 := by
  simp [literalRhinFourOrderAt, literalRhinMultiplicity,
    literalRhinWeightNumerator, Fin.sum_univ_succ]
  omega

private theorem literalRhinPolynomial_mem_three_pow (n : ℕ) :
    literalRhinPolynomial n ∈ endpointXIdeal 3 ^ n := by
  have hStrong := literalRhinPolynomial_mem_endpoint_strong
    3 (fun i ↦ literalRhinThreeOrderAt i n) n (by norm_num)
    (fun i ↦ literalRhinFactor_pow_mem_three i n)
  exact Ideal.pow_le_pow_right (literalRhinThreeOrder_floor_loss n) hStrong

private theorem literalRhinPolynomial_mem_four_pow (n : ℕ) :
    literalRhinPolynomial n ∈ endpointXIdeal 4 ^ n := by
  have hStrong := literalRhinPolynomial_mem_endpoint_strong
    4 (fun i ↦ literalRhinFourOrderAt i n) n (by norm_num)
    (fun i ↦ literalRhinFactor_pow_mem_four i n)
  exact Ideal.pow_le_pow_right (literalRhinFourOrder_floor_loss n) hStrong

private theorem endpoint_three_sup_four_eq_top :
    endpointXIdeal 3 ⊔ endpointXIdeal 4 = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h3 : C (3 : ℤ) ∈ endpointXIdeal 3 ⊔ endpointXIdeal 4 :=
    (le_sup_left : endpointXIdeal 3 ≤ endpointXIdeal 3 ⊔ endpointXIdeal 4)
      (endpointXIdeal_C_mem 3)
  have h4 : C (4 : ℤ) ∈ endpointXIdeal 3 ⊔ endpointXIdeal 4 :=
    (le_sup_right : endpointXIdeal 4 ≤ endpointXIdeal 3 ⊔ endpointXIdeal 4)
      (endpointXIdeal_C_mem 4)
  have hSub := (endpointXIdeal 3 ⊔ endpointXIdeal 4).sub_mem h4 h3
  norm_num at hSub ⊢
  exact hSub

private theorem endpoint_three_mul_four_eq_twelve :
    endpointXIdeal 3 * endpointXIdeal 4 = twelveXIdeal := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hr
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hs
    apply Ideal.mem_span_pair.mpr
    refine ⟨a * c * X + C 4 * a * d + C 3 * b * c, b * d, ?_⟩
    rw [← hab, ← hcd]
    norm_num [map_mul]
    ring
  · rw [twelveXIdeal, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have h4x := Ideal.mul_mem_mul
        (endpointXIdeal_X_mem 3) (endpointXIdeal_C_mem 4)
      have h3x := Ideal.mul_mem_mul
        (endpointXIdeal_C_mem 3) (endpointXIdeal_X_mem 4)
      have hSub := (endpointXIdeal 3 * endpointXIdeal 4).sub_mem h4x h3x
      convert hSub using 1; norm_num [map_mul]; ring
    · have hMul := Ideal.mul_mem_mul
        (endpointXIdeal_C_mem 3) (endpointXIdeal_C_mem 4)
      convert hMul using 1; norm_num [map_mul]

/-- The literal p. 162 polynomial has the corrected common `(X,12)^n`
certificate needed by the two p. 159 endpoint integrals.  The proof keeps
separate `(X,3)` and `(X,4)` order ledgers and combines their coprime powers;
this membership is derived, not printed verbatim by Rhin. -/
theorem literalRhinPolynomial_mem_twelveXIdeal_pow (n : ℕ) :
    literalRhinPolynomial n ∈ twelveXIdeal ^ n := by
  have hThree := literalRhinPolynomial_mem_three_pow n
  have hFour := literalRhinPolynomial_mem_four_pow n
  have hInf :
      literalRhinPolynomial n ∈
        endpointXIdeal 3 ^ n ⊓ endpointXIdeal 4 ^ n :=
    ⟨hThree, hFour⟩
  have hSup : endpointXIdeal 3 ^ n ⊔ endpointXIdeal 4 ^ n = ⊤ :=
    Ideal.pow_sup_pow_eq_top endpoint_three_sup_four_eq_top
  have hCoprime : IsCoprime (endpointXIdeal 3 ^ n) (endpointXIdeal 4 ^ n) :=
    Ideal.isCoprime_iff_sup_eq.mpr hSup
  have hProduct :
      literalRhinPolynomial n ∈
        endpointXIdeal 3 ^ n * endpointXIdeal 4 ^ n := by
    rw [Ideal.mul_eq_inf_of_isCoprime hCoprime]
    exact hInf
  rw [← mul_pow, endpoint_three_mul_four_eq_twelve] at hProduct
  exact hProduct

/-- The literal polynomial therefore satisfies the exact coefficientwise
endpoint divisibility consumed by the deterministic p. 159 row. -/
theorem literalRhinPolynomial_hasTwelveEndpointDivisibility (n : ℕ) :
    HasTwelveEndpointDivisibility (literalRhinPolynomial n) n :=
  hasTwelveEndpointDivisibility_of_mem_twelveXIdeal_pow n
    (literalRhinPolynomial n) (literalRhinPolynomial_mem_twelveXIdeal_pow n)

/-! ## The three literal square shifts

The source p. 162 prints `H_n` and the two unsquared integrals at order `n`.
The scale `2*n+2`, the factor `144`, the three shifts, the exact interior
witnesses, and the threshold `8` below are derived G8a certificates.  They
form a p. 159-compatible square construction; they are not additional data
printed by Rhin.
-/

/-- The derived p. 159 order attached to the square of the p. 162
polynomial. -/
def literalRhinSquareScale (n : ℕ) : ℕ :=
  2 * n + 2

/-- The three shifted square polynomials used to form the derived
p. 159-compatible simultaneous-approximation rows.  The chosen factor
`144 = 12²` supplies two further powers of the common endpoint ideal. -/
def literalRhinSquareShiftPolynomial (n : ℕ) (j : Fin 3) : ℤ[X] :=
  C 144 * X ^ (j : ℕ) * literalRhinPolynomial n ^ 2

/-- Shifting the literal square transports coefficients by the shift index
and multiplies them by the exact fixed factor `144`. -/
theorem literalRhinSquareShiftPolynomial_coeff
    (n : ℕ) (j : Fin 3) (k : ℕ) :
    (literalRhinSquareShiftPolynomial n j).coeff (k + (j : ℕ)) =
      144 * (literalRhinPolynomial n ^ 2).coeff k := by
  simp [literalRhinSquareShiftPolynomial, mul_assoc]

/-- The coefficient selected by the p. 159 row is one of the three central
coefficients of the unshifted square. -/
theorem literalRhinSquareShiftPolynomial_coeff_at_scale
    (n : ℕ) (j : Fin 3) :
    (literalRhinSquareShiftPolynomial n j).coeff
        (literalRhinSquareScale n) =
      144 * (literalRhinPolynomial n ^ 2).coeff
        (literalRhinSquareScale n - (j : ℕ)) := by
  have hj : (j : ℕ) ≤ literalRhinSquareScale n := by
    have hj3 := j.isLt
    simp only [literalRhinSquareScale]
    omega
  calc
    (literalRhinSquareShiftPolynomial n j).coeff
        (literalRhinSquareScale n) =
      (literalRhinSquareShiftPolynomial n j).coeff
        ((literalRhinSquareScale n - (j : ℕ)) + (j : ℕ)) := by
          rw [Nat.sub_add_cancel hj]
    _ = 144 * (literalRhinPolynomial n ^ 2).coeff
        (literalRhinSquareScale n - (j : ℕ)) :=
      literalRhinSquareShiftPolynomial_coeff n j _

/-- Uniform base-`24` bound for the coefficient selected as the denominator
of each one of the three common-scale rows. -/
theorem literalRhinSquareShiftPolynomial_coeff_natAbs_le
    (n : ℕ) (j : Fin 3) :
    Int.natAbs
        ((literalRhinSquareShiftPolynomial n j).coeff
          (literalRhinSquareScale n)) ≤
      144 * (((12 : ℕ) ^ 7 * 24 ^ n) ^ 2) := by
  rw [literalRhinSquareShiftPolynomial_coeff_at_scale, Int.natAbs_mul]
  simpa using Nat.mul_le_mul_left 144
    (literalRhinSquare_coeff_natAbs_le n
      (literalRhinSquareScale n - (j : ℕ)))

/-- The denominating coefficients of the three square shifts have the
alternating `+,-,+` pattern required by the ordered-moment determinant. -/
theorem literalRhinSquareShiftPolynomial_coeff_signs
    (n : ℕ) (hn : 8 ≤ n) :
    0 < (literalRhinSquareShiftPolynomial n 0).coeff
        (literalRhinSquareScale n) ∧
      (literalRhinSquareShiftPolynomial n 1).coeff
          (literalRhinSquareScale n) < 0 ∧
      0 < (literalRhinSquareShiftPolynomial n 2).coeff
          (literalRhinSquareScale n) := by
  constructor
  · rw [literalRhinSquareShiftPolynomial_coeff_at_scale]
    simp only [literalRhinSquareScale, Fin.val_zero, Nat.sub_zero]
    exact mul_pos (by norm_num) (literalRhinSquare_coeff_N_pos n hn)
  constructor
  · rw [literalRhinSquareShiftPolynomial_coeff_at_scale]
    simpa only [literalRhinSquareScale, Fin.val_one, Nat.reduceSubDiff]
      using mul_neg_of_pos_of_neg (by norm_num : (0 : ℤ) < 144)
        (literalRhinSquare_coeff_N_sub_one_neg n hn)
  · rw [literalRhinSquareShiftPolynomial_coeff_at_scale]
    simpa only [literalRhinSquareScale, Fin.val_two, Nat.reduceSubDiff]
      using mul_pos (by norm_num : (0 : ℤ) < 144)
        (literalRhinSquare_coeff_N_sub_two_pos n hn)

/-- Every square shift satisfies the p. 159 degree cap at its common scale. -/
theorem literalRhinSquareShiftPolynomial_natDegree_le
    (n : ℕ) (j : Fin 3) :
    (literalRhinSquareShiftPolynomial n j).natDegree ≤
      2 * literalRhinSquareScale n := by
  have hLeft : (C (144 : ℤ) * X ^ (j : ℕ)).natDegree ≤ (j : ℕ) := by
    calc
      (C (144 : ℤ) * X ^ (j : ℕ)).natDegree ≤
          (C (144 : ℤ)).natDegree + (X ^ (j : ℕ) : ℤ[X]).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + (j : ℕ) := by simp
      _ = (j : ℕ) := Nat.zero_add _
  have hSquare : (literalRhinPolynomial n ^ 2).natDegree ≤ 4 * n := by
    calc
      (literalRhinPolynomial n ^ 2).natDegree ≤
          2 * (literalRhinPolynomial n).natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ 2 * (2 * n) :=
        Nat.mul_le_mul_left 2 (literalRhinPolynomial_natDegree_le n)
      _ = 4 * n := by omega
  calc
    (literalRhinSquareShiftPolynomial n j).natDegree ≤
        (C (144 : ℤ) * X ^ (j : ℕ)).natDegree +
          (literalRhinPolynomial n ^ 2).natDegree := by
      exact Polynomial.natDegree_mul_le
    _ ≤ (j : ℕ) + 4 * n := Nat.add_le_add hLeft hSquare
    _ ≤ 2 * literalRhinSquareScale n := by
      have hj := j.isLt
      simp only [literalRhinSquareScale]
      omega

/-- The common nonnegative density whose first three moments are the two
residual columns of the literal square rows. -/
def literalRhinSquareDensity (n : ℕ) (x : ℝ) : ℝ :=
  144 * ((literalRhinPolynomial n).eval₂ (Int.castRingHom ℝ) x) ^ 2 /
    x ^ (literalRhinSquareScale n + 1)

/-- The continuous-remainder integrand is definitionally the corresponding
moment of the common square density. -/
theorem literalRhinSquareIntegrand_eq_moment
    (n : ℕ) (j : Fin 3) (x : ℝ) :
    literalRhinSquareIntegrand n (j : ℕ) x =
      x ^ (j : ℕ) * literalRhinSquareDensity n x := by
  have hScale : literalRhinSquareScale n + 1 = 2 * n + 3 := by
    simp only [literalRhinSquareScale]
  rw [literalRhinSquareIntegrand, literalRhinSquareDensity, hScale]
  ring

/-- Evaluation of the three shifted squares is exactly multiplication of the
common density by `x^j`. -/
theorem literalRhinSquareShift_integrand_eq_moment
    (n : ℕ) (j : Fin 3) (x : ℝ) :
    (literalRhinSquareShiftPolynomial n j).eval₂ (Int.castRingHom ℝ) x /
        x ^ (literalRhinSquareScale n + 1) =
      x ^ (j : ℕ) * literalRhinSquareDensity n x := by
  simp only [literalRhinSquareShiftPolynomial, literalRhinSquareDensity,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_pow]
  norm_num
  ring

/-- The derived p. 159-compatible integrals of the shifted squares are the
first three moments of one common density. -/
theorem intervalIntegral_literalRhinSquareShift_eq_moment
    (n : ℕ) (j : Fin 3) (a b : ℝ) :
    (∫ x in a..b,
      (literalRhinSquareShiftPolynomial n j).eval₂ (Int.castRingHom ℝ) x /
        x ^ (literalRhinSquareScale n + 1)) =
      ∫ x in a..b, x ^ (j : ℕ) * literalRhinSquareDensity n x := by
  apply intervalIntegral.integral_congr
  intro x _hx
  exact literalRhinSquareShift_integrand_eq_moment n j x

/-- The common literal-square density is continuous on the positive source
interval. -/
theorem literalRhinSquareDensity_continuousOn (n : ℕ) :
    ContinuousOn (literalRhinSquareDensity n) (Set.Icc 2 4) := by
  apply ContinuousOn.div
  · exact continuousOn_const.mul
      (((literalRhinPolynomial n).continuous_eval₂
        (Int.castRingHom ℝ)).continuousOn.pow 2)
  · exact continuousOn_id.pow (literalRhinSquareScale n + 1)
  · intro x hx
    exact pow_ne_zero _ (by linarith [hx.1])

/-- The common literal-square density is nonnegative throughout the source
interval. -/
theorem literalRhinSquareDensity_nonneg (n : ℕ) :
    ∀ x ∈ Set.Icc (2 : ℝ) 4, 0 ≤ literalRhinSquareDensity n x := by
  intro x hx
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (pow_nonneg (by linarith [hx.1]) _)

/-- The literal p. 162 polynomial is nonzero at the exact left-side witness
`5/2`; all six printed factors are checked symbolically. -/
theorem literalRhinPolynomial_eval_five_halves_ne_zero (n : ℕ) :
    (literalRhinPolynomial n).eval₂
        (Int.castRingHom ℝ) (5 / 2 : ℝ) ≠ 0 := by
  simp [literalRhinPolynomial, literalRhinFactor, literalRhinFactor1,
    literalRhinFactor2, literalRhinFactor3, literalRhinFactor4,
    literalRhinFactor5, literalRhinFactor6, Fin.prod_univ_succ,
    Polynomial.eval₂_pow]
  norm_num

/-- The literal p. 162 polynomial is nonzero at the exact right-side witness
`7/2`; all six printed factors are checked symbolically. -/
theorem literalRhinPolynomial_eval_seven_halves_ne_zero (n : ℕ) :
    (literalRhinPolynomial n).eval₂
        (Int.castRingHom ℝ) (7 / 2 : ℝ) ≠ 0 := by
  simp [literalRhinPolynomial, literalRhinFactor, literalRhinFactor1,
    literalRhinFactor2, literalRhinFactor3, literalRhinFactor4,
    literalRhinFactor5, literalRhinFactor6, Fin.prod_univ_succ,
    Polynomial.eval₂_pow]
  norm_num

/-- The common density has a strict positive witness inside `(2,3)`. -/
theorem literalRhinSquareDensity_pos_five_halves (n : ℕ) :
    0 < literalRhinSquareDensity n (5 / 2 : ℝ) := by
  apply div_pos
  · exact mul_pos (by norm_num)
      (sq_pos_of_ne_zero (literalRhinPolynomial_eval_five_halves_ne_zero n))
  · positivity

/-- The common density has a strict positive witness inside `(3,4)`. -/
theorem literalRhinSquareDensity_pos_seven_halves (n : ℕ) :
    0 < literalRhinSquareDensity n (7 / 2 : ℝ) := by
  apply div_pos
  · exact mul_pos (by norm_num)
      (sq_pos_of_ne_zero (literalRhinPolynomial_eval_seven_halves_ne_zero n))
  · positivity

/-- Every square shift lies in the common endpoint ideal power at the same
scale.  This is the exact integrality input for all three p. 159 rows. -/
theorem literalRhinSquareShiftPolynomial_mem_twelveXIdeal_pow
    (n : ℕ) (j : Fin 3) :
    literalRhinSquareShiftPolynomial n j ∈
      twelveXIdeal ^ literalRhinSquareScale n := by
  have hX : (X : ℤ[X]) ∈ twelveXIdeal := by
    apply Ideal.subset_span
    simp
  have hTwelve : C (12 : ℤ) ∈ twelveXIdeal := by
    apply Ideal.subset_span
    simp
  have h144 : C (144 : ℤ) ∈ twelveXIdeal ^ 2 := by
    have hMul := Ideal.mul_mem_mul hTwelve hTwelve
    convert hMul using 1 <;> norm_num [pow_two, map_mul]
  have hXPow : X ^ (j : ℕ) ∈ twelveXIdeal ^ (j : ℕ) :=
    Ideal.pow_mem_pow hX (j : ℕ)
  have hSquare : literalRhinPolynomial n ^ 2 ∈ twelveXIdeal ^ (n * 2) :=
    power_mem_scaled_power (m := 2)
      (literalRhinPolynomial_mem_twelveXIdeal_pow n)
  have hLeft :
      C (144 : ℤ) * X ^ (j : ℕ) ∈ twelveXIdeal ^ (2 + (j : ℕ)) :=
    mul_mem_pow_add h144 hXPow
  have hAll :
      C (144 : ℤ) * X ^ (j : ℕ) * literalRhinPolynomial n ^ 2 ∈
        twelveXIdeal ^ ((2 + (j : ℕ)) + n * 2) :=
    mul_mem_pow_add hLeft hSquare
  apply (Ideal.pow_le_pow_right (I := twelveXIdeal)
    (m := literalRhinSquareScale n)
    (n := (2 + (j : ℕ)) + n * 2) (by
      simp only [literalRhinSquareScale]
      omega))
  simpa only [literalRhinSquareShiftPolynomial] using hAll

/-- The ideal certificate supplies the coefficientwise endpoint divisibility
needed by the deterministic integer-row construction. -/
theorem literalRhinSquareShiftPolynomial_hasTwelveEndpointDivisibility
    (n : ℕ) (j : Fin 3) :
    HasTwelveEndpointDivisibility (literalRhinSquareShiftPolynomial n j)
      (literalRhinSquareScale n) :=
  hasTwelveEndpointDivisibility_of_mem_twelveXIdeal_pow
    (literalRhinSquareScale n) (literalRhinSquareShiftPolynomial n j)
    (literalRhinSquareShiftPolynomial_mem_twelveXIdeal_pow n j)

/-- Select the least shift at which a positive geometric error falls below a
positive target.  Away from the initial index, minimality gives the strict
predecessor inequality needed to bound geometric denominator growth. -/
theorem exists_least_geometric_scale
    {E rho T : ℝ} (start : ℕ)
    (hE : 0 < E) (hRho : 0 < rho) (hRhoOne : rho < 1)
    (hT : 0 < T) :
    ∃ k : ℕ,
      E * rho ^ (start + k) ≤ T ∧
        (k = 0 ∨ T < E * rho ^ (start + (k - 1))) := by
  have hScalePos : 0 < E * rho ^ start :=
    mul_pos hE (pow_pos hRho _)
  obtain ⟨witness, hWitness⟩ :=
    exists_pow_lt_of_lt_one (div_pos hT hScalePos) hRhoOne
  have hWitness' : E * rho ^ (start + witness) < T := by
    have hMul := (lt_div_iff₀ hScalePos).mp hWitness
    simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hMul
  let P : ℕ → Prop := fun k => E * rho ^ (start + k) ≤ T
  have hExists : ∃ k : ℕ, P k :=
    ⟨witness, hWitness'.le⟩
  let k : ℕ := Nat.find hExists
  have hk : P k := Nat.find_spec hExists
  refine ⟨k, hk, ?_⟩
  by_cases hkZero : k = 0
  · exact Or.inl hkZero
  · right
    by_contra hNot
    have hPrevious : P (k - 1) := by
      dsimp only [P]
      exact le_of_not_gt hNot
    have hImpossible : k ≤ k - 1 := by
      dsimp only [k]
      exact Nat.find_min' hExists hPrevious
    have hPreviousLt : k - 1 < k :=
      Nat.sub_lt (Nat.zero_lt_of_ne_zero hkZero) (by decide)
    exact (Nat.not_lt_of_ge hImpossible) hPreviousLt

/-- A strict lower bound for a decaying geometric term controls the matching
growing power when one integer exponent absorbs both bases. -/
theorem geometric_growth_le_of_decay_lower
    {E T Q rho : ℝ} {p s : ℕ}
    (hE : 0 < E) (hT : 0 < T) (hQ : 0 < Q) (hRho : 0 < rho)
    (hLower : T < E * rho ^ p)
    (hBase : Q * rho ^ s ≤ 1) :
    Q ^ p ≤ (E / T) ^ s := by
  have hTpow : 0 < T ^ s := pow_pos hT _
  have hLowerPow : T ^ s ≤ (E * rho ^ p) ^ s :=
    pow_le_pow_left₀ hT.le hLower.le _
  have hBaseNonneg : 0 ≤ Q * rho ^ s :=
    mul_nonneg hQ.le (pow_nonneg hRho.le _)
  have hBasePow : (Q * rho ^ s) ^ p ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hBaseNonneg hBase p
  have hProduct : Q ^ p * T ^ s ≤ E ^ s := by
    calc
      Q ^ p * T ^ s ≤ Q ^ p * (E * rho ^ p) ^ s :=
        mul_le_mul_of_nonneg_left hLowerPow (pow_nonneg hQ.le _)
      _ = E ^ s * (Q * rho ^ s) ^ p := by
        simp only [mul_pow]
        ring
      _ ≤ E ^ s * 1 :=
        mul_le_mul_of_nonneg_left hBasePow (pow_nonneg hE.le _)
      _ = E ^ s := mul_one _
  have hDiv : Q ^ p ≤ E ^ s / T ^ s :=
    (le_div_iff₀ hTpow).mpr hProduct
  simpa only [div_pow] using hDiv

/-- One integral simultaneous-approximation row. -/
structure SimultaneousLogApproximationRow where
  denominator : ℤ
  numerator23 : ℤ
  numerator34 : ℤ

/-- The exact quotient of a low coefficient by the endpoint power certified
by `HasTwelveEndpointDivisibility`. -/
def p159EndpointQuotient (G : ℤ[X]) (N d : ℕ) : ℤ :=
  G.coeff (N - d) / (12 : ℤ) ^ d

/-- The integral quotient `lcm(1,...,N) / d`. -/
def p159LCMQuotient (N d : ℕ) : ℤ :=
  ((rangeLCM N / d : ℕ) : ℤ)

theorem p159EndpointQuotient_mul
    {G : ℤ[X]} {N d : ℕ}
    (hG : HasTwelveEndpointDivisibility G N)
    (hd : 1 ≤ d) (hdN : d ≤ N) :
    p159EndpointQuotient G N d * (12 : ℤ) ^ d =
      G.coeff (N - d) := by
  exact Int.ediv_mul_cancel (hG d hd hdN)

theorem p159LCMQuotient_mul
    {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    p159LCMQuotient N d * (d : ℤ) = (rangeLCM N : ℤ) := by
  have hDvd : d ∣ rangeLCM N :=
    denominator_dvd_rangeLCM hd hdN
  have hNat : (rangeLCM N / d) * d = rangeLCM N := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel' hDvd
  unfold p159LCMQuotient
  exact_mod_cast hNat

/-- The integer rational part of the `[2,3]` p. 159 integral after endpoint
powers and all antiderivative denominators have been cleared. -/
def p159Remainder23 (G : ℤ[X]) (N : ℕ) : ℤ :=
  (∑ d ∈ Finset.Icc 1 N,
      p159LCMQuotient N d * p159EndpointQuotient G N d *
        (2 : ℤ) ^ d * ((3 : ℤ) ^ d - (2 : ℤ) ^ d)) +
    ∑ r ∈ Finset.Icc 1 N,
      p159LCMQuotient N r * G.coeff (N + r) *
        ((3 : ℤ) ^ r - (2 : ℤ) ^ r)

/-- The integer rational part of the `[3,4]` p. 159 integral after endpoint
powers and all antiderivative denominators have been cleared. -/
def p159Remainder34 (G : ℤ[X]) (N : ℕ) : ℤ :=
  (∑ d ∈ Finset.Icc 1 N,
      p159LCMQuotient N d * p159EndpointQuotient G N d *
        ((4 : ℤ) ^ d - (3 : ℤ) ^ d)) +
    ∑ r ∈ Finset.Icc 1 N,
      p159LCMQuotient N r * G.coeff (N + r) *
        ((4 : ℤ) ^ r - (3 : ℤ) ^ r)

/-- The canonical source-faithful integer row attached to `G` at scale `N`.
The minus sign in the third field matches the residual convention consumed
by the ordered-moment determinant. -/
def p159Row (G : ℤ[X]) (N : ℕ) :
    SimultaneousLogApproximationRow where
  denominator := (rangeLCM N : ℤ) * G.coeff N
  numerator23 := p159Remainder23 G N
  numerator34 := -p159Remainder34 G N

/-- The three deterministic p. 159 rows attached to the literal square
shifts at their common scale. -/
def literalRhinSquareRows (n : ℕ) (j : Fin 3) :
    SimultaneousLogApproximationRow :=
  p159Row (literalRhinSquareShiftPolynomial n j) (literalRhinSquareScale n)

/-- Exact common-row denominator bound obtained from one base-three LCM
estimate at the common scale.  The shift scalar contributes `144` once, and
`3^(2*n+2)` contributes the constant factor `9`. -/
theorem literalRhinSquareRows_denominator_natAbs_le
    (K n : ℕ)
    (hLCM : rangeLCM (literalRhinSquareScale n) ≤
      K * 3 ^ literalRhinSquareScale n)
    (j : Fin 3) :
    Int.natAbs (literalRhinSquareRows n j).denominator ≤
      1296 * K * ((12 : ℕ) ^ 7) ^ 2 * ((72 : ℕ) ^ 2) ^ n := by
  have h24 : ((24 : ℕ) ^ n) ^ 2 = (24 ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  have hRate :
      ((3 : ℕ) ^ 2) ^ n * ((24 : ℕ) ^ 2) ^ n =
        ((72 : ℕ) ^ 2) ^ n := by
    rw [← mul_pow]
    norm_num
  have hProduct := Nat.mul_le_mul hLCM
    (literalRhinSquareShiftPolynomial_coeff_natAbs_le n j)
  rw [literalRhinSquareRows, p159Row, Int.natAbs_mul,
    Int.natAbs_natCast]
  refine hProduct.trans_eq ?_
  rw [literalRhinSquareScale]
  simp only [pow_add, pow_mul, mul_pow]
  rw [h24, ← hRate]
  ring

/-- The literal square rows have the alternating denominator signs consumed
by the ordered-moment determinant. -/
theorem literalRhinSquareRows_denominator_signs
    (n : ℕ) (hn : 8 ≤ n) :
    0 < ((literalRhinSquareRows n 0).denominator : ℝ) ∧
      ((literalRhinSquareRows n 1).denominator : ℝ) < 0 ∧
      0 < ((literalRhinSquareRows n 2).denominator : ℝ) := by
  have hLCM :
      (0 : ℤ) < (rangeLCM (literalRhinSquareScale n) : ℤ) := by
    exact_mod_cast rangeLCM_pos (literalRhinSquareScale n)
  rcases literalRhinSquareShiftPolynomial_coeff_signs n hn with
    ⟨hc₀, hc₁, hc₂⟩
  have hq₀ : (0 : ℤ) < (literalRhinSquareRows n 0).denominator := by
    simpa only [literalRhinSquareRows, p159Row] using mul_pos hLCM hc₀
  have hq₁ : (literalRhinSquareRows n 1).denominator < (0 : ℤ) := by
    simpa only [literalRhinSquareRows, p159Row] using
      mul_neg_of_pos_of_neg hLCM hc₁
  have hq₂ : (0 : ℤ) < (literalRhinSquareRows n 2).denominator := by
    simpa only [literalRhinSquareRows, p159Row] using mul_pos hLCM hc₂
  exact ⟨by exact_mod_cast hq₀, by exact_mod_cast hq₁,
    by exact_mod_cast hq₂⟩

/-- The coefficient-linear rational part of the `[2,3]` integral before
multiplication by `rangeLCM`. -/
def p159RealRemainder23 (G : ℤ[X]) (N : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 N,
      (G.coeff (N - d) : ℝ) *
        ((3 : ℝ) ^ d - (2 : ℝ) ^ d) /
          ((d : ℝ) * (6 : ℝ) ^ d)) +
    ∑ r ∈ Finset.Icc 1 N,
      (G.coeff (N + r) : ℝ) *
        ((3 : ℝ) ^ r - (2 : ℝ) ^ r) / (r : ℝ)

/-- The coefficient-linear rational part of the `[3,4]` integral before
multiplication by `rangeLCM`. -/
def p159RealRemainder34 (G : ℤ[X]) (N : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 N,
      (G.coeff (N - d) : ℝ) *
        ((4 : ℝ) ^ d - (3 : ℝ) ^ d) /
          ((d : ℝ) * (12 : ℝ) ^ d)) +
    ∑ r ∈ Finset.Icc 1 N,
      (G.coeff (N + r) : ℝ) *
        ((4 : ℝ) ^ r - (3 : ℝ) ^ r) / (r : ℝ)

private theorem sum_range_eq_sum_Icc_reflect
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    (∑ k ∈ Finset.range N, f k) =
      ∑ d ∈ Finset.Icc 1 N, f (N - d) := by
  classical
  apply Finset.sum_bij (fun k _hk ↦ N - k)
  · intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le N k⟩
  · intro k₁ hk₁ k₂ hk₂ hEq
    have hk₁N : k₁ < N := Finset.mem_range.mp hk₁
    have hk₂N : k₂ < N := Finset.mem_range.mp hk₂
    omega
  · intro d hd
    have hdBounds := Finset.mem_Icc.mp hd
    refine ⟨N - d, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    congr 1
    omega

private theorem sum_range_succ_shift_eq_sum_Icc
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    (∑ i ∈ Finset.range N, f (i + 1)) =
      ∑ r ∈ Finset.Icc 1 N, f r := by
  classical
  apply Finset.sum_bij (fun i _hi ↦ i + 1)
  · intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i₁ _hi₁ i₂ _hi₂ hEq
    omega
  · intro r hr
    have hrBounds := Finset.mem_Icc.mp hr
    refine ⟨r - 1, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro i _hi
    rfl

private theorem sum_range_two_mul_add_one_eq_range_center_range
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N + 1), f k) =
      (∑ k ∈ Finset.range N, f k) +
        (f N + ∑ i ∈ Finset.range N, f (N + (i + 1))) := by
  calc
    (∑ k ∈ Finset.range (2 * N + 1), f k) =
        (∑ k ∈ Finset.range N, f k) +
          ∑ i ∈ Finset.range (1 + N), f (N + i) := by
      rw [show 2 * N + 1 = N + (1 + N) by omega]
      exact Finset.sum_range_add f N (1 + N)
    _ = (∑ k ∈ Finset.range N, f k) +
          (f N + ∑ i ∈ Finset.range N, f (N + (i + 1))) := by
      apply congrArg (fun z ↦ (∑ k ∈ Finset.range N, f k) + z)
      calc
        (∑ i ∈ Finset.range (1 + N), f (N + i)) =
            (∑ i ∈ Finset.range 1, f (N + i)) +
              ∑ i ∈ Finset.range N, f (N + (1 + i)) :=
          Finset.sum_range_add (fun i ↦ f (N + i)) 1 N
        _ = f N + ∑ i ∈ Finset.range N, f (N + (i + 1)) := by
          simp only [Finset.sum_range_one, Nat.add_zero]
          apply congrArg (fun z ↦ f N + z)
          apply Finset.sum_congr rfl
          intro i _hi
          congr 1
          omega

private theorem sum_range_two_mul_add_one_eq_Icc_center_Icc
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N + 1), f k) =
      (∑ d ∈ Finset.Icc 1 N, f (N - d)) +
        (f N + ∑ r ∈ Finset.Icc 1 N, f (N + r)) := by
  have hLow :
      (∑ k ∈ Finset.range N, f k) =
        ∑ d ∈ Finset.Icc 1 N, f (N - d) :=
    sum_range_eq_sum_Icc_reflect f N
  have hHigh :
      (∑ i ∈ Finset.range N, f (N + (i + 1))) =
        ∑ r ∈ Finset.Icc 1 N, f (N + r) := by
    simpa only using
      sum_range_succ_shift_eq_sum_Icc (fun r ↦ f (N + r)) N
  calc
    (∑ k ∈ Finset.range (2 * N + 1), f k) =
        (∑ k ∈ Finset.range N, f k) +
          (f N + ∑ i ∈ Finset.range N, f (N + (i + 1))) :=
      sum_range_two_mul_add_one_eq_range_center_range f N
    _ = (∑ d ∈ Finset.Icc 1 N, f (N - d)) +
          (f N + ∑ i ∈ Finset.range N, f (N + (i + 1))) :=
      congrArg
        (fun z ↦ z + (f N + ∑ i ∈ Finset.range N, f (N + (i + 1)))) hLow
    _ = (∑ d ∈ Finset.Icc 1 N, f (N - d)) +
          (f N + ∑ r ∈ Finset.Icc 1 N, f (N + r)) :=
      congrArg
        (fun z ↦ (∑ d ∈ Finset.Icc 1 N, f (N - d)) + (f N + z)) hHigh

private theorem eval₂_eq_Icc_center_Icc
    {S : Type*} [Semiring S] (phi : ℤ →+* S)
    (G : ℤ[X]) (x : S) (N : ℕ)
    (hDegree : G.natDegree ≤ 2 * N) :
    G.eval₂ phi x =
      (∑ d ∈ Finset.Icc 1 N,
        phi (G.coeff (N - d)) * x ^ (N - d)) +
      (phi (G.coeff N) * x ^ N +
        ∑ r ∈ Finset.Icc 1 N,
          phi (G.coeff (N + r)) * x ^ (N + r)) := by
  calc
    G.eval₂ phi x =
        ∑ k ∈ Finset.range (2 * N + 1),
          phi (G.coeff k) * x ^ k :=
      Polynomial.eval₂_eq_sum_range' phi
        (by omega : G.natDegree < 2 * N + 1) x
    _ = _ :=
      sum_range_two_mul_add_one_eq_Icc_center_Icc
        (fun k ↦ phi (G.coeff k) * x ^ k) N

private theorem integral_low_monomial
    (c : ℝ) (N d : ℕ) (hd : d < N)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in a..b, c * x ^ (N - (d + 1)) / x ^ (N + 1)) =
      c * (b ^ (d + 1) - a ^ (d + 1)) /
        (((d + 1 : ℕ) : ℝ) * (a * b) ^ (d + 1)) := by
  have hzero : (0 : ℝ) ∉ [[a, b]] := Set.notMem_uIcc_of_lt ha hb
  have hEq :
      Set.EqOn
        (fun x : ℝ ↦ c * x ^ (N - (d + 1)) / x ^ (N + 1))
        (fun x : ℝ ↦ c * x ^ (-((d + 2 : ℕ) : ℤ))) [[a, b]] := by
    intro x hx
    dsimp only
    have hx0 : x ≠ 0 := ne_of_mem_of_not_mem hx hzero
    rw [zpow_neg, zpow_natCast]
    field_simp [hx0]
    rw [mul_assoc, ← pow_add,
      show N - (d + 1) + (d + 2) = N + 1 by omega]
  rw [intervalIntegral.integral_congr hEq,
    intervalIntegral.integral_const_mul,
    integral_zpow (n := -((d + 2 : ℕ) : ℤ))
      (Or.inr ⟨by omega, hzero⟩)]
  have hExpZ :
      -((d + 2 : ℕ) : ℤ) + 1 = -((d + 1 : ℕ) : ℤ) := by
    omega
  rw [hExpZ]
  push_cast
  have hDen : -((d : ℝ) + 2) + 1 = -((d : ℝ) + 1) := by
    ring
  rw [hDen, zpow_neg, zpow_neg]
  have hPos : (d : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) := by
    omega
  rw [hPos]
  simp only [zpow_natCast]
  rw [mul_pow]
  field_simp [ha.ne', hb.ne', show ((d + 1 : ℕ) : ℝ) ≠ 0 by positivity]
  ring

private theorem integral_central_monomial
    (c : ℝ) (N : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in a..b, c * x ^ N / x ^ (N + 1)) =
      c * Real.log (b / a) := by
  have hzero : (0 : ℝ) ∉ [[a, b]] := Set.notMem_uIcc_of_lt ha hb
  have hEq :
      Set.EqOn
        (fun x : ℝ ↦ c * x ^ N / x ^ (N + 1))
        (fun x : ℝ ↦ c * x⁻¹) [[a, b]] := by
    intro x hx
    dsimp only
    have hx0 : x ≠ 0 := ne_of_mem_of_not_mem hx hzero
    field_simp [hx0]
    rw [pow_succ]
    ring
  calc
    (∫ x in a..b, c * x ^ N / x ^ (N + 1)) =
        ∫ x in a..b, c * x⁻¹ :=
      intervalIntegral.integral_congr hEq
    _ = c * ∫ x in a..b, x⁻¹ :=
      intervalIntegral.integral_const_mul c (fun x : ℝ ↦ x⁻¹)
    _ = c * Real.log (b / a) := by
      rw [integral_inv_of_pos ha hb]

private theorem integral_high_monomial
    (c : ℝ) (N r : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in a..b, c * x ^ (N + (r + 1)) / x ^ (N + 1)) =
      c * (b ^ (r + 1) - a ^ (r + 1)) / ((r + 1 : ℕ) : ℝ) := by
  have hzero : (0 : ℝ) ∉ [[a, b]] := Set.notMem_uIcc_of_lt ha hb
  have hEq :
      Set.EqOn
        (fun x : ℝ ↦ c * x ^ (N + (r + 1)) / x ^ (N + 1))
        (fun x : ℝ ↦ c * x ^ r) [[a, b]] := by
    intro x hx
    dsimp only
    have hx0 : x ≠ 0 := ne_of_mem_of_not_mem hx hzero
    field_simp [hx0]
    rw [show N + (r + 1) = (N + 1) + r by omega, pow_add]
    ring
  calc
    (∫ x in a..b, c * x ^ (N + (r + 1)) / x ^ (N + 1)) =
        ∫ x in a..b, c * x ^ r :=
      intervalIntegral.integral_congr hEq
    _ = c * ∫ x in a..b, x ^ r :=
      intervalIntegral.integral_const_mul c (fun x : ℝ ↦ x ^ r)
    _ = c * (b ^ (r + 1) - a ^ (r + 1)) / ((r + 1 : ℕ) : ℝ) := by
      rw [integral_pow]
      push_cast
      ring

/-- Rhin's p. 159 termwise antiderivative identity, arranged in the exact
low/central/high coefficient form used by the deterministic row. -/
theorem intervalIntegral_eval₂_div_pow_eq_low_central_high
    (G : ℤ[X]) (N : ℕ)
    (hdeg : G.natDegree ≤ 2 * N)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in a..b,
      G.eval₂ (Int.castRingHom ℝ) x / x ^ (N + 1)) =
      (∑ d ∈ Finset.Icc 1 N,
        (G.coeff (N - d) : ℝ) * (b ^ d - a ^ d) /
          ((d : ℝ) * (a * b) ^ d)) +
      (G.coeff N : ℝ) * Real.log (b / a) +
      (∑ r ∈ Finset.Icc 1 N,
        (G.coeff (N + r) : ℝ) * (b ^ r - a ^ r) / (r : ℝ)) := by
  have hzero : (0 : ℝ) ∉ [[a, b]] := Set.notMem_uIcc_of_lt ha hb
  have hMonomial : ∀ (c : ℝ) (k : ℕ),
      IntervalIntegrable
        (fun x : ℝ ↦ c * x ^ k / x ^ (N + 1))
        MeasureTheory.volume a b := by
    intro c k
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.mul (continuousOn_id.pow k)).div
      (continuousOn_id.pow (N + 1))
      (fun x hx ↦ pow_ne_zero _ (ne_of_mem_of_not_mem hx hzero))
  let low : ℕ → ℝ → ℝ := fun d x ↦
    (G.coeff (N - d) : ℝ) * x ^ (N - d) / x ^ (N + 1)
  let central : ℝ → ℝ := fun x ↦
    (G.coeff N : ℝ) * x ^ N / x ^ (N + 1)
  let high : ℕ → ℝ → ℝ := fun r x ↦
    (G.coeff (N + r) : ℝ) * x ^ (N + r) / x ^ (N + 1)
  have hLow : ∀ d ∈ Finset.Icc 1 N,
      IntervalIntegrable (low d) MeasureTheory.volume a b := by
    intro d _hd
    exact hMonomial (G.coeff (N - d) : ℝ) (N - d)
  have hCentral :
      IntervalIntegrable central MeasureTheory.volume a b :=
    hMonomial (G.coeff N : ℝ) N
  have hHigh : ∀ r ∈ Finset.Icc 1 N,
      IntervalIntegrable (high r) MeasureTheory.volume a b := by
    intro r _hr
    exact hMonomial (G.coeff (N + r) : ℝ) (N + r)
  have hLowSum :
      IntervalIntegrable
        (fun x ↦ ∑ d ∈ Finset.Icc 1 N, low d x)
        MeasureTheory.volume a b := by
    have hSum :
        IntervalIntegrable (∑ d ∈ Finset.Icc 1 N, low d)
          MeasureTheory.volume a b :=
      IntervalIntegrable.sum (Finset.Icc 1 N) hLow
    convert hSum using 1
    funext x
    simp only [Finset.sum_apply]
  have hHighSum :
      IntervalIntegrable
        (fun x ↦ ∑ r ∈ Finset.Icc 1 N, high r x)
        MeasureTheory.volume a b := by
    have hSum :
        IntervalIntegrable (∑ r ∈ Finset.Icc 1 N, high r)
          MeasureTheory.volume a b :=
      IntervalIntegrable.sum (Finset.Icc 1 N) hHigh
    convert hSum using 1
    funext x
    simp only [Finset.sum_apply]
  have hPointwise : Set.EqOn
      (fun x : ℝ ↦ G.eval₂ (Int.castRingHom ℝ) x / x ^ (N + 1))
      (fun x : ℝ ↦
        (∑ d ∈ Finset.Icc 1 N, low d x) +
          (central x + ∑ r ∈ Finset.Icc 1 N, high r x)) [[a, b]] := by
    intro x _hx
    dsimp only
    rw [eval₂_eq_Icc_center_Icc (Int.castRingHom ℝ) G x N hdeg]
    simp only [low, central, high, Int.coe_castRingHom]
    rw [add_div, add_div, Finset.sum_div, Finset.sum_div]
  calc
    (∫ x in a..b,
        G.eval₂ (Int.castRingHom ℝ) x / x ^ (N + 1)) =
        ∫ x in a..b,
          (∑ d ∈ Finset.Icc 1 N, low d x) +
            (central x + ∑ r ∈ Finset.Icc 1 N, high r x) :=
      intervalIntegral.integral_congr hPointwise
    _ = (∫ x in a..b, ∑ d ∈ Finset.Icc 1 N, low d x) +
          ((∫ x in a..b, central x) +
            ∫ x in a..b, ∑ r ∈ Finset.Icc 1 N, high r x) := by
      rw [intervalIntegral.integral_add hLowSum (hCentral.add hHighSum),
        intervalIntegral.integral_add hCentral hHighSum]
    _ = (∑ d ∈ Finset.Icc 1 N, (∫ x in a..b, low d x)) +
          ((∫ x in a..b, central x) +
            ∑ r ∈ Finset.Icc 1 N, (∫ x in a..b, high r x)) := by
      rw [intervalIntegral.integral_finset_sum hLow,
        intervalIntegral.integral_finset_sum hHigh]
    _ = (∑ d ∈ Finset.Icc 1 N,
          (G.coeff (N - d) : ℝ) * (b ^ d - a ^ d) /
            ((d : ℝ) * (a * b) ^ d)) +
        ((G.coeff N : ℝ) * Real.log (b / a) +
          ∑ r ∈ Finset.Icc 1 N,
            (G.coeff (N + r) : ℝ) * (b ^ r - a ^ r) / (r : ℝ)) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro d hd
        have hdBounds := Finset.mem_Icc.mp hd
        simpa only [low, Nat.sub_add_cancel hdBounds.1] using
          integral_low_monomial (G.coeff (N - d) : ℝ) N (d - 1)
            (by omega) ha hb
      · congr 1
        · exact integral_central_monomial (G.coeff N : ℝ) N ha hb
        · apply Finset.sum_congr rfl
          intro r hr
          have hrBounds := Finset.mem_Icc.mp hr
          simpa only [high, Nat.sub_add_cancel hrBounds.1] using
            integral_high_monomial (G.coeff (N + r) : ℝ) N (r - 1) ha hb
    _ = _ := by ring

/-- The central logarithm on `[2,3]` has Rhin's first sign convention. -/
theorem log_three_div_two_eq_neg_logTwoDivThree :
    Real.log ((3 : ℝ) / 2) = -logTwoDivThree := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  unfold logTwoDivThree
  ring

/-- The central logarithm on `[3,4]` is Rhin's second logarithm. -/
theorem log_four_div_three_eq_logFourDivThree :
    Real.log ((4 : ℝ) / 3) = logFourDivThree := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num [logFourDivThree]

/-- The p. 159 coefficient expansion on `[2,3]`, with the first logarithm
written in the convention used by approximation rows. -/
theorem intervalIntegral_p159_eq_23
    (G : ℤ[X]) (N : ℕ) (hdeg : G.natDegree ≤ 2 * N) :
    (∫ x in (2 : ℝ)..3,
      G.eval₂ (Int.castRingHom ℝ) x / x ^ (N + 1)) =
        p159RealRemainder23 G N -
          (G.coeff N : ℝ) * logTwoDivThree := by
  rw [intervalIntegral_eval₂_div_pow_eq_low_central_high
    G N hdeg (by norm_num) (by norm_num)]
  rw [log_three_div_two_eq_neg_logTwoDivThree]
  unfold p159RealRemainder23
  rw [show (2 : ℝ) * 3 = 6 by norm_num]
  ring

/-- The p. 159 coefficient expansion on `[3,4]`, with the second logarithm
written in the convention used by approximation rows. -/
theorem intervalIntegral_p159_eq_34
    (G : ℤ[X]) (N : ℕ) (hdeg : G.natDegree ≤ 2 * N) :
    (∫ x in (3 : ℝ)..4,
      G.eval₂ (Int.castRingHom ℝ) x / x ^ (N + 1)) =
        p159RealRemainder34 G N +
          (G.coeff N : ℝ) * logFourDivThree := by
  rw [intervalIntegral_eval₂_div_pow_eq_low_central_high
    G N hdeg (by norm_num) (by norm_num)]
  rw [log_four_div_three_eq_logFourDivThree]
  unfold p159RealRemainder34
  rw [show (3 : ℝ) * 4 = 12 by norm_num]
  ring

private theorem low23_cast
    {G : ℤ[X]} {N d : ℕ}
    (hG : HasTwelveEndpointDivisibility G N)
    (hd : 1 ≤ d) (hdN : d ≤ N) :
    ((p159LCMQuotient N d * p159EndpointQuotient G N d *
        (2 : ℤ) ^ d * ((3 : ℤ) ^ d - (2 : ℤ) ^ d) : ℤ) : ℝ) =
      (rangeLCM N : ℝ) *
        ((G.coeff (N - d) : ℝ) *
          ((3 : ℝ) ^ d - (2 : ℝ) ^ d) /
            ((d : ℝ) * (6 : ℝ) ^ d)) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hd
  have hD :
      (p159LCMQuotient N d : ℝ) * (d : ℝ) =
        (rangeLCM N : ℝ) := by
    exact_mod_cast p159LCMQuotient_mul hd hdN
  have hCoeff :
      (p159EndpointQuotient G N d : ℝ) * (12 : ℝ) ^ d =
        (G.coeff (N - d) : ℝ) := by
    exact_mod_cast p159EndpointQuotient_mul hG hd hdN
  have hTwelve :
      (12 : ℝ) ^ d = (2 : ℝ) ^ d * (6 : ℝ) ^ d := by
    calc
      (12 : ℝ) ^ d = ((2 : ℝ) * 6) ^ d := by norm_num
      _ = (2 : ℝ) ^ d * (6 : ℝ) ^ d := mul_pow _ _ _
  push_cast
  rw [← hD, ← hCoeff, hTwelve]
  field_simp [hd0]

private theorem high23_cast
    {G : ℤ[X]} {N r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N) :
    ((p159LCMQuotient N r * G.coeff (N + r) *
        ((3 : ℤ) ^ r - (2 : ℤ) ^ r) : ℤ) : ℝ) =
      (rangeLCM N : ℝ) *
        ((G.coeff (N + r) : ℝ) *
          ((3 : ℝ) ^ r - (2 : ℝ) ^ r) / (r : ℝ)) := by
  have hr0 : (r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hr
  have hD :
      (p159LCMQuotient N r : ℝ) * (r : ℝ) =
        (rangeLCM N : ℝ) := by
    exact_mod_cast p159LCMQuotient_mul hr hrN
  push_cast
  rw [← hD]
  field_simp [hr0]

private theorem low34_cast
    {G : ℤ[X]} {N d : ℕ}
    (hG : HasTwelveEndpointDivisibility G N)
    (hd : 1 ≤ d) (hdN : d ≤ N) :
    ((p159LCMQuotient N d * p159EndpointQuotient G N d *
        ((4 : ℤ) ^ d - (3 : ℤ) ^ d) : ℤ) : ℝ) =
      (rangeLCM N : ℝ) *
        ((G.coeff (N - d) : ℝ) *
          ((4 : ℝ) ^ d - (3 : ℝ) ^ d) /
            ((d : ℝ) * (12 : ℝ) ^ d)) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hd
  have hD :
      (p159LCMQuotient N d : ℝ) * (d : ℝ) =
        (rangeLCM N : ℝ) := by
    exact_mod_cast p159LCMQuotient_mul hd hdN
  have hCoeff :
      (p159EndpointQuotient G N d : ℝ) * (12 : ℝ) ^ d =
        (G.coeff (N - d) : ℝ) := by
    exact_mod_cast p159EndpointQuotient_mul hG hd hdN
  push_cast
  rw [← hD, ← hCoeff]
  field_simp [hd0]

private theorem high34_cast
    {G : ℤ[X]} {N r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N) :
    ((p159LCMQuotient N r * G.coeff (N + r) *
        ((4 : ℤ) ^ r - (3 : ℤ) ^ r) : ℤ) : ℝ) =
      (rangeLCM N : ℝ) *
        ((G.coeff (N + r) : ℝ) *
          ((4 : ℝ) ^ r - (3 : ℝ) ^ r) / (r : ℝ)) := by
  have hr0 : (r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hr
  have hD :
      (p159LCMQuotient N r : ℝ) * (r : ℝ) =
        (rangeLCM N : ℝ) := by
    exact_mod_cast p159LCMQuotient_mul hr hrN
  push_cast
  rw [← hD]
  field_simp [hr0]

/-- The first integer remainder is exactly `rangeLCM` times its real
coefficient expansion. -/
theorem p159Remainder23_cast
    {G : ℤ[X]} {N : ℕ}
    (hG : HasTwelveEndpointDivisibility G N) :
    (p159Remainder23 G N : ℝ) =
      (rangeLCM N : ℝ) * p159RealRemainder23 G N := by
  unfold p159Remainder23 p159RealRemainder23
  push_cast
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro d hdMem
    have hd := (Finset.mem_Icc.mp hdMem).1
    have hdN := (Finset.mem_Icc.mp hdMem).2
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sub] using
      low23_cast hG hd hdN
  · apply Finset.sum_congr rfl
    intro r hrMem
    have hr := (Finset.mem_Icc.mp hrMem).1
    have hrN := (Finset.mem_Icc.mp hrMem).2
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sub] using
      (high23_cast (G := G) hr hrN)

/-- The second integer remainder is exactly `rangeLCM` times its real
coefficient expansion. -/
theorem p159Remainder34_cast
    {G : ℤ[X]} {N : ℕ}
    (hG : HasTwelveEndpointDivisibility G N) :
    (p159Remainder34 G N : ℝ) =
      (rangeLCM N : ℝ) * p159RealRemainder34 G N := by
  unfold p159Remainder34 p159RealRemainder34
  push_cast
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro d hdMem
    have hd := (Finset.mem_Icc.mp hdMem).1
    have hdN := (Finset.mem_Icc.mp hdMem).2
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sub] using
      low34_cast hG hd hdN
  · apply Finset.sum_congr rfl
    intro r hrMem
    have hr := (Finset.mem_Icc.mp hrMem).1
    have hrN := (Finset.mem_Icc.mp hrMem).2
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sub] using
      (high34_cast (G := G) hr hrN)

/-- The canonical integer row has exactly the two coefficient-expansion
residuals required by the source integral identities.  The analytic layer
only needs to identify the parenthesized expressions with the two interval
integrals. -/
theorem p159Row_residuals_as_coefficient_expansions
    {G : ℤ[X]} {N : ℕ}
    (hG : HasTwelveEndpointDivisibility G N) :
    (((p159Row G N).numerator23 : ℝ) -
        ((p159Row G N).denominator : ℝ) * logTwoDivThree =
      (rangeLCM N : ℝ) *
        (p159RealRemainder23 G N -
          (G.coeff N : ℝ) * logTwoDivThree)) ∧
    (((p159Row G N).numerator34 : ℝ) -
        ((p159Row G N).denominator : ℝ) * logFourDivThree =
      -((rangeLCM N : ℝ) *
        (p159RealRemainder34 G N +
          (G.coeff N : ℝ) * logFourDivThree))) := by
  constructor
  · simp only [p159Row]
    rw [p159Remainder23_cast hG]
    push_cast
    ring
  · simp only [p159Row]
    push_cast
    rw [p159Remainder34_cast hG]
    ring

/-- Rhin's deterministic integer row has residuals equal to the two exact
interval integrals.  The minus sign on the `[3,4]` residual is part of the
source convention and is preserved explicitly. -/
theorem p159Row_residuals
    {G : ℤ[X]} {N : ℕ}
    (hG : HasTwelveEndpointDivisibility G N)
    (hdeg : G.natDegree ≤ 2 * N) :
    (((p159Row G N).numerator23 : ℝ) -
        ((p159Row G N).denominator : ℝ) * logTwoDivThree =
      (rangeLCM N : ℝ) *
        (∫ x in (2 : ℝ)..3,
          G.eval₂ (Int.castRingHom ℝ) x / x ^ (N + 1))) ∧
    (((p159Row G N).numerator34 : ℝ) -
        ((p159Row G N).denominator : ℝ) * logFourDivThree =
      -((rangeLCM N : ℝ) *
        (∫ x in (3 : ℝ)..4,
          G.eval₂ (Int.castRingHom ℝ) x / x ^ (N + 1)))) := by
  obtain ⟨h23, h34⟩ :=
    p159Row_residuals_as_coefficient_expansions hG
  constructor
  · calc
      _ = (rangeLCM N : ℝ) *
          (p159RealRemainder23 G N -
            (G.coeff N : ℝ) * logTwoDivThree) := h23
      _ = (rangeLCM N : ℝ) *
          (∫ x in (2 : ℝ)..3,
            G.eval₂ (Int.castRingHom ℝ) x / x ^ (N + 1)) := by
        rw [intervalIntegral_p159_eq_23 G N hdeg]
  · calc
      _ = -((rangeLCM N : ℝ) *
          (p159RealRemainder34 G N +
            (G.coeff N : ℝ) * logFourDivThree)) := h34
      _ = -((rangeLCM N : ℝ) *
          (∫ x in (3 : ℝ)..4,
            G.eval₂ (Int.castRingHom ℝ) x / x ^ (N + 1))) := by
        rw [intervalIntegral_p159_eq_34 G N hdeg]

/-- Each derived literal square row has exactly the two p. 159-compatible
integral residuals, with the source `[3,4]` sign preserved. -/
theorem literalRhinSquareRows_residuals (n : ℕ) (j : Fin 3) :
    (((literalRhinSquareRows n j).numerator23 : ℝ) -
        ((literalRhinSquareRows n j).denominator : ℝ) * logTwoDivThree =
      (rangeLCM (literalRhinSquareScale n) : ℝ) *
        (∫ x in (2 : ℝ)..3,
          (literalRhinSquareShiftPolynomial n j).eval₂
              (Int.castRingHom ℝ) x /
            x ^ (literalRhinSquareScale n + 1))) ∧
    (((literalRhinSquareRows n j).numerator34 : ℝ) -
        ((literalRhinSquareRows n j).denominator : ℝ) * logFourDivThree =
      -((rangeLCM (literalRhinSquareScale n) : ℝ) *
        (∫ x in (3 : ℝ)..4,
          (literalRhinSquareShiftPolynomial n j).eval₂
              (Int.castRingHom ℝ) x /
            x ^ (literalRhinSquareScale n + 1)))) := by
  simpa only [literalRhinSquareRows] using
    p159Row_residuals
      (literalRhinSquareShiftPolynomial_hasTwelveEndpointDivisibility n j)
      (literalRhinSquareShiftPolynomial_natDegree_le n j)

/-- Pair an approximation row with an integer coefficient triple. -/
def SimultaneousLogApproximationRow.pair
    (row : SimultaneousLogApproximationRow) (a b c : ℤ) : ℤ :=
  row.denominator * a + row.numerator23 * b + row.numerator34 * c

/-- The explicit determinant of three approximation rows. -/
def simultaneousLogApproximationDet
    (row₀ row₁ row₂ : SimultaneousLogApproximationRow) : ℤ :=
  row₀.denominator *
      (row₁.numerator23 * row₂.numerator34 -
        row₁.numerator34 * row₂.numerator23) -
    row₀.numerator23 *
      (row₁.denominator * row₂.numerator34 -
        row₁.numerator34 * row₂.denominator) +
    row₀.numerator34 *
      (row₁.denominator * row₂.numerator23 -
        row₁.numerator23 * row₂.denominator)

/-- A nonzero integer determinant supplies the exact row-separation property
used by the transference certificate. -/
theorem exists_row_pair_ne_zero_of_det_ne_zero
    (row₀ row₁ row₂ : SimultaneousLogApproximationRow)
    (hDet : simultaneousLogApproximationDet row₀ row₁ row₂ ≠ 0)
    (a b c : ℤ) (hCoefficients : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    row₀.pair a b c ≠ 0 ∨
      row₁.pair a b c ≠ 0 ∨
      row₂.pair a b c ≠ 0 := by
  by_contra hRows
  push Not at hRows
  rcases hRows with ⟨hRow₀, hRow₁, hRow₂⟩
  have haDet :
      simultaneousLogApproximationDet row₀ row₁ row₂ * a = 0 := by
    calc
      simultaneousLogApproximationDet row₀ row₁ row₂ * a =
          (row₁.numerator23 * row₂.numerator34 -
              row₁.numerator34 * row₂.numerator23) * row₀.pair a b c -
            (row₀.numerator23 * row₂.numerator34 -
              row₀.numerator34 * row₂.numerator23) * row₁.pair a b c +
            (row₀.numerator23 * row₁.numerator34 -
              row₀.numerator34 * row₁.numerator23) * row₂.pair a b c := by
        unfold simultaneousLogApproximationDet SimultaneousLogApproximationRow.pair
        ring
      _ = 0 := by rw [hRow₀, hRow₁, hRow₂]; ring
  have hbDet :
      simultaneousLogApproximationDet row₀ row₁ row₂ * b = 0 := by
    calc
      simultaneousLogApproximationDet row₀ row₁ row₂ * b =
          -(row₁.denominator * row₂.numerator34 -
              row₁.numerator34 * row₂.denominator) * row₀.pair a b c +
            (row₀.denominator * row₂.numerator34 -
              row₀.numerator34 * row₂.denominator) * row₁.pair a b c -
            (row₀.denominator * row₁.numerator34 -
              row₀.numerator34 * row₁.denominator) * row₂.pair a b c := by
        unfold simultaneousLogApproximationDet SimultaneousLogApproximationRow.pair
        ring
      _ = 0 := by rw [hRow₀, hRow₁, hRow₂]; ring
  have hcDet :
      simultaneousLogApproximationDet row₀ row₁ row₂ * c = 0 := by
    calc
      simultaneousLogApproximationDet row₀ row₁ row₂ * c =
          (row₁.denominator * row₂.numerator23 -
              row₁.numerator23 * row₂.denominator) * row₀.pair a b c -
            (row₀.denominator * row₂.numerator23 -
              row₀.numerator23 * row₂.denominator) * row₁.pair a b c +
            (row₀.denominator * row₁.numerator23 -
              row₀.numerator23 * row₁.denominator) * row₂.pair a b c := by
        unfold simultaneousLogApproximationDet SimultaneousLogApproximationRow.pair
        ring
      _ = 0 := by rw [hRow₀, hRow₁, hRow₂]; ring
  have ha : a = 0 := (mul_eq_zero.mp haDet).resolve_left hDet
  have hb : b = 0 := (mul_eq_zero.mp hbDet).resolve_left hDet
  have hc : c = 0 := (mul_eq_zero.mp hcDet).resolve_left hDet
  rcases hCoefficients with haNe | hbNe | hcNe
  · exact haNe ha
  · exact hbNe hb
  · exact hcNe hc

private def orderedMomentDet
    (q₀ q₁ q₂ i₀ i₁ i₂ k₀ k₁ k₂ : ℝ) : ℝ :=
  q₀ * (i₁ * (-k₂) - (-k₁) * i₂) -
    i₀ * (q₁ * (-k₂) - (-k₁) * q₂) +
      (-k₀) * (q₁ * i₂ - i₁ * q₂)

private theorem orderedMomentDet_neg
    (q₀ q₁ q₂ i₀ i₁ i₂ k₀ k₁ k₂ : ℝ)
    (hq₀ : 0 < q₀) (hq₁ : q₁ < 0) (hq₂ : 0 < q₂)
    (hCross₂ : 0 ≤ i₁ * k₂ - i₂ * k₁)
    (hCross₁ : 0 ≤ i₀ * k₂ - i₂ * k₀)
    (hCross₀ : 0 < i₀ * k₁ - i₁ * k₀) :
    orderedMomentDet q₀ q₁ q₂ i₀ i₁ i₂ k₀ k₁ k₂ < 0 := by
  unfold orderedMomentDet
  have hTerm₀ : 0 ≤ q₀ * (i₁ * k₂ - i₂ * k₁) :=
    mul_nonneg hq₀.le hCross₂
  have hTerm₁ : q₁ * (i₀ * k₂ - i₂ * k₀) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hq₁.le hCross₁
  have hTerm₂ : 0 < q₂ * (i₀ * k₁ - i₁ * k₀) :=
    mul_pos hq₂ hCross₀
  ring_nf
  linarith

private theorem ordered_crosses_of_moment_bounds
    (s i₀ i₁ i₂ k₀ k₁ k₂ : ℝ)
    (hi₀ : 0 < i₀) (hi₁ : 0 ≤ i₁)
    (hk₀ : 0 < k₀) (hk₁ : 0 ≤ k₁)
    (hiFirst : i₁ < s * i₀) (hkFirst : s * k₀ < k₁)
    (hiSecond : i₂ ≤ s * i₁) (hkSecond : s * k₁ ≤ k₂) :
    0 ≤ i₁ * k₂ - i₂ * k₁ ∧
      0 ≤ i₀ * k₂ - i₂ * k₀ ∧
        0 < i₀ * k₁ - i₁ * k₀ := by
  have hCross₂ : i₂ * k₁ ≤ i₁ * k₂ := by
    calc
      i₂ * k₁ ≤ (s * i₁) * k₁ :=
        mul_le_mul_of_nonneg_right hiSecond hk₁
      _ = i₁ * (s * k₁) := by ring
      _ ≤ i₁ * k₂ := mul_le_mul_of_nonneg_left hkSecond hi₁
  have hCross₀ : i₁ * k₀ < i₀ * k₁ := by
    calc
      i₁ * k₀ < (s * i₀) * k₀ := mul_lt_mul_of_pos_right hiFirst hk₀
      _ = i₀ * (s * k₀) := by ring
      _ < i₀ * k₁ := mul_lt_mul_of_pos_left hkFirst hi₀
  have hsI₀Pos : 0 < s * i₀ := hi₁.trans_lt hiFirst
  have hsPos : 0 < s := by
    rcases (mul_pos_iff.mp hsI₀Pos) with hBothPos | hBothNeg
    · exact hBothPos.1
    · exact (lt_asymm hi₀ hBothNeg.2).elim
  have hsK₀Pos : 0 < s * k₀ := mul_pos hsPos hk₀
  have hCross₁Strict : i₂ * k₀ < i₀ * k₂ := by
    calc
      i₂ * k₀ ≤ (s * i₁) * k₀ :=
        mul_le_mul_of_nonneg_right hiSecond hk₀.le
      _ = i₁ * (s * k₀) := by ring
      _ < (s * i₀) * (s * k₀) :=
        mul_lt_mul_of_pos_right hiFirst hsK₀Pos
      _ = i₀ * (s * (s * k₀)) := by ring
      _ < i₀ * (s * k₁) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hkFirst hsPos) hi₀
      _ ≤ i₀ * k₂ := mul_le_mul_of_nonneg_left hkSecond hi₀.le
  exact ⟨sub_nonneg.mpr hCross₂, sub_nonneg.mpr hCross₁Strict.le,
    sub_pos.mpr hCross₀⟩

/-- A continuous nonnegative density with positive mass on both sides of `3`
has the ordered moments used by the determinant argument.  This is the
abstract analytic part of the square-shift construction; it does not assert
integrality or introduce any Padé polynomial. -/
theorem orderedSupportMomentBounds
    (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Icc 2 4))
    (hnonneg : ∀ x ∈ Set.Icc (2 : ℝ) 4, 0 ≤ f x)
    (hpos23 : ∃ x ∈ Set.Ioo (2 : ℝ) 3, 0 < f x)
    (hpos34 : ∃ x ∈ Set.Ioo (3 : ℝ) 4, 0 < f x) :
    let i₀ := ∫ x in 2..3, f x
    let i₁ := ∫ x in 2..3, x * f x
    let i₂ := ∫ x in 2..3, x ^ 2 * f x
    let k₀ := ∫ x in 3..4, f x
    let k₁ := ∫ x in 3..4, x * f x
    let k₂ := ∫ x in 3..4, x ^ 2 * f x
    0 < i₀ ∧ 0 ≤ i₁ ∧
      0 < k₀ ∧ 0 ≤ k₁ ∧
      i₁ < 3 * i₀ ∧ 3 * k₀ < k₁ ∧
      i₂ ≤ 3 * i₁ ∧ 3 * k₁ ≤ k₂ := by
  dsimp only
  have h23Subset : Set.Icc (2 : ℝ) 3 ⊆ Set.Icc 2 4 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have h34Subset : Set.Icc (3 : ℝ) 4 ⊆ Set.Icc 2 4 := by
    intro x hx
    exact ⟨(by linarith [hx.1]), hx.2⟩
  have hf23 : ContinuousOn f (Set.Icc (2 : ℝ) 3) :=
    hcont.mono h23Subset
  have hf34 : ContinuousOn f (Set.Icc (3 : ℝ) 4) :=
    hcont.mono h34Subset
  have hnonneg23 : ∀ x ∈ Set.Icc (2 : ℝ) 3, 0 ≤ f x :=
    fun x hx ↦ hnonneg x (h23Subset hx)
  have hnonneg34 : ∀ x ∈ Set.Icc (3 : ℝ) 4, 0 ≤ f x :=
    fun x hx ↦ hnonneg x (h34Subset hx)
  have hi₀ : 0 < ∫ x in (2 : ℝ)..3, f x := by
    apply intervalIntegral.integral_pos (by norm_num) hf23
    · intro x hx
      exact hnonneg23 x ⟨hx.1.le, hx.2⟩
    · obtain ⟨x, hx, hfx⟩ := hpos23
      exact ⟨x, ⟨hx.1.le, hx.2.le⟩, hfx⟩
  have hi₁ : 0 ≤ ∫ x in (2 : ℝ)..3, x * f x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg (by linarith [hx.1]) (hnonneg23 x hx)
  have hk₀ : 0 < ∫ x in (3 : ℝ)..4, f x := by
    apply intervalIntegral.integral_pos (by norm_num) hf34
    · intro x hx
      exact hnonneg34 x ⟨hx.1.le, hx.2⟩
    · obtain ⟨x, hx, hfx⟩ := hpos34
      exact ⟨x, ⟨hx.1.le, hx.2.le⟩, hfx⟩
  have hk₁ : 0 ≤ ∫ x in (3 : ℝ)..4, x * f x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg (by linarith [hx.1]) (hnonneg34 x hx)
  have hiFirst :
      (∫ x in (2 : ℝ)..3, x * f x) < 3 * ∫ x in (2 : ℝ)..3, f x := by
    have hStrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun x : ℝ ↦ x * f x) (g := fun x : ℝ ↦ 3 * f x)
      (by norm_num) (continuousOn_id.mul hf23) (continuousOn_const.mul hf23)
      (by
        intro x hx
        exact mul_le_mul_of_nonneg_right hx.2 (hnonneg23 x ⟨hx.1.le, hx.2⟩))
      (by
        obtain ⟨x, hx, hfx⟩ := hpos23
        exact ⟨x, ⟨hx.1.le, hx.2.le⟩,
          mul_lt_mul_of_pos_right hx.2 hfx⟩)
    simpa only [intervalIntegral.integral_const_mul] using hStrict
  have hkFirst :
      3 * (∫ x in (3 : ℝ)..4, f x) < ∫ x in (3 : ℝ)..4, x * f x := by
    have hStrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun x : ℝ ↦ 3 * f x) (g := fun x : ℝ ↦ x * f x)
      (by norm_num) (continuousOn_const.mul hf34) (continuousOn_id.mul hf34)
      (by
        intro x hx
        exact mul_le_mul_of_nonneg_right hx.1.le (hnonneg34 x ⟨hx.1.le, hx.2⟩))
      (by
        obtain ⟨x, hx, hfx⟩ := hpos34
        exact ⟨x, ⟨hx.1.le, hx.2.le⟩,
          mul_lt_mul_of_pos_right hx.1 hfx⟩)
    simpa only [intervalIntegral.integral_const_mul] using hStrict
  have hiSecond :
      (∫ x in (2 : ℝ)..3, x ^ 2 * f x) ≤
        3 * ∫ x in (2 : ℝ)..3, x * f x := by
    have hStrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun x : ℝ ↦ x ^ 2 * f x) (g := fun x : ℝ ↦ 3 * (x * f x))
      (by norm_num)
      ((continuousOn_id.pow 2).mul hf23)
      (continuousOn_const.mul (continuousOn_id.mul hf23))
      (by
        intro x hx
        calc
          x ^ 2 * f x ≤ (3 * x) * f x :=
            mul_le_mul_of_nonneg_right (by nlinarith [hx.1, hx.2])
              (hnonneg23 x ⟨hx.1.le, hx.2⟩)
          _ = 3 * (x * f x) := by ring)
      (by
        obtain ⟨x, hx, hfx⟩ := hpos23
        exact ⟨x, ⟨hx.1.le, hx.2.le⟩, by
          calc
            x ^ 2 * f x < (3 * x) * f x :=
              mul_lt_mul_of_pos_right (by nlinarith [hx.1, hx.2]) hfx
            _ = 3 * (x * f x) := by ring⟩)
    exact (by simpa using hStrict.le)
  have hkSecond :
      3 * (∫ x in (3 : ℝ)..4, x * f x) ≤
        ∫ x in (3 : ℝ)..4, x ^ 2 * f x := by
    have hStrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun x : ℝ ↦ 3 * (x * f x)) (g := fun x : ℝ ↦ x ^ 2 * f x)
      (by norm_num)
      (continuousOn_const.mul (continuousOn_id.mul hf34))
      ((continuousOn_id.pow 2).mul hf34)
      (by
        intro x hx
        calc
          3 * (x * f x) = (3 * x) * f x := by ring
          _ ≤ x ^ 2 * f x :=
            mul_le_mul_of_nonneg_right (by nlinarith [hx.1, hx.2])
              (hnonneg34 x ⟨hx.1.le, hx.2⟩))
      (by
        obtain ⟨x, hx, hfx⟩ := hpos34
        exact ⟨x, ⟨hx.1.le, hx.2.le⟩, by
          calc
            3 * (x * f x) = (3 * x) * f x := by ring
            _ < x ^ 2 * f x :=
              mul_lt_mul_of_pos_right (by nlinarith [hx.1, hx.2]) hfx⟩)
    exact (by simpa using hStrict.le)
  exact ⟨hi₀, hi₁, hk₀, hk₁, hiFirst, hkFirst, hiSecond, hkSecond⟩

/-- Ordered residual moments on the two sides of Rhin's common boundary `3`
force the integral row determinant to be nonzero.  The residual identities
fix the exact logarithmic basis and the sign of the `[3,4]` moment column. -/
theorem simultaneousLogApproximationDet_ne_zero_of_ordered_support
    (rows : Fin 3 → SimultaneousLogApproximationRow)
    (i k : Fin 3 → ℝ)
    (hI : ∀ j,
      ((rows j).numerator23 : ℝ) -
          ((rows j).denominator : ℝ) * logTwoDivThree = i j)
    (hK : ∀ j,
      ((rows j).numerator34 : ℝ) -
          ((rows j).denominator : ℝ) * logFourDivThree = -(k j))
    (hq₀ : 0 < ((rows 0).denominator : ℝ))
    (hq₁ : ((rows 1).denominator : ℝ) < 0)
    (hq₂ : 0 < ((rows 2).denominator : ℝ))
    (hi₀ : 0 < i 0) (hi₁ : 0 ≤ i 1)
    (hk₀ : 0 < k 0) (hk₁ : 0 ≤ k 1)
    (hiFirst : i 1 < 3 * i 0)
    (hkFirst : 3 * k 0 < k 1)
    (hiSecond : i 2 ≤ 3 * i 1)
    (hkSecond : 3 * k 1 ≤ k 2) :
    simultaneousLogApproximationDet (rows 0) (rows 1) (rows 2) ≠ 0 := by
  rcases ordered_crosses_of_moment_bounds
      3 (i 0) (i 1) (i 2) (k 0) (k 1) (k 2)
      hi₀ hi₁ hk₀ hk₁ hiFirst hkFirst hiSecond hkSecond with
    ⟨hCross₂, hCross₁, hCross₀⟩
  have hCastDet :
      (simultaneousLogApproximationDet (rows 0) (rows 1) (rows 2) : ℝ) =
        orderedMomentDet
          ((rows 0).denominator : ℝ)
          ((rows 1).denominator : ℝ)
          ((rows 2).denominator : ℝ)
          (i 0) (i 1) (i 2) (k 0) (k 1) (k 2) := by
    unfold simultaneousLogApproximationDet orderedMomentDet
    push_cast
    rw [← hI 0, ← hI 1, ← hI 2, ← hK 0, ← hK 1, ← hK 2]
    ring
  have hNeg :
      orderedMomentDet
          ((rows 0).denominator : ℝ)
          ((rows 1).denominator : ℝ)
          ((rows 2).denominator : ℝ)
          (i 0) (i 1) (i 2) (k 0) (k 1) (k 2) < 0 :=
    orderedMomentDet_neg
      ((rows 0).denominator : ℝ)
      ((rows 1).denominator : ℝ)
      ((rows 2).denominator : ℝ)
      (i 0) (i 1) (i 2) (k 0) (k 1) (k 2)
      hq₀ hq₁ hq₂ hCross₂ hCross₁ hCross₀
  intro hZero
  have hCastZero :
      (simultaneousLogApproximationDet (rows 0) (rows 1) (rows 2) : ℝ) = 0 := by
    rw [hZero]
    norm_num
  rw [hCastDet] at hCastZero
  linarith

/-- The raw `[2,3]` moment of the literal square density at shift `j`. -/
def literalRhinSquareMoment23 (n : ℕ) (j : Fin 3) : ℝ :=
  ∫ x in (2 : ℝ)..3, x ^ (j : ℕ) * literalRhinSquareDensity n x

/-- The raw `[3,4]` moment of the literal square density at shift `j`. -/
def literalRhinSquareMoment34 (n : ℕ) (j : Fin 3) : ℝ :=
  ∫ x in (3 : ℝ)..4, x ^ (j : ℕ) * literalRhinSquareDensity n x

/-- The raw `[2,3]` moment inherits the exact continuous remainder bound. -/
theorem literalRhinSquareMoment23_abs_le (n : ℕ) (j : Fin 3) :
    |literalRhinSquareMoment23 n j| ≤
      144 * (((12 : ℝ) ^ 7 * 20) ^ 2) *
        ((239 : ℝ) / 1000) ^ (2 * n) := by
  have hj : (j : ℕ) ≤ 2 := by omega
  have hBound := literalRhinSquareIntegrand_integral23_abs_le n (j : ℕ) hj
  have hIntegral :
      (∫ x in (2 : ℝ)..3,
          x ^ (j : ℕ) * literalRhinSquareDensity n x) =
        ∫ x in (2 : ℝ)..3, literalRhinSquareIntegrand n (j : ℕ) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact (literalRhinSquareIntegrand_eq_moment n j x).symm
  simpa only [literalRhinSquareMoment23, hIntegral] using hBound

/-- The raw `[3,4]` moment inherits the exact continuous remainder bound. -/
theorem literalRhinSquareMoment34_abs_le (n : ℕ) (j : Fin 3) :
    |literalRhinSquareMoment34 n j| ≤
      144 * (((12 : ℝ) ^ 7 * 20) ^ 2) *
        ((239 : ℝ) / 1000) ^ (2 * n) := by
  have hj : (j : ℕ) ≤ 2 := by omega
  have hBound := literalRhinSquareIntegrand_integral34_abs_le n (j : ℕ) hj
  have hIntegral :
      (∫ x in (3 : ℝ)..4,
          x ^ (j : ℕ) * literalRhinSquareDensity n x) =
        ∫ x in (3 : ℝ)..4, literalRhinSquareIntegrand n (j : ℕ) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact (literalRhinSquareIntegrand_eq_moment n j x).symm
  simpa only [literalRhinSquareMoment34, hIntegral] using hBound

/-- The common literal density satisfies all eight ordered-moment conditions
needed by the determinant argument. -/
theorem literalRhinSquareMoments_ordered (n : ℕ) :
    0 < literalRhinSquareMoment23 n 0 ∧
      0 ≤ literalRhinSquareMoment23 n 1 ∧
      0 < literalRhinSquareMoment34 n 0 ∧
      0 ≤ literalRhinSquareMoment34 n 1 ∧
      literalRhinSquareMoment23 n 1 <
        3 * literalRhinSquareMoment23 n 0 ∧
      3 * literalRhinSquareMoment34 n 0 <
        literalRhinSquareMoment34 n 1 ∧
      literalRhinSquareMoment23 n 2 ≤
        3 * literalRhinSquareMoment23 n 1 ∧
      3 * literalRhinSquareMoment34 n 1 ≤
        literalRhinSquareMoment34 n 2 := by
  have hBounds := orderedSupportMomentBounds
    (literalRhinSquareDensity n)
    (literalRhinSquareDensity_continuousOn n)
    (literalRhinSquareDensity_nonneg n)
    ⟨5 / 2, by norm_num, literalRhinSquareDensity_pos_five_halves n⟩
    ⟨7 / 2, by norm_num, literalRhinSquareDensity_pos_seven_halves n⟩
  simpa only [literalRhinSquareMoment23, literalRhinSquareMoment34,
    Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_mul] using
    hBounds

/-- The scaled `[2,3]` moment that occurs literally in the integer-row
residual. -/
def literalRhinSquareScaledMoment23 (n : ℕ) (j : Fin 3) : ℝ :=
  (rangeLCM (literalRhinSquareScale n) : ℝ) *
    literalRhinSquareMoment23 n j

/-- The scaled `[3,4]` moment that occurs literally in the integer-row
residual. -/
def literalRhinSquareScaledMoment34 (n : ℕ) (j : Fin 3) : ℝ :=
  (rangeLCM (literalRhinSquareScale n) : ℝ) *
    literalRhinSquareMoment34 n j

/-- Positive common LCM scaling preserves the complete ordered-moment
package. -/
theorem literalRhinSquareScaledMoments_ordered (n : ℕ) :
    0 < literalRhinSquareScaledMoment23 n 0 ∧
      0 ≤ literalRhinSquareScaledMoment23 n 1 ∧
      0 < literalRhinSquareScaledMoment34 n 0 ∧
      0 ≤ literalRhinSquareScaledMoment34 n 1 ∧
      literalRhinSquareScaledMoment23 n 1 <
        3 * literalRhinSquareScaledMoment23 n 0 ∧
      3 * literalRhinSquareScaledMoment34 n 0 <
        literalRhinSquareScaledMoment34 n 1 ∧
      literalRhinSquareScaledMoment23 n 2 ≤
        3 * literalRhinSquareScaledMoment23 n 1 ∧
      3 * literalRhinSquareScaledMoment34 n 1 ≤
        literalRhinSquareScaledMoment34 n 2 := by
  let L : ℝ := rangeLCM (literalRhinSquareScale n)
  have hL : 0 < L := by
    change 0 < (rangeLCM (literalRhinSquareScale n) : ℝ)
    exact_mod_cast rangeLCM_pos (literalRhinSquareScale n)
  rcases literalRhinSquareMoments_ordered n with
    ⟨hi₀, hi₁, hk₀, hk₁, hiFirst, hkFirst, hiSecond, hkSecond⟩
  unfold literalRhinSquareScaledMoment23 literalRhinSquareScaledMoment34
  change
    0 < L * literalRhinSquareMoment23 n 0 ∧
      0 ≤ L * literalRhinSquareMoment23 n 1 ∧
      0 < L * literalRhinSquareMoment34 n 0 ∧
      0 ≤ L * literalRhinSquareMoment34 n 1 ∧
      L * literalRhinSquareMoment23 n 1 <
        3 * (L * literalRhinSquareMoment23 n 0) ∧
      3 * (L * literalRhinSquareMoment34 n 0) <
        L * literalRhinSquareMoment34 n 1 ∧
      L * literalRhinSquareMoment23 n 2 ≤
        3 * (L * literalRhinSquareMoment23 n 1) ∧
      3 * (L * literalRhinSquareMoment34 n 1) ≤
        L * literalRhinSquareMoment34 n 2
  refine ⟨mul_pos hL hi₀, mul_nonneg hL.le hi₁,
    mul_pos hL hk₀, mul_nonneg hL.le hk₁, ?_, ?_, ?_, ?_⟩
  · calc
      L * literalRhinSquareMoment23 n 1 <
          L * (3 * literalRhinSquareMoment23 n 0) :=
        mul_lt_mul_of_pos_left hiFirst hL
      _ = 3 * (L * literalRhinSquareMoment23 n 0) := by ring
  · calc
      3 * (L * literalRhinSquareMoment34 n 0) =
          L * (3 * literalRhinSquareMoment34 n 0) := by ring
      _ < L * literalRhinSquareMoment34 n 1 :=
        mul_lt_mul_of_pos_left hkFirst hL
  · calc
      L * literalRhinSquareMoment23 n 2 ≤
          L * (3 * literalRhinSquareMoment23 n 1) :=
        mul_le_mul_of_nonneg_left hiSecond hL.le
      _ = 3 * (L * literalRhinSquareMoment23 n 1) := by ring
  · calc
      3 * (L * literalRhinSquareMoment34 n 1) =
          L * (3 * literalRhinSquareMoment34 n 1) := by ring
      _ ≤ L * literalRhinSquareMoment34 n 2 :=
        mul_le_mul_of_nonneg_left hkSecond hL.le

/-- The two exact row residuals are the scaled moments of the common literal
square density. -/
theorem literalRhinSquareRows_residuals_as_scaledMoments
    (n : ℕ) (j : Fin 3) :
    (((literalRhinSquareRows n j).numerator23 : ℝ) -
        ((literalRhinSquareRows n j).denominator : ℝ) * logTwoDivThree =
      literalRhinSquareScaledMoment23 n j) ∧
    (((literalRhinSquareRows n j).numerator34 : ℝ) -
        ((literalRhinSquareRows n j).denominator : ℝ) * logFourDivThree =
      -(literalRhinSquareScaledMoment34 n j)) := by
  rcases literalRhinSquareRows_residuals n j with ⟨h23, h34⟩
  constructor
  · calc
      _ = (rangeLCM (literalRhinSquareScale n) : ℝ) *
          (∫ x in (2 : ℝ)..3,
            (literalRhinSquareShiftPolynomial n j).eval₂
                (Int.castRingHom ℝ) x /
              x ^ (literalRhinSquareScale n + 1)) := h23
      _ = literalRhinSquareScaledMoment23 n j := by
        rw [intervalIntegral_literalRhinSquareShift_eq_moment]
        rfl
  · calc
      _ = -((rangeLCM (literalRhinSquareScale n) : ℝ) *
          (∫ x in (3 : ℝ)..4,
            (literalRhinSquareShiftPolynomial n j).eval₂
                (Int.castRingHom ℝ) x /
              x ^ (literalRhinSquareScale n + 1))) := h34
      _ = -(literalRhinSquareScaledMoment34 n j) := by
        rw [intervalIntegral_literalRhinSquareShift_eq_moment]
        rfl

/-- For every `n ≥ 8`, the three literal square rows have a nonzero exact
integer determinant.  No coefficient table or root-count argument is used. -/
theorem literalRhinSquareRows_det_ne_zero (n : ℕ) (hn : 8 ≤ n) :
    simultaneousLogApproximationDet
      (literalRhinSquareRows n 0)
      (literalRhinSquareRows n 1)
      (literalRhinSquareRows n 2) ≠ 0 := by
  rcases literalRhinSquareRows_denominator_signs n hn with
    ⟨hq₀, hq₁, hq₂⟩
  rcases literalRhinSquareScaledMoments_ordered n with
    ⟨hi₀, hi₁, hk₀, hk₁, hiFirst, hkFirst, hiSecond, hkSecond⟩
  exact simultaneousLogApproximationDet_ne_zero_of_ordered_support
    (literalRhinSquareRows n)
    (literalRhinSquareScaledMoment23 n)
    (literalRhinSquareScaledMoment34 n)
    (fun j ↦ (literalRhinSquareRows_residuals_as_scaledMoments n j).1)
    (fun j ↦ (literalRhinSquareRows_residuals_as_scaledMoments n j).2)
    hq₀ hq₁ hq₂ hi₀ hi₁ hk₀ hk₁ hiFirst hkFirst hiSecond hkSecond

/-- A nonzero determinant for an arbitrary `Fin 3` row family supplies the
selection field of the scale-aligned certificate. -/
theorem rows_separate_of_det_ne_zero
    (rows : Fin 3 → SimultaneousLogApproximationRow)
    (hDet :
      simultaneousLogApproximationDet (rows 0) (rows 1) (rows 2) ≠ 0) :
    ∀ a b c : ℤ, a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 →
      ∃ j : Fin 3, (rows j).pair a b c ≠ 0 := by
  intro a b c hCoefficients
  have hRows := exists_row_pair_ne_zero_of_det_ne_zero
    (rows 0) (rows 1) (rows 2) hDet a b c hCoefficients
  rcases hRows with hRow₀ | hRow₁ | hRow₂
  · exact ⟨0, hRow₀⟩
  · exact ⟨1, hRow₁⟩
  · exact ⟨2, hRow₂⟩

/-- Package three integer sequences as approximation rows. -/
def simultaneousLogApproximationRow
    (denominator numerator23 numerator34 : ℕ → ℤ) (n : ℕ) :
    SimultaneousLogApproximationRow where
  denominator := denominator n
  numerator23 := numerator23 n
  numerator34 := numerator34 n

/-- The determinant of the consecutive rows `n`, `n+1`, and `n+2`. -/
def consecutiveSimultaneousLogApproximationDet
    (denominator numerator23 numerator34 : ℕ → ℤ) (n : ℕ) : ℤ :=
  simultaneousLogApproximationDet
    (simultaneousLogApproximationRow denominator numerator23 numerator34 n)
    (simultaneousLogApproximationRow denominator numerator23 numerator34 (n + 1))
    (simultaneousLogApproximationRow denominator numerator23 numerator34 (n + 2))

/-- A nonzero consecutive determinant has exactly the separation shape needed
by a scale-aligned certificate window. -/
theorem consecutive_rows_separate_of_det_ne_zero
    (denominator numerator23 numerator34 : ℕ → ℤ) (n : ℕ)
    (hDet :
      consecutiveSimultaneousLogApproximationDet
        denominator numerator23 numerator34 n ≠ 0) :
    ∀ a b c : ℤ, a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 →
      ∃ j : Fin 3,
        denominator (n + (j : ℕ)) * a +
            numerator23 (n + (j : ℕ)) * b +
            numerator34 (n + (j : ℕ)) * c ≠ 0 := by
  intro a b c hCoefficients
  have hRows := exists_row_pair_ne_zero_of_det_ne_zero
    (simultaneousLogApproximationRow denominator numerator23 numerator34 n)
    (simultaneousLogApproximationRow denominator numerator23 numerator34 (n + 1))
    (simultaneousLogApproximationRow denominator numerator23 numerator34 (n + 2))
    hDet a b c hCoefficients
  rcases hRows with hRow₀ | hRow₁ | hRow₂
  · refine ⟨⟨0, by omega⟩, ?_⟩
    simpa only [SimultaneousLogApproximationRow.pair,
      simultaneousLogApproximationRow, Nat.add_zero] using hRow₀
  · refine ⟨⟨1, by omega⟩, ?_⟩
    simpa only [SimultaneousLogApproximationRow.pair,
      simultaneousLogApproximationRow] using hRow₁
  · refine ⟨⟨2, by omega⟩, ?_⟩
    simpa only [SimultaneousLogApproximationRow.pair,
      simultaneousLogApproximationRow] using hRow₂

/-- A scale-aligned simultaneous-approximation certificate.

For each natural height above `threshold`, `window` supplies three integral
rows, indexed by `Fin 3`.  No relation between their raw Padé indices is
assumed here.  The final field is the exact nonzero-row selection property
normally obtained from a nonzero `3 × 3` determinant. -/
structure SimultaneousLogApproximationCertificate where
  factor : ℝ
  threshold : ℕ
  factor_pos : 0 < factor
  two_le_threshold : 2 ≤ threshold
  window : ∀ H : ℕ, threshold ≤ H →
    ∃ rows : Fin 3 → SimultaneousLogApproximationRow,
      (∀ j : Fin 3,
        |((rows j).denominator : ℝ)| ≤
          factor * Real.rpow (H : ℝ) (133 / 10 : ℝ)) ∧
      (∀ j : Fin 3,
        3 * (H : ℝ) *
              |((rows j).denominator : ℝ) * logTwoDivThree -
                ((rows j).numerator23 : ℝ)| +
            2 * (H : ℝ) *
              |((rows j).denominator : ℝ) * logFourDivThree -
                ((rows j).numerator34 : ℝ)| ≤
          1 / 2) ∧
      ∀ a b c : ℤ, a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 →
        ∃ j : Fin 3,
          (rows j).pair a b c ≠ 0

/-- Eventual geometric bounds for one raw Padé row sequence, together with an
explicit full-rank selection in a uniformly bounded index window.

The integer `exponent` and `growth_decay` field are a log-free certificate for
the desired rate.  The concrete Rhin producer may use `growth = 72`,
`decay = 27/40`, and `exponent = 11`. -/
structure GeometricSimultaneousLogApproximationCertificate where
  row : ℕ → SimultaneousLogApproximationRow
  growth : ℝ
  decay : ℝ
  denominatorFactor : ℝ
  errorFactor : ℝ
  start : ℕ
  windowWidth : ℕ
  exponent : ℕ
  one_le_growth : 1 ≤ growth
  decay_pos : 0 < decay
  decay_lt_one : decay < 1
  denominatorFactor_pos : 0 < denominatorFactor
  errorFactor_pos : 0 < errorFactor
  exponent_le : (exponent : ℝ) ≤ 133 / 10
  growth_decay : growth * decay ^ exponent ≤ 1
  denominator_le : ∀ n : ℕ, start ≤ n →
    |((row n).denominator : ℝ)| ≤ denominatorFactor * growth ^ n
  error_le : ∀ n : ℕ, start ≤ n →
    3 *
          |((row n).denominator : ℝ) * logTwoDivThree -
            ((row n).numerator23 : ℝ)| +
        2 *
          |((row n).denominator : ℝ) * logFourDivThree -
            ((row n).numerator34 : ℝ)| ≤
      errorFactor * decay ^ n
  bounded_window_det : ∀ n : ℕ, start ≤ n →
    ∃ indices : Fin 3 → ℕ,
      (∀ j : Fin 3, n ≤ indices j ∧ indices j ≤ n + windowWidth) ∧
      simultaneousLogApproximationDet
        (row (indices 0)) (row (indices 1)) (row (indices 2)) ≠ 0

/-- Three simultaneous-approximation rows produced at one common geometric
scale.  The `Fin 3` index labels square shifts, not successive Padé scales. -/
structure GroupedGeometricSimultaneousLogApproximationCertificate where
  rows : ℕ → Fin 3 → SimultaneousLogApproximationRow
  growth : ℝ
  decay : ℝ
  denominatorFactor : ℝ
  errorFactor : ℝ
  start : ℕ
  exponent : ℕ
  one_le_growth : 1 ≤ growth
  decay_pos : 0 < decay
  decay_lt_one : decay < 1
  denominatorFactor_pos : 0 < denominatorFactor
  errorFactor_pos : 0 < errorFactor
  exponent_le : (exponent : ℝ) ≤ 133 / 10
  growth_decay : growth * decay ^ exponent ≤ 1
  denominator_le : ∀ n : ℕ, start ≤ n → ∀ j : Fin 3,
    |((rows n j).denominator : ℝ)| ≤ denominatorFactor * growth ^ n
  error_le : ∀ n : ℕ, start ≤ n → ∀ j : Fin 3,
    3 *
          |((rows n j).denominator : ℝ) * logTwoDivThree -
            ((rows n j).numerator23 : ℝ)| +
        2 *
          |((rows n j).denominator : ℝ) * logFourDivThree -
            ((rows n j).numerator34 : ℝ)| ≤
      errorFactor * decay ^ n
  determinant_ne : ∀ n : ℕ, start ≤ n →
    simultaneousLogApproximationDet
      (rows n 0) (rows n 1) (rows n 2) ≠ 0

/-- Transfer the raw denominator estimate to the upper endpoint of a bounded
index window. -/
theorem GeometricSimultaneousLogApproximationCertificate.denominator_le_at_window
    (h : GeometricSimultaneousLogApproximationCertificate)
    {n m : ℕ} (hStart : h.start ≤ n) (hLower : n ≤ m)
    (hUpper : m ≤ n + h.windowWidth) :
    |((h.row m).denominator : ℝ)| ≤
      h.denominatorFactor * h.growth ^ (n + h.windowWidth) := by
  exact (h.denominator_le m (hStart.trans hLower)).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ h.one_le_growth hUpper)
      h.denominatorFactor_pos.le)

/-- Transfer the raw weighted residual estimate to the lower endpoint of a
bounded index window. -/
theorem GeometricSimultaneousLogApproximationCertificate.error_le_at_window
    (h : GeometricSimultaneousLogApproximationCertificate)
    {n m : ℕ} (hStart : h.start ≤ n) (hLower : n ≤ m) :
    3 *
          |((h.row m).denominator : ℝ) * logTwoDivThree -
            ((h.row m).numerator23 : ℝ)| +
        2 *
          |((h.row m).denominator : ℝ) * logFourDivThree -
            ((h.row m).numerator34 : ℝ)| ≤
      h.errorFactor * h.decay ^ n := by
  exact (h.error_le m (hStart.trans hLower)).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one h.decay_pos.le h.decay_lt_one.le hLower)
      h.errorFactor_pos.le)

/-- A single factor that absorbs the initial-index case and the
strict-predecessor geometric-growth case. -/
def GeometricSimultaneousLogApproximationCertificate.scaleFactor
    (h : GeometricSimultaneousLogApproximationCertificate) : ℝ :=
  max
    (h.denominatorFactor * h.growth ^ (h.start + h.windowWidth))
    (h.denominatorFactor * h.growth ^ (h.windowWidth + 1) *
      (2 * h.errorFactor) ^ h.exponent)

theorem GeometricSimultaneousLogApproximationCertificate.scaleFactor_pos
    (h : GeometricSimultaneousLogApproximationCertificate) :
    0 < h.scaleFactor := by
  exact (mul_pos h.denominatorFactor_pos
    (pow_pos (lt_of_lt_of_le zero_lt_one h.one_le_growth) _)).trans_le
      (le_max_left _ _)

/-- The least-scale predecessor alternative bounds every denominator in the
selected raw-index window by the scale-aligned factor. -/
theorem GeometricSimultaneousLogApproximationCertificate.denominator_le_at_scale
    (h : GeometricSimultaneousLogApproximationCertificate)
    (H : ℕ) (hH : 2 ≤ H) {k m : ℕ}
    (hPrevious :
      k = 0 ∨
        1 / (2 * (H : ℝ)) <
          h.errorFactor * h.decay ^ (h.start + (k - 1)))
    (hLower : h.start + k ≤ m)
    (hUpper : m ≤ h.start + k + h.windowWidth) :
    |((h.row m).denominator : ℝ)| ≤
      h.scaleFactor * Real.rpow (H : ℝ) (133 / 10 : ℝ) := by
  have hGrowthPos : 0 < h.growth :=
    lt_of_lt_of_le zero_lt_one h.one_le_growth
  have hHOne : (1 : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast (show 1 ≤ H by omega)
  have hHPos : 0 < (H : ℝ) := zero_lt_one.trans_le hHOne
  have hRpowOne :
      1 ≤ Real.rpow (H : ℝ) (133 / 10 : ℝ) :=
    Real.one_le_rpow hHOne (by norm_num)
  rcases hPrevious with rfl | hPrevious
  · have hWindow := h.denominator_le_at_window
      (n := h.start) (m := m) (by rfl) (by simpa using hLower) (by simpa using hUpper)
    calc
      |((h.row m).denominator : ℝ)| ≤
          h.denominatorFactor * h.growth ^ (h.start + h.windowWidth) :=
        hWindow
      _ ≤ h.scaleFactor := le_max_left _ _
      _ = h.scaleFactor * 1 := (mul_one _).symm
      _ ≤ h.scaleFactor * Real.rpow (H : ℝ) (133 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hRpowOne h.scaleFactor_pos.le
  · let p : ℕ := h.start + (k - 1)
    have hTPos : 0 < (1 / (2 * (H : ℝ)) : ℝ) := by positivity
    have hGrowthP :
        h.growth ^ p ≤
          (h.errorFactor / (1 / (2 * (H : ℝ)))) ^ h.exponent :=
      geometric_growth_le_of_decay_lower
        h.errorFactor_pos hTPos hGrowthPos h.decay_pos hPrevious h.growth_decay
    have hStartM : h.start ≤ m := by omega
    have hIndexUpper : m ≤ p + (h.windowWidth + 1) := by
      dsimp only [p]
      omega
    have hPowerM :
        h.growth ^ m ≤ h.growth ^ (p + (h.windowWidth + 1)) :=
      pow_le_pow_right₀ h.one_le_growth hIndexUpper
    have hRatio :
        h.errorFactor / (1 / (2 * (H : ℝ))) =
          (2 * h.errorFactor) * (H : ℝ) := by
      field_simp
    have hExponentPower :
        (H : ℝ) ^ h.exponent ≤ Real.rpow (H : ℝ) (133 / 10 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hHOne h.exponent_le
    calc
      |((h.row m).denominator : ℝ)| ≤
          h.denominatorFactor * h.growth ^ m :=
        h.denominator_le m hStartM
      _ ≤ h.denominatorFactor * h.growth ^ (p + (h.windowWidth + 1)) :=
        mul_le_mul_of_nonneg_left hPowerM h.denominatorFactor_pos.le
      _ = (h.denominatorFactor * h.growth ^ (h.windowWidth + 1)) *
          h.growth ^ p := by
        rw [pow_add]
        ring
      _ ≤ (h.denominatorFactor * h.growth ^ (h.windowWidth + 1)) *
          (h.errorFactor / (1 / (2 * (H : ℝ)))) ^ h.exponent :=
        mul_le_mul_of_nonneg_left hGrowthP
          (mul_nonneg h.denominatorFactor_pos.le (pow_nonneg hGrowthPos.le _))
      _ = (h.denominatorFactor * h.growth ^ (h.windowWidth + 1) *
          (2 * h.errorFactor) ^ h.exponent) * (H : ℝ) ^ h.exponent := by
        rw [hRatio, mul_pow]
        ring
      _ ≤ h.scaleFactor * (H : ℝ) ^ h.exponent :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hHPos.le _)
      _ ≤ h.scaleFactor * Real.rpow (H : ℝ) (133 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hExponentPower h.scaleFactor_pos.le

/-- Eventual geometric bounds plus a uniformly bounded full-rank raw-index
window produce the scale-aligned transference certificate. -/
def GeometricSimultaneousLogApproximationCertificate.toScaleAligned
    (h : GeometricSimultaneousLogApproximationCertificate) :
    SimultaneousLogApproximationCertificate := by
  refine
    { factor := h.scaleFactor
      threshold := 2
      factor_pos := h.scaleFactor_pos
      two_le_threshold := by rfl
      window := ?_ }
  intro H hH
  have hHPos : 0 < (H : ℝ) := by
    exact_mod_cast (show 0 < H by omega)
  have hTargetPos : 0 < (1 / (2 * (H : ℝ)) : ℝ) := by positivity
  obtain ⟨k, hScale, hPrevious⟩ :=
    exists_least_geometric_scale h.start h.errorFactor_pos h.decay_pos
      h.decay_lt_one hTargetPos
  let n : ℕ := h.start + k
  have hStart : h.start ≤ n := by
    dsimp only [n]
    omega
  obtain ⟨indices, hIndices, hDet⟩ := h.bounded_window_det n hStart
  let rows : Fin 3 → SimultaneousLogApproximationRow :=
    fun j => h.row (indices j)
  refine ⟨rows, ?_, ?_, ?_⟩
  · intro j
    exact h.denominator_le_at_scale H hH hPrevious
      (by simpa only [n] using (hIndices j).1)
      (by simpa only [n] using (hIndices j).2)
  · intro j
    have hRawError := h.error_le_at_window hStart (hIndices j).1
    calc
      3 * (H : ℝ) *
              |((rows j).denominator : ℝ) * logTwoDivThree -
                ((rows j).numerator23 : ℝ)| +
            2 * (H : ℝ) *
              |((rows j).denominator : ℝ) * logFourDivThree -
                ((rows j).numerator34 : ℝ)| =
          (H : ℝ) *
            (3 *
                |((h.row (indices j)).denominator : ℝ) * logTwoDivThree -
                  ((h.row (indices j)).numerator23 : ℝ)| +
              2 *
                |((h.row (indices j)).denominator : ℝ) * logFourDivThree -
                  ((h.row (indices j)).numerator34 : ℝ)|) := by
        dsimp only [rows]
        ring
      _ ≤ (H : ℝ) * (h.errorFactor * h.decay ^ n) :=
        mul_le_mul_of_nonneg_left hRawError hHPos.le
      _ ≤ (H : ℝ) * (1 / (2 * (H : ℝ))) :=
        mul_le_mul_of_nonneg_left (by simpa only [n] using hScale) hHPos.le
      _ = 1 / 2 := by field_simp
  · exact rows_separate_of_det_ne_zero rows (by simpa only [rows] using hDet)

/-- The grouped scale factor has only one extra growth step in the strict
predecessor case because all three rows share a common Padé scale. -/
def GroupedGeometricSimultaneousLogApproximationCertificate.scaleFactor
    (h : GroupedGeometricSimultaneousLogApproximationCertificate) : ℝ :=
  max
    (h.denominatorFactor * h.growth ^ h.start)
    (h.denominatorFactor * h.growth *
      (2 * h.errorFactor) ^ h.exponent)

theorem GroupedGeometricSimultaneousLogApproximationCertificate.scaleFactor_pos
    (h : GroupedGeometricSimultaneousLogApproximationCertificate) :
    0 < h.scaleFactor := by
  exact (mul_pos h.denominatorFactor_pos
    (pow_pos (lt_of_lt_of_le zero_lt_one h.one_le_growth) _)).trans_le
      (le_max_left _ _)

theorem GroupedGeometricSimultaneousLogApproximationCertificate.denominator_le_at_scale
    (h : GroupedGeometricSimultaneousLogApproximationCertificate)
    (H : ℕ) (hH : 2 ≤ H) {k : ℕ}
    (hPrevious :
      k = 0 ∨
        1 / (2 * (H : ℝ)) <
          h.errorFactor * h.decay ^ (h.start + (k - 1)))
    (j : Fin 3) :
    |((h.rows (h.start + k) j).denominator : ℝ)| ≤
      h.scaleFactor * Real.rpow (H : ℝ) (133 / 10 : ℝ) := by
  have hGrowthPos : 0 < h.growth :=
    lt_of_lt_of_le zero_lt_one h.one_le_growth
  have hHOne : (1 : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast (show 1 ≤ H by omega)
  have hHPos : 0 < (H : ℝ) := zero_lt_one.trans_le hHOne
  have hRpowOne :
      1 ≤ Real.rpow (H : ℝ) (133 / 10 : ℝ) :=
    Real.one_le_rpow hHOne (by norm_num)
  by_cases hkZero : k = 0
  · subst k
    calc
      |((h.rows (h.start + 0) j).denominator : ℝ)| ≤
          h.denominatorFactor * h.growth ^ h.start := by
        simpa only [Nat.add_zero] using h.denominator_le h.start (by rfl) j
      _ ≤ h.scaleFactor := le_max_left _ _
      _ = h.scaleFactor * 1 := (mul_one _).symm
      _ ≤ h.scaleFactor * Real.rpow (H : ℝ) (133 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hRpowOne h.scaleFactor_pos.le
  · have hPrevious := hPrevious.resolve_left hkZero
    let p : ℕ := h.start + (k - 1)
    have hTPos : 0 < (1 / (2 * (H : ℝ)) : ℝ) := by positivity
    have hGrowthP :
        h.growth ^ p ≤
          (h.errorFactor / (1 / (2 * (H : ℝ)))) ^ h.exponent :=
      geometric_growth_le_of_decay_lower
        h.errorFactor_pos hTPos hGrowthPos h.decay_pos hPrevious h.growth_decay
    have hRatio :
        h.errorFactor / (1 / (2 * (H : ℝ))) =
          (2 * h.errorFactor) * (H : ℝ) := by
      field_simp
    have hExponentPower :
        (H : ℝ) ^ h.exponent ≤ Real.rpow (H : ℝ) (133 / 10 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hHOne h.exponent_le
    calc
      |((h.rows (h.start + k) j).denominator : ℝ)| ≤
          h.denominatorFactor * h.growth ^ (h.start + k) :=
        h.denominator_le (h.start + k) (by omega) j
      _ = (h.denominatorFactor * h.growth) * h.growth ^ p := by
        rw [show h.start + k = p + 1 by dsimp only [p]; omega, pow_succ]
        ring
      _ ≤ (h.denominatorFactor * h.growth) *
          (h.errorFactor / (1 / (2 * (H : ℝ)))) ^ h.exponent :=
        mul_le_mul_of_nonneg_left hGrowthP
          (mul_nonneg h.denominatorFactor_pos.le hGrowthPos.le)
      _ = (h.denominatorFactor * h.growth *
          (2 * h.errorFactor) ^ h.exponent) * (H : ℝ) ^ h.exponent := by
        rw [hRatio, mul_pow]
        ring
      _ ≤ h.scaleFactor * (H : ℝ) ^ h.exponent :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hHPos.le _)
      _ ≤ h.scaleFactor * Real.rpow (H : ℝ) (133 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hExponentPower h.scaleFactor_pos.le

/-- A grouped three-row geometric producer converts directly to the
scale-aligned certificate without flattening its square-shift labels into
artificial Padé indices. -/
def GroupedGeometricSimultaneousLogApproximationCertificate.toScaleAligned
    (h : GroupedGeometricSimultaneousLogApproximationCertificate) :
    SimultaneousLogApproximationCertificate := by
  refine
    { factor := h.scaleFactor
      threshold := 2
      factor_pos := h.scaleFactor_pos
      two_le_threshold := by rfl
      window := ?_ }
  intro H hH
  have hHPos : 0 < (H : ℝ) := by
    exact_mod_cast (show 0 < H by omega)
  have hTargetPos : 0 < (1 / (2 * (H : ℝ)) : ℝ) := by positivity
  obtain ⟨shift, hScale, hPrevious⟩ :=
    exists_least_geometric_scale h.start h.errorFactor_pos h.decay_pos
      h.decay_lt_one hTargetPos
  let n : ℕ := h.start + shift
  have hStart : h.start ≤ n := by
    dsimp only [n]
    omega
  let rows : Fin 3 → SimultaneousLogApproximationRow := h.rows n
  refine ⟨rows, ?_, ?_, ?_⟩
  · intro j
    simpa only [rows, n] using h.denominator_le_at_scale H hH hPrevious j
  · intro j
    have hRawError := h.error_le n hStart j
    calc
      3 * (H : ℝ) *
              |((rows j).denominator : ℝ) * logTwoDivThree -
                ((rows j).numerator23 : ℝ)| +
            2 * (H : ℝ) *
              |((rows j).denominator : ℝ) * logFourDivThree -
                ((rows j).numerator34 : ℝ)| =
          (H : ℝ) *
            (3 *
                |((h.rows n j).denominator : ℝ) * logTwoDivThree -
                  ((h.rows n j).numerator23 : ℝ)| +
              2 *
                |((h.rows n j).denominator : ℝ) * logFourDivThree -
                  ((h.rows n j).numerator34 : ℝ)|) := by
        dsimp only [rows]
        ring
      _ ≤ (H : ℝ) * (h.errorFactor * h.decay ^ n) :=
        mul_le_mul_of_nonneg_left hRawError hHPos.le
      _ ≤ (H : ℝ) * (1 / (2 * (H : ℝ))) :=
        mul_le_mul_of_nonneg_left (by simpa only [n] using hScale) hHPos.le
      _ = 1 / 2 := by field_simp
  · exact rows_separate_of_det_ne_zero rows
      (by simpa only [rows] using h.determinant_ne n hStart)

/-- Package estimates stated at the square-and-shift common scale `2*m+2`
into the grouped geometric certificate indexed by the original Rhin parameter
`m`.  Squaring both bases preserves the integer exponent `11`. -/
def groupedGeometricCertificate_of_squareScale
    (rows : ℕ → Fin 3 → SimultaneousLogApproximationRow)
    (start : ℕ) (denominatorFactor errorFactor : ℝ)
    (hDenominatorFactor : 0 < denominatorFactor)
    (hErrorFactor : 0 < errorFactor)
    (hDenominator : ∀ m : ℕ, start ≤ m → ∀ j : Fin 3,
      |((rows m j).denominator : ℝ)| ≤
        denominatorFactor * (72 : ℝ) ^ (2 * m + 2))
    (hError : ∀ m : ℕ, start ≤ m → ∀ j : Fin 3,
      3 *
            |((rows m j).denominator : ℝ) * logTwoDivThree -
              ((rows m j).numerator23 : ℝ)| +
          2 *
            |((rows m j).denominator : ℝ) * logFourDivThree -
              ((rows m j).numerator34 : ℝ)| ≤
        errorFactor * ((27 : ℝ) / 40) ^ (2 * m + 2))
    (hDeterminant : ∀ m : ℕ, start ≤ m →
      simultaneousLogApproximationDet
        (rows m 0) (rows m 1) (rows m 2) ≠ 0) :
    GroupedGeometricSimultaneousLogApproximationCertificate where
  rows := rows
  growth := (72 : ℝ) ^ 2
  decay := ((27 : ℝ) / 40) ^ 2
  denominatorFactor := denominatorFactor * (72 : ℝ) ^ 2
  errorFactor := errorFactor * ((27 : ℝ) / 40) ^ 2
  start := start
  exponent := 11
  one_le_growth := by norm_num
  decay_pos := by norm_num
  decay_lt_one := by norm_num
  denominatorFactor_pos := mul_pos hDenominatorFactor (by norm_num)
  errorFactor_pos := mul_pos hErrorFactor (by norm_num)
  exponent_le := by norm_num
  growth_decay := by norm_num [pow_succ]
  denominator_le := by
    intro m hm j
    calc
      |((rows m j).denominator : ℝ)| ≤
          denominatorFactor * (72 : ℝ) ^ (2 * m + 2) :=
        hDenominator m hm j
      _ = (denominatorFactor * (72 : ℝ) ^ 2) *
          ((72 : ℝ) ^ 2) ^ m := by
        simp only [pow_add, pow_mul]
        ring
  error_le := by
    intro m hm j
    calc
      3 *
              |((rows m j).denominator : ℝ) * logTwoDivThree -
                ((rows m j).numerator23 : ℝ)| +
            2 *
              |((rows m j).denominator : ℝ) * logFourDivThree -
                ((rows m j).numerator34 : ℝ)| ≤
          errorFactor * ((27 : ℝ) / 40) ^ (2 * m + 2) :=
        hError m hm j
      _ = (errorFactor * ((27 : ℝ) / 40) ^ 2) *
          (((27 : ℝ) / 40) ^ 2) ^ m := by
        simp only [pow_add, pow_mul]
        ring
  determinant_ne := hDeterminant

private theorem transformed_coefficients_nonzero
    {u₁ u₂ : ℤ} (h : u₁ ≠ 0 ∨ u₂ ≠ 0) :
    -u₁ - 2 * u₂ ≠ 0 ∨ u₁ + u₂ ≠ 0 := by
  by_contra hzero
  push Not at hzero
  rcases hzero with ⟨h₁, h₂⟩
  rcases h with h | h <;> omega

private theorem transformed_first_abs_le
    (u₁ u₂ : ℤ) :
    |((-u₁ - 2 * u₂ : ℤ) : ℝ)| ≤
      3 * (linearFormHeight u₁ u₂ : ℝ) := by
  have hu₁Nat : u₁.natAbs ≤ linearFormHeight u₁ u₂ :=
    le_max_left _ _
  have hu₂Nat : u₂.natAbs ≤ linearFormHeight u₁ u₂ :=
    le_max_right _ _
  have hu₁ : |(u₁ : ℝ)| ≤ (linearFormHeight u₁ u₂ : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (Nat.cast_le.mpr hu₁Nat :
        (u₁.natAbs : ℝ) ≤ (linearFormHeight u₁ u₂ : ℝ))
  have hu₂ : |(u₂ : ℝ)| ≤ (linearFormHeight u₁ u₂ : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (Nat.cast_le.mpr hu₂Nat :
        (u₂.natAbs : ℝ) ≤ (linearFormHeight u₁ u₂ : ℝ))
  calc
    |((-u₁ - 2 * u₂ : ℤ) : ℝ)| ≤
        |(u₁ : ℝ)| + 2 * |(u₂ : ℝ)| := by
          push_cast
          calc
            |-((u₁ : ℝ)) - 2 * (u₂ : ℝ)| ≤
                |-((u₁ : ℝ))| + |2 * (u₂ : ℝ)| :=
              by
                simpa only [sub_eq_add_neg, abs_neg] using
                  abs_add_le (-(u₁ : ℝ)) (-(2 * (u₂ : ℝ)))
            _ = |(u₁ : ℝ)| + 2 * |(u₂ : ℝ)| := by
              rw [abs_neg, abs_mul]
              norm_num
    _ ≤ 3 * (linearFormHeight u₁ u₂ : ℝ) := by linarith

private theorem transformed_second_abs_le
    (u₁ u₂ : ℤ) :
    |((u₁ + u₂ : ℤ) : ℝ)| ≤
      2 * (linearFormHeight u₁ u₂ : ℝ) := by
  have hu₁Nat : u₁.natAbs ≤ linearFormHeight u₁ u₂ :=
    le_max_left _ _
  have hu₂Nat : u₂.natAbs ≤ linearFormHeight u₁ u₂ :=
    le_max_right _ _
  have hu₁ : |(u₁ : ℝ)| ≤ (linearFormHeight u₁ u₂ : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (Nat.cast_le.mpr hu₁Nat :
        (u₁.natAbs : ℝ) ≤ (linearFormHeight u₁ u₂ : ℝ))
  have hu₂ : |(u₂ : ℝ)| ≤ (linearFormHeight u₁ u₂ : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (Nat.cast_le.mpr hu₂Nat :
        (u₂.natAbs : ℝ) ≤ (linearFormHeight u₁ u₂ : ℝ))
  calc
    |((u₁ + u₂ : ℤ) : ℝ)| ≤ |(u₁ : ℝ)| + |(u₂ : ℝ)| := by
      push_cast
      exact abs_add_le _ _
    _ ≤ 2 * (linearFormHeight u₁ u₂ : ℝ) := by linarith

/-- Three scale-aligned simultaneous approximations imply Rhin's frozen
large-height lower bound. -/
theorem largeHeightBound_of_simultaneousLogApproximation
    (h : SimultaneousLogApproximationCertificate) :
    LargeHeightBound := by
  refine ⟨1 / (2 * h.factor), one_div_pos.mpr (mul_pos (by norm_num) h.factor_pos), h.threshold,
    h.two_le_threshold, ?_⟩
  intro u₀ u₁ u₂ hHeight
  have hNonzero : u₁ ≠ 0 ∨ u₂ ≠ 0 := by
    by_contra hzero
    push Not at hzero
    rcases hzero with ⟨rfl, rfl⟩
    simp only [linearFormHeight, Int.natAbs_zero, max_self] at hHeight
    have hTwo := h.two_le_threshold
    omega
  let H : ℕ := linearFormHeight u₁ u₂
  let v₂₃ : ℤ := -u₁ - 2 * u₂
  let v₃₄ : ℤ := u₁ + u₂
  rcases h.window H hHeight with ⟨rows, hDenominator, hError, hSeparate⟩
  have hvNonzero : u₀ ≠ 0 ∨ v₂₃ ≠ 0 ∨ v₃₄ ≠ 0 := by
    right
    dsimp only [v₂₃, v₃₄]
    exact transformed_coefficients_nonzero hNonzero
  rcases hSeparate u₀ v₂₃ v₃₄ hvNonzero with ⟨j, hInteger⟩
  let q : ℤ := (rows j).denominator
  let p₂₃ : ℤ := (rows j).numerator23
  let p₃₄ : ℤ := (rows j).numerator34
  let integerCombination : ℤ := q * u₀ + p₂₃ * v₂₃ + p₃₄ * v₃₄
  let error₂₃ : ℝ := (q : ℝ) * logTwoDivThree - (p₂₃ : ℝ)
  let error₃₄ : ℝ := (q : ℝ) * logFourDivThree - (p₃₄ : ℝ)
  have hIntegerNe : integerCombination ≠ 0 := by
    simpa only [integerCombination, q, p₂₃, p₃₄,
      SimultaneousLogApproximationRow.pair] using hInteger
  have hIntegerOne : (1 : ℝ) ≤ |(integerCombination : ℝ)| := by
    have hIntegerOneInt : (1 : ℤ) ≤ |integerCombination| := by
      have := abs_pos.mpr hIntegerNe
      omega
    exact_mod_cast hIntegerOneInt
  have hFormIdentity :
      (integerCombination : ℝ) =
        (q : ℝ) * linearForm u₀ u₁ u₂ -
          ((v₂₃ : ℝ) * error₂₃ + (v₃₄ : ℝ) * error₃₄) := by
    dsimp only [integerCombination, error₂₃, error₃₄,
      v₂₃, v₃₄, logTwoDivThree, logFourDivThree, linearForm]
    push_cast
    ring
  have hFirstCoefficient : |(v₂₃ : ℝ)| ≤ 3 * (H : ℝ) := by
    simpa only [v₂₃, H] using transformed_first_abs_le u₁ u₂
  have hSecondCoefficient : |(v₃₄ : ℝ)| ≤ 2 * (H : ℝ) := by
    simpa only [v₃₄, H] using transformed_second_abs_le u₁ u₂
  have hErrorBudget :
      3 * (H : ℝ) * |error₂₃| + 2 * (H : ℝ) * |error₃₄| ≤ 1 / 2 := by
    simpa only [error₂₃, error₃₄, q, p₂₃, p₃₄] using hError j
  have hCombinedError :
      |(v₂₃ : ℝ) * error₂₃ + (v₃₄ : ℝ) * error₃₄| ≤ 1 / 2 := by
    calc
      |(v₂₃ : ℝ) * error₂₃ + (v₃₄ : ℝ) * error₃₄| ≤
          |(v₂₃ : ℝ) * error₂₃| + |(v₃₄ : ℝ) * error₃₄| :=
        abs_add_le _ _
      _ = |(v₂₃ : ℝ)| * |error₂₃| + |(v₃₄ : ℝ)| * |error₃₄| := by
        rw [abs_mul, abs_mul]
      _ ≤ 3 * (H : ℝ) * |error₂₃| + 2 * (H : ℝ) * |error₃₄| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hFirstCoefficient (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hSecondCoefficient (abs_nonneg _))
      _ ≤ 1 / 2 := hErrorBudget
  have hHalf :
      (1 / 2 : ℝ) ≤ |(q : ℝ)| * |linearForm u₀ u₁ u₂| := by
    have hUpper :
        |(integerCombination : ℝ)| ≤
          |(q : ℝ) * linearForm u₀ u₁ u₂| + 1 / 2 := by
      rw [hFormIdentity]
      calc
        |(q : ℝ) * linearForm u₀ u₁ u₂ -
            ((v₂₃ : ℝ) * error₂₃ + (v₃₄ : ℝ) * error₃₄)| ≤
            |(q : ℝ) * linearForm u₀ u₁ u₂| +
              |(v₂₃ : ℝ) * error₂₃ + (v₃₄ : ℝ) * error₃₄| :=
          abs_sub _ _
        _ ≤ |(q : ℝ) * linearForm u₀ u₁ u₂| + 1 / 2 :=
          add_le_add_right hCombinedError _
    rw [abs_mul] at hUpper
    linarith
  have hHPos : 0 < (H : ℝ) := by
    have hTwo := h.two_le_threshold
    have hHNat : 0 < H := by
      dsimp only [H]
      omega
    exact_mod_cast hHNat
  have hScale :
      (1 / 2 : ℝ) ≤
        (h.factor * Real.rpow (H : ℝ) (133 / 10 : ℝ)) *
          |linearForm u₀ u₁ u₂| := by
    exact hHalf.trans
      (mul_le_mul_of_nonneg_right
        (by simpa only [q] using hDenominator j)
        (abs_nonneg _))
  have hScalePos :
      0 < h.factor * Real.rpow (H : ℝ) (133 / 10 : ℝ) :=
    mul_pos h.factor_pos (Real.rpow_pos_of_pos hHPos _)
  have hDiv :
      (1 / 2 : ℝ) /
          (h.factor * Real.rpow (H : ℝ) (133 / 10 : ℝ)) ≤
        |linearForm u₀ u₁ u₂| :=
    (div_le_iff₀ hScalePos).mpr (by simpa only [mul_comm] using hScale)
  have hPower :
      Real.rpow (H : ℝ) (-(133 / 10 : ℝ)) =
        (Real.rpow (H : ℝ) (133 / 10 : ℝ))⁻¹ :=
    Real.rpow_neg hHPos.le _
  calc
    (1 / (2 * h.factor)) *
        Real.rpow (linearFormHeight u₁ u₂ : ℝ) (-(133 / 10 : ℝ)) =
        (1 / 2 : ℝ) /
          (h.factor * Real.rpow (H : ℝ) (133 / 10 : ℝ)) := by
      rw [show (linearFormHeight u₁ u₂ : ℝ) = (H : ℝ) by rfl, hPower]
      field_simp [h.factor_pos.ne', (Real.rpow_pos_of_pos hHPos _).ne']
    _ ≤ |linearForm u₀ u₁ u₂| := hDiv

/-- The raw bounded-window geometric certificate feeds the frozen
large-height theorem without an already scale-aligned premise. -/
theorem largeHeightBound_of_geometricSimultaneousLogApproximation
    (h : GeometricSimultaneousLogApproximationCertificate) :
    LargeHeightBound :=
  largeHeightBound_of_simultaneousLogApproximation h.toScaleAligned

/-- The square-shift-friendly grouped geometric certificate also reaches the
frozen large-height theorem directly. -/
theorem largeHeightBound_of_groupedGeometricSimultaneousLogApproximation
    (h : GroupedGeometricSimultaneousLogApproximationCertificate) :
    LargeHeightBound :=
  largeHeightBound_of_simultaneousLogApproximation h.toScaleAligned

end

end Rhin
end NumberTheory
end Erdos1135
