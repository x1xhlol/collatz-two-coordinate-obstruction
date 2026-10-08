/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.NumberTheory.Rhin.RangeLCM
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Sum

/-!
# A table-free base-three bound for `lcm(1, ..., n)`

This module proves the elementary denominator-growth input needed by the
literal p. 159 construction.  It uses a residual-recursive four-floor
Sylvester multinomial, exact prime-adic divisibility, and an abstract finite
prefix sum.  The prefactor is existential: no low-frequency phase table or
historical numerical constant appears here.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

open scoped BigOperators Nat

private def sylvesterPart2 (n : ℕ) : ℕ := n / 2
private def sylvesterPart3 (n : ℕ) : ℕ := n / 3
private def sylvesterPart7 (n : ℕ) : ℕ := n / 7
private def sylvesterPart43 (n : ℕ) : ℕ := n / 43

private def sylvesterRemainder (n : ℕ) : ℕ :=
  n - (sylvesterPart2 n + sylvesterPart3 n +
    sylvesterPart7 n + sylvesterPart43 n)

/-- The five-part multinomial coefficient, written as four successive
binomial choices. -/
private def sylvesterMultinomial (n : ℕ) : ℕ :=
  let a := sylvesterPart2 n
  let b := sylvesterPart3 n
  let c := sylvesterPart7 n
  let d := sylvesterPart43 n
  n.choose a * (n - a).choose b * (n - a - b).choose c *
    (n - a - b - c).choose d

private theorem sylvester_parts_sum_le (n : ℕ) :
    sylvesterPart2 n + sylvesterPart3 n +
        sylvesterPart7 n + sylvesterPart43 n ≤ n := by
  have h2 := Nat.div_mul_le_self n 2
  have h3 := Nat.div_mul_le_self n 3
  have h7 := Nat.div_mul_le_self n 7
  have h43 := Nat.div_mul_le_self n 43
  unfold sylvesterPart2 sylvesterPart3 sylvesterPart7 sylvesterPart43
  omega

/-- The reciprocal sum `1/2 + 1/3 + 1/7 + 1/43 = 1805/1806`
is strictly below one. -/
private theorem sylvester_parts_sum_lt {n : ℕ} (hn : 0 < n) :
    sylvesterPart2 n + sylvesterPart3 n +
        sylvesterPart7 n + sylvesterPart43 n < n := by
  have h2 := Nat.div_mul_le_self n 2
  have h3 := Nat.div_mul_le_self n 3
  have h7 := Nat.div_mul_le_self n 7
  have h43 := Nat.div_mul_le_self n 43
  unfold sylvesterPart2 sylvesterPart3 sylvesterPart7 sylvesterPart43
  omega

private theorem choose_weighted_term_le_add_pow
    (n k x y : ℕ) (hk : k ≤ n) :
    n.choose k * x ^ k * y ^ (n - k) ≤ (x + y) ^ n := by
  have hkMem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hTerm :
      x ^ k * y ^ (n - k) * n.choose k ≤
        ∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * n.choose m := by
    exact Finset.single_le_sum
      (f := fun m ↦ x ^ m * y ^ (n - m) * n.choose m)
      (fun _ _ ↦ Nat.zero_le _) hkMem
  calc
    n.choose k * x ^ k * y ^ (n - k) =
        x ^ k * y ^ (n - k) * n.choose k := by ac_rfl
    _ ≤ ∑ m ∈ Finset.range (n + 1),
        x ^ m * y ^ (n - m) * n.choose m := hTerm
    _ = (x + y) ^ n := (add_pow x y n).symm

/-- Exact weighted multinomial estimate associated to
`(903,602,258,42,1) / 1806`. -/
private theorem sylvesterMultinomial_weighted_le (n : ℕ) :
    sylvesterMultinomial n *
        903 ^ sylvesterPart2 n *
        602 ^ sylvesterPart3 n *
        258 ^ sylvesterPart7 n *
        42 ^ sylvesterPart43 n ≤
      1806 ^ n := by
  let a := sylvesterPart2 n
  let b := sylvesterPart3 n
  let c := sylvesterPart7 n
  let d := sylvesterPart43 n
  have hsum : a + b + c + d ≤ n := by
    simpa only [a, b, c, d] using sylvester_parts_sum_le n
  have ha : a ≤ n := by omega
  have hb : b ≤ n - a := by omega
  have hc : c ≤ n - a - b := by omega
  have hd : d ≤ n - a - b - c := by omega
  have h1 := choose_weighted_term_le_add_pow n a 903 903 ha
  have h2 := choose_weighted_term_le_add_pow (n - a) b 602 301 hb
  have h3 := choose_weighted_term_le_add_pow (n - a - b) c 258 43 hc
  have h4 := choose_weighted_term_le_add_pow (n - a - b - c) d 42 1 hd
  norm_num only at h1 h2 h3 h4
  have h12 :
      n.choose a * (n - a).choose b *
          903 ^ a * 602 ^ b * 301 ^ (n - a - b) ≤
        1806 ^ n := by
    calc
      n.choose a * (n - a).choose b *
            903 ^ a * 602 ^ b * 301 ^ (n - a - b) =
          (n.choose a * 903 ^ a) *
            ((n - a).choose b * 602 ^ b * 301 ^ (n - a - b)) := by ac_rfl
      _ ≤ (n.choose a * 903 ^ a) * 903 ^ (n - a) :=
        Nat.mul_le_mul_left _ h2
      _ = n.choose a * 903 ^ a * 903 ^ (n - a) := by ac_rfl
      _ ≤ 1806 ^ n := h1
  have h123 :
      n.choose a * (n - a).choose b * (n - a - b).choose c *
          903 ^ a * 602 ^ b * 258 ^ c * 43 ^ (n - a - b - c) ≤
        1806 ^ n := by
    calc
      n.choose a * (n - a).choose b * (n - a - b).choose c *
            903 ^ a * 602 ^ b * 258 ^ c * 43 ^ (n - a - b - c) =
          (n.choose a * (n - a).choose b * 903 ^ a * 602 ^ b) *
            ((n - a - b).choose c * 258 ^ c * 43 ^ (n - a - b - c)) := by
              ac_rfl
      _ ≤ (n.choose a * (n - a).choose b * 903 ^ a * 602 ^ b) *
          301 ^ (n - a - b) := Nat.mul_le_mul_left _ h3
      _ = n.choose a * (n - a).choose b *
          903 ^ a * 602 ^ b * 301 ^ (n - a - b) := by ac_rfl
      _ ≤ 1806 ^ n := h12
  have h1234 :
      n.choose a * (n - a).choose b * (n - a - b).choose c *
          (n - a - b - c).choose d *
          903 ^ a * 602 ^ b * 258 ^ c * 42 ^ d ≤
        1806 ^ n := by
    calc
      n.choose a * (n - a).choose b * (n - a - b).choose c *
            (n - a - b - c).choose d *
            903 ^ a * 602 ^ b * 258 ^ c * 42 ^ d =
          (n.choose a * (n - a).choose b * (n - a - b).choose c *
            903 ^ a * 602 ^ b * 258 ^ c) *
            ((n - a - b - c).choose d * 42 ^ d * 1 ^
              (n - a - b - c - d)) := by
                simp only [one_pow, mul_one]
                ac_rfl
      _ ≤ (n.choose a * (n - a).choose b * (n - a - b).choose c *
            903 ^ a * 602 ^ b * 258 ^ c) *
          43 ^ (n - a - b - c) := Nat.mul_le_mul_left _ h4
      _ = n.choose a * (n - a).choose b * (n - a - b).choose c *
          903 ^ a * 602 ^ b * 258 ^ c * 43 ^ (n - a - b - c) := by ac_rfl
      _ ≤ 1806 ^ n := h123
  simpa only [sylvesterMultinomial, a, b, c, d, sylvesterPart2,
    sylvesterPart3, sylvesterPart7, sylvesterPart43, mul_assoc] using h1234

/-- The five Sylvester parts, including the remainder, form an exact
partition of `n`. -/
private theorem sylvester_parts_add_remainder (n : ℕ) :
    sylvesterPart2 n + sylvesterPart3 n + sylvesterPart7 n +
        sylvesterPart43 n + sylvesterRemainder n = n := by
  have h := sylvester_parts_sum_le n
  unfold sylvesterRemainder
  omega

private theorem sylvesterMultinomial_pos (n : ℕ) :
    0 < sylvesterMultinomial n := by
  let a := sylvesterPart2 n
  let b := sylvesterPart3 n
  let c := sylvesterPart7 n
  let d := sylvesterPart43 n
  have hsum : a + b + c + d ≤ n := by
    simpa only [a, b, c, d] using sylvester_parts_sum_le n
  have ha : a ≤ n := by omega
  have hb : b ≤ n - a := by omega
  have hc : c ≤ n - a - b := by omega
  have hd : d ≤ n - a - b - c := by omega
  simp only [sylvesterMultinomial]
  exact mul_pos (mul_pos (mul_pos (Nat.choose_pos ha) (Nat.choose_pos hb))
    (Nat.choose_pos hc)) (Nat.choose_pos hd)

/-- Factorial identity for the successive-binomial presentation of the
five-part multinomial coefficient. -/
private theorem sylvesterMultinomial_mul_factorials (n : ℕ) :
    sylvesterMultinomial n *
          (sylvesterPart2 n) ! * (sylvesterPart3 n) ! *
          (sylvesterPart7 n) ! * (sylvesterPart43 n) ! *
          (sylvesterRemainder n) ! =
      n ! := by
  let a := sylvesterPart2 n
  let b := sylvesterPart3 n
  let c := sylvesterPart7 n
  let d := sylvesterPart43 n
  let r := sylvesterRemainder n
  have hsum : a + b + c + d ≤ n := by
    simpa only [a, b, c, d] using sylvester_parts_sum_le n
  have ha : a ≤ n := by omega
  have hb : b ≤ n - a := by omega
  have hc : c ≤ n - a - b := by omega
  have hd : d ≤ n - a - b - c := by omega
  have hr : r = n - a - b - c - d := by
    have hpartition := sylvester_parts_add_remainder n
    dsimp only [a, b, c, d, r] at hpartition ⊢
    omega
  have h1 := Nat.choose_mul_factorial_mul_factorial ha
  have h2 := Nat.choose_mul_factorial_mul_factorial hb
  have h3 := Nat.choose_mul_factorial_mul_factorial hc
  have h4 := Nat.choose_mul_factorial_mul_factorial hd
  dsimp only [sylvesterMultinomial, a, b, c, d, r]
  rw [show sylvesterRemainder n = n - a - b - c - d by
    simpa only [r] using hr]
  calc
    (n.choose a * (n - a).choose b * (n - a - b).choose c *
          (n - a - b - c).choose d) * a ! * b ! * c ! * d ! *
          (n - a - b - c - d)! =
        (n.choose a * a !) *
          ((n - a).choose b * b ! *
            ((n - a - b).choose c * c ! *
              ((n - a - b - c).choose d * d ! *
                (n - a - b - c - d)!))) := by ac_rfl
    _ = (n.choose a * a !) *
          ((n - a).choose b * b ! *
            ((n - a - b).choose c * c ! * (n - a - b - c)!)) := by rw [h4]
    _ = (n.choose a * a !) *
          ((n - a).choose b * b ! * (n - a - b)!) := by rw [h3]
    _ = n.choose a * a ! * (n - a)! := by rw [h2]
    _ = n ! := h1

/-- Prime-adic form of the multinomial factorial identity. -/
private theorem factorization_sylvesterMultinomial_add_parts (n p : ℕ) :
    (sylvesterMultinomial n).factorization p +
          ((sylvesterPart2 n)!).factorization p +
          ((sylvesterPart3 n)!).factorization p +
          ((sylvesterPart7 n)!).factorization p +
          ((sylvesterPart43 n)!).factorization p +
          ((sylvesterRemainder n)!).factorization p =
      (n !).factorization p := by
  have h := congrArg (fun x : ℕ ↦ x.factorization p)
    (sylvesterMultinomial_mul_factorials n)
  dsimp only at h
  have hM : sylvesterMultinomial n ≠ 0 := (sylvesterMultinomial_pos n).ne'
  have h2 : (sylvesterPart2 n)! ≠ 0 := Nat.factorial_ne_zero _
  have h3 : (sylvesterPart3 n)! ≠ 0 := Nat.factorial_ne_zero _
  have h7 : (sylvesterPart7 n)! ≠ 0 := Nat.factorial_ne_zero _
  have h43 : (sylvesterPart43 n)! ≠ 0 := Nat.factorial_ne_zero _
  have hR : (sylvesterRemainder n)! ≠ 0 := Nat.factorial_ne_zero _
  have hM2 := mul_ne_zero hM h2
  have hM23 := mul_ne_zero hM2 h3
  have hM237 := mul_ne_zero hM23 h7
  have hM23743 := mul_ne_zero hM237 h43
  rw [Nat.factorization_mul hM23743 hR,
    Nat.factorization_mul hM237 h43,
    Nat.factorization_mul hM23 h7,
    Nat.factorization_mul hM2 h3,
    Nat.factorization_mul hM h2] at h
  simpa only [Finsupp.coe_add, Pi.add_apply, add_assoc] using h

/-- At every divisor scale `t ≤ n` above the fifth remainder part, the
Sylvester floor gap contributes at least one. -/
private theorem sylvester_floor_gap_pos (n t : ℕ) (ht : 0 < t)
    (htn : t ≤ n) (hRemainder : sylvesterRemainder n < t) :
    sylvesterPart2 n / t + sylvesterPart3 n / t +
          sylvesterPart7 n / t + sylvesterPart43 n / t +
          sylvesterRemainder n / t <
      n / t := by
  have hx : 0 < n / t := Nat.div_pos htn ht
  have hStrict := sylvester_parts_sum_lt hx
  have hRemainderZero : sylvesterRemainder n / t = 0 :=
    Nat.div_eq_of_lt hRemainder
  simp only [sylvesterPart2, sylvesterPart3, sylvesterPart7,
    sylvesterPart43, Nat.div_div_eq_div_mul] at hStrict ⊢
  rw [hRemainderZero]
  simp only [add_zero]
  convert hStrict using 1; simp only [mul_comm]

/-- Division is subadditive across the exact five-part partition. -/
private theorem sylvester_floor_parts_le (n t : ℕ) :
    sylvesterPart2 n / t + sylvesterPart3 n / t +
          sylvesterPart7 n / t + sylvesterPart43 n / t +
          sylvesterRemainder n / t ≤
      n / t := by
  have h23 := Nat.add_div_le_add_div (sylvesterPart2 n) (sylvesterPart3 n) t
  have h237 := Nat.add_div_le_add_div
    (sylvesterPart2 n + sylvesterPart3 n) (sylvesterPart7 n) t
  have h23743 := Nat.add_div_le_add_div
    (sylvesterPart2 n + sylvesterPart3 n + sylvesterPart7 n)
    (sylvesterPart43 n) t
  have hAll := Nat.add_div_le_add_div
    (sylvesterPart2 n + sylvesterPart3 n + sylvesterPart7 n +
      sylvesterPart43 n) (sylvesterRemainder n) t
  rw [sylvester_parts_add_remainder] at hAll
  omega

/-- The Sylvester multinomial supplies every prime-adic exponent above the
remainder's logarithmic range. -/
private theorem exponent_le_factorization_sylvesterMultinomial_add_log
    {n p e : ℕ} (hp : p.Prime) (hpow : p ^ e ≤ n) :
    e ≤ (sylvesterMultinomial n).factorization p +
      Nat.log p (sylvesterRemainder n) := by
  classical
  let B := Nat.log p n + 1
  let S := Finset.Ico 1 B
  let T := Finset.Icc (Nat.log p (sylvesterRemainder n) + 1) e
  have heLog : e ≤ Nat.log p n := Nat.le_log_of_pow_le hp.one_lt hpow
  have hTS : T ⊆ S := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    apply Finset.mem_Ico.mpr
    dsimp only [T, S, B] at hi' ⊢
    omega
  have hPoint : ∀ i ∈ S,
      (sylvesterPart2 n / p ^ i + sylvesterPart3 n / p ^ i +
          sylvesterPart7 n / p ^ i + sylvesterPart43 n / p ^ i +
          sylvesterRemainder n / p ^ i) +
          (if i ∈ T then 1 else 0) ≤
        n / p ^ i := by
    intro i hiS
    by_cases hiT : i ∈ T
    · have hiBounds := Finset.mem_Icc.mp hiT
      have hiLe : i ≤ e := hiBounds.2
      have hpiLe : p ^ i ≤ n :=
        (Nat.pow_le_pow_right hp.pos hiLe).trans hpow
      have hRemainderPow : sylvesterRemainder n < p ^ i := by
        have hBase := Nat.lt_pow_succ_log_self hp.one_lt (sylvesterRemainder n)
        have hPowerMono :
            p ^ (Nat.log p (sylvesterRemainder n) + 1) ≤ p ^ i :=
          Nat.pow_le_pow_right hp.pos hiBounds.1
        exact hBase.trans_le hPowerMono
      have hStrict := sylvester_floor_gap_pos n (p ^ i)
        (Nat.pow_pos hp.pos) hpiLe hRemainderPow
      simp only [hiT, if_true]
      omega
    · have hWeak := sylvester_floor_parts_le n (p ^ i)
      simpa only [hiT, if_false, add_zero] using hWeak
  have hSum := Finset.sum_le_sum hPoint
  have hFilter : {i ∈ S | i ∈ T} = T := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi ↦ hi.2
    · exact fun hi ↦ ⟨hTS hi, hi⟩
  have hSumExpanded :
      (∑ i ∈ S, sylvesterPart2 n / p ^ i) +
          (∑ i ∈ S, sylvesterPart3 n / p ^ i) +
          (∑ i ∈ S, sylvesterPart7 n / p ^ i) +
          (∑ i ∈ S, sylvesterPart43 n / p ^ i) +
          (∑ i ∈ S, sylvesterRemainder n / p ^ i) + T.card ≤
        ∑ i ∈ S, n / p ^ i := by
    simpa only [Finset.sum_add_distrib, Finset.sum_boole, hFilter,
      Nat.cast_id, add_assoc] using hSum
  have hFactorization := factorization_sylvesterMultinomial_add_parts n p
  have hPart2Log : Nat.log p (sylvesterPart2 n) < B := by
    have hle : sylvesterPart2 n ≤ n := by
      have h := sylvester_parts_sum_le n
      omega
    have hlog : Nat.log p (sylvesterPart2 n) ≤ Nat.log p n :=
      Nat.log_mono_right (b := p) hle
    dsimp only [B]
    omega
  have hPart3Log : Nat.log p (sylvesterPart3 n) < B := by
    have hle : sylvesterPart3 n ≤ n := by
      have h := sylvester_parts_sum_le n
      omega
    have hlog : Nat.log p (sylvesterPart3 n) ≤ Nat.log p n :=
      Nat.log_mono_right (b := p) hle
    dsimp only [B]
    omega
  have hPart7Log : Nat.log p (sylvesterPart7 n) < B := by
    have hle : sylvesterPart7 n ≤ n := by
      have h := sylvester_parts_sum_le n
      omega
    have hlog : Nat.log p (sylvesterPart7 n) ≤ Nat.log p n :=
      Nat.log_mono_right (b := p) hle
    dsimp only [B]
    omega
  have hPart43Log : Nat.log p (sylvesterPart43 n) < B := by
    have hle : sylvesterPart43 n ≤ n := by
      have h := sylvester_parts_sum_le n
      omega
    have hlog : Nat.log p (sylvesterPart43 n) ≤ Nat.log p n :=
      Nat.log_mono_right (b := p) hle
    dsimp only [B]
    omega
  have hRemainderLe : sylvesterRemainder n ≤ n := by
    have h := sylvester_parts_add_remainder n
    omega
  have hRemainderLog : Nat.log p (sylvesterRemainder n) < B := by
    have hlog : Nat.log p (sylvesterRemainder n) ≤ Nat.log p n :=
      Nat.log_mono_right (b := p) hRemainderLe
    dsimp only [B]
    omega
  have hnLog : Nat.log p n < B := by
    dsimp only [B]
    omega
  rw [Nat.factorization_factorial hp hPart2Log,
    Nat.factorization_factorial hp hPart3Log,
    Nat.factorization_factorial hp hPart7Log,
    Nat.factorization_factorial hp hPart43Log,
    Nat.factorization_factorial hp hRemainderLog,
    Nat.factorization_factorial hp hnLog] at hFactorization
  change _ ≤ _
  have hCard : T.card = e - Nat.log p (sylvesterRemainder n) := by
    dsimp only [T]
    rw [Nat.card_Icc]
    omega
  rw [hCard] at hSumExpanded
  dsimp only [S, B] at hSumExpanded hFactorization
  omega

private theorem pow_log_dvd_rangeLCM (p r : ℕ) (hp : p.Prime) :
    p ^ Nat.log p r ∣ rangeLCM r := by
  by_cases hr : r = 0
  · subst r
    simp [rangeLCM]
  · apply Finset.dvd_lcm
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.one_le_pow _ _ hp.pos, Nat.pow_log_le_self p hr⟩

/-- Every prime power at most `n` divides the product of the Sylvester
multinomial and the smaller range LCM. -/
private theorem prime_power_dvd_sylvesterMultinomial_mul_rangeLCM
    {n p e : ℕ} (hp : p.Prime) (hpow : p ^ e ≤ n) :
    p ^ e ∣ sylvesterMultinomial n * rangeLCM (sylvesterRemainder n) := by
  have hM : sylvesterMultinomial n ≠ 0 := (sylvesterMultinomial_pos n).ne'
  have hL : rangeLCM (sylvesterRemainder n) ≠ 0 := rangeLCM_ne_zero _
  have hLog :
      Nat.log p (sylvesterRemainder n) ≤
        (rangeLCM (sylvesterRemainder n)).factorization p :=
    (hp.pow_dvd_iff_le_factorization hL).mp
      (pow_log_dvd_rangeLCM p (sylvesterRemainder n) hp)
  rw [hp.pow_dvd_iff_le_factorization (mul_ne_zero hM hL),
    Nat.factorization_mul hM hL, Finsupp.coe_add, Pi.add_apply]
  exact (exponent_le_factorization_sylvesterMultinomial_add_log hp hpow).trans
    (Nat.add_le_add_left hLog _)

/-- Table-free Sylvester divisibility recurrence for the full range LCM. -/
private theorem rangeLCM_dvd_sylvesterMultinomial_mul_rangeLCM (n : ℕ) :
    rangeLCM n ∣
      sylvesterMultinomial n * rangeLCM (sylvesterRemainder n) := by
  apply Finset.lcm_dvd
  intro k hk
  have hkBounds := Finset.mem_Icc.mp hk
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p e hp hpk
  have hpke : p ^ e ≤ k := Nat.le_of_dvd (by omega) hpk
  exact prime_power_dvd_sylvesterMultinomial_mul_rangeLCM hp
    (hpke.trans hkBounds.2)

private theorem rangeLCM_le_sylvesterMultinomial_mul_rangeLCM (n : ℕ) :
    rangeLCM n ≤
      sylvesterMultinomial n * rangeLCM (sylvesterRemainder n) :=
  Nat.le_of_dvd
    (mul_pos (sylvesterMultinomial_pos n) (rangeLCM_pos _))
    (rangeLCM_dvd_sylvesterMultinomial_mul_rangeLCM n)

/-- Exact contraction behind the four-floor Sylvester multinomial after
cancelling common prime factors. -/
private theorem sylvester_multinomial_block_contraction_reduced :
    2 ^ 904 * 7 ^ 259 * 43 ^ 43 < 3 ^ 1179 := by
  have hTwoBlock : (2 : ℕ) ^ 19 < 3 ^ 12 := by norm_num
  have hTwoTail : (2 : ℕ) ^ 11 < 3 ^ 7 := by norm_num
  have hSevenBlock : (7 : ℕ) ^ 22 < 3 ^ 39 := by norm_num
  have hSevenTail : (7 : ℕ) ^ 17 < 3 ^ 31 := by norm_num
  have hFortyThreeBlock : (43 : ℕ) ^ 7 < 3 ^ 24 := by norm_num
  have hFortyThreeTail : (43 : ℕ) < 3 ^ 4 := by norm_num
  have hTwo : (2 : ℕ) ^ 904 < 3 ^ 571 := by
    calc
      (2 : ℕ) ^ 904 = (2 ^ 19) ^ 47 * 2 ^ 11 := by
        rw [show 904 = 19 * 47 + 11 by norm_num, pow_add, pow_mul]
      _ < (3 ^ 12) ^ 47 * 3 ^ 7 := by gcongr
      _ = 3 ^ 571 := by
        rw [← pow_mul, ← pow_add]
  have hSeven : (7 : ℕ) ^ 259 < 3 ^ 460 := by
    calc
      (7 : ℕ) ^ 259 = (7 ^ 22) ^ 11 * 7 ^ 17 := by
        rw [show 259 = 22 * 11 + 17 by norm_num, pow_add, pow_mul]
      _ < (3 ^ 39) ^ 11 * 3 ^ 31 := by gcongr
      _ = 3 ^ 460 := by
        rw [← pow_mul, ← pow_add]
  have hFortyThree : (43 : ℕ) ^ 43 < 3 ^ 148 := by
    calc
      (43 : ℕ) ^ 43 = (43 ^ 7) ^ 6 * 43 := by
        rw [show 43 = 7 * 6 + 1 by norm_num, pow_add, pow_mul, pow_one]
      _ < (3 ^ 24) ^ 6 * 3 ^ 4 := by gcongr
      _ = 3 ^ 148 := by
        rw [← pow_mul, ← pow_add]
  have hTwoSeven :
      (2 : ℕ) ^ 904 * 7 ^ 259 < 3 ^ 571 * 3 ^ 460 :=
    Nat.mul_lt_mul_of_lt_of_lt hTwo hSeven
  have hAll :
      (2 : ℕ) ^ 904 * 7 ^ 259 * 43 ^ 43 <
        3 ^ 571 * 3 ^ 460 * 3 ^ 148 :=
    Nat.mul_lt_mul_of_lt_of_lt hTwoSeven hFortyThree
  calc
    2 ^ 904 * 7 ^ 259 * 43 ^ 43 < 3 ^ 571 * 3 ^ 460 * 3 ^ 148 := hAll
    _ = 3 ^ 1179 := by rw [← pow_add, ← pow_add]

set_option maxRecDepth 100000 in
/-- The uncancelled weighted form consumed by the multinomial estimate. -/
private theorem sylvester_multinomial_block_contraction :
    3 ^ 24 * 602 ^ 1806 <
      903 ^ 903 * 602 ^ 602 * 258 ^ 258 * 42 ^ 42 := by
  let common : ℕ := 2 ^ 902 * 3 * 7 ^ 1547 * 43 ^ 1763
  have hCommon : 0 < common := by
    dsimp only [common]
    positivity
  have hReducedReserve :
      3 ^ 23 * (2 ^ 904 * 7 ^ 259 * 43 ^ 43) < 3 ^ 1202 := by
    calc
      3 ^ 23 * (2 ^ 904 * 7 ^ 259 * 43 ^ 43) < 3 ^ 23 * 3 ^ 1179 :=
        Nat.mul_lt_mul_of_pos_left
          sylvester_multinomial_block_contraction_reduced (by positivity)
      _ = 3 ^ 1202 := by rw [← pow_add]
  have hScaled := Nat.mul_lt_mul_of_pos_left hReducedReserve hCommon
  have hTwoNum : (2 : ℕ) ^ 1806 = 2 ^ 902 * 2 ^ 904 := by
    rw [← pow_add]
  have hSevenNum : (7 : ℕ) ^ 1806 = 7 ^ 1547 * 7 ^ 259 := by
    rw [← pow_add]
  have hFortyThreeNum : (43 : ℕ) ^ 1806 = 43 ^ 1763 * 43 ^ 43 := by
    rw [← pow_add]
  have hThreeNum : (3 : ℕ) ^ 24 = 3 * 3 ^ 23 := by
    rw [← pow_succ']
  have hLeft :
      3 ^ 24 * 602 ^ 1806 =
        common * (3 ^ 23 * (2 ^ 904 * 7 ^ 259 * 43 ^ 43)) := by
    rw [show (602 : ℕ) = (2 * 7) * 43 by norm_num, mul_pow, mul_pow,
      hTwoNum, hSevenNum, hFortyThreeNum, hThreeNum]
    dsimp only [common]
    ac_rfl
  have hTwoDen : (2 : ℕ) ^ 902 = 2 ^ 602 * 2 ^ 258 * 2 ^ 42 := by
    rw [← pow_add, ← pow_add]
  have hThreeDen : (3 : ℕ) * 3 ^ 1202 = 3 ^ 903 * 3 ^ 258 * 3 ^ 42 := by
    rw [← pow_add, ← pow_add, ← pow_succ']
  have hSevenDen : (7 : ℕ) ^ 1547 = 7 ^ 903 * 7 ^ 602 * 7 ^ 42 := by
    rw [← pow_add, ← pow_add]
  have hFortyThreeDen : (43 : ℕ) ^ 1763 =
      43 ^ 903 * 43 ^ 602 * 43 ^ 258 := by
    rw [← pow_add, ← pow_add]
  have hRight :
      common * 3 ^ 1202 =
        903 ^ 903 * 602 ^ 602 * 258 ^ 258 * 42 ^ 42 := by
    rw [show (903 : ℕ) = (3 * 7) * 43 by norm_num,
      show (602 : ℕ) = (2 * 7) * 43 by norm_num,
      show (258 : ℕ) = (2 * 3) * 43 by norm_num,
      show (42 : ℕ) = (2 * 3) * 7 by norm_num]
    simp only [mul_pow]
    dsimp only [common]
    rw [hTwoDen, hSevenDen, hFortyThreeDen]
    set_option exponentiation.threshold 2048 in
    calc
      (2 ^ 602 * 2 ^ 258 * 2 ^ 42) * 3 *
          (7 ^ 903 * 7 ^ 602 * 7 ^ 42) *
          (43 ^ 903 * 43 ^ 602 * 43 ^ 258) * 3 ^ 1202 =
        (3 * 3 ^ 1202) *
          (2 ^ 602 * 2 ^ 258 * 2 ^ 42) *
          (7 ^ 903 * 7 ^ 602 * 7 ^ 42) *
          (43 ^ 903 * 43 ^ 602 * 43 ^ 258) := by ac_rfl
      _ = (3 ^ 903 * 3 ^ 258 * 3 ^ 42) *
          (2 ^ 602 * 2 ^ 258 * 2 ^ 42) *
          (7 ^ 903 * 7 ^ 602 * 7 ^ 42) *
          (43 ^ 903 * 43 ^ 602 * 43 ^ 258) := by rw [hThreeDen]
      _ = ((3 ^ 903 * 7 ^ 903) * 43 ^ 903) *
          ((2 ^ 602 * 7 ^ 602) * 43 ^ 602) *
          ((2 ^ 258 * 3 ^ 258) * 43 ^ 258) *
          ((2 ^ 42 * 3 ^ 42) * 7 ^ 42) := by ac_rfl
  calc
    3 ^ 24 * 602 ^ 1806 =
        common * (3 ^ 23 * (2 ^ 904 * 7 ^ 259 * 43 ^ 43)) := hLeft
    _ < common * 3 ^ 1202 := hScaled
    _ = 903 ^ 903 * 602 ^ 602 * 258 ^ 258 * 42 ^ 42 := hRight

/-- Any eventually contractive recurrence against base `3` yields one global
base-`3` bound after absorbing the finite initial range into a prefactor. -/
private theorem exists_three_pow_bound_of_contractive_recurrence
    (L M r : ℕ → ℕ) (threshold : ℕ)
    (hRecurrence : ∀ n, threshold ≤ n → L n ≤ M n * L (r n))
    (hDescent : ∀ n, threshold ≤ n → r n < n)
    (hContraction : ∀ n, threshold ≤ n → M n * 3 ^ r n ≤ 3 ^ n) :
    ∃ K : ℕ, 0 < K ∧ ∀ n, L n ≤ K * 3 ^ n := by
  let K : ℕ := 1 + ∑ i ∈ Finset.range threshold, L i
  have hKPos : 0 < K := by
    dsimp only [K]
    omega
  refine ⟨K, hKPos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : threshold ≤ n
      · have hIH : L (r n) ≤ K * 3 ^ r n := ih (r n) (hDescent n hn)
        calc
          L n ≤ M n * L (r n) := hRecurrence n hn
          _ ≤ M n * (K * 3 ^ r n) := Nat.mul_le_mul_left _ hIH
          _ = K * (M n * 3 ^ r n) := by ac_rfl
          _ ≤ K * 3 ^ n := Nat.mul_le_mul_left K (hContraction n hn)
      · have hnRange : n ∈ Finset.range threshold :=
          Finset.mem_range.mpr (by omega)
        have hFinite : L n ≤ ∑ i ∈ Finset.range threshold, L i := by
          exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hnRange
        have hLK : L n ≤ K := by
          dsimp only [K]
          omega
        exact hLK.trans (Nat.le_mul_of_pos_right K (by positivity))

/-- The weight in the five-part multinomial estimate. -/
private def sylvesterWeight (n : ℕ) : ℕ :=
  903 ^ sylvesterPart2 n *
    602 ^ sylvesterPart3 n *
    258 ^ sylvesterPart7 n *
    42 ^ sylvesterPart43 n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Past an explicit coarse threshold, the weighted multinomial reserve
contracts the range-LCM recurrence against base `3`. -/
private theorem sylvesterMultinomial_three_pow_contraction
    {n : ℕ} (hn : 993300 ≤ n) :
    sylvesterMultinomial n * 3 ^ sylvesterRemainder n ≤ 3 ^ n := by
  let q := n / 1806
  have hq : 550 ≤ q := by
    dsimp only [q]
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    norm_num
    exact hn
  have hqBase : 1806 * q ≤ n := by
    dsimp only [q]
    simpa only [mul_comm] using Nat.div_mul_le_self n 1806
  have hnUpper : n ≤ 1806 * q + 1805 := by
    have h := Nat.lt_mul_div_succ n (by norm_num : 0 < (1806 : ℕ))
    dsimp only [q]
    omega
  have ha : 903 * q ≤ sylvesterPart2 n := by
    unfold sylvesterPart2
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    omega
  have hb : 602 * q ≤ sylvesterPart3 n := by
    unfold sylvesterPart3
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    omega
  have hc : 258 * q ≤ sylvesterPart7 n := by
    unfold sylvesterPart7
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    omega
  have hd : 42 * q ≤ sylvesterPart43 n := by
    unfold sylvesterPart43
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    omega
  have hr : sylvesterRemainder n ≤ q + 1805 := by
    have hpartition := sylvester_parts_add_remainder n
    omega
  let block : ℕ := 903 ^ 903 * 602 ^ 602 * 258 ^ 258 * 42 ^ 42
  have hWeightBlock : block ^ q ≤ sylvesterWeight n := by
    have h903 := Nat.pow_le_pow_right (by norm_num : 0 < (903 : ℕ)) ha
    have h602 := Nat.pow_le_pow_right (by norm_num : 0 < (602 : ℕ)) hb
    have h258 := Nat.pow_le_pow_right (by norm_num : 0 < (258 : ℕ)) hc
    have h42 := Nat.pow_le_pow_right (by norm_num : 0 < (42 : ℕ)) hd
    dsimp only [block, sylvesterWeight]
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
      ← pow_mul]
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h903 h602) h258) h42
  have hBlock : 3 ^ 24 * 602 ^ 1806 ≤ block := by
    dsimp only [block]
    exact Nat.le_of_lt sylvester_multinomial_block_contraction
  have hMain :
      3 ^ (24 * q) * 602 ^ (1806 * q) ≤ sylvesterWeight n := by
    calc
      3 ^ (24 * q) * 602 ^ (1806 * q) =
          (3 ^ 24 * 602 ^ 1806) ^ q := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ block ^ q := Nat.pow_le_pow_left hBlock q
      _ ≤ sylvesterWeight n := hWeightBlock
  have h602Residual : 602 ^ 1805 ≤ 3 ^ (6 * 1805) := by
    set_option exponentiation.threshold 2048 in
    calc
      602 ^ 1805 ≤ (3 ^ 6) ^ 1805 :=
        Nat.pow_le_pow_left (by norm_num) 1805
      _ = 3 ^ (6 * 1805) := by rw [pow_mul]
  have hExponent : 6 * 1805 + (q + 1805) ≤ 24 * q := by omega
  have hResidual :
      602 ^ 1805 * 3 ^ (q + 1805) ≤ 3 ^ (24 * q) := by
    calc
      602 ^ 1805 * 3 ^ (q + 1805) ≤
          3 ^ (6 * 1805) * 3 ^ (q + 1805) :=
        Nat.mul_le_mul_right _ h602Residual
      _ = 3 ^ (6 * 1805 + (q + 1805)) :=
        (pow_add 3 (6 * 1805) (q + 1805)).symm
      _ ≤ 3 ^ (24 * q) := Nat.pow_le_pow_right (by norm_num) hExponent
  have hScale :
      602 ^ n * 3 ^ sylvesterRemainder n ≤ sylvesterWeight n := by
    calc
      602 ^ n * 3 ^ sylvesterRemainder n ≤
          602 ^ (1806 * q + 1805) * 3 ^ (q + 1805) :=
        Nat.mul_le_mul
          (Nat.pow_le_pow_right (by norm_num) hnUpper)
          (Nat.pow_le_pow_right (by norm_num) hr)
      _ = 602 ^ (1806 * q) *
          (602 ^ 1805 * 3 ^ (q + 1805)) := by
        rw [pow_add 602 (1806 * q) 1805]
        exact mul_assoc _ _ _
      _ ≤ 602 ^ (1806 * q) * 3 ^ (24 * q) :=
        Nat.mul_le_mul_left _ hResidual
      _ = 3 ^ (24 * q) * 602 ^ (1806 * q) := mul_comm _ _
      _ ≤ sylvesterWeight n := hMain
  have hWeighted := sylvesterMultinomial_weighted_le n
  have hCombined :
      (sylvesterMultinomial n * 3 ^ sylvesterRemainder n) * 602 ^ n ≤
        3 ^ n * 602 ^ n := by
    calc
      (sylvesterMultinomial n * 3 ^ sylvesterRemainder n) * 602 ^ n =
          sylvesterMultinomial n *
            (602 ^ n * 3 ^ sylvesterRemainder n) := by
        rw [mul_assoc]
        exact congrArg (sylvesterMultinomial n * ·) (mul_comm _ _)
      _ ≤ sylvesterMultinomial n * sylvesterWeight n :=
        Nat.mul_le_mul_left _ hScale
      _ ≤ 1806 ^ n := by
        simpa only [sylvesterWeight, mul_assoc] using hWeighted
      _ = 3 ^ n * 602 ^ n := by
        rw [show (1806 : ℕ) = 3 * 602 by norm_num, mul_pow]
  exact Nat.le_of_mul_le_mul_right hCombined (by positivity)

private theorem sylvesterRemainder_lt_self
    {n : ℕ} (hn : 993300 ≤ n) : sylvesterRemainder n < n := by
  have hpartition := sylvester_parts_add_remainder n
  have hPart2 : 0 < sylvesterPart2 n := by
    unfold sylvesterPart2
    omega
  omega

/-- Fully table-free global base-`3` bound for `lcm(1,...,n)`, with the
finite initial range absorbed symbolically into one positive prefactor. -/
theorem exists_rangeLCM_le_const_mul_three_pow :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, rangeLCM n ≤ K * 3 ^ n := by
  exact exists_three_pow_bound_of_contractive_recurrence
    rangeLCM sylvesterMultinomial sylvesterRemainder 993300
    (fun n _ ↦ rangeLCM_le_sylvesterMultinomial_mul_rangeLCM n)
    (fun _ hn ↦ sylvesterRemainder_lt_self hn)
    (fun _ hn ↦ sylvesterMultinomial_three_pow_contraction hn)

end Rhin
end NumberTheory
end Erdos1135
