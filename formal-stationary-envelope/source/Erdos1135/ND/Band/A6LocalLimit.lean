/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Fourier.A6LogProducts
import Erdos1135.ND.Fourier.A6Wallis
import Erdos1135.ND.Band.A6Gaussian

/-!
# A6 Signed Local Limit

This leaf combines the checked signed logarithmic products with the finite
Wallis normalization.  It proves the raw pointwise Gaussian comparison on
both sides of the center and then packages them using the natural central
displacement.  Recentering, tube summation, and the A6 integral and exterior
estimates remain downstream.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

/-- The explicit signed log-product error used by the raw A6 local limit. -/
def ndA6LocalEta (n d : ℕ) : ℝ :=
  16 * ((d : ℝ) / (n : ℝ) + (d : ℝ) ^ 3 / (n : ℝ) ^ 2)

/-- The total relative error after finite Wallis normalization and
exponentiation of the signed log product. -/
def ndA6LocalRelativeError (n d : ℕ) : ℝ :=
  1 / (((2 * n + 1 : ℕ) : ℝ)) + 2 * ndA6LocalEta n d

/-- Exact right-hand endpoint product, expressed through its finite signed
logarithmic increments. -/
theorem ndGeom2EndpointMass_two_mul_add_eq_center_mul_exp
    {n d : ℕ} (hn : 0 < n) :
    ndGeom2EndpointMass n (2 * n + d) =
      ndGeom2EndpointMass n (2 * n) *
        Real.exp (∑ t ∈ Finset.range d, ndA6RightLogTerm n t) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show 2 * n + (d + 1) = (2 * n + d) + 1 by omega]
      rw [ndGeom2EndpointMass_succ hn (by omega : n ≤ 2 * n + d)]
      rw [ih, Finset.sum_range_succ, Real.exp_add]
      unfold ndA6RightLogTerm
      rw [Real.exp_log (by positivity)]
      rw [show 2 * n + d - n = n + d by omega]
      push_cast
      ring

/-- Exact left-hand endpoint product.  The guard `d ≤ n` is load-bearing:
without it the last logarithmic ratio can reach zero. -/
theorem ndGeom2EndpointMass_two_mul_sub_eq_center_mul_exp
    {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    ndGeom2EndpointMass n (2 * n - d) =
      ndGeom2EndpointMass n (2 * n) *
        Real.exp (∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hdlt : d < n := by omega
      have hdle : d ≤ n := hdlt.le
      have hL : n ≤ 2 * n - (d + 1) := by omega
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hd1R : (d : ℝ) + 1 ≤ n := by exact_mod_cast hdn
      have hnumR : 0 < 2 * (n : ℝ) - 2 * (d : ℝ) := by linarith
      have hdenR : 0 < 2 * (n : ℝ) - (d : ℝ) - 1 := by linarith
      have hratio :
          (2 * (((n - d : ℕ) : ℝ))) / (((2 * n - (d + 1) : ℕ) : ℝ)) =
            (2 * (n : ℝ) - 2 * (d : ℝ)) /
              (2 * (n : ℝ) - (d : ℝ) - 1) := by
        rw [Nat.cast_sub hdle]
        rw [Nat.cast_sub (by omega : d + 1 ≤ 2 * n)]
        push_cast
        congr 1 <;> ring
      rw [ndGeom2EndpointMass_eq_succ_mul hn hL]
      rw [show 2 * n - (d + 1) + 1 = 2 * n - d by omega]
      rw [ih hdle, Finset.sum_range_succ, Real.exp_add]
      unfold ndA6LeftLogTerm
      rw [Real.exp_log (div_pos hnumR hdenR)]
      rw [show 2 * n - (d + 1) - n + 1 = n - d by omega]
      rw [mul_div_assoc, hratio]
      ring

/-- The finite central amplitude is the exact ratio between the endpoint
mass at the center and the Gaussian peak. -/
theorem ndGeom2EndpointMass_two_mul_eq_gaussian_zero_mul_centralAmplitude
    {n : ℕ} (hn : 0 < n) :
    ndGeom2EndpointMass n (2 * n) =
      ndA6Gaussian (n : ℝ) 0 * ndA6CentralAmplitude n := by
  rw [ndA6Gaussian_zero]
  unfold ndA6CentralAmplitude
  have hsqrt : Real.sqrt (4 * Real.pi * (n : ℝ)) ≠ 0 := by
    positivity
  field_simp [hsqrt]

private theorem ndA6CentralAmplitude_le_one
    {n : ℕ} (hn : 0 < n) :
    ndA6CentralAmplitude n ≤ 1 := by
  have hupp := ndA6CentralAmplitude_sq_le_four_mul hn
  have hfrac :
      4 * (n : ℝ) * ((n : ℝ) + 1) /
          (((2 * n + 1 : ℕ) : ℝ) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    push_cast
    nlinarith
  have hsq : ndA6CentralAmplitude n ^ 2 ≤ 1 := hupp.trans hfrac
  have hpos := ndA6CentralAmplitude_pos hn
  nlinarith

private theorem ndA6Gaussian_eq_zero_mul_exp
    {n : ℕ} (x : ℝ) :
    ndA6Gaussian (n : ℝ) x =
      ndA6Gaussian (n : ℝ) 0 *
        Real.exp (-(x ^ 2 / (4 * (n : ℝ)))) := by
  simp [ndA6Gaussian]

private theorem ndGeom2EndpointMass_two_mul_add_factorization
    {n d : ℕ} (hn : 0 < n) :
    ndGeom2EndpointMass n (2 * n + d) =
      ndA6Gaussian (n : ℝ) (d : ℝ) * ndA6CentralAmplitude n *
        Real.exp
          ((∑ t ∈ Finset.range d, ndA6RightLogTerm n t) +
            (d : ℝ) ^ 2 / (4 * (n : ℝ))) := by
  rw [ndGeom2EndpointMass_two_mul_add_eq_center_mul_exp hn]
  rw [ndGeom2EndpointMass_two_mul_eq_gaussian_zero_mul_centralAmplitude hn]
  rw [ndA6Gaussian_eq_zero_mul_exp (n := n) (d : ℝ)]
  have hexp : Real.exp (-((d : ℝ) ^ 2 / (4 * (n : ℝ)))) *
          Real.exp
            ((∑ t ∈ Finset.range d, ndA6RightLogTerm n t) +
              (d : ℝ) ^ 2 / (4 * (n : ℝ))) =
        Real.exp (∑ t ∈ Finset.range d, ndA6RightLogTerm n t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

private theorem ndGeom2EndpointMass_two_mul_sub_factorization
    {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    ndGeom2EndpointMass n (2 * n - d) =
      ndA6Gaussian (n : ℝ) (-(d : ℝ)) * ndA6CentralAmplitude n *
        Real.exp
          ((∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) +
            (d : ℝ) ^ 2 / (4 * (n : ℝ))) := by
  rw [ndGeom2EndpointMass_two_mul_sub_eq_center_mul_exp hn hdn]
  rw [ndGeom2EndpointMass_two_mul_eq_gaussian_zero_mul_centralAmplitude hn]
  rw [ndA6Gaussian_eq_zero_mul_exp (n := n) (-(d : ℝ))]
  rw [show (-((d : ℝ))) ^ 2 = (d : ℝ) ^ 2 by ring]
  have hexp : Real.exp (-((d : ℝ) ^ 2 / (4 * (n : ℝ)))) *
          Real.exp
            ((∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) +
              (d : ℝ) ^ 2 / (4 * (n : ℝ))) =
        Real.exp (∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

private theorem abs_mul_exp_sub_one_le
    {a e eta c : ℝ} (haPos : 0 < a) (haLeOne : a ≤ 1)
    (haError : |a - 1| ≤ c) (he : |e| ≤ eta) (heta : eta ≤ 1) :
    |a * Real.exp e - 1| ≤ c + 2 * eta := by
  have hetaNonneg : 0 ≤ eta := (abs_nonneg e).trans he
  have heOne : |e| ≤ 1 := he.trans heta
  have hExp : |Real.exp e - 1| ≤ 2 * eta :=
    (Real.abs_exp_sub_one_le heOne).trans (mul_le_mul_of_nonneg_left he (by norm_num))
  have hmul : a * |Real.exp e - 1| ≤ 2 * eta := by
    calc
      a * |Real.exp e - 1| ≤ 1 * (2 * eta) :=
        mul_le_mul haLeOne hExp (abs_nonneg _) (by norm_num)
      _ = 2 * eta := by ring
  calc
    |a * Real.exp e - 1| = |(a - 1) + a * (Real.exp e - 1)| := by
      congr 1
      ring
    _ ≤ |a - 1| + |a * (Real.exp e - 1)| := abs_add_le _ _
    _ = |a - 1| + a * |Real.exp e - 1| := by
      rw [abs_mul, abs_of_pos haPos]
    _ ≤ c + 2 * eta := add_le_add haError hmul

/-- Right-hand raw local limit, before recentering or summation. -/
theorem abs_ndGeom2EndpointMass_two_mul_add_sub_gaussian_le
    {n d : ℕ} (hn : 0 < n) (hd : 4 * d ≤ n)
    (heta : ndA6LocalEta n d ≤ 1) :
    |ndGeom2EndpointMass n (2 * n + d) -
        ndA6Gaussian (n : ℝ) (d : ℝ)| ≤
      ndA6Gaussian (n : ℝ) (d : ℝ) *
        ndA6LocalRelativeError n d := by
  let e : ℝ :=
    (∑ t ∈ Finset.range d, ndA6RightLogTerm n t) +
      (d : ℝ) ^ 2 / (4 * (n : ℝ))
  have he : |e| ≤ ndA6LocalEta n d := by
    simpa [e, ndA6LocalEta, ndA6RightLogTerm] using
      ndGeom2_rightLogProduct_cubic hn hd
  have hscalar :
      |ndA6CentralAmplitude n * Real.exp e - 1| ≤
        ndA6LocalRelativeError n d := by
    simpa [ndA6LocalRelativeError] using
      abs_mul_exp_sub_one_le (ndA6CentralAmplitude_pos hn)
        (ndA6CentralAmplitude_le_one hn)
        (abs_ndA6CentralAmplitude_sub_one_le hn) he heta
  rw [ndGeom2EndpointMass_two_mul_add_factorization hn]
  change
    |ndA6Gaussian (n : ℝ) (d : ℝ) *
          ndA6CentralAmplitude n * Real.exp e -
        ndA6Gaussian (n : ℝ) (d : ℝ)| ≤ _
  rw [show ndA6Gaussian (n : ℝ) (d : ℝ) *
        ndA6CentralAmplitude n * Real.exp e -
          ndA6Gaussian (n : ℝ) (d : ℝ) =
        ndA6Gaussian (n : ℝ) (d : ℝ) *
          (ndA6CentralAmplitude n * Real.exp e - 1) by ring]
  rw [abs_mul, abs_of_nonneg (ndA6Gaussian_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left hscalar (ndA6Gaussian_nonneg _ _)

/-- Left-hand raw local limit.  Its Gaussian argument remains visibly signed. -/
theorem abs_ndGeom2EndpointMass_two_mul_sub_sub_gaussian_le
    {n d : ℕ} (hn : 0 < n) (hd : 4 * d ≤ n)
    (heta : ndA6LocalEta n d ≤ 1) :
    |ndGeom2EndpointMass n (2 * n - d) -
        ndA6Gaussian (n : ℝ) (-(d : ℝ))| ≤
      ndA6Gaussian (n : ℝ) (-(d : ℝ)) *
        ndA6LocalRelativeError n d := by
  have hdn : d ≤ n := by omega
  let e : ℝ :=
    (∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) +
      (d : ℝ) ^ 2 / (4 * (n : ℝ))
  have he : |e| ≤ ndA6LocalEta n d := by
    simpa [e, ndA6LocalEta, ndA6LeftLogTerm] using
      ndGeom2_leftLogProduct_cubic hn hd
  have hscalar :
      |ndA6CentralAmplitude n * Real.exp e - 1| ≤
        ndA6LocalRelativeError n d := by
    simpa [ndA6LocalRelativeError] using
      abs_mul_exp_sub_one_le (ndA6CentralAmplitude_pos hn)
        (ndA6CentralAmplitude_le_one hn)
        (abs_ndA6CentralAmplitude_sub_one_le hn) he heta
  rw [ndGeom2EndpointMass_two_mul_sub_factorization hn hdn]
  change
    |ndA6Gaussian (n : ℝ) (-(d : ℝ)) *
          ndA6CentralAmplitude n * Real.exp e -
        ndA6Gaussian (n : ℝ) (-(d : ℝ))| ≤ _
  rw [show ndA6Gaussian (n : ℝ) (-(d : ℝ)) *
        ndA6CentralAmplitude n * Real.exp e -
          ndA6Gaussian (n : ℝ) (-(d : ℝ)) =
        ndA6Gaussian (n : ℝ) (-(d : ℝ)) *
          (ndA6CentralAmplitude n * Real.exp e - 1) by ring]
  rw [abs_mul, abs_of_nonneg (ndA6Gaussian_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left hscalar (ndA6Gaussian_nonneg _ _)

/-- Signed raw A6 local limit in endpoint coordinates.  The two hypotheses
on the natural displacement expose the exact small-window and exponential
interfaces used downstream. -/
theorem abs_ndGeom2EndpointMass_sub_gaussian_le
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L)
    (hd : 4 * ndGeom2CentralDisplacement n L ≤ n)
    (heta : ndA6LocalEta n (ndGeom2CentralDisplacement n L) ≤ 1) :
    |ndGeom2EndpointMass n L -
        ndA6Gaussian (n : ℝ) ((L : ℝ) - 2 * (n : ℝ))| ≤
      ndA6Gaussian (n : ℝ) ((L : ℝ) - 2 * (n : ℝ)) *
        ndA6LocalRelativeError n (ndGeom2CentralDisplacement n L) := by
  have _ := hL
  let d := ndGeom2CentralDisplacement n L
  change 4 * d ≤ n at hd
  change ndA6LocalEta n d ≤ 1 at heta
  have hdn : d ≤ n := by omega
  have hsplit := ndGeom2CentralDisplacement_split n L
  change 2 * n + d = L ∨ L + d = 2 * n at hsplit
  rcases hsplit with hright | hleft
  · rw [← hright]
    have hdisp : ndGeom2CentralDisplacement n (2 * n + d) = d := by
      rw [ndGeom2CentralDisplacement_eq_sub_of_two_mul_le (by omega)]
      omega
    rw [hdisp]
    convert abs_ndGeom2EndpointMass_two_mul_add_sub_gaussian_le hn hd heta using 1 <;>
      push_cast <;> ring
  · have hLe : L = 2 * n - d := by omega
    rw [hLe]
    have hd2n : d ≤ 2 * n := by omega
    have hdisp : ndGeom2CentralDisplacement n (2 * n - d) = d := by
      rw [ndGeom2CentralDisplacement_eq_sub_of_le_two_mul (Nat.sub_le _ _)]
      omega
    rw [hdisp]
    convert abs_ndGeom2EndpointMass_two_mul_sub_sub_gaussian_le hn hd heta using 1 <;>
      rw [Nat.cast_sub hd2n] <;> push_cast <;> ring

section Canaries

example (n : ℕ) : ndA6LocalEta n 0 = 0 := by
  simp [ndA6LocalEta]

example {n : ℕ} (hn : 0 < n) :
    ndGeom2EndpointMass n (2 * n + 1) =
      ndGeom2EndpointMass n (2 * n) * (n : ℝ) / ((n : ℝ) + 1) := by
  rw [show 2 * n + 1 = 2 * n + 1 by rfl]
  rw [ndGeom2EndpointMass_succ hn (by omega : n ≤ 2 * n)]
  rw [show 2 * n - n + 1 = n + 1 by omega]
  push_cast
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn1]

example {n : ℕ} (hn : 0 < n) :
    ndGeom2EndpointMass n (2 * n - 1) =
      ndGeom2EndpointMass n (2 * n) *
        (2 * (n : ℝ)) / (2 * (n : ℝ) - 1) := by
  rw [ndGeom2EndpointMass_eq_succ_mul hn (by omega : n ≤ 2 * n - 1)]
  rw [show 2 * n - 1 + 1 = 2 * n by omega]
  rw [show 2 * n - 1 - n + 1 = n by omega]
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
  push_cast
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 2 * (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hden]

example : ndA6LocalEta 8 1 = 9 / 4 := by
  norm_num [ndA6LocalEta]

example :
    |ndGeom2EndpointMass 64 129 - ndA6Gaussian 64 1| ≤
      ndA6Gaussian 64 1 * ndA6LocalRelativeError 64 1 := by
  have h := abs_ndGeom2EndpointMass_sub_gaussian_le
    (n := 64) (L := 129) (by norm_num) (by norm_num)
    (by norm_num [ndGeom2CentralDisplacement])
    (by norm_num [ndGeom2CentralDisplacement, ndA6LocalEta])
  norm_num [ndGeom2CentralDisplacement] at h
  exact h

example :
    |ndGeom2EndpointMass 64 127 - ndA6Gaussian 64 (-1)| ≤
      ndA6Gaussian 64 (-1) * ndA6LocalRelativeError 64 1 := by
  have h := abs_ndGeom2EndpointMass_sub_gaussian_le
    (n := 64) (L := 127) (by norm_num) (by norm_num)
    (by norm_num [ndGeom2CentralDisplacement])
    (by norm_num [ndGeom2CentralDisplacement, ndA6LocalEta])
  norm_num [ndGeom2CentralDisplacement] at h
  exact h

end Canaries

end

end ND
end Erdos1135
