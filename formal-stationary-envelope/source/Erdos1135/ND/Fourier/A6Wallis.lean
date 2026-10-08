import Erdos1135.ND.Fourier.FiberEndpointFloor
import Mathlib.Analysis.Real.Pi.Wallis

/-!
# A6 Finite Wallis Center

This leaf proves the finite central normalization needed after the signed A6
log-product estimates.  Its primary identities are division-free, and it
stops before endpoint products, exponentiation, or any Gaussian comparison.
-/

namespace Erdos1135
namespace ND

/-- The central endpoint mass normalized by the Gaussian peak scale. -/
noncomputable def ndA6CentralAmplitude (n : ℕ) : ℝ :=
  Real.sqrt (4 * Real.pi * (n : ℝ)) *
    ndGeom2EndpointMass n (2 * n)

/-- The central binomial coefficient and finite Wallis product satisfy an
exact division-free square identity.  This includes `n = 0`. -/
theorem centralBinom_sq_mul_wallis (n : ℕ) :
    (Nat.centralBinom n : ℝ) ^ 2 *
        ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)) =
      ((4 : ℝ) ^ n) ^ 2 := by
  rw [Real.Wallis.W_eq_factorial_ratio]
  have hfacNat := Nat.add_choose_mul_factorial_mul_factorial n n
  have hfacReal := congrArg (fun m : ℕ => (m : ℝ)) hfacNat
  push_cast at hfacReal
  rw [show n + n = 2 * n by omega] at hfacReal
  have hfacSq := congrArg (fun x : ℝ => x ^ 2) hfacReal
  have hpow : (2 : ℝ) ^ (4 * n) = ((4 : ℝ) ^ n) ^ 2 := by
    calc
      (2 : ℝ) ^ (4 * n) = ((2 : ℝ) ^ 4) ^ n := by rw [pow_mul]
      _ = ((4 : ℝ) ^ 2) ^ n := by norm_num
      _ = (4 : ℝ) ^ (2 * n) := by rw [pow_mul]
      _ = ((4 : ℝ) ^ n) ^ 2 := by
        rw [pow_two, ← pow_add]
        congr 1
        omega
  unfold Nat.centralBinom
  field_simp
  push_cast
  rw [hpow]
  ring_nf at hfacSq ⊢
  rw [hfacSq]

/-- The central amplitude is positive at positive length. -/
theorem ndA6CentralAmplitude_pos {n : ℕ} (hn : 0 < n) :
    0 < ndA6CentralAmplitude n := by
  unfold ndA6CentralAmplitude
  exact mul_pos (Real.sqrt_pos.2 (by positivity))
    (ndGeom2EndpointMass_pos hn (by omega))

/-- After central endpoint normalization, the exact Wallis identity has the
Gaussian factor `pi*n` on the right. -/
theorem ndA6CentralAmplitude_sq_mul_wallis
    {n : ℕ} (hn : 0 < n) :
    ndA6CentralAmplitude n ^ 2 *
        ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)) =
      Real.pi * (n : ℝ) := by
  unfold ndA6CentralAmplitude
  rw [ndGeom2EndpointMass_two_mul_eq_centralBinom_div hn]
  rw [mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 4 * Real.pi * (n : ℝ))]
  have hcb := centralBinom_sq_mul_wallis n
  have hpow : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  field_simp [hpow.ne']
  nlinarith [hcb]

/-- Quotient form of the exact amplitude-square identity. -/
theorem ndA6CentralAmplitude_sq_eq
    {n : ℕ} (hn : 0 < n) :
    ndA6CentralAmplitude n ^ 2 =
      Real.pi * (n : ℝ) /
        ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)) := by
  rw [eq_div_iff (mul_ne_zero (by positivity) (Real.Wallis.W_pos n).ne')]
  exact ndA6CentralAmplitude_sq_mul_wallis hn

/-- The upper Wallis bound gives the lower finite amplitude-square bound. -/
theorem two_mul_div_le_ndA6CentralAmplitude_sq
    {n : ℕ} (hn : 0 < n) :
    2 * (n : ℝ) / (((2 * n + 1 : ℕ) : ℝ)) ≤
      ndA6CentralAmplitude n ^ 2 := by
  rw [ndA6CentralAmplitude_sq_eq hn]
  have hD : 0 < (((2 * n + 1 : ℕ) : ℝ)) := by positivity
  have hDW :
      0 < (((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n) :=
    mul_pos hD (Real.Wallis.W_pos n)
  apply (div_le_div_iff₀ hD hDW).2
  calc
    2 * (n : ℝ) *
        ((((2 * n + 1 : ℕ) : ℝ)) * Real.Wallis.W n) =
        (2 * (n : ℝ) * (((2 * n + 1 : ℕ) : ℝ))) *
          Real.Wallis.W n := by ring
    _ ≤ (2 * (n : ℝ) * (((2 * n + 1 : ℕ) : ℝ))) *
          (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left (Real.Wallis.W_le n) (by positivity)
    _ = Real.pi * (n : ℝ) * (((2 * n + 1 : ℕ) : ℝ)) := by ring

/-- The lower Wallis bound gives the upper finite amplitude-square bound. -/
theorem ndA6CentralAmplitude_sq_le_four_mul
    {n : ℕ} (hn : 0 < n) :
    ndA6CentralAmplitude n ^ 2 ≤
      4 * (n : ℝ) * ((n : ℝ) + 1) /
        (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
  rw [ndA6CentralAmplitude_sq_eq hn]
  have hD : 0 < (((2 * n + 1 : ℕ) : ℝ)) := by positivity
  have hDW :
      0 < (((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n) :=
    mul_pos hD (Real.Wallis.W_pos n)
  have hDsq : 0 < (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  apply (div_le_div_iff₀ hDW hDsq).2
  let K : ℝ :=
    4 * (n : ℝ) * ((n : ℝ) + 1) * (((2 * n + 1 : ℕ) : ℝ))
  calc
    Real.pi * (n : ℝ) * (((2 * n + 1 : ℕ) : ℝ) ^ 2) =
        K * ((((2 : ℝ) * n + 1) / (2 * n + 2)) *
          (Real.pi / 2)) := by
      dsimp [K]
      push_cast
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hn1]
      ring
    _ ≤ K * Real.Wallis.W n := by
      exact mul_le_mul_of_nonneg_left (Real.Wallis.le_W n) (by
        dsimp [K]
        positivity)
    _ = 4 * (n : ℝ) * ((n : ℝ) + 1) *
        ((((2 * n + 1 : ℕ) : ℝ)) * Real.Wallis.W n) := by
      dsimp [K]
      push_cast
      ring

/-- The finite Wallis packet gives a central relative error of at most
`1/(2*n+1)`.  The proof is algebraic after the square bounds. -/
theorem abs_ndA6CentralAmplitude_sub_one_le
    {n : ℕ} (hn : 0 < n) :
    |ndA6CentralAmplitude n - 1| ≤
      1 / (((2 * n + 1 : ℕ) : ℝ)) := by
  let a : ℝ := ndA6CentralAmplitude n
  let D : ℝ := (((2 * n + 1 : ℕ) : ℝ))
  have haPos : 0 < a := by
    dsimp [a]
    exact ndA6CentralAmplitude_pos hn
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hlow : 2 * (n : ℝ) / D ≤ a ^ 2 := by
    simpa only [a, D] using two_mul_div_le_ndA6CentralAmplitude_sq hn
  have hupp : a ^ 2 ≤
      4 * (n : ℝ) * ((n : ℝ) + 1) / D ^ 2 := by
    simpa only [a, D] using ndA6CentralAmplitude_sq_le_four_mul hn
  have hfractionLeOne :
      4 * (n : ℝ) * ((n : ℝ) + 1) / D ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hD)]
    dsimp [D]
    push_cast
    nlinarith
  have haSqLeOne : a ^ 2 ≤ 1 := hupp.trans hfractionLeOne
  have haLeOne : a ≤ 1 := by nlinarith
  have haSqLeA : a ^ 2 ≤ a := by nlinarith
  have hrewrite : 1 - 1 / D = 2 * (n : ℝ) / D := by
    dsimp [D]
    push_cast
    field_simp
    ring
  have haLower : 1 - 1 / D ≤ a := by
    rw [hrewrite]
    exact hlow.trans haSqLeA
  rw [abs_of_nonpos (sub_nonpos.mpr haLeOne)]
  linarith

end ND
end Erdos1135
