import TrapMicrocanonicalDeficit

/-! Superpolynomial decay on every conditional slice with a polynomial mass floor. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_polynomial_deficit_scalar
    (A B M : ℕ) (beta x y p : ℝ) (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hbeta : 0 ≤ beta) (hdegree : (beta - 1) * M + B + A ≤ 0)
    (hybound : y ≤ x ^ beta) (hp : 1 / x ^ B ≤ p) :
    ((y + 2) / (x + y)) ^ M / p ≤ 3 ^ M / x ^ A := by
  have hxpos : 0 < x := by linarith
  have hppos : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hxbeta : 1 ≤ x ^ beta := Real.one_le_rpow hx hbeta
  have hratio : (y + 2) / (x + y) ≤ 3 * x ^ (beta - 1) := by
    calc
      (y + 2) / (x + y) ≤ (y + 2) / x :=
        div_le_div_of_nonneg_left (by linarith) hxpos (by linarith)
      _ ≤ (3 * x ^ beta) / x :=
        div_le_div_of_nonneg_right (by linarith) hxpos.le
      _ = 3 * x ^ (beta - 1) := by rw [Real.rpow_sub hxpos, Real.rpow_one]; ring
  have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ (y + 2) / (x + y)) hratio M
  have hcombine : (x ^ (beta - 1)) ^ M * x ^ B * x ^ A =
      x ^ ((beta - 1) * M + B + A) := by
    rw [← Real.rpow_natCast (x ^ (beta - 1)), ← Real.rpow_mul hxpos.le,
      ← Real.rpow_natCast x B, ← Real.rpow_natCast x A,
      ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
  have hsmall : (x ^ (beta - 1)) ^ M * x ^ B ≤ 1 / x ^ A := by
    apply (le_div_iff₀ (by positivity : 0 < x ^ A)).mpr
    rw [hcombine]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx hdegree
  calc
    ((y + 2) / (x + y)) ^ M / p ≤
        (3 * x ^ (beta - 1)) ^ M / (1 / x ^ B) :=
      div_le_div₀ (by positivity) hpower (by positivity) hp
    _ = 3 ^ M * ((x ^ (beta - 1)) ^ M * x ^ B) := by rw [mul_pow]; field_simp
    _ ≤ 3 ^ M * (1 / x ^ A) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = 3 ^ M / x ^ A := by ring

theorem trap_unconditional_conditionedAffinePMF_polynomial_deficit_mass_floor
    (A B : ℕ) (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ k d : ℕ, 1 ≤ k → (d : ℝ) ≤ (k : ℝ) ^ beta →
      ∀ xi : ZMod (3 ^ (k + d)), zmodThreePrimitive (k + d) xi →
        ∀ z : ZMod (3 ^ (k + d)), ∀ s : ℕ,
          ∀ hs : 0 < unitSourceExponentMass k s,
            1 / (k : ℝ) ^ B ≤ unitSourceExponentMass k s →
              ‖ZMod.dft (pmfComplexMass
                (unitSourceConditionedAffinePMF (k + d) k s z hs)) xi‖ ≤
                  C / (k : ℝ) ^ A := by
  obtain ⟨M, hM⟩ := exists_nat_ge (((A : ℝ) + B) / (1 - beta))
  have hdegree : (beta - 1) * (M : ℝ) + B + A ≤ 0 := by
    have hm := (div_le_iff₀ (by linarith : 0 < 1 - beta)).mp hM
    nlinarith
  obtain ⟨C, hC, hbound⟩ := trap_unconditional_conditionedAffinePMF_deficit_all_powers M
  refine ⟨C * 3 ^ M, by positivity, ?_⟩
  intro k d hk hd xi hxi z s hs hp
  have hscalar := trap_polynomial_deficit_scalar A B M beta k d
    (unitSourceExponentMass k s) (by exact_mod_cast hk) (by positivity)
    hbeta0.le hdegree hd hp
  have hb := hbound (k + d) k (by omega) (by omega) xi hxi z s hs
  have hsub : k + d - k + 2 = d + 2 := by omega
  rw [hsub] at hb
  push_cast at hb
  calc
    ‖ZMod.dft (pmfComplexMass
      (unitSourceConditionedAffinePMF (k + d) k s z hs)) xi‖ ≤
        C * (((d : ℝ) + 2) / ((k : ℝ) + d)) ^ M / unitSourceExponentMass k s := hb
    _ = C * ((((d : ℝ) + 2) / ((k : ℝ) + d)) ^ M / unitSourceExponentMass k s) := by ring
    _ ≤ C * (3 ^ M / (k : ℝ) ^ A) := mul_le_mul_of_nonneg_left hscalar hC.le
    _ = C * 3 ^ M / (k : ℝ) ^ A := by ring

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_unconditional_conditionedAffinePMF_polynomial_deficit_mass_floor
