import CollatzReversedRealExpandingBounds

namespace CollatzResearch.RealExpandingGrowth

open Matrix CollatzCertificate RealAffine

set_option maxHeartbeats 1000000

theorem binaryInterp_times_pow_two {α : Type*} (a b : α → α) (p k : ℕ)
    (hp : 0<p) (x : α) :
    ReversedCertificate.binaryInterp a b (p*2^k) x=
      a^[k] (ReversedCertificate.binaryInterp a b p x) := by
  induction k with
  | zero => simp only [pow_zero,mul_one,Function.iterate_zero,Function.id_def]
  | succ k ih =>
    have he : p*2^(k+1)=2*(p*2^k) := by rw [pow_succ]; ring
    rw [he,ReversedCertificate.binaryInterp_even a b (mul_pos hp (pow_pos (by decide) k)),
      ih,Function.iterate_succ_apply']

theorem binary_prefix_exponential_lower (A B : Affine (Fin 2))
    (γ u : Vec (Fin 2)) (l c : ℝ) (p : ℕ)
    (hA : A.Nonnegative) (hAu : A.matrix *ᵥ u=l • u) (hp : 0<p)
    (hprefix : c • u≤ReversedCertificate.binaryInterp (eval A) (eval B) p γ)
    (k : ℕ) :
    (c*l^k) • u≤ReversedCertificate.binaryInterp (eval A) (eval B) (p*2^k) γ := by
  induction k with
  | zero => simpa only [pow_zero,mul_one] using hprefix
  | succ k ih =>
    have he : p*2^(k+1)=2*(p*2^k) := by rw [pow_succ]; ring
    rw [he,ReversedCertificate.binaryInterp_even (eval A) (eval B)
      (mul_pos hp (pow_pos (by decide) k))]
    apply le_trans _ (eval_monotone hA.1 ih)
    intro i
    have ho : 0≤A.offset i := hA.2 i
    simp only [eval,Matrix.mulVec_smul,hAu,Pi.add_apply,Pi.smul_apply,smul_eq_mul,pow_succ]
    nlinarith only [ho]

theorem ternary_uniform_ray_bounds (C E F G : Affine (Fin 2))
    (u : Vec (Fin 2)) (hu : ∀ i, 0<u i) :
    ∃ K M : ℝ, 0≤K ∧ 0≤M ∧ C.offset≤K • u ∧
      E.offset≤M • u ∧ F.offset≤M • u ∧ G.offset≤M • u := by
  obtain ⟨K,hK,hC⟩ := RealExpandingBounds.vector_bounded_by_positive_ray C.offset u hu
  obtain ⟨a,ha,hE⟩ := RealExpandingBounds.vector_bounded_by_positive_ray E.offset u hu
  obtain ⟨b,hb,hF⟩ := RealExpandingBounds.vector_bounded_by_positive_ray F.offset u hu
  obtain ⟨c,hc,hG⟩ := RealExpandingBounds.vector_bounded_by_positive_ray G.offset u hu
  refine ⟨K,a+b+c,hK,by positivity,hC,?_,?_,?_⟩
  · apply le_trans hE
    intro i
    exact mul_le_mul_of_nonneg_right (by linarith only [hb,hc]) (hu i).le
  · apply le_trans hF
    intro i
    exact mul_le_mul_of_nonneg_right (by linarith only [ha,hc]) (hu i).le
  · apply le_trans hG
    intro i
    exact mul_le_mul_of_nonneg_right (by linarith only [ha,hb]) (hu i).le

end CollatzResearch.RealExpandingGrowth

#print axioms CollatzResearch.RealExpandingGrowth.binaryInterp_times_pow_two
#print axioms CollatzResearch.RealExpandingGrowth.binary_prefix_exponential_lower
#print axioms CollatzResearch.RealExpandingGrowth.ternary_uniform_ray_bounds
