import CollatzReversedRealTriangularPrefix
import ReversedTriangularGrowthArithmetic

namespace CollatzResearch.RealTriangularGrowth

open Matrix CollatzCertificate RealAffine

theorem first_coordinate_expanding_contradiction
    (A B C D E F G : Affine (Fin 2))
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (u : Vec (Fin 2)) (lam L c : ℝ) (p : ℕ)
    (hu : ∀ i, 0<u i) (hu0 : u 0=1) (hlam : 1<lam) (hL : 1≤L)
    (hgap : L^2<lam^3) (hA00 : A.matrix 0 0=lam)
    (hEmat : E.matrix *ᵥ u≤L • u) (hFmat : F.matrix *ᵥ u≤L • u)
    (hGmat : G.matrix *ᵥ u≤L • u)
    (hp4 : 4≤p) (hp7 : p≤7)
    (hprefix : 0≤ReversedCertificate.binaryInterp (eval A) (eval B) p C.offset)
    (hc : 0<c) (hclower : c≤ReversedCertificate.binaryInterp (eval A) (eval B) p C.offset 0) :
    False := by
  obtain ⟨K,M,hK,hM,hinit,hEoff,hFoff,hGoff⟩ :=
    RealExpandingGrowth.ternary_uniform_ray_bounds C E F G u hu
  apply TriangularGrowthArithmetic.window_growth_contradiction c K M lam L hc hL hgap
  intro n
  obtain ⟨k,hlo,hhi,hk⟩ := PositivePrefixArithmetic.prefix_power_window p n hp4 hp7
  have hlower := RealTriangularPrefix.first_coordinate_binary_prefix_lower A B C.offset lam c p
    hA (by omega) (le_trans zero_le_one hlam.le) hA00 hprefix hclower k
  have hupper := RealExpandingBounds.ternary_window_upper_bound A B C D E F G
    hA hB hC hE hF hG h u L K M (fun i => (hu i).le) hL hK hM hinit
    hEmat hFmat hGmat hEoff hFoff hGoff (2*(n+1)) (p*2^k) hlo hhi
  have hupper0 := hupper 0
  change ReversedCertificate.binaryInterp (eval A) (eval B) (p*2^k) C.offset 0≤
    ((K+((2*(n+1):ℕ):ℝ)*M)*L^(2*(n+1)))*u 0 at hupper0
  rw [hu0,mul_one] at hupper0
  have hpow : lam^(3*n)≤lam^k := pow_le_pow_right₀ hlam.le hk
  exact le_trans (mul_le_mul_of_nonneg_left hpow hc.le) (le_trans hlower hupper0)

end CollatzResearch.RealTriangularGrowth

#print axioms CollatzResearch.RealTriangularGrowth.first_coordinate_expanding_contradiction
