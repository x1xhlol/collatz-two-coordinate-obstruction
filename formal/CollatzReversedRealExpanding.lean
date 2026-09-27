import CollatzReversedRealExpandingGrowth
import ReversedPositivePrefixArithmetic

namespace CollatzResearch.RealExpanding

open Matrix CollatzCertificate RealAffine

set_option maxHeartbeats 1000000

theorem positive_prefix_expanding_contradiction (A B C D E F G : Affine (Fin 2))
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (u : Vec (Fin 2)) (l m c : ℝ) (p : ℕ)
    (hu : ∀ i, 0<u i) (hl : 1<l) (hml : m≤l) (hc : 0<c)
    (hAu : A.matrix *ᵥ u=l • u)
    (hEu : E.matrix *ᵥ u=m • u) (hFu : F.matrix *ᵥ u=m • u)
    (hGu : G.matrix *ᵥ u=m • u)
    (hp4 : 4≤p) (hp7 : p≤7)
    (hprefix : c • u≤ReversedCertificate.binaryInterp (eval A) (eval B) p C.offset) :
    False := by
  obtain ⟨K,M,hK,hM,hinit,hEoff,hFoff,hGoff⟩ :=
    RealExpandingGrowth.ternary_uniform_ray_bounds C E F G u hu
  have hEmat : E.matrix *ᵥ u≤l • u := by
    rw [hEu]
    intro i
    exact mul_le_mul_of_nonneg_right hml (hu i).le
  have hFmat : F.matrix *ᵥ u≤l • u := by
    rw [hFu]
    intro i
    exact mul_le_mul_of_nonneg_right hml (hu i).le
  have hGmat : G.matrix *ᵥ u≤l • u := by
    rw [hGu]
    intro i
    exact mul_le_mul_of_nonneg_right hml (hu i).le
  apply PositivePrefixArithmetic.exponential_not_bounded_by_affine c l
    (l^2*(K+2*M)) (2*l^2*M) hc hl
  intro n
  obtain ⟨L,hlo,hhi,hL⟩ := PositivePrefixArithmetic.prefix_power_window p n hp4 hp7
  have hb := RealExpandingGrowth.binary_prefix_exponential_lower A B C.offset u l c p
    hA hAu (by omega) hprefix L
  have ht := RealExpandingBounds.ternary_window_upper_bound A B C D E F G
    hA hB hC hE hF hG h u l K M (fun i => (hu i).le) hl.le hK hM hinit
    hEmat hFmat hGmat hEoff hFoff hGoff (2*(n+1)) (p*2^L) hlo hhi
  have hh := le_trans hb ht 0
  change c*l^L*u 0≤((K+((2*(n+1):ℕ):ℝ)*M)*l^(2*(n+1)))*u 0 at hh
  have hs := (mul_le_mul_iff_left₀ (hu 0)).mp hh
  have hexp : l^(3*n)≤l^L := pow_le_pow_right₀ hl.le hL
  have hcompare : c*l^(3*n)≤(K+((2*(n+1):ℕ):ℝ)*M)*l^(2*(n+1)) :=
    le_trans (mul_le_mul_of_nonneg_left hexp hc.le) hs
  have he3 : 3*n=n+2*n := by omega
  have he2 : 2*(n+1)=2+2*n := by omega
  have hcancel : c*l^n≤l^2*(K+2*((n:ℝ)+1)*M) := by
    apply (mul_le_mul_iff_left₀ (pow_pos (lt_trans zero_lt_one hl) (2*n))).mp
    calc
      (c*l^n)*l^(2*n)=c*l^(3*n) := by rw [he3,pow_add]; ring
      _≤(K+((2*(n+1):ℕ):ℝ)*M)*l^(2*(n+1)) := hcompare
      _=(l^2*(K+2*((n:ℝ)+1)*M))*l^(2*n) := by
        rw [he2,pow_add]
        push_cast
        ring
  convert hcancel using 1
  ring

end CollatzResearch.RealExpanding

#print axioms CollatzResearch.RealExpanding.positive_prefix_expanding_contradiction
