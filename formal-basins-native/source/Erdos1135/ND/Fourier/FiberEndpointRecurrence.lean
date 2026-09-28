import Erdos1135.ND.Fourier.FiberEndpointFloor

/-!
# Cross-Length Endpoint Recurrences

This neutral leaf records the two exact negative-binomial endpoint ratios
consumed by A5 X.4.  They change both the number of Geom(2) variables and the
endpoint total; no A5 tube, phase, or normalization is introduced here.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Adding one Geom(2) variable and one unit of endpoint total has the exact
source ratio `L/(2*nu)`. -/
theorem ndGeom2EndpointMass_succ_length_one
    {nu L : ℕ} (hnu : 0 < nu) (hL : nu ≤ L) :
    ndGeom2EndpointMass (nu + 1) (L + 1) =
      ndGeom2EndpointMass nu L * (L : ℝ) / (2 * (nu : ℝ)) := by
  rw [ndGeom2EndpointMass_eq_choose_mul_pow (by omega : 0 < nu + 1)
      (by omega : nu + 1 ≤ L + 1),
    ndGeom2EndpointMass_eq_choose_mul_pow hnu hL]
  rw [show L + 1 - 1 = L by omega, show nu + 1 - 1 = nu by omega,
    pow_succ]
  have hchooseNat := Nat.add_one_mul_choose_eq (L - 1) (nu - 1)
  rw [show L - 1 + 1 = L by omega,
    show nu - 1 + 1 = nu by omega] at hchooseNat
  have hchoose := congrArg (fun m : ℕ => (m : ℝ)) hchooseNat
  push_cast at hchoose
  have hnuReal : (nu : ℝ) ≠ 0 := by positivity
  calc
    (Nat.choose L nu : ℝ) *
          ((1 / 2 : ℝ) ^ L * (1 / 2 : ℝ)) =
        (((Nat.choose L nu : ℝ) * (nu : ℝ)) *
          (1 / 2 : ℝ) ^ L) / (2 * (nu : ℝ)) := by
      field_simp [hnuReal]
    _ = (((L : ℝ) * (Nat.choose (L - 1) (nu - 1) : ℝ)) *
          (1 / 2 : ℝ) ^ L) / (2 * (nu : ℝ)) := by
      rw [hchoose]
    _ = (Nat.choose (L - 1) (nu - 1) : ℝ) *
          (1 / 2 : ℝ) ^ L * (L : ℝ) / (2 * (nu : ℝ)) := by
      ring

/-- Adding one Geom(2) variable and two units of endpoint total has the exact
second A5 ratio.  The natural subtraction in the denominator is guarded by
`nu ≤ L`, so it cannot clip. -/
theorem ndGeom2EndpointMass_succ_length_two
    {nu L : ℕ} (hnu : 0 < nu) (hL : nu ≤ L) :
    ndGeom2EndpointMass (nu + 1) (L + 2) =
      ndGeom2EndpointMass nu L *
        (((L : ℝ) * ((L + 1 : ℕ) : ℝ)) /
          (4 * (nu : ℝ) * ((L + 1 - nu : ℕ) : ℝ))) := by
  have hstep := ndGeom2EndpointMass_succ
    (n := nu + 1) (L := L + 1) (by omega : 0 < nu + 1)
    (by omega : nu + 1 ≤ L + 1)
  have hfirst := ndGeom2EndpointMass_succ_length_one hnu hL
  calc
    ndGeom2EndpointMass (nu + 1) (L + 2) =
        ndGeom2EndpointMass (nu + 1) ((L + 1) + 1) := by
      congr 2
    _ = ndGeom2EndpointMass (nu + 1) (L + 1) *
          ((L + 1 : ℕ) : ℝ) /
            (2 * (((L + 1) - (nu + 1) + 1 : ℕ) : ℝ)) := hstep
    _ = ndGeom2EndpointMass nu L *
        (((L : ℝ) * ((L + 1 : ℕ) : ℝ)) /
          (4 * (nu : ℝ) * ((L + 1 - nu : ℕ) : ℝ))) := by
      rw [hfirst, show L + 1 - (nu + 1) + 1 = L + 1 - nu by omega]
      ring

end

end ND
end Erdos1135
