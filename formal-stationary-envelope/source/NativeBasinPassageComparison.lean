import BasinIndicatorTransport

set_option autoImplicit false

namespace CollatzCanonical.NativeTao
open Erdos1135 CollatzCylinderPacking.Arithmetic

/-- Quantitative transport for the actual native real first-passage laws.
The good source event may be chosen independently of the target observable. -/
theorem native_real_windows_basin_comparison (b : ℝ)
    (_hbβ : CollatzCanonical.PackingParameters.beta < b) (_hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (x : ℝ) (hx : 1 ≤ x), (N : ℝ) ≤ x →
      ∀ (G : Set Tao.TaoOddNat),
      (∀ q ∈ G, ∃ n, Tao.syracuseFirstHitAtMostReal x q.1 n ∧
        N < (Tao.syracuse^[n]) q.1) →
      ∀ (lo₁ hi₁ lo₂ hi₂ : ℕ)
        (hmass₁ : 0 < Tao.logFinsetMass (Tao.oddLogWindow lo₁ hi₁))
        (hmass₂ : 0 < Tao.logFinsetMass (Tao.oddLogWindow lo₂ hi₂)),
      |Tao.pmfExpectation (Tao.oddLogWindowPMF lo₁ hi₁ hmass₁)
          (fun q => basinIndicator N q.1) -
        Tao.pmfExpectation (Tao.oddLogWindowPMF lo₂ hi₂ hmass₂)
          (fun q => basinIndicator N q.1)| ≤
        2 * C * x ^ (b - 1) +
        ((Tao.oddLogWindowOddNatPMF lo₁ hi₁ hmass₁).toOuterMeasure Gᶜ).toReal +
        ((Tao.oddLogWindowOddNatPMF lo₂ hi₂ hmass₂).toOuterMeasure Gᶜ).toReal +
        Tao.syracusePassRealFloorWindowTV x lo₁ hi₁ lo₂ hi₂ hx hmass₁ hmass₂ := by
  classical
  refine ⟨0, le_rfl, ?_⟩
  intro N x hx hN G hG lo₁ hi₁ lo₂ hi₂ hmass₁ hmass₂
  have hgood {lo hi : ℕ} (q : {n // n ∈ Tao.oddLogWindow lo hi})
      (hq : ¬¬Tao.oddLogWindowValueToOddNat q ∈ G) :
      GoodOddBarrierLanding q.1 (Tao.syracusePassLocationRealFloorOrOne x q.1 hx).1 N x := by
    obtain ⟨n, hfirst, hland⟩ := hG (Tao.oddLogWindowValueToOddNat q) (not_not.mp hq)
    change Tao.syracuseFirstHitAtMostReal x q.1 n at hfirst
    change N < (Tao.syracuse^[n]) q.1 at hland
    rw [native_real_passLocation_eq_of_first hx hfirst]
    exact native_real_first_passage_goodLanding (by linarith)
      (Tao.oddLogWindowValueToOddNat q).2 hfirst hland
  have he := native_basin_passage_expectation (Tao.oddLogWindowPMF lo₁ hi₁ hmass₁)
    (Tao.oddLogWindowPMF lo₂ hi₂ hmass₂) (fun q => q.1) (fun q => q.1)
    (fun q => Tao.syracusePassLocationRealFloorOrOne x q.1 hx)
    (fun q => Tao.syracusePassLocationRealFloorOrOne x q.1 hx)
    (fun q => q.1) (fun q => ¬Tao.oddLogWindowValueToOddNat q ∈ G)
    (fun q => ¬Tao.oddLogWindowValueToOddNat q ∈ G) N x hN hgood hgood
  rw [native_odd_source_bad_probability, native_odd_source_bad_probability] at he
  simpa only [mul_zero, zero_mul, zero_add] using he

#print axioms native_real_windows_basin_comparison

end CollatzCanonical.NativeTao
