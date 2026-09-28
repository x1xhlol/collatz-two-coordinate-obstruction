import NativeTaoProbabilityBridge
import NativeTaoArithmeticBridge
import Erdos1135.Tao.Probability.LogWindowResidue

set_option autoImplicit false

namespace CollatzCanonical.NativeTao

open Erdos1135 CollatzCylinderPacking.Arithmetic

theorem native_real_passLocation_eq_of_first {x : ℝ} {q n : ℕ} (hx : 1 ≤ x)
    (hfirst : Tao.syracuseFirstHitAtMostReal x q n) :
    (Tao.syracusePassLocationRealFloorOrOne x q hx).1 = (Tao.syracuse^[n]) q := by
  have hn := (Tao.syracuseFirstHitAtMostReal_iff_floor (by linarith : 0 ≤ x)).mp hfirst
  have hh : Tao.syracuseHitsAtMost q ⌊x⌋₊ := ⟨n, hn.1⟩
  have ht := Tao.syracuseFirstHitAtMost_unique
    (Tao.syracuseFirstHitAtMost_of_hitsAtMost q ⌊x⌋₊ hh) hn
  simp only [Tao.syracusePassLocationRealFloorOrOne, Tao.syracusePassLocationOrOne,
    Tao.syracusePassLocationAtMostOrOne_of_hitsAtMost _ hh, ht]

theorem native_odd_source_bad_probability {lo hi : ℕ}
    (hmass : 0 < Tao.logFinsetMass (Tao.oddLogWindow lo hi)) (G : Set Tao.TaoOddNat) :
    Tao.pmfProb (Tao.oddLogWindowPMF lo hi hmass)
      {q | ¬Tao.oddLogWindowValueToOddNat q ∈ G} =
      ((Tao.oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure Gᶜ).toReal := by
  rw [Tao.oddLogWindowOddNatPMF, PMF.toOuterMeasure_map_apply,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal]
  rfl

/-- Quantitative transport for the actual native real first-passage laws.
The good source event may be chosen independently of the target observable. -/
theorem native_real_windows_weight_comparison (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (x : ℝ) (hx : 1 ≤ x), (N : ℝ) ≤ x →
      ∀ (G : Set Tao.TaoOddNat),
      (∀ q ∈ G, ∃ n, Tao.syracuseFirstHitAtMostReal x q.1 n ∧
        N < (Tao.syracuse^[n]) q.1) →
      ∀ (lo₁ hi₁ lo₂ hi₂ : ℕ)
        (hmass₁ : 0 < Tao.logFinsetMass (Tao.oddLogWindow lo₁ hi₁))
        (hmass₂ : 0 < Tao.logFinsetMass (Tao.oddLogWindow lo₂ hi₂)),
      |Tao.pmfExpectation (Tao.oddLogWindowPMF lo₁ hi₁ hmass₁)
          (fun q => firstHitWeight N q.1) -
        Tao.pmfExpectation (Tao.oddLogWindowPMF lo₂ hi₂ hmass₂)
          (fun q => firstHitWeight N q.1)| ≤
        2 * C * x ^ (b - 1) +
        ((Tao.oddLogWindowOddNatPMF lo₁ hi₁ hmass₁).toOuterMeasure Gᶜ).toReal +
        ((Tao.oddLogWindowOddNatPMF lo₂ hi₂ hmass₂).toOuterMeasure Gᶜ).toReal +
        Tao.syracusePassRealFloorWindowTV x lo₁ hi₁ lo₂ hi₂ hx hmass₁ hmass₂ := by
  classical
  obtain ⟨C, hC, hbound⟩ := native_firstHitWeight_passage_expectation b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro N x hx hN G hG lo₁ hi₁ lo₂ hi₂ hmass₁ hmass₂
  have hpositive {lo hi : ℕ} (q : {n // n ∈ Tao.oddLogWindow lo hi}) : 0 < q.1 := by
    have ho := (Tao.oddLogWindow_mem.mp q.2).2.2
    omega
  have hgood {lo hi : ℕ} (q : {n // n ∈ Tao.oddLogWindow lo hi})
      (hq : ¬¬Tao.oddLogWindowValueToOddNat q ∈ G) :
      GoodOddBarrierLanding q.1 (Tao.syracusePassLocationRealFloorOrOne x q.1 hx).1 N x := by
    obtain ⟨n, hfirst, hland⟩ := hG (Tao.oddLogWindowValueToOddNat q) (not_not.mp hq)
    change Tao.syracuseFirstHitAtMostReal x q.1 n at hfirst
    change N < (Tao.syracuse^[n]) q.1 at hland
    rw [native_real_passLocation_eq_of_first hx hfirst]
    exact native_real_first_passage_goodLanding (by linarith)
      (Tao.oddLogWindowValueToOddNat q).2 hfirst hland
  have he := hbound (Tao.oddLogWindowPMF lo₁ hi₁ hmass₁)
    (Tao.oddLogWindowPMF lo₂ hi₂ hmass₂) (fun q => q.1) (fun q => q.1)
    (fun q => Tao.syracusePassLocationRealFloorOrOne x q.1 hx)
    (fun q => Tao.syracusePassLocationRealFloorOrOne x q.1 hx)
    (fun q => q.1) (fun q => ¬Tao.oddLogWindowValueToOddNat q ∈ G)
    (fun q => ¬Tao.oddLogWindowValueToOddNat q ∈ G) N x hpositive hpositive
    hx hN hgood hgood
  rw [native_odd_source_bad_probability, native_odd_source_bad_probability] at he
  exact he

#print axioms native_real_passLocation_eq_of_first
#print axioms native_real_windows_weight_comparison

end CollatzCanonical.NativeTao
