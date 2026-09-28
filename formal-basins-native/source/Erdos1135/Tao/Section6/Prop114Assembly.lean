import Erdos1135.Tao.Section6.HighRegimeAllScale
import Erdos1135.Tao.Section6.GlobalOscillationBound
import Erdos1135.Tao.Section6.Prop117ToProp114

/-!
# Natural-Exponent Proposition 1.14 Assembly

This leaf absorbs the bounded lower scales once, proves the direct implication
from Proposition 1.17 to the current natural-exponent Proposition 1.14 surface,
and inhabits the legacy two-premise bridge for compatibility.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- An eventual lower-scale inverse-power bound extends to every positive
lower scale after one use of the global oscillation bound. -/
theorem syracFineScaleMixingAt_of_large_and_global
    {A M0 : ℕ} {C : ℝ}
    (hlarge : ∀ n m : ℕ, M0 ≤ m → m ≤ n →
      syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A) :
    syracFineScaleMixingAt A
      (max C (2 * (M0 : ℝ) ^ A)) := by
  intro n m hm hmn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : 0 < (m : ℝ) ^ A := pow_pos hmR A
  by_cases hcut : M0 ≤ m
  · exact (hlarge n m hcut hmn).trans
      (div_le_div_of_nonneg_right
        (le_max_left C (2 * (M0 : ℝ) ^ A)) hden.le)
  · have hmM0 : m ≤ M0 := (Nat.lt_of_not_ge hcut).le
    have hmM0R : (m : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hmM0
    have hpow : (m : ℝ) ^ A ≤ (M0 : ℝ) ^ A :=
      pow_le_pow_left₀ (Nat.cast_nonneg m) hmM0R A
    have hscaled : 2 * (m : ℝ) ^ A ≤ 2 * (M0 : ℝ) ^ A :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    exact (syracFineScaleOscillation_le_two hmn).trans <|
      (le_div_iff₀ hden).2 <|
        hscaled.trans (le_max_right C (2 * (M0 : ℝ) ^ A))

/-- The checked Section 6 chain gives the current positive-natural-exponent
Proposition 1.14 statement directly from Proposition 1.17. -/
theorem TaoProp117PrimitivePolynomialDecayStatement.to_prop114
    (h117 : TaoProp117PrimitivePolynomialDecayStatement) :
    TaoProp114FineScaleMixingStatement := by
  intro A hA
  obtain ⟨C, hC, M0, _hM0, hlarge⟩ :=
    h117.exists_syracFineScaleOscillation_le_allScale_large A hA
  refine ⟨max C (2 * (M0 : ℝ) ^ A), ?_, ?_⟩
  · exact hC.trans (le_max_left _ _)
  · exact syracFineScaleMixingAt_of_large_and_global hlarge

/-- The old explicit Corollary 6.3 premise is retained only as a compatibility
argument; its checked result is already consumed inside the Section 6 chain. -/
theorem taoSection6Prop117ToProp114 :
    TaoSection6Prop117ToProp114Statement :=
  fun h117 _hcor63 => h117.to_prop114

/-- Large-branch boundary canary at `m=M0`. -/
theorem syracFineScaleMixingAt_of_large_and_global_cutoff
    {A M0 : ℕ} {C : ℝ} (hM0 : 1 ≤ M0)
    (hlarge : ∀ n m : ℕ, M0 ≤ m → m ≤ n →
      syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A) :
    syracFineScaleOscillation M0 M0 ≤
      max C (2 * (M0 : ℝ) ^ A) / (M0 : ℝ) ^ A :=
  (syracFineScaleMixingAt_of_large_and_global hlarge).apply
    hM0 (le_refl M0)

/-- Low-branch canary with a nontrivial denominator. -/
theorem syracFineScaleMixingAt_of_large_and_global_nine
    {A : ℕ} {C : ℝ}
    (hlarge : ∀ n m : ℕ, 10 ≤ m → m ≤ n →
      syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A)
    {n : ℕ} (hn : 9 ≤ n) :
    syracFineScaleOscillation 9 n ≤
      max C (2 * (10 : ℝ) ^ A) / (9 : ℝ) ^ A :=
  (syracFineScaleMixingAt_of_large_and_global hlarge).apply
    (by omega) hn

/-- Lowest public lower-scale canary. -/
theorem syracFineScaleMixingAt_of_large_and_global_one
    {A M0 : ℕ} {C : ℝ}
    (hlarge : ∀ n m : ℕ, M0 ≤ m → m ≤ n →
      syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A)
    {n : ℕ} (hn : 1 ≤ n) :
    syracFineScaleOscillation 1 n ≤
      max C (2 * (M0 : ℝ) ^ A) := by
  simpa using
    (syracFineScaleMixingAt_of_large_and_global hlarge).apply
      (m := 1) (n := n) (by omega) hn

/-- Exponent-one Proposition 1.17 specialization. -/
theorem TaoProp117PrimitivePolynomialDecayStatement.exists_syracFineScaleMixingAt_one
    (h117 : TaoProp117PrimitivePolynomialDecayStatement) :
    ∃ C : ℝ, 0 ≤ C ∧ syracFineScaleMixingAt 1 C :=
  h117.to_prop114 1 (by omega)

/-- Compatibility-bridge application canary. -/
theorem taoSection6Prop117ToProp114_apply
    (h117 : TaoProp117PrimitivePolynomialDecayStatement)
    (hcor63 : TaoCor63StarSourceResidueSeparationStatement) :
    TaoProp114FineScaleMixingStatement :=
  taoSection6Prop117ToProp114 h117 hcor63

end

end Tao
end Erdos1135
