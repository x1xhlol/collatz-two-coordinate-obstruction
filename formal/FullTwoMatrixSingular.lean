import FullTwoMatrixSingularSupport
import FullTwoMatrixStationary

namespace CollatzCertificate.FullTwoMatrix

open Matrix TwoDimensionalMiddleRank

local notation "tr₂" => TwoDimensionalSwapAlgebra.tr

theorem singular_middle_contradiction (A B C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hC : EntrywiseLE 0 C)
    (hD : EntrywiseLE 0 D) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hA₀ : 1 ≤ A 0 0) (hB₀ : 1 ≤ B 0 0) (hC₀ : 1 ≤ C 0 0)
    (hD₀ : 1 ≤ D 0 0) (hE₀ : 1 ≤ E 0 0) (hF₀ : 1 ≤ F 0 0) (hG₀ : 1 ≤ G 0 0)
    (h : WeakRules A B C D E F G) (hs : ExactSwaps A B E F G)
    (hd : F.det = 0)
    (h01 : 0 < ((A+B)+(E+F+G)) 0 1)
    (h10 : 0 < ((A+B)+(E+F+G)) 1 0) : False := by
  have ha₀ : 0 < A 0 0 := by linarith only [hA₀]
  have hb₀ : 0 < B 0 0 := by linarith only [hB₀]
  have he₀ : 0 < E 0 0 := by linarith only [hE₀]
  have hf₀ : 0 < F 0 0 := by linarith only [hF₀]
  have hg₀ : 0 < G 0 0 := by linarith only [hG₀]
  obtain ⟨a, hap, hfa, hfb, hfe, hfg, hABF, hBAF⟩ :=
    singular_middle_common_left A B E F G hA hB hF ha₀ hb₀ hf₀ hd hs
  have hff : F*F=tr₂ F • F := by
    simpa only [hd, zero_smul, sub_zero] using square_trace_identity F
  have hw := common_left_row_positive A B E F G a (tr₂ F)
    hF hf₀ hfa hfb hfe hff hfg h01
  have hAF : A*F=a • F := by
    ext i j
    let u : Fin 2 → ℝ := fun k => F k j
    have hwA : ∀ l, ∑ k, F 0 k * A k l = a*F 0 l := by
      intro l
      have hl := congrFun (congrFun hfa 0) l
      simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] using hl
    have hwB : ∀ l, ∑ k, F 0 k * B k l = a*F 0 l := by
      intro l
      have hl := congrFun (congrFun hfb 0) l
      simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] using hl
    have hAB : (A*B).mulVec u=a^2 • u := by
      funext k
      change ((A*B)*F) k j = a^2*F k j
      exact congrFun (congrFun hABF k) j
    have hBA : (B*A).mulVec u=a^2 • u := by
      funext k
      change ((B*A)*F) k j = a^2*F k j
      exact congrFun (congrFun hBAF k) j
    have hu := common_positive_left_product_fixed A B (fun k => F 0 k) u a
      hA hB ha₀ hb₀ hw hap hwA hwB hAB hBA
    have hi := congrFun hu.1 i
    change (A*F) i j = a*F i j at hi
    exact hi
  obtain ⟨haone, hbetaone⟩ := common_actions_force_eigenvalues_one A B C D E F G a (tr₂ F)
    hA hC hD hF hA₀ hC₀ hD₀ hF₀ h hfa hfb hfg hAF hff
  have hf11 : F 1 1=0 := by
    have hn : 0 ≤ F 1 1 := hF 1 1
    dsimp [TwoDimensionalSwapAlgebra.tr] at hbetaone
    linarith only [hbetaone, hF₀, hn]
  have hf10 := singular_middle_lower_entry_positive A B E F G
    hA hB hE hF hG ha₀ hb₀ he₀ hf₀ hg₀ hd hs h10
  have hp := mul_pos (hw 1) hf10
  simp only [Matrix.det_fin_two, hf11, mul_zero, zero_sub] at hd
  linarith only [hd, hp]

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.singular_middle_contradiction
