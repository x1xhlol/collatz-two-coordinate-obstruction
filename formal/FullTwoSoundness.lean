import FullTwoBasic

namespace CollatzResearch.FullTwoSoundness

open Matrix CollatzCertificate FullTwo RealAffine

def Gap (δ : ℝ) (x y : Vec (Fin 2)) : Prop := y 0 + δ ≤ x 0 ∧ y 1 ≤ x 1

theorem admissible_preserves_gap {X : Aff2} (hX : Admissible X)
    {δ : ℝ} (hδ : 0 ≤ δ) {x y : Vec (Fin 2)} (hxy : Gap δ x y) :
    Gap δ (eval X x) (eval X y) := by
  have h0 : y 0 ≤ x 0 := by linarith only [hxy.1, hδ]
  have h00 := mul_le_mul_of_nonneg_left hxy.1 (hX.1.1 0 0)
  have hδ' := mul_le_mul_of_nonneg_right hX.2 hδ
  have h01 := mul_le_mul_of_nonneg_left hxy.2 (hX.1.1 0 1)
  have h10 := mul_le_mul_of_nonneg_left h0 (hX.1.1 1 0)
  have h11 := mul_le_mul_of_nonneg_left hxy.2 (hX.1.1 1 1)
  constructor
  · change (X.matrix *ᵥ y + X.offset) 0 + δ ≤ (X.matrix *ᵥ x + X.offset) 0
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith only [h00, hδ', h01]
  · change (X.matrix *ᵥ y + X.offset) 1 ≤ (X.matrix *ᵥ x + X.offset) 1
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linarith only [h10, h11]

theorem weak_rule_gives_gap {X Y : Aff2} (h : X.Weak Y)
    {δ : ℝ} (hgap : δ ≤ X.offset 0 - Y.offset 0)
    {x : Vec (Fin 2)} (hx : 0 ≤ x) : Gap δ (eval X x) (eval Y x) := by
  constructor
  · have hh := eval_offset_gap h 0 hx
    linarith only [hh, hgap]
  · exact eval_weak h hx 1

theorem gap_wellFounded (δ : ℝ) (hδ : 0 < δ) :
    WellFounded (fun y x : {v : Vec (Fin 2) // 0 ≤ v} => Gap δ x.1 y.1) := by
  apply (measure (fun x : {v : Vec (Fin 2) // 0 ≤ v} => Nat.floor (x.1 0 / δ))).wf.mono
  intro y x hgap
  change Nat.floor (y.1 0 / δ) < Nat.floor (x.1 0 / δ)
  exact floor_scaled_gap (y.2 0) hδ hgap.1

end CollatzResearch.FullTwoSoundness

#print axioms CollatzResearch.FullTwoSoundness.admissible_preserves_gap
#print axioms CollatzResearch.FullTwoSoundness.weak_rule_gives_gap
#print axioms CollatzResearch.FullTwoSoundness.gap_wellFounded
