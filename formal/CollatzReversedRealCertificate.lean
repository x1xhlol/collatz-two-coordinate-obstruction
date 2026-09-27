import CollatzReversedCertificate
import ReversedBinaryPowerClosure
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Semiring

namespace CollatzResearch.RealAffine

open Matrix CollatzCertificate

variable {ι : Type*} [Fintype ι]

def eval (F : Affine ι) (x : Vec ι) : Vec ι := F.matrix *ᵥ x + F.offset

theorem eval_comp (F G : Affine ι) (x : Vec ι) :
    eval (F.comp G) x = eval F (eval G x) := by
  simp only [eval, Affine.comp, mulVec_add, mulVec_mulVec, add_assoc]

theorem eval_nonnegative {F : Affine ι} (hF : F.Nonnegative) {x : Vec ι}
    (hx : 0 ≤ x) : 0 ≤ eval F x := by
  intro i
  exact add_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hF.1 i j) (hx j))) (hF.2 i)

theorem eval_monotone {F : Affine ι} (hF : EntrywiseLE 0 F.matrix) : Monotone (eval F) := by
  intro x y hxy i
  exact add_le_add (Finset.sum_le_sum
    (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hF i j))) le_rfl

theorem eval_weak {F G : Affine ι} (h : F.Weak G) {x : Vec ι} (hx : 0 ≤ x) :
    eval G x ≤ eval F x := by
  intro i
  exact add_le_add (Finset.sum_le_sum
    (fun j _ => mul_le_mul_of_nonneg_right (h.1 i j) (hx j))) (h.2 i)

theorem eval_offset_gap {F G : Affine ι} (h : F.Weak G) (i₀ : ι)
    {x : Vec ι} (hx : 0 ≤ x) :
    eval G x i₀ + (F.offset i₀ - G.offset i₀) ≤ eval F x i₀ := by
  have hm := Finset.sum_le_sum
    (fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_right (h.1 i₀ j) (hx j))
  change (∑ j, G.matrix i₀ j * x j) + G.offset i₀ +
    (F.offset i₀ - G.offset i₀) ≤ (∑ j, F.matrix i₀ j * x j) + F.offset i₀
  linarith

omit [Fintype ι] in
theorem floor_scaled_gap {x y δ : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ)
    (hgap : x + δ ≤ y) : Nat.floor (x / δ) < Nat.floor (y / δ) := by
  have hi : x / δ + 1 ≤ y / δ := by
    rw [← div_self (ne_of_gt hδ), ← add_div]
    exact div_le_div_of_nonneg_right hgap (le_of_lt hδ)
  have hf := Nat.floor_mono hi
  rw [Nat.floor_add_one (div_nonneg hx (le_of_lt hδ))] at hf
  omega

theorem reversed_real_first_removal_implies_collatz
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (hda : (D.comp A).Weak D)
    (hdb : (D.comp B).Weak (D.comp G))
    (hea : (E.comp A).Weak (A.comp E))
    (hfa : (F.comp A).Weak (B.comp E))
    (hga : (G.comp A).Weak (A.comp F))
    (heb : (E.comp B).Weak (B.comp F))
    (hfb : (F.comp B).Weak (A.comp G))
    (hgb : (G.comp B).Weak (B.comp G))
    (hec : (E.comp C).Weak (B.comp C))
    (hfc : (F.comp C).Weak (A.comp (A.comp C)))
    (hgc : (G.comp C).Weak (B.comp (A.comp C)))
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    CollatzConjecture := by
  obtain ⟨δ, hδ, hgap⟩ : ∃ δ : ℝ, 0 < δ ∧
      (δ ≤ (D.comp A).offset i₀ - D.offset i₀ ∨
        δ ≤ (D.comp B).offset i₀ - (D.comp G).offset i₀) := by
    rcases hstrict with hs | hs
    · exact ⟨_, sub_pos.mpr hs, Or.inl le_rfl⟩
    · exact ⟨_, sub_pos.mpr hs, Or.inr le_rfl⟩
  let c : ReversedCertificate.Data {x : Vec ι // 0 ≤ x} := {
    a := fun x => ⟨eval A x.1, eval_nonnegative hA x.2⟩
    b := fun x => ⟨eval B x.1, eval_nonnegative hB x.2⟩
    e := fun x => ⟨eval E x.1, eval_nonnegative hE x.2⟩
    f := fun x => ⟨eval F x.1, eval_nonnegative hF x.2⟩
    g := fun x => ⟨eval G x.1, eval_nonnegative hG x.2⟩
    readout := fun x => Nat.floor (eval D x.1 i₀ / δ)
    initial := ⟨C.offset, hC.2⟩
    a_monotone := fun _ _ h => eval_monotone hA.1 h
    b_monotone := fun _ _ h => eval_monotone hB.1 h
    readout_monotone := fun _ _ h => Nat.floor_mono
      (div_le_div_of_nonneg_right (eval_monotone hD.1 h i₀) (le_of_lt hδ))
    ea := fun x => by simpa only [eval_comp] using eval_weak hea x.2
    fa := fun x => by simpa only [eval_comp] using eval_weak hfa x.2
    ga := fun x => by simpa only [eval_comp] using eval_weak hga x.2
    eb := fun x => by simpa only [eval_comp] using eval_weak heb x.2
    fb := fun x => by simpa only [eval_comp] using eval_weak hfb x.2
    gb := fun x => by simpa only [eval_comp] using eval_weak hgb x.2
    ec := hec.2
    fc := hfc.2
    gc := hgc.2
  }
  apply ReversedCertificate.first_eligible_root_implies_collatz c
  · intro x
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ (le_of_lt hδ)
    simpa only [eval_comp] using eval_weak hda x.2 i₀
  · intro x
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ (le_of_lt hδ)
    simpa only [eval_comp] using eval_weak hdb x.2 i₀
  · rcases hgap with hs | hs
    · left
      intro x
      apply floor_scaled_gap (eval_nonnegative hD x.2 i₀) hδ
      have hi := eval_offset_gap hda i₀ x.2
      rw [eval_comp] at hi
      change eval D x.1 i₀ + δ ≤ eval D (eval A x.1) i₀
      linarith
    · right
      intro x
      apply floor_scaled_gap (eval_nonnegative hD (eval_nonnegative hG x.2) i₀) hδ
      have hi := eval_offset_gap hdb i₀ x.2
      simp only [eval_comp] at hi
      change eval D (eval G x.1) i₀ + δ ≤ eval D (eval B x.1) i₀
      linarith

#print axioms eval_comp
#print axioms eval_nonnegative
#print axioms eval_monotone
#print axioms eval_weak
#print axioms eval_offset_gap
#print axioms floor_scaled_gap
#print axioms reversed_real_first_removal_implies_collatz

end CollatzResearch.RealAffine
