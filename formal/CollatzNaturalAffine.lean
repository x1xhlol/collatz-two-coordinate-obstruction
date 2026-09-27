import CollatzCertificateBridge
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace CollatzResearch

open Matrix

structure NatAffine (ι : Type*) where
  matrix : Matrix ι ι ℕ
  offset : ι → ℕ

namespace NatAffine

variable {ι : Type*} [Fintype ι]

def eval (F : NatAffine ι) (x : ι → ℕ) : ι → ℕ :=
  F.matrix *ᵥ x + F.offset

def comp (F G : NatAffine ι) : NatAffine ι :=
  ⟨F.matrix * G.matrix, F.matrix *ᵥ G.offset + F.offset⟩

def Weak (F G : NatAffine ι) : Prop :=
  (∀ i j, G.matrix i j ≤ F.matrix i j) ∧ G.offset ≤ F.offset

theorem eval_comp (F G : NatAffine ι) (x : ι → ℕ) :
    (F.comp G).eval x = F.eval (G.eval x) := by
  simp only [eval, comp, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

theorem eval_monotone (F : NatAffine ι) : Monotone F.eval := by
  intro x y hxy i
  change (∑ j, F.matrix i j * x j) + F.offset i ≤
    (∑ j, F.matrix i j * y j) + F.offset i
  exact Nat.add_le_add_right
    (Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left (F.matrix i j) (hxy j))) _

theorem eval_weak {F G : NatAffine ι} (h : F.Weak G) (x : ι → ℕ) :
    G.eval x ≤ F.eval x := by
  intro i
  change (∑ j, G.matrix i j * x j) + G.offset i ≤
    (∑ j, F.matrix i j * x j) + F.offset i
  exact add_le_add
    (Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right (x j) (h.1 i j))) (h.2 i)

theorem eval_strict_at {F G : NatAffine ι} (h : F.Weak G) (i₀ : ι)
    (hstrict : G.offset i₀ < F.offset i₀) (x : ι → ℕ) :
    G.eval x i₀ < F.eval x i₀ := by
  change (∑ j, G.matrix i₀ j * x j) + G.offset i₀ <
    (∑ j, F.matrix i₀ j * x j) + F.offset i₀
  exact add_lt_add_of_le_of_lt
    (Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right (x j) (h.1 i₀ j))) hstrict

theorem all_rules_and_three_strict_roots_imply_collatz
    (A B C D E F G : NatAffine ι) (i₀ : ι)
    (had : (A.comp D).Weak D)
    (hbd : (B.comp D).Weak (G.comp D))
    (hae : (A.comp E).Weak (E.comp A))
    (haf : (A.comp F).Weak (E.comp B))
    (hag : (A.comp G).Weak (F.comp A))
    (hbe : (B.comp E).Weak (F.comp B))
    (hbf : (B.comp F).Weak (G.comp A))
    (hbg : (B.comp G).Weak (G.comp B))
    (hce : (C.comp E).Weak (C.comp B))
    (hcf : (C.comp F).Weak (C.comp (A.comp A)))
    (hcg : (C.comp G).Weak (C.comp (A.comp B)))
    (hstrict_e : (C.comp B).offset i₀ < (C.comp E).offset i₀)
    (hstrict_f : (C.comp (A.comp A)).offset i₀ < (C.comp F).offset i₀)
    (hstrict_g : (C.comp (A.comp B)).offset i₀ < (C.comp G).offset i₀) :
    CollatzConjecture := by
  exact root_strict_certificate_implies_collatz {
    a := A.eval
    b := B.eval
    e := E.eval
    f := F.eval
    g := G.eval
    readout := fun x => C.eval x i₀
    initial := D.offset
    a_monotone := A.eval_monotone
    b_monotone := B.eval_monotone
    readout_monotone := fun _ _ h => C.eval_monotone h i₀
    ad := had.2
    bd := hbd.2
    ae := fun x => by simpa only [eval_comp] using eval_weak hae x
    af := fun x => by simpa only [eval_comp] using eval_weak haf x
    ag := fun x => by simpa only [eval_comp] using eval_weak hag x
    be := fun x => by simpa only [eval_comp] using eval_weak hbe x
    bf := fun x => by simpa only [eval_comp] using eval_weak hbf x
    bg := fun x => by simpa only [eval_comp] using eval_weak hbg x
    ce := fun x => by simpa only [eval_comp] using eval_strict_at hce i₀ hstrict_e x
    cf := fun x => by simpa only [eval_comp] using eval_strict_at hcf i₀ hstrict_f x
    cg := fun x => by simpa only [eval_comp] using eval_strict_at hcg i₀ hstrict_g x
  }

#print axioms eval_comp
#print axioms eval_monotone
#print axioms eval_weak
#print axioms eval_strict_at
#print axioms all_rules_and_three_strict_roots_imply_collatz

end NatAffine
end CollatzResearch
