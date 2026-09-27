import ReversedRealNormalization
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace CollatzResearch.FullTwo

open Matrix CollatzCertificate

abbrev Aff2 := Affine (Fin 2)

def Admissible (X : Aff2) : Prop := X.Nonnegative ∧ 1 ≤ X.matrix 0 0

def Upper (X : Aff2) : Prop := X.matrix 0 0 = 1 ∧ X.matrix 1 0 = 0

def Lower (X : Aff2) : Prop := X.matrix 0 0 = 1 ∧ X.matrix 0 1 = 0

def upper (q z h k : ℝ) : Aff2 := ⟨!![1, q; 0, z], ![h, k]⟩

def lower (q z h k : ℝ) : Aff2 := ⟨!![1, 0; q, z], ![h, k]⟩

structure ForwardWeak (A B C D E F G : Aff2) : Prop where
  ad : (A.comp D).Weak D
  bd : (B.comp D).Weak (G.comp D)
  ae : (A.comp E).Weak (E.comp A)
  af : (A.comp F).Weak (E.comp B)
  ag : (A.comp G).Weak (F.comp A)
  be : (B.comp E).Weak (F.comp B)
  bf : (B.comp F).Weak (G.comp A)
  bg : (B.comp G).Weak (G.comp B)
  ce : (C.comp E).Weak (C.comp B)
  cf : (C.comp F).Weak (C.comp (A.comp A))
  cg : (C.comp G).Weak (C.comp (A.comp B))

structure ForwardGapsZero (A B C D E F G : Aff2) : Prop where
  ad : (A.comp D).offset 0 = D.offset 0
  bd : (B.comp D).offset 0 = (G.comp D).offset 0
  ae : (A.comp E).offset 0 = (E.comp A).offset 0
  af : (A.comp F).offset 0 = (E.comp B).offset 0
  ag : (A.comp G).offset 0 = (F.comp A).offset 0
  be : (B.comp E).offset 0 = (F.comp B).offset 0
  bf : (B.comp F).offset 0 = (G.comp A).offset 0
  bg : (B.comp G).offset 0 = (G.comp B).offset 0
  ce : (C.comp E).offset 0 = (C.comp B).offset 0
  cf : (C.comp F).offset 0 = (C.comp (A.comp A)).offset 0
  cg : (C.comp G).offset 0 = (C.comp (A.comp B)).offset 0

structure ReversedGapsZero (A B C D E F G : Aff2) : Prop where
  da : (D.comp A).offset 0 = D.offset 0
  db : (D.comp B).offset 0 = (D.comp G).offset 0
  ea : (E.comp A).offset 0 = (A.comp E).offset 0
  fa : (F.comp A).offset 0 = (B.comp E).offset 0
  ga : (G.comp A).offset 0 = (A.comp F).offset 0
  eb : (E.comp B).offset 0 = (B.comp F).offset 0
  fb : (F.comp B).offset 0 = (A.comp G).offset 0
  gb : (G.comp B).offset 0 = (B.comp G).offset 0
  ec : (E.comp C).offset 0 = (B.comp C).offset 0
  fc : (F.comp C).offset 0 = (A.comp (A.comp C)).offset 0
  gc : (G.comp C).offset 0 = (B.comp (A.comp C)).offset 0

theorem affine_ext (X Y : Aff2) (hm : X.matrix = Y.matrix) (hv : X.offset = Y.offset) :
    X = Y := by
  cases X
  cases Y
  simp_all

theorem eq_upper (X : Aff2) (hX : Upper X) :
    X = upper (X.matrix 0 1) (X.matrix 1 1) (X.offset 0) (X.offset 1) := by
  apply affine_ext
  · ext i j
    fin_cases i <;> fin_cases j <;> simp_all [upper, Upper]
  · ext i
    fin_cases i <;> rfl

theorem eq_lower (X : Aff2) (hX : Lower X) :
    X = lower (X.matrix 1 0) (X.matrix 1 1) (X.offset 0) (X.offset 1) := by
  apply affine_ext
  · ext i j
    fin_cases i <;> fin_cases j <;> simp_all [lower, Lower]
  · ext i
    fin_cases i <;> rfl

end CollatzResearch.FullTwo

#print axioms CollatzResearch.FullTwo.affine_ext
#print axioms CollatzResearch.FullTwo.eq_upper
#print axioms CollatzResearch.FullTwo.eq_lower
