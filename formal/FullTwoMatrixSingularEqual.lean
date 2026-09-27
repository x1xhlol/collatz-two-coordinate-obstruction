import FullTwoMatrixSingularAlgebra
import FullTwoMatrixCommonRankOne
import Mathlib.Tactic.FieldSimp

namespace CollatzCertificate.FullTwoMatrix

open Matrix TwoDimensionalMiddleRank

local notation "tr₂" => TwoDimensionalSwapAlgebra.tr

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

theorem equal_singular_common_actions (A E F G : M2)
    (hA : EntrywiseLE 0 A) (hE : EntrywiseLE 0 E)
    (hA00 : 0 < A 0 0) (hE00 : 0 < E 0 0)
    (hd : A.det=0) (hs : ExactSwaps A A E F G) :
    ∃ β : ℝ, 0 < β ∧ A*A=tr₂ A • A ∧
      A*E=β • A ∧ E*A=β • A ∧
      A*F=β • A ∧ F*A=β • A ∧
      A*G=β • A ∧ G*A=β • A := by
  rcases hs with ⟨hae,haf,hag,hbe,hbf,hbg⟩
  have ht : 0 < tr₂ A := trace_positive A hA hA00
  have haa : A*A=tr₂ A • A := by
    simpa only [hd,zero_smul,sub_zero] using square_trace_identity A
  have hsan : (A*E)*A=tr₂ (A*E) • A := by
    simpa only [hd,zero_smul,zero_mul,add_zero,sub_zero] using sandwich_trace_identity A E
  have hscale : tr₂ A • (A*E)=tr₂ (A*E) • A := by
    rw [hae,Matrix.mul_assoc,haa,Matrix.mul_smul,← hae] at hsan
    exact hsan
  let β := tr₂ (A*E) / tr₂ A
  have hae' : A*E=β • A := by
    ext i j
    have hij := congrFun (congrFun hscale i) j
    change tr₂ A*(A*E) i j=tr₂ (A*E)*A i j at hij
    change (A*E) i j=β*A i j
    apply mul_left_cancel₀ (ne_of_gt ht)
    calc
      tr₂ A*(A*E) i j = tr₂ (A*E)*A i j := hij
      _ = tr₂ A*(β*A i j) := by dsimp [β]; field_simp
  have hβ : 0 < β := by
    have h00 := congrFun (congrFun hae' 0) 0
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul] at h00
    have hp := mul_pos hA00 hE00
    have hn := mul_nonneg (hA 0 1) (hE 1 0)
    nlinarith only [h00,hp,hn,hA00]
  have hea' : E*A=β • A := by rw [← hae]; exact hae'
  have haf' : A*F=β • A := by rw [haf]; exact hea'
  have hfa' : F*A=β • A := by rw [← hbe]; exact hae'
  have hag' : A*G=β • A := by rw [hag]; exact hfa'
  have hga' : G*A=β • A := by rw [← hbf]; exact haf'
  exact ⟨β,hβ,haa,hae',hea',haf',hfa',hag',hga'⟩


theorem equal_singular_boundary_contradiction (A C D E F G : M2)
    (hA : EntrywiseLE 0 A) (hC : EntrywiseLE 0 C) (hD : EntrywiseLE 0 D)
    (hE : EntrywiseLE 0 E) (_hF : EntrywiseLE 0 F) (_hG : EntrywiseLE 0 G)
    (hA00 : 1 ≤ A 0 0) (hC00 : 1 ≤ C 0 0) (hD00 : 1 ≤ D 0 0)
    (hE00 : 1 ≤ E 0 0) (_hF00 : 1 ≤ F 0 0) (_hG00 : 1 ≤ G 0 0)
    (h : WeakRules A A C D E F G) (hs : ExactSwaps A A E F G)
    (hd : A.det=0)
    (h01 : 0 < ((A+A)+(E+F+G)) 0 1)
    (h10 : 0 < ((A+A)+(E+F+G)) 1 0) : False := by
  obtain ⟨β,_,haa,hae,hea,haf,hfa,hag,hga⟩ := equal_singular_common_actions
    A E F G hA hE (by linarith only [hA00]) (by linarith only [hE00]) hd hs
  have hAH : A*((A+A)+(E+F+G))=(2*tr₂ A+3*β) • A := by
    simp only [Matrix.mul_add,haa,hae,haf,hag]
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  have hHA : ((A+A)+(E+F+G))*A=(2*tr₂ A+3*β) • A := by
    simp only [Matrix.add_mul,haa,hea,hfa,hga]
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  exact common_rankone_contradiction A A C D E F G A (tr₂ A) β (2*tr₂ A+3*β)
    hA hC hD hA hA00 hC00 hD00 hA00 h haa haa hag haa hfa hAH hHA hd rfl h01 h10

#print axioms equal_singular_common_actions
#print axioms equal_singular_boundary_contradiction

end CollatzCertificate.FullTwoMatrix
