import ReversedBinaryPowerClosure
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

namespace CollatzCertificate

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nonnegative_matrix_power_entries (H : Mat ι) (hH : EntrywiseLE 0 H) (k : ℕ) :
    EntrywiseLE 0 (H ^ k) := by
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split <;> norm_num
  | succ k ih =>
    rw [pow_succ]
    intro i j
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hH l j))

theorem commutator_power_trace_zero (H S : Mat ι) (k : ℕ) :
    Matrix.trace (H ^ k * (S * H - H * S)) = 0 := by
  have hc : H * H ^ k = H ^ k * H := by rw [← pow_succ', pow_succ]
  have ht : Matrix.trace (H ^ k * (S * H)) = Matrix.trace (H ^ k * (H * S)) := by
    calc
      Matrix.trace (H ^ k * (S * H)) = Matrix.trace (H * (H ^ k * S)) := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace ((H * H ^ k) * S) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((H ^ k * H) * S) := by rw [hc]
      _ = Matrix.trace (H ^ k * (H * S)) := by rw [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.trace_sub, ht, sub_self]

theorem nonnegative_commutator_return_product_zero (H S : Mat ι)
    (hH : EntrywiseLE 0 H) (hD : EntrywiseLE 0 (S * H - H * S))
    (k : ℕ) (i j : ι) :
    (H ^ k) j i * (S * H - H * S) i j = 0 := by
  have hp := nonnegative_matrix_power_entries H hH k
  have hn (l : ι) : 0 ≤ (H ^ k * (S * H - H * S)) l l :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (hp l m) (hD m l))
  have ht := commutator_power_trace_zero H S k
  have hz : (H ^ k * (S * H - H * S)) j j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hn l)).mp ht j (Finset.mem_univ j)
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun m _ => mul_nonneg (hp j m) (hD m j))).mp hz i (Finset.mem_univ i)

theorem nonnegative_commutator_zero_at_return (H S : Mat ι)
    (hH : EntrywiseLE 0 H) (hD : EntrywiseLE 0 (S * H - H * S))
    (k : ℕ) (i j : ι) (hreturn : 0 < (H ^ k) j i) :
    (S * H - H * S) i j = 0 := by
  exact (mul_eq_zero.mp (nonnegative_commutator_return_product_zero H S hH hD k i j)).resolve_left
    (ne_of_gt hreturn)

theorem reversed_swap_equalities_at_return (A B E F G : Mat ι)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hea : EntrywiseLE (A * E) (E * A))
    (hfa : EntrywiseLE (B * E) (F * A))
    (hga : EntrywiseLE (A * F) (G * A))
    (heb : EntrywiseLE (B * F) (E * B))
    (hfb : EntrywiseLE (A * G) (F * B))
    (hgb : EntrywiseLE (B * G) (G * B))
    (k : ℕ) (i j : ι) (hreturn : 0 < (((A + B) + (E + F + G)) ^ k) j i) :
    (E * A) i j = (A * E) i j ∧ (F * A) i j = (B * E) i j ∧
    (G * A) i j = (A * F) i j ∧ (E * B) i j = (B * F) i j ∧
    (F * B) i j = (A * G) i j ∧ (G * B) i j = (B * G) i j := by
  let H := (A + B) + (E + F + G)
  let S := E + F + G
  have hH : EntrywiseLE 0 H := by
    intro l m
    exact add_nonneg (add_nonneg (hA l m) (hB l m))
      (add_nonneg (add_nonneg (hE l m) (hF l m)) (hG l m))
  have hD : EntrywiseLE 0 (S * H - H * S) := by
    intro l m
    change 0 ≤ (S * H - H * S) l m
    simp only [H, S, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.sub_apply]
    linarith [hea l m, hfa l m, hga l m, heb l m, hfb l m, hgb l m]
  have hz := nonnegative_commutator_zero_at_return H S hH hD k i j hreturn
  simp only [H, S, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.sub_apply] at hz
  have h1 := hea i j
  have h2 := hfa i j
  have h3 := hga i j
  have h4 := heb i j
  have h5 := hfb i j
  have h6 := hgb i j
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem reversed_swap_equalities_of_all_returns (A B E F G : Mat ι)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hea : EntrywiseLE (A * E) (E * A))
    (hfa : EntrywiseLE (B * E) (F * A))
    (hga : EntrywiseLE (A * F) (G * A))
    (heb : EntrywiseLE (B * F) (E * B))
    (hfb : EntrywiseLE (A * G) (F * B))
    (hgb : EntrywiseLE (B * G) (G * B))
    (hreturn : ∀ i j, ∃ k : ℕ, 0 < (((A + B) + (E + F + G)) ^ k) j i) :
    E * A = A * E ∧ F * A = B * E ∧ G * A = A * F ∧
    E * B = B * F ∧ F * B = A * G ∧ G * B = B * G := by
  have hr (i j : ι) :
      (E * A) i j = (A * E) i j ∧ (F * A) i j = (B * E) i j ∧
      (G * A) i j = (A * F) i j ∧ (E * B) i j = (B * F) i j ∧
      (F * B) i j = (A * G) i j ∧ (G * B) i j = (B * G) i j := by
    obtain ⟨k, hk⟩ := hreturn i j
    exact reversed_swap_equalities_at_return A B E F G hA hB hE hF hG
      hea hfa hga heb hfb hgb k i j hk
  exact ⟨Matrix.ext (fun i j => (hr i j).1),
    Matrix.ext (fun i j => (hr i j).2.1), Matrix.ext (fun i j => (hr i j).2.2.1),
    Matrix.ext (fun i j => (hr i j).2.2.2.1), Matrix.ext (fun i j => (hr i j).2.2.2.2.1),
    Matrix.ext (fun i j => (hr i j).2.2.2.2.2)⟩

theorem reversed_swap_equalities_on_diagonal (A B E F G : Mat ι)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hea : EntrywiseLE (A * E) (E * A))
    (hfa : EntrywiseLE (B * E) (F * A))
    (hga : EntrywiseLE (A * F) (G * A))
    (heb : EntrywiseLE (B * F) (E * B))
    (hfb : EntrywiseLE (A * G) (F * B))
    (hgb : EntrywiseLE (B * G) (G * B)) (i : ι) :
    (E * A) i i = (A * E) i i ∧ (F * A) i i = (B * E) i i ∧
    (G * A) i i = (A * F) i i ∧ (E * B) i i = (B * F) i i ∧
    (F * B) i i = (A * G) i i ∧ (G * B) i i = (B * G) i i := by
  exact reversed_swap_equalities_at_return A B E F G hA hB hE hF hG
    hea hfa hga heb hfb hgb 0 i i (by simp)

theorem reversed_affine_swaps_exact_of_irreducible (A B E F G : Affine ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hE : E.Nonnegative)
    (hF : F.Nonnegative) (hG : G.Nonnegative)
    (hea : (E.comp A).Weak (A.comp E))
    (hfa : (F.comp A).Weak (B.comp E))
    (hga : (G.comp A).Weak (A.comp F))
    (heb : (E.comp B).Weak (B.comp F))
    (hfb : (F.comp B).Weak (A.comp G))
    (hgb : (G.comp B).Weak (B.comp G))
    (hirr : ((A.matrix + B.matrix) + (E.matrix + F.matrix + G.matrix)).IsIrreducible) :
    E.matrix * A.matrix = A.matrix * E.matrix ∧
    F.matrix * A.matrix = B.matrix * E.matrix ∧
    G.matrix * A.matrix = A.matrix * F.matrix ∧
    E.matrix * B.matrix = B.matrix * F.matrix ∧
    F.matrix * B.matrix = A.matrix * G.matrix ∧
    G.matrix * B.matrix = B.matrix * G.matrix := by
  apply reversed_swap_equalities_of_all_returns A.matrix B.matrix E.matrix F.matrix G.matrix
    hA.1 hB.1 hE.1 hF.1 hG.1 hea.1 hfa.1 hga.1 heb.1 hfb.1 hgb.1
  intro i j
  obtain ⟨k, _, hk⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hirr.nonneg).mp hirr j i
  exact ⟨k, hk⟩

#print axioms nonnegative_matrix_power_entries
#print axioms commutator_power_trace_zero
#print axioms nonnegative_commutator_return_product_zero
#print axioms nonnegative_commutator_zero_at_return
#print axioms reversed_swap_equalities_at_return
#print axioms reversed_swap_equalities_of_all_returns
#print axioms reversed_swap_equalities_on_diagonal
#print axioms reversed_affine_swaps_exact_of_irreducible

end CollatzCertificate
