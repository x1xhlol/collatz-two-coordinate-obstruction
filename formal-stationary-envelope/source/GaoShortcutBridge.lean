import Tejonas
import OptimalCylinderPacking

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.GaoShortcut

open CollatzCylinderPacking CadenaCompletaGao

theorem tm_nat (n : ℕ) : TejonasGao.Tm (n : ℤ) = (step n : ℤ) := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hz : (n : ℤ) % 2 = 0 := by exact_mod_cast he
    simp only [TejonasGao.Tm, step, he, hz, if_true]
    push_cast
    rfl
  · have hn : n % 2 ≠ 0 := by omega
    have hz : (n : ℤ) % 2 ≠ 0 := by omega
    simp only [TejonasGao.Tm, step, hn, hz, if_false]
    push_cast
    rfl

theorem imp_nat (n : ℕ) : TejonasGao.imp (n : ℤ) = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hz : (n : ℤ) % 2 = 0 := by exact_mod_cast he
    simp [TejonasGao.imp, he, hz]
  · have hz : (n : ℤ) % 2 ≠ 0 := by omega
    simp [TejonasGao.imp, ho, hz]

theorem pair_iterate (H n m : ℕ) :
    TejonasGao.iter H ⟨n, m, 0, 0⟩ =
      ⟨iterate H n, iterate H m, oddCount H n, oddCount H m⟩ := by
  induction H with
  | zero => rfl
  | succ H ih =>
    have hs : TejonasGao.iter (H + 1) ⟨n, m, 0, 0⟩ =
        TejonasGao.paso_par (TejonasGao.iter H ⟨n, m, 0, 0⟩) := by
      simp only [TejonasGao.iter, Function.iterate_succ_apply']
    rw [hs, ih]
    simp only [TejonasGao.paso_par, tm_nat, imp_nat, iterate, oddCount]

def good (H n : ℕ) : Prop :=
  TejonasGao.canon (TejonasGao.iter H ⟨(n : ℤ), (n : ℤ) + 1, 0, 0⟩) = .fusion

instance (H n : ℕ) : Decidable (good H n) := by
  unfold good
  infer_instance

theorem good_iff (H n : ℕ) :
    good H n ↔ iterate H n = iterate H (n + 1) ∧ oddCount H n = oddCount H (n + 1) := by
  have hn : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; rfl
  unfold good
  rw [← hn, pair_iterate]
  unfold TejonasGao.canon
  by_cases he : oddCount H n = oddCount H (n + 1)
  · by_cases hx : iterate H n = iterate H (n + 1)
    · simp [he, hx]
    · have hz : (iterate H n : ℤ) ≠ (iterate H (n + 1) : ℤ) := by exact_mod_cast hx
      simp [he, hx, hz]
      split <;> simp
  · simp [he]
    split <;> simp

theorem good_mod (H n : ℕ) : good H n ↔ good H (n % 2 ^ H) := by
  unfold good
  rw [TejonasGao.canon_modulo]

noncomputable def goodProbability (H : ℕ) : ℝ :=
  EnsayoGao.probabilidad_fusion H (.vivo 0 1)

theorem good_card (H : ℕ) :
    (((Finset.range (2 ^ H)).filter (good H)).card : ℝ) =
      (2 : ℝ) ^ H * goodProbability H := by
  classical
  have h := TejonasGao.transporte EnsayoGao.fusion H
  unfold goodProbability EnsayoGao.probabilidad_fusion
  rw [← h, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  unfold EnsayoGao.fusion good
  split <;> simp_all

theorem goodProbability_bounds (H : ℕ) :
    0 ≤ goodProbability H ∧ goodProbability H ≤ 1 := by
  have hc := good_card H
  have hp : 0 < (2 : ℝ) ^ H := by positivity
  have hlo : (0 : ℝ) ≤ (((Finset.range (2 ^ H)).filter (good H)).card : ℝ) := by positivity
  have hup : (((Finset.range (2 ^ H)).filter (good H)).card : ℝ) ≤ (2 : ℝ) ^ H := by
    have h := Finset.card_le_card (Finset.filter_subset (good H) (Finset.range (2 ^ H)))
    simpa using (show (((Finset.range (2 ^ H)).filter (good H)).card : ℝ) ≤
      ((Finset.range (2 ^ H)).card : ℝ) by exact_mod_cast h)
  constructor <;> nlinarith

theorem goodProbability_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ H0 : ℕ, ∀ H, H0 ≤ H → 1 - goodProbability H ≤ ε :=
  MartasGao.martas ε hε

theorem good_count_lower (H X : ℕ) :
    (X : ℝ) * goodProbability H - (2 : ℝ) ^ H ≤
      (((Finset.range X).filter (good H)).card : ℝ) := by
  classical
  let S := (Finset.range (2 ^ H)).filter (good H)
  have hperiod (n : ℕ) : n % 2 ^ H ∈ S ↔ good H n := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => (good_mod H n).mpr h.2,
      fun h => ⟨Nat.mod_lt _ (by positivity), (good_mod H n).mp h⟩⟩
  have he : (Finset.range X).filter (fun n => n % 2 ^ H ∈ S) =
      (Finset.range X).filter (good H) := by
    ext n
    simp only [Finset.mem_filter, hperiod]
  have hcount := TejonasGao.conteo_bloques X (2 ^ H) (by positivity) S
    (Finset.filter_subset _ _)
  rw [he] at hcount
  have hcountR : (X / 2 ^ H : ℕ) * ((S.card : ℕ) : ℝ) ≤
      (((Finset.range X).filter (good H)).card : ℝ) := by exact_mod_cast hcount
  have hcard : (S.card : ℝ) = (2 : ℝ) ^ H * goodProbability H := good_card H
  rw [hcard] at hcountR
  have hdiv : (X : ℝ) < (X / 2 ^ H : ℕ) * (2 : ℝ) ^ H + (2 : ℝ) ^ H := by
    exact_mod_cast (Nat.lt_div_mul_add (a := X) (by positivity : 0 < (2 : ℕ) ^ H))
  have hb := goodProbability_bounds H
  have hm : (2 : ℝ) ^ H * goodProbability H ≤ (2 : ℝ) ^ H := by
    nlinarith [show 0 ≤ (2 : ℝ) ^ H by positivity]
  have hmul := mul_le_mul_of_nonneg_right hdiv.le hb.1
  nlinarith

end CollatzCanonical.GaoShortcut

#print axioms CollatzCanonical.GaoShortcut.pair_iterate
#print axioms CollatzCanonical.GaoShortcut.good_iff
#print axioms CollatzCanonical.GaoShortcut.good_count_lower
#print axioms CollatzCanonical.GaoShortcut.goodProbability_eventually
