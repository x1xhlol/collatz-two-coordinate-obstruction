/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Antitone Residue-Class Sums

This module proves a sharp finite interlacing estimate for nonnegative
antitone weights on an inclusive natural interval.  It is independent of PMFs,
`ZMod`, and the analytic endpoint choices used by Tao's Section 5.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

/-- The elements of `[A, B]` lying in one normalized residue class modulo `Q`. -/
def antitoneResidueClass (A B Q : ℕ) (r : Fin Q) : Finset ℕ :=
  (Finset.Icc A B).filter fun i => i % Q = r.1

/-- The weight in one normalized residue class of an inclusive interval. -/
noncomputable def antitoneResidueClassSum
    (A B Q : ℕ) (w : ℕ → ℝ) (r : Fin Q) : ℝ :=
  ∑ i ∈ antitoneResidueClass A B Q r, w i

@[simp]
theorem mem_antitoneResidueClass {A B Q i : ℕ} {r : Fin Q} :
    i ∈ antitoneResidueClass A B Q r ↔ A ≤ i ∧ i ≤ B ∧ i % Q = r.1 := by
  simp [antitoneResidueClass, and_assoc]

/-- The positive cyclic distance which carries `s` to a distinct residue `r`. -/
private def antitoneResidueGap {Q : ℕ} (r s : Fin Q) : ℕ :=
  if s.1 ≤ r.1 then r.1 - s.1 else Q - (s.1 - r.1)

private theorem antitoneResidueGap_pos_lt {Q : ℕ} (_hQ : 0 < Q)
    {r s : Fin Q} (hrs : r ≠ s) :
    0 < antitoneResidueGap r s ∧ antitoneResidueGap r s < Q := by
  have hrsval : r.1 ≠ s.1 := by
    intro h
    apply hrs
    exact Fin.ext h
  unfold antitoneResidueGap
  split_ifs with hsr
  · constructor <;> omega
  · have hrslt : r.1 < s.1 := Nat.lt_of_not_ge hsr
    constructor <;> omega

private theorem antitoneResidueGap_add_mod {Q : ℕ} (_hQ : 0 < Q)
    {r s : Fin Q} (_hrs : r ≠ s) :
    (s.1 + antitoneResidueGap r s) % Q = r.1 := by
  unfold antitoneResidueGap
  split_ifs with hsr
  · have hsum : s.1 + (r.1 - s.1) = r.1 := by omega
    rw [hsum, Nat.mod_eq_of_lt r.2]
  · have hrslt : r.1 < s.1 := Nat.lt_of_not_ge hsr
    have hsum : s.1 + (Q - (s.1 - r.1)) = Q + r.1 := by omega
    rw [hsum, Nat.add_mod, Nat.mod_self, zero_add]
    simp [Nat.mod_eq_of_lt r.2]

/-- Every antitone residue-class sum is at most one initial weight larger than
any other residue-class sum. -/
theorem antitoneResidueClassSum_le_add
    {A B Q : ℕ} (hQ : 0 < Q) (w : ℕ → ℝ)
    (hw : Antitone w) (hw_nonneg : ∀ i, 0 ≤ w i) (r s : Fin Q) :
    antitoneResidueClassSum A B Q w r ≤
      w A + antitoneResidueClassSum A B Q w s := by
  classical
  let R := antitoneResidueClass A B Q r
  let S := antitoneResidueClass A B Q s
  by_cases hR : R.Nonempty
  · let a := R.min' hR
    have haR : a ∈ R := Finset.min'_mem R hR
    have haA : A ≤ a := (mem_antitoneResidueClass.mp haR).1
    by_cases hrs : r = s
    · subst s
      exact le_add_of_nonneg_left (hw_nonneg A)
    · let d := antitoneResidueGap r s
      have hd : 0 < d ∧ d < Q := antitoneResidueGap_pos_lt hQ hrs
      let P := S.filter fun j => j + d ∈ R.erase a
      have hpair_mem : ∀ i ∈ R.erase a, ∃ j, j ∈ P ∧ j + d = i := by
        intro i hi
        have hiR : i ∈ R := Finset.mem_of_mem_erase hi
        have hia : i ≠ a := (Finset.mem_erase.mp hi).1
        have hale : a ≤ i := Finset.min'_le R i hiR
        have halt : a < i := lt_of_le_of_ne hale (Ne.symm hia)
        have ha_mod : a % Q = r.1 := (mem_antitoneResidueClass.mp haR).2.2
        have hi_mod : i % Q = r.1 := (mem_antitoneResidueClass.mp hiR).2.2
        have hiB : i ≤ B := (mem_antitoneResidueClass.mp hiR).2.1
        have hai : a ≡ i [MOD Q] := by
          change a % Q = i % Q
          rw [ha_mod, hi_mod]
        have haQ_le_i : a + Q ≤ i := hai.add_le_of_lt halt
        have hd_le_i : d ≤ i := by omega
        obtain ⟨j, hij'⟩ := Nat.exists_eq_add_of_le hd_le_i
        have hij : j + d = i := by omega
        have hsd : s.1 + d ≡ r.1 [MOD Q] := by
          change (s.1 + d) % Q = r.1 % Q
          rw [show d = antitoneResidueGap r s by rfl,
            antitoneResidueGap_add_mod hQ hrs, Nat.mod_eq_of_lt r.2]
        have hjd : j + d ≡ r.1 [MOD Q] := by
          rw [hij]
          change i % Q = r.1 % Q
          rw [hi_mod, Nat.mod_eq_of_lt r.2]
        have hres : j ≡ s.1 [MOD Q] :=
          Nat.ModEq.add_right_cancel' d (hjd.trans hsd.symm)
        have hjS : j ∈ S := by
          rw [mem_antitoneResidueClass]
          refine ⟨?_, ?_, ?_⟩
          · omega
          · omega
          · simpa [Nat.ModEq, Nat.mod_eq_of_lt s.2] using hres
        refine ⟨j, ?_, hij⟩
        exact Finset.mem_filter.mpr ⟨hjS, hij ▸ hi⟩
      have hsum_pair :
          (∑ j ∈ P, w (j + d)) = ∑ i ∈ R.erase a, w i := by
        apply Finset.sum_bij (fun j _hj => j + d)
        · intro j hj
          exact (Finset.mem_filter.mp hj).2
        · intro j₁ _hj₁ j₂ _hj₂ h
          omega
        · intro i hi
          rcases hpair_mem i hi with ⟨j, hj, rfl⟩
          exact ⟨j, hj, rfl⟩
        · intro j _hj
          rfl
      have hPsub : P ⊆ S := Finset.filter_subset _ _
      have htail : (∑ i ∈ R.erase a, w i) ≤ ∑ j ∈ S, w j := by
        calc
          (∑ i ∈ R.erase a, w i) = ∑ j ∈ P, w (j + d) := hsum_pair.symm
          _ ≤ ∑ j ∈ P, w j := by
            exact Finset.sum_le_sum fun j _hj => hw (Nat.le_add_right j d)
          _ ≤ ∑ j ∈ S, w j :=
            Finset.sum_le_sum_of_subset_of_nonneg hPsub
              (fun j _hjS _hjT => hw_nonneg j)
      have hhead : w a ≤ w A := hw haA
      have hsplit : (∑ i ∈ R.erase a, w i) + w a = ∑ i ∈ R, w i :=
        Finset.sum_erase_add _ _ haR
      change (∑ i ∈ R, w i) ≤ w A + ∑ i ∈ S, w i
      rw [← hsplit]
      calc
        (∑ i ∈ R.erase a, w i) + w a ≤ (∑ i ∈ S, w i) + w A :=
          add_le_add htail hhead
        _ = w A + ∑ i ∈ S, w i := add_comm _ _
  · have hRempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    change (∑ i ∈ R, w i) ≤ w A + ∑ i ∈ S, w i
    rw [hRempty, Finset.sum_empty]
    exact add_nonneg (hw_nonneg A) (Finset.sum_nonneg fun i _hi => hw_nonneg i)

/-- Sharp pairwise discrepancy bound between two residue-class sums. -/
theorem abs_antitoneResidueClassSum_sub_le
    {A B Q : ℕ} (hQ : 0 < Q) (w : ℕ → ℝ)
    (hw : Antitone w) (hw_nonneg : ∀ i, 0 ≤ w i) (r s : Fin Q) :
    |antitoneResidueClassSum A B Q w r -
      antitoneResidueClassSum A B Q w s| ≤ w A := by
  rw [abs_le]
  constructor
  · linarith [antitoneResidueClassSum_le_add (A := A) (B := B)
      hQ w hw hw_nonneg s r]
  · linarith [antitoneResidueClassSum_le_add (A := A) (B := B)
      hQ w hw hw_nonneg r s]

/-- Summing all normalized residue fibers recovers the full interval weight. -/
theorem sum_antitoneResidueClassSum
    {A B Q : ℕ} (hQ : 0 < Q) (w : ℕ → ℝ) :
    (∑ r : Fin Q, antitoneResidueClassSum A B Q w r) =
      ∑ i ∈ Finset.Icc A B, w i := by
  classical
  let residue : ℕ → Fin Q := fun i => ⟨i % Q, Nat.mod_lt i hQ⟩
  have h := Finset.sum_fiberwise_eq_sum_filter
    (Finset.Icc A B) (Finset.univ : Finset (Fin Q)) residue w
  simpa [antitoneResidueClassSum, antitoneResidueClass, residue, Fin.ext_iff] using h

/-- Full-L1 deviation of normalized residue masses from their uniform average.
The convention is the full sum, with no factor `1/2`. -/
theorem antitoneResidueClassSum_fullL1_le
    {A B Q : ℕ} (hQ : 0 < Q) (w : ℕ → ℝ)
    (hw : Antitone w) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hZ : 0 < ∑ r : Fin Q, antitoneResidueClassSum A B Q w r) :
    (∑ r : Fin Q,
        |antitoneResidueClassSum A B Q w r /
            (∑ s : Fin Q, antitoneResidueClassSum A B Q w s) -
          1 / (Q : ℝ)|) ≤
      (Q : ℝ) * w A /
        (∑ s : Fin Q, antitoneResidueClassSum A B Q w s) := by
  let H : Fin Q → ℝ := antitoneResidueClassSum A B Q w
  let Z : ℝ := ∑ r : Fin Q, H r
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hcenter (r : Fin Q) : |H r - Z / Q| ≤ w A := by
    have hid : H r - Z / Q =
        (1 / (Q : ℝ)) * ∑ s : Fin Q, (H r - H s) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      dsimp [Z]
      field_simp [ne_of_gt hQreal]
    rw [hid, abs_mul]
    have hpair :
        ∑ s : Fin Q, |H r - H s| ≤ (Q : ℝ) * w A := by
      calc
        ∑ s : Fin Q, |H r - H s| ≤ ∑ _s : Fin Q, w A := by
          exact Finset.sum_le_sum fun s _hs =>
            abs_antitoneResidueClassSum_sub_le hQ w hw hw_nonneg r s
        _ = (Q : ℝ) * w A := by simp
    calc
      |1 / (Q : ℝ)| * |∑ s : Fin Q, (H r - H s)| ≤
          (1 / (Q : ℝ)) * ∑ s : Fin Q, |H r - H s| := by
        rw [abs_of_pos (one_div_pos.mpr hQreal)]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (one_div_nonneg.mpr hQreal.le)
      _ ≤ (1 / (Q : ℝ)) * ((Q : ℝ) * w A) :=
        mul_le_mul_of_nonneg_left hpair (one_div_nonneg.mpr hQreal.le)
      _ = w A := by field_simp
  have hpoint (r : Fin Q) :
      |H r / Z - 1 / (Q : ℝ)| ≤ w A / Z := by
    have hrewrite : H r / Z - 1 / (Q : ℝ) = (H r - Z / Q) / Z := by
      symm
      rw [sub_div]
      congr 1
      field_simp [ne_of_gt hQreal]
      exact div_self hZ.ne'
    rw [hrewrite, abs_div, abs_of_pos hZ]
    exact div_le_div_of_nonneg_right (hcenter r) hZ.le
  change (∑ r : Fin Q, |H r / Z - 1 / (Q : ℝ)|) ≤ (Q : ℝ) * w A / Z
  calc
    (∑ r : Fin Q, |H r / Z - 1 / (Q : ℝ)|) ≤ ∑ _r : Fin Q, w A / Z :=
      Finset.sum_le_sum fun r _hr => hpoint r
    _ = (Q : ℝ) * w A / Z := by simp [div_eq_mul_inv, mul_assoc]

example :
    antitoneResidueClassSum 1 1 2 (fun _ => (1 : ℝ)) ⟨1, by omega⟩ = 1 := by
  norm_num [antitoneResidueClassSum, antitoneResidueClass]; decide

example :
    antitoneResidueClassSum 1 1 2 (fun _ => (1 : ℝ)) ⟨0, by omega⟩ = 0 := by
  norm_num [antitoneResidueClassSum, antitoneResidueClass]

example :
    antitoneResidueClassSum 4 3 1 (fun _ => (1 : ℝ)) ⟨0, by omega⟩ = 0 := by
  norm_num [antitoneResidueClassSum, antitoneResidueClass]

end Tao
end Erdos1135SecondScale
