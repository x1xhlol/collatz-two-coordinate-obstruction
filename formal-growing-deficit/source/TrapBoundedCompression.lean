import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace CollatzResearch

theorem exists_ordered_nat_support (r : ℕ) (S : Finset ℕ) (hS : S.Nonempty)
    (hsub : S ⊆ Finset.range (r + 1)) :
    ∃ (t : ℕ) (I : ℕ → ℕ),
      (∀ i ≤ t, I i ∈ S) ∧
      (∀ i j, i < j → j ≤ t → I i < I j) ∧
      (∀ a ∈ S, ∃ i ≤ t, I i = a) ∧
      (∀ i ≤ t, I i ≤ r) := by
  classical
  have hcard : 0 < S.card := Finset.card_pos.mpr hS
  let t := S.card - 1
  let E : Fin S.card ↪o ℕ := S.orderEmbOfFin rfl
  let I (i : ℕ) : ℕ := if hi : i < S.card then E ⟨i, hi⟩ else E ⟨0, hcard⟩
  have hmem : ∀ i ≤ t, I i ∈ S := by
    intro i hi
    have hic : i < S.card := by dsimp [t] at hi; omega
    simp only [I, dite_eq_left hic]
    exact S.orderEmbOfFin_mem rfl ⟨i, hic⟩
  refine ⟨t, I, hmem, ?_, ?_, ?_⟩
  · intro i j hij hj
    have hjc : j < S.card := by dsimp [t] at hj; omega
    have hic : i < S.card := by omega
    simp only [I, dite_eq_left hic, dite_eq_left hjc]
    exact E.strictMono hij
  · intro a ha
    let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨a, ha⟩
    have hja : E j = a := by
      have hh := (S.orderIsoOfFin rfl).apply_symm_apply ⟨a, ha⟩
      exact congrArg Subtype.val hh
    refine ⟨j, ?_, ?_⟩
    · dsimp [t]
      have := j.isLt
      omega
    · simpa only [I, dite_eq_left j.isLt, Fin.eta] using hja
  · intro i hi
    have hb := Finset.mem_range.mp (hsub (hmem i hi))
    omega

theorem ordered_support_le {t : ℕ} {I : ℕ → ℕ}
    (hmono : ∀ i j, i < j → j ≤ t → I i < I j)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ t) : I i ≤ I j := by
  rcases lt_or_eq_of_le hij with hij | rfl
  · exact (hmono i j hij hj).le
  · exact le_rfl

theorem support_gap_not_mem (S : Finset ℕ) (t : ℕ) (I : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j ≤ t → I i < I j)
    (honto : ∀ a ∈ S, ∃ j ≤ t, I j = a)
    {i a : ℕ} (hi : i < t) (hia : I i < a) (hai : a < I (i + 1)) :
    a ∉ S := by
  intro ha
  obtain ⟨j, hj, hja⟩ := honto a ha
  by_cases hji : j ≤ i
  · have hb := ordered_support_le hmono hji (by omega)
    omega
  · have hb := ordered_support_le hmono (show i + 1 ≤ j by omega) hj
    omega

theorem support_before_first_not_mem (S : Finset ℕ) (t : ℕ) (I : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j ≤ t → I i < I j)
    (honto : ∀ b ∈ S, ∃ j ≤ t, I j = b)
    {a : ℕ} (ha : a < I 0) : a ∉ S := by
  intro hmem
  obtain ⟨j, hj, hja⟩ := honto a hmem
  have hb := ordered_support_le hmono (Nat.zero_le j) hj
  omega

theorem support_after_last_not_mem (S : Finset ℕ) (t : ℕ) (I : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j ≤ t → I i < I j)
    (honto : ∀ b ∈ S, ∃ j ≤ t, I j = b)
    {a : ℕ} (ha : I t < a) : a ∉ S := by
  intro hmem
  obtain ⟨j, hj, hja⟩ := honto a hmem
  have hb := ordered_support_le hmono hj le_rfl
  omega

theorem sum_ordered_support_le_range (r t : ℕ) (I m : ℕ → ℕ)
    (hbound : ∀ i ≤ t, I i ≤ r)
    (hmono : ∀ i j, i < j → j ≤ t → I i < I j) :
    ∑ i ∈ Finset.range (t + 1), m (I i) ≤ ∑ i ∈ Finset.range (r + 1), m i := by
  have hinj : Set.InjOn I (Finset.range (t + 1)) := by
    intro i hi j hj hij
    have hi' : i ≤ t := by have := Finset.mem_range.mp hi; omega
    have hj' : j ≤ t := by have := Finset.mem_range.mp hj; omega
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have := hmono i j hlt hj'
      omega
    · exact heq
    · have := hmono j i hgt hi'
      omega
  have hsub : (Finset.range (t + 1)).image I ⊆ Finset.range (r + 1) := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr (by
      have := hbound i (by have := Finset.mem_range.mp hi; omega)
      omega)
  rw [← Finset.sum_image hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

end CollatzResearch

#print axioms CollatzResearch.exists_ordered_nat_support
#print axioms CollatzResearch.support_gap_not_mem
#print axioms CollatzResearch.support_before_first_not_mem
#print axioms CollatzResearch.support_after_last_not_mem
#print axioms CollatzResearch.sum_ordered_support_le_range
