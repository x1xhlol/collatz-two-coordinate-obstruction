import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
A finite set of carry positions has a constant nonzero support along a strictly
increasing subsequence. The ordered support omits exactly the zero positions
and preserves every sum whose omitted summands vanish.
-/

set_option autoImplicit false

open Filter
open scoped BigOperators

namespace CollatzResearch

theorem exists_strictMono_fixed_support {r : ℕ} {A : Type*} [Zero A]
    (z : ℕ → Fin r → A) :
    ∃ (S : Finset (Fin r)) (sigma : ℕ → ℕ), StrictMono sigma ∧
      ∀ n i, z (sigma n) i ≠ 0 ↔ i ∈ S := by
  classical
  have h : ∃ᶠ n in atTop, ∃ S : Finset (Fin r),
      ∀ i, z n i ≠ 0 ↔ i ∈ S := by
    apply Filter.Frequently.of_forall
    intro n
    exact ⟨Finset.univ.filter (fun i => z n i ≠ 0), by simp⟩
  obtain ⟨S, hS⟩ := Filter.frequently_exists.mp h
  obtain ⟨sigma, hsigma, hsupport⟩ := Filter.extraction_of_frequently_atTop hS
  exact ⟨S, sigma, hsigma, hsupport⟩

theorem exists_strictMono_nonempty_fixed_support {r : ℕ} {A : Type*} [Zero A]
    (z : ℕ → Fin r → A) (hz : ∀ᶠ n in atTop, ∃ i, z n i ≠ 0) :
    ∃ (S : Finset (Fin r)) (sigma : ℕ → ℕ), StrictMono sigma ∧ S.Nonempty ∧
      ∀ n i, z (sigma n) i ≠ 0 ↔ i ∈ S := by
  classical
  have h : ∀ᶠ n in atTop, ∃ S : Finset (Fin r), S.Nonempty ∧
      ∀ i, z n i ≠ 0 ↔ i ∈ S := by
    filter_upwards [hz] with n hn
    obtain ⟨i, hi⟩ := hn
    refine ⟨Finset.univ.filter (fun j => z n j ≠ 0), ?_, by simp⟩
    exact ⟨i, by simp [hi]⟩
  obtain ⟨S, hS⟩ := Filter.frequently_exists.mp h.frequently
  obtain ⟨sigma, hsigma, hsupport⟩ := Filter.extraction_of_frequently_atTop hS
  exact ⟨S, sigma, hsigma, (hsupport 0).1, fun n => (hsupport n).2⟩

theorem ordered_support_index_strictMono {r : ℕ} (S : Finset (Fin r)) :
    StrictMono (fun i : Fin S.card => (S.orderEmbOfFin rfl i : ℕ)) := by
  intro i j hij
  exact (S.orderEmbOfFin rfl).strictMono hij

theorem ordered_support_coordinates_ne_zero {r : ℕ} {A : Type*} [Zero A]
    (z : ℕ → Fin r → A) (S : Finset (Fin r)) (sigma : ℕ → ℕ)
    (hsupport : ∀ n i, z (sigma n) i ≠ 0 ↔ i ∈ S) :
    ∀ n (i : Fin S.card), z (sigma n) (S.orderEmbOfFin rfl i) ≠ 0 := by
  intro n i
  exact (hsupport n _).mpr (S.orderEmbOfFin_mem rfl i)

theorem sum_eq_sum_ordered_support {r : ℕ} {A : Type*} [AddCommMonoid A]
    (S : Finset (Fin r)) (w : Fin r → A) (hzero : ∀ i, i ∉ S → w i = 0) :
    (∑ i, w i) = ∑ j : Fin S.card, w (S.orderEmbOfFin rfl j) := by
  have hsum : (∑ i ∈ S, w i) = ∑ j : Fin S.card, w (S.orderEmbOfFin rfl j) := by
    calc
      (∑ i ∈ S, w i) =
          ∑ i ∈ Finset.univ.map (S.orderEmbOfFin rfl).toEmbedding, w i := by
            rw [S.map_orderEmbOfFin_univ rfl]
      _ = _ := by rw [Finset.sum_map]; rfl
  exact (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hzero i hi)).symm.trans hsum

/-- The carry coefficient support may also select different summands, provided
a zero coefficient forces its corresponding summand to vanish. -/
theorem sum_eq_sum_selected_of_fixed_support {r : ℕ} {A B : Type*}
    [Zero A] [AddCommMonoid B] (z : ℕ → Fin r → A) (w : ℕ → Fin r → B)
    (S : Finset (Fin r)) (sigma : ℕ → ℕ)
    (hsupport : ∀ n i, z (sigma n) i ≠ 0 ↔ i ∈ S)
    (hzero : ∀ n i, z n i = 0 → w n i = 0) :
    ∀ n, (∑ i, w (sigma n) i) =
      ∑ j : Fin S.card, w (sigma n) (S.orderEmbOfFin rfl j) := by
  classical
  intro n
  apply sum_eq_sum_ordered_support
  intro i hi
  apply hzero
  by_contra hn
  exact hi ((hsupport n i).mp hn)

end CollatzResearch

#print axioms CollatzResearch.exists_strictMono_fixed_support
#print axioms CollatzResearch.exists_strictMono_nonempty_fixed_support
#print axioms CollatzResearch.ordered_support_index_strictMono
#print axioms CollatzResearch.ordered_support_coordinates_ne_zero
#print axioms CollatzResearch.sum_eq_sum_ordered_support
#print axioms CollatzResearch.sum_eq_sum_selected_of_fixed_support
