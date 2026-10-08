import RationalSubspaceBridge
import TrapCoordinateShear

set_option autoImplicit false
open Filter Finset Module NumberField
open scoped Topology BigOperators Classical

namespace CollatzSubspaceBridge

noncomputable def rationalLocalProduct {ι : Type*} [Fintype ι]
    (S : Finset Nat.Primes)
    (L : AbsoluteValue ℚ ℝ → ι → Dual ℚ (ι → ℚ)) (x : ι → ℤ) : ℝ :=
  (∏ i, |(L Rat.infinitePlace.1 i (fun j ↦ (x j : ℚ)) : ℝ)|) *
    ∏ p ∈ S, ∏ i,
      ((padicNorm (p : ℕ)
        (L (Rat.AbsoluteValue.padic (p : ℕ)) i (fun j ↦ (x j : ℚ))) : ℚ) : ℝ)

theorem not_eventually_small_localProduct_of_trap_ratios {t : ℕ} (ht : 0 < t)
    (S : Finset Nat.Primes)
    (L : AbsoluteValue ℚ ℝ → Fin (t + 1) → Dual ℚ (Fin (t + 1) → ℚ))
    (hLInf : LinearIndependent ℚ (L Rat.infinitePlace.1))
    (hLFin : ∀ p ∈ S, LinearIndependent ℚ (L (Rat.AbsoluteValue.padic (p : ℕ))))
    {ε : ℝ} (hε : 0 < ε)
    (x : ℕ → Fin (t + 1) → ℤ)
    (hb : ∀ᶠ n in atTop, x n 0 - ∑ i : Fin t, x n i.succ ≠ 0)
    (hx : ∀ i : Fin t, ∀ᶠ n in atTop, x n i.succ ≠ 0)
    (hbsmall : ∀ i : Fin t,
      Tendsto
        (fun n ↦ ((x n 0 - ∑ j : Fin t, x n j.succ : ℤ) : ℝ) /
          (x n i.succ : ℝ)) atTop (𝓝 0))
    (hsep : ∀ i j : Fin t, i < j →
      Tendsto (fun n ↦ (x n i.succ : ℝ) / (x n j.succ : ℝ)) atTop (𝓝 0)) :
    ¬ (∀ᶠ n in atTop,
      rationalLocalProduct S L (x n) ≤ (⨆ i, |(x n i : ℝ)|) ^ (-ε)) := by
  have : Nontrivial (Fin (t + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let q : ℕ → Fin (t + 1) → ℚ := fun n i ↦ (x n i : ℚ)
  have hbq : ∀ᶠ n in atTop, q n 0 - ∑ i : Fin t, q n i.succ ≠ 0 := by
    filter_upwards [hb] with n hn
    dsimp [q]
    exact_mod_cast hn
  have hxq : ∀ i : Fin t, ∀ᶠ n in atTop, q n i.succ ≠ 0 := by
    intro i
    filter_upwards [hx i] with n hn
    dsimp [q]
    exact_mod_cast hn
  have hbsmallq : ∀ i : Fin t,
      Tendsto (fun n ↦ ((q n 0 - ∑ j : Fin t, q n j.succ : ℚ) : ℝ) /
        (q n i.succ : ℝ)) atTop (𝓝 0) := by
    intro i
    simpa [q] using hbsmall i
  have hsepq : ∀ i j : Fin t, i < j →
      Tendsto (fun n ↦ (q n i.succ : ℝ) / (q n j.succ : ℝ)) atTop (𝓝 0) := by
    intro i j hij
    simpa [q] using hsep i j hij
  obtain ⟨T, hT, hcover⟩ := rational_integer_subspace_cover S L hLInf hLFin hε
  have havoid := CollatzResearch.eventually_avoids_finite_subspaces_of_trap_ratios
    q hbq hxq hbsmallq hsepq T hT
  have hnonzero : ∀ᶠ n in atTop, q n ≠ 0 := by
    filter_upwards [hbq] with n hn hzero
    apply hn
    rw [hzero]
    simp
  intro hsmall
  obtain ⟨n, hnsmall, hnnonzero, hnavoid⟩ :=
    (hsmall.and (hnonzero.and havoid)).exists
  obtain ⟨W, hWT, hmem⟩ := hcover (x n) hnnonzero hnsmall
  exact hnavoid W hWT hmem

end CollatzSubspaceBridge

#print axioms CollatzSubspaceBridge.not_eventually_small_localProduct_of_trap_ratios
