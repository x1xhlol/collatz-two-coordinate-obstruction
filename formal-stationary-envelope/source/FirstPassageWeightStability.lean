import FirstHitWeightTransport

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

theorem firstHit_prefix_injective {A q N : ℕ} (hfirst : FirstHit q N A) :
    Set.InjOn (fun i => iterate i q) (Finset.range A) := by
  have hno (i j : ℕ) (hi : i < A) (hj : j < A) (hij : i < j)
      (he : iterate i q = iterate j q) : False := by
    have ht := congrArg (iterate (A - j)) he
    rw [← iterate_add, ← iterate_add, Nat.add_sub_of_le (by omega : j ≤ A), hfirst.1] at ht
    exact hfirst.2 (i + (A - j)) (by omega) ht
  intro i hi j hj he
  have hiA := Finset.mem_range.mp hi
  have hjA := Finset.mem_range.mp hj
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (hno i j hiA hjA hij he)
  · exact hij
  · exact False.elim (hno j i hjA hiA hij he.symm)

/-- An actual shortcut prefix ending at the first odd state at or below M.
Even intermediate states are permitted below M. -/
structure OddBarrierPassage (q A : ℕ) (M : ℝ) : Prop where
  landing_odd : iterate A q % 2 = 1
  landing_le : (iterate A q : ℝ) ≤ M
  prefix_high : ∀ i < A, iterate i q % 2 = 1 → M < (iterate i q : ℝ)

theorem OddBarrierPassage.first_hit {q A : ℕ} {M : ℝ} (h : OddBarrierPassage q A M) :
    FirstHit q (iterate A q) A := by
  refine ⟨rfl, ?_⟩
  intro i hi he
  have ho : iterate i q % 2 = 1 := by rw [he]; exact h.landing_odd
  have hh := h.prefix_high i hi ho
  rw [he] at hh
  linarith [h.landing_le]

theorem OddBarrierPassage.prefix_injective {q A : ℕ} {M : ℝ}
    (h : OddBarrierPassage q A M) :
    Set.InjOn (fun i => iterate i q) (Finset.range A) :=
  firstHit_prefix_injective h.first_hit

/-- Once a passage prefix visits a target below the barrier, all remaining
steps up to the odd landing are halvings, so the landing cannot exceed that target. -/
theorem OddBarrierPassage.landing_le_of_prefix_hit {q A N i : ℕ} {M : ℝ}
    (h : OddBarrierPassage q A M) (hN : (N : ℝ) ≤ M)
    (hi : i ≤ A) (hhit : iterate i q = N) : iterate A q ≤ N := by
  have hb (d : ℕ) : i + d ≤ A → iterate (i + d) q ≤ N := by
    induction d with
    | zero => intro _; simp [hhit]
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      have heven : iterate (i + d) q % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one (iterate (i + d) q) with he | ho
        · exact he
        · have hhigh := h.prefix_high (i + d) (by omega) ho
          have hn : (iterate (i + d) q : ℝ) ≤ N := by exact_mod_cast hprev
          linarith
      have hs : step (iterate (i + d) q) ≤ iterate (i + d) q := by
        have he := step_even heven
        omega
      change iterate ((i + d) + 1) q ≤ N
      exact hs.trans hprev
  have hh := hb (A - i) (by omega)
  simpa only [Nat.add_sub_of_le hi] using hh

theorem OddBarrierPassage.prefix_avoids_of_landing_gt {q A N : ℕ} {M : ℝ}
    (h : OddBarrierPassage q A M) (hN : (N : ℝ) ≤ M) (hland : N < iterate A q) :
    ∀ i < A, iterate i q ≠ N := by
  intro i hi he
  have hb := h.landing_le_of_prefix_hit hN (by omega : i ≤ A) he
  omega

/-- The actual first-hit observable changes by at most C M^(b-1) under every
successful odd-barrier passage whose landing is above the target. -/
theorem firstHitWeight_uniform_barrier_stability (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A q N : ℕ) (M : ℝ), 0 < q → 1 ≤ M → (N : ℝ) ≤ M →
      OddBarrierPassage q A M → N < iterate A q →
      |firstHitWeight N q - firstHitWeight N (iterate A q)| ≤ C * M ^ (b - 1) := by
  obtain ⟨C, hC, htransport⟩ := firstHitWeight_uniform_prefix_transport b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro A q N M hq hM hN hpass hland
  exact htransport A q N hq (hpass.prefix_avoids_of_landing_gt hN hland)
    hpass.prefix_injective M hM (fun i hi ho => (hpass.prefix_high i hi ho).le)

#print axioms firstHit_prefix_injective
#print axioms OddBarrierPassage.landing_le_of_prefix_hit
#print axioms firstHitWeight_uniform_barrier_stability

end CollatzCylinderPacking.Arithmetic
