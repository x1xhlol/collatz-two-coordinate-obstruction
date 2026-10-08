import ShortcutOddEndpoints

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- A positive target has no positive backward ancestor below this barrier. -/
def NoSmallAncestor (v : ℕ) (M : ℝ) : Prop :=
  ∀ q : ℕ, 0 < q → (q : ℝ) ≤ M → ¬ ∃ K, iterate K q = v

theorem iterate_initial_halving (h u i : ℕ) (hi : i ≤ h) :
    iterate i (2 ^ h * u) = 2 ^ (h - i) * u := by
  induction h generalizing i with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    simp [iterate]
  | succ h ih =>
    cases i with
    | zero => simp [iterate]
    | succ i =>
      have hs : iterate 1 (2 ^ (h + 1) * u) = 2 ^ h * u := by
        have he : 2 ^ (h + 1) * u = 2 * (2 ^ h * u) := by rw [pow_succ]; ring
        rw [he]
        exact step_two_mul _
      rw [show i + 1 = 1 + i by omega, iterate_add, hs, ih i (by omega)]
      congr 2
      omega

theorem initial_halving_prefix_even (h u i : ℕ) (hi : i < h) :
    Even (iterate i (2 ^ h * u)) := by
  rw [iterate_initial_halving h u i hi.le]
  have hd : h - i = (h - i - 1) + 1 := by omega
  rw [hd, pow_succ]
  exact even_iff_two_dvd.mpr ⟨2 ^ (h - i - 1) * u, by ring⟩

theorem noSmallAncestor_prefix_above {v q K : ℕ} {M : ℝ}
    (hno : NoSmallAncestor v M) (hq : 0 < q) (hhit : iterate K q = v) :
    ∀ i ≤ K, M < (iterate i q : ℝ) := by
  intro i hi
  by_contra h
  apply hno (iterate i q) (CollatzCanonical.Correction.iterate_pos i hq) (le_of_not_gt h)
  refine ⟨K - i, ?_⟩
  rw [← iterate_add, Nat.add_sub_of_le hi]
  exact hhit

end CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.NativeTao
open Erdos1135 CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

/-- All odd starts in a basin without a small ancestor lie in one atom of
the actual total passage map. The atom at one also covers failed passages. -/
theorem noSmallAncestor_odd_basin_in_passage_atom {v : ℕ} (hv : 0 < v)
    {M : ℝ} (hM : 1 ≤ M) (hno : NoSmallAncestor v M) :
    ∃ m : ℕ, ∀ q : ℕ, Odd q → (∃ K, iterate K q = v) →
      (Tao.syracusePassLocationRealFloorOrOne M q hM).val = m := by
  obtain ⟨h, u, hu, hvu⟩ := Nat.exists_eq_two_pow_mul_odd hv.ne'
  let hB := Tao.one_le_floor_of_one_le hM
  refine ⟨(Tao.syracusePassLocationAtMostOrOne (Nat.floor M) u hB).val, ?_⟩
  intro q hq hhit
  obtain ⟨K, hK⟩ := hhit
  have hland : iterate (K + h) q = u := by
    rw [iterate_add, hK, hvu, iterate_initial_halving h u h le_rfl]
    simp
  have hpre : ∀ i < K + h, Odd (iterate i q) → Nat.floor M < iterate i q := by
    intro i hi hodd
    by_cases hiK : i < K
    · have hhigh := noSmallAncestor_prefix_above hno hq.pos hK i hiK.le
      have hfloor : ((Nat.floor M : ℕ) : ℝ) ≤ M := Nat.floor_le (by linarith)
      exact_mod_cast hfloor.trans_lt hhigh
    · have hKi : K ≤ i := Nat.le_of_not_gt hiK
      have he : iterate i q = iterate (i - K) (2 ^ h * u) := by
        rw [← hvu, ← hK, ← iterate_add, Nat.add_sub_of_le hKi]
      have heven := initial_halving_prefix_even h u (i - K) (by omega)
      exact False.elim ((Nat.not_even_iff_odd.mpr hodd) (by rwa [he]))
  have hp := pass_preserved_after_shortcut_odd_landing hB hq hu hland hpre
  exact congrArg Subtype.val hp

#print axioms noSmallAncestor_odd_basin_in_passage_atom

end CollatzCanonical.NativeTao
