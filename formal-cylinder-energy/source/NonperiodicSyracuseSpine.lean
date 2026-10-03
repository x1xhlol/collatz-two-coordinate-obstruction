import CylinderForwardPropagation
import ComponentPositivityEquivalences
import ShortcutMinimumCapture

set_option autoImplicit false
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao CollatzCanonical.ForwardComponent
open CollatzCanonical.LabelLaw Erdos1135

noncomputable section

theorem syracuse_is_unit (u : ℕ) : (Tao.syracuse u) % 3 ≠ 0 := by
  intro hz
  have hd : 3 ∣ 3 * u + 1 := by
    rw [← Tao.two_pow_syracuseExponent_mul_syracuse u]
    exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero hz) _
  omega

theorem syracuse_le_two_mul {u : ℕ} (hu : Odd u) : Tao.syracuse u ≤ 2 * u := by
  have hup : 0 < u := by obtain ⟨t, ht⟩ := hu; omega
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Tao.syracuseExponent_pos_of_odd hu))
  have hid := Tao.two_pow_syracuseExponent_mul_syracuse u
  rw [ha, pow_succ] at hid
  have hp : 0 < 2 ^ a := by positivity
  nlinarith

theorem syracuse_iterate_le_two_pow {u : ℕ} (hu : Odd u) (j : ℕ) :
    (Tao.syracuse^[j]) u ≤ 2 ^ j * u := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hs := syracuse_le_two_mul (Tao.syracuse_iterate_odd j u hu)
    rw [pow_succ]
    nlinarith

theorem syracuse_spine_injective {u : ℕ} (hu : Odd u)
    (hinj : Function.Injective (fun i => iterate i u)) :
    Function.Injective (fun j => (Tao.syracuse^[j]) u) := by
  intro i j hij
  apply (syracuse_clock_strictMono u hu).injective
  apply hinj
  simpa only [syracuse_shortcut_landing] using hij

theorem syracuse_spine_nonperiodic {u : ℕ} (hu : Odd u)
    (hinj : Function.Injective (fun i => iterate i u)) (j : ℕ) :
    ¬ ∃ r : ℕ, 0 < r ∧ iterate r ((Tao.syracuse^[j]) u) = (Tao.syracuse^[j]) u := by
  rintro ⟨r, hr, he⟩
  apply shortcut_component_target_nonperiodic (q := (Tao.syracuse^[j]) u)
    (n := u) ?_ hinj r hr he
  exact ⟨0, Tao.taoTupleWeight (Tao.syracuseValuationPNatList j u hu),
    (syracuse_shortcut_landing j u hu).symm⟩

/-- An odd unit root can be chosen on every injective positive shortcut orbit. -/
theorem exists_odd_unit_injective_root {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) :
    ∃ u : ℕ, Odd u ∧ u % 3 ≠ 0 ∧ Function.Injective (fun i => iterate i u) := by
  let q := ordCompl[2] n
  have hq : Odd q := ordCompl_two_odd hn
  let u := Tao.syracuse q
  refine ⟨u, Tao.syracuse_odd q, syracuse_is_unit q, ?_⟩
  apply shortcut_component_injective (n := n) ?_ hinj
  refine ⟨0, n.factorization 2 + Tao.taoTupleWeight (Tao.syracuseValuationPNatList 1 q hq), ?_⟩
  rw [iterate_add, shortcut_reaches_initial_oddPart]
  change u = iterate (Tao.taoTupleWeight (Tao.syracuseValuationPNatList 1 q hq)) q
  rw [syracuse_shortcut_landing]
  rfl

/-- A fixed depth shift puts the first K+1 distinct odd states inside the positive head. -/
theorem syracuse_spine_head_bound {u : ℕ} (hu : Odd u) {C : ℕ} (hC : u ≤ 3 ^ C)
    {K j : ℕ} (hj : j ≤ K) : (Tao.syracuse^[j]) u ≤ 3 ^ (K + C) := by
  calc
    (Tao.syracuse^[j]) u ≤ 2 ^ j * u := syracuse_iterate_le_two_pow hu j
    _ ≤ 3 ^ K * 3 ^ C := Nat.mul_le_mul
      ((Nat.pow_le_pow_left (by decide : 2 ≤ 3) j).trans
        (Nat.pow_le_pow_right (by decide : 1 ≤ 3) hj)) hC
    _ = 3 ^ (K + C) := (pow_add 3 K C).symm

#print axioms exists_odd_unit_injective_root
#print axioms syracuse_spine_injective
#print axioms syracuse_spine_nonperiodic
#print axioms syracuse_spine_head_bound
end
end CollatzCanonical.PeriodicCensusFloor
