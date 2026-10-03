import FirstHitCutCapacity

set_option autoImplicit false
open Filter Topology Classical
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao Erdos1135

noncomputable section

def SyrFirstHit (q N k : ℕ) : Prop :=
  (Tao.syracuse^[k]) q = N ∧ ∀ j < k, (Tao.syracuse^[j]) q ≠ N

theorem syrFirstHit_iff_shortcut_firstHit {q N k : ℕ} (hq : Odd q) (hN : Odd N) :
    SyrFirstHit q N k ↔
      FirstHit q N (Tao.taoTupleWeight (Tao.syracuseValuationPNatList k q hq)) := by
  constructor
  · rintro ⟨hland, havoid⟩
    refine ⟨by simpa only [syracuse_shortcut_landing] using hland, ?_⟩
    intro i hi he
    have ho : Odd ((Terras.accelerated^[i]) q) := by
      rw [← iterate_eq_native, he]
      exact hN
    obtain ⟨j, hj, hij⟩ := odd_shortcut_index_is_syracuse_clock k q hq i hi ho
    apply havoid j hj
    simpa only [hij, syracuse_shortcut_landing] using he
  · intro hf
    refine ⟨by simpa only [syracuse_shortcut_landing] using hf.1, ?_⟩
    intro j hj he
    apply hf.2 _ (syracuse_clock_strictMono q hq hj)
    simpa only [syracuse_shortcut_landing] using he

theorem shortcut_firstHit_odd_depth_iff_syrFirstHit {q N k : ℕ}
    (hq : Odd q) (hN : Odd N) :
    (∃ A, FirstHit q N A ∧ oddCount A q = k) ↔ SyrFirstHit q N k := by
  constructor
  · rintro ⟨A, hfirst, hdepth⟩
    obtain ⟨j, hj⟩ := shortcut_odd_endpoint_is_syracuse_clock A q hq
      (by simpa only [hfirst.1] using hN)
    have hjk : j = k := by
      simpa only [hj, syracuse_shortcut_oddCount] using hdepth
    subst j
    exact (syrFirstHit_iff_shortcut_firstHit hq hN).mpr (by simpa only [← hj] using hfirst)
  · intro hf
    exact ⟨_, (syrFirstHit_iff_shortcut_firstHit hq hN).mp hf,
      syracuse_shortcut_oddCount k q hq⟩

theorem syrFirstHit_succ_iff (q N k : ℕ) :
    SyrFirstHit q N (k + 1) ↔ q ≠ N ∧ SyrFirstHit (Tao.syracuse q) N k := by
  constructor
  · rintro ⟨hland, havoid⟩
    refine ⟨by simpa using havoid 0 (Nat.zero_lt_succ k), ?_, ?_⟩
    · simpa only [Function.iterate_succ_apply] using hland
    · intro j hj
      simpa only [Function.iterate_succ_apply] using havoid (j + 1) (by omega)
  · rintro ⟨hne, hland, havoid⟩
    refine ⟨by simpa only [Function.iterate_succ_apply] using hland, ?_⟩
    intro j hj
    cases j with
    | zero => simpa using hne
    | succ j => simpa only [Function.iterate_succ_apply] using havoid j (by omega)

theorem syrFirstHit_prepend_nonperiodic {q y N k : ℕ}
    (hq : Odd q) (hnext : Tao.syracuse q = y)
    (hf : SyrFirstHit y N k)
    (hnp : ¬ ∃ r : ℕ, 0 < r ∧ iterate r q = q) :
    SyrFirstHit q N (k + 1) := by
  apply (syrFirstHit_succ_iff q N k).mpr
  refine ⟨?_, by simpa only [hnext] using hf⟩
  intro he
  have hreturn : (Tao.syracuse^[k + 1]) q = q := by
    rw [Function.iterate_succ_apply, hnext]
    exact hf.1.trans he.symm
  apply hnp
  refine ⟨Tao.taoTupleWeight (Tao.syracuseValuationPNatList (k + 1) q hq),
    (Nat.zero_lt_succ k).trans_le (le_syracuse_clock (k + 1) q hq), ?_⟩
  simpa only [syracuse_shortcut_landing] using hreturn

theorem syrFirstHit_coefficient {q N k : ℕ} (hq : Odd q) (hN : Odd N)
    (hf : SyrFirstHit q N k) :
    (N : ℝ) * firstHitWeight N q / q =
      (3 : ℝ) ^ k * (1 / 2 : ℝ) ^
        Tao.taoTupleWeight (Tao.syracuseValuationPNatList k q hq) := by
  have hp : 0 < q := by have := hq.pos; exact this
  have hh := first_hit_weight hp ((syrFirstHit_iff_shortcut_firstHit hq hN).mp hf)
  simpa only [syracuse_shortcut_oddCount] using hh.symm

theorem syrFirstHit_coefficient_succ {q N k : ℕ} (hq : Odd q) (hN : Odd N)
    (hf : SyrFirstHit q N (k + 1)) :
    (N : ℝ) * firstHitWeight N q / q =
      (3 * (1 / 2 : ℝ) ^ Tao.syracuseExponent q) *
        ((N : ℝ) * firstHitWeight N (Tao.syracuse q) / Tao.syracuse q) := by
  rw [syrFirstHit_coefficient hq hN hf,
    syrFirstHit_coefficient (Tao.syracuse_odd q) hN ((syrFirstHit_succ_iff q N k).mp hf).2]
  have hclock : Tao.taoTupleWeight (Tao.syracuseValuationPNatList (k + 1) q hq) =
      Tao.syracuseExponent q + Tao.taoTupleWeight
        (Tao.syracuseValuationPNatList k (Tao.syracuse q) (Tao.syracuse_odd q)) := by
    simp [Tao.syracuseValuationPNatList, Tao.taoTupleWeight]
  rw [hclock, pow_add, pow_succ]
  ring

theorem syracuse_predecessor_exponent_injective (y : ℕ) :
    Set.InjOn Tao.syracuseExponent {q : ℕ | Tao.syracuse q = y} := by
  intro q hq r hr he
  have hqeq := Tao.two_pow_syracuseExponent_mul_syracuse q
  have hreq := Tao.two_pow_syracuseExponent_mul_syracuse r
  rw [hq, he] at hqeq
  rw [hr] at hreq
  omega

theorem syracuse_not_dvd_three (q : ℕ) : Tao.syracuse q % 3 ≠ 0 := by
  intro hz
  have h := congrArg (fun n : ℕ => n % 3) (Tao.two_pow_syracuseExponent_mul_syracuse q)
  simp [Nat.mul_mod, Nat.add_mod, hz] at h

#print axioms shortcut_firstHit_odd_depth_iff_syrFirstHit
#print axioms syrFirstHit_coefficient_succ
end
end CollatzCanonical.PeriodicCensusFloor
