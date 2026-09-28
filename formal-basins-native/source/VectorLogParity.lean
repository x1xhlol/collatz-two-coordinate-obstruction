import OddVectorWindows

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.BanachWindow
open CollatzCanonical.DirichletAbelian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def fullVectorCumulative (F : ℕ → V) (t : ℝ) : V :=
  ∑ n ∈ Finset.range ⌊Real.exp t⌋₊, (1 / (n + 1 : ℕ) : ℝ) • F (n + 1)

noncomputable def vectorLogTerm (F : ℕ → V) (t : ℝ) (q : ℕ) : V :=
  if Real.log (q : ℝ) ≤ t then (1 / (q : ℝ)) • F q else 0

noncomputable def oddVectorRestriction (F : ℕ → V) (q : ℕ) : V :=
  if q % 2 = 1 then F q else 0

theorem vectorLogTerm_zero (F : ℕ → V) (t : ℝ) : vectorLogTerm F t 0 = 0 := by
  simp [vectorLogTerm]

theorem vectorLogTerm_support (F : ℕ → V) (t : ℝ) {q : ℕ}
    (hq : q ∉ Finset.range (⌊Real.exp t⌋₊ + 1)) : vectorLogTerm F t q = 0 := by
  by_cases hzero : q = 0
  · rw [hzero, vectorLogTerm_zero]
  · have hpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hzero
    unfold vectorLogTerm
    apply if_neg
    intro hlog
    apply hq
    rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (Real.exp_pos t).le,
      ← Real.log_le_iff_le_exp hpos]
    exact hlog

theorem vectorLogTerm_summable (F : ℕ → V) (t : ℝ) : Summable (vectorLogTerm F t) := by
  exact summable_of_ne_finset_zero (fun q hq => vectorLogTerm_support F t hq)

theorem vectorLogTerm_tsum (F : ℕ → V) (t : ℝ) :
    (∑' q, vectorLogTerm F t q) = fullVectorCumulative F t := by
  rw [tsum_eq_sum (fun q hq => vectorLogTerm_support F t hq), Finset.sum_range_succ', vectorLogTerm_zero, add_zero]
  apply Finset.sum_congr rfl
  intro n hn
  have hpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlog : Real.log (n + 1 : ℕ) ≤ t := by
    rw [Real.log_le_iff_le_exp hpos]
    exact (Nat.le_floor_iff (Real.exp_pos t).le).mp (by simpa using hn)
  rw [vectorLogTerm, if_pos hlog]

theorem vectorLogTerm_even_odd [CompleteSpace V] (F : ℕ → V) (t : ℝ) :
    (∑' q, vectorLogTerm F t (2 * q)) + (∑' q, vectorLogTerm F t (2 * q + 1)) =
      fullVectorCumulative F t := by
  have he : Summable (fun q => vectorLogTerm F t (2 * q)) :=
    (vectorLogTerm_summable F t).comp_injective (by intro a b h; omega)
  have ho : Summable (fun q => vectorLogTerm F t (2 * q + 1)) :=
    (vectorLogTerm_summable F t).comp_injective (by
      intro a b h
      change 2 * a + 1 = 2 * b + 1 at h
      omega)
  rw [tsum_even_add_odd he ho, vectorLogTerm_tsum]

theorem fullVectorCumulative_oddRestriction (F : ℕ → V) (t : ℝ) :
    fullVectorCumulative (oddVectorRestriction F) t = oddVectorCumulative F t := by
  unfold fullVectorCumulative oddVectorCumulative
  apply Finset.sum_congr rfl
  intro n _
  unfold oddVectorRestriction oddVectorTerm
  split_ifs <;> simp

theorem oddVectorCumulative_eq_tsum [CompleteSpace V] (F : ℕ → V) (t : ℝ) :
    (∑' q, vectorLogTerm F t (2 * q + 1)) = oddVectorCumulative F t := by
  have h := vectorLogTerm_even_odd (oddVectorRestriction F) t
  have he (q : ℕ) : vectorLogTerm (oddVectorRestriction F) t (2 * q) = 0 := by
    simp [vectorLogTerm, oddVectorRestriction]
  have ho (q : ℕ) : vectorLogTerm (oddVectorRestriction F) t (2 * q + 1) =
      vectorLogTerm F t (2 * q + 1) := by
    simp [vectorLogTerm, oddVectorRestriction]
  simpa only [he, ho, tsum_zero, zero_add, fullVectorCumulative_oddRestriction] using h

theorem vectorLogTerm_even (F : ℕ → V) (t : ℝ) (q : ℕ) :
    vectorLogTerm F t (2 * q) = (1 / 2 : ℝ) •
      vectorLogTerm (fun n => F (2 * n)) (t - Real.log 2) q := by
  by_cases hzero : q = 0
  · simp only [hzero, mul_zero, vectorLogTerm_zero, smul_zero]
  · have hq : (q : ℝ) ≠ 0 := by exact_mod_cast hzero
    have hiff : Real.log (2 * q : ℕ) ≤ t ↔ Real.log (q : ℝ) ≤ t - Real.log 2 := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq]
      constructor <;> intro h <;> linarith
    unfold vectorLogTerm
    by_cases hlog : Real.log (q : ℝ) ≤ t - Real.log 2
    · rw [if_pos (hiff.mpr hlog), if_pos hlog, Nat.cast_mul, Nat.cast_ofNat, smul_smul]
      congr 1
      ring
    · rw [if_neg (mt hiff.mp hlog), if_neg hlog, smul_zero]

theorem fullVectorCumulative_parity [CompleteSpace V] (F : ℕ → V) (t : ℝ) :
    fullVectorCumulative F t = oddVectorCumulative F t +
      (1 / 2 : ℝ) • fullVectorCumulative (fun q => F (2 * q)) (t - Real.log 2) := by
  rw [← vectorLogTerm_even_odd F t, oddVectorCumulative_eq_tsum]
  simp_rw [vectorLogTerm_even]
  rw [(vectorLogTerm_summable (fun n => F (2 * n)) (t - Real.log 2)).tsum_const_smul, vectorLogTerm_tsum, add_comm]

theorem fullVectorCumulative_congr_positive {F G : ℕ → V}
    (h : ∀ q : ℕ, 0 < q → F q = G q) (t : ℝ) :
    fullVectorCumulative F t = fullVectorCumulative G t := by
  apply Finset.sum_congr rfl
  intro n _
  rw [h (n + 1) (by omega)]

theorem fullVectorCumulative_growth {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) : ‖fullVectorCumulative F t‖ ≤ t + 1 := by
  have hb := logarithmicCumulative_linear_bound
    (w := fun _ => (1 : ℝ)) (fun _ => by norm_num) (fun _ => by norm_num) ht
  calc
    ‖fullVectorCumulative F t‖ ≤
        ∑ n ∈ Finset.range ⌊Real.exp t⌋₊, ‖(1 / (n + 1 : ℕ) : ℝ) • F (n + 1)‖ := norm_sum_le _ _
    _ ≤ logarithmicCumulative (fun _ => 1) t :=
      Finset.sum_le_sum (fun n _ => norm_reciprocal_smul_le hF (n + 1))
    _ ≤ t + 1 := (le_abs_self _).trans hb

end CollatzCanonical.BanachWindow

#print axioms CollatzCanonical.BanachWindow.fullVectorCumulative_parity
#print axioms CollatzCanonical.BanachWindow.fullVectorCumulative_growth
