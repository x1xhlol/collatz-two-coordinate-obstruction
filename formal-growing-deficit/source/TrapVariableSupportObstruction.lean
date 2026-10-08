import TrapEntropyObstruction
import TrapSlopeAsymptotics
import TrapPatternSelection

set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace CollatzResearch

theorem eventually_nonzero_trap_coefficient_of_saving {r : ℕ}
    (x : ℕ → Fin (r + 1) → ℤ)
    (a : ℕ → ℤ) (D : ℕ → ℕ) (z : ℕ → Fin r → ℤ)
    (p s : ℕ → Fin r → ℕ) (N : ℕ → ℝ)
    (hhead : ∀ n, x n 0 = 2 ^ D n * a n)
    (htail : ∀ n (i : Fin r), x n i.succ = z n i * 2 ^ p n i * 3 ^ s n i)
    (hb : ∀ᶠ n in atTop, x n 0 - ∑ i : Fin r, x n i.succ ≠ 0)
    {eta : ℝ} (heta : 0 < eta) (hN : Tendsto N atTop atTop)
    (hsaving : ∀ᶠ n in atTop,
      |((x n 0 - ∑ i : Fin r, x n i.succ : ℤ) : ℝ)| / (2 : ℝ) ^ D n ≤
        Real.exp (-eta * N n)) :
    ∀ᶠ n in atTop, ∃ i : Fin r, z n i ≠ 0 := by
  classical
  have hNpos : ∀ᶠ n in atTop, 0 < N n := hN.eventually (eventually_gt_atTop 0)
  filter_upwards [hb, hsaving, hNpos] with n hbn hsn hn
  by_contra hz
  push Not at hz
  have hsum : (∑ i : Fin r, x n i.succ) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [htail n i, hz i]
    simp
  have heq : x n 0 - ∑ i : Fin r, x n i.succ = 2 ^ D n * a n := by
    rw [hsum, sub_zero, hhead n]
  have hge := trap_zero_carry_residual_ge_one (D n) hbn heq
  have hlt : Real.exp (-eta * N n) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  exact (not_le_of_gt hlt) (hge.trans hsn)

/-- The exponential obstruction allows the zero carry positions to vary with
the sequence index. Conditional ratio estimates only concern nonzero carries;
a fixed nonempty support is extracted inside the proof. -/
theorem false_of_trap_exponential_bounds_variable_support {r : ℕ}
    (x : ℕ → Fin (r + 1) → ℤ)
    (a : ℕ → ℤ) (D : ℕ → ℕ) (z : ℕ → Fin r → ℤ)
    (p s : ℕ → Fin r → ℕ) (N : ℕ → ℝ)
    (hhead : ∀ n, x n 0 = 2 ^ D n * a n)
    (htail : ∀ n (i : Fin r), x n i.succ = z n i * 2 ^ p n i * 3 ^ s n i)
    (hb : ∀ᶠ n in atTop, x n 0 - ∑ i : Fin r, x n i.succ ≠ 0)
    {eta K delta : ℝ} (heta : 0 < eta) (hK : 0 < K) (hdelta : 0 < delta)
    (hN : Tendsto N atTop atTop)
    (hbexp : ∀ i : Fin r, ∀ᶠ n in atTop, z n i ≠ 0 →
      |((x n 0 - ∑ j : Fin r, x n j.succ : ℤ) : ℝ) / (x n i.succ : ℝ)| ≤
        Real.exp (-delta * N n))
    (hsepexp : ∀ i j : Fin r, i < j → ∀ᶠ n in atTop,
      z n i ≠ 0 → z n j ≠ 0 →
      |(x n i.succ : ℝ) / (x n j.succ : ℝ)| ≤ Real.exp (-delta * N n))
    (hz : ∀ i : Fin r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |(z n i : ℝ)| ≤ Real.exp (gamma * N n))
    (hsaving : ∀ᶠ n in atTop,
      |((x n 0 - ∑ i : Fin r, x n i.succ : ℤ) : ℝ)| / (2 : ℝ) ^ D n ≤
        Real.exp (-eta * N n))
    (hheight : ∀ᶠ n in atTop,
      (⨆ i : Fin (r + 1), |(x n i : ℝ)|) ≤ Real.exp (K * N n)) :
    False := by
  classical
  have hexists := eventually_nonzero_trap_coefficient_of_saving
    x a D z p s N hhead htail hb heta hN hsaving
  obtain ⟨S, sigma, hsigma, hS, hsupport⟩ :=
    exists_strictMono_nonempty_fixed_support z hexists
  have hsigmat : Tendsto sigma atTop atTop := hsigma.tendsto_atTop
  let e : Fin S.card ↪o Fin r := S.orderEmbOfFin rfl
  let y : ℕ → Fin (S.card + 1) → ℤ :=
    fun n => Fin.cases (x (sigma n) 0) (fun i => x (sigma n) (e i).succ)
  have hzn : ∀ n (i : Fin S.card), z (sigma n) (e i) ≠ 0 :=
    ordered_support_coordinates_ne_zero z S sigma hsupport
  have hsum : ∀ n, (∑ i : Fin r, x (sigma n) i.succ) =
      ∑ j : Fin S.card, x (sigma n) (e j).succ := by
    apply sum_eq_sum_selected_of_fixed_support z (fun n i => x n i.succ) S sigma hsupport
    intro n i hi
    rw [htail n i, hi]
    simp
  have hres : ∀ n, y n 0 - ∑ i : Fin S.card, y n i.succ =
      x (sigma n) 0 - ∑ i : Fin r, x (sigma n) i.succ := by
    intro n
    simp only [y, Fin.cases_zero, Fin.cases_succ, ← hsum n]
  have hyhead : ∀ n, y n 0 = 2 ^ D (sigma n) * a (sigma n) := by
    intro n
    exact hhead (sigma n)
  have hytail : ∀ n (i : Fin S.card), y n i.succ =
      z (sigma n) (e i) * 2 ^ p (sigma n) (e i) * 3 ^ s (sigma n) (e i) := by
    intro n i
    exact htail (sigma n) (e i)
  have hyb : ∀ᶠ n in atTop, y n 0 - ∑ i : Fin S.card, y n i.succ ≠ 0 := by
    filter_upwards [hsigmat.eventually hb] with n hn
    rw [hres]
    exact hn
  have hyx : ∀ i : Fin S.card, ∀ᶠ n in atTop, y n i.succ ≠ 0 := by
    intro i
    apply Eventually.of_forall
    intro n
    rw [hytail]
    exact mul_ne_zero (mul_ne_zero (hzn n i) (by positivity)) (by positivity)
  have hybexp : ∀ i : Fin S.card, ∀ᶠ n in atTop,
      |((y n 0 - ∑ j : Fin S.card, y n j.succ : ℤ) : ℝ) / (y n i.succ : ℝ)| ≤
        Real.exp (-delta * N (sigma n)) := by
    intro i
    filter_upwards [hsigmat.eventually (hbexp (e i))] with n hn
    rw [hres]
    exact hn (hzn n i)
  have hysep : ∀ i j : Fin S.card, i < j → ∀ᶠ n in atTop,
      |(y n i.succ : ℝ) / (y n j.succ : ℝ)| ≤ Real.exp (-delta * N (sigma n)) := by
    intro i j hij
    filter_upwards [hsigmat.eventually (hsepexp (e i) (e j) (e.strictMono hij))] with n hn
    exact hn (hzn n i) (hzn n j)
  have hyz : ∀ i : Fin S.card, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |(z (sigma n) (e i) : ℝ)| ≤ Real.exp (gamma * N (sigma n)) := by
    intro i gamma hgamma
    exact hsigmat.eventually (hz (e i) gamma hgamma)
  have hysaving : ∀ᶠ n in atTop,
      |((y n 0 - ∑ i : Fin S.card, y n i.succ : ℤ) : ℝ)| / (2 : ℝ) ^ D (sigma n) ≤
        Real.exp (-eta * N (sigma n)) := by
    filter_upwards [hsigmat.eventually hsaving] with n hn
    rw [hres]
    exact hn
  have hyheight : ∀ᶠ n in atTop,
      (⨆ i : Fin (S.card + 1), |(y n i : ℝ)|) ≤ Real.exp (K * N (sigma n)) := by
    filter_upwards [hsigmat.eventually hheight] with n hn
    apply ciSup_le
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (Finite.le_ciSup (fun k : Fin (r + 1) => |(x (sigma n) k : ℝ)|) 0).trans hn
    · exact (Finite.le_ciSup (fun k : Fin (r + 1) => |(x (sigma n) k : ℝ)|)
        (e j).succ).trans hn
  exact false_of_trap_exponential_bounds (Finset.card_pos.mpr hS) y
    (fun n => a (sigma n)) (fun n => D (sigma n))
    (fun n i => z (sigma n) (e i)) (fun n i => p (sigma n) (e i))
    (fun n i => s (sigma n) (e i)) (fun n => N (sigma n))
    hyhead hytail hyb hyx heta hK hdelta (hN.comp hsigmat)
    hybexp hysep hyz hysaving hyheight

end CollatzResearch

#print axioms CollatzResearch.eventually_nonzero_trap_coefficient_of_saving
#print axioms CollatzResearch.false_of_trap_exponential_bounds_variable_support
