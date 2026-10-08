import TrapBoundedUniform

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

theorem integerHeightTrap_from_mem_subset
    (D : TaoSection7Triangle) (p : TaoSection7Point) (h : ℕ)
    (hp : D.Mem p) (hh : (h : ℤ) ≤ D.cornerL - p.l) :
    ∀ q, (integerHeightTrap ⟨p.j, p.l + h⟩ h).Mem q → D.Mem q := by
  intro q hq
  have hjp : (D.cornerJ : ℕ) ≤ p.j := hp.1
  have hjq : (p.j : ℕ) ≤ q.j := hq.1
  have hj : (D.cornerJ : ℕ) ≤ q.j := hjp.trans hjq
  refine ⟨hj, ?_, ?_⟩
  · have hqheight : q.l ≤ p.l + h := hq.2.1
    omega
  · have hpweight := hp.2.2
    have hqweight := hq.2.2
    change (((q.j : ℕ) - (p.j : ℕ) : ℕ) : ℝ) * Real.log 9 +
      (((p.l + h - q.l : ℤ) : ℝ)) * Real.log 2 ≤ (h : ℝ) * Real.log 2 at hqweight
    have hd : (q.j : ℕ) - (D.cornerJ : ℕ) =
        ((q.j : ℕ) - (p.j : ℕ)) + ((p.j : ℕ) - (D.cornerJ : ℕ)) := by omega
    unfold TaoSection7Triangle.horizontalDepth TaoSection7Triangle.verticalDepth at hpweight ⊢
    rw [hd, Nat.cast_add]
    push_cast at hpweight hqweight ⊢
    nlinarith

theorem integerHeightTrap_from_mem_black
    (D : TaoSection7Triangle) (p : TaoSection7Point) (h : ℕ)
    {black : TaoSection7Point → Prop}
    (hp : D.Mem p) (hh : (h : ℤ) ≤ D.cornerL - p.l) (hb : D.BlackOn black) :
    (integerHeightTrap ⟨p.j, p.l + h⟩ h).BlackOn black := by
  intro q hq
  exact hb q (integerHeightTrap_from_mem_subset D p h hp hh q hq)

end Erdos1135.Tao

namespace CollatzResearch

theorem trap_path_adjacent_length_sum (r : ℕ) (j : ℕ → ℕ)
    (hj : ∀ i < r, j i ≤ j (i + 1)) :
    (∑ i ∈ Finset.range r, (j (i + 1) - j i)) + j 0 = j r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hprev := ih (fun i hi => hj i (by omega))
    rw [Finset.sum_range_succ]
    have hlast := hj r (by omega)
    omega

def trapPathLength (r J : ℕ) (j : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < r then j (i + 1) - j i else J - j i

theorem trap_path_length_sum (r J : ℕ) (j : ℕ → ℕ)
    (hj : ∀ i < r, j i ≤ j (i + 1)) (hJ : j r ≤ J) :
    (∑ i ∈ Finset.range (r + 1), trapPathLength r J j i) + j 0 = J := by
  rw [Finset.sum_range_succ]
  have hs : (∑ i ∈ Finset.range r, trapPathLength r J j i) =
      ∑ i ∈ Finset.range r, (j (i + 1) - j i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [trapPathLength, Finset.mem_range.mp hi]
  rw [hs]
  simp only [trapPathLength, lt_self_iff_false, ↓reduceIte]
  have hsum := trap_path_adjacent_length_sum r j hj
  omega

theorem trap_path_block_error_le (r J i : ℕ) (j : ℕ → ℕ)
    (l : ℕ → ℤ) (h : ℕ → ℕ) {D : ℝ} (hi : i < r)
    (hj : j i ≤ j (i + 1))
    (hleft : |(l i : ℝ) - 4 * (j i : ℝ)| ≤ D)
    (hright : |(l (i + 1) : ℝ) - 4 * (j (i + 1) : ℝ)| ≤ D) :
    |(((h i : ℤ) - 4 * (trapPathLength r J j i : ℤ) : ℤ) : ℝ)| ≤
      2 * D + |((l (i + 1) - (l i + h i) : ℤ) : ℝ)| := by
  have heq : (((h i : ℤ) - 4 * (trapPathLength r J j i : ℤ) : ℤ) : ℝ) =
      ((l (i + 1) : ℝ) - 4 * (j (i + 1) : ℝ)) -
      ((l i : ℝ) - 4 * (j i : ℝ)) -
      ((l (i + 1) - (l i + h i) : ℤ) : ℝ) := by
    simp only [trapPathLength, ite_eq_left hi, Nat.cast_sub hj]
    push_cast
    ring
  rw [heq]
  have hs : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := by
    intro x y
    simpa using abs_sub_le x 0 y
  calc
    _ ≤ |((l (i + 1) : ℝ) - 4 * (j (i + 1) : ℝ)) -
        ((l i : ℝ) - 4 * (j i : ℝ))| +
        |((l (i + 1) - (l i + h i) : ℤ) : ℝ)| := hs _ _
    _ ≤ (|(l (i + 1) : ℝ) - 4 * (j (i + 1) : ℝ)| +
        |(l i : ℝ) - 4 * (j i : ℝ)|) +
        |((l (i + 1) - (l i + h i) : ℤ) : ℝ)| := add_le_add (hs _ _) le_rfl
    _ ≤ _ := by linarith

theorem trap_path_error_budget (r J : ℕ) (j : ℕ → ℕ)
    (l : ℕ → ℤ) (h : ℕ → ℕ) {D B : ℝ}
    (hj : ∀ i < r, j i ≤ j (i + 1))
    (htube : ∀ i ≤ r, |(l i : ℝ) - 4 * (j i : ℝ)| ≤ D)
    (hlast : |(((h r : ℤ) - 4 * (trapPathLength r J j r : ℤ) : ℤ) : ℝ)| ≤ 2 * D + B) :
    (∑ i ∈ Finset.range (r + 1),
        |(((h i : ℤ) - 4 * (trapPathLength r J j i : ℤ) : ℤ) : ℝ)|) +
      (∑ i ∈ Finset.range r, |((l (i + 1) - (l i + h i) : ℤ) : ℝ)|) ≤
      2 * ((r : ℝ) + 1) * D + B +
        2 * (∑ i ∈ Finset.range r, |((l (i + 1) - (l i + h i) : ℤ) : ℝ)|) := by
  have hsum := Finset.sum_le_sum (s := Finset.range r) (fun i hi =>
    trap_path_block_error_le r J i j l h (Finset.mem_range.mp hi)
      (hj i (Finset.mem_range.mp hi))
      (htube i (by have := Finset.mem_range.mp hi; omega))
      (htube (i + 1) (by have := Finset.mem_range.mp hi; omega)))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [Finset.sum_range_succ]
  nlinarith

theorem trap_path_last_height_bounds (j J h : ℕ) (l T S : ℤ) {D B : ℝ}
    (hj : j ≤ J) (hlT : l ≤ T) (hB : 0 ≤ B)
    (hheight : h = min (T - l).toNat (4 * (J - j)))
    (hl : |(l : ℝ) - 4 * (j : ℝ)| ≤ D)
    (hS : |(S : ℝ) - 4 * (J : ℝ)| ≤ D)
    (hT : (S : ℝ) ≤ (T : ℝ) + B) :
    |(((h : ℤ) - 4 * ((J - j : ℕ) : ℤ) : ℤ) : ℝ)| ≤ 2 * D + B ∧
      4 * (J : ℝ) - D - B ≤ (l : ℝ) + (h : ℝ) := by
  have hnat : ((T - l).toNat : ℝ) = (T : ℝ) - (l : ℝ) := by
    have hc := Int.toNat_of_nonneg (sub_nonneg.mpr hlT)
    exact_mod_cast hc
  have hc : (h : ℝ) = min ((T : ℝ) - (l : ℝ)) (4 * ((J : ℝ) - (j : ℝ))) := by
    rw [hheight, Nat.cast_min, hnat, Nat.cast_mul, Nat.cast_sub hj]
    norm_num
  have hl' := abs_le.mp hl
  have hS' := abs_le.mp hS
  have hupper : (h : ℝ) ≤ 4 * ((J : ℝ) - (j : ℝ)) := by rw [hc]; exact min_le_right _ _
  have hlower : 4 * ((J : ℝ) - (j : ℝ)) - (2 * D + B) ≤ (h : ℝ) := by
    rw [hc]
    exact le_min (by linarith) (by linarith [abs_nonneg ((l : ℝ) - 4 * (j : ℝ))])
  constructor
  · push_cast
    rw [Nat.cast_sub hj]
    exact abs_le.mpr ⟨by linarith, by linarith [abs_nonneg ((l : ℝ) - 4 * (j : ℝ))]⟩
  · have htop : 4 * (J : ℝ) - D - B - (l : ℝ) ≤ (h : ℝ) := by
      rw [hc]
      exact le_min (by linarith) (by linarith)
    linarith

end CollatzResearch

namespace Erdos1135.Tao

def nativeBlackTrapFamilyOfPath
    {epsilon : ℝ} {n r J : ℕ} (xi : ZMod (3 ^ n))
    (j : ℕ → ℕ+) (l : ℕ → ℤ) (h : ℕ → ℕ)
    (hxi : zmodThreePrimitive n xi)
    (hj : ∀ i < r, (j i : ℕ) ≤ j (i + 1))
    (hJ : ∀ i ≤ r, (j i : ℕ) ≤ J) (hnJ : 2 * J ≤ n)
    (hblack : ∀ i ≤ r, (integerHeightTrap ⟨j i, l i + h i⟩ (h i)).BlackOn
      (taoSection7SourceBlackPoint n xi epsilon)) : NativeBlackTrapFamily epsilon n r where
  h := h
  m := CollatzResearch.trapPathLength r J (fun i => j i)
  u := fun _ => 0
  e := fun i => (h i : ℤ) - 4 * (CollatzResearch.trapPathLength r J (fun i => j i) i : ℤ)
  g := fun i => l (i + 1) - (l i + h i)
  xi := xi
  p := fun i => ⟨j i, l i + h i⟩
  primitive := hxi
  strip := by
    intro i hi
    have hjpos := (j i).property
    change 2 * ((j i : ℕ) - 1) < n
    have hstrict : 2 * ((j i : ℕ) - 1) < 2 * (j i : ℕ) :=
      Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hjpos (by decide)) (by decide)
    exact hstrict.trans_le ((Nat.mul_le_mul_left 2 (hJ i hi)).trans hnJ)
  space := by
    intro i hi
    have hji := hj i hi
    simp only [CollatzResearch.trapPathLength, ite_eq_left hi, Nat.add_zero]
    omega
  top := by intro i _; dsimp; ring
  height := by intro i _; ring
  total := by
    have hs := CollatzResearch.trap_path_length_sum r J (fun i => (j i : ℕ)) hj (hJ r le_rfl)
    omega
  black := hblack

section PathBounds

variable {epsilon : ℝ} {n r J : ℕ} (xi : ZMod (3 ^ n))
  (j : ℕ → ℕ+) (l : ℕ → ℤ) (h : ℕ → ℕ)
  (hxi : zmodThreePrimitive n xi)
  (hj : ∀ i < r, (j i : ℕ) ≤ j (i + 1))
  (hJ : ∀ i ≤ r, (j i : ℕ) ≤ J) (hnJ : 2 * J ≤ n)
  (hblack : ∀ i ≤ r, (integerHeightTrap ⟨j i, l i + h i⟩ (h i)).BlackOn
    (taoSection7SourceBlackPoint n xi epsilon))

theorem nativeBlackTrapFamilyOfPath_span :
    nativeTrapFamilySpan (nativeBlackTrapFamilyOfPath xi j l h hxi hj hJ hnJ hblack) =
      (l r : ℝ) + (h r : ℝ) - (l 0 : ℝ) := by
  simp only [nativeTrapFamilySpan, nativeBlackTrapFamilyOfPath]
  push_cast
  ring

theorem nativeBlackTrapFamilyOfPath_error_le {D B : ℝ}
    (htube : ∀ i ≤ r, |(l i : ℝ) - 4 * ((j i : ℕ) : ℝ)| ≤ D)
    (hlast : |(((h r : ℤ) -
      4 * (CollatzResearch.trapPathLength r J (fun i => j i) r : ℤ) : ℤ) : ℝ)| ≤ 2 * D + B) :
    nativeTrapFamilyError (nativeBlackTrapFamilyOfPath xi j l h hxi hj hJ hnJ hblack) ≤
      2 * ((r : ℝ) + 1) * D + B +
        2 * (∑ i ∈ Finset.range r, |((l (i + 1) - (l i + h i) : ℤ) : ℝ)|) := by
  simpa only [nativeTrapFamilyError, nativeBlackTrapFamilyOfPath, Nat.cast_zero, zero_add] using
    CollatzResearch.trap_path_error_budget r J (fun i => (j i : ℕ)) l h hj htube hlast

theorem nativeBlackTrapFamilyOfPath_span_ge {D B : ℝ}
    (hfirst : |(l 0 : ℝ) - 4 * ((j 0 : ℕ) : ℝ)| ≤ D)
    (hlast : 4 * (J : ℝ) - D - B ≤ (l r : ℝ) + (h r : ℝ)) :
    4 * (J : ℝ) - 4 * ((j 0 : ℕ) : ℝ) - 2 * D - B ≤
      nativeTrapFamilySpan (nativeBlackTrapFamilyOfPath xi j l h hxi hj hJ hnJ hblack) := by
  rw [nativeBlackTrapFamilyOfPath_span]
  have hfirst' := (abs_le.mp hfirst).2
  linarith

end PathBounds

theorem exists_native_black_trap_family_of_entries
    {epsilon : ℝ} {n r J : ℕ} (xi : ZMod (3 ^ n))
    (j : ℕ → ℕ+) (l : ℕ → ℤ) (h : ℕ → ℕ) (triangles : ℕ → TaoSection7Triangle)
    (S : ℤ) {D B : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hj : ∀ i < r, (j i : ℕ) ≤ j (i + 1))
    (hJ : ∀ i ≤ r, (j i : ℕ) ≤ J) (hnJ : 2 * J ≤ n)
    (hmem : ∀ i ≤ r, (triangles i).Mem ⟨j i, l i⟩)
    (hblack : ∀ i ≤ r, (triangles i).BlackOn (taoSection7SourceBlackPoint n xi epsilon))
    (hcut : ∀ i ≤ r, (h i : ℤ) ≤ (triangles i).cornerL - l i)
    (hfinal : h r = min ((triangles r).cornerL - l r).toNat (4 * (J - (j r : ℕ))))
    (hB : 0 ≤ B)
    (htube : ∀ i ≤ r, |(l i : ℝ) - 4 * ((j i : ℕ) : ℝ)| ≤ D)
    (hS : |(S : ℝ) - 4 * (J : ℝ)| ≤ D)
    (htail : (S : ℝ) ≤ ((triangles r).cornerL : ℝ) + B) :
    ∃ t : NativeBlackTrapFamily epsilon n r,
      t.xi = xi ∧ t.p = (fun i => ⟨j i, l i + h i⟩) ∧
      nativeTrapFamilyError t ≤ 2 * ((r : ℝ) + 1) * D + B +
        2 * (∑ i ∈ Finset.range r, |((l (i + 1) - (l i + h i) : ℤ) : ℝ)|) ∧
      4 * (J : ℝ) - 4 * ((j 0 : ℕ) : ℝ) - 2 * D - B ≤ nativeTrapFamilySpan t := by
  have hb : ∀ i ≤ r, (integerHeightTrap ⟨j i, l i + h i⟩ (h i)).BlackOn
      (taoSection7SourceBlackPoint n xi epsilon) := by
    intro i hi
    exact integerHeightTrap_from_mem_black (triangles i) ⟨j i, l i⟩ (h i)
      (hmem i hi) (hcut i hi) (hblack i hi)
  have hlast := CollatzResearch.trap_path_last_height_bounds (j r) J (h r) (l r)
    (triangles r).cornerL S (hJ r le_rfl) (hmem r le_rfl).2.1 hB hfinal
    (htube r le_rfl) hS htail
  refine ⟨nativeBlackTrapFamilyOfPath xi j l h hxi hj hJ hnJ hb, rfl, rfl, ?_, ?_⟩
  · apply nativeBlackTrapFamilyOfPath_error_le xi j l h hxi hj hJ hnJ hb htube
    simpa only [CollatzResearch.trapPathLength, lt_self_iff_false, ↓reduceIte] using hlast.1
  · exact nativeBlackTrapFamilyOfPath_span_ge xi j l h hxi hj hJ hnJ hb (htube 0 (by omega)) hlast.2

end Erdos1135.Tao

#print axioms Erdos1135.Tao.integerHeightTrap_from_mem_subset
#print axioms Erdos1135.Tao.nativeBlackTrapFamilyOfPath
#print axioms CollatzResearch.trap_path_error_budget
#print axioms CollatzResearch.trap_path_last_height_bounds
#print axioms Erdos1135.Tao.nativeBlackTrapFamilyOfPath_error_le
#print axioms Erdos1135.Tao.nativeBlackTrapFamilyOfPath_span_ge
#print axioms Erdos1135.Tao.exists_native_black_trap_family_of_entries
