import TrapNativeWhiteGapExtraction
import TrapPathExtraction

/-! A literal black-trap family extracted from a bounded walk with few white points. -/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

noncomputable def trapEntryHeight (r J : ℕ) (pointAt : ℕ → TaoSection7Point)
    (t : ℕ → ℕ) (triangles : ℕ → TaoSection7Triangle) (i : ℕ) : ℕ :=
  if i < r then ((triangles i).cornerL - (pointAt (t i)).l).toNat
  else min ((triangles i).cornerL - (pointAt (t i)).l).toNat
    (4 * (J - ((pointAt (t i)).j : ℕ)))

theorem trap_entry_height_full (r J : ℕ) (pointAt : ℕ → TaoSection7Point)
    (t : ℕ → ℕ) (triangles : ℕ → TaoSection7Triangle) (i : ℕ) (hi : i < r)
    (hmem : (triangles i).Mem (pointAt (t i))) :
    (trapEntryHeight r J pointAt t triangles i : ℤ) =
      (triangles i).cornerL - (pointAt (t i)).l := by
  rw [trapEntryHeight, ite_eq_left hi, Int.toNat_of_nonneg (sub_nonneg.mpr hmem.2.1)]

theorem trap_entry_height_cut (r J : ℕ) (pointAt : ℕ → TaoSection7Point)
    (t : ℕ → ℕ) (triangles : ℕ → TaoSection7Triangle) (i : ℕ)
    (hmem : (triangles i).Mem (pointAt (t i))) :
    (trapEntryHeight r J pointAt t triangles i : ℤ) ≤
      (triangles i).cornerL - (pointAt (t i)).l := by
  by_cases hi : i < r
  · exact (trap_entry_height_full r J pointAt t triangles i hi hmem).le
  · rw [trapEntryHeight, ite_eq_right hi]
    calc
      ((min ((triangles i).cornerL - (pointAt (t i)).l).toNat
          (4 * (J - ((pointAt (t i)).j : ℕ))) : ℕ) : ℤ) ≤
        (((triangles i).cornerL - (pointAt (t i)).l).toNat : ℤ) := by
          exact_mod_cast Nat.min_le_left _ _
      _ = (triangles i).cornerL - (pointAt (t i)).l :=
        Int.toNat_of_nonneg (sub_nonneg.mpr hmem.2.1)

theorem exists_native_black_trap_family_of_few_white
    (n coverJ J M r K H : ℕ) (xi : ZMod (3 ^ n)) (epsilon V D : ℝ)
    (pointAt : ℕ → TaoSection7Point) (family : Set TaoSection7Triangle)
    (t : ℕ → ℕ) (triangles : ℕ → TaoSection7Triangle) (S : ℤ)
    (hxi : zmodThreePrimitive n xi) (hnJ : 2 * J ≤ n) (hJcover : J ≤ coverJ) (hV : 0 ≤ V)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon coverJ) family)
    (hdomain : ∀ q < M, ((pointAt q).j : ℕ) ≤ J)
    (hcount : trapSourceWhiteCount n xi epsilon pointAt M ≤ K)
    (hstop : ∀ i ≤ r, t i < M)
    (hmem : ∀ i ≤ r, (triangles i).Mem (pointAt (t i)))
    (hfamily : ∀ i ≤ r, triangles i ∈ family)
    (hfirst : ∀ q < t 0, ¬ ∃ Delta ∈ family, Delta.Mem (pointAt q))
    (hnext : ∀ i < r,
      t i < t (i + 1) ∧
      ((triangles i).cornerL < (pointAt (t (i + 1))).l ∧
        ∃ Delta ∈ family, Delta.Mem (pointAt (t (i + 1)))) ∧
      ∀ q, t i < q → q < t (i + 1) →
        ¬ ((triangles i).cornerL < (pointAt q).l ∧
          ∃ Delta ∈ family, Delta.Mem (pointAt q)))
    (hterminal : ∀ q, t r < q → q < M →
      ¬ ((triangles r).cornerL < (pointAt q).l ∧
        ∃ Delta ∈ family, Delta.Mem (pointAt q)))
    (hmonoJ : Monotone fun q => ((pointAt q).j : ℕ))
    (hstepJ : ∀ q < M, ((pointAt (q + 1)).j : ℕ) ≤ (pointAt q).j + H)
    (hstepL : ∀ q < M, ((pointAt (q + 1)).l : ℝ) ≤ (pointAt q).l + V)
    (htube : ∀ q < M, |((pointAt q).l : ℝ) - 4 * (((pointAt q).j : ℕ) : ℝ)| ≤ D)
    (hS : |(S : ℝ) - 4 * (J : ℝ)| ≤ D)
    (hendpoint : S ≤ (pointAt M).l) :
    ∃ f : NativeBlackTrapFamily epsilon n r,
      f.xi = xi ∧
      nativeTrapFamilyError f ≤
        2 * ((r : ℝ) + 1) * D + V * ((K : ℝ) + 1) + 2 * V * ((K : ℝ) + r) ∧
      4 * (J : ℝ) - 4 * ((((pointAt 0).j : ℕ) + H * K : ℕ) : ℝ) -
        2 * D - V * ((K : ℝ) + 1) ≤ nativeTrapFamilySpan f := by
  have hgap := trap_native_white_gap_bounds n coverJ M r K H xi epsilon V
    pointAt family t triangles hV hcover (fun q hq => (hdomain q hq).trans hJcover)
      hcount hstop hmem hfirst hnext hterminal hstepJ hstepL
  let h := trapEntryHeight r J pointAt t triangles
  have hblack : ∀ i ≤ r, (triangles i).BlackOn (taoSection7SourceBlackPoint n xi epsilon) := by
    intro i hi p hp
    exact ((hcover p).mpr ⟨triangles i, hfamily i hi, hp⟩).2
  have htail : (S : ℝ) ≤ ((triangles r).cornerL : ℝ) + V * ((K : ℝ) + 1) := by
    have hSM : (S : ℝ) ≤ ((pointAt M).l : ℝ) := by exact_mod_cast hendpoint
    exact hSM.trans hgap.2.2.2
  have hcut : ∀ i ≤ r, (h i : ℤ) ≤ (triangles i).cornerL - (pointAt (t i)).l := by
    intro i hi
    exact trap_entry_height_cut r J pointAt t triangles i (hmem i hi)
  have hfinal : h r = min ((triangles r).cornerL - (pointAt (t r)).l).toNat
      (4 * (J - ((pointAt (t r)).j : ℕ))) := by simp [h, trapEntryHeight]
  obtain ⟨f, hfxi, _, herror, hspan⟩ := exists_native_black_trap_family_of_entries
    (r := r) (J := J) xi (fun i => (pointAt (t i)).j) (fun i => (pointAt (t i)).l) h triangles S
    hxi (fun i hi => hmonoJ (hnext i hi).1.le)
    (fun i hi => hdomain (t i) (hstop i hi)) hnJ hmem hblack hcut hfinal
    (mul_nonneg hV (by positivity)) (fun i hi => htube (t i) (hstop i hi)) hS htail
  have hsum : (∑ i ∈ Finset.range r,
      |(((pointAt (t (i + 1))).l - ((pointAt (t i)).l + h i) : ℤ) : ℝ)|) =
    ∑ i ∈ Finset.range r, |(((pointAt (t (i + 1))).l - (triangles i).cornerL : ℤ) : ℝ)| := by
    apply Finset.sum_congr rfl
    intro i hi
    have hh := trap_entry_height_full r J pointAt t triangles i (Finset.mem_range.mp hi)
      (hmem i (by have := Finset.mem_range.mp hi; omega))
    change (h i : ℤ) = _ at hh
    rw [show (pointAt (t i)).l + (h i : ℤ) = (triangles i).cornerL by omega]
  have hj0 : (((pointAt (t 0)).j : ℕ) : ℝ) ≤
      ((((pointAt 0).j : ℕ) + H * K : ℕ) : ℝ) := by exact_mod_cast hgap.2.1
  refine ⟨f, hfxi, ?_, ?_⟩
  · rw [hsum] at herror
    have hG := hgap.2.2.1
    nlinarith
  · linarith

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_entry_height_full
#print axioms Erdos1135.Tao.trap_entry_height_cut
#print axioms Erdos1135.Tao.exists_native_black_trap_family_of_few_white
