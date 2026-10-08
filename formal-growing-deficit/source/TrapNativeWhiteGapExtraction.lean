import TrapWhiteGapExtraction
import Erdos1135.Tao.Fourier.Section7SourcePredicates

/-!
White-count gap estimates for literal Section 7 points and triangle families.
The no-hit contracts are stated explicitly; no source distribution is changed.
-/

set_option autoImplicit false
open scoped BigOperators Classical
open CollatzResearch

namespace Erdos1135.Tao

noncomputable def trapSourceWhiteCount (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (pointAt : ℕ → TaoSection7Point) (M : ℕ) : ℕ :=
  trapWhiteCount (fun q => taoSection7SourceWhitePoint n xi epsilon (pointAt q)) M

theorem trap_source_white_of_no_triangle_hit
    (n J : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (family : Set TaoSection7Triangle)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (p : TaoSection7Point) (hp : (p.j : ℕ) ≤ J)
    (hno : ¬ ∃ Delta ∈ family, Delta.Mem p) :
    taoSection7SourceWhitePoint n xi epsilon p := by
  apply (taoSection7White_iff_not_black epsilon _).mpr
  intro hb
  exact hno ((hcover p).mp ⟨hp, hb⟩)

theorem trap_source_exists_triangle_hit_of_few_white
    (n J M : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (pointAt : ℕ → TaoSection7Point) (family : Set TaoSection7Triangle)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hdomain : ∀ q < M, ((pointAt q).j : ℕ) ≤ J)
    (hcount : trapSourceWhiteCount n xi epsilon pointAt M < M) :
    ∃ q < M, ∃ Delta ∈ family, Delta.Mem (pointAt q) := by
  by_contra hno
  have hW : ∀ q < M, taoSection7SourceWhitePoint n xi epsilon (pointAt q) := by
    intro q hq
    apply trap_source_white_of_no_triangle_hit n J xi epsilon family hcover (pointAt q) (hdomain q hq)
    exact fun hh => hno ⟨q, hq, hh⟩
  have hc := trap_white_count_of_all
    (fun q => taoSection7SourceWhitePoint n xi epsilon (pointAt q)) M hW
  change trapWhiteCount (fun q => taoSection7SourceWhitePoint n xi epsilon (pointAt q)) M < M at hcount
  omega

/-- The exact first-hit and post-top no-hit contracts imply the three gap
bounds needed by the native black-trap extraction. -/
theorem trap_native_white_gap_bounds
    (n J M r K H : ℕ) (xi : ZMod (3 ^ n)) (epsilon V : ℝ)
    (pointAt : ℕ → TaoSection7Point) (family : Set TaoSection7Triangle)
    (t : ℕ → ℕ) (triangles : ℕ → TaoSection7Triangle)
    (hV : 0 ≤ V)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hdomain : ∀ q < M, ((pointAt q).j : ℕ) ≤ J)
    (hcount : trapSourceWhiteCount n xi epsilon pointAt M ≤ K)
    (hstop : ∀ i ≤ r, t i < M)
    (hmem : ∀ i ≤ r, (triangles i).Mem (pointAt (t i)))
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
    (hstepJ : ∀ q < M, ((pointAt (q + 1)).j : ℕ) ≤ (pointAt q).j + H)
    (hstepL : ∀ q < M, ((pointAt (q + 1)).l : ℝ) ≤ (pointAt q).l + V) :
    t 0 ≤ K ∧
      ((pointAt (t 0)).j : ℕ) ≤ (pointAt 0).j + H * K ∧
      (∑ i ∈ Finset.range r,
        |(((pointAt (t (i + 1))).l - (triangles i).cornerL : ℤ) : ℝ)|) ≤
          V * ((K : ℝ) + r) ∧
      ((pointAt M).l : ℝ) ≤ (triangles r).cornerL + V * ((K : ℝ) + 1) := by
  let W : ℕ → Prop := fun q => taoSection7SourceWhitePoint n xi epsilon (pointAt q)
  have hwhite : ∀ q < M, (¬ ∃ Delta ∈ family, Delta.Mem (pointAt q)) → W q := by
    intro q hq hno
    exact trap_source_white_of_no_triangle_hit n J xi epsilon family hcover (pointAt q) (hdomain q hq) hno
  have hinit := trap_initial_entry_le W (fun q => (pointAt q).j) H M (t 0) K
    (hstop 0 (by omega)).le hcount
    (fun q hq => hwhite q (hq.trans (hstop 0 (by omega))) (hfirst q hq)) hstepJ
  have hstart : ∀ i ≤ r, ((pointAt (t i)).l : ℝ) ≤ (triangles i).cornerL := by
    intro i hi
    exact_mod_cast (hmem i hi).2.1
  have hbetween : ∀ i < r, ∀ q, t i ≤ q → q < t (i + 1) →
      ((triangles i).cornerL : ℝ) < (pointAt q).l → W q := by
    intro i hi q hti hq hT
    have hTz : (triangles i).cornerL < (pointAt q).l := by exact_mod_cast hT
    have hstrict : t i < q := by
      by_contra hnot
      have heq : q = t i := by omega
      rw [heq] at hTz
      exact (not_lt_of_ge (hmem i (by omega)).2.1) hTz
    apply hwhite q (hq.trans (hstop (i + 1) (by omega)))
    exact fun hh => (hnext i hi).2.2 q hstrict hq ⟨hTz, hh⟩
  have hG := trap_post_top_gap_sum_le W (fun q => (pointAt q).l)
    (fun i => (triangles i).cornerL) t r M V hV
    (fun i hi => (hnext i hi).1.le) (fun i hi => (hstop i hi).le)
    (fun i hi => hstart i (by omega))
    (fun i hi => by exact_mod_cast (hnext i hi).2.1.1.le) hstepL hbetween
  have htailwhite : ∀ q, t r ≤ q → q < M →
      ((triangles r).cornerL : ℝ) < (pointAt q).l → W q := by
    intro q htq hq hT
    have hTz : (triangles r).cornerL < (pointAt q).l := by exact_mod_cast hT
    have hstrict : t r < q := by
      by_contra hnot
      have heq : q = t r := by omega
      rw [heq] at hTz
      exact (not_lt_of_ge (hmem r le_rfl).2.1) hTz
    exact hwhite q hq (fun hh => hterminal q hstrict hq ⟨hTz, hh⟩)
  have hB := trap_terminal_top_bound W (fun q => (pointAt q).l) (t r) M K
    (triangles r).cornerL V (hstop r le_rfl).le hV (hstart r le_rfl) hcount hstepL htailwhite
  refine ⟨hinit.1, hinit.2, ?_, hB⟩
  have hcr : (trapWhiteCount W M : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcount
  calc
    _ ≤ V * ((trapWhiteCount W M : ℝ) + r) := by simpa only [Int.cast_sub] using hG
    _ ≤ V * ((K : ℝ) + r) := by gcongr

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_source_exists_triangle_hit_of_few_white
#print axioms Erdos1135.Tao.trap_native_white_gap_bounds
