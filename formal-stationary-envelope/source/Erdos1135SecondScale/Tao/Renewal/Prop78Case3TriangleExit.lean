/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Prop78Case3Event

/-!
# Proposition 7.8 Case 3 Triangle Exit Support

This module records support-only triangle-geometry consequences used by the
future Proposition 7.8 Case 3 one-step source exit.  It isolates the algebra
around Tao's triangle membership inequality: a point in a small triangle and a
large enough later vertical increment force the later point above the old
triangle's top edge, hence outside that old triangle.

It does not prove the source vertical-growth lower bound, the source-calibrated
finite exit budget, first-stopping/new-triangle compatibility, Lemma 7.9,
Lemma 7.10, the Case 3 many-whites estimate, any Proposition 7.8 case,
boundary estimate `(7.41)`, Proposition 7.8, or Tao's theorem.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

theorem taoSection7Case3_verticalDepth_log2_le_size_of_mem
    {Δ : TaoSection7Triangle} {p : TaoSection7Point}
    (hmem : Δ.Mem p) :
    ((Δ.verticalDepth p : ℤ) : ℝ) * Real.log 2 ≤ Δ.size := by
  have hlog9_nonneg : 0 ≤ Real.log 9 :=
    le_of_lt (Real.log_pos (by norm_num))
  have hhorizontal_nonneg :
      0 ≤ ((Δ.horizontalDepth p : ℕ) : ℝ) * Real.log 9 :=
    mul_nonneg (by positivity) hlog9_nonneg
  have hweight_le := TaoSection7Triangle.mem_weight_le_size hmem
  linarith

/--
Height-exit form of the triangle membership inequality.  The later source
growth hypothesis is explicit; the source path proof will supply it later.
-/
theorem taoSection7Case3_cornerL_lt_of_mem_and_vertical_growth_log2_gt_size
    {pointAt : ℕ → TaoSection7Point}
    {Δ : TaoSection7Triangle} {p p' : ℕ}
    (hmem : Δ.Mem (pointAt p))
    (hsize_growth :
      Δ.size <
        (((pointAt p').l - (pointAt p).l : ℤ) : ℝ) * Real.log 2) :
    Δ.cornerL < (pointAt p').l := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvertical_le_size :
      ((Δ.verticalDepth (pointAt p) : ℤ) : ℝ) * Real.log 2 ≤ Δ.size :=
    taoSection7Case3_verticalDepth_log2_le_size_of_mem hmem
  have hmul_lt :
      ((Δ.verticalDepth (pointAt p) : ℤ) : ℝ) * Real.log 2 <
        (((pointAt p').l - (pointAt p).l : ℤ) : ℝ) * Real.log 2 :=
    lt_of_le_of_lt hvertical_le_size hsize_growth
  have hdepth_lt_growth_real :
      ((Δ.verticalDepth (pointAt p) : ℤ) : ℝ) <
        (((pointAt p').l - (pointAt p).l : ℤ) : ℝ) :=
    lt_of_mul_lt_mul_right hmul_lt (le_of_lt hlog2_pos)
  have hdepth_lt_growth :
      Δ.verticalDepth (pointAt p) < (pointAt p').l - (pointAt p).l := by
    exact_mod_cast hdepth_lt_growth_real
  unfold TaoSection7Triangle.verticalDepth at hdepth_lt_growth
  omega

theorem taoSection7Case3_cornerL_lt_of_mem_source_bound_and_vertical_growth
    {pointAt : ℕ → TaoSection7Point}
    {Δ : TaoSection7Triangle} {A p p' : ℕ}
    (hmem : Δ.Mem (pointAt p))
    (hsize : Δ.size < taoSection7Case3LargeTriangleBound A p)
    (hgrowth :
      taoSection7Case3LargeTriangleBound A p ≤
        (((pointAt p').l - (pointAt p).l : ℤ) : ℝ) * Real.log 2) :
    Δ.cornerL < (pointAt p').l :=
  taoSection7Case3_cornerL_lt_of_mem_and_vertical_growth_log2_gt_size
    hmem (lt_of_lt_of_le hsize hgrowth)

theorem taoSection7Case3_not_mem_of_cornerL_lt
    {Δ : TaoSection7Triangle} {p : TaoSection7Point}
    (hexit_height : Δ.cornerL < p.l) :
    ¬ Δ.Mem p := by
  intro hmem
  exact not_le_of_gt hexit_height hmem.2.1

theorem taoSection7Case3_not_mem_of_mem_source_bound_and_vertical_growth
    {pointAt : ℕ → TaoSection7Point}
    {Δ : TaoSection7Triangle} {A p p' : ℕ}
    (hmem : Δ.Mem (pointAt p))
    (hsize : Δ.size < taoSection7Case3LargeTriangleBound A p)
    (hgrowth :
      taoSection7Case3LargeTriangleBound A p ≤
        (((pointAt p').l - (pointAt p).l : ℤ) : ℝ) * Real.log 2) :
    ¬ Δ.Mem (pointAt p') :=
  taoSection7Case3_not_mem_of_cornerL_lt
    (taoSection7Case3_cornerL_lt_of_mem_source_bound_and_vertical_growth
      hmem hsize hgrowth)

theorem taoSection7Case3_black_later_point_has_different_triangle_of_exit
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Δ : TaoSection7Triangle} {p' : ℕ}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hblack : black (pointAt p'))
    (hnot_mem_old : ¬ Δ.Mem (pointAt p')) :
    ∃ Γ : TaoSection7Triangle, Γ ∈ family ∧ Γ.Mem (pointAt p') ∧ Γ ≠ Δ := by
  rcases (hcover (pointAt p')).1 hblack with ⟨Γ, hΓ, hmemΓ⟩
  refine ⟨Γ, hΓ, hmemΓ, ?_⟩
  intro hΓ_eq
  subst hΓ_eq
  exact hnot_mem_old hmemΓ

/--
Package for the later black pivot after the old triangle has been exited.
This keeps the height-exit fact visible together with the covering triangle
chosen for the later black point.
-/
def taoSection7Case3BlackPivotStep
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (old Γ : TaoSection7Triangle) (p' : ℕ) : Prop :=
  old.cornerL < (pointAt p').l ∧
    black (pointAt p') ∧ Γ ∈ family ∧ Γ.Mem (pointAt p') ∧ Γ ≠ old

theorem taoSection7Case3_exists_blackPivotStep_of_exit_height
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {old : TaoSection7Triangle} {p' : ℕ}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hblack : black (pointAt p'))
    (hexit_height : old.cornerL < (pointAt p').l) :
    ∃ Γ : TaoSection7Triangle,
      taoSection7Case3BlackPivotStep black family pointAt old Γ p' := by
  rcases taoSection7Case3_black_later_point_has_different_triangle_of_exit
      hcover hblack (taoSection7Case3_not_mem_of_cornerL_lt hexit_height) with
    ⟨Γ, hΓ, hmemΓ, hΓ_ne⟩
  exact ⟨Γ, hexit_height, hblack, hΓ, hmemΓ, hΓ_ne⟩

theorem taoSection7Case3_exists_blackPivotStep_of_source_bound_and_growth
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {old : TaoSection7Triangle} {A p p' : ℕ}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hblack : black (pointAt p'))
    (hmem_old : old.Mem (pointAt p))
    (hsize : old.size < taoSection7Case3LargeTriangleBound A p)
    (hgrowth :
      taoSection7Case3LargeTriangleBound A p ≤
        (((pointAt p').l - (pointAt p).l : ℤ) : ℝ) * Real.log 2) :
    ∃ Γ : TaoSection7Triangle,
      taoSection7Case3BlackPivotStep black family pointAt old Γ p' :=
  taoSection7Case3_exists_blackPivotStep_of_exit_height
    hcover hblack
    (taoSection7Case3_cornerL_lt_of_mem_source_bound_and_vertical_growth
      hmem_old hsize hgrowth)

end Tao
end Erdos1135SecondScale
