/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Section7Character
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Section 7 Source Law

This module proves the exact source-law bridge from the recursive `syracPMF`
definition to Tao's iid positive `Geom(2)` valuation-list character sum.
-/

open scoped BigOperators
open scoped ZMod

/-!
It intentionally does not prove Fourier decay, all-nonzero estimates, or any
Section 6 bridge.
-/

namespace Erdos1135SecondScale
namespace Tao

theorem syracPMF_zero_eq_geom2PNatListPMF_map_taoSection7OffsetZMod :
    syracPMF 0 =
      (geom2PNatListPMF 0).map (fun as => taoSection7OffsetZMod 0 as) := by
  rw [syracPMF, geom2PNatListPMF, PMF.pure_map]
  simp [taoSection7OffsetZMod]

theorem syracPMF_succ_eq_geom2PNatListPMF_map_taoSection7OffsetZMod
    (n : ℕ)
    (h : syracPMF n =
      (geom2PNatListPMF n).map (fun as => taoSection7OffsetZMod n as)) :
    syracPMF (n + 1) =
      (geom2PNatListPMF (n + 1)).map
        (fun as => taoSection7OffsetZMod (n + 1) as) := by
  rw [syracPMF, h, PMF.bind_map]
  change
    (geom2PNatListPMF n).bind (fun as =>
      geom2PNat.bind (fun a =>
        PMF.pure (syracStep n (taoSection7OffsetZMod n as) a))) =
    (geom2PNatListPMF (n + 1)).map
      (fun as => taoSection7OffsetZMod (n + 1) as)
  rw [PMF.bind_comm]
  rw [geom2PNatListPMF, PMF.map_bind]
  congr 1
  funext a
  rw [PMF.map_comp]
  simp only [PMF.map]
  congr 1
  funext as
  simp [Function.comp_apply, taoSection7OffsetZMod_cons]

theorem syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod (n : ℕ) :
    syracPMF n =
      (geom2PNatListPMF n).map (fun as => taoSection7OffsetZMod n as) := by
  induction n with
  | zero =>
      exact syracPMF_zero_eq_geom2PNatListPMF_map_taoSection7OffsetZMod
  | succ n ih =>
      exact syracPMF_succ_eq_geom2PNatListPMF_map_taoSection7OffsetZMod n ih

theorem syracPMF_two_eq_geom2PNatListPMF_map_taoSection7OffsetZMod :
    syracPMF 2 =
      (geom2PNatListPMF 2).map (fun as => taoSection7OffsetZMod 2 as) :=
  syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod 2

theorem pmf_summable_toReal {α : Type*} (p : PMF α) :
    Summable fun a : α => (p a).toReal := by
  refine ENNReal.summable_toReal ?_
  rw [PMF.tsum_coe p]
  norm_num

theorem pmf_map_apply_toReal_tsum {α β : Type*} [DecidableEq β]
    (p : PMF α) (f : α → β) (b : β) :
    ((p.map f) b).toReal =
      ∑' a : α, if b = f a then (p a).toReal else 0 := by
  classical
  calc
    ((p.map f) b).toReal
        = ∑' a : α,
            @ite ℝ (b = f a) (Classical.propDecidable (b = f a)) (p a).toReal 0 := by
            rw [PMF.map_apply]
            rw [ENNReal.tsum_toReal_eq]
            · apply tsum_congr
              intro a
              by_cases h : b = f a <;> simp [h]
            · intro a
              by_cases h : b = f a <;> simp [h, PMF.apply_ne_top p a]
    _ = ∑' a : α, if b = f a then (p a).toReal else 0 := by
            apply tsum_congr
            intro a
            by_cases h : b = f a <;> simp [h]

private theorem source_kernel_indicator_summable {α β : Type*} [DecidableEq β]
    (p : PMF α) (f : α → β) (w : β → ℂ) (b : β) :
    Summable fun a : α =>
      w b * ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ) := by
  classical
  have htop_classical :
      (∑' a : α,
        @ite ENNReal (b = f a) (Classical.propDecidable (b = f a)) (p a) 0) ≠ ⊤ := by
    simpa [PMF.map_apply] using PMF.apply_ne_top (p.map f) b
  have htop : (∑' a : α, if b = f a then p a else 0) ≠ ⊤ := by
    have heq : (∑' a : α, if b = f a then p a else 0) =
        ∑' a : α,
          @ite ENNReal (b = f a) (Classical.propDecidable (b = f a)) (p a) 0 := by
      apply tsum_congr
      intro a
      by_cases h : b = f a <;> simp [h]
    rw [heq]
    exact htop_classical
  have hreal : Summable fun a : α =>
      (if b = f a then p a else 0 : ENNReal).toReal :=
    ENNReal.summable_toReal htop
  have hreal' : Summable fun a : α =>
      if b = f a then (p a).toReal else 0 := by
    refine hreal.congr ?_
    intro a
    by_cases h : b = f a <;> simp [h]
  have hcomplex : Summable fun a : α =>
      ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ) := by
    simpa using Complex.ofRealCLM.summable hreal'
  exact Summable.mul_left (w b) hcomplex

theorem finite_kernel_indicator_sum {α β : Type*} [Fintype β] [DecidableEq β]
    (p : PMF α) (f : α → β) (w : β → ℂ) :
    (∑ b : β, w b * (((p.map f) b).toReal : ℂ)) =
      ∑' a : α, w (f a) * (((p a).toReal : ℝ) : ℂ) := by
  classical
  calc
    (∑ b : β, w b * (((p.map f) b).toReal : ℂ))
        = ∑ b : β, w b * (∑' a : α,
              ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro b _hb
            rw [pmf_map_apply_toReal_tsum p f b]
            rw [Complex.ofReal_tsum]
    _ = ∑ b : β, ∑' a : α,
            w b * ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro b _hb
            rw [tsum_mul_left]
    _ = ∑' a : α, ∑ b : β,
            w b * ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ) := by
            simpa using
              (Summable.tsum_finsetSum (s := (Finset.univ : Finset β))
                (f := fun b a =>
                  w b * ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ))
                (fun b _hb => source_kernel_indicator_summable p f w b)).symm
    _ = ∑' a : α, w (f a) * (((p a).toReal : ℝ) : ℂ) := by
            apply tsum_congr
            intro a
            rw [Finset.sum_eq_single_of_mem (f a) (Finset.mem_univ (f a))]
            · simp
            · intro b _hb hb
              simp [hb]

theorem dft_map_source_sum_core {α : Type*} {N : ℕ} [NeZero N]
    (p : PMF α) (f : α → ZMod N) (ξ : ZMod N) :
    (∑ x : ZMod N,
        taoForwardDFTKernel x ξ * (((p.map f) x).toReal : ℂ)) =
      ∑' a : α,
        taoForwardDFTKernel (f a) ξ * (((p a).toReal : ℝ) : ℂ) := by
  exact finite_kernel_indicator_sum p f (fun x => taoForwardDFTKernel x ξ)

theorem tao_dft_pmfComplexMass_map_apply {α : Type*} {N : ℕ} [NeZero N]
    (p : PMF α) (f : α → ZMod N) (ξ : ZMod N) :
    ZMod.dft (pmfComplexMass (p.map f)) ξ =
      ∑' a : α,
        taoForwardDFTKernel (f a) ξ * (((p a).toReal : ℝ) : ℂ) := by
  rw [tao_dft_pmfComplexMass_apply]
  exact dft_map_source_sum_core p f ξ

theorem dft_geom2PNatListPMF_map_taoSection7OffsetZMod_eq_schi
    (n : ℕ) (ξ : ZMod (3 ^ n)) :
    ZMod.dft
        (pmfComplexMass
          ((geom2PNatListPMF n).map (fun as => taoSection7OffsetZMod n as))) ξ =
      taoSection7SChi n ξ := by
  rw [tao_dft_pmfComplexMass_map_apply]
  unfold taoSection7SChi taoSection7CharacterTerm
  apply tsum_congr
  intro as
  ring

theorem TaoSection7CharacterBridgeStatement.source_law :
    TaoSection7CharacterBridgeStatement := by
  intro n _ xi _
  rw [syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod n]
  exact dft_geom2PNatListPMF_map_taoSection7OffsetZMod_eq_schi n xi

end Tao
end Erdos1135SecondScale
