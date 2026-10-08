/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Truncation
import Erdos1135SecondScale.Tao.Syracuse.CylinderMass

/-!
# First Finite Valuation-Distribution Package

This module packages the pointwise positive `Geom(2)` valuation-tuple mass and connects it to the
checked head-true Syracuse cylinder-prefix mass.  It also defines the exact-length iid list PMF and
finite bounded-tuple total masses.  It intentionally does not define finite `Syrac`, Fourier
transforms, renewal estimates, a pushforward representation of the truncated overflow PMF, or
Proposition 1.9 bounds.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Pointwise product mass of a finite positive valuation list under independent `Geom(2)` laws. -/
noncomputable def geom2PNatListMass (as : List ℕ+) : ℝ :=
  (as.map fun a => (geom2PNat a).toReal).prod

theorem one_div_two_pow_eq_inv_pow (n : ℕ) :
    (1 / 2 : ℝ) ^ n = (1 : ℝ) / (2 ^ n : ℝ) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      field_simp [pow_ne_zero]

theorem geom2PNatListMass_eq_pow (as : List ℕ+) :
    geom2PNatListMass as = (1 / 2 : ℝ) ^ taoTupleWeight as := by
  induction as with
  | nil =>
      simp [geom2PNatListMass, taoTupleWeight]
  | cons a as ih =>
      rw [geom2PNatListMass] at ih
      simp [taoTupleWeight, geom2PNat_apply_toReal] at ih
      simp [geom2PNatListMass, taoTupleWeight, geom2PNat_apply_toReal, ih, pow_add]

theorem geom2PNatListMass_eq_inv_pow (as : List ℕ+) :
    geom2PNatListMass as = (1 : ℝ) / (2 ^ taoTupleWeight as : ℝ) := by
  rw [geom2PNatListMass_eq_pow, one_div_two_pow_eq_inv_pow]

noncomputable def geom2PNatListPMF : ℕ → PMF (List ℕ+)
  | 0 => PMF.pure []
  | n + 1 => geom2PNat.bind fun a =>
      (geom2PNatListPMF n).map fun as => a :: as

theorem geom2PNatListPMF_zero_apply_nil :
    geom2PNatListPMF 0 [] = 1 := by
  simp [geom2PNatListPMF]

theorem geom2PNatListPMF_zero_apply_cons (a : ℕ+) (as : List ℕ+) :
    geom2PNatListPMF 0 (a :: as) = 0 := by
  simp [geom2PNatListPMF]

theorem geom2PNatListPMF_succ_apply_cons (n : ℕ) (a : ℕ+) (as : List ℕ+) :
    geom2PNatListPMF (n + 1) (a :: as) =
      geom2PNat a * geom2PNatListPMF n as := by
  classical
  rw [geom2PNatListPMF, PMF.bind_apply]
  have hmap : ∀ a' : ℕ+,
      ((geom2PNatListPMF n).map fun bs => a' :: bs) (a :: as) =
        if a = a' then geom2PNatListPMF n as else 0 := by
    intro a'
    rw [PMF.map_apply]
    by_cases h : a = a'
    · subst h
      rw [tsum_eq_single as]
      · simp
      · intro bs hbs
        have hc : ¬ a :: as = a :: bs := by
          intro hcons
          exact hbs (List.cons.inj hcons).2.symm
        simp [hc]
    · have hnone : ∀ bs : List ℕ+, ¬ a :: as = a' :: bs := by
        intro bs hcons
        exact h (List.cons.inj hcons).1
      simp [h, hnone]
  calc
    (∑' a' : ℕ+,
        geom2PNat a' * ((geom2PNatListPMF n).map fun bs => a' :: bs) (a :: as))
        = ∑' a' : ℕ+,
            geom2PNat a' * (if a = a' then geom2PNatListPMF n as else 0) := by
          apply tsum_congr
          intro a'
          rw [hmap a']
    _ = geom2PNat a * geom2PNatListPMF n as := by
          rw [tsum_eq_single a]
          · simp
          · intro a' ha'
            simp [ha'.symm]

theorem geom2PNatListPMF_apply_length_toReal (as : List ℕ+) :
    (geom2PNatListPMF as.length as).toReal = geom2PNatListMass as := by
  induction as with
  | nil =>
      simp [geom2PNatListPMF, geom2PNatListMass]
  | cons a as ih =>
      rw [List.length_cons, geom2PNatListPMF_succ_apply_cons]
      rw [ENNReal.toReal_mul, ih]
      simp [geom2PNatListMass]

theorem geom2PNatListPMF_apply_length_toReal_eq_weight (as : List ℕ+) :
    (geom2PNatListPMF as.length as).toReal =
      (1 / 2 : ℝ) ^ taoTupleWeight as := by
  rw [geom2PNatListPMF_apply_length_toReal, geom2PNatListMass_eq_pow]

theorem geom2PNatListPMF_succ_apply_nil (n : ℕ) :
    geom2PNatListPMF (n + 1) [] = 0 := by
  classical
  rw [geom2PNatListPMF, PMF.bind_apply]
  simp [PMF.map_apply]

theorem geom2PNatListPMF_apply_eq_zero_of_length_ne
    (n : ℕ) (as : List ℕ+) (h : as.length ≠ n) :
    geom2PNatListPMF n as = 0 := by
  induction n generalizing as with
  | zero =>
      cases as with
      | nil => exact (h rfl).elim
      | cons a as => simp [geom2PNatListPMF]
  | succ n ih =>
      cases as with
      | nil =>
          exact geom2PNatListPMF_succ_apply_nil n
      | cons a as =>
          rw [geom2PNatListPMF_succ_apply_cons]
          have htail : as.length ≠ n := by
            intro hs
            exact h (by simp [hs])
          rw [ih as htail, mul_zero]

/-- Every list in the support of the iid Geom(2) list law has the prescribed length. -/
theorem geom2PNatListPMF_support_length_eq
    {n : ℕ} {as : List ℕ+}
    (has : as ∈ (geom2PNatListPMF n).support) :
    as.length = n := by
  by_contra hlength
  have hnonzero : geom2PNatListPMF n as ≠ 0 :=
    ((geom2PNatListPMF n).mem_support_iff as).mp has
  exact hnonzero
    (geom2PNatListPMF_apply_eq_zero_of_length_ne n as hlength)

theorem geom2PNatListMass_eq_headTrue_syracuseCylinderPrefix
    (K : ℕ) (as : List ℕ+) (hK : taoTupleWeight as ≤ K) :
    geom2PNatListMass as =
      pmfProb (PMF.uniformOfFintype (HeadTrueParityWords K))
        {w : HeadTrueParityWords K |
          ∀ i : Fin (syracuseValuationCylinderTail as).length,
            (headTrueParityWordsEquivTail K w)
              ⟨i.1, Nat.lt_of_lt_of_le i.2 (by
                rw [syracuseValuationCylinderTail_length]
                exact hK)⟩ = (syracuseValuationCylinderTail as).get i} := by
  rw [geom2PNatListMass_eq_inv_pow]
  rw [pmfProb_uniform_headTrue_syracuseCylinderPrefix K as hK]

theorem boundedValuationTuple_geom2PNatListMass_eq_headTrue_syracuseCylinderPrefix
    {n M K : ℕ} (v : BoundedValuationTuple n M)
    (hK : taoTupleWeight (BoundedValuationTuple.toList v) ≤ K) :
    geom2PNatListMass (BoundedValuationTuple.toList v) =
      pmfProb (PMF.uniformOfFintype (HeadTrueParityWords K))
        {w : HeadTrueParityWords K |
          ∀ i : Fin (syracuseValuationCylinderTail (BoundedValuationTuple.toList v)).length,
            (headTrueParityWordsEquivTail K w)
              ⟨i.1, Nat.lt_of_lt_of_le i.2 (by
                rw [syracuseValuationCylinderTail_length]
                exact hK)⟩ =
              (syracuseValuationCylinderTail (BoundedValuationTuple.toList v)).get i} := by
  exact geom2PNatListMass_eq_headTrue_syracuseCylinderPrefix K
    (BoundedValuationTuple.toList v) hK

theorem boundedValuationTuple_toList_injective {n M : ℕ} :
    Function.Injective (BoundedValuationTuple.toList (n := n) (M := M)) := by
  intro v w h
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply Fin.ext
  have hf : (fun i : Fin n => PNatBelow.toPNat (v.1 i)) =
      (fun i : Fin n => PNatBelow.toPNat (w.1 i)) := by
    apply List.ofFn_injective
    exact h
  have hi := congrFun hf i
  exact congrArg Subtype.val hi

noncomputable def boundedValuationTupleGeom2Mass {n M : ℕ}
    (v : BoundedValuationTuple n M) : ℝ :=
  geom2PNatListMass (BoundedValuationTuple.toList v)

theorem boundedValuationTupleGeom2Mass_eq_inv_pow {n M : ℕ}
    (v : BoundedValuationTuple n M) :
    boundedValuationTupleGeom2Mass v =
      (1 : ℝ) / (2 ^ taoTupleWeight (BoundedValuationTuple.toList v) : ℝ) :=
  geom2PNatListMass_eq_inv_pow (BoundedValuationTuple.toList v)

noncomputable def boundedValuationTupleGeom2TotalMass (n M : ℕ) : ℝ :=
  ∑ v : BoundedValuationTuple n M, boundedValuationTupleGeom2Mass v

theorem boundedValuationTupleGeom2TotalMass_nonneg (n M : ℕ) :
    0 ≤ boundedValuationTupleGeom2TotalMass n M := by
  unfold boundedValuationTupleGeom2TotalMass
  exact Finset.sum_nonneg fun v _ => by
    rw [boundedValuationTupleGeom2Mass_eq_inv_pow]
    positivity

theorem boundedValuationTupleGeom2TotalMass_eq_sum_inv_pow (n M : ℕ) :
    boundedValuationTupleGeom2TotalMass n M =
      ∑ v : BoundedValuationTuple n M,
        (1 : ℝ) / (2 ^ taoTupleWeight (BoundedValuationTuple.toList v) : ℝ) := by
  unfold boundedValuationTupleGeom2TotalMass boundedValuationTupleGeom2Mass
  apply Finset.sum_congr rfl
  intro v _hv
  exact geom2PNatListMass_eq_inv_pow (BoundedValuationTuple.toList v)

theorem boundedValuationTupleGeom2TotalMass_eq_sum_headTruePrefix
    (n M K : ℕ) (hMK : M ≤ K + 1) :
    boundedValuationTupleGeom2TotalMass n M =
      ∑ v : BoundedValuationTuple n M,
        pmfProb (PMF.uniformOfFintype (HeadTrueParityWords K))
          {w : HeadTrueParityWords K |
            ∀ i : Fin (syracuseValuationCylinderTail (BoundedValuationTuple.toList v)).length,
              (headTrueParityWordsEquivTail K w)
                ⟨i.1, Nat.lt_of_lt_of_le i.2 (by
                  rw [syracuseValuationCylinderTail_length]
                  have hv := BoundedValuationTuple.taoTupleWeight_toList_lt v
                  omega)⟩ =
                (syracuseValuationCylinderTail (BoundedValuationTuple.toList v)).get i} := by
  unfold boundedValuationTupleGeom2TotalMass boundedValuationTupleGeom2Mass
  apply Finset.sum_congr rfl
  intro v _hv
  exact boundedValuationTuple_geom2PNatListMass_eq_headTrue_syracuseCylinderPrefix v (by
    have hvw := BoundedValuationTuple.taoTupleWeight_toList_lt v
    omega)

theorem boundedValuationTupleGeom2MassENNReal_toReal {n M : ℕ}
    (v : BoundedValuationTuple n M) :
    (geom2PNatListPMF n (BoundedValuationTuple.toList v)).toReal =
      boundedValuationTupleGeom2Mass v := by
  have h := geom2PNatListPMF_apply_length_toReal (BoundedValuationTuple.toList v)
  simpa [boundedValuationTupleGeom2Mass, BoundedValuationTuple.toList_length v] using h

noncomputable def boundedValuationTupleGeom2TotalMassENNReal (n M : ℕ) : ENNReal :=
  ∑ v : BoundedValuationTuple n M,
    geom2PNatListPMF n (BoundedValuationTuple.toList v)

theorem boundedValuationTupleGeom2TotalMassENNReal_le_one (n M : ℕ) :
    boundedValuationTupleGeom2TotalMassENNReal n M ≤ 1 := by
  unfold boundedValuationTupleGeom2TotalMassENNReal
  calc
    (∑ v : BoundedValuationTuple n M,
      geom2PNatListPMF n (BoundedValuationTuple.toList v))
        ≤ ∑' v : BoundedValuationTuple n M,
            geom2PNatListPMF n (BoundedValuationTuple.toList v) := by
          exact ENNReal.sum_le_tsum Finset.univ
    _ ≤ ∑' as : List ℕ+, geom2PNatListPMF n as := by
          exact ENNReal.tsum_comp_le_tsum_of_injective
            boundedValuationTuple_toList_injective _
    _ = 1 := PMF.tsum_coe (geom2PNatListPMF n)

noncomputable def truncatedValuationTupleGeom2PMF (n M : ℕ) :
    PMF (TruncatedValuationTuple n M) :=
  PMF.ofFintype
    (fun x : TruncatedValuationTuple n M =>
      match x with
      | none => 1 - boundedValuationTupleGeom2TotalMassENNReal n M
      | some v => geom2PNatListPMF n (BoundedValuationTuple.toList v))
    (by
      rw [Fintype.sum_option]
      change (1 - boundedValuationTupleGeom2TotalMassENNReal n M) +
          (∑ v : BoundedValuationTuple n M,
            geom2PNatListPMF n (BoundedValuationTuple.toList v)) = 1
      change (1 - boundedValuationTupleGeom2TotalMassENNReal n M) +
          boundedValuationTupleGeom2TotalMassENNReal n M = 1
      exact tsub_add_cancel_of_le
        (boundedValuationTupleGeom2TotalMassENNReal_le_one n M))

theorem truncatedValuationTupleGeom2PMF_apply_none (n M : ℕ) :
    truncatedValuationTupleGeom2PMF n M none =
      1 - boundedValuationTupleGeom2TotalMassENNReal n M := by
  rw [truncatedValuationTupleGeom2PMF, PMF.ofFintype_apply]

theorem truncatedValuationTupleGeom2PMF_apply_some {n M : ℕ}
    (v : BoundedValuationTuple n M) :
    truncatedValuationTupleGeom2PMF n M (some v) =
      geom2PNatListPMF n (BoundedValuationTuple.toList v) := by
  rw [truncatedValuationTupleGeom2PMF, PMF.ofFintype_apply]

end Tao
end Erdos1135SecondScale
