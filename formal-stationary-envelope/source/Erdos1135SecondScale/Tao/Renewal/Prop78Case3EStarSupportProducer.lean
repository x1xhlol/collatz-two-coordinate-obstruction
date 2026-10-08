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
# Proposition 7.8 Case 3 `E*_used` Source-Producer Packets

This module records the downstream source-facing producer interface for the
strengthened Case 3 large-triangle event `E*_used`.

It refines the raw `TaoSection7Case3EStarUsedOffsetSupport` consumer from
`Prop78Case3Event` into named packets: deterministic finite cover, Lemma 7.10
admissibility schedule, per-offset probability estimate, and finite-sum
budget.  The analytic source proofs remain future inputs.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

noncomputable section

/--
Deterministic finite-cover packet for the strengthened Case 3 event.

The bound is fixed to the K-cut threshold `4^Kcut (1+p)^3`; routes using a
different repaired threshold should add a parallel packet rather than hiding
the scale in the final support record.
-/
structure TaoSection7Case3EStarUsedKcutCover
    {Ω : Type*} [Fintype Ω]
    (pointAt : Ω → ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (EStarUsed : Set Ω)
    (Kcut : ℕ)
    (inspected : Set ℕ) where
  allowed : Finset ℕ
  cover :
    EStarUsed ⊆
      {ω | ∃ p, p ∈ allowed ∧
        taoSection7Case3LargeTriangleEvent (pointAt ω) family p
          (taoSection7Case3LargeTriangleBound Kcut p)}
  inspected_mem_allowed :
    ∀ p, p ∈ inspected → p ∈ allowed

/--
K-cut admissibility schedule for applying the Lemma 7.10 large-event estimate.

This is intentionally separate from the finite-sum budget: a large `Kcut` helps
the sum, but the same threshold must still lie in Lemma 7.10's source domain.
-/
structure TaoSection7Case3KcutAdmissibilitySchedule
    (allowed : Finset ℕ) (m Kcut : ℕ) : Prop where
  p_range :
    ∀ p, p ∈ allowed →
      (p : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10)
  bound_pos :
    ∀ p, p ∈ allowed →
      1 ≤ taoSection7Case3LargeTriangleBound Kcut p
  bound_le_m :
    ∀ p, p ∈ allowed →
      taoSection7Case3LargeTriangleBound Kcut p ≤
        Real.rpow (m : ℝ) ((2 : ℝ) / 5)

theorem TaoSection7Case3KcutAdmissibilitySchedule.admissible
    {allowed : Finset ℕ} {m Kcut p : ℕ}
    (h : TaoSection7Case3KcutAdmissibilitySchedule allowed m Kcut)
    (hp : p ∈ allowed) :
    TaoSection7Case3EStarUsedOffsetAdmissible m p
      (taoSection7Case3LargeTriangleBound Kcut p) :=
  ⟨h.p_range p hp, h.bound_pos p hp, h.bound_le_m p hp⟩

/--
Uniform constants for the Lemma 7.10 large-triangle estimate.

The signs are part of the source meaning of the packet: `C710` is the
nonnegative implicit constant and `c710` is the positive exponential-decay
constant.
-/
structure TaoSection7Lemma710Constants where
  C710 : ℝ
  c710 : ℝ
  C710_nonneg : 0 ≤ C710
  c710_pos : 0 < c710

/--
Per-offset Lemma 7.10 probability packet for the K-cut large-triangle events.

The displayed budget shape mirrors the source estimate, while `prob_le` is the
field consumed by the finite-union algebra.  The constants are source-uniform;
the analytic proof is not produced here.
-/
structure TaoSection7Case3KcutPerOffsetProbabilityPacket
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (pointAt : Ω → ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (allowed : Finset ℕ)
    (Aweight Kcut : ℕ)
    (constants : TaoSection7Lemma710Constants) where
  perBudget : ℕ → ℝ
  perBudget_eq :
    ∀ p, p ∈ allowed →
      perBudget p =
        constants.C710 *
            (((Aweight : ℝ) ^ 2 * (1 + (p : ℝ))) /
              taoSection7Case3LargeTriangleBound Kcut p) +
          constants.C710 *
            Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2 * (1 + (p : ℝ))))
  prob_le :
    ∀ p, p ∈ allowed →
      pmfProb μ
        {ω | taoSection7Case3LargeTriangleEvent (pointAt ω) family p
          (taoSection7Case3LargeTriangleBound Kcut p)}
        ≤ perBudget p

/-- Finite-sum budget packet for the K-cut `E*_used` support producer. -/
structure TaoSection7Case3KcutFiniteSumBudgetPacket
    (allowed : Finset ℕ) (perBudget : ℕ → ℝ)
    (Aweight Kcut : ℕ) : Prop where
  sum_budget :
    allowed.sum perBudget ≤ (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut)

/--
Assemble the raw `E*_used` support record from the source-facing K-cut packets.

This constructor is the intended credit boundary for the next Case 3 producer:
it cannot be built without a named Lemma 7.10 admissibility schedule and a
separate finite-sum budget.
-/
def TaoSection7Case3EStarUsedOffsetSupport.of_kcutPackets
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {Aweight Kcut m : ℕ}
    {inspected : Set ℕ}
    {constants : TaoSection7Lemma710Constants}
    (cover :
      TaoSection7Case3EStarUsedKcutCover
        pointAt family EStarUsed Kcut inspected)
    (admissible :
      TaoSection7Case3KcutAdmissibilitySchedule cover.allowed m Kcut)
    (perOffset :
      TaoSection7Case3KcutPerOffsetProbabilityPacket
        μ pointAt family cover.allowed Aweight Kcut constants)
    (budget :
      TaoSection7Case3KcutFiniteSumBudgetPacket
        cover.allowed perOffset.perBudget Aweight Kcut) :
    TaoSection7Case3EStarUsedOffsetSupport
      μ pointAt family EStarUsed Aweight Kcut m inspected where
  allowed := cover.allowed
  bound := taoSection7Case3LargeTriangleBound Kcut
  perBudget := perOffset.perBudget
  cover := cover.cover
  inspected_mem_allowed := cover.inspected_mem_allowed
  source_threshold := by
    intro p _hp
    exact Or.inl rfl
  admissible := by
    intro p hp
    exact admissible.admissible hp
  per_offset_prob := perOffset.prob_le
  sum_budget := budget.sum_budget

/--
Probability-bound consumer for the source-facing K-cut packets.

The proof is just the existing finite-support consumer after assembling the
explicit support record.
-/
theorem taoSection7Case3_prob_EStarUsed_le_of_kcutPackets
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {Aweight Kcut m : ℕ}
    {inspected : Set ℕ}
    {constants : TaoSection7Lemma710Constants}
    (cover :
      TaoSection7Case3EStarUsedKcutCover
        pointAt family EStarUsed Kcut inspected)
    (admissible :
      TaoSection7Case3KcutAdmissibilitySchedule cover.allowed m Kcut)
    (perOffset :
      TaoSection7Case3KcutPerOffsetProbabilityPacket
        μ pointAt family cover.allowed Aweight Kcut constants)
    (budget :
      TaoSection7Case3KcutFiniteSumBudgetPacket
        cover.allowed perOffset.perBudget Aweight Kcut) :
    pmfProb μ EStarUsed ≤ (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) :=
  taoSection7Case3_prob_EStarUsed_le_of_finite_used_offsets
    (μ := μ)
    (support :=
      TaoSection7Case3EStarUsedOffsetSupport.of_kcutPackets
        (μ := μ) cover admissible perOffset budget)

/--
Deterministic finite-cover packet for a base-repaired Case 3 event.

This is the source-credit sibling of the same-base K-cut packet.  The event
threshold is `base^Kcut (1+p)^3`, while the downstream probability target
remains normalized against `4^Kcut`.
-/
structure TaoSection7Case3EStarUsedBaseKcutCover
    {Ω : Type*} [Fintype Ω]
    (pointAt : Ω → ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (EStarUsed : Set Ω)
    (base Kcut : ℕ)
    (inspected : Set ℕ) where
  base_ge_four : 4 ≤ base
  allowed : Finset ℕ
  cover :
    EStarUsed ⊆
      {ω | ∃ p, p ∈ allowed ∧
        taoSection7Case3LargeTriangleEvent (pointAt ω) family p
          (taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p)}
  inspected_mem_allowed :
    ∀ p, p ∈ inspected → p ∈ allowed

/--
Base-repaired admissibility schedule for applying Lemma 7.10.

The larger base is only useful if the resulting threshold is still inside the
same source domain `1 <= s' <= m^0.4`.
-/
structure TaoSection7Case3BaseKcutAdmissibilitySchedule
    (allowed : Finset ℕ) (base m Kcut : ℕ) : Prop where
  base_ge_four : 4 ≤ base
  p_range :
    ∀ p, p ∈ allowed →
      (p : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10)
  bound_pos :
    ∀ p, p ∈ allowed →
      1 ≤ taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p
  bound_le_m :
    ∀ p, p ∈ allowed →
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p ≤
        Real.rpow (m : ℝ) ((2 : ℝ) / 5)

theorem TaoSection7Case3BaseKcutAdmissibilitySchedule.admissible
    {allowed : Finset ℕ} {base m Kcut p : ℕ}
    (h : TaoSection7Case3BaseKcutAdmissibilitySchedule allowed base m Kcut)
    (hp : p ∈ allowed) :
    TaoSection7Case3EStarUsedOffsetAdmissible m p
      (taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p) :=
  ⟨h.p_range p hp, h.bound_pos p hp, h.bound_le_m p hp⟩

theorem taoSection7Case3LargeTriangleBoundWithBase_mono_p
    {base : ℝ} (hbase : 0 ≤ base) (Kcut : ℕ) :
    Monotone (taoSection7Case3LargeTriangleBoundWithBase base Kcut) := by
  intro p q hpq
  dsimp [taoSection7Case3LargeTriangleBoundWithBase]
  gcongr

theorem taoSection7Case3LargeTriangleBoundWithBase_one_le
    {base : ℕ} (hbase : 1 ≤ base) (Kcut p : ℕ) :
    1 ≤ taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p := by
  dsimp [taoSection7Case3LargeTriangleBoundWithBase]
  have hbase_real : (1 : ℝ) ≤ (base : ℝ) := by
    exact_mod_cast hbase
  have hpow : (1 : ℝ) ≤ (base : ℝ) ^ Kcut := one_le_pow₀ hbase_real
  have hp_nonneg : 0 ≤ (p : ℝ) := by
    exact_mod_cast Nat.zero_le p
  have honep : (1 : ℝ) ≤ 1 + (p : ℝ) := by
    nlinarith
  have hcube : (1 : ℝ) ≤ (1 + (p : ℝ)) ^ 3 := one_le_pow₀ honep
  have hpow_nonneg : 0 ≤ (base : ℝ) ^ Kcut := le_trans zero_le_one hpow
  have hmul :
      (1 : ℝ) * 1 ≤ (base : ℝ) ^ Kcut * (1 + (p : ℝ)) ^ 3 :=
    mul_le_mul hpow hcube zero_le_one hpow_nonneg
  simpa using hmul

/--
Finite-cap admissibility package for the base-repaired Lemma 7.10 schedule.

The cap is on actually used/allowed offsets, not on all offsets below `m`.
This is the source-shaped way to choose `m` after the deterministic finite
offset range is known.
-/
structure TaoSection7Case3BaseKcutAllowedCapAdmissibility
    (allowed : Finset ℕ) (base m Kcut Pmax : ℕ) : Prop where
  base_ge_four : 4 ≤ base
  allowed_le_Pmax : ∀ p, p ∈ allowed → p ≤ Pmax
  Pmax_range :
    (Pmax : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10)
  bound_le_m_at_Pmax :
    taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut Pmax ≤
      Real.rpow (m : ℝ) ((2 : ℝ) / 5)

theorem TaoSection7Case3BaseKcutAllowedCapAdmissibility.to_admissibilitySchedule
    {allowed : Finset ℕ} {base m Kcut Pmax : ℕ}
    (h :
      TaoSection7Case3BaseKcutAllowedCapAdmissibility
        allowed base m Kcut Pmax) :
    TaoSection7Case3BaseKcutAdmissibilitySchedule allowed base m Kcut where
  base_ge_four := h.base_ge_four
  p_range := by
    intro p hp
    have hp_le_Pmax : (p : ℝ) ≤ (Pmax : ℝ) := by
      exact_mod_cast h.allowed_le_Pmax p hp
    exact hp_le_Pmax.trans h.Pmax_range
  bound_pos := by
    intro p _hp
    have hbase_one : 1 ≤ base :=
      le_trans (by norm_num : 1 ≤ 4) h.base_ge_four
    exact
      taoSection7Case3LargeTriangleBoundWithBase_one_le
        (base := base) hbase_one Kcut p
  bound_le_m := by
    intro p hp
    have hbase_nonneg : 0 ≤ (base : ℝ) := by
      exact_mod_cast Nat.zero_le base
    exact
      ((taoSection7Case3LargeTriangleBoundWithBase_mono_p
          (base := (base : ℝ)) hbase_nonneg Kcut)
        (h.allowed_le_Pmax p hp)).trans h.bound_le_m_at_Pmax

/--
Cap provenance for the actual finite cover used by the base-`Kcut` `E*_used`
packet.  This ties the offset cap to `cover.allowed` instead of introducing a
fresh unrelated allowed set.
-/
structure TaoSection7Case3BaseKcutCoverAllowedCap
    {Ω : Type*} [Fintype Ω]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {base Kcut : ℕ}
    {inspected : Set ℕ}
    (cover :
      TaoSection7Case3EStarUsedBaseKcutCover
        pointAt family EStarUsed base Kcut inspected)
    (Pmax : ℕ) : Prop where
  allowed_le_Pmax : ∀ p, p ∈ cover.allowed → p ≤ Pmax

theorem TaoSection7Case3BaseKcutCoverAllowedCap.of_allowed_subset_range_succ
    {Ω : Type*} [Fintype Ω]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {base Kcut : ℕ}
    {inspected : Set ℕ}
    {cover :
      TaoSection7Case3EStarUsedBaseKcutCover
        pointAt family EStarUsed base Kcut inspected}
    {Pmax : ℕ}
    (hsubset : cover.allowed ⊆ Finset.range (Pmax + 1)) :
    TaoSection7Case3BaseKcutCoverAllowedCap cover Pmax where
  allowed_le_Pmax := by
    intro p hp
    have hp_lt : p < Pmax + 1 := Finset.mem_range.mp (hsubset hp)
    omega

def TaoSection7Case3BaseKcutCoverAllowedCap.to_allowedCapAdmissibility
    {Ω : Type*} [Fintype Ω]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {base Kcut : ℕ}
    {inspected : Set ℕ}
    {cover :
      TaoSection7Case3EStarUsedBaseKcutCover
        pointAt family EStarUsed base Kcut inspected}
    {m Pmax : ℕ}
    (hcap : TaoSection7Case3BaseKcutCoverAllowedCap cover Pmax)
    (Pmax_range :
      (Pmax : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10))
    (bound_le_m_at_Pmax :
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut Pmax ≤
        Real.rpow (m : ℝ) ((2 : ℝ) / 5)) :
    TaoSection7Case3BaseKcutAllowedCapAdmissibility
      cover.allowed base m Kcut Pmax where
  base_ge_four := cover.base_ge_four
  allowed_le_Pmax := hcap.allowed_le_Pmax
  Pmax_range := Pmax_range
  bound_le_m_at_Pmax := bound_le_m_at_Pmax

def TaoSection7Case3BaseKcutCoverAllowedCap.to_admissibilitySchedule
    {Ω : Type*} [Fintype Ω]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {base Kcut : ℕ}
    {inspected : Set ℕ}
    {cover :
      TaoSection7Case3EStarUsedBaseKcutCover
        pointAt family EStarUsed base Kcut inspected}
    {m Pmax : ℕ}
    (hcap : TaoSection7Case3BaseKcutCoverAllowedCap cover Pmax)
    (Pmax_range :
      (Pmax : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10))
    (bound_le_m_at_Pmax :
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut Pmax ≤
        Real.rpow (m : ℝ) ((2 : ℝ) / 5)) :
    TaoSection7Case3BaseKcutAdmissibilitySchedule
      cover.allowed base m Kcut :=
  (hcap.to_allowedCapAdmissibility
    Pmax_range bound_le_m_at_Pmax).to_admissibilitySchedule

/--
Per-offset Lemma 7.10 packet for the base-repaired large-triangle events.

The constants are the same source-uniform Lemma 7.10 constants used in the
same-base packet.
-/
structure TaoSection7Case3BaseKcutPerOffsetProbabilityPacket
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (pointAt : Ω → ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (allowed : Finset ℕ)
    (Aweight base Kcut : ℕ)
    (constants : TaoSection7Lemma710Constants) where
  base_ge_four : 4 ≤ base
  perBudget : ℕ → ℝ
  perBudget_eq :
    ∀ p, p ∈ allowed →
      perBudget p =
        constants.C710 *
            (((Aweight : ℝ) ^ 2 * (1 + (p : ℝ))) /
              taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p) +
          constants.C710 *
            Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2 * (1 + (p : ℝ))))
  prob_le :
    ∀ p, p ∈ allowed →
      pmfProb μ
        {ω | taoSection7Case3LargeTriangleEvent (pointAt ω) family p
          (taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p)}
        ≤ perBudget p

/--
Two-part scalar budget packet for the base-repaired finite sum.

The `polynomialBudget` and `exponentialBudget` fields make the future scalar
absorption visible instead of hiding it inside a raw `sum_budget` premise.
-/
structure TaoSection7Case3BaseKcutFiniteSumBudgetPacket
    (allowed : Finset ℕ) (perBudget : ℕ → ℝ)
    (Aweight base Kcut : ℕ) where
  base_ge_four : 4 ≤ base
  polynomialBudget : ℝ
  exponentialBudget : ℝ
  polynomial_nonneg : 0 ≤ polynomialBudget
  exponential_nonneg : 0 ≤ exponentialBudget
  sum_perBudget_le :
    allowed.sum perBudget ≤ polynomialBudget + exponentialBudget
  scalar_tail_budget :
    polynomialBudget + exponentialBudget ≤
      (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut)

theorem TaoSection7Case3BaseKcutFiniteSumBudgetPacket.sum_budget
    {allowed : Finset ℕ} {perBudget : ℕ → ℝ}
    {Aweight base Kcut : ℕ}
    (h :
      TaoSection7Case3BaseKcutFiniteSumBudgetPacket
        allowed perBudget Aweight base Kcut) :
    allowed.sum perBudget ≤ (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) :=
  h.sum_perBudget_le.trans h.scalar_tail_budget

/--
Assemble the raw `E*_used` support record from base-repaired packets.

The source-threshold field uses the repaired right branch of
`TaoSection7Case3EStarUsedOffsetSupport.source_threshold`.
-/
def TaoSection7Case3EStarUsedOffsetSupport.of_baseKcutPackets
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {Aweight base Kcut m : ℕ}
    {inspected : Set ℕ}
    {constants : TaoSection7Lemma710Constants}
    (cover :
      TaoSection7Case3EStarUsedBaseKcutCover
        pointAt family EStarUsed base Kcut inspected)
    (admissible :
      TaoSection7Case3BaseKcutAdmissibilitySchedule
        cover.allowed base m Kcut)
    (perOffset :
      TaoSection7Case3BaseKcutPerOffsetProbabilityPacket
        μ pointAt family cover.allowed Aweight base Kcut constants)
    (budget :
      TaoSection7Case3BaseKcutFiniteSumBudgetPacket
        cover.allowed perOffset.perBudget Aweight base Kcut) :
    TaoSection7Case3EStarUsedOffsetSupport
      μ pointAt family EStarUsed Aweight Kcut m inspected where
  allowed := cover.allowed
  bound := taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut
  perBudget := perOffset.perBudget
  cover := cover.cover
  inspected_mem_allowed := cover.inspected_mem_allowed
  source_threshold := by
    intro p _hp
    refine Or.inr ⟨(base : ℝ), ?_, rfl⟩
    exact_mod_cast cover.base_ge_four
  admissible := by
    intro p hp
    exact admissible.admissible hp
  per_offset_prob := perOffset.prob_le
  sum_budget := budget.sum_budget

/--
Probability-bound consumer for the base-repaired packet family.

This is still conditional on the packet fields; it only ensures all fields
feed the same existing `E*_used` finite-support consumer.
-/
theorem taoSection7Case3_prob_EStarUsed_le_of_baseKcutPackets
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {Aweight base Kcut m : ℕ}
    {inspected : Set ℕ}
    {constants : TaoSection7Lemma710Constants}
    (cover :
      TaoSection7Case3EStarUsedBaseKcutCover
        pointAt family EStarUsed base Kcut inspected)
    (admissible :
      TaoSection7Case3BaseKcutAdmissibilitySchedule
        cover.allowed base m Kcut)
    (perOffset :
      TaoSection7Case3BaseKcutPerOffsetProbabilityPacket
        μ pointAt family cover.allowed Aweight base Kcut constants)
    (budget :
      TaoSection7Case3BaseKcutFiniteSumBudgetPacket
        cover.allowed perOffset.perBudget Aweight base Kcut) :
    pmfProb μ EStarUsed ≤ (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) :=
  taoSection7Case3_prob_EStarUsed_le_of_finite_used_offsets
    (μ := μ)
    (support :=
      TaoSection7Case3EStarUsedOffsetSupport.of_baseKcutPackets
        (μ := μ) cover admissible perOffset budget)

end

end Tao
end Erdos1135SecondScale
