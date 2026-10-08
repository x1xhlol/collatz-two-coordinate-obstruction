/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7SourceFThreeQFinite
import Erdos1135Predecessor.Tao.Fourier.Section7SourceLaw
import Erdos1135Predecessor.Tao.Fourier.Section7SourcePairing

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable def taoSection7Geom2PairPMF : PMF (ℕ+ × ℕ+) :=
  geom2PNat.bind fun a₁ => geom2PNat.map fun a₂ => (a₁, a₂)

theorem taoSection7Geom2PairPMF_map_sum_eq_pascalSourcePMF :
    taoSection7Geom2PairPMF.map
        (fun a => (a.1 : ℕ) + (a.2 : ℕ)) =
      taoSection7PascalSourcePMF := by
  unfold taoSection7Geom2PairPMF taoSection7PascalSourcePMF
  rw [PMF.map_bind]
  apply congrArg (fun f : ℕ+ → PMF ℕ => geom2PNat.bind f)
  funext a₁
  rw [PMF.map_comp]
  change
    geom2PNat.map (fun a₂ : ℕ+ => (a₁ : ℕ) + (a₂ : ℕ)) =
      (geom2PNat.map fun a₂ : ℕ+ => (a₂ : ℕ)).map
        (fun b => (a₁ : ℕ) + b)
  rw [PMF.map_comp]
  rfl

theorem taoSection7Geom2PairPMF_apply_toReal (a₁ a₂ : ℕ+) :
    (taoSection7Geom2PairPMF (a₁, a₂)).toReal =
      geom2PNatPairMass a₁ a₂ := by
  classical
  rw [taoSection7Geom2PairPMF, PMF.bind_apply]
  rw [tsum_eq_single a₁]
  · rw [PMF.map_apply]
    rw [tsum_eq_single a₂]
    · simp [geom2PNatPairMass, ENNReal.toReal_mul]
    · intro b hb
      have hpair : ¬(a₁, a₂) = (a₁, b) := by
        intro h
        exact hb (Prod.ext_iff.mp h).2.symm
      simp [hpair]
  · intro a ha
    have hmap_zero :
        (geom2PNat.map fun b => (a, b)) (a₁, a₂) = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro b
      have hpair : ¬(a₁, a₂) = (a, b) := by
        intro h
        exact ha (Prod.ext_iff.mp h).1.symm
      simp [hpair]
    simp [hmap_zero]

private def taoSection7FixedSumPairToIndex (b : ℕ) :
    {p : ℕ+ × ℕ+ // b = (p.1 : ℕ) + (p.2 : ℕ)} →
      {a : ℕ // a ∈ Finset.Icc 1 (b - 1)} :=
  fun p => ⟨(p.1.1 : ℕ), by
    rw [Finset.mem_Icc]
    constructor
    · exact p.1.1.2
    · have hp₂ : 0 < (p.1.2 : ℕ) := p.1.2.2
      omega⟩

private theorem taoSection7FixedSumPairToIndex_injective (b : ℕ) :
    Function.Injective (taoSection7FixedSumPairToIndex b) := by
  rintro ⟨⟨a₁, a₂⟩, ha⟩ ⟨⟨c₁, c₂⟩, hc⟩ h
  have h₁ : (a₁ : ℕ) = (c₁ : ℕ) :=
    congrArg (fun a : {a : ℕ // a ∈ Finset.Icc 1 (b - 1)} => (a : ℕ)) h
  have ha' : b = (a₁ : ℕ) + (a₂ : ℕ) := ha
  have hc' : b = (c₁ : ℕ) + (c₂ : ℕ) := hc
  have h₂ : (a₂ : ℕ) = (c₂ : ℕ) := by omega
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext h₁
  · exact Subtype.ext h₂

private theorem taoSection7FixedSumPairToIndex_surjective (b : ℕ) :
    Function.Surjective (taoSection7FixedSumPairToIndex b) := by
  rintro ⟨a, ha⟩
  rcases Finset.mem_Icc.mp ha with ⟨ha₁, hab⟩
  have hab' : a ≤ b := le_trans hab (Nat.sub_le b 1)
  have hba : 0 < b - a := by omega
  refine ⟨⟨(⟨a, ha₁⟩, ⟨b - a, hba⟩), ?_⟩, ?_⟩
  · exact (Nat.add_sub_of_le hab').symm
  · apply Subtype.ext
    rfl

private noncomputable def taoSection7FixedSumPairEquiv (b : ℕ) :
    {p : ℕ+ × ℕ+ // b = (p.1 : ℕ) + (p.2 : ℕ)} ≃
      {a : ℕ // a ∈ Finset.Icc 1 (b - 1)} :=
  Equiv.ofBijective (taoSection7FixedSumPairToIndex b)
    ⟨taoSection7FixedSumPairToIndex_injective b,
      taoSection7FixedSumPairToIndex_surjective b⟩

private theorem taoSection7FixedSumPair_mass
    (b : ℕ) (p : {p : ℕ+ × ℕ+ //
      b = (p.1 : ℕ) + (p.2 : ℕ)}) :
    (taoSection7Geom2PairPMF p.1).toReal =
      (1 / 2 : ℝ) ^ (p.1.1 : ℕ) *
        (1 / 2 : ℝ) ^ (b - (p.1.1 : ℕ)) := by
  rw [taoSection7Geom2PairPMF_apply_toReal]
  unfold geom2PNatPairMass
  rw [geom2PNat_apply_toReal, geom2PNat_apply_toReal]
  have hsub : b - (p.1.1 : ℕ) = (p.1.2 : ℕ) := by omega
  rw [hsub]

theorem taoSection7PascalSourcePMF_apply_toReal (b : ℕ) :
    (taoSection7PascalSourcePMF b).toReal =
      pascalGeom2PairMass b := by
  classical
  rw [← taoSection7Geom2PairPMF_map_sum_eq_pascalSourcePMF,
    pmf_map_apply_toReal_tsum]
  calc
    (∑' p : ℕ+ × ℕ+,
        if b = (p.1 : ℕ) + (p.2 : ℕ)
        then (taoSection7Geom2PairPMF p).toReal else 0) =
        ∑' p : {p : ℕ+ × ℕ+ //
          b = (p.1 : ℕ) + (p.2 : ℕ)},
          (taoSection7Geom2PairPMF p.1).toReal := by
      simpa only [Set.indicator, Set.mem_setOf_eq] using
        (tsum_subtype
          {p : ℕ+ × ℕ+ | b = (p.1 : ℕ) + (p.2 : ℕ)}
          (fun p => (taoSection7Geom2PairPMF p).toReal)).symm
    _ = ∑' a : {a : ℕ // a ∈ Finset.Icc 1 (b - 1)},
          (1 / 2 : ℝ) ^ a.1 * (1 / 2 : ℝ) ^ (b - a.1) := by
      rw [← (taoSection7FixedSumPairEquiv b).tsum_eq]
      exact tsum_congr (taoSection7FixedSumPair_mass b)
    _ = ∑ a ∈ Finset.Icc 1 (b - 1),
          (1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (b - a) := by
      rw [tsum_fintype, ← Finset.attach_eq_univ]
      exact Finset.sum_attach (Finset.Icc 1 (b - 1))
        (fun a => (1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (b - a))
    _ = pascalGeom2PairMass b := by
      rfl

noncomputable def taoSection7PairPhase
    (n : ℕ) (xi x : ZMod (3 ^ n)) (a₂ : ℕ+) : ℂ :=
  taoForwardDFTKernel
    ((((2 : ZMod (3 ^ n)) ^ (a₂ : ℕ) + 3) * x)) xi

@[simp] theorem taoSection7PairPhase_one
    (n : ℕ) (xi x : ZMod (3 ^ n)) :
    taoSection7PairPhase n xi x (1 : ℕ+) =
      taoForwardDFTKernel ((5 : ZMod (3 ^ n)) * x) xi := by
  unfold taoSection7PairPhase
  congr 2
  norm_num

@[simp] theorem taoSection7PairPhase_two
    (n : ℕ) (xi x : ZMod (3 ^ n)) :
    taoSection7PairPhase n xi x (2 : ℕ+) =
      taoForwardDFTKernel ((7 : ZMod (3 ^ n)) * x) xi := by
  simp [taoSection7PairPhase, pow_two]
  congr 2
  ring

noncomputable def taoSection7PairFiberCharacterMass
    (n : ℕ) (xi x : ZMod (3 ^ n)) (b : ℕ) : ℂ :=
  ∑' a : ℕ+ × ℕ+,
    if (a.1 : ℕ) + (a.2 : ℕ) = b then
      ((taoSection7Geom2PairPMF a).toReal : ℂ) *
        taoSection7PairPhase n xi x a.2
    else
      0

private theorem pnat_pair_eq_one_two_or_two_one_of_sum_eq_three
    (a₁ a₂ : ℕ+) (h : (a₁ : ℕ) + (a₂ : ℕ) = 3) :
    (a₁ = 1 ∧ a₂ = 2) ∨ (a₁ = 2 ∧ a₂ = 1) := by
  have ha₁pos : 0 < (a₁ : ℕ) := a₁.2
  have ha₂pos : 0 < (a₂ : ℕ) := a₂.2
  have ha₁ : (a₁ : ℕ) = 1 ∨ (a₁ : ℕ) = 2 := by omega
  rcases ha₁ with ha₁ | ha₁
  · left
    constructor
    · apply Subtype.ext
      change (a₁ : ℕ) = 1
      exact ha₁
    · apply Subtype.ext
      change (a₂ : ℕ) = 2
      omega
  · right
    constructor
    · apply Subtype.ext
      change (a₁ : ℕ) = 2
      exact ha₁
    · apply Subtype.ext
      change (a₂ : ℕ) = 1
      omega

private theorem taoSection7PairFiberCharacterMass_three_explicit
    (n : ℕ) (xi x : ZMod (3 ^ n)) :
    taoSection7PairFiberCharacterMass n xi x 3 =
      ((1 / 8 : ℝ) : ℂ) *
          taoForwardDFTKernel ((7 : ZMod (3 ^ n)) * x) xi +
        ((1 / 8 : ℝ) : ℂ) *
          taoForwardDFTKernel ((5 : ZMod (3 ^ n)) * x) xi := by
  classical
  unfold taoSection7PairFiberCharacterMass
  rw [tsum_eq_sum
    (s := ({((1 : ℕ+), (2 : ℕ+)), ((2 : ℕ+), (1 : ℕ+))} :
      Finset (ℕ+ × ℕ+)))]
  · simp [taoSection7Geom2PairPMF_apply_toReal,
      geom2PNatPairMass_one_two, geom2PNatPairMass_two_one, add_comm]
  · intro a ha
    by_cases hsum : (a.1 : ℕ) + (a.2 : ℕ) = 3
    · rcases pnat_pair_eq_one_two_or_two_one_of_sum_eq_three
          a.1 a.2 hsum with h | h
      · exfalso
        apply ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (Prod.ext h.1 h.2)
      · exfalso
        apply ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Prod.ext h.1 h.2)
    · simp [hsum]

theorem taoSection7PascalSourcePMF_three_toReal :
    (taoSection7PascalSourcePMF 3).toReal = (1 / 4 : ℝ) := by
  rw [← taoSection7Geom2PairPMF_map_sum_eq_pascalSourcePMF]
  rw [pmf_map_apply_toReal_tsum]
  classical
  rw [tsum_eq_sum
    (s := ({((1 : ℕ+), (2 : ℕ+)), ((2 : ℕ+), (1 : ℕ+))} :
      Finset (ℕ+ × ℕ+)))]
  · simp [taoSection7Geom2PairPMF_apply_toReal,
      geom2PNatPairMass_one_two, geom2PNatPairMass_two_one]
    norm_num
  · intro a ha
    by_cases hsum : (a.1 : ℕ) + (a.2 : ℕ) = 3
    · rcases pnat_pair_eq_one_two_or_two_one_of_sum_eq_three
          a.1 a.2 hsum with h | h
      · exfalso
        apply ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (Prod.ext h.1 h.2)
      · exfalso
        apply ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Prod.ext h.1 h.2)
    · have hsum' : ¬3 = (a.1 : ℕ) + (a.2 : ℕ) := by omega
      simp [hsum']

theorem taoSection7PairFiberCharacterMass_three_eq
    (n : ℕ) (xi x : ZMod (3 ^ n)) :
    taoSection7PairFiberCharacterMass n xi x 3 =
      ((taoSection7PascalSourcePMF 3).toReal : ℂ) *
        taoSection7FThree n xi x := by
  rw [taoSection7PairFiberCharacterMass_three_explicit,
    taoSection7PascalSourcePMF_three_toReal]
  unfold taoSection7FThree
  rw [geom2PNatPairMass_one_two_div_pascal_three,
    geom2PNatPairMass_two_one_div_pascal_three]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

private theorem taoSection7PairFiberCharacterMass_summable
    (n : ℕ) (xi x : ZMod (3 ^ n)) (b : ℕ) :
    Summable fun a : ℕ+ × ℕ+ =>
      if (a.1 : ℕ) + (a.2 : ℕ) = b then
        ((taoSection7Geom2PairPMF a).toReal : ℂ) *
          taoSection7PairPhase n xi x a.2
      else
        0 := by
  refine Summable.of_norm_bounded
    (pmf_summable_toReal taoSection7Geom2PairPMF) ?_
  intro a
  by_cases hsum : (a.1 : ℕ) + (a.2 : ℕ) = b
  · have hphase : ‖taoSection7PairPhase n xi x a.2‖ = 1 := by
      unfold taoSection7PairPhase
      exact norm_taoForwardDFTKernel_eq_one _ _
    simp only [hsum, if_true, norm_mul, Complex.norm_real, hphase, mul_one]
    simp [abs_of_nonneg ENNReal.toReal_nonneg]
  · simp [hsum, ENNReal.toReal_nonneg]

theorem norm_taoSection7PairFiberCharacterMass_le_sourceMass
    (n : ℕ) (xi x : ZMod (3 ^ n)) (b : ℕ) :
    ‖taoSection7PairFiberCharacterMass n xi x b‖ ≤
      (taoSection7PascalSourcePMF b).toReal := by
  rw [taoSection7PairFiberCharacterMass]
  calc
    ‖∑' a : ℕ+ × ℕ+,
        if (a.1 : ℕ) + (a.2 : ℕ) = b then
          ((taoSection7Geom2PairPMF a).toReal : ℂ) *
            taoSection7PairPhase n xi x a.2
        else 0‖ ≤
        ∑' a : ℕ+ × ℕ+,
          ‖if (a.1 : ℕ) + (a.2 : ℕ) = b then
            ((taoSection7Geom2PairPMF a).toReal : ℂ) *
              taoSection7PairPhase n xi x a.2
          else 0‖ :=
      norm_tsum_le_tsum_norm
        (taoSection7PairFiberCharacterMass_summable n xi x b).norm
    _ = ∑' a : ℕ+ × ℕ+,
          if b = (a.1 : ℕ) + (a.2 : ℕ) then
            (taoSection7Geom2PairPMF a).toReal
          else 0 := by
      apply tsum_congr
      intro a
      by_cases hsum : (a.1 : ℕ) + (a.2 : ℕ) = b
      · have hphase : ‖taoSection7PairPhase n xi x a.2‖ = 1 := by
          unfold taoSection7PairPhase
          exact norm_taoForwardDFTKernel_eq_one _ _
        simp [hsum, hphase]
      · have hsum' : ¬b = (a.1 : ℕ) + (a.2 : ℕ) := by omega
        simp [hsum, hsum']
    _ = (taoSection7PascalSourcePMF b).toReal := by
      rw [← taoSection7Geom2PairPMF_map_sum_eq_pascalSourcePMF]
      exact (pmf_map_apply_toReal_tsum taoSection7Geom2PairPMF
        (fun a => (a.1 : ℕ) + (a.2 : ℕ)) b).symm

theorem norm_taoSection7PairFiberCharacterMass_le_sourceFactor
    (n : ℕ) (xi : ZMod (3 ^ n)) (j : ℕ+) (s b : ℕ) :
    ‖taoSection7PairFiberCharacterMass n xi
        (taoSection7PairX n j (Int.ofNat (s + b))) b‖ ≤
      (taoSection7PascalSourcePMF b).toReal *
        taoSection7SourceFThreeFactor n xi (j : ℕ) s b := by
  by_cases hb : b = 3
  · subst b
    rw [taoSection7PairFiberCharacterMass_three_eq]
    have hcond : (3 : ℕ) = 3 ∧ 0 < (j : ℕ) := ⟨rfl, j.2⟩
    rw [taoSection7SourceFThreeFactor, dif_pos hcond]
    rw [norm_mul, Complex.norm_real]
    have hj : (⟨(j : ℕ), hcond.2⟩ : ℕ+) = j := Subtype.ext rfl
    rw [hj]
    simp
  · rw [taoSection7SourceFThreeFactor, dif_neg (by tauto)]
    simpa using norm_taoSection7PairFiberCharacterMass_le_sourceMass n xi
      (taoSection7PairX n j (Int.ofNat (s + b))) b

end Tao

end Erdos1135Predecessor
