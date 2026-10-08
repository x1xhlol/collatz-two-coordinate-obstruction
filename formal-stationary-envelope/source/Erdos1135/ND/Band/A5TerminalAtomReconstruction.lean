import Erdos1135.ND.Band.A5TerminalAtomNominalization
import Erdos1135.ND.Band.A5TwoProfileRawQ
import Erdos1135.ND.Fourier.FixedTotalReconstruction

/-!
# A5 Terminal-Atom Reconstruction

This leaf specializes the multiplicity-preserving fixed-total reconstruction
to one affine residue cell, transports it through the terminal `Sym` carrier,
and lands the harmonic and flat nominal terminal slices on the existing A5
profile factors.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Strict positive time subtraction identifies the original padded time
carrier with the physical `nu` carrier. -/
private noncomputable def ndA5PaddedBandWindowEquivPhysicalNuWindow
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n) :
    {n // n ∈ ndA5PaddedBandWindow B branch C j} ≃
      {nu // nu ∈ ndA5PhysicalNuWindow B branch C j} where
  toFun n :=
    ⟨n.1 - Tao.taoSection5M0 B,
      mem_ndA5PhysicalNuWindow_iff.mpr
        ⟨Nat.sub_pos_of_lt (htime n.1 n.2), by
          rw [Nat.sub_add_cancel (htime n.1 n.2).le]
          exact n.2⟩⟩
  invFun nu :=
    ⟨nu.1 + Tao.taoSection5M0 B,
      (mem_ndA5PhysicalNuWindow_iff.mp nu.2).2⟩
  left_inv n := by
    apply Subtype.ext
    exact Nat.sub_add_cancel (htime n.1 n.2).le
  right_inv nu := by
    apply Subtype.ext
    simp

/-- Sum form of the exact padded-time/physical-time equivalence.  The
summand is arbitrary and signed; no support or positivity is hidden here. -/
theorem sum_ndA5PaddedBandWindow_eq_physicalNuWindow
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n)
    (f : ℕ → ℝ) :
    (∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        f (n.1 - Tao.taoSection5M0 B)) =
      ∑ nu ∈ ndA5PhysicalNuWindow B branch C j, f nu := by
  classical
  calc
    _ = ∑ nu : {nu // nu ∈ ndA5PhysicalNuWindow B branch C j},
        f nu.1 := by
      apply Fintype.sum_equiv
        (ndA5PaddedBandWindowEquivPhysicalNuWindow htime)
      intro n
      rfl
    _ = _ := by
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach (ndA5PhysicalNuWindow B branch C j) f

/-- Under the all-window T2 packet, the natural physical endpoint belongs to
the terminal-total carrier exactly when its signed affine sweep lies in the
strict full tube. -/
private theorem ndA5PhysicalLevel_mem_terminalTotals_iff_mem_fullTube
    {B n : ℕ} {C A : ℝ} (ht2 : NDA5T2ScaleFacts B n C) :
    let q := n - Tao.taoSection5M0 B
    let W := ndA5TubeWidth B C
    ndA5PhysicalLevel A q ∈ ndA5TerminalTotals B C n ↔
      q ∈ ndA5FullTube A W := by
  dsimp only
  let q := n - Tao.taoSection5M0 B
  let W := ndA5TubeWidth B C
  constructor
  · intro hlevelMem
    have hterminal := mem_ndA5TerminalTotals_iff.mp hlevelMem
    have hlevelPos : 0 < ndA5PhysicalLevel A q :=
      ht2.nu_pos.trans_le hterminal.1
    have hlevelIntPos : 0 < ndA5PhysicalLevelInt A q := by
      unfold ndA5PhysicalLevel at hlevelPos
      omega
    have hlevelCast :
        (ndA5PhysicalLevel A q : ℤ) = ndA5PhysicalLevelInt A q := by
      unfold ndA5PhysicalLevel
      exact Int.toNat_of_nonneg hlevelIntPos.le
    have hlevelCastReal :=
      congrArg (fun z : ℤ => (z : ℝ)) hlevelCast
    have hbridgeReal := congrArg (fun z : ℤ => (z : ℝ))
      (ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep A q)
    push_cast at hlevelCastReal hbridgeReal
    have htube : |(ndA5StrictAffineSweep A q : ℝ)| < W := by
      rw [← hbridgeReal, ← hlevelCastReal]
      exact hterminal.2.2
    have hWpos : 0 < W := (abs_nonneg _).trans_lt htube
    exact (mem_ndA5FullTube_iff hWpos A q).mpr htube
  · intro htubeMem
    have htube : |(ndA5StrictAffineSweep A q : ℝ)| < W :=
      (Finset.mem_filter.mp htubeMem).2
    have hlevel := ndA5PhysicalLevelFacts_of_mem_fullTube
      ht2.nu_pos ht2.width_le_nu_div_eight htubeMem
    apply mem_ndA5TerminalTotals_iff.mpr
    refine ⟨hlevel.nu_le_nat, hlevel.nat_le_three_mul, ?_⟩
    have hlevelCastReal :=
      congrArg (fun z : ℤ => (z : ℝ)) hlevel.nat_cast_eq
    have hbridgeReal := congrArg (fun z : ℤ => (z : ℝ))
      (ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep A q)
    push_cast at hlevelCastReal hbridgeReal
    rw [hlevelCastReal, hbridgeReal]
    exact htube

/-- A T2-guarded terminal-total sum with strict nominal support is exactly
the zero-extended pair of physical cells. The endpoint mass is absorbed into
raw `q`; `f` is an arbitrary residual summand. -/
theorem sum_ndA5TerminalTotals_endpointMass_strict_eq_range_two
    {B n : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C A : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht2 : NDA5T2ScaleFacts B n C)
    (f : ℕ → ℝ) :
    let q := n - Tao.taoSection5M0 B
    let W := ndA5TubeWidth B C
    let beta := ndA5BandBeta B branch
    (∑ L : {L // L ∈ ndA5TerminalTotals B C n},
        ndGeom2EndpointMass q L.1 *
          (@ite ℝ
            (ndA5NominalStrictBandLevel beta A q (L.1 : ℤ))
            (Classical.propDecidable _) (f L.1) 0)) =
      ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandRawQTerm B branch A W q r *
          f (ndA5PhysicalLevel (A + (r : ℝ)) q) := by
  classical
  dsimp only
  let q := n - Tao.taoSection5M0 B
  let W := ndA5TubeWidth B C
  let beta := ndA5BandBeta B branch
  let level (r : ℕ) := ndA5PhysicalLevel (A + (r : ℝ)) q
  let SL := (ndA5TerminalTotals B C n).filter fun (L : ℕ) =>
    ndA5NominalStrictBandLevel beta A q (L : ℤ)
  let SR := (Finset.range 2).filter fun (r : ℕ) =>
    q ∈ ndA5FullTube (A + (r : ℝ)) W ∧
      ndA5NominalStrictBandLevel beta A q
        (ndA5PhysicalLevelInt (A + (r : ℝ)) q)
  have hleft :
      (∑ L : {L // L ∈ ndA5TerminalTotals B C n},
          ndGeom2EndpointMass q L.1 *
            (@ite ℝ
              (ndA5NominalStrictBandLevel beta A q (L.1 : ℤ))
              (Classical.propDecidable _) (f L.1) 0)) =
        ∑ L ∈ SL,
          ndGeom2EndpointMass q L * f L := by
    calc
      _ = ∑ L ∈ ndA5TerminalTotals B C n,
          ndGeom2EndpointMass q L *
            (@ite ℝ (ndA5NominalStrictBandLevel beta A q (L : ℤ))
              (Classical.propDecidable _) (f L) 0) := by
        rw [← Finset.attach_eq_univ]
        exact Finset.sum_attach (ndA5TerminalTotals B C n)
          (fun L => ndGeom2EndpointMass q L *
            (@ite ℝ (ndA5NominalStrictBandLevel beta A q (L : ℤ))
              (Classical.propDecidable _) (f L) 0))
      _ = _ := by
        symm
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro L _hL
        by_cases hstrict : ndA5NominalStrictBandLevel beta A q (L : ℤ)
        · simp [hstrict]
        · simp [hstrict]
  have hright :
      (∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandRawQTerm B branch A W q r *
            f (level r)) =
        ∑ r ∈ SR,
          ndGeom2EndpointMass q (level r) * f (level r) := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases htube : q ∈ ndA5FullTube (A + (r : ℝ)) W
    · by_cases hstrict : ndA5NominalStrictBandLevel beta A q
          (ndA5PhysicalLevelInt (A + (r : ℝ)) q)
      · simp [htube, hstrict, ndA5NominalStrictBandRawQTerm,
          ndA5RawQ, level, beta]
      · simp [htube, hstrict, ndA5NominalStrictBandRawQTerm, beta]
    · simp [htube, ndA5NominalStrictBandRawQTerm, ndA5RawQ, beta]
  have hpair :
      (∑ r ∈ SR,
          ndGeom2EndpointMass q (level r) * f (level r)) =
        ∑ L ∈ SL,
          ndGeom2EndpointMass q L * f L := by
    apply Finset.sum_bij (fun r _hr => level r)
    · intro r hr
      rcases Finset.mem_filter.mp hr with ⟨_hrange, htube, hstrict⟩
      have hlevel := ndA5PhysicalLevelFacts_of_mem_fullTube
        ht2.nu_pos ht2.width_le_nu_div_eight htube
      apply Finset.mem_filter.mpr
      constructor
      · have hmem :=
          (ndA5PhysicalLevel_mem_terminalTotals_iff_mem_fullTube
            (A := A + (r : ℝ)) ht2).mpr htube
        simpa [q, W, level] using hmem
      · have hcast : (level r : ℤ) =
            ndA5PhysicalLevelInt (A + (r : ℝ)) q := by
          simpa [q, level] using hlevel.nat_cast_eq
        rw [hcast]
        exact hstrict
    · intro r₁ hr₁ r₂ hr₂ heq
      have htube₁ := (Finset.mem_filter.mp hr₁).2.1
      have htube₂ := (Finset.mem_filter.mp hr₂).2.1
      have hlevel₁ := ndA5PhysicalLevelFacts_of_mem_fullTube
        ht2.nu_pos ht2.width_le_nu_div_eight htube₁
      have hlevel₂ := ndA5PhysicalLevelFacts_of_mem_fullTube
        ht2.nu_pos ht2.width_le_nu_div_eight htube₂
      have heqInt :
          ndA5PhysicalLevelInt (A + (r₁ : ℝ)) q =
            ndA5PhysicalLevelInt (A + (r₂ : ℝ)) q := by
        rw [← hlevel₁.nat_cast_eq, ← hlevel₂.nat_cast_eq]
        exact_mod_cast heq
      rw [ndA5PhysicalLevelInt_add_nat,
        ndA5PhysicalLevelInt_add_nat] at heqInt
      omega
    · intro L hL
      rcases Finset.mem_filter.mp hL with ⟨hterminal, hstrict⟩
      rcases (ndA5NominalStrictBandLevel_iff_base_or_firstShift
          (nu := q) (A := A) hB hlogB).mp hstrict with hbase | hshift
      · have hlevelEq : level 0 = L := by
          dsimp [level]
          simp only [Nat.cast_zero, add_zero]
          unfold ndA5PhysicalLevel
          rw [← hbase]
          simp
        have htube : q ∈ ndA5FullTube A W := by
          have hmem : ndA5PhysicalLevel A q ∈
              ndA5TerminalTotals B C n := by
            have hlevelEq' : ndA5PhysicalLevel A q = L := by
              simpa [level] using hlevelEq
            rw [hlevelEq']
            exact hterminal
          exact (ndA5PhysicalLevel_mem_terminalTotals_iff_mem_fullTube
            (A := A) ht2).mp hmem
        have hstrictBase : ndA5NominalStrictBandLevel beta A q
            (ndA5PhysicalLevelInt A q) := by
          rw [← hbase]
          exact hstrict
        refine ⟨0, Finset.mem_filter.mpr ?_, hlevelEq⟩
        simpa using (show 0 ∈ Finset.range 2 ∧
            q ∈ ndA5FullTube A W ∧
              ndA5NominalStrictBandLevel beta A q
                (ndA5PhysicalLevelInt A q) from
          ⟨by simp, htube, hstrictBase⟩)
      · have htranslate := ndA5PhysicalLevelInt_add_nat A q 1
        norm_num at htranslate
        have hsigned : (L : ℤ) = ndA5PhysicalLevelInt (A + 1) q := by
          omega
        have hlevelEq : level 1 = L := by
          dsimp [level]
          norm_num
          unfold ndA5PhysicalLevel
          rw [← hsigned]
          simp
        have htube : q ∈ ndA5FullTube (A + 1) W := by
          have hmem : ndA5PhysicalLevel (A + 1) q ∈
              ndA5TerminalTotals B C n := by
            have hlevelEq' : ndA5PhysicalLevel (A + 1) q = L := by
              simpa [level] using hlevelEq
            rw [hlevelEq']
            exact hterminal
          exact (ndA5PhysicalLevel_mem_terminalTotals_iff_mem_fullTube
            (A := A + 1) ht2).mp hmem
        have hstrictShift : ndA5NominalStrictBandLevel beta A q
            (ndA5PhysicalLevelInt (A + 1) q) := by
          rw [← hsigned]
          exact hstrict
        refine ⟨1, Finset.mem_filter.mpr ?_, hlevelEq⟩
        simpa using (show 1 ∈ Finset.range 2 ∧
            q ∈ ndA5FullTube (A + 1) W ∧
              ndA5NominalStrictBandLevel beta A q
                (ndA5PhysicalLevelInt (A + 1) q) from
          ⟨by simp, htube, hstrictShift⟩)
    · intro r _hr
      rfl
  calc
    _ = ∑ L ∈ SL,
        ndGeom2EndpointMass q L * f L := hleft
    _ = ∑ r ∈ SR,
        ndGeom2EndpointMass q (level r) * f (level r) := hpair.symm
    _ = _ := hright.symm

/-- On a T2-supported physical cell, the nominal affine position is exactly
the exponential coordinate stored by the named flat raw profile. -/
private theorem ndA5NominalAffinePosition_physicalLevel_eq_profileExponent
    {B n r : ℕ} {C z M : ℝ}
    (ht2 : NDA5T2ScaleFacts B n C)
    (htube :
      let q := n - Tao.taoSection5M0 B
      let A := ndA5PhysicalPhase z M
      let W := ndA5TubeWidth B C
      q ∈ ndA5FullTube (A + (r : ℝ)) W) :
    let q := n - Tao.taoSection5M0 B
    let A := ndA5PhysicalPhase z M
    ndA5NominalAffinePosition z M q
        (ndA5PhysicalLevel (A + (r : ℝ)) q) =
      ((((r + 1 : ℕ) : ℝ) -
          Int.fract (A + (q : ℝ) * logTwoThree)) * Real.log 2) := by
  dsimp only at htube ⊢
  let q := n - Tao.taoSection5M0 B
  let A := ndA5PhysicalPhase z M
  have hlevel := ndA5PhysicalLevelFacts_of_mem_fullTube
    ht2.nu_pos ht2.width_le_nu_div_eight htube
  have hlevelCastReal :=
    congrArg (fun v : ℤ => (v : ℝ)) hlevel.nat_cast_eq
  push_cast at hlevelCastReal
  have htranslate := ndA5PhysicalLevelInt_add_nat A q r
  unfold ndA5NominalAffinePosition
  rw [hlevelCastReal, htranslate]
  unfold ndA5PhysicalLevelInt Int.fract
  push_cast
  ring

/-- The fiber-free harmonic terminal-total sum lands on the two strict raw
cells.  The endpoint mass is already contained in each raw `q` term. -/
theorem sum_ndA5TerminalTotals_harmonicStrict_eq_range_two
    {B n : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C A : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht2 : NDA5T2ScaleFacts B n C) :
    let q := n - Tao.taoSection5M0 B
    let W := ndA5TubeWidth B C
    let beta := ndA5BandBeta B branch
    (∑ L : {L // L ∈ ndA5TerminalTotals B C n},
        ndGeom2EndpointMass q L.1 *
          (@ite ℝ
            (ndA5NominalStrictBandLevel beta A q (L.1 : ℤ))
            (Classical.propDecidable _) 1 0)) =
      ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandRawQTerm B branch A W q r := by
  simpa using
    (sum_ndA5TerminalTotals_endpointMass_strict_eq_range_two
      (branch := branch) (A := A) hB hlogB ht2 (fun _ => (1 : ℝ)))

/-- The fiber-free flat terminal-total sum lands on the two strict
exponential raw cells, with the exponential attached exactly once. -/
theorem sum_ndA5TerminalTotals_flatStrict_eq_range_two
    {B n : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C z M : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht2 : NDA5T2ScaleFacts B n C) :
    let q := n - Tao.taoSection5M0 B
    let A := ndA5PhysicalPhase z M
    let W := ndA5TubeWidth B C
    let beta := ndA5BandBeta B branch
    (∑ L : {L // L ∈ ndA5TerminalTotals B C n},
        ndGeom2EndpointMass q L.1 *
          (@ite ℝ
            (ndA5NominalStrictBandLevel beta A q (L.1 : ℤ))
            (Classical.propDecidable _)
            (Real.exp (ndA5NominalAffinePosition z M q L.1)) 0)) =
      ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandFlatRawQTerm B branch A W q r := by
  classical
  dsimp only
  let q := n - Tao.taoSection5M0 B
  let A := ndA5PhysicalPhase z M
  let W := ndA5TubeWidth B C
  let beta := ndA5BandBeta B branch
  let position (L : ℕ) := ndA5NominalAffinePosition z M q L
  calc
    _ = ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandRawQTerm B branch A W q r *
          Real.exp
            (position (ndA5PhysicalLevel (A + (r : ℝ)) q)) := by
      simpa [q, A, W, beta, position] using
        (sum_ndA5TerminalTotals_endpointMass_strict_eq_range_two
          (branch := branch) (A := A) hB hlogB ht2
          (fun L => Real.exp (position L)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases htube : q ∈ ndA5FullTube (A + (r : ℝ)) W
      · have hposition :=
          ndA5NominalAffinePosition_physicalLevel_eq_profileExponent
            (B := B) (n := n) (r := r) (C := C)
            (z := z) (M := M) ht2 (by simpa [q, A, W] using htube)
        dsimp [q, A, W, beta, position] at hposition ⊢
        rw [hposition]
        simp only [ndA5NominalStrictBandFlatRawQTerm]
      · dsimp [q, A, W, beta, position] at htube ⊢
        simp [ndA5NominalStrictBandFlatRawQTerm,
          ndA5NominalStrictBandRawQTerm, ndA5RawQ, htube]

/-- The custom finite instance on terminal atoms is intentionally opaque.
This local adapter exposes its literal two sigma indices and product without
changing the carrier or identifying equal affine residues. -/
private theorem sum_ndA5TerminalAtomIndex_eq_nested
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (f : NDA5TerminalAtomIndex B branch C j E → ℝ) :
    (∑ i : NDA5TerminalAtomIndex B branch C j E, f i) =
      ∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
          ∑ u : Sym (Fin (n.1 - Tao.taoSection5M0 B))
              (L.1 - (n.1 - Tao.taoSection5M0 B)),
            ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
              f ⟨n, ⟨L, (u, M)⟩⟩ := by
  classical
  let S : Finset (NDA5TerminalAtomIndex B branch C j E) :=
    (Finset.univ :
        Finset {n // n ∈ ndA5PaddedBandWindow B branch C j}).sigma
      (fun n =>
        (Finset.univ :
            Finset {L // L ∈ ndA5TerminalTotals B C n.1}).sigma
          (fun L =>
            (Finset.univ :
                Finset (Sym (Fin (n.1 - Tao.taoSection5M0 B))
                  (L.1 - (n.1 - Tao.taoSection5M0 B)))) ×ˢ
              (Finset.univ :
                Finset {M // M ∈ Tao.taoSection5EPrime B E})))
  have hS :
      (Finset.univ : Finset (NDA5TerminalAtomIndex B branch C j E)) = S := by
    ext i
    simp [S]
  change (Finset.univ.sum f) = _
  rw [hS]
  simp [S, Finset.sum_sigma, Finset.sum_product]

/-- The literal terminal-atom sum is the dependent fixed-cell sum with the
original `EPrime` endpoint before the collision-preserving `Sym` fiber.
Equal residues are not identified. -/
theorem sum_ndA5TerminalAtomIndex_eq_fixedCells
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (f : NDA5TerminalAtomIndex B branch C j E → ℝ) :
    (∑ i : NDA5TerminalAtomIndex B branch C j E, f i) =
      ∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
          ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
            ∑ u : Sym (Fin (n.1 - Tao.taoSection5M0 B))
                (L.1 - (n.1 - Tao.taoSection5M0 B)),
              f ⟨n, ⟨L, (u, M)⟩⟩ := by
  classical
  rw [sum_ndA5TerminalAtomIndex_eq_nested]
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro L _hL
  exact Finset.sum_comm

/-- A fixed affine residue cell reconstructs as exactly one endpoint mass
times the corresponding normalized Section-7 fiber atom. -/
theorem ndFixedTotalAffineResidueCell_eq_endpoint_mul_fiberAtom
    {q L M : ℕ} (hq : 0 < q) (hqL : q ≤ L) (kappa : ℝ) :
    (∑' a : NDFixedTotalValuations q L,
        Tao.geom2PNatListMass a.1 *
          (if (M : ZMod (3 ^ q)) =
              Tao.taoAffineOffsetZMod q a.1 then kappa else 0)) =
      ndGeom2EndpointMass q L *
        ((ndSection7FiberPMF q L hq hqL
          (M : ZMod (3 ^ q))).toReal * kappa) := by
  calc
    _ = ndGeom2EndpointMass q L *
        Tao.pmfExpectation (ndSection7FiberPMF q L hq hqL)
          (fun y => if (M : ZMod (3 ^ q)) = y then kappa else 0) :=
      ndFixedTotalAffineExpectation_eq_endpoint_mul_fiberExpectation
        hq hqL _
    _ = ndGeom2EndpointMass q L *
        ((ndSection7FiberPMF q L hq hqL
          (M : ZMod (3 ^ q))).toReal * kappa) := by
      congr 1
      unfold Tao.pmfExpectation
      rw [Finset.sum_eq_single_of_mem
        (M : ZMod (3 ^ q)) (Finset.mem_univ _)]
      · simp
      · intro y _hy hyM
        simp [Ne.symm hyM]

/-- The residue-cell identity on the literal `Sym` carrier stored in an A5
terminal index. The equivalence retains every tuple and hence every residue
collision. -/
theorem ndFixedTotalSymAffineResidueCell_eq_endpoint_mul_fiberAtom
    {q L M : ℕ} (hq : 0 < q) (hqL : q ≤ L) (kappa : ℝ) :
    (∑ u : Sym (Fin q) (L - q),
        Tao.geom2PNatListMass
            ((ndFiberExtrasEquivFixedTotal q L hqL u).1) *
          (if (M : ZMod (3 ^ q)) =
              Tao.taoAffineOffsetZMod q
                ((ndFiberExtrasEquivFixedTotal q L hqL u).1)
            then kappa else 0)) =
      ndGeom2EndpointMass q L *
        ((ndSection7FiberPMF q L hq hqL
          (M : ZMod (3 ^ q))).toReal * kappa) := by
  calc
    _ = ∑' u : Sym (Fin q) (L - q),
        Tao.geom2PNatListMass
            ((ndFiberExtrasEquivFixedTotal q L hqL u).1) *
          (if (M : ZMod (3 ^ q)) =
              Tao.taoAffineOffsetZMod q
                ((ndFiberExtrasEquivFixedTotal q L hqL u).1)
            then kappa else 0) := by
      rw [tsum_fintype]
    _ = ∑' a : NDFixedTotalValuations q L,
        Tao.geom2PNatListMass a.1 *
          (if (M : ZMod (3 ^ q)) =
              Tao.taoAffineOffsetZMod q a.1 then kappa else 0) := by
      exact (ndFiberExtrasEquivFixedTotal q L hqL).tsum_eq
        (fun a : NDFixedTotalValuations q L =>
          Tao.geom2PNatListMass a.1 *
            (if (M : ZMod (3 ^ q)) =
                Tao.taoAffineOffsetZMod q a.1 then kappa else 0))
    _ = _ := ndFixedTotalAffineResidueCell_eq_endpoint_mul_fiberAtom
      hq hqL kappa

/-- One fixed `(n,L,M)` harmonic terminal slice is an endpoint-weighted
fiber atom with the exact `3^q/(M*H)` profile coefficient. -/
theorem sum_ndA5HarmonicTerminalAtomNominalIdealMass_fixedFiber_eq
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j})
    (L : {L // L ∈ ndA5TerminalTotals B C n.1})
    (M : {M // M ∈ Tao.taoSection5EPrime B E})
    (hq : 0 < n.1 - Tao.taoSection5M0 B) :
    let q := n.1 - Tao.taoSection5M0 B
    let z := ndA5BandLower B branch j
    let beta := ndA5BandBeta B branch
    let H := Tao.logFinsetMass (ndA5OddBand B branch j)
    (∑ u : Sym (Fin q) (L.1 - q),
        ndA5HarmonicTerminalAtomNominalIdealMass
          (⟨n, ⟨L, (u, M)⟩⟩ :
            NDA5TerminalAtomIndex B branch C j E)) =
      ndGeom2EndpointMass q L.1 *
        ((ndSection7FiberPMFTotal q L.1
          (M.1 : ZMod (3 ^ q))).toReal *
          ((3 : ℝ) ^ q / ((M.1 : ℝ) * H) *
            @ite ℝ
              (ndA5NominalStrictBandLevel beta
                (ndA5PhysicalPhase z M.1) q (L.1 : ℤ))
              (Classical.propDecidable _) 1 0)) := by
  classical
  dsimp only
  let q := n.1 - Tao.taoSection5M0 B
  let hqL : q ≤ L.1 :=
    (mem_ndA5TerminalTotals_iff.mp L.2).1
  let z := ndA5BandLower B branch j
  let beta := ndA5BandBeta B branch
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  let kappa : ℝ :=
    (3 : ℝ) ^ q / ((M.1 : ℝ) * H) *
      @ite ℝ
        (ndA5NominalStrictBandLevel beta
          (ndA5PhysicalPhase z M.1) q (L.1 : ℤ))
        (Classical.propDecidable _) 1 0
  calc
    (∑ u : Sym (Fin q) (L.1 - q),
        ndA5HarmonicTerminalAtomNominalIdealMass
          (⟨n, ⟨L, (u, M)⟩⟩ :
            NDA5TerminalAtomIndex B branch C j E)) =
        ∑ u : Sym (Fin q) (L.1 - q),
          Tao.geom2PNatListMass
              ((ndFiberExtrasEquivFixedTotal q L.1 hqL u).1) *
            (if (M.1 : ZMod (3 ^ q)) =
                Tao.taoAffineOffsetZMod q
                  ((ndFiberExtrasEquivFixedTotal q L.1 hqL u).1)
              then kappa else 0) := by
      apply Finset.sum_congr rfl
      intro u _hu
      have hval :
          ndA5TerminalAtomValuations
              (⟨n, ⟨L, (u, M)⟩⟩ :
                NDA5TerminalAtomIndex B branch C j E) =
            (ndFiberExtrasEquivFixedTotal q L.1 hqL u).1 := by
        rfl
      unfold ndA5HarmonicTerminalAtomNominalIdealMass
      unfold ndA5TerminalAtomNominalSupported
      unfold ndA5HarmonicTerminalAtomMWeight
      unfold ndA5TerminalAtomCompatible
      simp only [hval]
      change (if
          (M.1 : ZMod (3 ^ q)) =
              Tao.taoAffineOffsetZMod q
                ((ndFiberExtrasEquivFixedTotal q L.1 hqL u).1) ∧
            ndA5NominalStrictBandLevel beta
              (ndA5PhysicalPhase z M.1) q (L.1 : ℤ)
        then
          (((3 : ℝ) ^ q *
              Tao.geom2PNatListMass
                ((ndFiberExtrasEquivFixedTotal q L.1 hqL u).1)) /
            (M.1 : ℝ)) / H
        else 0) = _
      by_cases hcompat : (M.1 : ZMod (3 ^ q)) =
          Tao.taoAffineOffsetZMod q
            ((ndFiberExtrasEquivFixedTotal q L.1 hqL u).1)
      · by_cases hstrict : ndA5NominalStrictBandLevel beta
            (ndA5PhysicalPhase z M.1) q (L.1 : ℤ)
        · simp [hcompat, hstrict, kappa]
          ring
        · simp [hcompat, hstrict, kappa]
      · simp [hcompat, kappa]
    _ = ndGeom2EndpointMass q L.1 *
        ((ndSection7FiberPMF q L.1 hq hqL
          (M.1 : ZMod (3 ^ q))).toReal * kappa) :=
      ndFixedTotalSymAffineResidueCell_eq_endpoint_mul_fiberAtom
        hq hqL kappa
    _ = _ := by
      rw [ndSection7FiberPMFTotal_eq_of_pos_of_le hq hqL]

/-- One fixed `(n,L,M)` flat terminal slice is an endpoint-weighted fiber
atom with the exponential retained exactly once and residual coefficient
`z*3^q/(M*card)`. -/
theorem sum_ndA5FlatTerminalAtomNominalIdealMass_fixedFiber_eq
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j})
    (L : {L // L ∈ ndA5TerminalTotals B C n.1})
    (M : {M // M ∈ Tao.taoSection5EPrime B E})
    (hq : 0 < n.1 - Tao.taoSection5M0 B) :
    let q := n.1 - Tao.taoSection5M0 B
    let z := ndA5BandLower B branch j
    let beta := ndA5BandBeta B branch
    let card := ((ndA5OddBand B branch j).card : ℝ)
    let uNominal := ndA5NominalAffinePosition z M.1 q L.1
    (∑ u : Sym (Fin q) (L.1 - q),
        ndA5FlatTerminalAtomNominalIdealMass
          (⟨n, ⟨L, (u, M)⟩⟩ :
            NDA5TerminalAtomIndex B branch C j E)) =
      ndGeom2EndpointMass q L.1 *
        ((ndSection7FiberPMFTotal q L.1
          (M.1 : ZMod (3 ^ q))).toReal *
          (((z * (3 : ℝ) ^ q) / ((M.1 : ℝ) * card)) *
            @ite ℝ
              (ndA5NominalStrictBandLevel beta
                (ndA5PhysicalPhase z M.1) q (L.1 : ℤ))
              (Classical.propDecidable _) (Real.exp uNominal) 0)) := by
  classical
  dsimp only
  let q := n.1 - Tao.taoSection5M0 B
  let hqL : q ≤ L.1 :=
    (mem_ndA5TerminalTotals_iff.mp L.2).1
  let z := ndA5BandLower B branch j
  let beta := ndA5BandBeta B branch
  let card := ((ndA5OddBand B branch j).card : ℝ)
  let uNominal := ndA5NominalAffinePosition z M.1 q L.1
  let kappa : ℝ :=
    ((z * (3 : ℝ) ^ q) / ((M.1 : ℝ) * card)) *
      @ite ℝ
        (ndA5NominalStrictBandLevel beta
          (ndA5PhysicalPhase z M.1) q (L.1 : ℤ))
        (Classical.propDecidable _) (Real.exp uNominal) 0
  calc
    (∑ u : Sym (Fin q) (L.1 - q),
        ndA5FlatTerminalAtomNominalIdealMass
          (⟨n, ⟨L, (u, M)⟩⟩ :
            NDA5TerminalAtomIndex B branch C j E)) =
        ∑ u : Sym (Fin q) (L.1 - q),
          Tao.geom2PNatListMass
              ((ndFiberExtrasEquivFixedTotal q L.1 hqL u).1) *
            (if (M.1 : ZMod (3 ^ q)) =
                Tao.taoAffineOffsetZMod q
                  ((ndFiberExtrasEquivFixedTotal q L.1 hqL u).1)
              then kappa else 0) := by
      apply Finset.sum_congr rfl
      intro u _hu
      have hval :
          ndA5TerminalAtomValuations
              (⟨n, ⟨L, (u, M)⟩⟩ :
                NDA5TerminalAtomIndex B branch C j E) =
            (ndFiberExtrasEquivFixedTotal q L.1 hqL u).1 := by
        rfl
      unfold ndA5FlatTerminalAtomNominalIdealMass
      unfold ndA5TerminalAtomNominalSupported
      unfold ndA5HarmonicTerminalAtomMWeight
      unfold ndA5TerminalAtomCompatible
      simp only [hval]
      change (if
          (M.1 : ZMod (3 ^ q)) =
              Tao.taoAffineOffsetZMod q
                ((ndFiberExtrasEquivFixedTotal q L.1 hqL u).1) ∧
            ndA5NominalStrictBandLevel beta
              (ndA5PhysicalPhase z M.1) q (L.1 : ℤ)
        then
          ((((3 : ℝ) ^ q *
              Tao.geom2PNatListMass
                ((ndFiberExtrasEquivFixedTotal q L.1 hqL u).1)) /
            (M.1 : ℝ)) * (z * Real.exp uNominal)) / card
        else 0) = _
      by_cases hcompat : (M.1 : ZMod (3 ^ q)) =
          Tao.taoAffineOffsetZMod q
            ((ndFiberExtrasEquivFixedTotal q L.1 hqL u).1)
      · by_cases hstrict : ndA5NominalStrictBandLevel beta
            (ndA5PhysicalPhase z M.1) q (L.1 : ℤ)
        · simp [hcompat, hstrict, kappa]
          ring
        · simp [hcompat, hstrict, kappa]
      · simp [hcompat, kappa]
    _ = ndGeom2EndpointMass q L.1 *
        ((ndSection7FiberPMF q L.1 hq hqL
          (M.1 : ZMod (3 ^ q))).toReal * kappa) :=
      ndFixedTotalSymAffineResidueCell_eq_endpoint_mul_fiberAtom
        hq hqL kappa
    _ = _ := by
      rw [ndSection7FiberPMFTotal_eq_of_pos_of_le hq hqL]

/-- For one padded time and endpoint, the complete harmonic terminal slice
lands literally on the two named raw `q` cells, with the normalized fiber
atom retained as a multiplier. -/
theorem sum_ndA5HarmonicTerminalAtomNominalIdealMass_fixedEndpoint_eq_twoProfile
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j})
    (M : {M // M ∈ Tao.taoSection5EPrime B E})
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht2 : NDA5T2ScaleFacts B n.1 C) :
    let q := n.1 - Tao.taoSection5M0 B
    let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M.1
    let W := ndA5TubeWidth B C
    let H := Tao.logFinsetMass (ndA5OddBand B branch j)
    (∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
        ∑ u : Sym (Fin q) (L.1 - q),
          ndA5HarmonicTerminalAtomNominalIdealMass
            (⟨n, ⟨L, (u, M)⟩⟩ :
              NDA5TerminalAtomIndex B branch C j E)) =
      ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandRawQTerm B branch A W q r *
          ((ndSection7FiberPMFTotal q
            (ndA5PhysicalLevel (A + (r : ℝ)) q)
            (M.1 : ZMod (3 ^ q))).toReal *
            ((3 : ℝ) ^ q / ((M.1 : ℝ) * H))) := by
  classical
  dsimp only
  let q := n.1 - Tao.taoSection5M0 B
  let z := ndA5BandLower B branch j
  let A := ndA5PhysicalPhase z M.1
  let W := ndA5TubeWidth B C
  let beta := ndA5BandBeta B branch
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  let coeff : ℝ := (3 : ℝ) ^ q / ((M.1 : ℝ) * H)
  calc
    _ = ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
        ndGeom2EndpointMass q L.1 *
          ((ndSection7FiberPMFTotal q L.1
            (M.1 : ZMod (3 ^ q))).toReal *
            (coeff *
              @ite ℝ
                (ndA5NominalStrictBandLevel beta A q (L.1 : ℤ))
                (Classical.propDecidable _) 1 0)) := by
      apply Finset.sum_congr rfl
      intro L _hL
      simpa [q, z, A, beta, H, coeff] using
        (sum_ndA5HarmonicTerminalAtomNominalIdealMass_fixedFiber_eq
          n L M ht2.nu_pos)
    _ = ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
        ndGeom2EndpointMass q L.1 *
          (@ite ℝ
            (ndA5NominalStrictBandLevel beta A q (L.1 : ℤ))
            (Classical.propDecidable _)
            ((ndSection7FiberPMFTotal q L.1
              (M.1 : ZMod (3 ^ q))).toReal * coeff) 0) := by
      apply Finset.sum_congr rfl
      intro L _hL
      by_cases hstrict : ndA5NominalStrictBandLevel beta A q (L.1 : ℤ)
      · simp [hstrict]
      · simp [hstrict]
    _ = _ := by
      simpa [q, A, W, beta, H, coeff] using
        (sum_ndA5TerminalTotals_endpointMass_strict_eq_range_two
          (branch := branch) hB hlogB ht2
          (fun L =>
            (ndSection7FiberPMFTotal q L
              (M.1 : ZMod (3 ^ q))).toReal * coeff))

/-- For one padded time and endpoint, the complete flat terminal slice lands
on the named exponential raw cells. The exponential is attached exactly once
and the residual coefficient is `z*3^q/(M*card)`. -/
theorem sum_ndA5FlatTerminalAtomNominalIdealMass_fixedEndpoint_eq_twoProfile
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j})
    (M : {M // M ∈ Tao.taoSection5EPrime B E})
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht2 : NDA5T2ScaleFacts B n.1 C) :
    let q := n.1 - Tao.taoSection5M0 B
    let z := ndA5BandLower B branch j
    let A := ndA5PhysicalPhase z M.1
    let W := ndA5TubeWidth B C
    let card := ((ndA5OddBand B branch j).card : ℝ)
    (∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
        ∑ u : Sym (Fin q) (L.1 - q),
          ndA5FlatTerminalAtomNominalIdealMass
            (⟨n, ⟨L, (u, M)⟩⟩ :
              NDA5TerminalAtomIndex B branch C j E)) =
      ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandFlatRawQTerm B branch A W q r *
          ((ndSection7FiberPMFTotal q
            (ndA5PhysicalLevel (A + (r : ℝ)) q)
            (M.1 : ZMod (3 ^ q))).toReal *
            ((z * (3 : ℝ) ^ q) / ((M.1 : ℝ) * card))) := by
  classical
  dsimp only
  let q := n.1 - Tao.taoSection5M0 B
  let z := ndA5BandLower B branch j
  let A := ndA5PhysicalPhase z M.1
  let W := ndA5TubeWidth B C
  let beta := ndA5BandBeta B branch
  let card := ((ndA5OddBand B branch j).card : ℝ)
  let coeff : ℝ := (z * (3 : ℝ) ^ q) / ((M.1 : ℝ) * card)
  let position (L : ℕ) := ndA5NominalAffinePosition z M.1 q L
  calc
    _ = ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
        ndGeom2EndpointMass q L.1 *
          ((ndSection7FiberPMFTotal q L.1
            (M.1 : ZMod (3 ^ q))).toReal *
            (coeff *
              @ite ℝ
                (ndA5NominalStrictBandLevel beta A q (L.1 : ℤ))
                (Classical.propDecidable _) (Real.exp (position L.1)) 0)) := by
      apply Finset.sum_congr rfl
      intro L _hL
      simpa [q, z, A, beta, card, coeff, position] using
        (sum_ndA5FlatTerminalAtomNominalIdealMass_fixedFiber_eq
          n L M ht2.nu_pos)
    _ = ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
        ndGeom2EndpointMass q L.1 *
          (@ite ℝ
            (ndA5NominalStrictBandLevel beta A q (L.1 : ℤ))
            (Classical.propDecidable _)
            ((ndSection7FiberPMFTotal q L.1
              (M.1 : ZMod (3 ^ q))).toReal *
              (coeff * Real.exp (position L.1))) 0) := by
      apply Finset.sum_congr rfl
      intro L _hL
      by_cases hstrict : ndA5NominalStrictBandLevel beta A q (L.1 : ℤ)
      · simp [hstrict]
      · simp [hstrict]
    _ = ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandRawQTerm B branch A W q r *
          ((ndSection7FiberPMFTotal q
            (ndA5PhysicalLevel (A + (r : ℝ)) q)
            (M.1 : ZMod (3 ^ q))).toReal *
            (coeff * Real.exp
              (position (ndA5PhysicalLevel (A + (r : ℝ)) q)))) := by
      simpa [q, A, W, beta, coeff, position] using
        (sum_ndA5TerminalTotals_endpointMass_strict_eq_range_two
          (branch := branch) hB hlogB ht2
          (fun L =>
            (ndSection7FiberPMFTotal q L
              (M.1 : ZMod (3 ^ q))).toReal *
              (coeff * Real.exp (position L))))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases htube : q ∈ ndA5FullTube (A + (r : ℝ)) W
      · have hposition :=
          ndA5NominalAffinePosition_physicalLevel_eq_profileExponent
            (B := B) (n := n.1) (r := r) (C := C)
            (z := z) (M := M.1) ht2 (by simpa [q, A, W] using htube)
        dsimp [q, z, A, W, card, coeff, position] at hposition ⊢
        rw [hposition]
        simp only [ndA5NominalStrictBandFlatRawQTerm]
        ring
      · dsimp [q, z, A, W, card, coeff, position] at htube ⊢
        simp [ndA5NominalStrictBandFlatRawQTerm,
          ndA5NominalStrictBandRawQTerm, ndA5RawQ, htube]

/-- The literal harmonic terminal ideal sum, reindexed by endpoint, physical
time, and the two named strict raw cells. No interior-endpoint restriction is
used, and the conditioned fiber atom remains visible. -/
theorem sum_ndA5HarmonicTerminalAtomNominalIdealMass_eq_twoProfile
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    (∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomNominalIdealMass i) =
      ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
        ∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
          ∑ r ∈ Finset.range 2,
            let z := ndA5BandLower B branch j
            let A := ndA5PhysicalPhase z M.1
            let W := ndA5TubeWidth B C
            let H := Tao.logFinsetMass (ndA5OddBand B branch j)
            ndA5NominalStrictBandRawQTerm B branch A W nu r *
              ((ndSection7FiberPMFTotal nu
                (ndA5PhysicalLevel (A + (r : ℝ)) nu)
                (M.1 : ZMod (3 ^ nu))).toReal *
                ((3 : ℝ) ^ nu / ((M.1 : ℝ) * H))) := by
  classical
  have htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n := by
    intro n hn
    exact Nat.sub_pos_iff_lt.mp
      (ndA5PaddedBandWindow_t2_of_guards
        hB hlogB hpadding hj hn).nu_pos
  calc
    _ = ∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
          ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
            ∑ u : Sym (Fin (n.1 - Tao.taoSection5M0 B))
                (L.1 - (n.1 - Tao.taoSection5M0 B)),
              ndA5HarmonicTerminalAtomNominalIdealMass
                (⟨n, ⟨L, (u, M)⟩⟩ :
                  NDA5TerminalAtomIndex B branch C j E) := by
      rw [sum_ndA5TerminalAtomIndex_eq_nested]
      apply Finset.sum_congr rfl
      intro n _hn
      calc
        _ = ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
            ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
              ∑ u : Sym (Fin (n.1 - Tao.taoSection5M0 B))
                  (L.1 - (n.1 - Tao.taoSection5M0 B)),
                ndA5HarmonicTerminalAtomNominalIdealMass
                  (⟨n, ⟨L, (u, M)⟩⟩ :
                    NDA5TerminalAtomIndex B branch C j E) := by
          apply Finset.sum_congr rfl
          intro L _hL
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
          ∑ r ∈ Finset.range 2,
            let q := n.1 - Tao.taoSection5M0 B
            let z := ndA5BandLower B branch j
            let A := ndA5PhysicalPhase z M.1
            let W := ndA5TubeWidth B C
            let H := Tao.logFinsetMass (ndA5OddBand B branch j)
            ndA5NominalStrictBandRawQTerm B branch A W q r *
              ((ndSection7FiberPMFTotal q
                (ndA5PhysicalLevel (A + (r : ℝ)) q)
                (M.1 : ZMod (3 ^ q))).toReal *
                ((3 : ℝ) ^ q / ((M.1 : ℝ) * H))) := by
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro M _hM
      exact
        sum_ndA5HarmonicTerminalAtomNominalIdealMass_fixedEndpoint_eq_twoProfile
          n M hB hlogB
            (ndA5PaddedBandWindow_t2_of_guards
              hB hlogB hpadding hj n.2)
    _ = ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
        ∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
          ∑ r ∈ Finset.range 2,
            let q := n.1 - Tao.taoSection5M0 B
            let z := ndA5BandLower B branch j
            let A := ndA5PhysicalPhase z M.1
            let W := ndA5TubeWidth B C
            let H := Tao.logFinsetMass (ndA5OddBand B branch j)
            ndA5NominalStrictBandRawQTerm B branch A W q r *
              ((ndSection7FiberPMFTotal q
                (ndA5PhysicalLevel (A + (r : ℝ)) q)
                (M.1 : ZMod (3 ^ q))).toReal *
                ((3 : ℝ) ^ q / ((M.1 : ℝ) * H))) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro M _hM
      exact sum_ndA5PaddedBandWindow_eq_physicalNuWindow htime
        (fun nu =>
          ∑ r ∈ Finset.range 2,
            let z := ndA5BandLower B branch j
            let A := ndA5PhysicalPhase z M.1
            let W := ndA5TubeWidth B C
            let H := Tao.logFinsetMass (ndA5OddBand B branch j)
            ndA5NominalStrictBandRawQTerm B branch A W nu r *
              ((ndSection7FiberPMFTotal nu
                (ndA5PhysicalLevel (A + (r : ℝ)) nu)
                (M.1 : ZMod (3 ^ nu))).toReal *
                ((3 : ℝ) ^ nu / ((M.1 : ℝ) * H))))

/-- The literal flat terminal ideal sum on the same physical carrier and two
named strict cells. The named profile contains the unique exponential factor;
only `z*3^nu/(M*card)` remains outside it. -/
theorem sum_ndA5FlatTerminalAtomNominalIdealMass_eq_twoProfile
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    (∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5FlatTerminalAtomNominalIdealMass i) =
      ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
        ∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
          ∑ r ∈ Finset.range 2,
            let z := ndA5BandLower B branch j
            let A := ndA5PhysicalPhase z M.1
            let W := ndA5TubeWidth B C
            let card := ((ndA5OddBand B branch j).card : ℝ)
            ndA5NominalStrictBandFlatRawQTerm B branch A W nu r *
              ((ndSection7FiberPMFTotal nu
                (ndA5PhysicalLevel (A + (r : ℝ)) nu)
                (M.1 : ZMod (3 ^ nu))).toReal *
                ((z * (3 : ℝ) ^ nu) / ((M.1 : ℝ) * card))) := by
  classical
  have htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n := by
    intro n hn
    exact Nat.sub_pos_iff_lt.mp
      (ndA5PaddedBandWindow_t2_of_guards
        hB hlogB hpadding hj hn).nu_pos
  calc
    _ = ∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
          ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
            ∑ u : Sym (Fin (n.1 - Tao.taoSection5M0 B))
                (L.1 - (n.1 - Tao.taoSection5M0 B)),
              ndA5FlatTerminalAtomNominalIdealMass
                (⟨n, ⟨L, (u, M)⟩⟩ :
                  NDA5TerminalAtomIndex B branch C j E) := by
      rw [sum_ndA5TerminalAtomIndex_eq_nested]
      apply Finset.sum_congr rfl
      intro n _hn
      calc
        _ = ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
            ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
              ∑ u : Sym (Fin (n.1 - Tao.taoSection5M0 B))
                  (L.1 - (n.1 - Tao.taoSection5M0 B)),
                ndA5FlatTerminalAtomNominalIdealMass
                  (⟨n, ⟨L, (u, M)⟩⟩ :
                    NDA5TerminalAtomIndex B branch C j E) := by
          apply Finset.sum_congr rfl
          intro L _hL
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
          ∑ r ∈ Finset.range 2,
            let q := n.1 - Tao.taoSection5M0 B
            let z := ndA5BandLower B branch j
            let A := ndA5PhysicalPhase z M.1
            let W := ndA5TubeWidth B C
            let card := ((ndA5OddBand B branch j).card : ℝ)
            ndA5NominalStrictBandFlatRawQTerm B branch A W q r *
              ((ndSection7FiberPMFTotal q
                (ndA5PhysicalLevel (A + (r : ℝ)) q)
                (M.1 : ZMod (3 ^ q))).toReal *
                ((z * (3 : ℝ) ^ q) / ((M.1 : ℝ) * card))) := by
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro M _hM
      exact
        sum_ndA5FlatTerminalAtomNominalIdealMass_fixedEndpoint_eq_twoProfile
          n M hB hlogB
            (ndA5PaddedBandWindow_t2_of_guards
              hB hlogB hpadding hj n.2)
    _ = ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
        ∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
          ∑ r ∈ Finset.range 2,
            let q := n.1 - Tao.taoSection5M0 B
            let z := ndA5BandLower B branch j
            let A := ndA5PhysicalPhase z M.1
            let W := ndA5TubeWidth B C
            let card := ((ndA5OddBand B branch j).card : ℝ)
            ndA5NominalStrictBandFlatRawQTerm B branch A W q r *
              ((ndSection7FiberPMFTotal q
                (ndA5PhysicalLevel (A + (r : ℝ)) q)
                (M.1 : ZMod (3 ^ q))).toReal *
                ((z * (3 : ℝ) ^ q) / ((M.1 : ℝ) * card))) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro M _hM
      exact sum_ndA5PaddedBandWindow_eq_physicalNuWindow htime
        (fun nu =>
          ∑ r ∈ Finset.range 2,
            let z := ndA5BandLower B branch j
            let A := ndA5PhysicalPhase z M.1
            let W := ndA5TubeWidth B C
            let card := ((ndA5OddBand B branch j).card : ℝ)
            ndA5NominalStrictBandFlatRawQTerm B branch A W nu r *
              ((ndSection7FiberPMFTotal nu
                (ndA5PhysicalLevel (A + (r : ℝ)) nu)
                (M.1 : ZMod (3 ^ nu))).toReal *
                ((z * (3 : ℝ) ^ nu) / ((M.1 : ℝ) * card))))

/-- The exact harmonic nominal terminal sum, flattened only through its two
dependent sigma indices and the stored `Sym × EPrime` product. -/
theorem sum_ndA5HarmonicTerminalAtomNominalIdealMass_eq_nestedFiber
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n) :
    (∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomNominalIdealMass i) =
      ∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
          ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
            let q := n.1 - Tao.taoSection5M0 B
            let z := ndA5BandLower B branch j
            let beta := ndA5BandBeta B branch
            let H := Tao.logFinsetMass (ndA5OddBand B branch j)
            ndGeom2EndpointMass q L.1 *
              ((ndSection7FiberPMFTotal q L.1
                (M.1 : ZMod (3 ^ q))).toReal *
                ((3 : ℝ) ^ q / ((M.1 : ℝ) * H) *
                  @ite ℝ
                    (ndA5NominalStrictBandLevel beta
                      (ndA5PhysicalPhase z M.1) q (L.1 : ℤ))
                    (Classical.propDecidable _) 1 0)) := by
  classical
  rw [sum_ndA5TerminalAtomIndex_eq_nested]
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro L _hL
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _hM
  dsimp only
  exact sum_ndA5HarmonicTerminalAtomNominalIdealMass_fixedFiber_eq
    n L M (Nat.sub_pos_of_lt (htime n.1 n.2))

/-- The exact flat nominal terminal sum on the same literal carrier. The
exponential remains inside the cell factor and is not duplicated by a
`2^L / card` coefficient. -/
theorem sum_ndA5FlatTerminalAtomNominalIdealMass_eq_nestedFiber
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n) :
    (∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5FlatTerminalAtomNominalIdealMass i) =
      ∑ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
        ∑ L : {L // L ∈ ndA5TerminalTotals B C n.1},
          ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
            let q := n.1 - Tao.taoSection5M0 B
            let z := ndA5BandLower B branch j
            let beta := ndA5BandBeta B branch
            let card := ((ndA5OddBand B branch j).card : ℝ)
            let uNominal := ndA5NominalAffinePosition z M.1 q L.1
            ndGeom2EndpointMass q L.1 *
              ((ndSection7FiberPMFTotal q L.1
                (M.1 : ZMod (3 ^ q))).toReal *
                (((z * (3 : ℝ) ^ q) / ((M.1 : ℝ) * card)) *
                  @ite ℝ
                    (ndA5NominalStrictBandLevel beta
                      (ndA5PhysicalPhase z M.1) q (L.1 : ℤ))
                    (Classical.propDecidable _)
                    (Real.exp uNominal) 0)) := by
  classical
  rw [sum_ndA5TerminalAtomIndex_eq_nested]
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro L _hL
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _hM
  dsimp only
  exact sum_ndA5FlatTerminalAtomNominalIdealMass_fixedFiber_eq
    n L M (Nat.sub_pos_of_lt (htime n.1 n.2))

end

end ND
end Erdos1135
