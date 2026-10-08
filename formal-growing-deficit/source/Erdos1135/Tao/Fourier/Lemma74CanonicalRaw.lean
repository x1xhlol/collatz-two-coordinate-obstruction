import Erdos1135.Tao.Fourier.Lemma74SoutheastTransport
import Erdos1135.Tao.Fourier.Lemma74ClaimStarScalars

/-!
# Lemma 7.4 Canonical Raw Triangle

This leaf constructs the canonical bounded selectors and the raw triangle
attached to one source black point. It stops before ClaimStar, source
membership, TriangleSeed, coherence, and family assembly.
-/

namespace Erdos1135
namespace Tao

noncomputable section

noncomputable def taoSection7BoundedSet
    (P : ℕ → Prop) (lo hi : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc lo hi).filter P

theorem taoSection7BoundedLeast_nonempty
    (P : ℕ → Prop) (lo hi : ℕ)
    (hex : ∃ k, lo ≤ k ∧ k ≤ hi ∧ P k) :
    (taoSection7BoundedSet P lo hi).Nonempty := by
  classical
  rcases hex with ⟨k, hlo, hhi, hk⟩
  exact ⟨k, by simp [taoSection7BoundedSet, hlo, hhi, hk]⟩

noncomputable def taoSection7BoundedLeast
    (P : ℕ → Prop) (lo hi : ℕ)
    (hex : ∃ k, lo ≤ k ∧ k ≤ hi ∧ P k) : ℕ := by
  classical
  exact (taoSection7BoundedSet P lo hi).min'
    (taoSection7BoundedLeast_nonempty P lo hi hex)

theorem taoSection7BoundedLeast_spec
    (P : ℕ → Prop) (lo hi : ℕ)
    (hex : ∃ k, lo ≤ k ∧ k ≤ hi ∧ P k) :
    lo ≤ taoSection7BoundedLeast P lo hi hex ∧
      taoSection7BoundedLeast P lo hi hex ≤ hi ∧
      P (taoSection7BoundedLeast P lo hi hex) := by
  classical
  have hmem := Finset.min'_mem (taoSection7BoundedSet P lo hi)
    (taoSection7BoundedLeast_nonempty P lo hi hex)
  have hparts :
      taoSection7BoundedLeast P lo hi hex ∈ Finset.Icc lo hi ∧
        P (taoSection7BoundedLeast P lo hi hex) := by
    simpa [taoSection7BoundedSet, taoSection7BoundedLeast] using hmem
  have hinterval := Finset.mem_Icc.mp hparts.1
  exact ⟨hinterval.1, hinterval.2, hparts.2⟩

theorem taoSection7BoundedLeast_minimal
    (P : ℕ → Prop) (lo hi : ℕ)
    (hex : ∃ k, lo ≤ k ∧ k ≤ hi ∧ P k)
    {k : ℕ} (hlo : lo ≤ k)
    (hk : k < taoSection7BoundedLeast P lo hi hex) :
    ¬ P k := by
  classical
  intro hPk
  have htop := (taoSection7BoundedLeast_spec P lo hi hex).2.1
  have hmem : k ∈ taoSection7BoundedSet P lo hi := by
    simp [taoSection7BoundedSet, hlo, hk.le.trans htop, hPk]
  have hle := Finset.min'_le (taoSection7BoundedSet P lo hi) k hmem
  exact (not_le_of_gt hk) (by simpa [taoSection7BoundedLeast] using hle)

abbrev TaoSection7CanonicalBlackPoint
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) :=
  {p : TaoSection7Point //
    taoSection7SourceBlackInDomain n xi epsilon (n / 2) p}

theorem taoSection7CanonicalWhiteOffset_exists
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ 2 * n ∧
      taoSection7SourceWhitePoint n xi epsilon (p.1.upN t) := by
  have hn : 1 ≤ n := by
    have hjpos : 0 < (p.1.j : ℕ) := p.1.j.pos
    have hj : (p.1.j : ℕ) ≤ n / 2 := p.2.1
    omega
  exact exists_sourceWhitePoint_upN_le_two_mul
    hn hxi p.1 p.2.1 p.2.2 hscalar.epsilon_lt_one_hundredth

noncomputable def taoSection7CanonicalFirstWhiteOffset
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) : ℕ :=
  taoSection7BoundedLeast
    (fun t => taoSection7SourceWhitePoint n xi epsilon (p.1.upN t))
    1 (2 * n) (taoSection7CanonicalWhiteOffset_exists hxi hscalar p)

theorem taoSection7CanonicalFirstWhiteOffset_spec
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    1 ≤ taoSection7CanonicalFirstWhiteOffset hxi hscalar p ∧
      taoSection7CanonicalFirstWhiteOffset hxi hscalar p ≤ 2 * n ∧
      taoSection7SourceWhitePoint n xi epsilon
        (p.1.upN (taoSection7CanonicalFirstWhiteOffset hxi hscalar p)) := by
  exact taoSection7BoundedLeast_spec _ _ _
    (taoSection7CanonicalWhiteOffset_exists hxi hscalar p)

theorem taoSection7CanonicalFirstWhiteOffset_prefix_black
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon)
    {u : ℕ} (hu : u < taoSection7CanonicalFirstWhiteOffset hxi hscalar p) :
    taoSection7SourceBlackPoint n xi epsilon (p.1.upN u) := by
  by_cases hu0 : u = 0
  · simpa [hu0] using p.2.2
  · have hnotWhite := taoSection7BoundedLeast_minimal
      (fun t => taoSection7SourceWhitePoint n xi epsilon (p.1.upN t))
      1 (2 * n) (taoSection7CanonicalWhiteOffset_exists hxi hscalar p)
      (Nat.one_le_iff_ne_zero.2 hu0) hu
    simpa [taoSection7SourceWhitePoint, taoSection7White,
      taoSection7SourceBlackPoint, taoSection7Black, not_lt] using hnotWhite

noncomputable def taoSection7CanonicalLStar
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) : ℤ :=
  p.1.l + (taoSection7CanonicalFirstWhiteOffset hxi hscalar p : ℤ) - 1

theorem taoSection7CanonicalLStar_point_eq
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    ({ j := p.1.j, l := taoSection7CanonicalLStar hxi hscalar p } :
        TaoSection7Point) =
      p.1.upN (taoSection7CanonicalFirstWhiteOffset hxi hscalar p - 1) := by
  apply TaoSection7Point.ext'
  · rfl
  · simp [taoSection7CanonicalLStar, TaoSection7Point.upN]
    have ht := (taoSection7CanonicalFirstWhiteOffset_spec hxi hscalar p).1
    omega

theorem taoSection7CanonicalLStar_black
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    taoSection7SourceBlackPoint n xi epsilon
      ⟨p.1.j, taoSection7CanonicalLStar hxi hscalar p⟩ := by
  rw [taoSection7CanonicalLStar_point_eq hxi hscalar p]
  exact taoSection7CanonicalFirstWhiteOffset_prefix_black hxi hscalar p (by
    have ht := (taoSection7CanonicalFirstWhiteOffset_spec hxi hscalar p).1
    omega)

theorem taoSection7CanonicalLStar_up_white
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    taoSection7SourceWhitePoint n xi epsilon
      ⟨p.1.j, taoSection7CanonicalLStar hxi hscalar p + 1⟩ := by
  have hwhite :=
    (taoSection7CanonicalFirstWhiteOffset_spec hxi hscalar p).2.2
  convert hwhite using 1
  apply TaoSection7Point.ext'
  · rfl
  · simp [taoSection7CanonicalLStar, TaoSection7Point.upN]

theorem taoSection7CanonicalLStar_unique
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon)
    (LStar : ℤ) (hlower : p.1.l ≤ LStar)
    (hblack : ∀ q : TaoSection7Point,
      q.j = p.1.j → p.1.l ≤ q.l → q.l ≤ LStar →
        taoSection7SourceBlackPoint n xi epsilon q)
    (hwhite : taoSection7SourceWhitePoint n xi epsilon
      ⟨p.1.j, LStar + 1⟩) :
    LStar = taoSection7CanonicalLStar hxi hscalar p := by
  let t := taoSection7CanonicalFirstWhiteOffset hxi hscalar p
  let u : ℕ := (LStar + 1 - p.1.l).toNat
  have huCast : (u : ℤ) = LStar + 1 - p.1.l := by
    exact Int.toNat_of_nonneg (by omega)
  have hupEq : p.1.upN u =
      ({ j := p.1.j, l := LStar + 1 } : TaoSection7Point) := by
    apply TaoSection7Point.ext'
    · rfl
    · simp [TaoSection7Point.upN, huCast]
  have hwhiteU : taoSection7SourceWhitePoint n xi epsilon (p.1.upN u) := by
    rw [hupEq]
    exact hwhite
  have htLe : t ≤ u := by
    by_contra hnot
    have huLt : u < t := by omega
    have hblackU := taoSection7CanonicalFirstWhiteOffset_prefix_black
      hxi hscalar p huLt
    exact
      (taoSection7SourceWhitePoint_iff_not_geometryBlack n xi epsilon _).1
        hwhiteU
        ((taoSection7SourceBlackPoint_iff_geometryBlack n xi epsilon _).1
          hblackU)
  have huLe : u ≤ t := by
    by_contra hnot
    have htLt : t < u := by omega
    have htSpec := (taoSection7CanonicalFirstWhiteOffset_spec hxi hscalar p).2.2
    have hpointBlack :
        taoSection7SourceBlackPoint n xi epsilon (p.1.upN t) := by
      apply hblack (p.1.upN t)
      · rfl
      · simp [TaoSection7Point.upN]
      · simp [TaoSection7Point.upN]
        omega
    exact
      (taoSection7SourceWhitePoint_iff_not_geometryBlack n xi epsilon _).1
        htSpec
        ((taoSection7SourceBlackPoint_iff_geometryBlack n xi epsilon _).1
          hpointBlack)
  have htu : t = u := Nat.le_antisymm htLe huLe
  unfold taoSection7CanonicalLStar
  dsimp [t] at htu
  omega

def taoSection7BlackSuffix
    (black : TaoSection7Point → Prop) (jEnd : ℕ+) (lStar : ℤ)
    (jStart : ℕ) : Prop :=
  ∀ q : ℕ+, jStart ≤ (q : ℕ) → q ≤ jEnd → black ⟨q, lStar⟩

noncomputable def taoSection7TerminalBlackRunStart
    (black : TaoSection7Point → Prop) (jEnd : ℕ+) (lStar : ℤ)
    (hend : black ⟨jEnd, lStar⟩) : ℕ :=
  taoSection7BoundedLeast (taoSection7BlackSuffix black jEnd lStar)
    1 jEnd ⟨jEnd, jEnd.pos, le_rfl, by
      intro q hleft hright
      have hq : q = jEnd := by
        have hleftNat : (jEnd : ℕ) ≤ (q : ℕ) := hleft
        have hrightNat : (q : ℕ) ≤ (jEnd : ℕ) := by exact_mod_cast hright
        apply Subtype.ext
        exact Nat.le_antisymm hrightNat hleftNat
      simpa [hq] using hend⟩

theorem taoSection7TerminalBlackRunStart_spec
    (black : TaoSection7Point → Prop) (jEnd : ℕ+) (lStar : ℤ)
    (hend : black ⟨jEnd, lStar⟩) :
    1 ≤ taoSection7TerminalBlackRunStart black jEnd lStar hend ∧
      taoSection7TerminalBlackRunStart black jEnd lStar hend ≤ jEnd ∧
      taoSection7BlackSuffix black jEnd lStar
        (taoSection7TerminalBlackRunStart black jEnd lStar hend) := by
  exact taoSection7BoundedLeast_spec _ _ _ _

theorem taoSection7TerminalBlackRunStart_boundary
    (black : TaoSection7Point → Prop) (jEnd : ℕ+) (lStar : ℤ)
    (hend : black ⟨jEnd, lStar⟩) :
    taoSection7TerminalBlackRunStart black jEnd lStar hend = 1 ∨
      ∃ h : 1 < taoSection7TerminalBlackRunStart black jEnd lStar hend,
        ¬ black
          ⟨⟨taoSection7TerminalBlackRunStart black jEnd lStar hend - 1,
              by omega⟩, lStar⟩ := by
  let jStar := taoSection7TerminalBlackRunStart black jEnd lStar hend
  have hspec := taoSection7TerminalBlackRunStart_spec black jEnd lStar hend
  by_cases hOne : jStar = 1
  · exact Or.inl hOne
  · right
    have hj : 1 < jStar := by omega
    refine ⟨hj, ?_⟩
    intro hpred
    have hsuffix : taoSection7BlackSuffix black jEnd lStar (jStar - 1) := by
      intro q hleft hright
      by_cases hq : (q : ℕ) = jStar - 1
      · have hpoint : q = ⟨jStar - 1, by omega⟩ := by
          apply Subtype.ext
          exact hq
        simpa [hpoint] using hpred
      · exact hspec.2.2 q (by omega) hright
    have hminimal := taoSection7BoundedLeast_minimal
      (taoSection7BlackSuffix black jEnd lStar) 1 jEnd
      ⟨jEnd, jEnd.pos, le_rfl, by
        intro q hleft hright
        have hq : q = jEnd := by
          have hleftNat : (jEnd : ℕ) ≤ (q : ℕ) := hleft
          have hrightNat : (q : ℕ) ≤ (jEnd : ℕ) := by exact_mod_cast hright
          apply Subtype.ext
          exact Nat.le_antisymm hrightNat hleftNat
        simpa [hq] using hend⟩
      (by omega : 1 ≤ jStar - 1) (by omega : jStar - 1 < jStar)
    exact hminimal hsuffix

theorem taoSection7TerminalBlackRunStart_unique
    (black : TaoSection7Point → Prop) (jEnd : ℕ+) (lStar : ℤ)
    (hend : black ⟨jEnd, lStar⟩)
    (a : ℕ) (haPos : 1 ≤ a) (haEnd : a ≤ (jEnd : ℕ))
    (haSuffix : taoSection7BlackSuffix black jEnd lStar a)
    (haBoundary : a = 1 ∨
      ∃ h : 1 < a, ¬ black ⟨⟨a - 1, by omega⟩, lStar⟩) :
    a = taoSection7TerminalBlackRunStart black jEnd lStar hend := by
  let jStar := taoSection7TerminalBlackRunStart black jEnd lStar hend
  have hspec := taoSection7TerminalBlackRunStart_spec black jEnd lStar hend
  have hjLe : jStar ≤ a := by
    by_contra hnot
    have haLt : a < jStar := by omega
    have hex : ∃ k, 1 ≤ k ∧ k ≤ (jEnd : ℕ) ∧
        taoSection7BlackSuffix black jEnd lStar k :=
      ⟨jEnd, jEnd.pos, le_rfl, by
        intro q hleft hright
        have hleftNat : (jEnd : ℕ) ≤ (q : ℕ) := hleft
        have hrightNat : (q : ℕ) ≤ (jEnd : ℕ) := by exact_mod_cast hright
        have hq : q = jEnd := by
          apply Subtype.ext
          exact Nat.le_antisymm hrightNat hleftNat
        simpa [hq] using hend⟩
    have hminimal := taoSection7BoundedLeast_minimal
      (taoSection7BlackSuffix black jEnd lStar) 1 jEnd hex haPos
      (by simpa [jStar, taoSection7TerminalBlackRunStart] using haLt)
    exact hminimal haSuffix
  have haLe : a ≤ jStar := by
    by_contra hnot
    have hjLt : jStar < a := by omega
    rcases haBoundary with hOne | hpred
    · omega
    · rcases hpred with ⟨haTwo, hnotPred⟩
      have hjPred : jStar ≤ a - 1 := by omega
      let pred : ℕ+ := ⟨a - 1, by omega⟩
      have hpredEnd : pred ≤ jEnd := by
        exact_mod_cast (show a - 1 ≤ (jEnd : ℕ) by omega)
      exact hnotPred (hspec.2.2 pred hjPred hpredEnd)
  exact Nat.le_antisymm haLe hjLe

theorem taoSection7CanonicalLStar_blackInDomain
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    taoSection7SourceBlackInDomain n xi epsilon (n / 2)
      ⟨p.1.j, taoSection7CanonicalLStar hxi hscalar p⟩ :=
  ⟨p.2.1, taoSection7CanonicalLStar_black hxi hscalar p⟩

noncomputable def taoSection7CanonicalJStart
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) : ℕ :=
  taoSection7TerminalBlackRunStart
    (taoSection7SourceBlackInDomain n xi epsilon (n / 2))
    p.1.j (taoSection7CanonicalLStar hxi hscalar p)
    (taoSection7CanonicalLStar_blackInDomain hxi hscalar p)

theorem taoSection7CanonicalJStart_spec
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    1 ≤ taoSection7CanonicalJStart hxi hscalar p ∧
      taoSection7CanonicalJStart hxi hscalar p ≤ (p.1.j : ℕ) ∧
      taoSection7BlackSuffix
        (taoSection7SourceBlackInDomain n xi epsilon (n / 2))
        p.1.j (taoSection7CanonicalLStar hxi hscalar p)
        (taoSection7CanonicalJStart hxi hscalar p) := by
  exact taoSection7TerminalBlackRunStart_spec _ _ _ _

noncomputable def taoSection7CanonicalJStar
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) : ℕ+ :=
  ⟨taoSection7CanonicalJStart hxi hscalar p,
    (taoSection7CanonicalJStart_spec hxi hscalar p).1⟩

theorem taoSection7CanonicalJStart_boundary
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    taoSection7CanonicalJStart hxi hscalar p = 1 ∨
      ∃ h : 1 < taoSection7CanonicalJStart hxi hscalar p,
        ¬ taoSection7SourceBlackInDomain n xi epsilon (n / 2)
          ⟨⟨taoSection7CanonicalJStart hxi hscalar p - 1, by omega⟩,
            taoSection7CanonicalLStar hxi hscalar p⟩ := by
  exact taoSection7TerminalBlackRunStart_boundary _ _ _ _

theorem taoSection7CanonicalVertical_black
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon)
    (q : TaoSection7Point) (hqj : q.j = p.1.j)
    (hqlower : p.1.l ≤ q.l)
    (hqupper : q.l ≤ taoSection7CanonicalLStar hxi hscalar p) :
    taoSection7SourceBlackInDomain n xi epsilon (n / 2) q := by
  let u : ℕ := (q.l - p.1.l).toNat
  have huCast : (u : ℤ) = q.l - p.1.l := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hqlower)
  have hqEq : q = p.1.upN u := by
    apply TaoSection7Point.ext'
    · exact hqj
    · simp [TaoSection7Point.upN, huCast]
  have huLt : u < taoSection7CanonicalFirstWhiteOffset hxi hscalar p := by
    have ht := (taoSection7CanonicalFirstWhiteOffset_spec hxi hscalar p).1
    unfold taoSection7CanonicalLStar at hqupper
    omega
  refine ⟨?_, ?_⟩
  · unfold taoSection7SourcePointInDomain
    rw [hqj]
    exact p.2.1
  · rw [hqEq]
    exact taoSection7CanonicalFirstWhiteOffset_prefix_black
      hxi hscalar p huLt

noncomputable def taoSection7CanonicalTopLeftWitness
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    TaoSection7TopLeftWitness
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) p.1 := by
  let jStar := taoSection7CanonicalJStar hxi hscalar p
  let lStar := taoSection7CanonicalLStar hxi hscalar p
  refine
    { topLeft := ⟨jStar, lStar⟩
      topLeft_j_le := ?_
      source_l_le_topLeft_l := ?_
      vertical_black := ?_
      vertical_up_white := ?_
      horizontal_black := ?_
      left_boundary_white := ?_ }
  · exact_mod_cast (taoSection7CanonicalJStart_spec hxi hscalar p).2.1
  · have ht := (taoSection7CanonicalFirstWhiteOffset_spec hxi hscalar p).1
    dsimp [lStar, taoSection7CanonicalLStar]
    omega
  · intro q hqj hqlower hqupper
    exact taoSection7CanonicalVertical_black hxi hscalar p q hqj hqlower hqupper
  · intro hblack
    exact
      (taoSection7SourceWhitePoint_iff_not_geometryBlack n xi epsilon _).1
        (taoSection7CanonicalLStar_up_white hxi hscalar p)
        ((taoSection7SourceBlackPoint_iff_geometryBlack n xi epsilon _).1
          hblack.2)
  · intro q hleft hright hql
    have hsuffix := (taoSection7CanonicalJStart_spec hxi hscalar p).2.2
    have hb := hsuffix q.j (by exact_mod_cast hleft) hright
    have hqpoint :
        ({ j := q.j, l := taoSection7CanonicalLStar hxi hscalar p } :
          TaoSection7Point) = q := by
      apply TaoSection7Point.ext'
      · rfl
      · simpa [jStar, lStar] using hql.symm
    rwa [hqpoint] at hb
  · rcases taoSection7CanonicalJStart_boundary hxi hscalar p with hOne | hpred
    · exact Or.inl (by simpa [jStar, taoSection7CanonicalJStar] using hOne)
    · right
      rcases hpred with ⟨h, hwhite⟩
      refine ⟨by simpa [jStar, taoSection7CanonicalJStar] using h, ?_⟩
      simpa [jStar, lStar, taoSection7CanonicalJStar,
        TaoSection7Point.left] using hwhite

noncomputable def taoSection7CanonicalTriangleSize
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) : ℝ :=
  Real.log
    (epsilon /
      |taoSection7SourceTheta n xi
        (taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft|)

noncomputable def taoSection7CanonicalTriangle
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) : TaoSection7Triangle :=
  (taoSection7CanonicalTopLeftWitness hxi hscalar p).triangle
    (taoSection7CanonicalTriangleSize hxi hscalar p)

theorem taoSection7CanonicalTopLeft_abs_pos
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    0 < |taoSection7SourceTheta n xi
      (taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft| := by
  let w := taoSection7CanonicalTopLeftWitness hxi hscalar p
  have hdomain := (w.topLeft_black).1
  have hamp := one_third_le_three_pow_mul_abs_taoSection7ThetaResidue
    hxi w.topLeft.j hdomain w.topLeft.l
  change (1 : ℝ) / 3 ≤
    (3 : ℝ) ^ (n + 1 - 2 * (w.topLeft.j : ℕ)) *
      |taoSection7SourceTheta n xi w.topLeft| at hamp
  by_contra hnot
  have hzero : |taoSection7SourceTheta n xi w.topLeft| = 0 :=
    le_antisymm (not_lt.mp hnot) (abs_nonneg _)
  rw [hzero] at hamp
  norm_num at hamp

theorem taoSection7CanonicalTriangleSize_nonneg
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    0 ≤ taoSection7CanonicalTriangleSize hxi hscalar p := by
  let w := taoSection7CanonicalTopLeftWitness hxi hscalar p
  have hblack := (w.topLeft_black).2
  have habs := taoSection7CanonicalTopLeft_abs_pos hxi hscalar p
  unfold taoSection7CanonicalTriangleSize
  change |taoSection7SourceTheta n xi w.topLeft| ≤ epsilon at hblack
  exact Real.log_nonneg ((le_div_iff₀ habs).2 (by simpa using hblack))

theorem taoSection7CanonicalTopLeft_abs_eq
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    |taoSection7SourceTheta n xi
      (taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft| =
      epsilon * Real.exp
        (-taoSection7CanonicalTriangleSize hxi hscalar p) := by
  have habs := taoSection7CanonicalTopLeft_abs_pos hxi hscalar p
  have hepsilon := hscalar.epsilon_pos
  unfold taoSection7CanonicalTriangleSize
  rw [Real.exp_neg, Real.exp_log (div_pos hepsilon habs)]
  field_simp

theorem taoSection7CanonicalTriangle_rightEdge
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    TaoSection7TriangleRightEdgeInStrip
      (taoSection7TriangleRightBound n epsilon)
      (taoSection7CanonicalTriangle hxi hscalar p) := by
  let w := taoSection7CanonicalTopLeftWitness hxi hscalar p
  let A := |taoSection7SourceTheta n xi w.topLeft|
  let L := taoSection7TriangleLogScale epsilon
  let rho := taoSection7TriangleSeparation epsilon
  have hApos : 0 < A := taoSection7CanonicalTopLeft_abs_pos hxi hscalar p
  have hdomain := (w.topLeft_black).1
  have hraw := taoSection7SourceBlackPoint_raw_log_coordinate
    hxi hApos w.topLeft hdomain (by
      unfold taoSection7SourceBlackPoint taoSection7Black
      exact le_rfl)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog9Eq : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have harg : (1 : ℝ) / (3 * A) = (1 / A) / 3 := by field_simp
  have hratio :
      Real.log (1 / (3 * A)) / Real.log 3 =
        2 * (Real.log (1 / A) / Real.log 9) - 1 := by
    rw [harg, Real.log_div (one_div_ne_zero hApos.ne') (by norm_num),
      hlog9Eq]
    field_simp [hlog3.ne']
  rw [hratio] at hraw
  have hcoord :
      ((w.topLeft.j : ℕ) : ℝ) + Real.log (1 / A) / Real.log 9 ≤
        (n : ℝ) / 2 + 1 := by
    linarith
  have hsizeEq :
      taoSection7CanonicalTriangleSize hxi hscalar p =
        Real.log (1 / A) - L := by
    unfold taoSection7CanonicalTriangleSize
    rw [Real.log_div hscalar.epsilon_pos.ne' hApos.ne',
      show Real.log (1 / A) = -Real.log A by
        rw [one_div, Real.log_inv],
      show L = -Real.log epsilon by
        simp [L, taoSection7TriangleLogScale, one_div, Real.log_inv]]
    ring
  have hmargin := hscalar.inset_margin
  change 1 + rho ≤ L / Real.log 9 at hmargin
  unfold TaoSection7TriangleRightEdgeInStrip
  change ((w.topLeft.j : ℕ) : ℝ) +
      taoSection7CanonicalTriangleSize hxi hscalar p / Real.log 9 ≤
    (n : ℝ) / 2 - rho
  rw [hsizeEq]
  have hdiv :
      (Real.log (1 / A) - L) / Real.log 9 =
        Real.log (1 / A) / Real.log 9 - L / Real.log 9 := by ring
  rw [hdiv]
  linarith

theorem taoSection7CanonicalTriangle_member_jReal_le_rightEdge
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon)
    {q : TaoSection7Point}
    (hq : (taoSection7CanonicalTriangle hxi hscalar p).Mem q) :
    q.jReal ≤
      (((taoSection7CanonicalTriangle hxi hscalar p).cornerJ : ℕ) : ℝ) +
        (taoSection7CanonicalTriangle hxi hscalar p).size / Real.log 9 := by
  let Δ := taoSection7CanonicalTriangle hxi hscalar p
  change Δ.Mem q at hq
  change q.jReal ≤ ((Δ.cornerJ : ℕ) : ℝ) + Δ.size / Real.log 9
  have hlog9 : 0 < Real.log (9 : ℝ) := Real.log_pos (by norm_num)
  have hdepth := TaoSection7Triangle.horizontalDepth_real_eq_sub_of_cornerJ_le
    (Δ := Δ) (jStar := q.j) (lStar := q.l)
    (show Δ.cornerJ ≤ q.j from hq.1)
  have hvertical := TaoSection7Triangle.verticalDepth_nonneg_of_mem hq
  have hverticalTerm :
      0 ≤ ((Δ.verticalDepth q : ℤ) : ℝ) * Real.log 2 :=
    mul_nonneg (by exact_mod_cast hvertical)
      (Real.log_pos (by norm_num)).le
  have hweight := hq.2.2
  have hhorizontal :
      (q.jReal - ((Δ.cornerJ : ℕ) : ℝ)) * Real.log 9 ≤ Δ.size := by
    rw [hdepth] at hweight
    dsimp [TaoSection7Point.jReal]
    linarith
  have hdiv :
      q.jReal - ((Δ.cornerJ : ℕ) : ℝ) ≤ Δ.size / Real.log 9 :=
    (le_div_iff₀ hlog9).2 (by simpa [mul_comm] using hhorizontal)
  exact by linarith

theorem taoSection7CanonicalTriangle_blackOn
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    (taoSection7CanonicalTriangle hxi hscalar p).BlackOn
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) := by
  let w := taoSection7CanonicalTopLeftWitness hxi hscalar p
  let Δ := taoSection7CanonicalTriangle hxi hscalar p
  intro q hq
  have hj : (w.topLeft.j : ℕ) ≤ (q.j : ℕ) := by
    exact_mod_cast hq.1
  have hl : q.l ≤ w.topLeft.l := hq.2.1
  have hweight :
      taoSection7SoutheastWeight w.topLeft q ≤
        taoSection7CanonicalTriangleSize hxi hscalar p := by
    have hm := hq.2.2
    change
      ((((q.j : ℕ) - (w.topLeft.j : ℕ) : ℕ) : ℝ) * Real.log 9 +
          (((w.topLeft.l - q.l : ℤ) : ℝ)) * Real.log 2 ≤
        taoSection7CanonicalTriangleSize hxi hscalar p) at hm
    unfold taoSection7SoutheastWeight taoSection7SoutheastH
      taoSection7SoutheastV
    have hv := Int.toNat_of_nonneg (sub_nonneg.mpr hl)
    have hvReal :
        (((w.topLeft.l - q.l).toNat : ℕ) : ℝ) =
          ((w.topLeft.l - q.l : ℤ) : ℝ) := by
      exact_mod_cast hv
    rw [hvReal]
    exact hm
  have htheta : |taoSection7SourceTheta n xi q| ≤ epsilon := by
    calc
      |taoSection7SourceTheta n xi q| ≤
          Real.exp (taoSection7SoutheastWeight w.topLeft q) *
            |taoSection7SourceTheta n xi w.topLeft| :=
        abs_taoSection7SourceTheta_southeast_le n xi w.topLeft q hj hl
      _ ≤ Real.exp (taoSection7CanonicalTriangleSize hxi hscalar p) *
          |taoSection7SourceTheta n xi w.topLeft| := by
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hweight)
          (abs_nonneg _)
      _ = epsilon := by
        rw [taoSection7CanonicalTopLeft_abs_eq hxi hscalar p]
        calc
          Real.exp (taoSection7CanonicalTriangleSize hxi hscalar p) *
              (epsilon * Real.exp
                (-taoSection7CanonicalTriangleSize hxi hscalar p)) =
              epsilon *
                (Real.exp (taoSection7CanonicalTriangleSize hxi hscalar p) *
                  Real.exp
                    (-taoSection7CanonicalTriangleSize hxi hscalar p)) := by ring
          _ = epsilon := by rw [← Real.exp_add]; simp
  have hqEdge :=
    taoSection7CanonicalTriangle_member_jReal_le_rightEdge hxi hscalar p hq
  have hright := taoSection7CanonicalTriangle_rightEdge hxi hscalar p
  have hqRight : q.jReal ≤ taoSection7TriangleRightBound n epsilon :=
    hqEdge.trans hright
  have hqHalf : q.jReal ≤ (n : ℝ) / 2 :=
    hqRight.trans (taoSection7TriangleRightBound_le_half
      hscalar.epsilon_pos
      (hscalar.epsilon_le_one_hundredth.trans (by norm_num)))
  have htwoReal : (2 * (q.j : ℕ) : ℝ) ≤ (n : ℝ) := by
    dsimp [TaoSection7Point.jReal] at hqHalf
    nlinarith
  have htwoNat : 2 * (q.j : ℕ) ≤ n := by exact_mod_cast htwoReal
  exact ⟨by
    unfold taoSection7SourcePointInDomain
    omega, htheta⟩

end

end Tao
end Erdos1135
