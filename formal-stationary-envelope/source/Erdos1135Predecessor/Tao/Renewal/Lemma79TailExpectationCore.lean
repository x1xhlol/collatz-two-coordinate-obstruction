/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.HoldFirstPassagePMF
import Erdos1135Predecessor.Tao.Renewal.Lemma710PostStoppedKernel
import Erdos1135Predecessor.Tao.Renewal.Lemma77FirstPassageEndpoint
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3Stopping

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

def Lemma79FirstTriangleHitFromZero
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (first : ℕ) : Prop :=
  TaoSection7Case3TriangleHit pointAt family first ∧
    ∀ s : ℕ, s < first ->
      ¬ TaoSection7Case3TriangleHit pointAt family s

namespace Lemma79FirstEntryAtomFamily

end Lemma79FirstEntryAtomFamily

namespace Lemma79FirstEntryAtomFiniteCarrier

end Lemma79FirstEntryAtomFiniteCarrier

noncomputable def lemma79VerticalFirstPassageFixedTailSplit
    (p : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ)
    (full : List TaoSection7RenewalPoint) :
    List TaoSection7RenewalPoint × List TaoSection7RenewalPoint :=
  let K := lemma79VerticalFirstPassageCut start gap full
  (full.take K, (full.drop K).take p)

noncomputable def lemma79RawHoldFirstPassageFixedTailSplitPMF
    (N p : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ) :
    PMF (List TaoSection7RenewalPoint × List TaoSection7RenewalPoint) :=
  (taoSection7HoldSourcePrefixListPMF N).map fun src =>
    lemma79VerticalFirstPassageFixedTailSplit p start gap
      (lemma79DecodeHoldSourcePrefixes src)

theorem lemma79VerticalFirstPassagePrefix_take_cut_of_rawSource_nonzero
    (start : TaoSection7RenewalPoint) (gap p : ℕ)
    (src : List (ℕ × List ℕ))
    (hsrc :
      taoSection7HoldSourcePrefixListPMF (gap + 1 + p) src ≠ 0) :
    let full := lemma79DecodeHoldSourcePrefixes src
    let K := lemma79VerticalFirstPassageCut start gap full
    TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap K (full.take K) ∧ K ≤ gap + 1 := by
  have hlength : src.length = gap + 1 + p := by
    by_contra hne
    exact hsrc
      (taoSection7HoldSourcePrefixListPMF_apply_eq_zero_of_length_ne
        (gap + 1 + p) src hne)
  have hlen : gap + 1 ≤ src.length := by omega
  exact
    lemma79VerticalFirstPassagePrefix_take_cut_decode_and_le
      start gap src hlen

theorem lemma79VerticalFirstPassageFixedTailSplit_eq_iff_take_add_eq
    {start : TaoSection7RenewalPoint} {gap K p : ℕ}
    {pre tail full : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre) :
    lemma79VerticalFirstPassageFixedTailSplit p start gap full = (pre, tail) ↔
      full.take (K + p) = pre ++ tail := by
  let cut := lemma79VerticalFirstPassageCut start gap full
  constructor
  · intro hsplit
    have hpre : full.take cut = pre := by
      exact congrArg Prod.fst hsplit
    have htail_take : (full.drop cut).take p = tail := by
      exact congrArg Prod.snd hsplit
    have hcut_le : cut ≤ full.length :=
      lemma79VerticalFirstPassageCut_le_length start gap full
    have hcut : cut = K := by
      calc
        cut = (full.take cut).length := by
          simp [List.length_take, hcut_le]
        _ = pre.length := congrArg List.length hpre
        _ = K := hfirst.length_eq
    calc
      full.take (K + p) = full.take K ++ (full.drop K).take p :=
        List.take_add
      _ = pre ++ tail := by simpa [hcut] using congrArg₂ (· ++ ·) hpre htail_take
  · intro hprefix
    have hpre : full.take K = pre := by
      have htake := congrArg (fun xs => xs.take K) hprefix
      change (full.take (K + p)).take K = (pre ++ tail).take K at htake
      rw [List.take_take, Nat.min_eq_left (Nat.le_add_right K p)] at htake
      simpa [hfirst.length_eq] using htake
    have htail_take : (full.drop K).take p = tail := by
      have hdrop := congrArg (fun xs => xs.drop K) hprefix
      change (full.take (K + p)).drop K = (pre ++ tail).drop K at hdrop
      rw [List.drop_take, Nat.add_sub_cancel_left] at hdrop
      simpa [hfirst.length_eq] using hdrop
    have hcut : lemma79VerticalFirstPassageCut start gap full = K :=
      lemma79VerticalFirstPassageCut_eq_of_take_eq hfirst hpre
    apply Prod.ext
    · simpa [lemma79VerticalFirstPassageFixedTailSplit, hcut] using hpre
    · simpa [lemma79VerticalFirstPassageFixedTailSplit, hcut] using htail_take

theorem lemma79_decodedHoldFirstPassageFixedTailSplit_apply_toReal
    {start : TaoSection7RenewalPoint} {gap K p N : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (horizon : K + p ≤ N) :
    (((taoSection7HoldListPMF N).map
        (lemma79VerticalFirstPassageFixedTailSplit p start gap))
      (pre, tail)).toReal =
      (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal := by
  have hmap :
      ((taoSection7HoldListPMF N).map
          (lemma79VerticalFirstPassageFixedTailSplit p start gap))
          (pre, tail) =
        ((taoSection7HoldListPMF N).map
          (fun full : List TaoSection7RenewalPoint => full.take (K + p)))
          (pre ++ tail) := by
    exact
      lemma79_map_apply_eq_of_fiber_iff
        (taoSection7HoldListPMF N)
        (lemma79VerticalFirstPassageFixedTailSplit p start gap)
        (fun full : List TaoSection7RenewalPoint => full.take (K + p))
        (pre, tail) (pre ++ tail) (by
          intro full
          simpa only [eq_comm] using
            lemma79VerticalFirstPassageFixedTailSplit_eq_iff_take_add_eq
              (full := full) (p := p) (tail := tail) hfirst)
  rw [hmap]
  exact
    taoSection7HoldListPMF_map_take_apply_toReal_eq_of_le
      horizon (pre ++ tail)

theorem lemma79_rawHoldFirstPassageFixedTailSplit_apply_toReal
    {start : TaoSection7RenewalPoint} {gap K p N : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (horizon : K + p ≤ N) :
    (lemma79RawHoldFirstPassageFixedTailSplitPMF N p start gap
      (pre, tail)).toReal =
      (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal := by
  unfold lemma79RawHoldFirstPassageFixedTailSplitPMF
  change
    (((taoSection7HoldSourcePrefixListPMF N).map
        (lemma79VerticalFirstPassageFixedTailSplit p start gap ∘
          lemma79DecodeHoldSourcePrefixes)) (pre, tail)).toReal = _
  rw [← PMF.map_comp]
  change
    ((((taoSection7HoldSourcePrefixListPMF N).map
        (fun xs => xs.map fun x =>
          taoSection7HoldPointOfPrefix x.1 x.2)).map
        (lemma79VerticalFirstPassageFixedTailSplit p start gap))
      (pre, tail)).toReal = _
  rw [taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq]
  exact
    lemma79_decodedHoldFirstPassageFixedTailSplit_apply_toReal
      hfirst horizon

theorem lemma79_rawHoldFirstPassageFixedTailSplit_product_toReal
    {start : TaoSection7RenewalPoint} {gap K p N : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (htail : tail.length = p) (horizon : K + p ≤ N) :
    (lemma79RawHoldFirstPassageFixedTailSplitPMF N p start gap
      (pre, tail)).toReal =
      (taoSection7HoldListPMF K pre).toReal *
        (taoSection7HoldListPMF p tail).toReal := by
  rw [lemma79_rawHoldFirstPassageFixedTailSplit_apply_toReal
    hfirst horizon]
  exact taoSection7HoldListPMF_append_toReal_of_lengths
    hfirst.length_eq htail

theorem lemma79_rawHoldFirstPassageFixedTailSplit_product_toReal_of_le_bound
    {start : TaoSection7RenewalPoint} {gap K B p : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (htail : tail.length = p) (hKB : K ≤ B) :
    (lemma79RawHoldFirstPassageFixedTailSplitPMF (B + p) p start gap
      (pre, tail)).toReal =
      (taoSection7HoldListPMF K pre).toReal *
        (taoSection7HoldListPMF p tail).toReal :=
  lemma79_rawHoldFirstPassageFixedTailSplit_product_toReal
    hfirst htail (Nat.add_le_add_right hKB p)

noncomputable def lemma79RawHoldFirstPassagePrefixPMF
    (p : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ) :
    PMF (List TaoSection7RenewalPoint) :=
  (lemma79RawHoldFirstPassageFixedTailSplitPMF
    (gap + 1 + p) p start gap).map Prod.fst

theorem lemma79_rawHoldFirstPassageFixedTailSplit_product_of_le_bound
    {start : TaoSection7RenewalPoint} {gap K B p : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (htail : tail.length = p) (hKB : K ≤ B) :
    lemma79RawHoldFirstPassageFixedTailSplitPMF (B + p) p start gap
        (pre, tail) =
      taoSection7HoldListPMF K pre * taoSection7HoldListPMF p tail := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  exact
    lemma79_rawHoldFirstPassageFixedTailSplit_product_toReal_of_le_bound
      hfirst htail hKB

theorem lemma79VerticalFirstPassageFixedTailSplit_fst_eq_iff_take_eq
    {start : TaoSection7RenewalPoint} {gap K p : ℕ}
    {pre full : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre) :
    (lemma79VerticalFirstPassageFixedTailSplit p start gap full).1 = pre ↔
      full.take K = pre := by
  let cut := lemma79VerticalFirstPassageCut start gap full
  constructor
  · intro hpre
    change full.take cut = pre at hpre
    have hcut_le : cut ≤ full.length :=
      lemma79VerticalFirstPassageCut_le_length start gap full
    have hcut : cut = K := by
      calc
        cut = (full.take cut).length := by
          simp [List.length_take, hcut_le]
        _ = pre.length := congrArg List.length hpre
        _ = K := hfirst.length_eq
    simpa [hcut] using hpre
  · intro htake
    have hcut : lemma79VerticalFirstPassageCut start gap full = K :=
      lemma79VerticalFirstPassageCut_eq_of_take_eq hfirst htake
    simpa [lemma79VerticalFirstPassageFixedTailSplit, hcut] using htake

theorem lemma79_rawHoldFirstPassagePrefixPMF_apply_of_firstPassage
    {start : TaoSection7RenewalPoint} {gap K p : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (hK : K ≤ gap + 1) :
    lemma79RawHoldFirstPassagePrefixPMF p start gap pre =
      taoSection7HoldListPMF K pre := by
  have hKN : K ≤ gap + 1 + p := hK.trans (Nat.le_add_right (gap + 1) p)
  unfold lemma79RawHoldFirstPassagePrefixPMF
  unfold lemma79RawHoldFirstPassageFixedTailSplitPMF
  rw [PMF.map_comp]
  have hmap :
      ((taoSection7HoldSourcePrefixListPMF (gap + 1 + p)).map
          (Prod.fst ∘ fun src =>
            lemma79VerticalFirstPassageFixedTailSplit p start gap
              (lemma79DecodeHoldSourcePrefixes src))) pre =
        ((taoSection7HoldSourcePrefixListPMF (gap + 1 + p)).map
          (fun src => (lemma79DecodeHoldSourcePrefixes src).take K)) pre := by
    exact
      lemma79_map_apply_eq_of_fiber_iff
        (taoSection7HoldSourcePrefixListPMF (gap + 1 + p))
        (Prod.fst ∘ fun src =>
          lemma79VerticalFirstPassageFixedTailSplit p start gap
            (lemma79DecodeHoldSourcePrefixes src))
        (fun src => (lemma79DecodeHoldSourcePrefixes src).take K)
        pre pre (by
          intro src
          simpa only [Function.comp_apply, eq_comm] using
            lemma79VerticalFirstPassageFixedTailSplit_fst_eq_iff_take_eq
              (p := p) (full := lemma79DecodeHoldSourcePrefixes src) hfirst)
  rw [hmap]
  have htake :=
    taoSection7HoldSourcePrefixListPMF_map_take_holdPoint_eq_of_le hKN
  exact congrArg (fun rho : PMF (List TaoSection7RenewalPoint) => rho pre)
    (by simpa [lemma79DecodeHoldSourcePrefixes] using htake)

theorem lemma79_rawHoldFirstPassageFixedTailSplit_nonzero_certifies
    {start : TaoSection7RenewalPoint} {gap p : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hpair :
      lemma79RawHoldFirstPassageFixedTailSplitPMF (gap + 1 + p) p start gap
        (pre, tail) ≠ 0) :
    TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap pre.length pre ∧
      pre.length ≤ gap + 1 ∧ tail.length = p := by
  classical
  have hmem :
      (pre, tail) ∈
        (lemma79RawHoldFirstPassageFixedTailSplitPMF
          (gap + 1 + p) p start gap).support := hpair
  unfold lemma79RawHoldFirstPassageFixedTailSplitPMF at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨src, hsrc, hsplit⟩
  let full := lemma79DecodeHoldSourcePrefixes src
  let K := lemma79VerticalFirstPassageCut start gap full
  have hcert :=
    lemma79VerticalFirstPassagePrefix_take_cut_of_rawSource_nonzero
      start gap p src (by simpa using hsrc)
  change
    TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap K (full.take K) ∧ K ≤ gap + 1 at hcert
  have hpre : full.take K = pre := by
    exact congrArg Prod.fst hsplit
  have htail : (full.drop K).take p = tail := by
    exact congrArg Prod.snd hsplit
  have hK : K = pre.length := by
    calc
      K = (full.take K).length := hcert.1.length_eq.symm
      _ = pre.length := congrArg List.length hpre
  have hfirst :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap pre.length pre := by
    rw [← hK, ← hpre]
    exact hcert.1
  have hB : pre.length ≤ gap + 1 := by
    rw [← hK]
    exact hcert.2
  have hsrc_length : src.length = gap + 1 + p := by
    by_contra hne
    exact hsrc
      (taoSection7HoldSourcePrefixListPMF_apply_eq_zero_of_length_ne
        (gap + 1 + p) src hne)
  have hfull_length : full.length = gap + 1 + p := by
    simpa [full] using hsrc_length
  have htail_length : tail.length = p := by
    rw [← htail]
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    omega
  exact ⟨hfirst, hB, htail_length⟩

theorem lemma79_rawHoldFirstPassageFixedTailSplit_apply_eq_zero_of_invalid
    {start : TaoSection7RenewalPoint} {gap p : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hinvalid :
      ¬ (TaoSection7Lemma710.VerticalFirstPassagePrefix
          start gap pre.length pre ∧
        pre.length ≤ gap + 1 ∧ tail.length = p)) :
    lemma79RawHoldFirstPassageFixedTailSplitPMF (gap + 1 + p) p start gap
        (pre, tail) = 0 := by
  by_contra hne
  exact hinvalid
    (lemma79_rawHoldFirstPassageFixedTailSplit_nonzero_certifies hne)

theorem lemma79_rawHoldFirstPassagePrefixPMF_apply_eq_zero_of_invalid
    {start : TaoSection7RenewalPoint} {gap p : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (hinvalid :
      ¬ (TaoSection7Lemma710.VerticalFirstPassagePrefix
          start gap pre.length pre ∧ pre.length ≤ gap + 1)) :
    lemma79RawHoldFirstPassagePrefixPMF p start gap pre = 0 := by
  classical
  by_contra hne
  have hmem :
      pre ∈ (lemma79RawHoldFirstPassagePrefixPMF p start gap).support := hne
  unfold lemma79RawHoldFirstPassagePrefixPMF at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨pair, hpair, hfst⟩
  rcases pair with ⟨pre', tail⟩
  change pre' = pre at hfst
  subst pre'
  have hcert :=
    lemma79_rawHoldFirstPassageFixedTailSplit_nonzero_certifies
      (show
        lemma79RawHoldFirstPassageFixedTailSplitPMF (gap + 1 + p) p start gap
          (pre, tail) ≠ 0 from hpair)
  exact hinvalid ⟨hcert.1, hcert.2.1⟩

theorem lemma79_rawHoldFirstPassagePrefixPMF_eq_canonical
    (p : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ) :
    lemma79RawHoldFirstPassagePrefixPMF p start gap =
      lemma77CanonicalFirstPassagePrefixPMF start gap := by
  classical
  apply PMF.ext
  intro pre
  by_cases hpre :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
          start gap pre.length pre ∧
        pre.length ≤ gap + 1
  · rw [lemma79_rawHoldFirstPassagePrefixPMF_apply_of_firstPassage
          hpre.1 hpre.2,
        lemma77CanonicalFirstPassagePrefixPMF_apply_of_firstPassage
          hpre.1 hpre.2]
  · rw [lemma79_rawHoldFirstPassagePrefixPMF_apply_eq_zero_of_invalid hpre,
        lemma77CanonicalFirstPassagePrefixPMF_apply_eq_zero_of_invalid hpre]

theorem lemma79_prefixFreshTail_bind_apply
    {Pre Tail : Type*} (pi : PMF Pre) (tau : PMF Tail)
    (pre : Pre) (tail : Tail) :
    (pi.bind fun pre' => tau.map fun tail' => (pre', tail')) (pre, tail) =
      pi pre * tau tail := by
  classical
  rw [PMF.bind_apply]
  rw [tsum_eq_single pre]
  · rw [PMF.map_apply]
    rw [tsum_eq_single tail]
    · simp
    · intro tail' hne
      have hpair : (pre, tail) ≠ (pre, tail') := by
        intro h
        exact hne (Prod.ext_iff.mp h).2.symm
      simp [hpair]
  · intro pre' hne
    have hmap_zero :
        (tau.map fun tail' => (pre', tail')) (pre, tail) = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro tail'
      have hpair : (pre, tail) ≠ (pre', tail') := by
        intro h
        exact hne (Prod.ext_iff.mp h).1.symm
      simp [hpair]
    rw [hmap_zero, mul_zero]

theorem lemma79_rawHoldFirstPassageFixedTailSplitPMF_eq_bind
    (p : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ) :
    lemma79RawHoldFirstPassageFixedTailSplitPMF
        (gap + 1 + p) p start gap =
      (lemma79RawHoldFirstPassagePrefixPMF p start gap).bind fun pre =>
        (taoSection7HoldListPMF p).map fun tail => (pre, tail) := by
  classical
  apply PMF.ext
  rintro ⟨pre, tail⟩
  rw [lemma79_prefixFreshTail_bind_apply]
  by_cases hpre :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
          start gap pre.length pre ∧ pre.length ≤ gap + 1
  · by_cases htail : tail.length = p
    · rw [lemma79_rawHoldFirstPassageFixedTailSplit_product_of_le_bound
          hpre.1 htail hpre.2]
      rw [lemma79_rawHoldFirstPassagePrefixPMF_apply_of_firstPassage
          hpre.1 hpre.2]
    · rw [taoSection7HoldListPMF_apply_eq_zero_of_length_ne p tail htail,
          mul_zero]
      exact
        lemma79_rawHoldFirstPassageFixedTailSplit_apply_eq_zero_of_invalid
          (fun hcert => htail hcert.2.2)
  · rw [lemma79_rawHoldFirstPassagePrefixPMF_apply_eq_zero_of_invalid hpre,
        zero_mul]
    exact
      lemma79_rawHoldFirstPassageFixedTailSplit_apply_eq_zero_of_invalid
        (fun hcert => hpre ⟨hcert.1, hcert.2.1⟩)

noncomputable def lemma79PMFENNExpectation
    {Omega : Type*} (mu : PMF Omega) (F : Omega -> ENNReal) : ENNReal :=
  ∑' omega, mu omega * F omega

theorem lemma79PMFENNExpectation_map
    {Omega Xi : Type*} (mu : PMF Omega) (f : Omega -> Xi)
    (G : Xi -> ENNReal) :
    lemma79PMFENNExpectation (mu.map f) G =
      lemma79PMFENNExpectation mu (G ∘ f) := by
  classical
  unfold lemma79PMFENNExpectation
  calc
    (∑' xi, (mu.map f) xi * G xi) =
        ∑' xi, (∑' omega, if xi = f omega then mu omega else 0) * G xi := by
      apply tsum_congr
      intro xi
      rw [PMF.map_apply]
    _ = ∑' xi, ∑' omega,
        (if xi = f omega then mu omega else 0) * G xi := by
      apply tsum_congr
      intro xi
      rw [ENNReal.tsum_mul_right]
    _ = ∑' omega, ∑' xi,
        (if xi = f omega then mu omega else 0) * G xi := by
      rw [ENNReal.tsum_comm]
    _ = ∑' omega, mu omega * G (f omega) := by
      apply tsum_congr
      intro omega
      rw [tsum_eq_single (f omega)]
      · simp
      · intro xi hne
        simp [hne]
    _ = ∑' omega, mu omega * (G ∘ f) omega := by
      rfl

theorem lemma79_pmfENNExpectation_bind_pair_prefix_mul
    {Pre Tail : Type*} (pi : PMF Pre) (tau : PMF Tail)
    (prefixWeight : Pre -> ENNReal) (future : Pre -> Tail -> ENNReal) :
    lemma79PMFENNExpectation
        (pi.bind fun pre => tau.map fun tail => (pre, tail))
        (fun pair => prefixWeight pair.1 * future pair.1 pair.2) =
      ∑' pre, pi pre *
        (prefixWeight pre *
          ∑' tail, tau tail * future pre tail) := by
  classical
  unfold lemma79PMFENNExpectation
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro pre
  calc
    (∑' tail,
      (pi.bind fun pre => tau.map fun tail => (pre, tail)) (pre, tail) *
        (prefixWeight pre * future pre tail)) =
        ∑' tail, (pi pre * tau tail) *
          (prefixWeight pre * future pre tail) := by
            apply tsum_congr
            intro tail
            rw [lemma79_prefixFreshTail_bind_apply]
    _ = ∑' tail, pi pre *
        (prefixWeight pre * (tau tail * future pre tail)) := by
          apply tsum_congr
          intro tail
          ac_rfl
    _ = pi pre *
        ∑' tail, prefixWeight pre * (tau tail * future pre tail) := by
          rw [ENNReal.tsum_mul_left]
    _ = pi pre *
        (prefixWeight pre * ∑' tail, tau tail * future pre tail) := by
          rw [ENNReal.tsum_mul_left]

theorem lemma79_pmfENNExpectation_bind_pair_prefix_mul_le
    {Pre Tail : Type*} (pi : PMF Pre) (tau : PMF Tail)
    (prefixWeight : Pre -> ENNReal) (future : Pre -> Tail -> ENNReal)
    (C : ENNReal)
    (hfuture :
      ∀ pre, lemma79PMFENNExpectation tau (future pre) ≤ C) :
    lemma79PMFENNExpectation
        (pi.bind fun pre => tau.map fun tail => (pre, tail))
        (fun pair => prefixWeight pair.1 * future pair.1 pair.2) ≤
      lemma79PMFENNExpectation pi (fun pre => prefixWeight pre * C) := by
  rw [lemma79_pmfENNExpectation_bind_pair_prefix_mul]
  unfold lemma79PMFENNExpectation
  apply ENNReal.tsum_le_tsum
  intro pre
  exact mul_le_mul_right
    (mul_le_mul_right (hfuture pre) (prefixWeight pre)) (pi pre)

theorem lemma79PMFENNExpectation_mul_const
    {Omega : Type*} (mu : PMF Omega) (F : Omega -> ENNReal) (C : ENNReal) :
    lemma79PMFENNExpectation mu (fun omega => F omega * C) =
      lemma79PMFENNExpectation mu F * C := by
  unfold lemma79PMFENNExpectation
  calc
    (∑' omega, mu omega * (F omega * C)) =
        ∑' omega, (mu omega * F omega) * C := by
          apply tsum_congr
          intro omega
          ac_rfl
    _ = (∑' omega, mu omega * F omega) * C :=
      ENNReal.tsum_mul_right

theorem lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure
    {Omega : Type*} (mu : PMF Omega) (Event : Set Omega) :
    lemma79PMFENNExpectation mu (Event.indicator fun _ => 1) =
      mu.toOuterMeasure Event := by
  classical
  unfold lemma79PMFENNExpectation
  rw [PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro omega
  by_cases hmem : omega ∈ Event <;>
    simp [Set.indicator, hmem]

theorem lemma79_pmfENNExpectation_bind_pair_prefix_mul_le_const_mul
    {Pre Tail : Type*} (pi : PMF Pre) (tau : PMF Tail)
    (prefixWeight : Pre -> ENNReal) (future : Pre -> Tail -> ENNReal)
    (C : ENNReal)
    (hfuture :
      ∀ pre, lemma79PMFENNExpectation tau (future pre) ≤ C) :
    lemma79PMFENNExpectation
        (pi.bind fun pre => tau.map fun tail => (pre, tail))
        (fun pair => prefixWeight pair.1 * future pair.1 pair.2) ≤
      C * lemma79PMFENNExpectation pi prefixWeight := by
  calc
    lemma79PMFENNExpectation
        (pi.bind fun pre => tau.map fun tail => (pre, tail))
        (fun pair => prefixWeight pair.1 * future pair.1 pair.2) ≤
        lemma79PMFENNExpectation pi (fun pre => prefixWeight pre * C) :=
      lemma79_pmfENNExpectation_bind_pair_prefix_mul_le
        pi tau prefixWeight future C hfuture
    _ = lemma79PMFENNExpectation pi prefixWeight * C :=
      lemma79PMFENNExpectation_mul_const pi prefixWeight C
    _ = C * lemma79PMFENNExpectation pi prefixWeight := mul_comm _ _

theorem lemma79_rawHoldFirstPassageFixedTailSplit_weightedExpectation_le
    (J : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ)
    (prefixWeight : List TaoSection7RenewalPoint -> ENNReal)
    (future : TaoSection7RenewalPoint ->
      List TaoSection7RenewalPoint -> ENNReal)
    (C : ENNReal)
    (hfuture :
      ∀ endpoint,
        lemma79PMFENNExpectation
          (taoSection7HoldListPMF J) (future endpoint) ≤ C) :
    lemma79PMFENNExpectation
        (lemma79RawHoldFirstPassageFixedTailSplitPMF
          (gap + 1 + J) J start gap)
        (fun pair =>
          prefixWeight pair.1 *
            future
              (taoSection7RenewalPathPoint start pair.1 pair.1.length)
              pair.2) ≤
      C * lemma79PMFENNExpectation
        (lemma79RawHoldFirstPassagePrefixPMF J start gap)
        prefixWeight := by
  rw [lemma79_rawHoldFirstPassageFixedTailSplitPMF_eq_bind]
  exact
    lemma79_pmfENNExpectation_bind_pair_prefix_mul_le_const_mul
      (lemma79RawHoldFirstPassagePrefixPMF J start gap)
      (taoSection7HoldListPMF J) prefixWeight
      (fun pre tail =>
        future (taoSection7RenewalPathPoint start pre pre.length) tail)
      C (fun pre =>
        hfuture (taoSection7RenewalPathPoint start pre pre.length))

def lemma79KeyAtom
    {Omega Key : Type*} (Parent : Set Omega) (key : Omega -> Key) (k : Key) :
    Set Omega :=
  {omega | omega ∈ Parent ∧ key omega = k}

theorem lemma79_pmfToOuterMeasure_partition_of_key
    {Omega Key : Type*} (mu : PMF Omega)
    (Parent : Set Omega) (key : Omega -> Key) :
    mu.toOuterMeasure Parent =
      ∑' k, mu.toOuterMeasure (lemma79KeyAtom Parent key k) := by
  classical
  rw [PMF.toOuterMeasure_apply]
  calc
    (∑' omega, Parent.indicator mu omega) =
        ∑' omega, ∑' k,
          (lemma79KeyAtom Parent key k).indicator mu omega := by
      apply tsum_congr
      intro omega
      by_cases hParent : omega ∈ Parent
      · rw [tsum_eq_single (key omega)]
        · simp [lemma79KeyAtom, hParent]
        · intro k hne
          have hkey_ne : key omega ≠ k := fun h => hne h.symm
          simp [lemma79KeyAtom, hParent, hkey_ne]
      · simp [lemma79KeyAtom, hParent]
    _ = ∑' k, ∑' omega,
        (lemma79KeyAtom Parent key k).indicator mu omega := by
      rw [ENNReal.tsum_comm]
    _ = ∑' k, mu.toOuterMeasure (lemma79KeyAtom Parent key k) := by
      apply tsum_congr
      intro k
      rw [PMF.toOuterMeasure_apply]

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
