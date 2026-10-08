/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.OddSource
import Erdos1135SecondScale.Tao.Syracuse.TruncatedValuationGeom2
import Erdos1135SecondScale.Tao.Syracuse.TruncatedValuationUniformOdd

/-!
# Neutral source laws for Proposition 1.9

This module owns the odd source type and its residue and Syracuse valuation
laws below the Section 5 facade.  It also records the exact deterministic PMF
squares through strict truncation, including the degenerate modulus-one case.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The law of the first `n` actual Syracuse valuations from an odd-valued source. -/
noncomputable def taoProp19ActualValuationLaw
    (μ : PMF TaoOddNat) (n : ℕ) : PMF (List ℕ+) :=
  μ.map fun N => syracuseValuationPNatList n N.1 N.2

/-- The source law modulo `2^M`, before comparison to odd residue classes. -/
noncomputable def taoProp19SourceResidueLaw
    (μ : PMF TaoOddNat) (M : ℕ) : PMF (ZMod (2 ^ M)) :=
  μ.map fun N => (N.1 : ZMod (2 ^ M))

/-- Canonical comparison law at every modulus.  Modulus one is the sole
residue class; positive moduli use the uniform law on odd representatives. -/
noncomputable def taoCanonicalUniformOddResiduePMF :
    (M : ℕ) → PMF (ZMod (2 ^ M))
  | 0 => PMF.pure 0
  | K + 1 => taoUniformOddResiduePMF K

/-- The total canonical comparison law pushes through the strict decoder to
the ideal finite tuple law, including the honest modulus-one endpoint. -/
theorem taoCanonicalUniformOddResiduePMF_map_decoder (n M : ℕ) :
    (taoCanonicalUniformOddResiduePMF M).map
        (taoProp19ResidueDecoder n M) =
      truncatedValuationTupleGeom2PMF n M := by
  cases M with
  | zero =>
      rw [← geom2PNatListPMF_map_truncateValuationList]
      have hdecoder : taoProp19ResidueDecoder n 0 =
          fun _ : ZMod (2 ^ 0) => (none : TruncatedValuationTuple n 0) := by
        funext r
        exact taoProp19ResidueDecoder_modulus_zero n r
      have htruncate : truncateValuationList n 0 =
          fun _ : List ℕ+ => (none : TruncatedValuationTuple n 0) := by
        funext as
        rw [truncateValuationList_eq_none_iff]
        exact Or.inr (Nat.zero_le _)
      rw [taoCanonicalUniformOddResiduePMF, hdecoder, htruncate,
        show (fun _ : ZMod (2 ^ 0) => (none : TruncatedValuationTuple n 0)) =
            Function.const (ZMod (2 ^ 0)) none by rfl,
        show (fun _ : List ℕ+ => (none : TruncatedValuationTuple n 0)) =
            Function.const (List ℕ+) none by rfl,
        PMF.map_const, PMF.map_const]
  | succ K =>
      exact taoUniformOddResiduePMF_map_decoder n K

/-- Reducing an odd source modulo `2^M` and decoding commutes with taking and
strictly truncating its first `n` Syracuse valuations. -/
theorem taoProp19SourceResidueLaw_map_decoder
    (μ : PMF TaoOddNat) (n M : ℕ) :
    (taoProp19SourceResidueLaw μ M).map
        (taoProp19ResidueDecoder n M) =
      (taoProp19ActualValuationLaw μ n).map
        (truncateValuationList n M) := by
  unfold taoProp19SourceResidueLaw taoProp19ActualValuationLaw
  rw [PMF.map_comp, PMF.map_comp]
  apply congrArg (fun f => μ.map f)
  funext N
  exact taoProp19ResidueDecoder_natCast n M N.1 N.2

theorem taoProp19SourceResidueLaw_map_decoder_modulus_zero
    (μ : PMF TaoOddNat) (n : ℕ) :
    (taoProp19SourceResidueLaw μ 0).map
        (taoProp19ResidueDecoder n 0) =
      (taoProp19ActualValuationLaw μ n).map
        (truncateValuationList n 0) :=
  taoProp19SourceResidueLaw_map_decoder μ n 0

/-- A zero-length actual valuation list is deterministically empty. -/
theorem taoProp19ActualValuationLaw_zero (μ : PMF TaoOddNat) :
    taoProp19ActualValuationLaw μ 0 = geom2PNatListPMF 0 := by
  change μ.map (Function.const TaoOddNat ([] : List ℕ+)) = PMF.pure []
  exact PMF.map_const μ []

end

end Tao
end Erdos1135SecondScale
