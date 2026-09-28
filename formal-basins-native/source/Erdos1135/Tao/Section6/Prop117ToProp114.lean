import Erdos1135.Tao.Fourier.DecayStatement
import Erdos1135.Tao.Fourier.MixingStatement
import Erdos1135.Tao.Section6.Corollary63

/-!
# Section 6 Proposition 1.17 To Proposition 1.14 Bridge Surface

This module records the theorem-shaped Section 6 bridge from Tao's primitive
Fourier decay statement and the repaired Corollary 6.3 source-residue endpoint
to the fine-scale mixing statement.  It proves no analytic bridge; the main
declaration is a `Prop` target consumed by a small accessor theorem.
-/

namespace Erdos1135
namespace Tao

/--
Section 6 bridge target from Proposition 1.17 and repaired Corollary 6.3 star
source-residue separation to Proposition 1.14.

This is intentionally a theorem-shaped `Prop` target, not an axiom and not a
proof of the bridge.
-/
def TaoSection6Prop117ToProp114Statement : Prop :=
  TaoProp117PrimitivePolynomialDecayStatement →
    TaoCor63StarSourceResidueSeparationStatement →
      TaoProp114FineScaleMixingStatement

theorem TaoSection6Prop117ToProp114Statement.apply
    (h : TaoSection6Prop117ToProp114Statement)
    (h117 : TaoProp117PrimitivePolynomialDecayStatement)
    (hcor63 : TaoCor63StarSourceResidueSeparationStatement) :
    TaoProp114FineScaleMixingStatement :=
  h h117 hcor63

theorem TaoProp114FineScaleMixingStatement.of_section6
    (hsection6 : TaoSection6Prop117ToProp114Statement)
    (h117 : TaoProp117PrimitivePolynomialDecayStatement)
    (hcor63 : TaoCor63StarSourceResidueSeparationStatement) :
    TaoProp114FineScaleMixingStatement :=
  hsection6.apply h117 hcor63

end Tao
end Erdos1135
