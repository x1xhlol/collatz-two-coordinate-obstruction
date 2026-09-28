import Erdos1135.Tao.Fourier.Prop71CanonicalAssembly
import Erdos1135.Tao.Section6.Prop114Assembly

/-!
# Canonical Natural-Exponent Proposition 1.14

This leaf composes the unconditional checked Proposition 1.17 theorem with
the Section 6 implication without importing Section 7 back into the Section 6
facade.  Literal positive-real-exponent fidelity remains a separate adapter.
-/

namespace Erdos1135
namespace Tao

/-- Unconditional current positive-natural-exponent Proposition 1.14. -/
theorem taoProp114FineScaleMixing :
    TaoProp114FineScaleMixingStatement :=
  taoProp117PrimitivePolynomialDecay.to_prop114

end Tao
end Erdos1135
