/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Prop71CanonicalAssembly
import Erdos1135SecondScale.Tao.Section6.Prop114Assembly

/-!
# Canonical Natural-Exponent Proposition 1.14

This leaf composes the unconditional checked Proposition 1.17 theorem with
the Section 6 implication without importing Section 7 back into the Section 6
facade.  Literal positive-real-exponent fidelity remains a separate adapter.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Unconditional current positive-natural-exponent Proposition 1.14. -/
theorem taoProp114FineScaleMixing :
    TaoProp114FineScaleMixingStatement :=
  taoProp117PrimitivePolynomialDecay.to_prop114

end Tao
end Erdos1135SecondScale
