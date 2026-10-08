/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.Affine

/-!
# Odd Syracuse Sources

This dependency-light leaf owns the odd natural source carrier shared by the
deterministic Section 5 event partition and the Proposition 1.9 probability
laws.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Odd natural numbers as the generic Syracuse source type. -/
abbrev TaoOddNat : Type :=
  {N : ℕ // Odd N}

end Tao
end Erdos1135SecondScale
