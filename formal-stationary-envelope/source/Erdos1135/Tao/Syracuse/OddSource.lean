import Erdos1135.Tao.Syracuse.Affine

/-!
# Odd Syracuse Sources

This dependency-light leaf owns the odd natural source carrier shared by the
deterministic Section 5 event partition and the Proposition 1.9 probability
laws.
-/

namespace Erdos1135
namespace Tao

/-- Odd natural numbers as the generic Syracuse source type. -/
abbrev TaoOddNat : Type :=
  {N : ℕ // Odd N}

end Tao
end Erdos1135
