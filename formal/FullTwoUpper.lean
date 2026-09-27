import FullTwoUpperPositive
import FullTwoUpperZero

namespace CollatzResearch.FullTwoUpper

theorem zero_gaps (m : Data) (w : Weak m) : ZeroGaps m := by
  by_cases az : m.za=0
  · exact zero_binary_zero_gaps m w (Or.inl az)
  by_cases bz : m.zb=0
  · exact zero_binary_zero_gaps m w (Or.inr bz)
  exact positive_zero_gaps m w
    (lt_of_le_of_ne w.za (Ne.symm az)) (lt_of_le_of_ne w.zb (Ne.symm bz))

#print axioms zero_gaps

end CollatzResearch.FullTwoUpper
