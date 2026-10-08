import NaturalToLogarithmicSourceMean
import WeightedSourcePeriodicMean

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic CollatzCanonical.NativeTao

theorem actual_firstHitWeight_logarithmicSourceMean (N : ℕ) :
    Tendsto (logarithmicSourceMean (firstHitWeight N)) atTop
      (𝓝 (actualFirstHitDensity N)) :=
  logarithmicSourceMean_of_sourceMean (firstHitWeight N)
    (firstHitWeight_abs_le_one N) (actual_firstHitWeight_sourceMean N)

theorem actual_firstHitWeight_oddUnit_logarithmicSourceMean (N : ℕ) :
    Tendsto (logarithmicSourceMean (fun q => firstHitWeight N q * oddUnitMask q)) atTop
      (𝓝 (actualFirstHitDensity N / 3)) :=
  logarithmicSourceMean_of_sourceMean (fun q => firstHitWeight N q * oddUnitMask q)
    (weighted_oddUnit_abs_le_one N) (actual_firstHitWeight_oddUnit_sourceMean N)

#print axioms actual_firstHitWeight_logarithmicSourceMean
#print axioms actual_firstHitWeight_oddUnit_logarithmicSourceMean

end CollatzCanonical.PeriodicCensusFloor
