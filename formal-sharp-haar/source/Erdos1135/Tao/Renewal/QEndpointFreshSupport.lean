import Erdos1135.Tao.Renewal.QEndpointFreshDomain
import Erdos1135.Tao.Renewal.HoldFirstPassagePMF

/-!
# Canonical Endpoint/Fresh Strict Support

This leaf transports positive vertical-increment support from the iid Hold law
to every nonzero atom of the canonical endpoint/fresh carrier.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Every fresh increment on a nonzero endpoint/fresh atom raises the vertical
coordinate by at least one. -/
theorem lemma79CanonicalEndpointFreshPMF_fresh_all_l_ge_one
    {J : ℕ} {entry : TaoSection7RenewalPoint} {gap : ℕ}
    {endpoint : ℕ × ℤ} {fresh : List TaoSection7RenewalPoint}
    (hne :
      lemma79CanonicalEndpointFreshPMF J entry gap (endpoint, fresh) ≠ 0) :
    taoSection7AllHoldIncrementsLGeOne fresh := by
  have hprod :
      lemma77CanonicalFirstPassageEndpointPMF entry gap endpoint *
          taoSection7HoldListPMF J fresh ≠ 0 := by
    rw [← lemma79CanonicalEndpointFreshPMF_apply]
    exact hne
  exact taoSection7HoldListPMF_ne_zero_all_l_ge_one
    (right_ne_zero_of_mul hprod)

/-- The strict support fact remains valid on every prefix actually consumed
through a horizon `P ≤ J`. -/
theorem lemma79CanonicalEndpointFreshPMF_used_fresh_support
    {P J : ℕ} {entry : TaoSection7RenewalPoint} {gap : ℕ}
    {endpoint : ℕ × ℤ} {fresh : List TaoSection7RenewalPoint}
    (hPJ : P ≤ J)
    (hne :
      lemma79CanonicalEndpointFreshPMF J entry gap (endpoint, fresh) ≠ 0) :
    P ≤ fresh.length ∧
      taoSection7AllHoldIncrementsLGeOne (fresh.take P) := by
  have hlength :=
    (lemma79CanonicalEndpointFreshPMF_nonzero_support hne).2.2
  refine ⟨by omega, ?_⟩
  intro h hh
  exact lemma79CanonicalEndpointFreshPMF_fresh_all_l_ge_one hne h
    (List.mem_of_mem_take hh)

/-- A supported canonical endpoint starts strictly above its first-passage
gap, so every later fresh-prefix point lies strictly above the old corner
when the gap is aligned with that corner. -/
theorem lemma79CanonicalEndpointFreshPMF_cornerL_lt_pointAt
    {J p fpGap : ℕ}
    {entry : TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    (hne :
      lemma79CanonicalEndpointFreshPMF J entry fpGap atom ≠ 0)
    (hpJ : p ≤ J)
    (hgap : old.cornerL - entry.l = (fpGap : ℤ)) :
    old.cornerL < (lemma79EndpointFreshPointAt entry atom p).l := by
  have hsupp :=
    lemma79CanonicalEndpointFreshPMF_nonzero_support hne
  have hendpoint : (fpGap : ℤ) < atom.1.2 := hsupp.2.1
  have hpLen : p ≤ atom.2.length := by
    rw [hsupp.2.2]
    exact hpJ
  have hall : taoSection7AllHoldIncrementsLGeOne atom.2 :=
    lemma79CanonicalEndpointFreshPMF_fresh_all_l_ge_one hne
  have hgrowth :=
    taoSection7RenewalPathPoint_l_growth_ge_steps
      (lemma79EndpointFreshOrigin entry atom) atom.2 p hpLen hall
  have horigin :
      old.cornerL < (lemma79EndpointFreshOrigin entry atom).l := by
    simp only [lemma79EndpointFreshOrigin,
      lemma77RenewalPointOfRelativeEndpoint_l]
    omega
  change old.cornerL <
    (taoSection7RenewalPathPoint
      (lemma79EndpointFreshOrigin entry atom) atom.2 p).l
  omega

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
