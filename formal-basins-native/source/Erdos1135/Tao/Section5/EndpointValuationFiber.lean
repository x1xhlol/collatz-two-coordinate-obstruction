import Erdos1135.Tao.Probability.Geom2TerminalMoment
import Erdos1135.Tao.Section5.PassLostWindow
import Erdos1135.Tao.Section5.PayloadFreeCoefficient
import Erdos1135.Tao.Syracuse.FirstPassageInterval
import Erdos1135.Tao.Syracuse.ValuationCylinderCRT

/-!
# Section 5 Endpoint Valuation Fibers

This leaf partitions the finite target `EPrime` by its actual length-`m0`
valuation lists and coefficient residues.  It then attaches the checked
first-passage interval and CRT class to every fixed fiber.  Reciprocal
progression estimates remain in later leaves.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- An endpoint attached to its membership in the finite target `EPrime`. -/
abbrev TaoSection5Endpoint (B : ℕ) (E : Set ℕ) :=
  {M : ℕ // M ∈ taoSection5EPrime B E}

/-- Oddness carried by an attached endpoint. -/
theorem taoSection5Endpoint_odd
    {B : ℕ} {E : Set ℕ} (M : TaoSection5Endpoint B E) :
    Odd M.1 :=
  (mem_taoSection5EPrime_iff.mp M.2).2.2.1

/-- The endpoint's own chronological valuation list, of length `m0`. -/
def taoSection5EndpointValuation
    {B : ℕ} {E : Set ℕ} (M : TaoSection5Endpoint B E) : List ℕ+ :=
  syracuseValuationPNatList (taoSection5M0 B) M.1
    (taoSection5Endpoint_odd M)

theorem taoSection5EndpointValuation_length
    {B : ℕ} {E : Set ℕ} (M : TaoSection5Endpoint B E) :
    (taoSection5EndpointValuation M).length = taoSection5M0 B := by
  exact syracuseValuationPNatList_length _ _ _

/-- Finite image of actual endpoint valuation lists. -/
def taoSection5EndpointValuationCarrier
    (B : ℕ) (E : Set ℕ) : Finset (List ℕ+) := by
  classical
  exact (Finset.univ : Finset (TaoSection5Endpoint B E)).image
    (fun M => taoSection5EndpointValuation M)

theorem mem_taoSection5EndpointValuationCarrier_iff
    {B : ℕ} {E : Set ℕ} {bs : List ℕ+} :
    bs ∈ taoSection5EndpointValuationCarrier B E ↔
      ∃ M : TaoSection5Endpoint B E,
        taoSection5EndpointValuation M = bs := by
  classical
  simp [taoSection5EndpointValuationCarrier, eq_comm]

theorem length_eq_m0_of_mem_taoSection5EndpointValuationCarrier
    {B : ℕ} {E : Set ℕ} {bs : List ℕ+}
    (hbs : bs ∈ taoSection5EndpointValuationCarrier B E) :
    bs.length = taoSection5M0 B := by
  rw [mem_taoSection5EndpointValuationCarrier_iff] at hbs
  rcases hbs with ⟨M, rfl⟩
  exact taoSection5EndpointValuation_length M

/-- Fixed valuation-list and `3^q` residue fiber on attached endpoints. -/
def taoSection5EndpointValuationFiber
    (B : ℕ) (E : Set ℕ) (q : ℕ) (X : ZMod (3 ^ q))
    (bs : List ℕ+) : Finset (TaoSection5Endpoint B E) := by
  classical
  exact Finset.univ.filter fun M =>
    taoSection5EndpointValuation M = bs ∧
      (M.1 : ZMod (3 ^ q)) = X

theorem mem_taoSection5EndpointValuationFiber_iff
    {B : ℕ} {E : Set ℕ} {q : ℕ} {X : ZMod (3 ^ q)}
    {bs : List ℕ+} {M : TaoSection5Endpoint B E} :
    M ∈ taoSection5EndpointValuationFiber B E q X bs ↔
      taoSection5EndpointValuation M = bs ∧
        (M.1 : ZMod (3 ^ q)) = X := by
  classical
  simp [taoSection5EndpointValuationFiber]

theorem mem_taoSection5EndpointValuationCarrier_of_mem_fiber
    {B : ℕ} {E : Set ℕ} {q : ℕ} {X : ZMod (3 ^ q)}
    {bs : List ℕ+} {M : TaoSection5Endpoint B E}
    (hM : M ∈ taoSection5EndpointValuationFiber B E q X bs) :
    bs ∈ taoSection5EndpointValuationCarrier B E := by
  rw [mem_taoSection5EndpointValuationCarrier_iff]
  exact ⟨M, (mem_taoSection5EndpointValuationFiber_iff.mp hM).1⟩

/-- Distinct valuation tuples have disjoint attached endpoint fibers. -/
theorem taoSection5EndpointValuationFiber_disjoint
    {B : ℕ} {E : Set ℕ} {q : ℕ} {X : ZMod (3 ^ q)}
    {bs cs : List ℕ+} (hne : bs ≠ cs) :
    Disjoint
      (taoSection5EndpointValuationFiber B E q X bs)
      (taoSection5EndpointValuationFiber B E q X cs) := by
  classical
  rw [Finset.disjoint_left]
  intro M hMbs hMcs
  have hbs := (mem_taoSection5EndpointValuationFiber_iff.mp hMbs).1
  have hcs := (mem_taoSection5EndpointValuationFiber_iff.mp hMcs).1
  exact hne (hbs.symm.trans hcs)

/-- Finite residue-restricted endpoint sums reindex exactly over valuation
fibers in the finite image carrier. -/
theorem sum_taoSection5EndpointValuationFiber
    {R : Type*} [AddCommMonoid R]
    {B : ℕ} {E : Set ℕ} (q : ℕ) (X : ZMod (3 ^ q))
    (f : TaoSection5Endpoint B E → R) :
    (∑ M : TaoSection5Endpoint B E
        with (M.1 : ZMod (3 ^ q)) = X, f M) =
      ∑ bs ∈ taoSection5EndpointValuationCarrier B E,
        ∑ M ∈ taoSection5EndpointValuationFiber B E q X bs, f M := by
  classical
  let S : Finset (TaoSection5Endpoint B E) :=
    Finset.univ.filter fun M => (M.1 : ZMod (3 ^ q)) = X
  let T : Finset (List ℕ+) := taoSection5EndpointValuationCarrier B E
  let g : TaoSection5Endpoint B E → List ℕ+ :=
    taoSection5EndpointValuation
  have hmaps : ∀ M ∈ S, g M ∈ T := by
    intro M _hM
    exact Finset.mem_image.mpr ⟨M, by simp, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps f
  symm
  calc
    (∑ bs ∈ T, ∑ M ∈ taoSection5EndpointValuationFiber B E q X bs, f M) =
        ∑ bs ∈ T, ∑ M ∈ S with g M = bs, f M := by
      apply Finset.sum_congr rfl
      intro bs _hbs
      apply Finset.sum_congr
      · ext M
        simp [S, g, taoSection5EndpointValuationFiber, and_comm]
      · intro M _hM
        rfl
    _ = ∑ M ∈ S, f M := hfiber
    _ = ∑ M : TaoSection5Endpoint B E
        with (M.1 : ZMod (3 ^ q)) = X, f M := by
      rfl

/-- The endpoint valuation splits into its predecessor prefix and genuine
last coordinate under the checked positivity of `m0`. -/
theorem taoSection5EndpointValuation_eq_dropLast_append_terminal
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    (M : TaoSection5Endpoint B E) :
    taoSection5EndpointValuation M =
      syracuseValuationPNatList (taoSection5M0 B - 1) M.1
          (taoSection5Endpoint_odd M) ++
        [syracuseTerminalExponentPNat (taoSection5M0 B - 1) M.1
          (taoSection5Endpoint_odd M)] := by
  have hm : taoSection5M0 B - 1 + 1 = taoSection5M0 B := by
    exact Nat.sub_add_cancel facts.one_le_m0
  unfold taoSection5EndpointValuation
  rw [← hm]
  exact syracuseValuationPNatList_succ_eq_append_terminal _ _ _

theorem taoSection5EndpointValuation_dropLast
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    (M : TaoSection5Endpoint B E) :
    (taoSection5EndpointValuation M).dropLast =
      syracuseValuationPNatList (taoSection5M0 B - 1) M.1
        (taoSection5Endpoint_odd M) := by
  rw [taoSection5EndpointValuation_eq_dropLast_append_terminal facts]
  simp

theorem taoSection5EndpointValuation_terminalValue
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    (M : TaoSection5Endpoint B E) :
    geom2PNatListTerminalValue (taoSection5EndpointValuation M) =
      (syracuseTerminalExponentPNat (taoSection5M0 B - 1) M.1
        (taoSection5Endpoint_odd M) : ℕ) := by
  rw [taoSection5EndpointValuation_eq_dropLast_append_terminal facts]
  simp [geom2PNatListTerminalValue]

theorem taoSection5EndpointValuation_weight_dropLast_add_terminalValue
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    (M : TaoSection5Endpoint B E) :
    taoTupleWeight (taoSection5EndpointValuation M) =
      taoTupleWeight (taoSection5EndpointValuation M).dropLast +
        geom2PNatListTerminalValue (taoSection5EndpointValuation M) := by
  rw [taoSection5EndpointValuation_eq_dropLast_append_terminal facts,
    taoTupleWeight_append_trajectory]
  simp [taoTupleWeight, geom2PNatListTerminalValue]

/-- Fixed-fiber form of the terminal append identity, stated on the supplied
tuple `bs`. -/
theorem taoSection5EndpointFiber_eq_prefix_append_terminal
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    {M : TaoSection5Endpoint B E}
    (hM : M ∈ taoSection5EndpointValuationFiber B E q X bs) :
    bs = syracuseValuationPNatList (taoSection5M0 B - 1) M.1
          (taoSection5Endpoint_odd M) ++
        [syracuseTerminalExponentPNat (taoSection5M0 B - 1) M.1
          (taoSection5Endpoint_odd M)] := by
  have hval := (mem_taoSection5EndpointValuationFiber_iff.mp hM).1
  exact hval.symm.trans
    (taoSection5EndpointValuation_eq_dropLast_append_terminal facts M)

theorem taoSection5EndpointFiber_dropLast
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    {M : TaoSection5Endpoint B E}
    (hM : M ∈ taoSection5EndpointValuationFiber B E q X bs) :
    bs.dropLast =
      syracuseValuationPNatList (taoSection5M0 B - 1) M.1
        (taoSection5Endpoint_odd M) := by
  rw [taoSection5EndpointFiber_eq_prefix_append_terminal facts hM]
  simp

theorem taoSection5EndpointFiber_terminalValue
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    {M : TaoSection5Endpoint B E}
    (hM : M ∈ taoSection5EndpointValuationFiber B E q X bs) :
    geom2PNatListTerminalValue bs =
      (syracuseTerminalExponentPNat (taoSection5M0 B - 1) M.1
        (taoSection5Endpoint_odd M) : ℕ) := by
  rw [taoSection5EndpointFiber_eq_prefix_append_terminal facts hM]
  simp [geom2PNatListTerminalValue]

theorem taoSection5EndpointFiber_weight_dropLast_add_terminalValue
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    {M : TaoSection5Endpoint B E}
    (hM : M ∈ taoSection5EndpointValuationFiber B E q X bs) :
    taoTupleWeight bs =
      taoTupleWeight bs.dropLast + geom2PNatListTerminalValue bs := by
  have hval := (mem_taoSection5EndpointValuationFiber_iff.mp hM).1
  rw [← hval]
  exact taoSection5EndpointValuation_weight_dropLast_add_terminalValue facts M

/-- Tuple-facing lower endpoint for one endpoint valuation list. -/
def taoSection5EndpointLower (B : ℕ) (bs : List ℕ+) : ℕ :=
  syracuseFirstPassageLowerEndpoint B (taoSection5M0 B - 1)
    (taoTupleWeight bs.dropLast)

/-- Tuple-facing weak upper endpoint for one endpoint valuation list. -/
def taoSection5EndpointUpper (B : ℕ) (bs : List ℕ+) : ℕ :=
  syracuseFirstPassageUpperEndpoint B (taoSection5M0 B - 1)
    (taoTupleWeight bs)

/-- Tuple-facing high-weight lower endpoint. -/
def taoSection5EndpointHighLower (B : ℕ) (bs : List ℕ+) : ℕ :=
  max (taoSection5EndpointLower B bs)
    (syracuseFirstPassageHighLowerEndpoint (taoSection5M0 B - 1)
      (taoTupleWeight bs))

private theorem taoSection5Endpoint_room
    {B : ℕ} (facts : TaoSection5PassLostWindowFacts B) :
    2 * 3 ^ (taoSection5M0 B - 1) ≤ B := by
  exact_mod_cast facts.preterminal_offset_room

private theorem taoSection5Endpoint_firstHit
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    (M : TaoSection5Endpoint B E) :
    syracuseFirstHitAtMost B M.1 (taoSection5M0 B - 1 + 1) := by
  have hfirst := (mem_taoSection5EPrime_iff.mp M.2).2.2.2.1
  have hm : taoSection5M0 B - 1 + 1 = taoSection5M0 B :=
    Nat.sub_add_cancel facts.one_le_m0
  simpa only [hm] using hfirst

theorem taoSection5Endpoint_lower_le
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    (M : TaoSection5Endpoint B E) :
    taoSection5EndpointLower B (taoSection5EndpointValuation M) ≤ M.1 := by
  rw [taoSection5EndpointLower,
    taoSection5EndpointValuation_dropLast facts M]
  exact syracuseFirstHitAtMost_lowerEndpoint_le
    (taoSection5Endpoint_odd M) (taoSection5Endpoint_room facts)
      (taoSection5Endpoint_firstHit facts M)

theorem taoSection5Endpoint_le_upper
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    (M : TaoSection5Endpoint B E) :
    M.1 ≤ taoSection5EndpointUpper B (taoSection5EndpointValuation M) := by
  unfold taoSection5EndpointUpper
  have h := syracuseFirstHitAtMost_le_upperEndpoint
    (taoSection5Endpoint_odd M) (taoSection5Endpoint_firstHit facts M)
  have hm : taoSection5M0 B - 1 + 1 = taoSection5M0 B :=
    Nat.sub_add_cancel facts.one_le_m0
  simpa only [taoSection5EndpointValuation, hm] using h

theorem taoSection5Endpoint_highLower_le
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    (M : TaoSection5Endpoint B E) :
    taoSection5EndpointHighLower B (taoSection5EndpointValuation M) ≤ M.1 := by
  unfold taoSection5EndpointHighLower
  rw [taoSection5EndpointLower,
    taoSection5EndpointValuation_dropLast facts M]
  have h := syracuseFirstHitAtMost_maxLowerEndpoint_le
    (taoSection5Endpoint_odd M) (taoSection5Endpoint_room facts)
      (taoSection5Endpoint_firstHit facts M)
  have hm : taoSection5M0 B - 1 + 1 = taoSection5M0 B :=
    Nat.sub_add_cancel facts.one_le_m0
  simpa only [taoSection5EndpointValuation, hm] using h

theorem taoSection5EndpointFiber_mem_interval
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    {M : TaoSection5Endpoint B E}
    (hM : M ∈ taoSection5EndpointValuationFiber B E q X bs) :
    M.1 ∈ Finset.Icc
      (taoSection5EndpointLower B bs) (taoSection5EndpointUpper B bs) := by
  have hval := (mem_taoSection5EndpointValuationFiber_iff.mp hM).1
  rw [← hval]
  exact Finset.mem_Icc.mpr
    ⟨taoSection5Endpoint_lower_le facts M,
      taoSection5Endpoint_le_upper facts M⟩

theorem taoSection5EndpointFiber_mem_highInterval
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    {M : TaoSection5Endpoint B E}
    (hM : M ∈ taoSection5EndpointValuationFiber B E q X bs) :
    M.1 ∈ Finset.Icc
      (taoSection5EndpointHighLower B bs) (taoSection5EndpointUpper B bs) := by
  have hval := (mem_taoSection5EndpointValuationFiber_iff.mp hM).1
  rw [← hval]
  exact Finset.mem_Icc.mpr
    ⟨taoSection5Endpoint_highLower_le facts M,
      taoSection5Endpoint_le_upper facts M⟩

theorem taoSection5EndpointFiber_nonempty_lower_le_upper
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hne : (taoSection5EndpointValuationFiber B E q X bs).Nonempty) :
    taoSection5EndpointLower B bs ≤ taoSection5EndpointUpper B bs := by
  rcases hne with ⟨M, hM⟩
  have hi := Finset.mem_Icc.mp
    (taoSection5EndpointFiber_mem_interval facts hM)
  exact hi.1.trans hi.2

theorem taoSection5EndpointFiber_eq_empty_of_upper_lt_lower
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hgap : taoSection5EndpointUpper B bs < taoSection5EndpointLower B bs) :
    taoSection5EndpointValuationFiber B E q X bs = ∅ := by
  classical
  ext M
  constructor
  · intro hM
    have hi := Finset.mem_Icc.mp
      (taoSection5EndpointFiber_mem_interval facts hM)
    exfalso
    omega
  · intro hM
    simpa using hM

theorem taoSection5EndpointFiber_nonempty_highLower_le_upper
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hne : (taoSection5EndpointValuationFiber B E q X bs).Nonempty) :
    taoSection5EndpointHighLower B bs ≤ taoSection5EndpointUpper B bs := by
  rcases hne with ⟨M, hM⟩
  have hi := Finset.mem_Icc.mp
    (taoSection5EndpointFiber_mem_highInterval facts hM)
  exact hi.1.trans hi.2

theorem taoSection5EndpointFiber_eq_empty_of_upper_lt_highLower
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hgap : taoSection5EndpointUpper B bs < taoSection5EndpointHighLower B bs) :
    taoSection5EndpointValuationFiber B E q X bs = ∅ := by
  classical
  ext M
  constructor
  · intro hM
    have hi := Finset.mem_Icc.mp
      (taoSection5EndpointFiber_mem_highInterval facts hM)
    exfalso
    omega
  · intro hM
    simpa using hM

/-- Exact full-product CRT class for every member of a fixed endpoint
valuation/residue fiber. -/
theorem taoSection5EndpointFiber_modEq_crt
    {B : ℕ} {E : Set ℕ} {q : ℕ} {X : ZMod (3 ^ q)}
    {bs : List ℕ+} {M : TaoSection5Endpoint B E}
    (hM : M ∈ taoSection5EndpointValuationFiber B E q X bs) :
    M.1 ≡ syracuseValuationCylinderCRTResidue bs q X
      [MOD 2 ^ (taoTupleWeight bs + 1) * 3 ^ q] := by
  rcases mem_taoSection5EndpointValuationFiber_iff.mp hM with
    ⟨hval, hresidue⟩
  have hlength : bs.length = taoSection5M0 B := by
    rw [← hval]
    exact taoSection5EndpointValuation_length M
  have hval' :
      syracuseValuationPNatList bs.length M.1
          (taoSection5Endpoint_odd M) = bs := by
    rw [hlength]
    exact hval
  exact
    (syracuseValuationPNatList_eq_and_natCast_eq_iff_modEq_crt
      bs q X (taoSection5Endpoint_odd M)).mp ⟨hval', hresidue⟩

/-- On attached endpoints, a carrier tuple's exact valuation/residue fiber is
equivalent to its full-product CRT class. -/
theorem mem_taoSection5EndpointValuationFiber_iff_modEq_crt
    {B : ℕ} {E : Set ℕ} {q : ℕ} {X : ZMod (3 ^ q)}
    {bs : List ℕ+}
    (hbs : bs ∈ taoSection5EndpointValuationCarrier B E)
    (M : TaoSection5Endpoint B E) :
    M ∈ taoSection5EndpointValuationFiber B E q X bs ↔
      M.1 ≡ syracuseValuationCylinderCRTResidue bs q X
        [MOD 2 ^ (taoTupleWeight bs + 1) * 3 ^ q] := by
  constructor
  · exact taoSection5EndpointFiber_modEq_crt
  · intro hcrt
    have hlength : bs.length = taoSection5M0 B :=
      length_eq_m0_of_mem_taoSection5EndpointValuationCarrier hbs
    rcases
        (syracuseValuationPNatList_eq_and_natCast_eq_iff_modEq_crt
          bs q X (taoSection5Endpoint_odd M)).mpr hcrt with
      ⟨hval, hresidue⟩
    rw [mem_taoSection5EndpointValuationFiber_iff]
    constructor
    · unfold taoSection5EndpointValuation
      rw [← hlength]
      exact hval
    · exact hresidue

@[simp]
theorem mem_taoSection5EndpointValuationFiber_zero_iff
    {B : ℕ} {E : Set ℕ} {bs : List ℕ+}
    {M : TaoSection5Endpoint B E} :
    M ∈ taoSection5EndpointValuationFiber B E 0 0 bs ↔
      taoSection5EndpointValuation M = bs := by
  rw [mem_taoSection5EndpointValuationFiber_iff]
  constructor
  · exact fun h => h.1
  · intro hval
    refine ⟨hval, ?_⟩
    change (M.1 : ZMod 1) = 0
    exact Subsingleton.elim _ _

/-- The payload-free coefficient is exactly the sum of reciprocal masses over
the finite endpoint valuation fibers. -/
theorem taoSection5PayloadFreeCoefficient_eq_sum_endpointValuationFiber
    (B : ℕ) (E : Set ℕ) (q : ℕ) (X : ZMod (3 ^ q)) :
    taoSection5PayloadFreeCoefficient q (taoSection5EPrime B E) X =
      ((3 ^ q : ℕ) : ℝ) *
        ∑ bs ∈ taoSection5EndpointValuationCarrier B E,
          ∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
            1 / (M.1 : ℝ) := by
  classical
  unfold taoSection5PayloadFreeCoefficient
  rw [← sum_taoSection5EndpointValuationFiber q X
    (fun M : TaoSection5Endpoint B E => 1 / (M.1 : ℝ))]
  congr 1
  apply Finset.sum_bij
    (fun M hM =>
      (⟨M, (Finset.mem_filter.mp hM).1⟩ : TaoSection5Endpoint B E))
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hM).2
  · intro M₁ _hM₁ M₂ _hM₂ hEq
    exact congrArg Subtype.val hEq
  · intro M hM
    refine ⟨M.1, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨M.2, (Finset.mem_filter.mp hM).2⟩
    · apply Subtype.ext
      rfl
  · intro M _hM
    rfl

@[simp]
theorem taoSection5EndpointValuationCarrier_empty (B : ℕ) :
    taoSection5EndpointValuationCarrier B (∅ : Set ℕ) = ∅ := by
  classical
  ext bs
  simp [mem_taoSection5EndpointValuationCarrier_iff, TaoSection5Endpoint,
    taoSection5EPrime_empty]

@[simp]
theorem taoSection5EndpointValuationFiber_empty
    (B q : ℕ) (X : ZMod (3 ^ q)) (bs : List ℕ+) :
    taoSection5EndpointValuationFiber B (∅ : Set ℕ) q X bs = ∅ := by
  classical
  ext M
  constructor
  · intro _hM
    have hfalse : M.1 ∈ (∅ : Finset ℕ) := by
      rw [← taoSection5EPrime_empty B]
      exact M.2
    exfalso
    simpa using hfalse
  · intro hM
    simpa using hM

@[simp]
theorem taoSection5PayloadFreeCoefficient_EPrime_empty
    (B q : ℕ) (X : ZMod (3 ^ q)) :
    taoSection5PayloadFreeCoefficient q
      (taoSection5EPrime B (∅ : Set ℕ)) X = 0 := by
  rw [taoSection5EPrime_empty]
  simp [taoSection5PayloadFreeCoefficient]

end

end Tao
end Erdos1135
