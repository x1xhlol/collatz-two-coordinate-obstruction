import CollatzNaturalAffine
import CollatzReversedCertificate

namespace CollatzResearch.NatAffine

variable {ι : Type*} [Fintype ι]

theorem reversed_first_removal_implies_collatz
    (A B C D E F G : NatAffine ι) (i₀ : ι)
    (hda : (D.comp A).Weak D)
    (hdb : (D.comp B).Weak (D.comp G))
    (hea : (E.comp A).Weak (A.comp E))
    (hfa : (F.comp A).Weak (B.comp E))
    (hga : (G.comp A).Weak (A.comp F))
    (heb : (E.comp B).Weak (B.comp F))
    (hfb : (F.comp B).Weak (A.comp G))
    (hgb : (G.comp B).Weak (B.comp G))
    (hec : (E.comp C).Weak (B.comp C))
    (hfc : (F.comp C).Weak (A.comp (A.comp C)))
    (hgc : (G.comp C).Weak (B.comp (A.comp C)))
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    CollatzConjecture := by
  let c : ReversedCertificate.Data (ι → ℕ) := {
    a := A.eval
    b := B.eval
    e := E.eval
    f := F.eval
    g := G.eval
    readout := fun x => D.eval x i₀
    initial := C.offset
    a_monotone := A.eval_monotone
    b_monotone := B.eval_monotone
    readout_monotone := fun _ _ h => D.eval_monotone h i₀
    ea := fun x => by simpa only [eval_comp] using eval_weak hea x
    fa := fun x => by simpa only [eval_comp] using eval_weak hfa x
    ga := fun x => by simpa only [eval_comp] using eval_weak hga x
    eb := fun x => by simpa only [eval_comp] using eval_weak heb x
    fb := fun x => by simpa only [eval_comp] using eval_weak hfb x
    gb := fun x => by simpa only [eval_comp] using eval_weak hgb x
    ec := hec.2
    fc := hfc.2
    gc := hgc.2
  }
  apply ReversedCertificate.first_eligible_root_implies_collatz c
  · intro x
    simpa only [eval_comp] using eval_weak hda x i₀
  · intro x
    simpa only [eval_comp] using eval_weak hdb x i₀
  · rcases hstrict with hs | hs
    · left
      intro x
      simpa only [eval_comp] using eval_strict_at hda i₀ hs x
    · right
      intro x
      simpa only [eval_comp] using eval_strict_at hdb i₀ hs x

#print axioms reversed_first_removal_implies_collatz

end CollatzResearch.NatAffine
