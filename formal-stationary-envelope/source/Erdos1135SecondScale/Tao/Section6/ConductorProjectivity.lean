/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Section7SourceLaw
import Erdos1135SecondScale.Tao.Section6.ModulusProjection

/-!
# Section 6 Syracuse Projectivity

The iid positive Geom(2) list law has the expected prefix marginal.  Together
with deterministic offset projection, this gives the cross-level projective
law for `syracPMF`.  The later conductor DFT identity is intentionally left to
a separate Fourier leaf.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- A length `r + L` iid positive Geom(2) list has the length-`r` law as its
first-`r` marginal. -/
theorem geom2PNatListPMF_map_take_eq (r L : ℕ) :
    (geom2PNatListPMF (r + L)).map (fun as => as.take r) =
      geom2PNatListPMF r := by
  induction r with
  | zero =>
      rw [Nat.zero_add]
      change PMF.map (fun as : List ℕ+ => as.take 0)
          (geom2PNatListPMF L) = PMF.pure []
      convert PMF.map_const (geom2PNatListPMF L) ([] : List ℕ+) using 1
  | succ r ih =>
      rw [Nat.succ_add]
      change PMF.map (fun as : List ℕ+ => as.take (r + 1))
          (geom2PNat.bind fun a =>
            (geom2PNatListPMF (r + L)).map fun as => a :: as) =
        geom2PNat.bind fun a =>
          (geom2PNatListPMF r).map fun as => a :: as
      rw [PMF.map_bind]
      congr
      funext a
      calc
        PMF.map (fun as : List ℕ+ => as.take (r + 1))
            (PMF.map (fun as : List ℕ+ => a :: as)
              (geom2PNatListPMF (r + L))) =
          PMF.map
              ((fun as : List ℕ+ => as.take (r + 1)) ∘
                (fun as : List ℕ+ => a :: as))
              (geom2PNatListPMF (r + L)) := by
            rw [PMF.map_comp]
        _ = PMF.map (fun as : List ℕ+ => a :: as.take r)
              (geom2PNatListPMF (r + L)) := by
            apply congrArg (fun f => PMF.map f (geom2PNatListPMF (r + L)))
            funext as
            rw [Function.comp_apply]
            rw [List.take_cons (Nat.succ_pos r)]
            simp
        _ = PMF.map ((fun as : List ℕ+ => a :: as) ∘
              (fun as : List ℕ+ => as.take r))
              (geom2PNatListPMF (r + L)) := rfl
        _ = PMF.map (fun as : List ℕ+ => a :: as)
              (PMF.map (fun as : List ℕ+ => as.take r)
                (geom2PNatListPMF (r + L))) := by
            rw [← PMF.map_comp]
        _ = PMF.map (fun as : List ℕ+ => a :: as)
              (geom2PNatListPMF r) := by
            rw [ih]

/-- Splitting a length-`K+N` iid positive Geom(2) list after its first `K`
valuations gives the independent length-`K` head and length-`N` tail laws, in
the direct source order. -/
theorem geom2PNatListPMF_map_take_drop_eq
    (K N : ℕ) :
    (geom2PNatListPMF (K + N)).map
        (fun full => (full.take K, full.drop K)) =
      (geom2PNatListPMF K).bind fun pre =>
        (geom2PNatListPMF N).map fun future => (pre, future) := by
  induction K with
  | zero =>
      rw [Nat.zero_add]
      change
        (geom2PNatListPMF N).map
            (fun full => (full.take 0, full.drop 0)) =
          (PMF.pure []).bind fun pre =>
            (geom2PNatListPMF N).map fun future => (pre, future)
      rw [PMF.pure_bind]
      apply congrArg (fun f => (geom2PNatListPMF N).map f)
      funext full
      simp
  | succ K ih =>
      rw [Nat.succ_add]
      change
        (geom2PNat.bind fun h =>
            (geom2PNatListPMF (K + N)).map fun hs => h :: hs).map
            (fun full => (full.take (K + 1), full.drop (K + 1))) =
          (geom2PNat.bind fun h =>
            (geom2PNatListPMF K).map fun hs => h :: hs).bind fun pre =>
              (geom2PNatListPMF N).map fun future => (pre, future)
      rw [PMF.map_bind, PMF.bind_bind]
      congr
      funext h
      calc
        ((geom2PNatListPMF (K + N)).map fun hs => h :: hs).map
            (fun full => (full.take (K + 1), full.drop (K + 1))) =
            (geom2PNatListPMF (K + N)).map
              (fun hs => (h :: hs.take K, hs.drop K)) := by
                rw [PMF.map_comp]
                apply congrArg
                  (fun f => (geom2PNatListPMF (K + N)).map f)
                funext hs
                simp [Function.comp_apply]
        _ = ((geom2PNatListPMF (K + N)).map
              (fun hs => (hs.take K, hs.drop K))).map
              (fun pair => (h :: pair.1, pair.2)) := by
                rw [PMF.map_comp]
                apply congrArg
                  (fun f => (geom2PNatListPMF (K + N)).map f)
                funext hs
                rfl
        _ = ((geom2PNatListPMF K).bind fun pre =>
              (geom2PNatListPMF N).map fun future =>
                (pre, future)).map
              (fun pair => (h :: pair.1, pair.2)) := by
                rw [ih]
        _ = (geom2PNatListPMF K).bind fun pre =>
              (geom2PNatListPMF N).map fun future =>
                (h :: pre, future) := by
                rw [PMF.map_bind]
                congr
                funext pre
                rw [PMF.map_comp]
                apply congrArg
                  (fun f => (geom2PNatListPMF N).map f)
                funext future
                rfl
        _ = ((geom2PNatListPMF K).map fun pre => h :: pre).bind
              (fun pre =>
                (geom2PNatListPMF N).map fun future =>
                  (pre, future)) := by
                rw [PMF.bind_map]
                rfl

/-- The zero-head split leaves the entire iid list in the future coordinate. -/
theorem geom2PNatListPMF_map_take_drop_eq_zero_left
    (N : ℕ) :
    (geom2PNatListPMF N).map
        (fun full => (full.take 0, full.drop 0)) =
      (geom2PNatListPMF N).map
        (fun future => (([] : List ℕ+), future)) := by
  simp

/-- Splitting the empty iid source produces the empty head-tail pair. -/
theorem geom2PNatListPMF_map_take_drop_eq_zero_zero :
    (geom2PNatListPMF 0).map
        (fun full => (full.take 0, full.drop 0)) =
      PMF.pure (([] : List ℕ+), ([] : List ℕ+)) := by
  simp [geom2PNatListPMF, PMF.pure_map]

/-- The zero-future split leaves the entire iid list in the head coordinate. -/
theorem geom2PNatListPMF_map_take_drop_eq_zero_right
    (K : ℕ) :
    (geom2PNatListPMF K).map
        (fun full => (full.take K, full.drop K)) =
      (geom2PNatListPMF K).map
        (fun head => (head, ([] : List ℕ+))) := by
  simpa only [Nat.add_zero, geom2PNatListPMF, PMF.pure_map] using
    geom2PNatListPMF_map_take_drop_eq K 0

/-- The two-variable iid law specializes to one-variable head and tail laws. -/
theorem geom2PNatListPMF_map_take_drop_eq_one_one :
    (geom2PNatListPMF 2).map
        (fun full => (full.take 1, full.drop 1)) =
      (geom2PNatListPMF 1).bind fun head =>
        (geom2PNatListPMF 1).map fun tail => (head, tail) := by
  simpa using geom2PNatListPMF_map_take_drop_eq 1 1

/-- The underlying two-variable list split preserves direct source order. -/
theorem geom2PNatListSplit_one_one_direct (a b : ℕ+) :
    (fun full : List ℕ+ => (full.take 1, full.drop 1)) [a, b] =
      ([a], [b]) := by
  rfl

theorem geom2PNatListPMF_map_take_eq_of_le
    {r T : ℕ} (h : r ≤ T) :
    (geom2PNatListPMF T).map (fun as => as.take r) =
      geom2PNatListPMF r := by
  simpa [Nat.add_sub_of_le h] using
    (geom2PNatListPMF_map_take_eq r (T - r))

/-- The Syracuse offset law is projective under reduction between powers of
three. -/
theorem syracPMF_map_taoZModThreeProjection_eq_of_le
    {r T : ℕ} (h : r ≤ T) :
    (syracPMF T).map (taoZModThreeProjection h) =
      syracPMF r := by
  rw [syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod T]
  rw [syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod r]
  rw [PMF.map_comp]
  have hfun :
      taoZModThreeProjection h ∘
          (fun as : List ℕ+ => taoSection7OffsetZMod T as) =
        (fun as : List ℕ+ => taoSection7OffsetZMod r as) ∘
          (fun as : List ℕ+ => as.take r) := by
    funext as
    exact taoSection7OffsetZMod_projection_eq_take_of_le h as
  rw [hfun]
  rw [← PMF.map_comp]
  rw [geom2PNatListPMF_map_take_eq_of_le h]

end

end Tao
end Erdos1135SecondScale
