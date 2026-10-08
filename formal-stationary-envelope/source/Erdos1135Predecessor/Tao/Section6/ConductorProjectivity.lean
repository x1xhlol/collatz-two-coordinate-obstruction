/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7SourceLaw
import Erdos1135Predecessor.Tao.Section6.ModulusProjection

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

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

theorem geom2PNatListPMF_map_take_eq_of_le
    {r T : ℕ} (h : r ≤ T) :
    (geom2PNatListPMF T).map (fun as => as.take r) =
      geom2PNatListPMF r := by
  simpa [Nat.add_sub_of_le h] using
    (geom2PNatListPMF_map_take_eq r (T - r))

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

end Erdos1135Predecessor
