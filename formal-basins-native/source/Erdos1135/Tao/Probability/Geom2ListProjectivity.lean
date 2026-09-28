import Erdos1135.Tao.Syracuse.ValuationDistribution

/-!
# Low Geom(2) List Projectivity

This probability leaf exposes iid prefix and head-tail marginals without
importing Fourier or renewal infrastructure.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- A length `r+L` iid positive Geom(2) list has the length-`r` prefix law. -/
theorem geom2PNatListPMF_map_take_low_eq (r L : ℕ) :
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
              (geom2PNatListPMF r) := by rw [ih]

/-- Splitting after `K` entries gives independent iid head and tail laws. -/
theorem geom2PNatListPMF_map_take_drop_low_eq (K N : ℕ) :
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
              (fun pair => (h :: pair.1, pair.2)) := by rw [ih]
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

/-- Dropping an iid prefix leaves the iid suffix law. -/
theorem geom2PNatListPMF_map_drop_low_eq (K N : ℕ) :
    (geom2PNatListPMF (K + N)).map (fun full => full.drop K) =
      geom2PNatListPMF N := by
  calc
    (geom2PNatListPMF (K + N)).map (fun full => full.drop K) =
        ((geom2PNatListPMF (K + N)).map
          (fun full => (full.take K, full.drop K))).map Prod.snd := by
            rw [PMF.map_comp]
            rfl
    _ = ((geom2PNatListPMF K).bind fun pre =>
          (geom2PNatListPMF N).map fun future => (pre, future)).map
        Prod.snd := by
      rw [geom2PNatListPMF_map_take_drop_low_eq]
    _ = (geom2PNatListPMF K).bind (fun _ => geom2PNatListPMF N) := by
      rw [PMF.map_bind]
      apply congrArg (PMF.bind (geom2PNatListPMF K))
      funext pre
      rw [PMF.map_comp]
      simpa [Function.comp_def] using
        (PMF.map_id (geom2PNatListPMF N))
    _ = geom2PNatListPMF N := PMF.bind_const _ _

theorem geom2PNatListPMF_map_take_low_eq_of_le
    {r T : ℕ} (h : r ≤ T) :
    (geom2PNatListPMF T).map (fun as => as.take r) =
      geom2PNatListPMF r := by
  simpa [Nat.add_sub_of_le h] using
    (geom2PNatListPMF_map_take_low_eq r (T - r))

end

end Tao
end Erdos1135
