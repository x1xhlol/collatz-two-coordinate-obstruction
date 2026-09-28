import Erdos1135.Tao.Section3

namespace CollatzClockAudit
open Erdos1135.Tao

theorem passAtMostOrOne_of_first_hit {B q t : ℕ} (hB : 1 ≤ B)
    (hfirst : syracuseFirstHitAtMost B q t) :
    (syracusePassLocationAtMostOrOne B q hB).1 = (syracuse^[t]) q := by
  have hhit : syracuseHitsAtMost q B := ⟨t, hfirst.1⟩
  rw [syracusePassLocationAtMostOrOne_of_hitsAtMost hB hhit]
  have ht := syracuseFirstHitAtMost_unique
    (syracuseFirstHitAtMost_of_hitsAtMost q B hhit) hfirst
  simp only [ht]

theorem passAtMostOrOne_of_le {B q : ℕ} (hB : 1 ≤ B) (hq : q ≤ B) :
    (syracusePassLocationAtMostOrOne B q hB).1 = q := by
  have hfirst : syracuseFirstHitAtMost B q 0 := ⟨by simpa using hq, by simp⟩
  simpa using passAtMostOrOne_of_first_hit hB hfirst

theorem pass_value_eq_of_first_hit {B q t : ℕ} (hB : 1 ≤ B)
    (hfirst : syracuseFirstHitAtMost B q t) :
    (syracusePassLocationOrOne B q hB).1 = (syracuse^[t]) q :=
  passAtMostOrOne_of_first_hit hB hfirst

theorem real_pass_value_eq_of_first_hit {x : ℝ} {q t : ℕ} (hx : 1 ≤ x)
    (hfirst : syracuseFirstHitAtMostReal x q t) :
    (syracusePassLocationRealFloorOrOne x q hx).1 = (syracuse^[t]) q := by
  exact pass_value_eq_of_first_hit (one_le_floor_of_one_le hx)
    ((syracuseFirstHitAtMostReal_iff_floor (by linarith : 0 ≤ x)).mp hfirst)

/-- Successful outer passage preserves whether the lower barrier is ever
reached, including a lower hit at the outer landing itself. -/
theorem hitsAtMost_tail_iff_of_first_hit {B C q r : ℕ} (hBC : B ≤ C)
    (hfirst : syracuseFirstHitAtMost C q r) :
    syracuseHitsAtMost ((syracuse^[r]) q) B ↔ syracuseHitsAtMost q B := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t + r, ?_⟩
    simpa only [Function.iterate_add_apply] using ht
  · intro hhit
    let t := syracuseFirstPassageTime q B hhit
    have hBfirst : syracuseFirstHitAtMost B q t :=
      syracuseFirstHitAtMost_of_hitsAtMost q B hhit
    have hrt : r ≤ t := by
      by_contra h
      have ht := hfirst.2 t (by omega)
      exact not_lt_of_ge (hBfirst.1.trans hBC) ht
    exact ⟨t - r, (syracuseFirstHitAtMost_tail hBfirst hrt).1⟩

/-- The default value is one, which is fixed by every admitted lower
passage map. This identity includes all success and no-hit cases. -/
theorem passAtMostOrOne_compose {B C q : ℕ} (hB : 1 ≤ B) (hBC : B ≤ C)
    (hC : 1 ≤ C) :
    syracusePassLocationAtMostOrOne B
      (syracusePassLocationAtMostOrOne C q hC).1 hB =
      syracusePassLocationAtMostOrOne B q hB := by
  classical
  apply Subtype.ext
  by_cases hqC : syracuseHitsAtMost q C
  · let r := syracuseFirstPassageTime q C hqC
    have hr : syracuseFirstHitAtMost C q r :=
      syracuseFirstHitAtMost_of_hitsAtMost q C hqC
    have hpassC := passAtMostOrOne_of_first_hit hC hr
    rw [hpassC]
    by_cases hqB : syracuseHitsAtMost q B
    · have htail := (hitsAtMost_tail_iff_of_first_hit hBC hr).mpr hqB
      let t := syracuseFirstPassageTime ((syracuse^[r]) q) B htail
      have ht : syracuseFirstHitAtMost B ((syracuse^[r]) q) t :=
        syracuseFirstHitAtMost_of_hitsAtMost _ B htail
      have hconcat : syracuseFirstHitAtMost B q (r + t) :=
        syracuseFirstHitAtMost_of_tail (fun k hk => hBC.trans_lt (hr.2 k hk)) ht
      rw [passAtMostOrOne_of_first_hit hB ht, passAtMostOrOne_of_first_hit hB hconcat]
      rw [Nat.add_comm r t, Function.iterate_add_apply]
    · have htail : ¬ syracuseHitsAtMost ((syracuse^[r]) q) B :=
        fun h => hqB ((hitsAtMost_tail_iff_of_first_hit hBC hr).mp h)
      rw [syracusePassLocationAtMostOrOne_of_not_hitsAtMost hB htail,
        syracusePassLocationAtMostOrOne_of_not_hitsAtMost hB hqB]
  · have hqB : ¬ syracuseHitsAtMost q B := by
      rintro ⟨t, ht⟩
      exact hqC ⟨t, ht.trans hBC⟩
    rw [syracusePassLocationAtMostOrOne_of_not_hitsAtMost hC hqC,
      syracusePassLocationAtMostOrOne_of_not_hitsAtMost hB hqB]
    exact passAtMostOrOne_of_le hB hB

theorem passOrOne_compose {B C q : ℕ} (hB : 1 ≤ B) (hBC : B ≤ C)
    (hC : 1 ≤ C) :
    syracusePassLocationOrOne B (syracusePassLocationOrOne C q hC).1 hB =
      syracusePassLocationOrOne B q hB :=
  passAtMostOrOne_compose hB hBC hC

theorem realFloorPassOrOne_compose {x y : ℝ} {q : ℕ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hy : 1 ≤ y) :
    syracusePassLocationRealFloorOrOne x
      (syracusePassLocationRealFloorOrOne y q hy).1 hx =
      syracusePassLocationRealFloorOrOne x q hx := by
  exact passOrOne_compose (one_le_floor_of_one_le hx) (Nat.floor_le_floor hxy)
    (one_le_floor_of_one_le hy)

theorem passOrOne_map_compose {Ω : Type*} (μ : PMF Ω) (q : Ω → ℕ)
    {B C : ℕ} (hB : 1 ≤ B) (hBC : B ≤ C) (hC : 1 ≤ C) :
    (μ.map (fun ω => syracusePassLocationOrOne C (q ω) hC)).map
      (fun u => syracusePassLocationOrOne B u.1 hB) =
        μ.map (fun ω => syracusePassLocationOrOne B (q ω) hB) := by
  rw [PMF.map_comp]
  congr 1
  funext ω
  exact passOrOne_compose hB hBC hC

theorem realFloorPassOrOne_map_compose {Ω : Type*} (μ : PMF Ω) (q : Ω → ℕ)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : 1 ≤ y) :
    (μ.map (fun ω => syracusePassLocationRealFloorOrOne y (q ω) hy)).map
      (fun u => syracusePassLocationRealFloorOrOne x u.1 hx) =
        μ.map (fun ω => syracusePassLocationRealFloorOrOne x (q ω) hx) := by
  exact passOrOne_map_compose μ q (one_le_floor_of_one_le hx) (Nat.floor_le_floor hxy)
    (one_le_floor_of_one_le hy)

theorem passLocationLaw_map_lower {lo hi B C : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (hB : 1 ≤ B) (hBC : B ≤ C) (hC : 1 ≤ C) :
    (syracusePassLocationLaw lo hi C hC hmass).map
      (fun u => syracusePassLocationOrOne B u.1 hB) =
        syracusePassLocationLaw lo hi B hB hmass := by
  exact passOrOne_map_compose (oddLogWindowPMF lo hi hmass) Subtype.val hB hBC hC

theorem realFloorPassLocationLaw_map_lower {lo hi : ℕ} {x y : ℝ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (hx : 1 ≤ x) (hxy : x ≤ y) (hy : 1 ≤ y) :
    (syracusePassLocationRealFloorLaw lo hi y hy hmass).map
      (fun u => syracusePassLocationRealFloorOrOne x u.1 hx) =
        syracusePassLocationRealFloorLaw lo hi x hx hmass := by
  exact realFloorPassOrOne_map_compose (oddLogWindowPMF lo hi hmass) Subtype.val hx hxy hy

end CollatzClockAudit
