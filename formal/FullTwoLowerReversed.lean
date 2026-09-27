import FullTwoLowerForward
import FullTwoLowerScalarReverseShape

namespace CollatzResearch.FullTwoLower

open Matrix CollatzCertificate FullTwo

theorem lower_reversed_parameters
    (qa qb qe qf qg za zb ze zf zg ha hb he hf hg ka kb ke kf kg : ℝ)
    (C D : Aff2)
    (hA : Admissible (lower qa za ha ka))
    (hB : Admissible (lower qb zb hb kb))
    (hC : Admissible C) (hD : Admissible D)
    (hE : Admissible (lower qe ze he ke))
    (hF : Admissible (lower qf zf hf kf))
    (hG : Admissible (lower qg zg hg kg))
    (hw : ReversedRealWeak (lower qa za ha ka) (lower qb zb hb kb) C D
      (lower qe ze he ke) (lower qf zf hf kf) (lower qg zg hg kg)) :
    ReversedGapsZero (lower qa za ha ka) (lower qb zb hb kb) C D
      (lower qe ze he ke) (lower qf zf hf kf) (lower qg zg hg kg) := by
  have nqa : 0 ≤ qa := by simpa [lower] using hA.1.1 1 0
  have nqb : 0 ≤ qb := by simpa [lower] using hB.1.1 1 0
  have nqe : 0 ≤ qe := by simpa [lower] using hE.1.1 1 0
  have nqf : 0 ≤ qf := by simpa [lower] using hF.1.1 1 0
  have nqg : 0 ≤ qg := by simpa [lower] using hG.1.1 1 0
  have nza : 0 ≤ za := by simpa [lower] using hA.1.1 1 1
  have nzb : 0 ≤ zb := by simpa [lower] using hB.1.1 1 1
  have nze : 0 ≤ ze := by simpa [lower] using hE.1.1 1 1
  have nzf : 0 ≤ zf := by simpa [lower] using hF.1.1 1 1
  have nzg : 0 ≤ zg := by simpa [lower] using hG.1.1 1 1
  have nha : 0 ≤ ha := by simpa [lower] using hA.1.2 0
  have nhf : 0 ≤ hf := by simpa [lower] using hF.1.2 0
  have nka : 0 ≤ ka := by simpa [lower] using hA.1.2 1
  have nkb : 0 ≤ kb := by simpa [lower] using hB.1.2 1
  have nkf : 0 ≤ kf := by simpa [lower] using hF.1.2 1
  have nkg : 0 ≤ kg := by simpa [lower] using hG.1.2 1
  have hfa₀ := hw.fa.2 0
  have hga₀ := hw.ga.2 0
  have heb₀ := hw.eb.2 0
  have hfb₀ := hw.fb.2 0
  simp [comp_offset_entry, lower] at hfa₀ hga₀ heb₀ hfb₀
  have hhe : he = hf := by linarith only [hfa₀, hga₀, heb₀, hfb₀]
  have hhg : hg = hf := by linarith only [hfa₀, hga₀, heb₀, hfb₀]
  have hhb : hb = ha := by linarith only [hfa₀, hga₀, heb₀, hfb₀]
  subst he
  subst hg
  subst hb
  have h2ru : ha + ha ≤ hf := by
    have h := hw.fc.2 0
    simpa [comp_offset_entry, lower, add_assoc] using h
  let d0 := D.matrix 0 0
  let d1 := D.matrix 0 1
  let c0 := C.matrix 0 0
  let c1 := C.matrix 1 0
  have nd0 : 0 ≤ d0 := hD.1.1 0 0
  have pd0 : 0 < d0 := lt_of_lt_of_le zero_lt_one hD.2
  have nd1 : 0 ≤ d1 := hD.1.1 0 1
  have nc0 : 0 ≤ c0 := hC.1.1 0 0
  have pc0 : 0 < c0 := lt_of_lt_of_le zero_lt_one hC.2
  have nc1 : 0 ≤ c1 := hC.1.1 1 0
  have hdb : d0 * hf + d1 * kg ≤ d0 * ha + d1 * kb := by
    simpa [d0, d1, comp_offset_entry, lower] using hw.db.2 0
  have finish (hr : ha = 0) (hu : hf = 0)
      (hka : d1 * ka = 0) (hkb : d1 * kb = d1 * kg) :
      ReversedGapsZero (lower qa za ha ka) (lower qb zb ha kb) C D
        (lower qe ze hf ke) (lower qf zf hf kf) (lower qg zg hf kg) := by
    constructor <;> simp [comp_offset_entry, lower, hr, hu]
    · simpa [d1] using hka
    · simpa [d1] using hkb
  by_cases hd1 : d1 = 0
  · have hh : d0 * hf ≤ d0 * ha := by simpa [hd1] using hdb
    have hru := le_of_mul_le_mul_left hh pd0
    have hr : ha = 0 := by linarith only [h2ru, hru, nha]
    have hu : hf = 0 := by linarith only [h2ru, hru, hr]
    exact finish hr hu (by simp [hd1]) (by simp [hd1])
  · have pd1 : 0 < d1 := lt_of_le_of_ne nd1 (Ne.symm hd1)
    have hza : 1 ≤ za := by
      have h := hw.da.1 0 1
      have hh : d1 ≤ d1 * za := by simpa [d1, comp_matrix_entry, lower] using h
      have hh' : d1 * 1 ≤ d1 * za := by simpa using hh
      exact le_of_mul_le_mul_left hh' pd1
    have hzbg : zg ≤ zb := by
      have hh : d1 * zg ≤ d1 * zb := by
        simpa [d1, comp_matrix_entry, lower] using hw.db.1 0 1
      exact le_of_mul_le_mul_left hh pd1
    have hqbg : qg ≤ qb := by
      have hh : d0 + d1 * qg ≤ d0 + d1 * qb := by
        simpa [d0, d1, comp_matrix_entry, lower] using hw.db.1 0 0
      exact le_of_mul_le_mul_left (by linarith only [hh]) pd1
    have zfa := hw.fa.1 1 1
    have zga := hw.ga.1 1 1
    have zeb := hw.eb.1 1 1
    have zfb := hw.fb.1 1 1
    have qea := hw.ea.1 1 0
    have qfa := hw.fa.1 1 0
    have qga := hw.ga.1 1 0
    have qeb := hw.eb.1 1 0
    have qfb := hw.fb.1 1 0
    simp [comp_matrix_entry, lower] at zfa zga zeb zfb qea qfa qga qeb qfb
    have qgc : zb * (za * c1 + qa * c0) + qb * c0 ≤ zg * c1 + qg * c0 := by
      have h := hw.gc.1 1 0
      have hh : qb * c0 + zb * (qa * c0 + za * c1) ≤ qg * c0 + zg * c1 := by
        simpa [c0, c1, comp_matrix_entry, lower] using h
      nlinarith only [hh]
    obtain ⟨hqa, hqbg_eq⟩ := FullTwoLowerScalar.reversed_gaps_zero
      za zb zf zg (qa * c0) (qb * c0) (qf * c0) (qg * c0) c1
      hza nzb nzf nzg (mul_nonneg nqa nc0) (mul_nonneg nqb nc0)
      (mul_nonneg nqf nc0) (mul_nonneg nqg nc0) nc1 hzbg
      (mul_le_mul_of_nonneg_right hqbg nc0) zga qgc
      (by nlinarith only [mul_le_mul_of_nonneg_right qga nc0])
      (by nlinarith only [mul_le_mul_of_nonneg_right qfb nc0])
    have qa0 : qa = 0 := (mul_eq_zero.mp hqa).resolve_right (ne_of_gt pc0)
    have qbg : qb = qg := mul_right_cancel₀ (ne_of_gt pc0) hqbg_eq
    have hfa : zb * qe + qb ≤ qf := by simpa [qa0, add_comm] using qfa
    have hga : za * qf ≤ qb := by simpa [qa0, ← qbg] using qga
    have hea : za * qe ≤ qe := by simpa [qa0] using qea
    have heb : zb * qf + qb ≤ ze * qb + qe := by
      nlinarith only [qeb]
    have hshape := FullTwoLowerScalar.reversed_offset_shape za zb ze zf zg qb qe qf
      hza nzb nze nzf nzg nqb nqe nqf hzbg
      (by nlinarith only [zfa]) (by nlinarith only [zga])
      (by nlinarith only [zeb]) (by nlinarith only [zfb]) hfa hga hea heb
    rcases hshape with hzero | hexception
    · rcases hzero with ⟨qb0, qe0, qf0⟩
      have qg0 : qg = 0 := qbg.symm.trans qb0
      have hkg : kg ≤ kb := by
        have hru' : ha ≤ hf := by linarith only [h2ru, nha]
        apply le_of_mul_le_mul_left (a := d1) _ pd1
        nlinarith only [hdb, mul_le_mul_of_nonneg_left hru' nd0]
      have hgc : zb * (za * C.offset 1 + ka) + kb ≤ zg * C.offset 1 + kg := by
        simpa [comp_offset_entry, lower, qa0, qb0, qg0] using hw.gc.2 1
      have hga' : za * kf + ka ≤ zg * ka + kg := by
        simpa [comp_offset_entry, lower, qa0, qg0] using hw.ga.2 1
      have hfb : za * kg + ka ≤ zf * kb + kf := by
        simpa [comp_offset_entry, lower, qa0, qf0] using hw.fb.2 1
      obtain ⟨ka0, kbg⟩ := FullTwoLowerScalar.reversed_gaps_zero za zb zf zg
        ka kb kf kg (C.offset 1) hza nzb nzf nzg nka nkb nkf nkg (hC.1.2 1)
        hzbg hkg zga hgc hga' hfb
      have hh : d0 * hf ≤ d0 * ha := by rw [kbg] at hdb; linarith only [hdb]
      have hru := le_of_mul_le_mul_left hh pd0
      have hr : ha = 0 := by linarith only [h2ru, hru, nha]
      have hu : hf = 0 := by linarith only [h2ru, hru, hr]
      exact finish hr hu (by simp [ka0]) (congrArg (d1 * ·) kbg)
    · rcases hexception with ⟨za1, zb0, zf0, zg0, _hqf⟩
      have hgb : qb * hf + kb ≤ qb * ha + kg := by
        simpa [comp_offset_entry, lower, zb0, zg0, ← qbg] using hw.gb.2 1
      have hpos : 0 < d0 + d1 * qb :=
        add_pos_of_pos_of_nonneg pd0 (mul_nonneg nd1 nqb)
      have hh : (d0 + d1 * qb) * hf ≤ (d0 + d1 * qb) * ha := by
        nlinarith only [hdb, mul_le_mul_of_nonneg_left hgb nd1]
      have hru := le_of_mul_le_mul_left hh hpos
      have hr : ha = 0 := by linarith only [h2ru, hru, nha]
      have hu : hf = 0 := by linarith only [h2ru, hru, hr]
      have hkb_le : kb ≤ kg := by simpa [hr, hu] using hgb
      have hkg_le : kg ≤ kb := by
        apply le_of_mul_le_mul_left (a := d1) _ pd1
        simpa [hr, hu] using hdb
      have kbg : kb = kg := le_antisymm hkb_le hkg_le
      have hga' : kf + ka ≤ kg := by
        simpa [comp_offset_entry, lower, hr, hu, za1, zg0, qa0] using hw.ga.2 1
      have hfb : kg + ka ≤ kf := by
        simpa [comp_offset_entry, lower, hr, hu, za1, zf0, qa0] using hw.fb.2 1
      have ka0 : ka = 0 := by linarith only [hga', hfb, nka]
      exact finish hr hu (by simp [ka0]) (congrArg (d1 * ·) kbg)

theorem lower_reversed_gaps_zero (A B C D E F G : Aff2)
    (hA : Admissible A) (hB : Admissible B) (hC : Admissible C)
    (hD : Admissible D) (hE : Admissible E) (hF : Admissible F) (hG : Admissible G)
    (lA : Lower A) (lB : Lower B) (lE : Lower E) (lF : Lower F) (lG : Lower G)
    (hw : ReversedRealWeak A B C D E F G) : ReversedGapsZero A B C D E F G := by
  obtain ⟨qa, za, ha, ka, rfl⟩ : ∃ q z h k, A = lower q z h k :=
    ⟨_, _, _, _, eq_lower A lA⟩
  obtain ⟨qb, zb, hb, kb, rfl⟩ : ∃ q z h k, B = lower q z h k :=
    ⟨_, _, _, _, eq_lower B lB⟩
  obtain ⟨qe, ze, he, ke, rfl⟩ : ∃ q z h k, E = lower q z h k :=
    ⟨_, _, _, _, eq_lower E lE⟩
  obtain ⟨qf, zf, hf, kf, rfl⟩ : ∃ q z h k, F = lower q z h k :=
    ⟨_, _, _, _, eq_lower F lF⟩
  obtain ⟨qg, zg, hg, kg, rfl⟩ : ∃ q z h k, G = lower q z h k :=
    ⟨_, _, _, _, eq_lower G lG⟩
  exact lower_reversed_parameters qa qb qe qf qg za zb ze zf zg ha hb he hf hg ka kb ke kf kg
    C D hA hB hC hD hE hF hG hw

#print axioms lower_reversed_parameters
#print axioms lower_reversed_gaps_zero

end CollatzResearch.FullTwoLower
