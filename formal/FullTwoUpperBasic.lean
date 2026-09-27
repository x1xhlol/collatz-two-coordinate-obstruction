import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace CollatzResearch.FullTwoUpper

structure Data where
  za : ℝ
  zb : ℝ
  ze : ℝ
  zf : ℝ
  zg : ℝ
  qa : ℝ
  qb : ℝ
  qe : ℝ
  qf : ℝ
  qg : ℝ
  ha : ℝ
  hb : ℝ
  he : ℝ
  hf : ℝ
  hg : ℝ
  ka : ℝ
  kb : ℝ
  ke : ℝ
  kf : ℝ
  kg : ℝ
  kap : ℝ
  tau : ℝ

structure Weak (m : Data) : Prop where
  za : 0 ≤ m.za
  zb : 0 ≤ m.zb
  ze : 0 ≤ m.ze
  zf : 0 ≤ m.zf
  zg : 0 ≤ m.zg
  qa : 0 ≤ m.qa
  qb : 0 ≤ m.qb
  qe : 0 ≤ m.qe
  qf : 0 ≤ m.qf
  qg : 0 ≤ m.qg
  ha : 0 ≤ m.ha
  hb : 0 ≤ m.hb
  he : 0 ≤ m.he
  hf : 0 ≤ m.hf
  hg : 0 ≤ m.hg
  ka : 0 ≤ m.ka
  kb : 0 ≤ m.kb
  ke : 0 ≤ m.ke
  kf : 0 ≤ m.kf
  kg : 0 ≤ m.kg
  kap : 0 ≤ m.kap
  tau : 0 ≤ m.tau
  af_z : m.ze * m.zb ≤ m.za * m.zf
  ag_z : m.zf * m.za ≤ m.za * m.zg
  be_z : m.zf * m.zb ≤ m.zb * m.ze
  bf_z : m.zg * m.za ≤ m.zb * m.zf
  ae_q : m.qa + m.qe * m.za ≤ m.qe + m.qa * m.ze
  af_q : m.qb + m.qe * m.zb ≤ m.qf + m.qa * m.zf
  ag_q : m.qa + m.qf * m.za ≤ m.qg + m.qa * m.zg
  be_q : m.qb + m.qf * m.zb ≤ m.qe + m.qb * m.ze
  bf_q : m.qa + m.qg * m.za ≤ m.qf + m.qb * m.zf
  bg_q : m.qb + m.qg * m.zb ≤ m.qg + m.qb * m.zg
  ae_k : m.ke + m.ze * m.ka ≤ m.ka + m.za * m.ke
  af_k : m.ke + m.ze * m.kb ≤ m.ka + m.za * m.kf
  ag_k : m.kf + m.zf * m.ka ≤ m.ka + m.za * m.kg
  be_k : m.kf + m.zf * m.kb ≤ m.kb + m.zb * m.ke
  bf_k : m.kg + m.zg * m.ka ≤ m.kb + m.zb * m.kf
  bg_k : m.kg + m.zg * m.kb ≤ m.kb + m.zb * m.kg
  ae_h : m.he + m.ha + m.qe * m.ka ≤ m.ha + m.he + m.qa * m.ke
  af_h : m.he + m.hb + m.qe * m.kb ≤ m.ha + m.hf + m.qa * m.kf
  ag_h : m.hf + m.ha + m.qf * m.ka ≤ m.ha + m.hg + m.qa * m.kg
  be_h : m.hf + m.hb + m.qf * m.kb ≤ m.hb + m.he + m.qb * m.ke
  bf_h : m.hg + m.ha + m.qg * m.ka ≤ m.hb + m.hf + m.qb * m.kf
  bg_h : m.hg + m.hb + m.qg * m.kb ≤ m.hb + m.hg + m.qb * m.kg
  ad_k : m.tau ≤ m.za * m.tau + m.ka
  bd_k : m.zg * m.tau + m.kg ≤ m.zb * m.tau + m.kb
  ad_h : 0 ≤ m.qa * m.tau + m.ha
  bd_h : m.qg * m.tau + m.hg ≤ m.qb * m.tau + m.hb
  ce_q : m.qb + m.kap * m.zb ≤ m.qe + m.kap * m.ze
  cf_q : m.qa + m.qa * m.za + m.kap * (m.za * m.za) ≤ m.qf + m.kap * m.zf
  cg_q : m.qb + m.qa * m.zb + m.kap * (m.za * m.zb) ≤ m.qg + m.kap * m.zg
  ce_h : m.hb + m.kap * m.kb ≤ m.he + m.kap * m.ke
  cf_h : 2 * m.ha + m.qa * m.ka + m.kap * (m.ka + m.za * m.ka) ≤ m.hf + m.kap * m.kf
  cg_h : m.ha + m.hb + m.qa * m.kb + m.kap * (m.ka + m.za * m.kb) ≤ m.hg + m.kap * m.kg

structure ZeroGaps (m : Data) : Prop where
  ad : m.qa * m.tau + m.ha = 0
  bd : m.qb * m.tau + m.hb = m.qg * m.tau + m.hg
  ae : m.ha + m.he + m.qa * m.ke = m.he + m.ha + m.qe * m.ka
  af : m.ha + m.hf + m.qa * m.kf = m.he + m.hb + m.qe * m.kb
  ag : m.ha + m.hg + m.qa * m.kg = m.hf + m.ha + m.qf * m.ka
  be : m.hb + m.he + m.qb * m.ke = m.hf + m.hb + m.qf * m.kb
  bf : m.hb + m.hf + m.qb * m.kf = m.hg + m.ha + m.qg * m.ka
  bg : m.hb + m.hg + m.qb * m.kg = m.hg + m.hb + m.qg * m.kb
  ce : m.he + m.kap * m.ke = m.hb + m.kap * m.kb
  cf : m.hf + m.kap * m.kf = 2 * m.ha + m.qa * m.ka + m.kap * (m.ka + m.za * m.ka)
  cg : m.hg + m.kap * m.kg = m.ha + m.hb + m.qa * m.kb + m.kap * (m.ka + m.za * m.kb)

structure ExactSwaps (m : Data) : Prop where
  ae_q : m.qa + m.qe * m.za = m.qe + m.qa * m.ze
  af_q : m.qb + m.qe * m.zb = m.qf + m.qa * m.zf
  ag_q : m.qa + m.qf * m.za = m.qg + m.qa * m.zg
  be_q : m.qb + m.qf * m.zb = m.qe + m.qb * m.ze
  bf_q : m.qa + m.qg * m.za = m.qf + m.qb * m.zf
  bg_q : m.qb + m.qg * m.zb = m.qg + m.qb * m.zg
  ae_k : m.ke + m.ze * m.ka = m.ka + m.za * m.ke
  af_k : m.ke + m.ze * m.kb = m.ka + m.za * m.kf
  ag_k : m.kf + m.zf * m.ka = m.ka + m.za * m.kg
  be_k : m.kf + m.zf * m.kb = m.kb + m.zb * m.ke
  bf_k : m.kg + m.zg * m.ka = m.kb + m.zb * m.kf
  bg_k : m.kg + m.zg * m.kb = m.kb + m.zb * m.kg
  ae_h : m.he + m.ha + m.qe * m.ka = m.ha + m.he + m.qa * m.ke
  af_h : m.he + m.hb + m.qe * m.kb = m.ha + m.hf + m.qa * m.kf
  ag_h : m.hf + m.ha + m.qf * m.ka = m.ha + m.hg + m.qa * m.kg
  be_h : m.hf + m.hb + m.qf * m.kb = m.hb + m.he + m.qb * m.ke
  bf_h : m.hg + m.ha + m.qg * m.ka = m.hb + m.hf + m.qb * m.kf
  bg_h : m.hg + m.hb + m.qg * m.kb = m.hb + m.hg + m.qb * m.kg

theorem slope_equalities (m : Data) (w : Weak m) :
    m.za * m.zf = m.ze * m.zb ∧ m.za * m.zg = m.zf * m.za ∧
    m.zb * m.ze = m.zf * m.zb ∧ m.zb * m.zf = m.zg * m.za := by
  have h1 := w.af_z
  have h2 := w.ag_z
  have h3 := w.be_z
  have h4 := w.bf_z
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem aggregate_nonneg (m : Data) (w : Weak m) :
    0 ≤ (m.ze + m.zf + m.zg - 3) * (m.qa + m.qb) -
      (m.za + m.zb - 2) * (m.qe + m.qf + m.qg) ∧
    0 ≤ (m.za + m.zb - 2) * (m.ke + m.kf + m.kg) -
      (m.ze + m.zf + m.zg - 3) * (m.ka + m.kb) ∧
    0 ≤ (m.qa + m.qb) * (m.ke + m.kf + m.kg) -
      (m.qe + m.qf + m.qg) * (m.ka + m.kb) := by
  constructor
  · nlinarith only [w.ae_q, w.af_q, w.ag_q, w.be_q, w.bf_q, w.bg_q]
  constructor
  · nlinarith only [w.ae_k, w.af_k, w.ag_k, w.be_k, w.bf_k, w.bg_k]
  · nlinarith only [w.ae_h, w.af_h, w.ag_h, w.be_h, w.bf_h, w.bg_h]

theorem negative_aggregate_exact {p r Q P R K : ℝ}
    (hQ : 0 ≤ Q) (hP : 0 ≤ P) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hq : 0 ≤ r*Q-p*P) (hk : 0 ≤ p*K-r*R) (hh : 0 ≤ Q*K-P*R)
    (hn : p < 0 ∨ r < 0) (hQP : 0 < Q+P) (hRK : 0 < R+K) :
    r*Q-p*P = 0 ∧ p*K-r*R = 0 ∧ Q*K-P*R = 0 := by
  have i1 : R*(r*Q-p*P)+Q*(p*K-r*R)=p*(Q*K-P*R) := by ring
  have i2 : K*(r*Q-p*P)+P*(p*K-r*R)=r*(Q*K-P*R) := by ring
  have hzero : Q*K-P*R = 0 := by
    rcases hn with hp | hr
    · have hleft := add_nonneg (mul_nonneg hR hq) (mul_nonneg hQ hk)
      by_contra hnz
      have hpz : 0 < Q*K-P*R := lt_of_le_of_ne hh (Ne.symm hnz)
      have := mul_neg_of_neg_of_pos hp hpz
      linarith
    · have hleft := add_nonneg (mul_nonneg hK hq) (mul_nonneg hP hk)
      by_contra hnz
      have hpz : 0 < Q*K-P*R := lt_of_le_of_ne hh (Ne.symm hnz)
      have := mul_neg_of_neg_of_pos hr hpz
      linarith
  rw [hzero,mul_zero] at i1 i2
  have iz : (R+K)*(r*Q-p*P)+(Q+P)*(p*K-r*R)=0 := by nlinarith only [i1,i2]
  have qzero : r*Q-p*P=0 := by
    have hn := mul_nonneg (le_of_lt hQP) hk
    have hz : (R+K)*(r*Q-p*P)=0 := by nlinarith only [iz,hn,mul_nonneg (le_of_lt hRK) hq]
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hRK)
  have kzero : p*K-r*R=0 := by
    have hz : (Q+P)*(p*K-r*R)=0 := by rw [qzero,mul_zero,zero_add] at iz; exact iz
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hQP)
  exact ⟨qzero,kzero,hzero⟩


theorem exact_of_negative (m : Data) (w : Weak m)
    (hn : m.za + m.zb < 2 ∨ m.ze + m.zf + m.zg < 3)
    (hq : 0 < m.qa + m.qb + (m.qe + m.qf + m.qg))
    (hk : 0 < m.ka + m.kb + (m.ke + m.kf + m.kg)) : ExactSwaps m := by
  obtain ⟨gq,gk,gh⟩ := aggregate_nonneg m w
  have hn' : m.za+m.zb-2 < 0 ∨ m.ze+m.zf+m.zg-3 < 0 := by
    rcases hn with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  obtain ⟨eqQ,eqK,eqH⟩ := negative_aggregate_exact
    (add_nonneg w.qa w.qb) (add_nonneg (add_nonneg w.qe w.qf) w.qg)
    (add_nonneg w.ka w.kb) (add_nonneg (add_nonneg w.ke w.kf) w.kg)
    gq gk gh hn' hq hk
  constructor
  · nlinarith only [eqQ, w.ae_q, w.af_q, w.ag_q, w.be_q, w.bf_q, w.bg_q]
  · nlinarith only [eqQ, w.ae_q, w.af_q, w.ag_q, w.be_q, w.bf_q, w.bg_q]
  · nlinarith only [eqQ, w.ae_q, w.af_q, w.ag_q, w.be_q, w.bf_q, w.bg_q]
  · nlinarith only [eqQ, w.ae_q, w.af_q, w.ag_q, w.be_q, w.bf_q, w.bg_q]
  · nlinarith only [eqQ, w.ae_q, w.af_q, w.ag_q, w.be_q, w.bf_q, w.bg_q]
  · nlinarith only [eqQ, w.ae_q, w.af_q, w.ag_q, w.be_q, w.bf_q, w.bg_q]
  · nlinarith only [eqK, w.ae_k, w.af_k, w.ag_k, w.be_k, w.bf_k, w.bg_k]
  · nlinarith only [eqK, w.ae_k, w.af_k, w.ag_k, w.be_k, w.bf_k, w.bg_k]
  · nlinarith only [eqK, w.ae_k, w.af_k, w.ag_k, w.be_k, w.bf_k, w.bg_k]
  · nlinarith only [eqK, w.ae_k, w.af_k, w.ag_k, w.be_k, w.bf_k, w.bg_k]
  · nlinarith only [eqK, w.ae_k, w.af_k, w.ag_k, w.be_k, w.bf_k, w.bg_k]
  · nlinarith only [eqK, w.ae_k, w.af_k, w.ag_k, w.be_k, w.bf_k, w.bg_k]
  · nlinarith only [eqH, w.ae_h, w.af_h, w.ag_h, w.be_h, w.bf_h, w.bg_h]
  · nlinarith only [eqH, w.ae_h, w.af_h, w.ag_h, w.be_h, w.bf_h, w.bg_h]
  · nlinarith only [eqH, w.ae_h, w.af_h, w.ag_h, w.be_h, w.bf_h, w.bg_h]
  · nlinarith only [eqH, w.ae_h, w.af_h, w.ag_h, w.be_h, w.bf_h, w.bg_h]
  · nlinarith only [eqH, w.ae_h, w.af_h, w.ag_h, w.be_h, w.bf_h, w.bg_h]
  · nlinarith only [eqH, w.ae_h, w.af_h, w.ag_h, w.be_h, w.bf_h, w.bg_h]

end CollatzResearch.FullTwoUpper
