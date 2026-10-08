/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Section7Cancellation
import Erdos1135SecondScale.Tao.Fourier.Section7Geometry

/-!
# Section 7 Source Predicates

This low Fourier leaf defines the raw source black/white predicates and their
finite horizontal domain gate. It intentionally imports no renewal modules.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Raw source blackness at a Section 7 point, before the source-domain gate. -/
noncomputable def taoSection7SourceBlackPoint
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (p : TaoSection7Point) : Prop :=
  taoSection7Black epsilon (taoSection7ThetaResidue n xi p.j p.l)

/-- Raw source whiteness at a Section 7 point, before the source cutoff gate. -/
noncomputable def taoSection7SourceWhitePoint
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (p : TaoSection7Point) : Prop :=
  taoSection7White epsilon (taoSection7ThetaResidue n xi p.j p.l)

/-- Source-domain membership for Section 7 points. -/
def taoSection7SourcePointInDomain (J : ℕ) (p : TaoSection7Point) : Prop :=
  (p.j : ℕ) ≤ J

/-- Source blackness restricted to Tao's finite source domain. -/
noncomputable def taoSection7SourceBlackInDomain
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ)
    (p : TaoSection7Point) : Prop :=
  taoSection7SourcePointInDomain J p ∧
    taoSection7SourceBlackPoint n xi epsilon p

/-- Alias matching source-checker wording for the domain-gated black set. -/
noncomputable def taoSection7SourceBlackDomain
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ) :
    TaoSection7Point → Prop :=
  taoSection7SourceBlackInDomain n xi epsilon J

theorem taoSection7SourceBlackInDomain_domain
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7Point}
    (hp : taoSection7SourceBlackInDomain n xi epsilon J p) :
    (p.j : ℕ) ≤ J :=
  hp.1

theorem taoSection7SourceBlackInDomain_raw
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7Point}
    (hp : taoSection7SourceBlackInDomain n xi epsilon J p) :
    taoSection7SourceBlackPoint n xi epsilon p :=
  hp.2

end Tao
end Erdos1135SecondScale
