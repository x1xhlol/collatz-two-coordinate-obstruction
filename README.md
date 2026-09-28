# Collatz matrix obstructions, synchronization, and basin densities

Three standalone papers by Lucas Valbuena are maintained here, with their LaTeX sources and formal verification artifacts.

| Paper | Files | Verification scope |
| --- | --- | --- |
| Two-coordinate obstructions for affine interpretations of the Yolcu–Aaronson–Heule Collatz system | [PDF](paper/two-coordinate-obstruction.pdf) · [Source](paper/two-coordinate-obstruction.tex) | Lean checks the stated algebraic obstruction results and supporting lemmas. |
| An independent second proof of Said Duran’s equal-height Collatz runs theorem | [PDF](paper/said-duran-second-proof.pdf) · [Source](paper/said-duran-second-proof.tex) | Lean checks finite-pattern synchronization and equal first hitting times. Priority belongs to Said Duran. |
| Collatz basin densities and canonical traces from first-passage stabilization | [PDF](paper/tao-basin-densities.pdf) · [Source](paper/tao-basin-densities.tex) | Selected proof steps are checked. The main analytic theorem chain is not yet fully formalized. |

The first paper retains Sections 1–8 of the earlier combined manuscript. Its two-coordinate obstruction with diagonal bounds covers all eleven weak rules, separately in both word orientations. A second result removes the diagonal bounds for the reversed system and excludes both eligible TOP removals. It also proves a forward growth and contraction criterion in arbitrary finite dimension. The unrestricted forward TOP problem and unrestricted higher-dimensional interpretations remain unresolved.

The second paper gives an independent proof of Omar Javier Said Duran’s theorem on arbitrarily long consecutive runs with equal finite Collatz height and equal odd-step counts. His [preprint](https://doi.org/10.5281/zenodo.23003526), dated 27 September 2026, was posted before our proof; his [Lean archive](https://doi.org/10.5281/zenodo.23003500) is separate. Our equivalent finite-pattern formulation synchronizes affine families on a dyadic progression and selects a power-of-two endpoint. It constructs translating integers, rather than proving convergence from an arbitrary prescribed start.

The third paper develops logarithmic basin densities and countable label laws from Tao’s first-passage stabilization. Weighted basin densities identify the critical Green, cylinder Cesàro, and cylinder Abel limits. It also bounds the largest stationary cylinder mass between `2^(-k)` and `(2k+3)2^(-k)`.

The literature comparison uses Shaik’s **6 September 2026 version 4.0.0**, Nashida’s three **27 September 2026** preprints, and Mazur’s pinned formalizations. Additional theorems of Mazur upgrade the basin and label limits to natural density and give positivity of the canonical trace exactly at integers not divisible by three. Those inputs are credited separately from Tao’s theorem. Global sublinearity remains unproved; with the predecessor theorem it is equivalent to eventual periodicity of every orbit. Additional cycles also remain unexcluded. None of the three papers proves the Collatz conjecture.

## Lean verification

The [matrix and synchronization claim map](paper/lean-claims.md) identifies the checked declarations in the first two papers. Their combined closure contains **137 Lean modules, 633 public theorem/lemma declarations, and 93 audited definitions**. Four auxiliary modules on conditional stationary profiles are retained as checked algebra outside the papers’ contributions. The [rebuild report](verification/rebuild.json) records the build and axiom audit.

The [basin claim map](paper/basin-lean-claims.md) records the partial formalization of the third paper, including the precise missing analytic steps. Its sources, inventory, and rebuild report are separate from the original closure. A successful check of these modules does not certify the full basin-density paper or its external theorem interfaces.

Use Lean **4.27.0** and mathlib commit **`a3a10db0e9d66acbebf76c5e6a135066525ac900`**. Dependency setup is described in [formal/README.md](formal/README.md). Both scopes use the same [verifier](verify.py), which creates fresh local compiled modules and permits only `propext`, `Classical.choice`, and `Quot.sound`:

```sh
python3 verify.py --mathlib-root /path/to/mathlib4 --report /new/path/matrix-synchronization.json
python3 verify.py --scope basins --mathlib-root /path/to/mathlib4 --report /new/path/basins.json
```

Each report path must be unused. No SAT-solver result is used as a proof premise.

## Build the papers

Each source is self-contained, including its bibliography and any Lean excerpts. It uses XeLaTeX and the TeX Live font `DejaVuSansMono.ttf`. Run XeLaTeX twice per paper, or use Tectonic:

```sh
cd paper
tectonic --keep-logs --untrusted two-coordinate-obstruction.tex
tectonic --keep-logs --untrusted said-duran-second-proof.tex
tectonic --keep-logs --untrusted tao-basin-densities.tex
```

## Attribution and citation

The rewriting system and its equivalence to the Collatz conjecture are due to Yolcu, Aaronson, and Heule, [An Automated Approach to the Collatz Conjecture](https://doi.org/10.1007/s10817-022-09658-8), *Journal of Automated Reasoning* 67(2), Article 15 (2023). Priority for the equal-height runs theorem belongs to Said Duran. The main analytic input is Tao’s [Almost all orbits of the Collatz map attain almost bounded values](https://doi.org/10.1017/fmp.2022.8), *Forum of Mathematics, Pi* 10 (2022), e12. The basin paper gives precise citations for the additional results of Shaik, Nashida, Mazur, and Inselmann.

[CITATION.cff](CITATION.cff) lists the three papers. Each manuscript discloses the use of OpenAI Codex. Automated proof development and review do not constitute external peer review or endorsement by the cited authors.
