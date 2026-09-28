# Collatz matrix obstructions, synchronization, and basin densities

Three standalone papers are maintained here, with their LaTeX sources and formal verification artifacts.

| Paper | Files | Verification scope |
| --- | --- | --- |
| Two-coordinate obstructions for affine interpretations of the Yolcu–Aaronson–Heule Collatz system | [PDF](paper/two-coordinate-obstruction.pdf) · [Source](paper/two-coordinate-obstruction.tex) | Lean checks the stated algebraic obstruction results and supporting lemmas. |
| An independent second proof of Said Duran’s equal-height Collatz runs theorem | [PDF](paper/said-duran-second-proof.pdf) · [Source](paper/said-duran-second-proof.tex) | Lean checks finite-pattern synchronization and equal first hitting times. Priority belongs to Said Duran. |
| Collatz basin densities and canonical traces from first-passage stabilization | [PDF](paper/tao-basin-densities.pdf) · [Source](paper/tao-basin-densities.tex) | Lean checks the density, clock, Green/cylinder identification, natural-density, positivity, and component-equivalence results. |

The first paper retains Sections 1–8 of the earlier combined manuscript. Its two-coordinate obstruction with diagonal bounds covers all eleven weak rules, separately in both word orientations. A second result removes the diagonal bounds for the reversed system and excludes both eligible TOP removals. It also proves a forward growth and contraction criterion in arbitrary finite dimension. The unrestricted forward TOP problem and unrestricted higher-dimensional interpretations remain unresolved.

The second paper gives an independent proof of Omar Javier Said Duran’s theorem on arbitrarily long consecutive runs with equal finite Collatz height and equal odd-step counts. His [preprint](https://doi.org/10.5281/zenodo.23003526), dated 27 September 2026, was posted before our proof; his [Lean archive](https://doi.org/10.5281/zenodo.23003500) is separate. Our equivalent finite-pattern formulation synchronizes affine families on a dyadic progression and selects a power-of-two endpoint. It constructs translating integers, rather than proving convergence from an arbitrary prescribed start.

The third paper develops logarithmic basin densities and countable label laws from Tao’s first-passage stabilization. Weighted basin densities identify the critical Green, cylinder Cesàro, and cylinder Abel limits. It also bounds the largest stationary cylinder mass between `2^(-k)` and `(2k+3)2^(-k)`.

The literature comparison uses Shaik’s **6 September 2026 version 4.0.0**, Nashida’s three **27 September 2026** preprints, and Mazur’s pinned formalizations. Additional theorems of Mazur upgrade the basin and label limits to natural density and give positivity of the canonical trace exactly at integers not divisible by three. Those inputs are credited separately from Tao’s theorem. Global sublinearity remains unproved; with the predecessor theorem it is equivalent to eventual periodicity of every orbit. Additional cycles also remain unexcluded. None of the three papers proves the Collatz conjecture.

## Lean verification

The [matrix and synchronization claim map](paper/lean-claims.md) identifies the checked declarations in the first two papers. Their combined closure contains **137 Lean modules, 633 public theorem/lemma declarations, and 93 audited definitions**. Four auxiliary modules on conditional stationary profiles are retained as checked algebra outside the papers’ contributions. The [rebuild report](verification/rebuild.json) records the build and axiom audit.

The [basin claim map](paper/basin-lean-claims.md) matches the third paper's numbered results to the [native Lean 4.30.0-rc2 development](formal-basins-native/README.md). Its joint closure contains **1,602 bundled Lean modules, including 281 local proof modules, 1,507 local theorem/lemma declarations, 275 definitions and named instances, and 5 separately audited upstream roots**. The actual first-passage estimates at both scales are connected to density existence, clock laws, and the Green/cylinder identification. Mazur's natural-counting and predecessor inputs are also connected to the natural-density and positivity conclusions. The [joint replay](formal-basins-native/REPLAY-REPORT.md) audits 1,787 declarations using only `propext`, `Classical.choice`, and `Quot.sound`.

The native bundle includes both **α = 1001/1000** and **α = 2001/2000** in one Lean environment. The [original second-scale replay](external/mazur-alpha-2001-2000/REPLAY-REPORT.md) and patch remain available. The joint source preserves the independently named scale and predecessor packages, their licenses, and their provenance. The manifest and report distinguish fresh compilation from exact dependency-checked object reuse; the default command rebuilds every bundled module.

Use the [native bundle instructions](formal-basins-native/README.md) with Lean **4.30.0-rc2** and mathlib **`5450b53e5ddc75d46418fabb605edbf36bd0beb6`**:

```sh
python3 formal-basins-native/verify_replay.py --mathlib /path/to/native/mathlib4 --lean /path/to/lean-4.30.0-rc2/bin/lean --output /new/path/native-basin-build --jobs 3
```

The first two papers use Lean **4.27.0** and mathlib **`a3a10db0e9d66acbebf76c5e6a135066525ac900`**, as described in [formal/README.md](formal/README.md):

```sh
python3 verify.py --mathlib-root /path/to/lean-4.27/mathlib4 --report /new/path/matrix-synchronization.json
```

The earlier [98-module basin development](formal-basins/README.md) is retained for reproducibility and can still be checked with `verify.py --scope basins` under Lean 4.27.0. The current theorem map refers to the native bundle. Every output path must be unused. No SAT-solver result is used as a proof premise.

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

## License and archival releases

The original Lean source, scripts, and documentation use the [MIT License](LICENSE). Imported proof sources in `external/` and `formal-basins-native/source/` retain their own licenses; the [native source-license map](formal-basins-native/SOURCE-LICENSES.md) identifies the Apache-2.0 packages and their separate Mazur, Advameg, and upstream notices. The adapted Sharpe parity module retains its MIT attribution. The papers, including their LaTeX sources and PDFs, use [CC BY 4.0](paper/LICENSE); code excerpts retain their code license. Referenced works and third-party material retain their original rights.

[GitHub releases](https://github.com/x1xhlol/collatz-two-coordinate-obstruction/releases) bundle the three standalone PDFs, sources, and verification reports. Zenodo’s [concept DOI (all versions)](https://doi.org/10.5281/zenodo.23021640) groups deposited releases. Each deposited release has its own version DOI and contains the complete repository with the three separately titled papers. A new GitHub release’s version DOI becomes available after Zenodo finishes archiving it.
