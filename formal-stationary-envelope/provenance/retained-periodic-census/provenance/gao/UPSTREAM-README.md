# Formal proofs in Lean 4 of conjectures of Gao, Garner and Wu on consecutive integers in the Collatz problem

Version 1.0.0, 27 September 2026.
Omar Javier Said Duran, Independent Researcher,
ORCID [0009-0009-1418-2558](https://orcid.org/0009-0009-1418-2558).
Archive: [doi:10.5281/zenodo.23003500](https://doi.org/10.5281/zenodo.23003500).

This archive is the formal artifact of three papers:

- **I.** *Consecutive integers coalesce with density one under the Collatz
  map: a formally verified proof of a conjecture of Gao*,
  [doi:10.5281/zenodo.23003524](https://doi.org/10.5281/zenodo.23003524).
- **II.** *Arbitrarily long runs of consecutive integers with the same
  Collatz height*,
  [doi:10.5281/zenodo.23003526](https://doi.org/10.5281/zenodo.23003526).
- **III.** *On two conjectures of Wu on consecutive integers of the same
  height in the Collatz problem*,
  [doi:10.5281/zenodo.23003528](https://doi.org/10.5281/zenodo.23003528).

Throughout, `C(n) = n/2` for even `n` and `C(n) = 3n+1` for odd `n`.
Nothing in this archive proves the Collatz conjecture: apart from the runs
that are built explicitly in paper II, no statement here says that an
integer reaches 1.

## Main theorems

All files below are in `depuracion/gao20260920/formal/`.

| Paper | Statement | Lean declaration | File |
|---|---|---|---|
| I, Theorem A | the set of `n` with `C^k(n) = C^k(n+1)` for some `k ≤ log₂ n` has natural density one (Gao's conjecture as recorded by Lagarias) | `GaoEnunciado.conjetura_gao` | `GaoEnunciado.lean` |
| I, Theorem B | Gao's literal form: `d̄_k → 1` and `d(x) → 1` | `GaoLiteral.conjetura_gao_literal` | `GaoLiteral.lean` |
| I | Lagarias's form restated without importing the project, and proved from `conjetura_gao` | `GaoLiteral.lagarias` | `GaoLiteral.lean` |
| II, Theorem 1.1 | for all `L, N` there is `n ≥ N` such that `n, …, n+L` have the same height and the same total stopping time (Garner's conjecture) | `GarnerEnunciado.conjetura_garner` | `GarnerEnunciado.lean` |
| III, Theorem A | the longest run of equal height in `[1, M)` tends to infinity (Wu's second conjecture) | `WuEnunciado.conjetura_wu_dos` | `WuEnunciado.lean` |
| III, Theorem B | `d(M) → 1` (Wu's first conjecture) if and only if the integers that reach 1 have natural density one | `WuEnunciado.conjetura_wu_uno` | `WuEnunciado.lean` |

The statement files are short and are meant to be read against the papers.
`Hienas.lean` imports only Mathlib and contains Gao's definitions
(coalescence, `d̄_k`, `d(x)`) used in Theorem B.

`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`
for these six theorems. The sources contain no `sorry`, `admit`,
`native_decide`, declared axioms, `extern` or `implemented_by`. The commands
`#guard` in the statement files (Gao's Table 3 for `4 ≤ k ≤ 12`; runs of Gao,
Penning and Wu; `K(2^10) = 620`) are evaluated by the interpreter, and no
theorem depends on them.

## Building

Lean 4.32.2 (`lean-toolchain`) and Mathlib commit
`905b95818eb32af7874a58b427f50c1711a5e96c` (`lake-manifest.json`) are pinned.
With [elan](https://github.com/leanprover/elan) installed:

```text
cd depuracion/gao20260920/formal
lake exe cache get
lake build GaoCore GaoFormal
```

The library `GaoCore` reads `../cadena_completa.lean` and `MangostasCore`
reads `../../frente20260910/rachas.lean`, so the directory layout of the
archive must be kept. The directory names come from the author's working
repository (*depuracion* means refinement, followed by a date).

On 27 September 2026 this archive was extracted and built exactly as above,
with the Mathlib cache, and the build completed successfully (1615 jobs).
On Windows, extract it into a short path such as `C:\src`: Lake creates deep
paths inside `.lake`, and a long base path can exceed the limit of 260
characters.

`depuracion/gao20260920/evidencia_gao_lean.json` records the build of
26 September 2026 (`Build completed successfully (1615 jobs)`, Lean 4.32.2 on
Windows), the SHA-256 hashes of the final modules and of the build files, the
output of `#print axioms`, and the runs of `leanchecker`, which replayed each
of the 30 modules with exit code 0. The Lean files of this archive have those
hashes.

## Modules

The identifiers and comments of the sources are in Spanish. The modules in
`formal/` form the library `GaoFormal`.

| Module | Content | Paper |
|---|---|---|
| `cadena_completa` (library `GaoCore`) | the transition `P` of the chain of pairs | I, Table 1 |
| `rachas` (library `MangostasCore`), `RachasEnteras`, `UmbralRachas`, `Reloj` | runs of shared steps, the dyadic threshold, the block clock | I, (7)–(9) |
| `Momentos`, `Maximos` | square-root drift, finite maxima | I, (4) |
| `Resto`, `Producto` | affine identity of an excursion, product bound | I, §3.3 |
| `Supervivencia`, `Banda` | survival `1/(t+1)`, tail of the mixed steps | I, (5), (6) |
| `Palabras`, `SalidaPalabras`, `Ventana`, `ParametrosVentana` | the exit window | I, Prop. 3.2 |
| `Hormigas`, `Ensayo` | universal absorbing word, one trial | I, Props. 3.3, 3.4 |
| `Repeticion`, `Guardias`, `ConteoEnsayos` | guarded trials | I, Prop. 3.5 |
| `Lagartijas` | few admissible entries, the bound `CF_F` | I, Prop. 3.6, (10) |
| `Martas` | almost sure absorption, `P(σ > h) → 0` | I, Thm. 3.1 |
| `Tejonas` | pairs of integers, transport to residue classes, density one | I, §2, Thm. 4.1 |
| `GaoEnunciado` | Theorem A | I |
| `Hienas` | Gao's definitions and the bridge lemma | I, Lemma 5.1 |
| `GaoLiteral` | Theorem B | I |
| `Alpacas` | block of merged residues, 2 is a primitive root modulo `3^k`, runs | II |
| `GarnerEnunciado` | Theorem 1.1 | II |
| `Condoras` | Wu's two conjectures | III |
| `WuEnunciado` | Theorems A and B | III |

Several module names are animal names that the author gives to results
(*tejonas* badgers, *martas* martens, *hienas* hyenas, *lagartijas* lizards,
*hormigas* ants, *condoras* condors). Glossary of other words:
*enunciado* statement, *altura* height, *mitades* halvings,
*llega* reaches, *encuentro* meeting, *coalescen* coalesce,
*enUpla* in a run, *uplaEn* run inside, *proporcionLlegan* proportion that
reach 1, *cadena* chain, *resto* remainder, *producto* product,
*supervivencia* survival, *reloj* clock, *palabras* words, *ventana* window,
*ensayo* trial, *guardias* guards, *conteo* count, *rachas* runs,
*umbral* threshold.

## Numerical checks

The folder `checks/` contains the independent Python programs (they need
`numpy`, except `verificar_alpacas.py` and the `verificar_lagartijas*`
scripts) of the numerical checks reported in the papers, with their saved
outputs. They do not use the Lean code. Run them with
`python -B -X utf8 <script>.py`. These are finite checks of the definitions
and of the reading of the statements; the universal statements rest on the
Lean proofs.

| Script | What it checks | Paper | Saved output |
|---|---|---|---|
| `revision_gao.py` | Gao's Tables 3 and 2 with the definitions of `Hienas.lean`; the bridge lemma for `n < 2^22`; the density of meetings | I, §6.3, §7 | `revision_gao_salida.txt`; `tabla2_1e8_salida.txt` (with `X_TABLA2 = 8`, about 20 minutes) |
| `verificar_lagartijas.py`, `verificar_lagartijas_pares.py` | the chain of pairs against the 262144 pairs `(n, n+1)` with `2^18 ≤ n < 2^19` | I, §6.3 | `evidencia_lagartijas_exacta.json`, `evidencia_lagartijas_pares.json` |
| `revision_garner.py` | the runs built by the proof (Table 1), A078441(1..40), Gao's Table 1 | II, §7 | `revision_garner_salida.txt` |
| `verificar_alpacas.py` | the same construction by another route; a sample of Gao's run of 35654 integers from `2^500+1` | II, §7 | `verificar_alpacas_salida.txt` |
| `revision_wu.py` | `K(2^N)`, `d(2^N)`, `L(2^N)`; coalescence gives the same height for `n < 2^20`; Gao's question | III, §4; I, §7; II, Remark 9.2 | `revision_wu_salida.txt` (`N_MAX = 22`); `revision_wu_n24_salida.txt` (`N_MAX = 24`) |
| `terminos_oeis.py` | `K(2^N)` and `L(2^N)` for `N ≤ 26`, and `2^k d̄_k` for `k ≤ 28` | III, §4 | `terminos_oeis_salida.txt` |

`revision_wu.py` imports `revision_gao.py`, and `verificar_lagartijas_pares.py`
imports `verificar_lagartijas.py`. `terminos_oeis.py` and the
`verificar_lagartijas*` scripts write their output files next to themselves.

## License

Copyright 2026 Omar Javier Said Duran. The contents of this archive are
distributed under the Apache License 2.0 (`LICENSE`), the license of Mathlib.
The papers are distributed separately under CC BY 4.0.

## Use of AI tools

The formalization and the checks were produced with extensive assistance
from large language models of Anthropic's Claude family (Claude Opus 5.5 for
the final results; Claude Opus 5 and Claude Fable 5 in earlier stages), as
declared in the papers. Every theorem listed above is checked by the Lean
kernel.

## How to cite

O. J. Said Duran, *Formal proofs in Lean 4 of conjectures of Gao, Garner and
Wu on consecutive integers in the Collatz problem*, software, version 1.0.0,
Zenodo, 2026. doi:10.5281/zenodo.23003500.
