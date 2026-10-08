# Collatz basin densities and affine Fourier decay

This repository maintains two papers by Lucas Valbuena, with Lean sources, pinned dependencies, and reproducible verification records.

- [Fourier decay for truncated Syracuse affine laws](paper/growing-deficit-fourier.pdf) · [Source](paper/growing-deficit-fourier.tex) · [Theorem-to-Lean map](paper/growing-deficit-lean-claims.md)
- [Collatz basin densities and canonical traces from first-passage stabilization](paper/tao-basin-densities.pdf) · [Source](paper/tao-basin-densities.tex) · [Theorem-to-Lean map](paper/basin-lean-claims.md)

## Growing-deficit Fourier decay

For independent positive geometric exponents with probability `P(a = j) = 2^(-j)`, let `S_j = a_1 + ... + a_j`. The affine law modulo `3^n` is

```text
Phi_k(z) = sum_(j=1)^k 3^(j-1) * 2^(-S_j) + 3^k * 2^(-S_k) * z.
```

For every fixed natural power `A`, one constant `C_A` bounds every primitive Fourier coefficient by

```text
C_A * ((n - k + 2) / n)^A,    n >= 1, 0 <= k <= n.
```

The bound is uniform in the seed and remains valid after multiplying by any unit-modulus function of `S_k`. Conditioning on a total-exponent slice of probability at least `k^(-B)` therefore preserves decay faster than every fixed inverse power of `k` when `n-k <= k^beta`, for each fixed `0 < beta < 1`. The central slice `S_k = 2k` has mass at least `1/(4k)` for `k >= 1` and satisfies this conclusion for `k >= 4` without an additional mass hypothesis.

The growing deficit and conditioning ranges are the contributions of this paper. Tao's full-length endpoint is credited as prior work; the central-slice comparison with Si concerns his stated logarithmic oversampling range. The proof combines a finite black-triangle obstruction from the Subspace Theorem with a renewal estimate and a conductor recursion. Its constants are ineffective, and it gives no inverse power of the conductor at a fixed positive deficit ratio. These finite random-law results do not prove the Collatz conjecture.

The standalone [Fourier proof bundle](formal-growing-deficit/README.md) rebuilds all 357 bundled application and Subspace modules using Lean **4.35.0-rc3**. Its recipe, source provenance, and verification scope are separate from the Lean 4.30 density bundles below.

The primary replay and recovery contain 1,073 successful commands. All 357 proof modules first passed compilation and individual kernel checking; the generated audit then failed on a legacy-module import incompatibility. After correcting the audit header and import syntax, all 357 compiled proofs were kernel-checked again and the complete audit was compiled and kernel-checked. The recovery saved and verified its full dependency inventory before and after those checks; the initial run had not retained that inventory. The original failed audit is preserved in the evidence. The audit covers 11,718 module/constant rows, with 11,703 distinct constant names and 1,697 encoded private names. A second directory check freshly rebuilt the three entry modules against copied, authenticated dependencies. See the [recorded validation](formal-growing-deficit/recorded/README.md) and [independent automated review](formal-growing-deficit/recorded/independent-review.json) for the exact scope.

## Basin densities and occupation

For the shortcut Collatz map, let `d_N` be the natural density of positive integers whose orbit reaches `N`. The main new result is

```text
d_N >= 3 / (128 * K_seed * N)    for N > 0 and 3 ∤ N.
```

Here `K_seed` is one fixed positive integer, independent of `N`. Every positive target also has an ordinary-map predecessor natural density; for targets prime to three it satisfies the same lower bound. The weighted first-hit density has a uniform reciprocal lower bound, and the canonical trace has a uniform positive lower bound on those targets. The constants are defined by fixed Lean choices; no numerical value or uniform finite-cutoff estimate is asserted.

This establishes the uniform inverse-linear form proposed by [Wirsching](https://doi.org/10.3934/dcds.2003.9.771), including periodic targets. The proof combines Mazur's weighted predecessor construction with Said Duran's coalescence theorem and a periodic averaging argument. The paper credits those inputs separately from Tao's first-passage theorem. It makes no claim of an exhaustive priority search.

A further application gives a uniform bound for exact first-hit coefficients at every positive depth and odd target, including periodic targets. A finite cylinder-energy criterion is equivalent to eventual periodicity of every positive orbit. For any ancestor threshold tending to infinity, the complementary energy is sublinear; the contribution from targets with a small ancestor remains the unresolved condition. Additional cycles also remain unresolved, so these results do not prove the Collatz conjecture.

The first-passage clock also gives a lower bound for the raw occupation trace: for every `b < 1/log(4/3)`, the sum of the actual weighted first-hit densities over odd targets `N ≤ R` is at least `b log R` for all sufficiently large integer `R`. The argument retains the clocks below intermediate barriers and averages a finite set of distinct first visits. A divergent orbit would force a strict additional contribution `D_u/(P_infinity(u) log(3/2))` to that lower coefficient. A matching raw upper bound remains open.

The actual inverse Markov law also has an almost-sure height clock: at each positive odd nonperiodic root prime to three, `log(Y_k)/k → log(4/3)`. The proof constructs the inverse path law from actual predecessor weights and transfers the source clock through fixed finite prefixes. This does not give an expected occupation upper bound or settle forward convergence.

## What is checked for the basin paper

The paper contains 31 numbered results with accompanying Lean statements. Its foundations include natural and logarithmic basin densities, countable label laws, first-hit clock estimates, and identification of the critical Green and stationary-cylinder limits.

The [native foundation](formal-basins-native/README.md) supplies 1,602 Lean modules and its recorded audit of 1,787 declarations. The [density-extension bundle](formal-periodic-census/README.md) rebuilds 51 application modules: 26 from the compatible Gao development, 14 bounded-seed modules, and 11 new density modules. Its completed audit checks all 1,697 compiled constants, including 89 private constants and generated declarations, and runs the kernel checker on each application module. Its required native dependencies are authenticated against the pinned source and replay records before reuse.

The [finite-energy bundle](formal-cylinder-energy/README.md) freshly compiles and individually kernel-checks 17 further application modules. Its audit covers all 193 compiled constants, including generated declarations; none are private. It authenticates and reuses 40 required density-extension modules and 1,566 native modules. The generated audit harness is also freshly compiled and kernel-checked.

The [raw-occupation bundle](formal-raw-occupation/README.md) adds 16 application modules for the occupation lower bound and finite first-hit factorization. Its audit covers all 153 compiled constants, including five private constants and generated declarations. Every application module and the generated audit harness are freshly compiled and individually kernel-checked. It authenticates and reuses 913 native modules.

The [divergent-excess bundle](formal-raw-divergent-excess/README.md) adds eight application modules, with 63 compiled constants including five private constants. It turns the finite first-hit factorization into the conditional strict asymptotic excess. The [inverse-clock bundle](formal-inverse-doob-clock/README.md) adds 26 application modules, with 307 compiled constants and no private constants. Both freshly compile and individually kernel-check every application module and their all-constant audits. They authenticate and reuse the required native and raw-occupation objects.

The logical dependencies of the checked results use only `propext`, `Classical.choice`, and `Quot.sound`. The records distinguish fresh compilation and kernel checking from authenticated reuse. No compiled Lean objects are distributed.

The [artifact manifest](paper/artifact-manifest.json) binds the current paper and verification reports. Automated proof development and review are disclosed in the paper; they are not external peer review.

## Reproduce the proofs

The six basin-paper bundles use Lean **4.30.0-rc2**, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, and Mathlib **`5450b53e5ddc75d46418fabb605edbf36bd0beb6`**. Their manifests pin the package revisions as well.

First rebuild the native foundation using its [instructions](formal-basins-native/README.md):

```sh
python3 formal-basins-native/verify_replay.py \
  --mathlib /path/to/pinned/mathlib4 \
  --lean /path/to/lean-4.30.0-rc2/bin/lean \
  --output /new/path/native-basin-build \
  --jobs 3
```

Then follow the [additive bundle instructions](formal-periodic-census/README.md). Supply the SHA-256 of that successful native replay record with `--native-record-sha256`:

```sh
python3 formal-periodic-census/verify.py \
  --native-bundle formal-basins-native \
  --native-build /new/path/native-basin-build \
  --native-record-sha256 YOUR_VERIFIED_NATIVE_RECORD_SHA256 \
  --lean-bin /path/to/lean-4.30.0-rc2/bin \
  --mathlib /path/to/pinned/mathlib4 \
  --output /new/path/periodic-census-build
```

Follow the [finite-energy bundle instructions](formal-cylinder-energy/README.md), using those two completed replays:

```sh
python3 formal-cylinder-energy/verify.py \
  --native-bundle formal-basins-native \
  --native-build /new/path/native-basin-build \
  --native-record-sha256 YOUR_VERIFIED_NATIVE_RECORD_SHA256 \
  --floor-bundle formal-periodic-census \
  --floor-build /new/path/periodic-census-build \
  --floor-record-sha256 YOUR_VERIFIED_CENSUS_RECORD_SHA256 \
  --lean-bin /path/to/lean-4.30.0-rc2/bin \
  --mathlib /path/to/pinned/mathlib4 \
  --output /new/path/cylinder-energy-build
```

The [raw-occupation bundle](formal-raw-occupation/README.md) needs only the native replay:

```sh
python3 formal-raw-occupation/verify.py \
  --native-bundle formal-basins-native \
  --native-build /new/path/native-basin-build \
  --native-record-sha256 YOUR_VERIFIED_NATIVE_RECORD_SHA256 \
  --lean-bin /path/to/lean-4.30.0-rc2/bin \
  --mathlib /path/to/pinned/mathlib4 \
  --output /new/path/raw-occupation-build
```

The [divergent-excess](formal-raw-divergent-excess/README.md) and [inverse-clock](formal-inverse-doob-clock/README.md) bundles each need the native and raw-occupation replays. For the clock bundle, run:

```sh
python3 formal-inverse-doob-clock/verify.py \
  --native-bundle formal-basins-native \
  --native-build /new/path/native-basin-build \
  --native-record-sha256 YOUR_VERIFIED_NATIVE_RECORD_SHA256 \
  --raw-bundle formal-raw-occupation \
  --raw-build /new/path/raw-occupation-build \
  --raw-record-sha256 YOUR_VERIFIED_RAW_RECORD_SHA256 \
  --lean-bin /path/to/lean-4.30.0-rc2/bin \
  --mathlib /path/to/pinned/mathlib4 \
  --output /new/path/inverse-doob-clock-build
```

For the excess bundle, use `formal-raw-divergent-excess/verify.py` with the same prerequisites and a different new output directory. The raw replay must use the same native replay supplied to these commands.

Each output directory must be new. Each additive verifier recompiles all its supplied application sources. Each bundle states which prerequisite objects and library caches it reuses and how it checks their provenance.

## Build the papers

Both sources are self-contained, including their bibliographies. Use XeLaTeX twice or Tectonic. The basin paper also requires the TeX Live font `DejaVuSansMono.ttf`:

```sh
cd paper
tectonic --keep-logs --untrusted tao-basin-densities.tex
tectonic --keep-logs --untrusted growing-deficit-fourier.tex
```

## Attribution and licenses

The paper credits [Tao's first-passage theorem](https://doi.org/10.1017/fmp.2022.8), Mazur's separate natural-counting and predecessor results, and [Omar Javier Said Duran's Gao formalization](https://doi.org/10.5281/zenodo.23003500). The literature comparison also covers the specified works of Shaik, Nashida, Inselmann, and Tavares. The uniform inverse-linear question is due to Wirsching.

Original code and documentation use the [MIT license](LICENSE). The paper and its source use [CC BY 4.0](paper/LICENSE). Imported and adapted formal sources retain their own licenses and notices; see the [native source-license map](formal-basins-native/SOURCE-LICENSES.md), [density-extension source-license map](formal-periodic-census/SOURCE-LICENSES.txt), [energy-extension source-license map](formal-cylinder-energy/SOURCE-LICENSES.txt), [occupation-extension source-license map](formal-raw-occupation/SOURCE-LICENSES.txt), [excess source-license map](formal-raw-divergent-excess/SOURCE-LICENSES.txt), and [inverse-clock source-license map](formal-inverse-doob-clock/SOURCE-LICENSES.txt). They are not relicensed as original local work.

The publication set was narrowed to the basin paper on 3 October 2026 and subsequently expanded with the growing-deficit Fourier result. Earlier standalone papers and superseded Lean developments remain in [repository history](https://github.com/x1xhlol/collatz-two-coordinate-obstruction/commits/main/) and [previous releases](https://github.com/x1xhlol/collatz-two-coordinate-obstruction/releases). Their removal from the current collection is an editorial choice, not a claim that their checked results were false. The repository URL is retained for existing citations. The Fourier bundle has its own [third-party notices](formal-growing-deficit/THIRD_PARTY_NOTICES.md), including the incorporated Advameg and Ralf Stephan formalizations.
