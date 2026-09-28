# Joint native replay

Status: **PASS**. The final combined source closure contains 1602 bundled modules and audits 1787 declarations. All audited roots use at most `propext`, `Classical.choice`, and `Quot.sound`.

The final run freshly compiled 847 modules and validated 755 previously compiled modules against their exact source hashes, transitive dependency fingerprints, object hashes, and compiler/dependency pins. The root audit was compiled afresh. The [default verification command](README.md) rebuilds every bundled module.

| Artifact | SHA-256 |
| --- | --- |
| Final replay manifest | `efc8bc1226fb158341a4626eeafaf5c97b9284da1a2d137de38b7db035cbb230` |
| Final replay record | `260930d45985dca3d8b7abe88fff1c8c73aa154893d5fa1476b5c76b0b70a79c` |
| Root audit source | `41c885cad755ee724ba65909f380cc2e8937ac2134fe9dffe669ce8fcd8f40c9` |
| Root audit output | `7d4cfdedc0e33351a1318fe217ae9e20b1b69819dea0618003eee2f229cddd5f` |

The [retained replay records](provenance/replays) document the preceding fresh checks and incremental assemblies. The original first-scale/natural-density replay rebuilt 578 modules, the namespaced second-scale replay rebuilt 382, the predecessor replay rebuilt 388, and the first joint native replay rebuilt 858. Later records identify each additional freshly compiled module and each validated reused object. Their recorded absolute build paths describe the original runs; reproduction uses the complete sources in this bundle and the paths supplied to the verifier.

No assertion of global sublinearity, universal eventual periodicity, exclusion of additional cycles, or the Collatz conjecture follows from this audit.
