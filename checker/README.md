# Finite regional enumeration and checker (partial formalization)

Build the shared Lake project with `lake build siteperc_checker`. The executable
is `.lake/build/bin/siteperc_checker`; its IO layer only loads files and emits
receipts. Large certificate inputs and generated evidence are not part of the
public source bundle. The default library build does not run this executable.

```sh
.lake/build/bin/siteperc_checker certify 2 1 "$DATA/laws.bin" \
  "$DATA/s1_nodes.bin" "$DATA/s1_edges.bin" \
  "$DATA/s2_nodes.bin" "$DATA/s2_edges.bin"
```

Use the certificate format and exact parameter selection in `Exec.lean`.
`flow` skips C7 and must never be presented as a full law verification. The
`wierman1995` final argument selects the exact small-block regression endpoint.

The generic union-find, bounded-cached parallel coefficient path, byte-checker
soundness and actual boundary-domination semantics are proved in Lean under
standard axioms. `LawProbability.lean` connects checked coefficients to the
finite Bernoulli law. The direct-law checker constructs its regional laws
internally; the stored flow bytes alone do not certify those laws.

The 2 x 2, 4 x 4 and Wierman small pure-data targets have completed with the
explicit native-computation axioms recorded in `data/AXIOM_AUDIT.json`. Saved
shard regressions separately cover a full 2 x 2 merge and one 4 x 4 piece.
The actual 6 x 6 D1/D2 obligations and the final instantiated site/road targets
remain unfinished. Executable PASS alone is not a concrete Lean theorem.

`regression.py` accepts external input/output directories, leaves inputs
unchanged, and checks the small positive regressions and H1/H2 counterexample
patterns. `Audit.lean` prints selected generic proof dependencies. Public
axiom and partial native receipts are in `data/`; external data requirements
are documented in `data/README.md`. `SOURCE_MANIFEST.json` identifies the
source snapshot; hashes do not certify computation or close an unfinished
theorem. See the root `README.md` for the precise trust boundaries.
