# Exact small native direct-check inputs

Copyright 2026 Sungsoo Na, TEAM42 Inc. Assisted by AI.
Certificate data: CC BY 4.0. The Lean/Python proof-repository sources retain
their Apache-2.0 license. The separate original producer source archive is
MIT-licensed. See the attribution and source pointers below.

## Reference input bytes

This directory supplies twelve binary files, four each in `m2/`, `m4/`, and
`wierman/`, totaling 2,845,792 bytes. They are exact integer-flow
witnesses for the existing small direct-check regression, not a 6 x 6
certificate. `INPUTS.json` lists their sizes and hashes, and
`MANIFEST.sha256` verifies the bytes directly.

The files already start with `R10ANODE` or `R10AEDGE`, as required by the Lean
parser. Do not convert these headers. The `CERT` to `R10A` instructions in
`data/README.md` apply only to the separately distributed 6 x 6 inputs.
The direct checker constructs its laws internally; no producer `laws.bin`,
mass table, producer verdict, or external download is an input to this small
regression. The Wierman-named case uses the exact endpoint
`169873/250000 = 0.679492`; its witness files were generated for this project,
not taken from Wierman's paper.

## Reproduce from the repository root

First install the pinned Lean/Lake dependencies and complete the default
`lake build`. Verify the supplied data:

```sh
(cd data/small-native && sha256sum --check MANIFEST.sha256)
```

Generate pure Lean data and the deterministic malformed-input fixtures
without invoking Lean or native evaluation:

```sh
python3 -B scripts/generate_direct_regression.py \
  --m2 data/small-native/m2 --m4 data/small-native/m4 \
  --wierman data/small-native/wierman \
  --output ../direct-regression-output
```

This writes `../direct-regression-output/GENERATION.json`, verifies lossless
codec replay, and produces `src/SitePercDirectRegressionData.lean` under that
output directory. The reference generated source is 1,824,234 bytes,
with SHA-256 `2ec7435d79b18d3c2f5368d80b33deb35af2a55104680d7bb850b33d87cdf0f8`.
Five negative test cases use seven deterministically generated support
blobs. No additional negative-data download is needed.

To compile the generated data and execute the existing native regression,
run the same command with `--run`:

```sh
python3 -B scripts/generate_direct_regression.py \
  --m2 data/small-native/m2 --m4 data/small-native/m4 \
  --wierman data/small-native/wierman \
  --output ../direct-regression-output --run
```

The expected eight results are:

| Result name | Expected |
|---|---|
| `m2` | `true` |
| `m4` | `true` |
| `wierman1995` | `true` |
| `H1_omitted_nonbottom` | `false` |
| `H1_zero_nodes` | `false` |
| `H2_noncanonical_orbit` | `false` |
| `H2_ignored_high_bit` | `false` |
| `H2_duplicate_key` | `false` |

Expect `all_pass: true` in the terminal summary and `RUN.json`. The run
receipt also records source hashes, `sources_unchanged`, and the native
axioms printed by Lean. Inspect these records separately: `all_pass` checks
the expected result map and input preservation; it does not itself enforce
an independent native-axiom whitelist or the `sources_unchanged` flag.
`data/AXIOM_AUDIT.json` records the fresh native results, input/source
hash bindings and exact axiom lists. `MANIFEST.sha256` and `INPUTS.json`
provide the standalone twelve-input manifest. Generated files, compiled artifacts and logs stay under the
chosen output directory, outside the clone.

## Original producer sources and attribution

The producer code is available in the fixed paper record
`doi:10.5281/zenodo.23870145`, in
`site-percolation-square-lattice-1.1.0-reproduction.zip`:

- `src/make_region.py` and `src/enum_pattern.cpp`: block geometry and laws;
- `src/masses.py`: exact integer rounding at scale `2^100`;
- `src/certflow.cpp`: exact integer-flow witnesses;
- `src/driver.py`: the producer job pipeline.

These are producer-source pointers, not extra trusted inputs to Lean.
The public producer writes `CERTNODE`/`CERTEDGE`; the reference small files
here retain the `R10A` headers of the successful regression inputs.
Different producer builds may choose different valid maximum flows: use the
shipped manifest, not an unverified regenerated witness, when reproducing
these exact reference bytes. Regenerating a valid witness is distinct from
byte-for-byte reproduction of the supplied witness.

Data attribution: Sungsoo Na, TEAM42 Inc., 2026, the above paper record,
CC BY 4.0 (`https://creativecommons.org/licenses/by/4.0/`). The producer
archive contains its MIT `LICENSE`; the proof repository contains its
Apache-2.0 `LICENSE` and `NOTICE`. The twelve reference binaries are local
project-generated numerical data, not downloaded third-party binary files.

These small native executable receipts depend on their printed native
axioms. They are not standard-axiom semantic boundary-domination proofs,
not a completed 6 x 6 direct check, and not a rerun of the shard pipeline.
