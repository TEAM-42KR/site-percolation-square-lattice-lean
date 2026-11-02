# External finite-certificate data

The large data files are distributed separately from the proof-source repository. `MANIFEST.sha256` contains the fixed SHA-256 digests of the original 6×6 inputs:

- `laws.bin`: exact state-count coefficient tables for the three finite block graphs.
- `region.json`, `group.perm`, `enum.in`: region, boundary-order, graph and symmetry descriptions.
- `params.json`: rational stage parameters.
- `masses_s1.bin`, `masses_s2.bin`: producer mass tables, retained for identification but not trusted as semantic evidence.
- `s1_nodes.bin`, `s1_edges.bin`, `s2_nodes.bin`, `s2_edges.bin`: the two positive integer-flow witnesses.

The stage parameters are `q0 = 5001/10000`, `p1 = 117/200` and `p2 = 79/125`. The comparison direction is reference-boundary law dominated by target-boundary law. Boundary states distinguish a closed singleton from an open singleton and record actual open connectivity, not planar crossing pictures.

## Getting and checking the 6 x 6 data

The paper data are public at the [concept DOI (latest)](https://doi.org/10.5281/zenodo.23856107)
and the [v1.1.0 record](https://doi.org/10.5281/zenodo.23870145). Follow that
record's README to reassemble and extract the certificate archive and
reproduction ZIP. Check the public `SHA256SUMS` **before any conversion**.
The twelve small-native inputs are included separately in this repository;
see `small-native/README.md` and the root README.

### Public `CERT` headers versus Lean `R10A` headers

The public four flow files start with `CERTNODE` or `CERTEDGE`. The Lean
parser expects `R10ANODE` or `R10AEDGE`. Only the first four bytes differ:
replace `CERT` by `R10A`; every byte from offset 4 onward is identical.
Do this only to separate copies, never the downloaded public files.
The procedure and paired hashes below match the Zenodo v1.1.0 README.

After unpacking the public reproduction ZIP and certificate archive, run
from their common root. Set `REPO_DIR` to the absolute path of this clone:

```sh
sha256sum --check SHA256SUMS
mkdir lean-input
cp certificates/s1_nodes.bin certificates/s1_edges.bin certificates/s2_nodes.bin certificates/s2_edges.bin lean-input/
for f in lean-input/s1_nodes.bin lean-input/s1_edges.bin lean-input/s2_nodes.bin lean-input/s2_edges.bin; do printf 'R10A' | dd of="$f" bs=1 count=4 conv=notrunc status=none; done
(cd lean-input && sha256sum --check "$REPO_DIR/data/FLOW_MANIFEST.sha256")
```

Each original public file must first match the `CERT...` hash and each
converted copy must then match the `R10A...` hash. The four conversions
leave the lengths and bytes at offsets 4 onward unchanged.

| File | SHA-256 in this record (`CERT...`) | SHA-256 after the conversion (`R10A...`) |
|---|---|---|
| `certificates/s1_nodes.bin` | `8270fb6b60fa492b0e30799cfbc609cd172c2e053e7811f0e7b3f68fa590ea1e` | `0f76669abe031a96daae331e26b940ef132c684e7d45feff7623f1cbc127a79f` |
| `certificates/s1_edges.bin` | `93d1cf2cd14932a863d2210df0c57fded09da7ea80e49ca153f7858480c68adf` | `3a63c78164d5ae41d598a59d3310da658f4bb44eecde21da973c75a5475cedd2` |
| `certificates/s2_nodes.bin` | `3491a3f16b3234dbec52a574e6f09942e04a75b0a6516bb9dffb1afe04e7296e` | `75b808ec2b15737a8b5ccdee72966079328b4a9bada8dea77a6ac8219949a6e7` |
| `certificates/s2_edges.bin` | `2358aa13a7a52213b971913f5ffb27f85e188c45f1f6dde55a4deff3f5f118b1` | `3281cb7c5e16bba814ea0434fb687f8afe1c8ce56fc3d22c50831ce40ce0af24` |


`MANIFEST.sha256` lists these same four converted hashes; its other seven
entries agree with the public `SHA256SUMS`. To verify all eleven Lean-format
inputs, copy the other seven unchanged files from `certificates/` alongside
the converted four, then run `sha256sum --check "$REPO_DIR/data/MANIFEST.sha256"`
from that directory. Do not apply the converted manifest directly to the
unmodified public `CERT...` files.

A hash match identifies bytes; it is not a proof of C7. The verified Lean
checker must establish statewise agreement with the actual Bernoulli
boundary law, valid states, automorphisms, source-positive support, exact
rounding, increasing edges, flow conservation and sink capacity bounds.

## Exact four-flow input subset

The direct Lean path does not read `laws.bin` or the producer mass tables. Its only external inputs are the four exact flow byte arrays. `FLOW_MANIFEST.sha256` lists their original SHA-256 values; the general enumerator proves C7 and generates the laws internally.

## Recorded execution outcome

The full pure-data preparation completed and all input/chunk roundtrips matched the original bytes. The single final native target attempt then reached its fixed work cap without a success witness. `NATIVE_EXECUTION.json` records that timeout; `AXIOM_AUDIT.json` records the exact completed general and small-native audits. No final two-target audit or completed C7 value exists. The public receipts retain computational outcomes, not infrastructure records.

## Restartable shard data and trust

The L2 runtime can produce disjoint C7 shards as pure literal maps with individual
native-check theorems and hash-bound compiled artifacts. See
`checker/sharded/USAGE.md` and `INTERFACE_L2_A.md`. The complete merge consumes saved
maps and verified imports without re-enumerating completed pieces. Missing pieces
remain missing, and different runtime pins cannot be adopted.

The completed saved regression is the full m2 six-piece merge and stored-law flow
checks, with one additional m4 piece, not a full m4 or m6 calculation.
`AXIOM_AUDIT.json` includes the seven standard-axiom generic shard theorems and the
exact additional native axioms from the completed small runs. Full6 final target
audits remain unavailable. Hash manifests identify observed data/artifacts against
the selected trusted snapshot; they do not prove C7 or authenticate malicious
replacement of an entire manifest.

`L2_PROFILE.json` records that the actual profile was partial and did not
complete the separated native evaluations. `NATIVE_EXECUTION.json` retains
the monolithic timeout and a separately named shard-stage outcome; neither
is a successful 6 x 6 reproduction.

## Attempt recipe, not a successful reproduction

After obtaining the external files and independently estimating the required computation, the following describes the same pure-byte/direct-law route. It must not be treated as a successful proof-reproduction transcript. `CERT_DIR` is the external directory containing the four original flow files; generated modules remain outside this repository at the path declared by `lakefile.toml`.

```sh
PROJECT_DIR="$PWD"
(cd "$CERT_DIR" && sha256sum --check "$PROJECT_DIR/data/FLOW_MANIFEST.sha256")
python3 checker/encode_compact_certificate.py --input-dir "$CERT_DIR" --all-bytes --source-manifest data/FLOW_MANIFEST.sha256 --output-dir ../lean-data/g/compact_bytes --module SitePercCompactCertificateData --chunk-bytes 16384 --chunks-per-module 32 --receipt ../flow-encoding.json
lake build SitePercCompactCertificateData
python3 scripts/generate_final_target.py --workers 192
lake --no-cache build SitePerc.Final
```

The last command was attempted once and did not finish within the recorded cap. A future successful build would print its exact native axiom name. Only after observing that output should the two final targets be audited with `scripts/audit_axioms.py`, passing each printed native axiom individually through `--allow-native`. Do not assume an axiom name, reuse a small-block receipt as a large-block proof, or omit the final audit.
