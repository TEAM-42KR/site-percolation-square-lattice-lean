# External finite-certificate data

The large data files are distributed separately from the proof-source repository. `MANIFEST.sha256` contains the fixed SHA-256 digests of the original 6×6 inputs:

- `laws.bin`: exact state-count coefficient tables for the three finite block graphs.
- `region.json`, `group.perm`, `enum.in`: region, boundary-order, graph and symmetry descriptions.
- `params.json`: rational stage parameters.
- `masses_s1.bin`, `masses_s2.bin`: producer mass tables, retained for identification but not trusted as semantic evidence.
- `s1_nodes.bin`, `s1_edges.bin`, `s2_nodes.bin`, `s2_edges.bin`: the two positive integer-flow witnesses.

The stage parameters are `q0 = 5001/10000`, `p1 = 117/200` and `p2 = 79/125`. The comparison direction is reference-boundary law dominated by target-boundary law. Boundary states distinguish a closed singleton from an open singleton and record actual open connectivity, not planar crossing pictures.

## Getting and checking the data

The original 6 x 6 law/flow data accompany the paper at https://doi.org/10.5281/zenodo.23856108. Extract the named files into a directory outside the source repository. This does not supply the separate small-regression bundles. Copy this manifest beside the original 6 x 6 files and run:

```sh
sha256sum --check MANIFEST.sha256
```

A hash match identifies bytes; it is not a proof of C7. The verified Lean checker must establish statewise agreement with the actual Bernoulli boundary law, as well as valid states, automorphisms, all source-positive support, correct exact rounding, increasing edges, per-node flow conservation and sink capacity bounds.

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
