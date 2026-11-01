# Square-lattice site percolation: partial Lean formalization

**Release v1.1.0 is a PARTIAL formalization, not a completed Lean proof of the
6 x 6 site bound. The concrete boundary dominations D1 and D2 remain explicit
hypotheses.** The paper checks these comparisons using two independent exact
programs; that external verification is not a completed Lean computation.

- **Kernel-checked (standard axioms only):** the general substitution theorem
  in infinite-cluster-existence form; finite Strassen; flow-certificate
  soundness; D4 orbit lift; line-graph equivalence; reduction to the origin;
  the general road Theorem 1.2 and Corollary 1.3 with five named classical inputs;
  enumerator refinement; disjoint shard partition and merge; and checker
  semantics. The improved numerical road consequences still require D1/D2
  through the conditional site bound.
- **Small native checks only:** 2 x 2, 4 x 4, and Wierman's 0.679492 endpoint.
  These use explicitly disclosed native-computation axioms, not just the
  three standard axioms, and do not discharge the 6 x 6 obligations.
- **Not closed in Lean:** the actual 6 x 6 D1 and D2 computations, the final
  Kesten-only site-bound theorem, and its fully instantiated numerical road
  corollary. A clean default build below checks the general theory only.

**Author:** Sungsoo Na, TEAM42 Inc., Seoul, Republic of Korea.  
**Acknowledgment:** Assisted by AI.  
**License:** Apache-2.0; see `LICENSE` and `NOTICE`.

**Paper:** [The site percolation threshold of the square lattice is at most
0.632, and one random completion per cell creates a giant cluster](https://doi.org/10.5281/zenodo.23856108).
This DOI identifies the already published paper v1.0.0. The repository's
v1.1.0 tag identifies this partial-formalization release; it does not change
that paper record or assert that a new paper version has been published.

## What is proved, and what is conditional

The concrete nearest-neighbour square-lattice site target is
`pcSite <= 79 / 125`. The two-stage comparison uses `q0 = 5001/10000`,
`p1 = 117/200`, and `p2 = 79/125`.

`SitePerc.site_upper_of_boundary_domination` proves the site bound from
`SitePerc.KestenAboveHalf` and `SitePerc.TwoStageBoundaryDominations`.
The latter exposes exactly D1 and D2 at the actual 6 x 6 parameters; it is
not silently discharged or introduced as a new axiom. General substitution
compares the **existence of an infinite cluster**, not theta at an arbitrary
interior vertex. `SitePerc.square_exists_to_origin` supplies the origin step.

For the random-completion model, cells are sampled uniformly, independently
and with replacement. For counts `m(n)/n^2 -> c > 0`, put
`rho(c) = 1 - exp(-c)`. The general road theorem gives the positive limiting
giant-cluster density above `pcSite` and a logarithmic largest-cluster bound
below it. The numerical consequence at `c = 1` requires the unresolved
site-bound input. The actual occupancy law and iid sandwich are proved,
not extra percolation assumptions.

### Five explicitly named classical inputs

These are theorem arguments or structures, never custom axiom declarations:

1. Kesten's strictly supercritical square-bond direction, above 1/2.
2. Supercritical square-box largest-cluster density.
3. Continuity of theta above the site critical probability.
4. Subcritical exponential cluster-volume tail.
5. The van den Berg-Ermakov (1996) lower bound `pcSite > 0.556`, used only
   for the lower critical-completion-time corollary.

Only input 1 enters the conditional site bound. The road assembly
`SitePercUpper.Lean.RoadMain` takes density, continuity, tail, lower bound
and a site-bound theorem as arguments; obtaining its improved site-bound
argument from this repository additionally requires Kesten and D1/D2.
No empirical estimate of the site critical probability is asserted as a
proved input or conclusion.

## Clean build and reproduction

Install elan and git, then clone this release and run from its root:

```sh
git clone https://github.com/TEAM-42KR/site-percolation-square-lattice-lean.git
cd site-percolation-square-lattice-lean
git checkout v1.1.0
lake exe cache get
lake build
```

`lean-toolchain` pins Lean v4.35.0; `lake-manifest.json` locks Mathlib and
its dependencies. Do not run `lake update` when reproducing the pinned
release. The default `SitePerc.lean` umbrella imports general theory and
checker semantics, including `ShardedSoundness`, but **does not import
`SitePerc.Final` or any external concrete certificate data**. Its successful
build is not verification of the final 6 x 6 result.

## Exact axiom results

The kernel axioms permitted here are exactly
`[propext, Classical.choice, Quot.sound]`. For the completed general
declarations the recorded `#print axioms` lists contain only those axioms;
no `sorryAx` or custom mathematical axiom is hidden in the general theory.
For example, the exact recorded list for each of
`SitePerc.site_upper_of_boundary_domination` and
`SitePercUpper.Lean.RoadMain` is the three-element list above.

The complete per-declaration lists and corresponding source hashes are in
`data/AXIOM_AUDIT.json`. Reproduce selected prints after `lake build`:

```sh
python3 scripts/audit_axioms.py --module SitePerc.Flow --theorem SitePerc.flow_implies_domination --source-file SitePerc/Flow.lean
python3 scripts/audit_axioms.py --module SitePerc.Conditional --theorem SitePerc.site_upper_of_boundary_domination --theorem SitePerc.substitution_exists --source-file SitePerc/Conditional.lean --source-file SitePerc/Substitution.lean
python3 scripts/audit_axioms.py --module SitePerc.Road --theorem SitePercUpper.Lean.RoadMain --theorem SitePerc.road_theorem12a --theorem SitePerc.road_theorem12b --theorem SitePerc.road_corollary13ab --source-file SitePerc/Road.lean
python3 scripts/audit_axioms.py --module SitePerc.Checker.DirectSoundness --theorem SitePerc.Checker.directRegionalLaws_exact --theorem SitePerc.Checker.directRegionalPass_boundary_stages --source-file SitePerc/Checker/DirectSoundness.lean
```

The script requests actual Lean `#print axioms` output, fails on missing
targets, and rejects additional axioms unless each is explicitly allowed.
The direct small regressions have eight disclosed native axioms; the saved
shard/flow receipts add eight more. Each list records its standard axioms
and the additional native axioms separately.
The exact names are recorded, not inferred from status labels. The final
6 x 6 target audits are **unavailable**, not empty axiom sets.

## Finite data, small native checks, and shards

`data/MANIFEST.sha256` and `data/FLOW_MANIFEST.sha256` identify the original
6 x 6 law/flow data, distributed separately with the paper. The Lean direct
checker constructs laws internally; its only external computation inputs
are the four flow-certificate byte arrays. Matching file hashes or binomial
totals alone does not prove the boundary law or D1/D2.

Small direct-law regressions cover 2 x 2, 4 x 4 and
`169873/250000 = 0.679492`, plus five malformed-input negatives. Their
execution theorems require the native axioms recorded in
`data/AXIOM_AUDIT.json`. Given the separate small flow-input bundles:

```sh
python3 scripts/generate_direct_regression.py --m2 "$M2_DATA" --m4 "$M4_DATA" --wierman "$WIERMAN_DATA" --output ../direct-regression-output --run
```

The small bundles are not in this repository; a clean default build does
not rerun them. Do not substitute the 6 x 6 data for these inputs.

`SitePerc.Checker.ShardedDefs` and `ShardedSoundness` implement a disjoint,
clipped boundary partition, coefficientwise refinement and exact saved-map
merge. The generic proofs use only standard axioms. Native piece theorems
are separate. The recorded saved-data regression covers all six 2 x 2
pieces and their merge, and one 4 x 4 piece, not a full 4 x 4 or 6 x 6
sharded calculation. See `INTERFACE_L2_A.md`, `INTERFACE_L2_B.md`,
`checker/sharded/USAGE.md` and `data/L2_SHARDED_SUPPORT.json`.

The original monolithic 6 x 6 attempt ended without a success witness;
the later shard profile did not complete the required native evaluations.
Neither outcome is a false checker result or a mathematical refutation.
Portable outcomes are in `data/NATIVE_EXECUTION.json` and
`data/L2_PROFILE.json`. Raw execution and infrastructure records are not
part of the public proof source.

`SitePerc/Final.lean` is an **optional, unverified target source**, excluded
from the default umbrella. Its native decision and final declarations have
not successfully compiled on the concrete 6 x 6 data. Generating or reading
that source is not a proof receipt. See `data/README.md` for the attempt-only
recipe and the explicit missing-data boundary.

## Source snapshot

`SOURCE_MANIFEST.json` lists SHA-256 and byte length for every distributed
file except itself. Packaging changes do not alter any Lean source, proof
or theorem statement. To make a portable source-only export:

```sh
python3 scripts/export_source.py --output ../site-perc-public-source
```
