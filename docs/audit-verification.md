# Verification trust review

Baseline: `29fad6d4d3a68fbd806525034e8d07cd373f3d4c`; review branch
`codex/paper-proof-audit`. Commands run only in the isolated paper-audit
worktree. This review checks the verification mechanism separately from
paper correspondence.

## Independently observed pins and baseline

- Lean `leanprover/lean4:v4.34.1`, reported commit
  `5045d0056413266e57c625dcd7c365b10e377c52`, arm64-apple-darwin24.6.0.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All nine packages match `lean/lake-manifest.json` revisions; their tracked
  sources are clean. All 51 vendored sources match `UPSTREAM_MANIFEST.json`.
- Dependencies and initial project artifacts were APFS-cloned into this
  worktree's own `.lake`. Lake resolves paths here, not in the primary
  checkout. No project artifact is shared for writing.
- The baseline exact-target guard succeeded. Both
  `ExactFourierCircuits.UniformFinalDFTExecution.execution` and `.uniformDFT`
  report only `propext`, `Classical.choice`, `Quot.sound`.
- Historical receipt SHA256:
  `d6ebf13364d4d0c4af24b7e73fc40af379ca9aee8725ba0b7bade759cdc7374e`.
  Its exact bytes are preserved in
  `verification/history/uniform-final-algorithm-pre-paper-audit.json`.
  It does not certify the annotated sources.

## What the canonical check establishes

`./scripts/verify-uniform.sh` dispatches to `verify-uniform-final.py` when
`UNIFORM_CHECKS.json` names the closed theorem. The driver checks pins, freezes
all registered project sources/configuration, computes their import closure,
and stages sources into an isolated directory. Normal reuse requires matching
compiler, external artifacts, certified source/import/artifact bytes, and
transitive dependency eligibility. A changed dependency invalidates every
consumer. `--rebuild-all` disables project reuse altogether.

The build invokes Lean with `-DautoImplicit=false`, checks resolved dependency
paths, and hashes each resulting `.olean`. The final source is compiled again
in the normal project environment. The census uses each declaration's
**defining module**, rather than just a public namespace prefix, and
`collectAxioms`; this includes private and generated declarations. It requires
an exact match to the registry's declaration set. The exact target guard checks
that the closed theorem inhabits
`UniformMachine.UniformDFTStatement UniformExponent.theta`, and prints axioms
for both the statement and its actual-execution theorem. The driver checks
sources/configuration, external artifacts and project artifacts again after
these checks before writing the new source/artifact-bound receipt.

The source-policy scan rejects admissions, custom axiom declarations,
`native_decide`, and newly raised proof limits. Seven historical source files
have exact-hash exceptions for existing limit settings:
`GateFrames`, `TripleInvocationFrames`, `TripleSchedule`,
`UniformAllAxisSeedPreparation`, `UniformGlobalLocalPreparation`,
`UniformLocalSeedTableMachine`, `UniformNewtonTableMachine`.
They remain byte-identical in this review. “Default driver limits” does **not**
mean these seven sources have no local settings.

## Trust boundary and limits

The check relies on the installed Lean compiler/kernel, its elaborator/runtime,
the operating system, Python verification driver, and external dependency
artifacts. Package source pins and artifact hashes identify inputs; they do not
rebuild Lean or Mathlib from first principles. No separate `leanchecker` replay
or independent kernel implementation is claimed. Axiom collection does not
prove that a formal definition is the intended mathematical or machine model.

The registry is a source/declaration inventory, not a proof of paper adequacy.
Refreshing a comment-changed source hash is legitimate only together with
fresh compilation of the invalidated dependency cone and a new census/guard;
copying old receipt hashes would not establish that result. Historical import
and coherent-source receipts remain untouched, as provenance for eligible
unchanged artifacts rather than certificates for new sources.

No astronomical seed, saving-role array or full numerical execution is
materialized. Universal correctness is established by the Lean proof of
executions in the stated exact-arithmetic semantics, not a benchmark of the
resulting enormous program. There is no deployment or publication in this
review.

## Focused stale-artifact control

Before refreshing the source registry, the canonical command was run on the
annotated tree with the old registry and cloned old project artifacts. It
failed as expected with `Normal project source differs from registry:
UniformMachine`, before any proof build or final receipt overwrite. This
reproduces the source-binding boundary rather than assuming it from the code.

## Result on the annotated tree

The canonical command completed successfully:

```sh
./scripts/verify-uniform.sh --rebuild-all --jobs 4 --output logs/paper-audit/rebuild-v2
```

- All 1,271 project modules compiled freshly; project-artifact reuse: **0**.
- Fresh normal Main compile and exact closed-target guard: **passed**.
- Defining-module census: **82,513** closures, comprising 79,030 public/generated
  and 3,483 private; only the three standard axioms occur.
- Final source/configuration/external/project artifact checks: **passed**.
- [Canonical receipt](../verification/uniform-final-algorithm.json) SHA256:
  `2ac6d22ee5292260ab17217619c2ea19f9ef488013696a8174bb22ed52ab637b`.

An independent rehash checked every receipt entry: 1,271 sources, 13 configuration
entries, 1,271 normal project artifacts, 11,265 external artifacts and eight check
artifacts. It also revalidated the held inventory and all 175 annotated source
hashes. The [cross-check receipt](../verification/paper-audit-crosscheck.json)
records these observations. External Lean/dependency artifacts were hashed,
not rebuilt by this run.

`UniformDiagonal` and `UniformCRTTransferMachine` are outside the final import
closure. Both compiled freshly against the newly verified dependencies, and a
separate defining-module census passed all **146** declarations (zero private),
with standard axioms only. Their [receipt](../verification/paper-legacy-check.json)
binds source, compiler, canonical receipt, driver and artifact hashes, each
independently rechecked. The exact [audit harness](../scripts/paper-audit/check-legacy.py)
was preserved; run it with `python3 scripts/paper-audit/check-legacy.py` after
the full canonical rebuild in a fresh checkout. Its fixed output directory must
not already exist; it refuses to overwrite an earlier run. No existing generated
checker was modified.

Build/census logs and binary artifacts remain local under `logs/paper-audit`;
the committed receipts identify their exact bytes. The historical receipt was
preserved, not overwritten to claim the old build verified new annotations.
No enormous runtime fixture was executed, and nothing was deployed or published.
