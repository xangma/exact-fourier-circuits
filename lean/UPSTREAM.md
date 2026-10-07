The `OAI/` files are an unmodified 51-module import closure copied from
https://github.com/openai/math at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, under `lean/`,
rooted at `OAI.Computability.FourierCircuit.Main`.

The source is distributed under Apache-2.0; see `LICENSE.upstream`. Original
file headers are preserved. `UPSTREAM_MANIFEST.json` records each SHA-256 hash.
The challenge comparator is outside this closure and has not been copied.

`lakefile.lean`, `CheckAxioms.lean`, `KernelIdentities.lean`, and
`CheckKernelAxioms.lean` are new project files. The kernel identities verify
the local Python word formulas as exact complex matrix identities; they do
not implement extraction of the existential saving witness. Mathlib is pinned
to the same revision as upstream; its own transitive dependency pins apply.
