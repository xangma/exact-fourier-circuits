# Project instructions

- Keep exact arithmetic in the proof/circuit engine. Hardware floats belong
  at the CUDA evaluation boundary.
- Preserve the 51 vendored `lean/OAI/` files and their upstream hashes. Put new
  proofs in separate modules. Never introduce `sorry`, custom axioms, or native
  decision shortcuts to make verification pass.
- Distinguish a positive symbolic budget, sampled checks, exhaustive exact
  basis checks, and a Lean-verified witness. The full generated seed has not
  been formally verified or materialized. Small demos do not save calls.
- Bound expansion before allocating or shifting by astronomical exponents.
- Prefer codebase-memory graph discovery; if unavailable, disclose the gap
  and use bounded exact source inspection.
- Run focused checks for changed components. The standard commands are in
  README.md. GPU work must preserve existing services and retain job/log/stop
  records; coordination is informational.
