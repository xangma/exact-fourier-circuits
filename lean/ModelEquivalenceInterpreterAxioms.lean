import ModelEquivalenceInterpreterFixtures
import Lean.Util.CollectAxioms

set_option autoImplicit false

/-! Enumerate public, private and generated declarations belonging to both sources. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.filterMap fun (n, _) =>
    if n.toString.startsWith "ExactFourierCircuits.ModelEquivalenceInterpreter" ||
        n.toString.startsWith "_private.ModelEquivalenceInterpreter" then some n else none).toArray
  let names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    let axioms ← Lean.collectAxioms n
    for a in axioms do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "Unexpected axiom in {n}: {a}"
    logInfo m!"{n}: {axioms}"
  logInfo m!"MODEL_EQUIVALENCE_INTERPRETER_AUDIT_PASS {names.size}"
