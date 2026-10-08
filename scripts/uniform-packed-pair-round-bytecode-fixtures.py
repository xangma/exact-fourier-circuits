"""Fresh Lean-exported literal23, exact cyclotomic values and actual tags.

From a clean checkout, build the module normally (or put its scratch olean on
LEAN_PATH), then run lake env lean ../verification/ExportPackedPairRoundBytecode.lean
from lean/, and run this script. Physical entry banks are explicit fixture inputs;
this diagnostic does not claim an initial-state or six-C shear assembly.
"""
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from uniform_seed_cyclotomic_engine import Poly, scalar, execute

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / "logs/uniform-packed-c-round-agent-20261008"
CODE = json.loads((LOG / "program.json").read_text())
assert len(CODE) == 23
assert CODE[3:5] == [["getscalar", 0, 1282], ["getscalar", 1, 1283]]
assert CODE[5] == ["branch", 1284, 1281, 6, 22]
assert CODE[9:19] == [
    ["getscalar", 2, 0], ["getscalar", 3, 1],
    ["fmul", 4, 0, 2], ["fmul", 5, 1, 3], ["fadd", 6, 4, 5],
    ["fmul", 4, 1, 2], ["fmul", 5, 0, 3], ["fadd", 7, 4, 5],
    ["putscalar", 0, 6], ["putscalar", 1, 7]]
assert CODE[19:] == [["jump", 20], ["add", 1284, 1284, 1285], ["jump", 5], ["halt"]]
assert all(row[0] not in ("root", "input", "output", "putnat") for row in CODE)


def entry(D, m, base, family):
    B = max(4096, base + 2*m + 64)
    s = {"pc": 0, "nat": [(j*7+3) % 41 for j in range(1288)],
         "sr": {j: scalar(D, j-13, 4-j, True) for j in range(40)},
         "nh": {j: j+17 for j in range(47)},
         "sh": {j: scalar(D, j-7, 19-j, bool(j % 2)) for j in range(27)},
         "out": {0: scalar(D, 17, -9)[0], 4: scalar(D, -2, 5)[0]}, "roots": [4, 12]}
    s["nat"][1280:1284] = [base, m, 10, 11]
    s["sh"][10] = scalar(D, Fraction(1, 2), Fraction(1, 2))
    s["sh"][11] = scalar(D, Fraction(1, 2), Fraction(-1, 2))
    eta = Poly(D, {1: 1})
    for i in range(m):
        if family == "zero":
            u, v = scalar(D), scalar(D, dep=bool(i % 2))
        elif family == "cancellation":
            u, v = scalar(D, 0, 1, True), scalar(D, 1, 0, False)
        elif family == "prepared":
            u, v = (eta**(i % D), False), (eta**((-i) % D), False)
        else:
            u = scalar(D, Fraction(2*i-7, 8), Fraction(3-i, 4), bool(i % 2))
            v = scalar(D, Fraction(13-i, 16), Fraction(i-5, 8), bool((i+1) % 3))
        s["sh"][base+2*i], s["sh"][base+2*i+1] = u, v
    s["sh"][base-1] = scalar(D, -99, 13, True)
    s["sh"][base+2*m] = scalar(D, 123, -17, True)
    return s, B


def reference(D, u, v):
    # Independent sum/difference identity; no source-kernel bytecode emulation.
    half = Poly(D, {0: Fraction(1, 2)})
    imag = Poly(D, {D//4: 1})
    mean = half*(u[0]+v[0])
    rotation = half*imag*(u[0]-v[0])
    tag = u[1] or v[1]
    return (mean+rotation, tag), (mean-rotation, tag)


success, guards, seen = [], [], set()
for D in (4, 8, 12):
    for m in (0, 1, 2, 3, 7, 16, 64, 257):
        for base in (32, 97, 640):
            for family in ("mixed", "zero", "prepared", "cancellation"):
                s, B = entry(D, m, base, family)
                old = deepcopy(s)
                expected = deepcopy(old["sh"])
                for i in range(m):
                    expected[base+2*i], expected[base+2*i+1] = reference(
                        D, old["sh"][base+2*i], old["sh"][base+2*i+1])
                ticks, pcs, peak = execute(CODE, s, B, 17*m+7, D)
                assert ticks == 17*m+7 and s["pc"] == 22 and peak <= B
                assert s["sh"] == expected
                assert s["nh"] == old["nh"] and s["out"] == old["out"] and s["roots"] == old["roots"]
                assert all(s["nat"][r] == old["nat"][r] for r in range(1288)
                           if r not in (0, 1, 1284, 1285, 1286, 1287))
                assert all(s["sr"].get(r, scalar(D)) == old["sr"].get(r, scalar(D)) for r in range(8, 40))
                assert s["sh"][10] == old["sh"][10] and s["sh"][11] == old["sh"][11]
                if family == "cancellation" and m:
                    assert s["sh"][base] == scalar(D, dep=True)  # zero retains the actual OR tag.
                seen.update(pcs)
                success.append({"D": D, "pairs": m, "base": base, "family": family, "ticks": ticks, "peak": peak})

for label in ("missing-diagonal", "missing-off-diagonal", "missing-first-input", "missing-last-input",
              "dependent-diagonal", "dependent-off-diagonal", "short-runtime", "bad-entry-pc"):
    s, B = entry(4, 3, 97, "cancellation")
    budget = 58
    if label == "missing-diagonal": del s["sh"][10]
    elif label == "missing-off-diagonal": del s["sh"][11]
    elif label == "missing-first-input": del s["sh"][97]
    elif label == "missing-last-input": del s["sh"][102]
    elif label == "dependent-diagonal": s["sh"][10] = (s["sh"][10][0], True)
    elif label == "dependent-off-diagonal":
        s["sh"][11] = (s["sh"][11][0], True)
        s["sh"][98] = (s["sh"][98][0], True)
    elif label == "short-runtime": budget = 57
    else: s["pc"] = 23
    try:
        execute(CODE, s, B, budget, 4)
    except AssertionError as e:
        guards.append({"case": label, "reason": str(e)})
    else:
        raise AssertionError(("expected failed guard", label))

assert seen == set(range(23))
report = {"status": "PASS", "success_count": len(success), "guard_count": len(guards),
          "all_pc": sorted(seen), "bytecode_sha256": hashlib.sha256((LOG/"program.json").read_bytes()).hexdigest(),
          "success": success, "guards": guards,
          "scope": "Fresh Lean literal23; explicit physical entry banks; exact numeric C and OR tags; no six-C or startup assembly claim."}
(LOG/"bytecode-fixtures.json").write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps({k: report[k] for k in ("status", "success_count", "guard_count", "all_pc", "bytecode_sha256")}))
