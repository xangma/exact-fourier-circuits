"""Fresh exported literal diagnostics; universal results are Lean theorems.

The continuous 4306 traces start empty and take the small-axis branch.  The
canonical selected-axis193 branch is not practically executed here.  Body21
and initializer125 tests disclose their honest local physical-entry premises.
No host state writes occur between phases of the continuous branch.
"""
from pathlib import Path
import copy
import hashlib
import json
import sys

ROOT = next(p for p in Path(__file__).resolve().parents
            if (p / "scripts/uniform_seed_cyclotomic_engine.py").is_file())
sys.path.insert(0, str(ROOT / "scripts"))
from uniform_seed_cyclotomic_engine import Poly, scalar, execute, direct_dft

P = ROOT / "logs/uniform-bytecode/empty-startup-matching"
programs = json.loads((P / "programs.json").read_text())
spec = json.loads((P / "spec.json").read_text())
assert {k: len(v) for k, v in programs.items()} == {
    "selected": 4255, "branch": 4306, "fallback": 49,
    "body": 21, "initializer": 125, "startup": 1460,
}
assert all(i[0] != "root" for key in ("body", "fallback", "initializer") for i in programs[key])
assert programs["branch"][1461] == ["branch", 102, 3270, 1462, 1511]


def empty():
    return dict(pc=0, nat=[0] * 3300, sr={}, nh={}, sh={}, out={}, roots=[])


def inputs_for(D, n, case):
    if case == "zero":
        return [scalar(D)[0] for _ in range(n)]
    if case == "cancellation":
        return [scalar(D, (-1) ** i, (-1) ** (i + 1))[0] for i in range(n)]
    return [scalar(D, i + 1, 2 - i)[0] for i in range(n)]


def output_check(s, D, n, inputs):
    omega = Poly(D, {1: 1}) ** (D // n)
    ref = direct_dft(omega, [(v, True) for v in inputs])
    assert all(s["out"][i] == ref[i][0] for i in range(n))


def loop_cost(e):
    ticks = 2
    while e:
        ticks += 6 + e % 2
        e //= 2
    return ticks


def seed_values(D, r, omega):
    one = Poly(D, {0: 1})
    H, scale = [one], [one]
    for j in range(1, r):
        H.append(H[-1] * (one - omega ** j))
        scale.append(scale[-1] * -(omega ** (j - 1)))
    h, g = [v.inverse() for v in H], [one]
    for j in range(1, r):
        v = Poly(D)
        for k in range(1, j + 1):
            v = v + h[k] * g[j - k]
        g.append(-v)
    return H, scale, [(v * w).inverse() for v, w in zip(H, scale)], h, g


def check_retained(s, m, D):
    original, conjugate = m["pool"], m["conjugatePool"]
    for j, r in enumerate(m["radices"]):
        assert s["nh"][m["directory"] + 2 * j] == original
        assert s["nh"][m["directory"] + 2 * j + 1] == r
        assert s["nh"][m["conjugateDirectory"] + 2 * j] == conjugate
        assert s["nh"][m["conjugateDirectory"] + 2 * j + 1] == r
        vals = seed_values(D, r, Poly(D, {1: 1}) ** (D // r))
        for q, lane in enumerate(vals):
            for k, v in enumerate(lane):
                assert s["sh"][original + q * r + k] == (v, False)
                assert s["sh"][conjugate + q * r + k] == (v.conjugate(), False)
        original += 5 * r
        conjugate += 5 * r
    assert original == m["destination"]


cases, failures, pcs = [], [], {k: set() for k in programs}
for m in spec["models"]:
    n, D, B = m["n"], m["masterOrder"], (m["n"] + 2) ** 19
    for case in ("nonreal", "zero", "cancellation"):
        inputs = inputs_for(D, n, case)
        reference = empty()
        rt, rp, _ = execute(programs["startup"], reference, B, 200000, D, n, inputs)
        pcs["startup"].update(rp)
        check_retained(reference, m, D)
        # Actual4306 starts empty; there are no intervening host header writes.
        s = empty()
        ticks, seen, peak = execute(programs["branch"], s, B, 200000, D, n, inputs)
        assert ticks == rt + 2 + 7 * n * n + 9 * n + 27 + loop_cost(D // n) + 1
        assert s["pc"] == 4305 and s["roots"] == reference["roots"] == [D]
        output_check(s, D, n, inputs)
        check_retained(s, m, D)
        assert s["sh"][0] == reference["sh"][0]
        assert s["nh"] == reference["nh"]
        assert s["nat"][100:107] == reference["nat"][100:107]
        assert 1511 not in seen and 1462 in seen
        assert ticks > rt and ticks <= 200000
        pcs["branch"].update(seen)
        cases.append(dict(program="branch", entry="empty actual1460→branch→49",
                          n=n, case=case, steps=ticks, startupSteps=rt, peak=peak))
        # Disclosed fallback entry: actual startup poststate with dirty fresh cells.
        s = copy.deepcopy(reference)
        s["pc"] = 0
        q = 100000 * (n + 2) ** 2
        s["sh"][q] = scalar(D, 91, -7, True)
        s["sh"][q + 1] = scalar(D, 11, 13, True)
        s["out"][n + 3] = scalar(D, 7, -9)[0]
        before = copy.deepcopy(s)
        ticks, seen, peak = execute(programs["fallback"], s, B, 100000, D, n, inputs)
        assert ticks == 7 * n * n + 9 * n + 27 + loop_cost(D // n)
        output_check(s, D, n, inputs)
        assert s["roots"] == before["roots"] and s["nh"] == before["nh"]
        assert all(s["sh"][a] == v for a, v in before["sh"].items() if a != q)
        assert s["out"][n + 3] == before["out"][n + 3]
        assert s["nat"][100:107] == before["nat"][100:107]
        pcs["fallback"].update(seen)
        cases.append(dict(program="fallback", entry="actual1460 poststate; dirty future bank",
                          n=n, case=case, steps=ticks, peak=peak))
        for label in ("missing-master", "dependent-master", "zero-length-header"):
            bad = copy.deepcopy(before)
            if label == "missing-master":
                del bad["sh"][0]
            elif label == "dependent-master":
                bad["sh"][0] = (bad["sh"][0][0], True)
            else:
                bad["nat"][101] = 0
            try:
                execute(programs["fallback"], bad, B, 100000, D, n, inputs)
            except AssertionError as exc:
                failures.append(dict(program="fallback", n=n, case=case, guard=label,
                                     lastPC=bad["pc"], error=str(exc)))
            else:
                raise AssertionError(("expected guard", label))

# Honest loaded-root21 entry; arbitrary surrounding heaps/output are dirty.
for n in (1, 2, 4, 8, 16):
    D, B = 64, 10000000
    for case in ("nonreal", "zero", "cancellation"):
        inputs = inputs_for(D, n, case)
        s = empty()
        s["nat"] = [(17 * i + 3) % 97 for i in range(3300)]
        s["nat"][2], s["nat"][140] = 0, 500
        s["sh"] = {0: scalar(D, 17, -3, True), 500: (Poly(D, {1: 1}) ** (D // n), False),
                   501: scalar(D), 711: scalar(D, -1, 4, True)}
        s["nh"], s["roots"] = {0: 13, 111: 27}, [D]
        s["out"] = {n + 1: scalar(D, 37, 11)[0]}
        before = copy.deepcopy(s)
        ticks, seen, peak = execute(programs["body"], s, B, 100000, D, n, inputs)
        assert ticks == 7 * n * n + 9 * n + 7
        output_check(s, D, n, inputs)
        assert s["sh"] == before["sh"] and s["nh"] == before["nh"]
        assert s["roots"] == before["roots"] and s["out"][n + 1] == before["out"][n + 1]
        pcs["body"].update(seen)
        cases.append(dict(program="body", entry="prepared physical canonical root; dirty surroundings",
                          n=n, case=case, steps=ticks, peak=peak))
        # n1 finishes before a root-dependent power multiplies an input.
        for label in (("missing-root", "dependent-root") if n > 1 else ("missing-root",)):
            bad = copy.deepcopy(before)
            if label == "missing-root":
                del bad["sh"][500]
            else:
                bad["sh"][500] = (bad["sh"][500][0], True)
            try:
                execute(programs["body"], bad, B, 100000, D, n, inputs)
            except AssertionError as exc:
                failures.append(dict(program="body", n=n, case=case, guard=label,
                                     lastPC=bad["pc"], error=str(exc)))
            else:
                raise AssertionError(("expected guard", label))

# Initializer diagnostics deliberately do not assert canonical Metadata foraxis193.
for n, ell, width in ((1, 194, 196), (4, 200, 211), (23, 203, 227)):
    D, B, q = 64, (n + 2) ** 19, 100000 * (n + 2) ** 2
    s = empty()
    s["nat"] = [(i * 11 + 5) % 71 for i in range(3300)]
    s["nat"][100:107] = [233, n, ell, 500, 64, 9000, 1011]
    address = 9000 + 1011 + 500 + 387
    s["nh"] = {address: width, 4: 917}
    s["sh"], s["sr"], s["out"], s["roots"] = (
        {0: scalar(D, 3, 4, True)}, {6: scalar(D, 7, -3, True)},
        {0: scalar(D, 9, 11)[0]}, [D])
    before = copy.deepcopy(s)
    code = programs["initializer"] + [["halt"]]
    ticks, seen, peak = execute(code, s, B, 1000, D, n, [])
    assert ticks == 126 and s["nat"][2200] == width
    for dst, factor in spec["scales"]:
        assert s["nat"][dst] == factor * q + (1 if dst == 2210 else 0)
    assert s["nat"][2240] == ell + 7 + 2 * n
    for key in ("nh", "sh", "sr", "out", "roots"):
        assert s[key] == before[key]
    assert s["nat"][100:107] == before["nat"][100:107]
    pcs["initializer"].update(set(seen) - {125})
    cases.append(dict(program="initializer", entry="synthetic physical directory; not canonical Metadata",
                      n=n, ell=ell, width=width, steps=ticks, peak=peak))
    bad = copy.deepcopy(before)
    del bad["nh"][address]
    try:
        execute(code, bad, B, 1000, D, n, [])
    except AssertionError as exc:
        assert bad["pc"] == 124
        failures.append(dict(program="initializer", n=n, guard="missing-selected-width", error=str(exc)))
    else:
        raise AssertionError("expected missing-directory failure")

assert pcs["body"] == set(range(21))
assert pcs["fallback"] == set(range(49))
assert pcs["initializer"] == set(range(125))
summary = dict(status="PASS", exactCases=len(cases) + len(failures), successfulCases=len(cases),
               guardCases=len(failures), continuousEmptyCases=6,
               visitedPCs={key: len(value) for key, value in pcs.items()},
               missingPCs={key: sorted(set(range(len(programs[key]))) - value)
                           for key, value in pcs.items()},
               programSHA256=hashlib.sha256((P / "programs.json").read_bytes()).hexdigest(),
               specSHA256=hashlib.sha256((P / "spec.json").read_bytes()).hexdigest(),
               limitation="No practical canonicalaxis193 large-branch trace; universal Lean theorem covers it. Large Outcome is matching, not DFT.")
(P / "fixtures.json").write_text(json.dumps(dict(summary=summary, successful=cases, guards=failures), indent=2) + "\n")
print(json.dumps(summary, indent=2))
