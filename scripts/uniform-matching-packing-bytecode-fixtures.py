"""Exact dirty-state tests of the actual Matching215 -> setup8 -> Packing137.

Run verification/ExportMatchingPackingBytecode.lean first. Typed cases enter
at the honest Height.Processed boundary; generic cases test Domain/degree
layers with output ports. No generated matching/packing bank is initialized.
Only Nat instructions and tagged scalar copies execute (no root/division).
"""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
from uniform_cyclotomic_engine import Poly, execute, scalar

ROOT = Path(__file__).resolve().parents[1]
P = ROOT / "logs/uniform-bytecode/matching-packing"
CODE = json.loads((P / "program.json").read_text())
TYPED = json.loads((P / "typed.json").read_text())
GENERIC = json.loads((P / "generic.json").read_text())
B = 1_000_000


def fresh():
    s = {"pc": 0, "nat": [(17*i+13) % 10000 for i in range(1450)],
         "nh": {0: 71, 7: 41, B-1: 3},
         "sh": {i: scalar(8, F(i-7, 3), F(11-i, 5), i % 3 == 0) for i in range(47)},
         "sr": {i: scalar(8, F(i-5, 3), F(11-i, 2), i % 2 == 1) for i in range(100)},
         "out": {9: Poly(8, {0: 3, 2: -7, 5: F(9, 2)})}, "roots": [16, 7, 1]}
    for j in range(100, 107):
        s["nat"][j] = 17*j+9
    return s


def greedy(rows):
    colors = []
    for i, (d, s, _) in enumerate(rows):
        blocked = {colors[j] for j, (x, y, _) in enumerate(rows[:i])
                   if d in (x, y) or s in (x, y)}
        colors.append(next(j for j in range(11) if j not in blocked))
    return colors


def pools(K, a, e, dirty, exact=False):
    N = 1 << K
    G = 6*(3*K*N+2*N)+2*a
    H = 8*K+7
    T = 13+dirty*19
    Q, R = T+5*G+9, T+6*G+18
    D = R+G+11
    F0 = D+6*G*H+9
    U = F0+2*G*H+9
    J = U+23
    v = G+e+a+(0 if exact else 7)
    src, tgt = (0, G+e) if exact else (2, v-a-2)
    b = J+3*H+17
    o = b+G+3
    ids = o+6*G+3
    m = ids+2*G+3
    perm = m+6*G+3
    w = perm+v+3
    mark = w+v+3
    axis = mark+v+3
    suffix = axis+13
    stack = suffix+5
    inverse = stack+13
    return dict(K=K, a=a, e=e, N=N, G=G, H=H, T=T, Q=Q, R=R,
                D=D, F=F0, U=U, J=J, C=200000, P=300000, Z=400000,
                v=v, src=src, tgt=tgt, b=b, o=o, ids=ids, m=m,
                perm=perm, w=w, mark=mark, axis=axis,
                suffix=suffix, stack=stack, inverse=inverse,
                data=500000+dirty*1000, dest=600000+dirty*1000)


def validate_layout(p, depth, color):
    v, e, a, G, H = [p[q] for q in ["v", "e", "a", "G", "H"]]
    assert 361 <= B and 2 <= v and e <= p["N"] and a <= p["N"]
    assert p["src"]+e <= v and p["tgt"]+a <= v
    assert p["src"]+e <= p["tgt"] or p["tgt"]+a <= p["src"]
    assert G+e+a <= v and depth < H and color < 11
    assert p["D"]+6*G*H <= p["b"] and p["F"]+2*G*H <= p["b"]
    assert p["J"]+3*H <= p["b"] and p["b"]+G <= p["o"]
    assert p["o"]+6*G <= p["ids"] and p["ids"]+2*G <= p["m"]
    assert p["m"]+6*G <= p["perm"] and p["perm"]+v <= p["w"]
    assert p["w"]+v <= p["mark"] and p["mark"]+v <= p["axis"]
    assert p["axis"]+4 <= p["suffix"] and p["suffix"]+2 <= p["stack"]
    assert p["stack"]+9 <= p["inverse"] and p["inverse"]+v <= B
    assert p["data"]+v <= p["dest"] and p["dest"]+v <= B and v <= B


def initialize(p, depth, color, enabled, slices):
    validate_layout(p, depth, color)
    s = fresh()
    s["nat"][1050:1063] = [p[q] for q in
        ["K", "a", "e", "T", "Q", "R", "D", "F", "U", "J", "C"]] + [int(enabled), p["P"]]
    s["nat"][1180:1193] = [p[q] for q in
        ["v", "src", "tgt", "b", "o", "ids", "m", "perm", "w", "mark", "axis"]] + [depth, color]
    s["nat"][1400:1405] = [p[q] for q in ["suffix", "stack", "inverse", "data", "dest"]]
    # New output banks contain arbitrary dirty cells, never correct readiness.
    for q in range(p["b"], p["inverse"]+p["v"]):
        s["nh"][q] = (31*q+17) % 10000
    for d, sl in enumerate(slices):
        assert sl["colors"] == greedy(sl["rows"])
        assert len(sl["rows"]) <= 2*p["G"]
        endpoints = [q for dst, src, _ in sl["rows"] for q in [dst, src]]
        assert all(endpoints.count(q) <= 6 for q in set(endpoints))
        assert all(dst != src for dst, src, _ in sl["rows"])
        assert all(q < p["e"] or p["e"]+1 <= q < p["e"]+1+p["G"]+p["a"] for q in endpoints)
        rd, cd = p["D"]+6*p["G"]*d, p["F"]+2*p["G"]*d
        for i, row in enumerate(sl["rows"]):
            for j, v in enumerate(row):
                s["nh"][rd+3*i+j] = v
        for i, v in enumerate(sl["colors"]):
            s["nh"][cd+i] = v
        for j, v in enumerate([len(sl["rows"]), rd, cd]):
            s["nh"][p["J"]+3*d+j] = v
    for i in range(p["v"]):
        s["sh"][p["data"]+i] = scalar(8, 0 if i % 5 == 0 else F(i-3, 7),
                                       0 if i % 5 == 0 else F(4-i, 9), i % 3 == 0)
        s["sh"][p["dest"]+i] = scalar(8, F(100+i, 13), F(-i, 5), i % 2 == 1)
    # External prepared coefficient banks must survive; no values are used.
    for base, size in [(p["C"], 7*p["N"]), (p["P"], 6), (p["Z"], 7*p["N"])]:
        for i in range(size):
            s["sh"][base+i] = scalar(8, F(i-2, 11), F(3-i, 17))
    return s


def expected(p, rows, color):
    colors = greedy(rows)
    ids = [i for i, c in enumerate(colors) if c == color]
    selected = [rows[i] for i in ids]
    v, e, a, G = [p[q] for q in ["v", "e", "a", "G"]]
    borrowed = [i for i in range(v) if not p["src"] <= i < p["src"]+e
                and not p["tgt"] <= i < p["tgt"]+a][:G]
    assert len(borrowed) == G

    def mapped(q):
        assert q < e or e+1 <= q < e+1+G+a
        if q < e:
            return p["src"]+q
        if q < e+1+G:
            return borrowed[q-e-1]
        return p["tgt"]+q-e-1-G

    mapped_rows = [[mapped(d), mapped(s), co] for d, s, co in selected]
    used = [x for d, s, _ in mapped_rows for x in [d, s]]
    assert len(used) == len(set(used))
    order = used+[j for j in range(v) if j not in used]
    widths = [2]*len(selected)+[1]*(v-2*len(selected))
    assert sum(widths) == v and sorted(order) == list(range(v))
    return ids, selected, borrowed, mapped_rows, order, widths


def protected(r):
    return all(not lo <= r < hi for lo, hi in
               [(261, 273), (840, 862), (880, 900), (1020, 1035),
                (1080, 1101), (1193, 1206), (600, 650)]) and r != 1405


def check(s, old, p, W, color, steps):
    ids, selected, borrowed, rows, order, widths = expected(p, W, color)
    assert s["pc"] == 360 and steps <= 4*p["K"]+393*p["v"]+121
    assert s["nat"][894] == len(ids)
    assert [s["nh"][p["ids"]+i] for i in range(len(ids))] == ids
    assert [[s["nh"][p["o"]+3*i+j] for j in range(3)] for i in range(len(ids))] == selected
    assert [[s["nh"][p["m"]+3*i+j] for j in range(3)] for i in range(len(ids))] == rows
    assert [s["nh"][p["b"]+i] for i in range(p["G"])] == borrowed
    assert [s["nh"][p["perm"]+i] for i in range(p["v"])] == order
    assert [s["nh"][p["w"]+i] for i in range(len(widths))] == widths
    assert [s["nh"][p["axis"]+j] for j in range(4)] == [len(widths), p["w"], p["v"], p["perm"]]
    assert [s["nh"][p["inverse"]+i] for i in range(p["v"])] == order
    assert [s["sh"][p["dest"]+i] for i in range(p["v"])] == [old["sh"][p["data"]+i] for i in order]
    assert all(s["sh"].get(q) == old["sh"].get(q) for q in set(s["sh"]) | set(old["sh"])
               if not p["dest"] <= q < p["dest"]+p["v"])
    assert all(s["nh"].get(q) == old["nh"].get(q) for q in set(s["nh"]) | set(old["nh"])
               if not p["b"] <= q < p["inverse"]+p["v"])
    assert s["out"] == old["out"] and s["roots"] == old["roots"]
    assert all(s["nat"][r] == old["nat"][r] for r in range(len(s["nat"])) if protected(r))
    assert all(s["sr"][r] == old["sr"][r] for r in old["sr"] if r != 70)
    return len(ids)


results, coverage, saved = [], set(), []
for c in TYPED:
    for dirty in range(3):
        p = pools(c["K"], c["a"], c["e"], dirty)
        for d, sl in enumerate(c["slices"]):
            for color in [0, 1, 2, 10]:
                s = initialize(p, d, color, c["enabled"], c["slices"])
                old = copy.deepcopy(s)
                steps, pcs = execute(CODE, s, B, 1000000, 8)
                selected = check(s, old, p, sl["rows"], color, steps)
                coverage.update(pcs)
                results.append(dict(origin="actual typed K0 corrected-cross Height.Processed", dirty=dirty,
                                    K=p["K"], a=p["a"], e=p["e"], depth=d, color=color,
                                    enabled=c["enabled"], radix=p["v"], selected=selected, steps=steps))
                if sl["rows"] and color == 0:
                    saved.append((old, p, d, color))
for c in GENERIC:
    assert c["colors"] == greedy(c["rows"])
    for exact in [False, True]:
        for dirty in range(3):
            p = pools(c["K"], c["a"], c["e"], dirty, exact)
            for color in [0, 1, 2, 10]:
                sl = dict(rows=c["rows"], colors=c["colors"])
                s = initialize(p, 0, color, True, [sl])
                old = copy.deepcopy(s)
                steps, pcs = execute(CODE, s, B, 1000000, 8)
                selected = check(s, old, p, c["rows"], color, steps)
                coverage.update(pcs)
                results.append(dict(origin="generic Domain/degree layer with target ports", dirty=dirty,
                                    exactCapacity=exact, K=p["K"], a=p["a"], e=p["e"], depth=0,
                                    color=color, radix=p["v"], selected=selected, steps=steps))
controls = []


def reject(name, s, b=B):
    try:
        execute(CODE, s, b, 1000000, 8)
    except (AssertionError, KeyError):
        controls.append(dict(name=name, kind="actual missing-load or ambient WordBound rejection"))
        return
    raise AssertionError("negative control accepted: "+name)


assert saved
old, p, d, color = saved[0]
for name, q in [("missing physical layer record", p["J"]+3*d),
                ("missing physical logical row", p["D"]+6*p["G"]*d),
                ("missing physical color", p["F"]+2*p["G"]*d)]:
    s = copy.deepcopy(old)
    del s["nh"][q]
    reject(name, s)
s = copy.deepcopy(old)
del s["sh"][p["data"]]
reject("missing original scalar source", s)
reject("insufficient ambient word bound", copy.deepcopy(old), 360)
# Allocation/matching hypotheses are mathematical entry conditions, not runtime guards.
controls.append(dict(name="overlapping source/destination", kind="excluded by Layout; no invented bytecode guard"))
controls.append(dict(name="nonmatching same-color pairs", kind="excluded by degree+actual greedy; no invented bytecode guard"))
report = dict(status="PASS", caseCount=len(results), totalSteps=sum(c["steps"] for c in results), cases=results,
              controls=controls, coverage=dict(length=361, visited=len(coverage), unvisited=sorted(set(range(361))-coverage)),
              hashes={str(f.relative_to(ROOT)): hashlib.sha256(f.read_bytes()).hexdigest() for f in
                      [ROOT/"lean/UniformMatchingPackingPreparation.lean", ROOT/"verification/ExportMatchingPackingBytecode.lean",
                       Path(__file__), ROOT/"scripts/uniform_cyclotomic_engine.py", P/"program.json", P/"typed.json", P/"generic.json"]},
              entryContracts=dict(ordinaryLayout="All 408 cases assert exact capacity, source/target separation, depth/color bounds and Matching+Packing fresh-bank Layout inequalities.",
                                  typed="336 cases initialize every Height.Processed record/row/color from the fresh Lean actual K0 crossDAG depth bucket and actual coloring reference; earlier Height execution and full selected-axis startup are not replayed here.",
                                  generic="72 cases initialize only the generic logical bucket Table/Record/greedy Colors; Domain, degree<=6, row-count and Layout checked independently; these are not actual selected-axis witnesses.",
                                  scalars="Original scalar bank contains exact arbitrary prepared/input tags and nonreal/zero values. Destination and every new Nat bank are dirty."),
              arithmetic="Exact Gaussian rational scalars embedded in Q[X]/(X^8+1); program only copies tagged values, no roots/division.",
              boundary="Typed fixtures initialize earlier physical Height.Processed rows/colors/directory and original scalars. Actual361 internally produces matching tables, packing inverse and tagged packed scalars. Generic target-port fixtures start at honest Domain/degree entry. No six-C execution, unpack restoration, or whole-DFT claim.")
(P/"fixtures.json").write_text(json.dumps(report, indent=2))
print(json.dumps({k: v for k, v in report.items() if k != "cases"}, indent=2))
