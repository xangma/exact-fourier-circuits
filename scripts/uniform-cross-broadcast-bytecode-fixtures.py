"""Run Borrowed17 and the actual output-broadcast table producer in exact RAM."""
from pathlib import Path
import copy
import hashlib
import json
from uniform_seed_cyclotomic_engine import scalar, execute

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT/'logs/uniform-bytecode/cross-broadcast'
CODE = json.loads((PACKET/'program.json').read_text())
BORROWED = json.loads((PACKET/'borrowed.json').read_text())
assert len(CODE) == 20 and len(BORROWED) == 17
WRITES = {894, *range(3110, 3118)}


def fresh(source, e, target, a, g, salt):
    s = dict(pc=0, nat=[(13*i+salt)%97 for i in range(3120)],
             nh={0: 19, 9999: 27},
             sh={1: scalar(4, 1), 700: scalar(4, 3, -2, True)},
             sr={2: scalar(4, 3, 7, True)},
             out={2: scalar(4, -3, 2)[0]}, roots=[4, 12])
    s['nat'][261:267] = [source, e, target, a, g, 256]
    s['nat'][3100:3106] = [a, g, target, 256, 1000, 1]
    return s


cases = []; covered = set(); ticks = 0; borrowed_ticks = 0
# The first geometry is the real K=2,a=e=1 corrected-cross G=194 shape.
# Others exercise empty/multiple rows and different excluded physical blocks.
for source, e, target, a, g, volume in [
        (0, 1, 1, 1, 194, 256), (0, 0, 0, 0, 0, 1),
        (0, 2, 2, 2, 5, 16), (5, 3, 20, 3, 7, 32),
        (0, 1, 1, 4, 9, 16), (10, 2, 1, 2, 4, 16)]:
    assert a <= g and g+e+a <= volume and target+a <= volume
    available = [i for i in range(volume)
                 if not source <= i < source+e and not target <= i < target+a]
    for salt in (0, 31):
        s = fresh(source, e, target, a, g, salt)
        steps, _, _ = execute(BORROWED, s, 10000, 10000, 4)
        borrowed_ticks += steps
        assert [s['nh'][256+j] for j in range(g)] == available[:g]
        # Separate component entry after Borrowed17; no uncharged continuous
        # global caller is claimed. All table cells come from that real run.
        s['pc'] = 0
        before = copy.deepcopy(s); expected = dict(s['nh'])
        edges = []
        for j in range(a):
            edge = (target+j, available[g-a+j])
            edges.append(edge)
            expected.update({1000+3*j: edge[0], 1000+3*j+1: edge[1],
                             1000+3*j+2: 1})
        endpoints = [z for edge in edges for z in edge]
        assert len(set(endpoints)) == len(endpoints)
        steps, pcs, peak = execute(CODE, s, 10000, 14*a+7, 4)
        assert steps == 14*a+7 and s['pc'] == 19 and s['nat'][894] == a
        assert s['nh'] == expected
        for key in ('sh', 'sr', 'out', 'roots'):
            assert s[key] == before[key], key
        for r in range(len(s['nat'])):
            if r not in WRITES:
                assert s['nat'][r] == before['nat'][r], r
        covered.update(pcs); ticks += steps
        cases.append(dict(source=source, sourceWidth=e, target=target,
                          outputWidth=a, gates=g, volume=volume, salt=salt,
                          steps=steps, maximumWord=peak))

controls = []


def prepared():
    s = fresh(0, 1, 1, 1, 194, 0)
    execute(BORROWED, s, 10000, 10000, 4)
    s['pc'] = 0
    return s


def reject(name, state, bound=10000, fuel=10000):
    try:
        execute(CODE, state, bound, fuel, 4)
    except (AssertionError, KeyError):
        controls.append(name)
        return
    raise AssertionError('negative control accepted: '+name)


s = prepared(); del s['nh'][256+193]; reject('missing borrowed coordinate', s)
reject('charged runtime guard', prepared(), fuel=20)
s = prepared(); s['nat'][3102] = 10000; s['nat'][3100] = 2
reject('target address overflow', s)
s = prepared(); s['nat'][3104] = 10000
reject('row address overflow', s)
s = prepared(); s['nat'][3103] = 10000
reject('borrowed address overflow', s)
assert covered == set(range(20))
result = dict(status='PASS', exactCases=len(cases), chargedSteps=ticks,
              borrowedSteps=borrowed_ticks, cases=cases,
              negativeControls=controls, coveredPCs=sorted(covered),
              scope='Actual Borrowed17 output is consumed by fixed20 broadcast-row producer. Exact count, complete Nat table/outside frame, scalar/flag/root/output retention and physical matching checked. Ordinary component headers and positive coefficient pointer are entry inputs. Header installation between components is explicit; no full six-phase cross action, global startup or all-length DFT claim.',
              hashes={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in [Path(__file__), PACKET/'program.json',
                                PACKET/'borrowed.json',
                                ROOT/'verification/ExportCrossBroadcastBytecode.lean']})
(PACKET/'fixtures.json').write_text(json.dumps(result, indent=2)+'\n')
print('PASS', len(cases), 'exact broadcast tables,', ticks,
      'charged steps,', len(controls), 'guard controls')
