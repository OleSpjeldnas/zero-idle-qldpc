"""Check the exported Z memories independently. Run with Python, NumPy and Stim."""
import json
import re
from pathlib import Path
import numpy as np
import stim

ROOT = Path(__file__).resolve().parents[1] / 'circuits'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def rank(a):
    pivots = {}
    for row in a:
        v = int.from_bytes(np.packbits(row, bitorder='little').tobytes(), 'little')
        while v and v.bit_length() in pivots:
            v ^= pivots[v.bit_length()]
        if v:
            pivots[v.bit_length()] = v
    return len(pivots)

def verify(path):
    name, rounds, rate = re.fullmatch(r'(.+)-r(\d+)-p(0\.00[12])', path.stem).groups()
    rounds, p = int(rounds), float(rate)
    cert = json.loads((ROOT / (name + '.json')).read_text())
    hx, hz = [np.array(cert[key]) for key in ('hx', 'hz')]
    m, n = hx.shape
    k, steps = cert['k'], cert['schedule']
    require(n == 2*m == cert['n'] and hz.shape == hx.shape, 'dimensions')
    h = np.vstack((hx, hz))
    require(np.isin(h, [0, 1]).all() and np.all(h.sum(0) == 6) and np.all(h.sum(1) == 6), 'degrees')
    require(not np.any((hx @ hz.T) % 2) and n-rank(hx)-rank(hz) == k, 'CSS checks')
    depth = {'n56':6,'n84':6,'n96':6,'n70':10,'ibm72-t9':9}.get(name,7)
    require(len(steps)==depth, 'advertised CNOT depth')
    if name.startswith('ibm'):
        shifts = ((3,0),(0,1),(0,2),(0,3),(1,0),(2,0))
        require(all({int(q) for q in np.flatnonzero(row)} ==
                    {((i//6+x)%(m//6))*6+(i%6+y)%6+(j>=3)*m for j,(x,y) in enumerate(shifts)}
                    for i,row in enumerate(hx)), 'published IBM polynomials')
    x, z = np.eye(2*n, dtype=np.uint8)[n:].reshape(2, m, 2*n).copy()
    expected = {(n+i, int(q)) for i,row in enumerate(hx) for q in np.flatnonzero(row)}
    expected |= {(int(q), n+m+i) for i,row in enumerate(hz) for q in np.flatnonzero(row)}
    for gates in reversed(steps):
        endpoints = [q for gate in gates for q in gate]
        require(gates and len(set(endpoints)) == len(endpoints), 'CNOT collision or empty tick')
        for u,v in gates:
            expected.remove((u,v))
            x[:,v] ^= x[:,u]
            z[:,u] ^= z[:,v]
    require(not expected and np.array_equal(x[:,:n], hx) and np.array_equal(z[:,:n], hz), 'check pullback')
    require(np.array_equal(np.vstack((x,z))[:,n:], np.eye(n)), 'ancilla contamination')
    c = stim.Circuit.from_file(path)
    require((c.num_qubits,c.num_detectors,c.num_observables) == (2*n,n*rounds,k), 'memory dimensions')
    dem = c.detector_error_model()
    require(dem.num_detectors == n*rounds, 'determinism')
    layers, pairs, noisy, busy, idle = [], [], [], set(), set()
    logical = np.zeros((k,n), np.uint8)
    measured, dets, restricted = [], set(), stim.Circuit()
    support = cert['logical_x_witness']
    ops = list(c.flattened())
    check_noise = {'R':'X_ERROR', 'RX':'Z_ERROR', 'M':'X_ERROR', 'MX':'Z_ERROR'}
    for j,ins in enumerate(ops):
        require(ins.name in {*check_noise,'CX','TICK','DETECTOR','OBSERVABLE_INCLUDE','X_ERROR','Z_ERROR',
                             'DEPOLARIZE1','DEPOLARIZE2'}, 'unexpected instruction')
        if ins.name in check_noise:
            neighbor = ops[j+(1 if ins.name.startswith('R') else -1)]
            require(neighbor.name==check_noise[ins.name] and neighbor.targets_copy()==ins.targets_copy(), 'SPAM noise')
        if ins.name in ('X_ERROR','Z_ERROR'):
            require(any(0<=i<len(ops) and ops[i].name in names and ops[i].targets_copy()==ins.targets_copy()
                        for i,names in ((j-1,('R','RX')),(j+1,('M','MX')))), 'extra noise')
    for ins in ops:
        op, args = ins.name, ins.gate_args_copy()
        targets = ins.targets_copy()
        ids = [t.value for t in targets]
        if op == 'TICK':
            if pairs:
                require(pairs == noisy and idle == set(range(2*n))-busy, 'CNOT or idle noise')
                layers.append(pairs)
            elif measured:
                require(idle==set(range(n)), 'data idle noise on ancilla SPAM tick')
            pairs, noisy, busy, idle = [], [], set(), set()
        if op in ('R','RX','M','MX','CX'):
            require(not busy.intersection(ids) and len(set(ids))==len(ids), 'same-tick qubit collision')
        if op == 'CX':
            pairs.extend(ids)
            busy.update(ids)
        if op in ('M','MX','RX','R'):
            require(all((op in ('MX','RX'))==(n<=q<n+m) for q in ids), 'SPAM basis')
            busy.update(ids)
        if op in ('M','MX'):
            measured.extend(ids)
        if op in ('DEPOLARIZE1','DEPOLARIZE2','X_ERROR','Z_ERROR'):
            require(args == [p], 'noise probability')
            if op == 'DEPOLARIZE1':
                require(not idle.intersection(ids) and len(ids)==len(set(ids)), 'duplicate idle noise'); idle.update(ids)
            if op == 'DEPOLARIZE2': noisy.extend(ids)
            if op == 'X_ERROR' and ids == list(range(n)) and len(measured) == n*rounds:
                restricted.append('X_ERROR', support, p)
            continue
        restricted.append(ins)
        if op == 'OBSERVABLE_INCLUDE':
            require(all(t.is_measurement_record_target and -n <= t.value < 0 for t in targets), 'logical readout')
            logical[int(args[0]), np.array(ids)+n] ^= 1
        if op == 'DETECTOR':
            require(all(t.is_measurement_record_target for t in targets), 'detector targets')
            dets.add(tuple(sorted(len(measured)+i for i in ids)))
    require(layers == [[q for gate in tick for q in gate] for tick in steps]*rounds, 'CNOT depth or order')
    require(np.all((hx@logical.T)%2 == 0) and rank(np.vstack((hz,logical))) == rank(hz)+k, 'logical basis')
    record = {}
    for i,q in enumerate(measured):
        record.setdefault(q,[]).append(i)
    wanted = set()
    for a in range(n,2*n):
        times = record[a]
        require(len(times)==rounds, 'ancilla measurements')
        wanted.update(zip(times,times[1:]))
        if a>=n+m:
            wanted.add((times[0],))
            wanted.add(tuple(sorted([times[-1]]+[record[q][0] for q in np.flatnonzero(hz[a-n-m])])))
    require(wanted == dets and all(record[q]==[n*rounds+q] for q in range(n)), 'memory boundaries')
    try:
        graph = len(c.shortest_graphlike_error(canonicalize_circuit_errors=True))
    except ValueError as e:
        if 'Failed to find any graphlike logical errors' not in str(e): raise
        graph = None
    opts = dict(dont_explore_edges_increasing_symptom_degree=False, canonicalize_circuit_errors=True)
    try:
        bounded = len(c.search_for_undetectable_logical_errors(dont_explore_detection_event_sets_with_size_above=2,
                       dont_explore_edges_with_degree_above=3, **opts))
    except ValueError as e:
        if 'Failed to find any' not in str(e): raise
        bounded = None
    # Restrict to actual final-readout faults. This yields a physical upper bound even for hypergraph-only codes.
    witness = restricted.search_for_undetectable_logical_errors(dont_explore_detection_event_sets_with_size_above=n,
                  dont_explore_edges_with_degree_above=6, **opts)
    require(len(witness)==len(set(support))==cert['data_distance'], 'readout fault witness')
    return graph, bounded, len(witness)

if __name__ == '__main__':
    files = sorted(ROOT.glob('*.stim'))
    expected = {f'{p.stem}-r{r}-p{v}.stim' for p in ROOT.glob('*.json')
                for r in ((4,12) if p.stem=='ibm144-published' else (4,)) for v in ('0.001','0.002')}
    required = {'n56','n60-archive','n60-nonabelian','n70','n84','n96','ibm72-published',
                'ibm72-t7','ibm72-t9','ibm144-published'}
    require({p.stem for p in ROOT.glob('*.json')}==required and {p.name for p in files}==expected, 'incomplete suite')
    for path in files:
        print(path.name, 'graphlike / bounded / readout witness', verify(path), flush=True)
