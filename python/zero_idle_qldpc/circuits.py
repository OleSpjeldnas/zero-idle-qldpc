"""Noisy Z-memory circuits with signed measurement-record boundaries."""

import numpy as np
import stim


def rref(matrix):
    rows = matrix.copy()
    pivots = []
    for c in range(rows.shape[1]):
        r = len(pivots)
        hits = np.flatnonzero(rows[r:, c])
        if not len(hits):
            continue
        j = r + hits[0]
        rows[[r, j]] = rows[[j, r]]
        mask = rows[:, c].astype(bool)
        mask[r] = False
        rows[mask] ^= rows[r]
        pivots.append(c)
    return rows[: len(pivots)], pivots


def logical_z(hx, hz):
    rows, piv = rref(hx)
    free = np.setdiff1d(np.arange(hx.shape[1]), piv)
    kernel = np.eye(hx.shape[1], dtype=np.uint8)[free]
    kernel[:, piv] = rows[:, free].T
    _, independent = rref(np.vstack([hz, kernel]).T)
    return kernel[[j - len(hz) for j in independent if j >= len(hz)]]


def memory(code, rounds, p, published=False):
    n = code["n"]
    m = n // 2
    data = list(range(n))
    xa = list(range(n, n + m))
    za = list(range(n + m, 2 * n))
    all_q = set(range(2 * n))
    hx, hz = (np.asarray(code[key], np.uint8) for key in ("hx", "hz"))
    c = stim.Circuit()

    def noisy(op, qubits, err):
        if op.startswith("M"):
            c.append(err, qubits, p)
        c.append(op, qubits)
        if op.startswith("R"):
            c.append(err, qubits, p)

    def detector(indices, coords):
        c.append("DETECTOR", [stim.target_rec(i) for i in indices], coords)

    noisy("R", data, "X_ERROR")
    noisy("R", za, "X_ERROR")
    if not published:
        noisy("RX", xa, "Z_ERROR")
    c.append("TICK")
    for r in range(rounds):
        for t, gates in enumerate(code["schedule"]):
            flat = [q for gate in gates for q in gate]
            busy = set(flat)
            if published and t == 0:
                noisy("RX", xa, "Z_ERROR")
                busy.update(xa)
            if published and t == 6:
                noisy("M", za, "X_ERROR")
                busy.update(za)
            c.append("CX", flat)
            c.append("DEPOLARIZE2", flat, p)
            idle = sorted(all_q - busy)
            if idle:
                c.append("DEPOLARIZE1", idle, p)
            c.append("TICK")
        noisy("MX", xa, "Z_ERROR")
        if not published:
            noisy("M", za, "X_ERROR")
        c.append("DEPOLARIZE1", data, p)
        if published and r + 1 < rounds:
            noisy("R", za, "X_ERROR")
        zstart = -n if published else -m
        xstart = -m if published else -n
        for j in range(m):
            z = zstart + j
            detector([z, z - n] if r else [z], (0, j, r))
            if r:
                detector([xstart + j, xstart + j - n], (1, j, r))
        c.append("TICK")
        if not published and r + 1 < rounds:
            noisy("RX", xa, "Z_ERROR")
            noisy("R", za, "X_ERROR")
            c.append("DEPOLARIZE1", data, p)
            c.append("TICK")
    noisy("M", data, "X_ERROR")
    for j, row in enumerate(hz):
        detector(
            [int(q) - n for q in np.flatnonzero(row)] + [zstart + j - n], (0, j, rounds)
        )
    for j, row in enumerate(logical_z(hx, hz)):
        c.append(
            "OBSERVABLE_INCLUDE",
            [stim.target_rec(int(q) - n) for q in np.flatnonzero(row)],
            j,
        )
    return c
