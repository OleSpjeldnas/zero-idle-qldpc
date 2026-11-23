"""Reproduce the checked-in certificates and four-/twelve-round memory circuits."""

import json

import numpy as np

from .synthesizer import ROOT, ZeroIdleSynthesizer, IBM, T6, T7, T9, T10, materialize
from .circuits import memory, rref
from .layout import analyze


def witness(code):
    """Sample information sets until a kernel vector outside the stabilizer span attains d."""
    n = code["n"]
    d = code["data_distance"]
    hx, hz = (np.array(code[k], np.uint8) for k in ("hx", "hz"))
    rng = np.random.default_rng(1234)
    stab, piv = rref(hx)
    for attempt in range(20000):
        order = rng.permutation(n)
        red, p = rref(hz[:, order])
        f = np.setdiff1d(np.arange(n), p)
        trial = np.eye(n, dtype=np.uint8)[f]
        trial[:, p] = red[:, f].T
        for v in trial[trial.sum(1) == d]:
            original = v[np.argsort(order)]
            rem = original.copy()
            for j, q in enumerate(piv):
                if rem[q]:
                    rem ^= stab[j]
            if rem.any():
                return np.flatnonzero(original).tolist()
    raise ValueError("no static witness")


def designs():
    s = ZeroIdleSynthesizer()
    yield "n56", s.schedule((14, 2, 1), (13, 19, 2, 0), (0, 12), 6, 6, T6), 6
    yield "n84", s.cyclic(84, 8), 6
    yield "n96", s.schedule((12, 4, 1), (0, 1, 20, 34), (0, 10), 8, 6, T6), 6
    yield "n70", s.schedule((7, 5, 1), (0, 5, 28), (0, 21, 31), 6, 7, T10), 8
    # Keep the seven-tick witness on the noncommuting order-30 group fixed.
    nonabelian_ticks = (1, 2, 4, 0, 3, 6, 6, 3, 0, 4, 5, 2)
    yield "n60-nonabelian", s.schedule(
        (5, 6, 4), (8, 26, 0), (0, 22, 1), 8, 4, (nonabelian_ticks,), reorder=False
    ), 6
    yield "n60-archive", s.schedule((6, 5, 1), (0, 17, 21), (0, 7, 23), 8, 6, T7), 6
    A, B = (18, 1, 2), (3, 6, 12)
    for l, d in ((6, 6), (12, 12)):
        yield f"ibm{12 * l}-published", materialize((l, 6, 1), A, B, IBM, 12, d), d
    yield "ibm72-t7", s.schedule((6, 6, 1), A, B, 12, 5, T7), 6
    yield "ibm72-t9", s.schedule((6, 6, 1), A, B, 12, 6, T9), 6


def main():
    out = ROOT / "circuits"
    for name, code, data_distance in designs():
        published = name.endswith("published")
        hook = code.pop("d") if not published else None
        code.update(data_distance=data_distance, hook_distance=hook)
        code.pop("d", None)
        code["logical_x_witness"] = witness(code)
        code["layout"] = analyze(code)
        (out / (name + ".json")).write_text(
            json.dumps(code, separators=(",", ":")) + "\n"
        )
        for rounds in (4, 12) if name.startswith("ibm144") else (4,):
            for p in (0.001, 0.002):
                path = out / f"{name}-r{rounds}-p{p:.3f}.stim"
                label = (
                    f"# {name}  [[{code['n']},{code['k']},{data_distance}]] Z memory\n"
                )
                path.write_text(label + str(memory(code, rounds, p, published)) + "\n")
        print(name, flush=True)


if __name__ == "__main__":
    main()
