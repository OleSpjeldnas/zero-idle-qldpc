"""Two-block group algebra synthesis. Element x*b+y denotes (x,y)."""

import ctypes as ct
from itertools import permutations
from math import gcd
from pathlib import Path
import numpy as np

T6 = (
    (0, 2, 3, 5, 4, 1, 1, 4, 5, 3, 2, 0),
    (0, 1, 4, 5, 3, 2, 2, 3, 5, 4, 1, 0),
    (1, 2, 3, 4, 5, 0, 0, 5, 4, 3, 2, 1),
)
T7 = (
    (2, 3, 4, 5, 1, 0, 0, 5, 6, 2, 3, 4),
    (4, 1, 2, 6, 3, 0, 0, 3, 6, 1, 5, 4),
    (0, 2, 4, 5, 3, 1, 1, 3, 5, 6, 4, 2),
)
T9 = ((5, 7, 8, 6, 4, 2, 2, 4, 6, 3, 0, 1),)
T10 = ((0, 1, 2, 3, 4, 5, 4, 5, 6, 7, 8, 9),)
# Published direction lists sX=(idle,1,4,3,5,0,2), sZ=(3,5,0,1,2,4,idle).
IBM = (5, 1, 6, 3, 2, 4, 2, 3, 4, 0, 5, 1)
ROOT = Path(__file__).resolve().parents[2]


def group_table(a, b, action):
    if (
        a <= 1
        or b <= 0
        or a * b < 4
        or a * b > 1024
        or gcd(a, action) != 1
        or pow(action, b, a) != 1
    ):
        raise ValueError("Invalid cyclic semidirect product")
    i, j = np.indices((a * b, a * b))
    powers = np.array([pow(action, y, a) for y in range(b)])
    return np.ascontiguousarray(
        ((i // b + powers[i % b] * (j // b)) % a) * b + (i + j) % b, dtype=np.int32
    )


def materialize(group, A, B, times, k, distance):
    a, b, r = group
    mul = group_table(a, b, r)
    m = len(mul)
    n = 2 * m
    rows = np.arange(m)
    left, right = mul[:, A].T, mul[B, :]
    matchings = [
        *((n + rows, col) for col in left),
        *((n + rows, m + col) for col in right),
        *((np.argsort(col), n + m + rows) for col in right),
        *((m + np.argsort(col), n + m + rows) for col in left),
    ]
    schedule = [[] for _ in range(max(times) + 1)]
    for t, (u, v) in zip(times, matchings, strict=True):
        schedule[t].extend(zip(u.tolist(), v.tolist()))
    hx = np.zeros((m, n), np.uint8)
    for col in left:
        hx[rows, col] = 1
    for col in right:
        hx[rows, m + col] = 1
    hz = np.hstack((hx[:, m:].T, hx[:, :m].T))
    return dict(
        n=n,
        k=k,
        d=distance,
        group=group,
        A=list(A),
        B=list(B),
        times=times,
        hx=hx.tolist(),
        hz=hz.tolist(),
        schedule=schedule,
    )


class ZeroIdleSynthesizer:
    """Search schedules for given terms, or cyclic (4,2) supports by dimension."""

    def __init__(self):
        self.lib = ct.CDLL(str(ROOT / "build/libqldpc.so"))
        array = np.ctypeslib.ndpointer(dtype=np.int32, flags="C_CONTIGUOUS")
        self.lib.hook_distance.argtypes = [
            ct.c_int,
            array,
            ct.c_int,
            array,
            array,
            ct.c_int,
            ct.c_int,
            ct.c_int,
        ]

    def schedule(self, group, A, B, k, distance, templates, reorder=True):
        mul = group_table(*group)
        if len(mul) > 64 or (len(A), len(B)) not in ((3, 3), (4, 2)):
            raise ValueError(
                "Hook search supports (3,3) and (4,2) at group order <= 64"
            )
        A, B = tuple(A), tuple(B)
        if (
            len(set(A)) != len(A)
            or len(set(B)) != len(B)
            or any(t not in range(len(mul)) for t in A + B)
            or not 1 <= distance <= 8
            or not 1 <= k < 2 * len(mul)
        ):
            raise ValueError("Invalid terms, logical dimension or target distance")
        for t in templates:
            if len(t) != 12 or any(v not in range(12) for v in t):
                raise ValueError("A template needs twelve tick indices in [0,11]")
            ticks = np.asarray(t, np.int32)
            for aa in permutations(A) if reorder else (A,):
                for bb in permutations(B) if reorder else (B,):
                    terms = np.asarray(aa + bb, np.int32)
                    d = self.lib.hook_distance(
                        len(mul), mul, len(aa), terms, ticks, max(t) + 1, distance, k
                    )
                    if d == distance:
                        return materialize(group, aa, bb, t, k, d)
        raise ValueError("No schedule witnessed the requested hook distance")

    def cyclic(self, n, k, distance=6):
        """Normalize binomial steps by units, then translation-prune four-term supports."""
        terms = np.empty(6, np.int32)
        ticks = np.empty(12, np.int32)
        arr = np.ctypeslib.ndpointer(dtype=np.int32, flags="C_CONTIGUOUS")
        self.lib.synthesize_cyclic42.argtypes = [ct.c_int] * 3 + [arr, arr]
        if self.lib.synthesize_cyclic42(n, k, distance, terms, ticks):
            raise ValueError("No witness in the canonical cyclic template search")
        return materialize(
            (n // 2, 1, 1),
            terms[:4].tolist(),
            terms[4:].tolist(),
            ticks.tolist(),
            k,
            distance,
        )


def search_seven(group, A, B, k, distance):
    """Separate the sectors before testing the paired CNOT ordering constraints."""
    s = ZeroIdleSynthesizer()
    arr = np.ctypeslib.ndpointer(dtype=np.int32, flags="C_CONTIGUOUS")
    f = s.lib.sector_distance
    f.argtypes = [ct.c_int, arr, ct.c_int, arr, arr, ct.c_int, ct.c_int]
    mul = group_table(*group)
    if (
        len(A) != 3
        or len(B) != 3
        or len(set(A)) != 3
        or len(set(B)) != 3
        or len(mul) > 64
        or any(t not in range(len(mul)) for t in (*A, *B))
        or not 2 <= distance <= 8
    ):
        raise ValueError("Expected two supported trinomials and distance in [2,8]")
    terms = np.array([*A, *B], np.int32)
    choices = []
    for z in (0, 1):
        cache = {}
        orders = []
        for order in permutations(range(6)):
            # Singlets and stabilizers are implicit. The two end pairs
            # and the middle triple determine all remaining hook cosets.
            end1 = tuple(sorted(order[:2]))
            end2 = tuple(sorted(order[-2:]))
            key = min(
                (end1, order[2], order[3], end2), (end2, order[3], order[2], end1)
            )
            if key not in cache:
                cache[key] = (
                    f(
                        len(mul),
                        mul,
                        3,
                        terms,
                        np.array(order, np.int32),
                        z,
                        distance - 1,
                    )
                    >= distance
                )
            if cache[key]:
                orders.append(order)
        if not orders:
            return None
        choices.append(orders)

    def layers(orders):
        for o in orders:
            for idle in range(7):
                seq = (*o[:idle], 6, *o[idle:])
                yield [seq.index(i) for i in range(6)]

    xlists = list(layers(choices[0]))
    for z in layers(choices[1]):
        for x in xlists:
            if set(x[:3]) & set(z[:3]) or set(x[3:]) & set(z[3:]):
                continue
            if all(
                (x[i] < z[j]) == (x[j + 3] < z[i + 3])
                for i in range(3)
                for j in range(3)
            ):
                times = tuple(x + z)
                try:
                    return s.schedule(
                        group, tuple(A), tuple(B), k, distance, [times], False
                    )
                except ValueError:
                    continue
    return None
