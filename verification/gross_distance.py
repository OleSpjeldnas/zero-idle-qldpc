"""Exact nine-fault exclusion for the published 144-qubit Gross Z memories."""

from collections import defaultdict
from functools import lru_cache


@lru_cache(maxsize=2)
def spatial_nines(events, roots):
    """Enumerate all spatial weight-nine logical supports through a root orbit.

    The caller has excluded weights through eight. A proper prefix of a minimum
    solution has nonzero syndrome, so its least fired check anchors a remaining
    fault. At depth three, join a column at that check with every matching pair.
    Two pairs with equal syndrome must have equal frame by the four-fault bound.
    """
    positions = {e: i for i, e in enumerate(events)}
    incident = defaultdict(list)
    pairs = defaultdict(list)
    frame = {}
    maximum = max(s.bit_count() for s, _ in events)
    for i, (s, l) in enumerate(events):
        b = s
        while b:
            low = b & -b
            incident[low].append((i, s, l))
            b ^= low
        for j, (t, v) in enumerate(events[:i]):
            key = s ^ t
            if frame.setdefault(key, l ^ v) != l ^ v:
                raise ValueError("violated four-fault bound")
            pairs[key].append((j, i))

    @lru_cache(160000)
    def triples(s):
        found = []
        if s and s.bit_count() <= 3 * maximum:
            for i, t, v in incident[s & -s]:
                key = s ^ t
                if key in frame:
                    found.append((i, key, frame[key] ^ v))
        return found

    solutions = set()

    def visit(path, s, l, left):
        if s.bit_count() > left * maximum or not s:
            return
        if left == 3:
            for i, key, v in triples(s):
                if v != l:
                    for j, k in pairs[key]:
                        ids = tuple(sorted((*path, i, j, k)))
                        if len(set(ids)) == 9:
                            solutions.add(ids)
        else:
            for i, t, v in incident[s & -s]:
                if i not in path:
                    visit((*path, i), s ^ t, l ^ v, left - 1)

    for e in roots:
        visit((positions[e],), *e, 8)
    return tuple(sorted(solutions))


def can_cancel(domains):
    """Choose one time signature per spatial column. Each detector parity must vanish."""
    if any(not d for d in domains):
        return False
    width = 72
    sites = defaultdict(set)
    for i, terms in enumerate(domains):
        for v in terms:
            while v:
                bit = v & -v
                sites[(bit.bit_length() - 1) % width].add(i)
                v ^= bit
    parts = {}
    for q, ids in sites.items():
        for i in ids:
            values = {}
            for s in domains[i]:
                parity = 0
                v = s >> q
                t = 0
                while v:
                    parity |= (v & 1) << t
                    v >>= width
                    t += 1
                values[s] = parity
            parts[i, q] = values

    def solve(domains):
        domains = list(domains)
        while True:
            changed = False
            for q, ids in sites.items():
                ids = tuple(ids)
                values = [{parts[i, q][v] for v in domains[i]} for i in ids]
                for j, i in enumerate(ids):
                    allowed = {0}
                    for k, vs in enumerate(values):
                        if j != k:
                            allowed = {v ^ w for v in allowed for w in vs}
                    new = tuple(v for v in domains[i] if parts[i, q][v] in allowed)
                    if not new:
                        return False
                    if len(new) < len(domains[i]):
                        domains[i] = new
                        changed = True
            if not changed:
                break
        options = [i for i, d in enumerate(domains) if len(d) > 1]
        if not options:
            return True
        i = min(options, key=lambda j: len(domains[j]))
        for v in domains[i]:
            new = domains.copy()
            new[i] = (v,)
            if solve(new):
                return True
        return False

    return solve(domains)


@lru_cache(maxsize=4)
def excludes_lifts(events, real, supports):
    """Verify time-resolved closure under the two generators of torus translations.

    The augmented spatial action was verified linear. At each measurement time
    it permutes detector coordinates. Its image frame is fixed by the translated
    spatial syndrome. This check lets us lift one representative per spatial orbit.
    """
    width = 72
    mask = (1 << width) - 1

    def collapse(s):
        value = 0
        while s:
            value ^= s & mask
            s >>= width
        return value

    options = defaultdict(list)
    frame = dict(events)
    frame[0] = 0
    for s, o in real:
        spatial = collapse(s)
        if frame[spatial] != o:
            raise ValueError("time and spatial frames disagree")
        options[spatial, o].append(s)
    real = set(real)
    for dx, dy in ((1, 0), (0, 1)):
        size = max(s.bit_length() for s, o in real)
        shifts = [
            1
            << (
                width * (b // width)
                + 6 * ((b % width // 6 + dx) % 12)
                + (b % 6 + dy) % 6
            )
            for b in range(size)
        ]
        for s, o in real:
            v = s
            other = 0
            while v:
                bit = v & -v
                other ^= shifts[bit.bit_length() - 1]
                v ^= bit
            if (other, frame[collapse(other)]) not in real:
                raise ValueError("time translation broke closure")
    return not any(can_cancel([options[events[i]] for i in ids]) for ids in supports)
