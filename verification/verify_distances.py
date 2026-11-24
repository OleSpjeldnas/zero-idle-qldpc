"""Independent lower bounds on the complete Stim detector model.

Parity projection can introduce new undetectable faults. Excluding them in the
projection therefore excludes them in the full circuit. Logical masks stay intact.
"""

from collections import defaultdict
from functools import lru_cache
import json
from pathlib import Path

import stim

from gross_distance import excludes_lifts, spatial_nines

ROOT = Path(__file__).resolve().parents[1]


def project(dem, period):
    coords = dem.get_detector_coordinates()
    width = 1 + max(int(v[1]) for v in coords.values())
    mapped = {
        d: (1 << (width * (int(t) % period) + int(j)) if side == 0 else 0)
        for d, (side, j, t) in coords.items()
    }
    events = set()
    for instruction in dem.flattened():
        if instruction.type != "error":
            continue
        syndrome = logical = 0
        for t in instruction.targets_copy():
            if t.is_relative_detector_id():
                syndrome ^= mapped[t.val]
            elif t.is_logical_observable_id():
                logical ^= 1 << t.val
        if syndrome or logical:
            events.add((syndrome, logical))
    return tuple(sorted(events))


def translation_roots(events, nx, ny):
    """Certify torus translations on the full projected fault signatures.

    Each detector permutation must permute the fault columns. Verify that the
    images respect every binary dependency of the augmented (syndrome, logical)
    columns. This induces a surjective linear map on their finite span, hence an
    automorphism. An invisible nonzero logical maps to another such logical.
    """
    masks = dict(events)
    if len(masks) != len(events):
        raise ValueError("multiple logical masks for one detector column")
    width = nx * ny
    roots = []
    covered = set()
    translations = []
    for dx in range(nx):
        for dy in range(ny):
            bits = [
                1 << (ny * ((i // ny + dx) % nx) + (i % ny + dy) % ny)
                for i in range(width)
            ]
            image = {}
            basis = {}
            for s, l in events:
                t, rem = 0, s
                while rem:
                    bit = rem & -rem
                    t ^= bits[bit.bit_length() - 1]
                    rem ^= bit
                q = masks[t]
                image[s, l] = t, q
                a, b = s | (l << width), t | (q << width)
                while a:
                    pivot = a.bit_length()
                    if pivot not in basis:
                        basis[pivot] = a, b
                        break
                    u, v = basis[pivot]
                    a, b = a ^ u, b ^ v
                if not a and b:
                    raise ValueError("translation breaks a logical dependency")
            if set(image.values()) != set(events):
                raise ValueError("translation does not preserve fault columns")
            translations.append(image)
    for event in events:
        if event not in covered:
            roots.append(event)
            covered.update(image[event] for image in translations)
    return roots


@lru_cache(maxsize=24)
def excludes(events, limit, torus=None):
    """Meet in the middle with two faults on the lookup side.

    Choose a member of a minimum logical set. At any nonzero partial syndrome
    at least one remaining column touches its lowest fired detector. Iterate
    every such column. Reusing a column cancels it in GF(2). A zero-syndrome,
    zero-logical prefix cannot occur in a minimum logical set.
    """
    pairs = {0: 0}
    incident = defaultdict(list)
    max_weight = max(s.bit_count() for s, _ in events)
    for i, (s, l) in enumerate(events):
        for t, v in ((0, 0), *events[:i]):
            key, value = s ^ t, l ^ v
            if pairs.setdefault(key, value) != value:
                return False  # At most four faults with unequal logical masks.
        fired = s
        while fired:
            bit = fired & -fired
            incident[bit].append((s, l))
            fired ^= bit

    def reaches(s, l, left):
        if left == 2:
            other = pairs.get(s)
            return other is not None and other != l
        if not s:
            return bool(l)
        if s.bit_count() > left * max_weight:
            return False
        return any(reaches(s ^ t, l ^ v, left - 1) for t, v in incident[s & -s])

    roots = (
        translation_roots(events, *torus) if torus else ((s, l) for s, l in events if l)
    )
    return not any(reaches(s, l, limit - 1) for s, l in roots)


def check_physical_witness(circuit, faults):
    record = stim.DetectorErrorModel(
        "\n".join("error(1) " + " ".join(row) for row in faults)
    )
    explained = circuit.explain_detector_error_model_errors(
        dem_filter=record, reduce_to_one_representative_error=True
    )
    parity = set()
    sites = set()
    if len(explained) != len(faults):
        raise ValueError("repeated or missing fault signatures")
    for e in explained:
        location = e.circuit_error_locations[0]
        sites.add(
            (
                location.stack_frames[0].instruction_offset,
                location.instruction_targets.target_range_start,
            )
        )
        parity.symmetric_difference_update(t.dem_target for t in e.dem_error_terms)
    if (
        len(sites) != len(faults)
        or not parity
        or not all(t.is_logical_observable_id() for t in parity)
    ):
        raise ValueError(
            "physical faults must be distinct and implement an invisible logical"
        )


if __name__ == "__main__":
    witnesses = json.loads((ROOT / "verification/faults.json").read_text())
    for path in sorted((ROOT / "circuits").glob("*.stim")):
        name = path.name.split("-r")[0]
        c = stim.Circuit.from_file(path)
        period = {"ibm72-published": 2, "ibm72-t7": 2, "n60-nonabelian": 5}.get(name, 1)
        lower = {"n70": 7, "ibm144-published": 9}.get(name, 6)
        events = project(c.detector_error_model(), period)
        torus = (12, 6) if name == "ibm144-published" else None
        if not excludes(events, lower - 1, torus):
            raise ValueError(f"{path.name} fails the projected lower bound {lower}")
        if torus:
            roots = tuple(translation_roots(events, *torus))
            nines = spatial_nines(events, roots)
            full = project(c.detector_error_model(), c.num_detectors // 144 + 1)
            if not excludes_lifts(events, full, nines):
                raise ValueError("a spatial weight-nine logical admits detector times")
            lower = 10
        if name in witnesses:
            check_physical_witness(c, witnesses[name])
        upper = (
            len(witnesses[name])
            if name in witnesses
            else len(
                json.loads((ROOT / "circuits" / (name + ".json")).read_text())[
                    "logical_x_witness"
                ]
            )
        )
        print(
            f"{path.name}    {lower} <= Z-memory fault distance <= {upper}", flush=True
        )
