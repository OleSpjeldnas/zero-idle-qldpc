import itertools
import json
from pathlib import Path
import unittest
import time

import numpy as np
import stim

from zero_idle_qldpc import SpaceTimeDecoder, ZeroIdleSynthesizer
from zero_idle_qldpc.decoder import Mechanisms
from zero_idle_qldpc.layout import analyze
from zero_idle_qldpc.synthesizer import ROOT, group_table


class PackageTests(unittest.TestCase):
    def test_minimum_cost_triple(self):
        support = [(0, 1), (0, 2), (1, 3), (2, 3)]
        costs = np.array([3, 0.9, 0.9, 0.9])
        masks = np.array([0, 1, 0, 0], np.uint64)
        for perm in itertools.permutations(range(4)):
            ids = list(perm)
            model = Mechanisms(
                4,
                1,
                np.arange(0, 9, 2),
                np.array([support[i] for i in ids]).ravel(),
                1 / (1 + np.exp(costs[ids])),
                masks[ids],
            )
            self.assertEqual(
                SpaceTimeDecoder(model).decode(np.array([3], np.uint8))[0], 1
            )

    def test_gross_scalar_shuffled(self):
        for r in (4, 12):
            c = stim.Circuit.from_file(
                ROOT / f"circuits/ibm144-published-r{r}-p0.002.stim"
            )
            self.assertEqual(c.num_detectors, 144 * r)
            d = SpaceTimeDecoder(c.detector_error_model())
            syn = c.compile_detector_sampler(seed=1137).sample(64, bit_packed=True)
            order = np.random.default_rng(714).permutation(len(syn))
            pred = np.array([d.decode(row) for row in syn])
            np.testing.assert_array_equal(d.decode(syn[order]), pred[order])
            np.testing.assert_array_equal(d.decode(syn[0]), pred[0])
            with self.assertRaises(ValueError):
                d.decode(syn[:, :-1])

    def test_limits(self):
        for d, k in ((2048, 64), (2049, 64), (2048, 65)):
            model = Mechanisms(
                d,
                k,
                np.array([0, 1]),
                np.array([d - 1]),
                np.array([0.01]),
                np.array([1 << 63], np.uint64),
            )
            if d == 2048 and k == 64:
                row = np.zeros(256, np.uint8)
                row[-1] = 128
                self.assertEqual(SpaceTimeDecoder(model).decode(row)[63], 1)
            else:
                with self.assertRaises(ValueError):
                    SpaceTimeDecoder(model)

    def test_constructions(self):
        for path in sorted((ROOT / "circuits").glob("*.json")):
            code = json.loads(path.read_text())
            layout = analyze(code)
            import networkx as nx

            actual = set()
            for i, layer in enumerate(layout):
                rotation = code["layout"][i]["rotation"]
                embedding = nx.PlanarEmbedding()
                embedding.set_data({int(v): nbrs for v, nbrs in rotation.items()})
                embedding.check_structure()
                edges = {tuple(sorted(e)) for e in embedding.edges()}
                self.assertFalse(actual & edges)
                actual.update(edges)
                self.assertEqual(layer["grid"], code["layout"][i]["grid"])
                rot = layer["rotation"]
                self.assertTrue(all(len(neighbors) == 3 for neighbors in rot.values()))
            self.assertEqual(
                actual,
                {tuple(sorted(edge)) for tick in code["schedule"] for edge in tick},
            )
            if path.stem == "n60-nonabelian":
                table = group_table(*code["group"])
                self.assertTrue(np.any(table != table.T))
            if path.stem == "n84":
                start = time.perf_counter()
                fresh = ZeroIdleSynthesizer().cyclic(84, 8)
                elapsed = time.perf_counter() - start
                print(f"n=84 fresh cyclic synthesis: {elapsed:.4f} s")
                self.assertLess(elapsed, 1.2)
                self.assertEqual(fresh["hx"], code["hx"])
                self.assertEqual(fresh["d"], 6)


class IndependentCheckerTests(unittest.TestCase):
    def test_rejects_circuit_mutations(self):
        import importlib.util
        import tempfile

        spec = importlib.util.spec_from_file_location(
            "cert_check", ROOT / "verification/verify_circuits.py"
        )
        checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(checker)
        source = ROOT / "circuits/n84-r4-p0.002.stim"
        original = source.read_text()
        with tempfile.TemporaryDirectory() as directory:
            checker.ROOT = Path(directory)
            (checker.ROOT / "n84.json").write_bytes(
                (source.parent / "n84.json").read_bytes()
            )
            path = checker.ROOT / source.name
            for start in (
                "DEPOLARIZE1(",
                "DEPOLARIZE2(",
                "TICK",
                "DETECTOR(",
                "OBSERVABLE_INCLUDE(",
            ):
                lines = original.splitlines()
                # Drop a CNOT-layer boundary (the initial preparation tick can be redundant).
                i = next(
                    i
                    for i, line in enumerate(lines)
                    if line.startswith(start) and i > 10
                )
                del lines[i]
                path.write_text("\n".join(lines))
                with self.subTest(removed=start), self.assertRaises(ValueError):
                    checker.verify(path)

    def test_checker_has_no_local_imports(self):
        import ast

        script = (ROOT / "verification/verify_circuits.py").read_text()
        self.assertLess(len(script.splitlines()), 150)
        imports = set()
        for node in ast.walk(ast.parse(script)):
            if isinstance(node, ast.Import):
                imports.update(x.name for x in node.names)
            elif isinstance(node, ast.ImportFrom):
                imports.add(node.module)
        self.assertLessEqual(imports, {"json", "re", "pathlib", "numpy", "stim"})

    def test_published_directions_and_distances(self):
        from zero_idle_qldpc.synthesizer import group_table

        synth = ZeroIdleSynthesizer()
        for path in (ROOT / "circuits").glob("*.json"):
            c = json.loads(path.read_text())
            m = c["n"] // 2
            if m <= 64:
                terms = np.array(c["A"] + c["B"], np.int32)
                times = np.array(c["times"], np.int32)
                actual = synth.lib.hook_distance(
                    m,
                    group_table(*c["group"]),
                    len(c["A"]),
                    terms,
                    times,
                    len(c["schedule"]),
                    -c["data_distance"],
                    c["k"],
                )
                self.assertEqual(actual, c["data_distance"], path.stem)
            if not path.stem.endswith("published"):
                continue
            shifts = [(3, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)]
            sx = [None, 1, 4, 3, 5, 0, 2]
            sz = [3, 5, 0, 1, 2, 4, None]
            for tick, (xterm, zterm) in enumerate(zip(sx, sz)):
                expected = set()
                for i in range(m):
                    for z, t in ((False, xterm), (True, zterm)):
                        if t is None:
                            continue
                        a, b = shifts[(t + 3) % 6] if z else shifts[t]
                        sign = -1 if z else 1
                        q = (
                            ((i // 6 + sign * a) % (m // 6)) * 6
                            + (i % 6 + sign * b) % 6
                            + (t >= 3) * m
                        )
                        expected.add((q, 3 * m + i) if z else (2 * m + i, q))
                self.assertEqual(expected, set(map(tuple, c["schedule"][tick])))
