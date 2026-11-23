"""Combinatorial planar embeddings and wire lengths on a rectangular grid."""

import numpy as np
import networkx as nx
from .synthesizer import group_table


def analyze(code):
    a, b, r = code["group"]
    m = a * b
    n = 2 * m
    mul = group_table(a, b, r)
    A, B = code["A"], code["B"]
    # Each term and its transpose give one perfect matching on all 2n vertices.
    # Split into (2 A + 1 B) and the three remaining matchings.
    layers = [nx.Graph(), nx.Graph()]
    for side, terms in enumerate((A, B)):
        for j, t in enumerate(terms):
            layer = layers[int(j >= (1 if side else 2))]
            perm = mul[t, :] if side else mul[:, t]
            for i, q in enumerate(perm.tolist()):
                layer.add_edge(n + i, side * m + q)
                layer.add_edge(n + m + q, (1 - side) * m + i)
    shape = np.array([2 * a, 2 * b])

    def coord(u):
        block, i = divmod(u, m)
        x, y = divmod(i, b)
        return np.array((2 * x + (block in (1, 2)), 2 * y + (block in (1, 3))))

    result = []
    for layer in layers:
        if set(dict(layer.degree()).values()) != {3} or len(layer) != 2 * n:
            raise ValueError("Incomplete cubic layer")
        planar, embedding = nx.check_planarity(layer)
        if not planar:
            raise ValueError("Layer is nonplanar")
        embedding.check_structure()
        lengths = np.array([abs(coord(u) - coord(v)) for u, v in layer.edges])

        def stats(lengths):
            d = lengths.sum(axis=1)
            return dict(mean=float(d.mean()), max=int(d.max()))

        result.append(
            dict(
                rotation={i: list(embedding.neighbors_cw_order(i)) for i in layer},
                grid=stats(lengths),
                torus=stats(np.minimum(lengths, shape - lengths)),
            )
        )
    return result
