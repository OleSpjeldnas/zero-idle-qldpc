"""Packed little-endian detector input, unpacked binary logical frames."""

import ctypes as ct
from dataclasses import dataclass
import threading

import numpy as np

from .synthesizer import ROOT


@dataclass
class Mechanisms:
    detectors: int
    observables: int
    offsets: np.ndarray
    indices: np.ndarray
    probabilities: np.ndarray
    masks: np.ndarray

    @classmethod
    def from_dem(cls, dem):
        if not 1 <= dem.num_detectors <= 2048 or not 0 <= dem.num_observables <= 64:
            raise ValueError("Unsupported number of detectors or observables")
        offsets, indices, probs, masks = [0], [], [], []
        for instruction in dem.flattened():
            if instruction.type != "error":
                continue
            mask = 0
            ds = set()
            for t in instruction.targets_copy():
                if t.is_relative_detector_id():
                    ds.symmetric_difference_update([t.val])
                if t.is_logical_observable_id():
                    mask ^= 1 << t.val
            indices.extend(sorted(ds))
            offsets.append(len(indices))
            probs.append(instruction.args_copy()[0])
            masks.append(mask)
        return cls(
            dem.num_detectors,
            dem.num_observables,
            np.array(offsets, np.int32),
            np.array(indices, np.int32),
            np.array(probs),
            np.array(masks, np.uint64),
        )


class SpaceTimeDecoder:
    def __init__(self, model, *, reference=False):
        model = model if isinstance(model, Mechanisms) else Mechanisms.from_dem(model)
        self.detectors, self.observables = model.detectors, model.observables
        if not 1 <= model.detectors <= 2048 or not 0 <= model.observables <= 64:
            raise ValueError("Expected 1..2048 detectors and 0..64 observables")
        self._lock = threading.Lock()
        self._lib = ct.CDLL(str(ROOT / "build/libqldpc.so"))
        family = "bposd" if reference else "spacetime"
        create = getattr(self._lib, "create_" + family + "_decoder")
        create.argtypes = [ct.c_int] * 3 + [ct.c_void_p] * 4
        create.restype = ct.c_void_p
        self._destroy = getattr(self._lib, "destroy_" + family + "_decoder")
        self._destroy.argtypes = [ct.c_void_p]
        self._decode = getattr(self._lib, "decode_" + family + "_batch")
        self._decode.argtypes = [
            ct.c_void_p,
            ct.c_void_p,
            ct.c_int,
            ct.c_int,
            ct.c_int,
            ct.c_float,
            ct.c_float,
        ]
        self._params = (20, 0.85, 0.75, 2, 20) if reference else (8, 0.82, 0.78)
        if reference:
            self._decode.argtypes += [ct.c_int, ct.c_int]
        self._decode.argtypes += [ct.c_void_p]
        prob = np.asarray(model.probabilities)
        if prob.ndim != 1 or not np.all((0 < prob) & (prob < 0.5)):
            raise ValueError("Expected positive mechanism probabilities below one half")
        llr = np.ascontiguousarray(np.log((1 - prob) / prob), np.float32)
        offsets = np.ascontiguousarray(model.offsets, np.int32)
        indices = np.ascontiguousarray(model.indices, np.int32)
        masks = np.ascontiguousarray(model.masks, np.uint64)
        if (
            offsets.shape != (len(prob) + 1,)
            or masks.shape != prob.shape
            or indices.ndim != 1
            or offsets[0] != 0
            or offsets[-1] != len(indices)
            or np.any(np.diff(offsets) < 0)
            or np.any(indices < 0)
            or np.any(indices >= model.detectors)
        ):
            raise ValueError("Malformed detector incidence arrays")
        self._ptr = create(
            model.detectors,
            len(prob),
            model.observables,
            *(x.ctypes.data for x in (offsets, indices, llr, masks)),
        )
        if not self._ptr:
            raise ValueError("Native decoder rejected model")

    def __del__(self):
        if getattr(self, "_ptr", None):
            self._destroy(self._ptr)

    def decode(self, packed):
        array = np.asarray(packed)
        if (
            array.dtype != np.uint8
            or array.ndim not in (1, 2)
            or array.shape[-1] != (self.detectors + 7) // 8
        ):
            raise ValueError(
                "Expected packed uint8 syndromes, little-endian by detector index"
            )
        syn = np.ascontiguousarray(np.atleast_2d(array))
        out = np.empty((len(syn), self.observables), np.uint8)
        with self._lock:
            rc = self._decode(
                self._ptr,
                syn.ctypes.data,
                len(syn),
                syn.shape[1],
                *self._params,
                out.ctypes.data,
            )
        if rc:
            raise RuntimeError(f"Native decode failed ({rc})")
        return out[0] if array.ndim == 1 else out
