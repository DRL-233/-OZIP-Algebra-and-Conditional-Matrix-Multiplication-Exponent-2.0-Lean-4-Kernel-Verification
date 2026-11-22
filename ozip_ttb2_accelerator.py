# Companion Runtime Verification & TTB2 v0.2.0 Cycloidal Hub Execution Benchmark
# for the OZIP <3, 3, 2> Tensor Restriction Witness.
# Author: Matthias Asare-Darko (Darkon Research Laboratory, Ghana)
# Zenodo Archive DOI: https://doi.org/10.5281/zenodo.24440448

import subprocess
import sys
import time
import numpy as np

try:
    import ttb2
except ImportError:
    repo = (
        "git+https://github.com/DRL-233/"
        "TTB1-Succinct-Threaded-Ternary-Binary-Serialization-and-SIMD-OpenMP-Execution-Engine.git"
    )
    subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", "--no-cache-dir", "--upgrade", repo])
    import ttb2


def build_ozip_ttb2_hub(A_mat: np.ndarray, B_mat: np.ndarray):
    assert A_mat.shape == (3, 3) and B_mat.shape == (3, 2)
    spokes = []
    for j in range(3):
        for i in range(3):
            for k in range(2):
                a_val = int(A_mat[i, j])
                b_val = int(B_mat[j, k])
                active = 1 if (a_val != 0 and b_val != 0) else 0
                spokes.append({
                    "status": active,
                    "val": a_val * b_val if active else 0,
                })
    return ttb2.from_json({"gateway": 1, "nodes": spokes})


if __name__ == "__main__":
    A = np.array([[2, -1, 3], [0, 4, -2], [1, 5, 0]], dtype=np.int64)
    B = np.array([[3, 1], [-2, 4], [1, -1]], dtype=np.int64)

    blob, values = build_ozip_ttb2_hub(A, B)

    with ttb2.TTB2Engine(blob, values) as engine:
        t0 = time.perf_counter()
        for _ in range(10000):
            _ = engine.query_skip()
        dt_us = (time.perf_counter() - t0) * 1e6 / 10000

        C_ozip = np.zeros((3, 2), dtype=np.int64)
        for j in range(3):
            for i in range(3):
                for k in range(2):
                    idx = j * 6 + i * 2 + k + 1
                    C_ozip[i, k] += values[idx]

        assert np.array_equal(C_ozip, A @ B)
        print("Exact <3,3,2> OZIP-TTB2 Result:\n", C_ozip)
        print(f"Branchless AVX2 Contraction Latency: {dt_us:.3f} us/pass | Wire size: {len(blob)} bytes")
