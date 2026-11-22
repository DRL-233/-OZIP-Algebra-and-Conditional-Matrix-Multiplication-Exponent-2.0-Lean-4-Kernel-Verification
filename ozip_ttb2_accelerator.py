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


def build_ozip_channel_packet(A_mat: np.ndarray, B_mat: np.ndarray, i: int, k: int) -> bytes:
    """
    Encodes the 3 Z_3 triality sector products (j in {0, 1, 2}) for output channel (i, k)
    of <3, 3, 2> matrix multiplication into a zero-copy TTB2 v0.2.0 wire packet.
    Inactive/zero bilinear terms carry status=0 and are bypassed via predicate-sparse jumps.
    """
    spokes = []
    for j in range(3):
        a_val = int(A_mat[i, j])
        b_val = int(B_mat[j, k])
        if a_val != 0 and b_val != 0:
            spokes.append(a_val * b_val)
        else:
            spokes.append({"status": 0})
    packet, _ = ttb2.from_json(spokes, embed_values=True)
    return packet


if __name__ == "__main__":
    A = np.array([[2, -1, 3], [0, 4, -2], [1, 5, 0]], dtype=np.int64)
    B = np.array([[3, 1], [-2, 4], [1, -1]], dtype=np.int64)

    C_ozip = np.zeros((3, 2), dtype=np.int64)
    total_wire_bytes = 0
    total_latency_us = 0.0

    for i in range(3):
        for k in range(2):
            pkt = build_ozip_channel_packet(A, B, i, k)
            total_wire_bytes += len(pkt)
            with ttb2.TTB2Engine(pkt) as engine:
                t0 = time.perf_counter()
                for _ in range(10000):
                    acc = engine.query_skip()
                total_latency_us += (time.perf_counter() - t0) * 1e6 / 10000
                C_ozip[i, k] = acc

    assert np.array_equal(C_ozip, A @ B), f"Mismatch: {C_ozip} vs {A @ B}"
    print("Exact <3,3,2> OZIP-TTB2 Result:\n", C_ozip)
    print(f"Total AVX2 Contraction Latency (6 channels): {total_latency_us:.3f} us | Total Wire Size: {total_wire_bytes} bytes")
