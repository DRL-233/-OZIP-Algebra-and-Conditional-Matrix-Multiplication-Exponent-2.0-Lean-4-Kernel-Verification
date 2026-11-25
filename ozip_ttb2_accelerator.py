"""
ozip_ttb2_accelerator.py — Native C/AVX2 Bridge between OZIP-Algebra v2.0.0+
(DOI: 10.5281/zenodo.24528210) and TTB v0.3.0 / TTB3-Bridge (DOI: 10.5281/zenodo.24379185).

Executes Lean-4-verified <3, 3, 2> Z3-triality contractions and mixed-radix
psi1(s, g, i) = 9s + 3g + i index mappings directly through TTB3-Bridge's
C/AVX2/OpenMP runtime.
"""
from typing import Sequence, List
import ttb2


def psi1(s: int, g: int, i: int) -> int:
    """
    Lean-4-verified mixed-radix bijection psi1(s, g, i) = 9s + 3g + i in Fin 18
    (OZIPDecouplingInductive.lean).
    """
    if hasattr(ttb2, "ozip_psi1"):
        return ttb2.ozip_psi1(s, g, i)
    return 9 * s + 3 * g + i


def contract_3x3x2(A: Sequence[int], B: Sequence[int]) -> List[int]:
    """
    Executes a single-sweep <3, 3, 2> Z3-triality contraction across all 6 output
    channels in native C/AVX2 via ttb2.ozip_contract_3x3x2() (OZIPTheorem5_1.lean).

    Args:
        A: Flat 9-element sequence (3x3 row-major integer matrix).
        B: Flat 6-element sequence (3x2 row-major integer matrix).

    Returns:
        Flat 6-element list [C_00, C_01, C_10, C_11, C_20, C_21] = A @ B.
    """
    if len(A) != 9 or len(B) != 6:
        raise ValueError(f"Expected 9 elements for A and 6 for B, got {len(A)} and {len(B)}")

    if hasattr(ttb2, "ozip_contract_3x3x2"):
        return ttb2.ozip_contract_3x3x2(A, B)

    # Pure-Python fallback if running against TTB < 0.3.0
    return [
        sum(int(A[i * 3 + g]) * int(B[g * 2 + j]) for g in range(3))
        for i in range(3)
        for j in range(2)
    ]


def contract_triality_manifold(
    sectors_A: Sequence[Sequence[int]],
    sectors_B: Sequence[Sequence[int]],
    prune_threshold: int = 999999999,
) -> dict:
    """
    Contracts a collection of disjoint <3, 3, 2> Z3-triality sectors through
    TTB3-Bridge's native contraction kernel, then aggregates active sector energies
    inside a 64-byte aligned TTB2 cycloidal hub with branchless AVX2 pruning.
    """
    if len(sectors_A) != len(sectors_B):
        raise ValueError("sectors_A and sectors_B must have the same number of blocks")

    contracted_blocks = [
        contract_3x3x2(a_blk, b_blk)
        for a_blk, b_blk in zip(sectors_A, sectors_B)
    ]

    workload = {
        "n_sectors": len(contracted_blocks),
        "spokes": [
            {
                "sector_id": idx,
                "channels": blk,
            }
            for idx, blk in enumerate(contracted_blocks)
        ],
    }

    packet, _ = ttb2.from_json(workload, embed_values=True, embed_width="auto")
    with ttb2.TTB2Engine(packet, skip_sentinel=prune_threshold) as eng:
        active_energy = eng.query_skip(prune_threshold)
        total_energy = eng.sum_leaves()

    return {
        "ttb_version": getattr(ttb2, "__version__", "unknown"),
        "wire_bytes": len(packet),
        "blocks": contracted_blocks,
        "active_energy": active_energy,
        "total_energy": total_energy,
    }
