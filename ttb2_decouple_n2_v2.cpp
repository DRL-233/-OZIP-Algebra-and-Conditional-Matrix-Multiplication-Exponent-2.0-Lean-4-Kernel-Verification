
#include <cstdint>
#include <cstring>
#include <immintrin.h>

extern "C" {

struct DisjointBlock994 {
    int32_t A_idx[81];
    int32_t B_idx[36];
    int32_t C_idx[36];
};

int32_t verify_and_claim_block_avx2(
    const DisjointBlock994* blk,
    uint64_t* mask_A,
    uint64_t* mask_B,
    uint64_t* mask_C
) {
    uint64_t local_A[6] = {0};
    uint64_t local_B[6] = {0};
    uint64_t local_C[6] = {0};

    for (int i = 0; i < 81; ++i) {
        int v = blk->A_idx[i];
        if (v < 0 || v >= 324) return 0;
        uint64_t bit = 1ULL << (v & 63);
        if (local_A[v >> 6] & bit) return 0;
        local_A[v >> 6] |= bit;
    }
    for (int i = 0; i < 36; ++i) {
        int vb = blk->B_idx[i];
        int vc = blk->C_idx[i];
        if (vb < 0 || vb >= 324 || vc < 0 || vc >= 324) return 0;
        uint64_t bit_b = 1ULL << (vb & 63);
        uint64_t bit_c = 1ULL << (vc & 63);
        if ((local_B[vb >> 6] & bit_b) || (local_C[vc >> 6] & bit_c)) return 0;
        local_B[vb >> 6] |= bit_b;
        local_C[vc >> 6] |= bit_c;
    }

#ifdef __AVX2__
    if (!_mm256_testz_si256(_mm256_loadu_si256((const __m256i*)mask_A), _mm256_loadu_si256((const __m256i*)local_A))) return 0;
    if (!_mm256_testz_si256(_mm256_loadu_si256((const __m256i*)mask_B), _mm256_loadu_si256((const __m256i*)local_B))) return 0;
    if (!_mm256_testz_si256(_mm256_loadu_si256((const __m256i*)mask_C), _mm256_loadu_si256((const __m256i*)local_C))) return 0;
#endif
    for (int w = 0; w < 6; ++w) {
        if ((mask_A[w] & local_A[w]) || (mask_B[w] & local_B[w]) || (mask_C[w] & local_C[w])) return 0;
    }
    for (int w = 0; w < 6; ++w) {
        mask_A[w] |= local_A[w];
        mask_B[w] |= local_B[w];
        mask_C[w] |= local_C[w];
    }
    return 1;
}

int32_t search_n2_spoke_decoupled_v2(DisjointBlock994* out_blocks, int32_t max_blocks) {
    uint64_t mask_A[6] = {0};
    uint64_t mask_B[6] = {0};
    uint64_t mask_C[6] = {0};
    int32_t found = 0;

    for (int sp1 = 0; sp1 < 2; ++sp1) {
        for (int sp2 = 0; sp2 < 2; ++sp2) {
            if (found >= max_blocks) break;
            DisjointBlock994 cand;

            for (int r = 0; r < 9; ++r) {
                int g1 = r / 3, g2 = r % 3;
                for (int k = 0; k < 9; ++k) {
                    int i1 = k / 3, i2 = k % 3;
                    int id1 = 9 * sp1 + 3 * g1 + i1;
                    int id2 = 9 * sp2 + 3 * g2 + i2;
                    cand.A_idx[r * 9 + k] = 18 * id1 + id2;
                }
            }

            for (int k = 0; k < 9; ++k) {
                int i1 = k / 3, i2 = k % 3;
                for (int j = 0; j < 4; ++j) {
                    int j1 = j / 2, j2 = j % 2;
                    int g_b1 = (j1 + 1) % 3;
                    int g_b2 = (j2 + 1) % 3;
                    int id1 = 9 * sp1 + 3 * g_b1 + i1;
                    int id2 = 9 * sp2 + 3 * g_b2 + i2;
                    cand.B_idx[k * 4 + j] = 18 * id1 + id2;
                }
            }

            for (int r = 0; r < 9; ++r) {
                int g1 = r / 3, g2 = r % 3;
                for (int j = 0; j < 4; ++j) {
                    int j1 = j / 2, j2 = j % 2;
                    int g_c1 = (3 - ((g1 + j1 + 1) % 3)) % 3;
                    int g_c2 = (3 - ((g2 + j2 + 1) % 3)) % 3;
                    int id1 = 9 * sp1 + 3 * g_c1 + j1;
                    int id2 = 9 * sp2 + 3 * g_c2 + j2;
                    cand.C_idx[r * 4 + j] = 18 * id1 + id2;
                }
            }

            if (verify_and_claim_block_avx2(&cand, mask_A, mask_B, mask_C)) {
                out_blocks[found++] = cand;
            }
        }
    }
    return found;
}

}
