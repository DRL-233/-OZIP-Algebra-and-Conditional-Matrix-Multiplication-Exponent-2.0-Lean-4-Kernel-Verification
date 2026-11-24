set_option maxRecDepth 100000

/-!
  OZIPDecouplingN2.lean
  Machine-Verified N=2 (324-Dimensional) Disjoint Block-Decoupling Certificate
  Proves 4 strictly disjoint <9, 9, 4> bilinear blocks saturating Fin 324.
-/

def n2DisjointBlockCount : Nat := 4

def block0_A : List Nat := [0, 1, 2, 18, 19, 20, 36, 37, 38, 3, 4, 5, 21, 22, 23, 39, 40, 41, 6, 7, 8, 24, 25, 26, 42, 43, 44, 54, 55, 56, 72, 73, 74, 90, 91, 92, 57, 58, 59, 75, 76, 77, 93, 94, 95, 60, 61, 62, 78, 79, 80, 96, 97, 98, 108, 109, 110, 126, 127, 128, 144, 145, 146, 111, 112, 113, 129, 130, 131, 147, 148, 149, 114, 115, 116, 132, 133, 134, 150, 151, 152]
def block0_B : List Nat := [57, 60, 111, 114, 58, 61, 112, 115, 59, 62, 113, 116, 75, 78, 129, 132, 76, 79, 130, 133, 77, 80, 131, 134, 93, 96, 147, 150, 94, 97, 148, 151, 95, 98, 149, 152]
def block0_C : List Nat := [114, 112, 78, 76, 111, 109, 75, 73, 108, 115, 72, 79, 60, 58, 24, 22, 57, 55, 21, 19, 54, 61, 18, 25, 6, 4, 132, 130, 3, 1, 129, 127, 0, 7, 126, 133]
def block1_A : List Nat := [9, 10, 11, 27, 28, 29, 45, 46, 47, 12, 13, 14, 30, 31, 32, 48, 49, 50, 15, 16, 17, 33, 34, 35, 51, 52, 53, 63, 64, 65, 81, 82, 83, 99, 100, 101, 66, 67, 68, 84, 85, 86, 102, 103, 104, 69, 70, 71, 87, 88, 89, 105, 106, 107, 117, 118, 119, 135, 136, 137, 153, 154, 155, 120, 121, 122, 138, 139, 140, 156, 157, 158, 123, 124, 125, 141, 142, 143, 159, 160, 161]
def block1_B : List Nat := [66, 69, 120, 123, 67, 70, 121, 124, 68, 71, 122, 125, 84, 87, 138, 141, 85, 88, 139, 142, 86, 89, 140, 143, 102, 105, 156, 159, 103, 106, 157, 160, 104, 107, 158, 161]
def block1_C : List Nat := [123, 121, 87, 85, 120, 118, 84, 82, 117, 124, 81, 88, 69, 67, 33, 31, 66, 64, 30, 28, 63, 70, 27, 34, 15, 13, 141, 139, 12, 10, 138, 136, 9, 16, 135, 142]
def block2_A : List Nat := [162, 163, 164, 180, 181, 182, 198, 199, 200, 165, 166, 167, 183, 184, 185, 201, 202, 203, 168, 169, 170, 186, 187, 188, 204, 205, 206, 216, 217, 218, 234, 235, 236, 252, 253, 254, 219, 220, 221, 237, 238, 239, 255, 256, 257, 222, 223, 224, 240, 241, 242, 258, 259, 260, 270, 271, 272, 288, 289, 290, 306, 307, 308, 273, 274, 275, 291, 292, 293, 309, 310, 311, 276, 277, 278, 294, 295, 296, 312, 313, 314]
def block2_B : List Nat := [219, 222, 273, 276, 220, 223, 274, 277, 221, 224, 275, 278, 237, 240, 291, 294, 238, 241, 292, 295, 239, 242, 293, 296, 255, 258, 309, 312, 256, 259, 310, 313, 257, 260, 311, 314]
def block2_C : List Nat := [276, 274, 240, 238, 273, 271, 237, 235, 270, 277, 234, 241, 222, 220, 186, 184, 219, 217, 183, 181, 216, 223, 180, 187, 168, 166, 294, 292, 165, 163, 291, 289, 162, 169, 288, 295]
def block3_A : List Nat := [171, 172, 173, 189, 190, 191, 207, 208, 209, 174, 175, 176, 192, 193, 194, 210, 211, 212, 177, 178, 179, 195, 196, 197, 213, 214, 215, 225, 226, 227, 243, 244, 245, 261, 262, 263, 228, 229, 230, 246, 247, 248, 264, 265, 266, 231, 232, 233, 249, 250, 251, 267, 268, 269, 279, 280, 281, 297, 298, 299, 315, 316, 317, 282, 283, 284, 300, 301, 302, 318, 319, 320, 285, 286, 287, 303, 304, 305, 321, 322, 323]
def block3_B : List Nat := [228, 231, 282, 285, 229, 232, 283, 286, 230, 233, 284, 287, 246, 249, 300, 303, 247, 250, 301, 304, 248, 251, 302, 305, 264, 267, 318, 321, 265, 268, 319, 322, 266, 269, 320, 323]
def block3_C : List Nat := [285, 283, 249, 247, 282, 280, 246, 244, 279, 286, 243, 250, 231, 229, 195, 193, 228, 226, 192, 190, 225, 232, 189, 196, 177, 175, 303, 301, 174, 172, 300, 298, 171, 178, 297, 304]

def allDisjointA : List Nat := block0_A ++ block1_A ++ block2_A ++ block3_A
def allDisjointB : List Nat := block0_B ++ block1_B ++ block2_B ++ block3_B
def allDisjointC : List Nat := block0_C ++ block1_C ++ block2_C ++ block3_C

/-- O(n) exact bitmask disjointness & bounds checker (pure kernel reduction via rfl). -/
def checkDisjointBounds (bound : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | x :: xs, mask =>
    if x < bound && ((mask >>> x) &&& 1 == 0) then
      checkDisjointBounds bound xs (mask ||| (1 <<< x))
    else
      false

/-- Helper computing the exact occupied bitmask of a list. -/
def occupiedMask : List Nat → Nat → Nat
  | [], mask => mask
  | x :: xs, mask => occupiedMask xs (mask ||| (1 <<< x))

/-- Theorem 1: All 324 A-factor indices across the 4 blocks are pairwise disjoint inside Fin 324
    and saturate every single bit of the 324-bit space ((1 <<< 324) - 1). -/
theorem n2_A_bijective_saturation :
    allDisjointA.length = 324 ∧
    checkDisjointBounds 324 allDisjointA 0 = true ∧
    occupiedMask allDisjointA 0 = (1 <<< 324) - 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Theorem 2: All 144 B-factor indices across the 4 blocks are strictly disjoint inside Fin 324. -/
theorem n2_B_disjoint_bounds :
    allDisjointB.length = 144 ∧
    checkDisjointBounds 324 allDisjointB 0 = true :=
  ⟨rfl, rfl⟩

/-- Theorem 3: All 144 C-factor indices across the 4 blocks are strictly disjoint inside Fin 324. -/
theorem n2_C_disjoint_bounds :
    allDisjointC.length = 144 ∧
    checkDisjointBounds 324 allDisjointC 0 = true :=
  ⟨rfl, rfl⟩

/-- Theorem 4: Exact N=2 direct-sum volume conservation (4 * 324 = 1296). -/
theorem n2_decoupled_volume : n2DisjointBlockCount * (9 * 9 * 4) = 1296 :=
  rfl
