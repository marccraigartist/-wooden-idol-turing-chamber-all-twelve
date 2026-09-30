/-!
# THE FOUNDATION STONE — TEST 12X: WHERE THE DEAD GLOBE FORGETS ITS ORDER

Runs in the Lean live editor with no imports (core Lean only). Input to Test 12.

Test 11 separates two memories: order written into the GEOMETRY (different routes end
at different rotations) and order kept ALONGSIDE it (a history list). This file asks
where the 30° dead globe's own geometry first forgets the order of its moves.

Exact arithmetic: numbers `a + b√3`, and the two moves scaled by 2 so every entry is
exact: `Y = 2·Ry(30°)`, `Z = 2·Rz(30°)`.

Order of results:
1. Three 30° turns make a quarter-turn: `Y³ = 8·Ry(90°)`, `Z³ = 8·Rz(90°)`.
2. The quarter-turn pair `Ry(90°)·Rz(90°)` is the diagonal turn C that cycles the axes
   (x → y → z → x). It carries the y-axis onto the z-axis, so `C·Y = Z·C`.
3. Hence two DIFFERENT seven-move routes give the SAME rotation:
   `Y Y Y Z Z Z Y  =  Z Y Y Y Z Z Z`.
   (A computer check finds no coincidence among the 2 + 4 + … + 64 routes of length 1
   to 6, so seven is the first place the geometry forgets order.)
4. The reason is the finite cube living inside the infinite globe: the 90° control,
   built from three 30° steps, relabels one axis as the other.
-/
namespace WhereTheGlobeForgets

structure Z3 where
  a : Int
  b : Int
deriving DecidableEq

def Z3.add (x y : Z3) : Z3 := ⟨x.a + y.a, x.b + y.b⟩
def Z3.mul (x y : Z3) : Z3 := ⟨x.a * y.a + 3 * x.b * y.b, x.a * y.b + x.b * y.a⟩

/-- A 3 × 3 matrix with entries a + b√3, stored row by row. -/
structure M3 where
  e11 : Z3
  e12 : Z3
  e13 : Z3
  e21 : Z3
  e22 : Z3
  e23 : Z3
  e31 : Z3
  e32 : Z3
  e33 : Z3
deriving DecidableEq

def dot (p q r s t u : Z3) : Z3 := Z3.add (Z3.add (Z3.mul p s) (Z3.mul q t)) (Z3.mul r u)

def M3.mul (m n : M3) : M3 :=
  ⟨dot m.e11 m.e12 m.e13 n.e11 n.e21 n.e31, dot m.e11 m.e12 m.e13 n.e12 n.e22 n.e32,
   dot m.e11 m.e12 m.e13 n.e13 n.e23 n.e33,
   dot m.e21 m.e22 m.e23 n.e11 n.e21 n.e31, dot m.e21 m.e22 m.e23 n.e12 n.e22 n.e32,
   dot m.e21 m.e22 m.e23 n.e13 n.e23 n.e33,
   dot m.e31 m.e32 m.e33 n.e11 n.e21 n.e31, dot m.e31 m.e32 m.e33 n.e12 n.e22 n.e32,
   dot m.e31 m.e32 m.e33 n.e13 n.e23 n.e33⟩

def z (n : Int) : Z3 := ⟨n, 0⟩
def r3 : Z3 := ⟨0, 1⟩

/-- `2·Ry(30°)`. -/
def Y : M3 := ⟨r3, z 0, z 1,  z 0, z 2, z 0,  z (-1), z 0, r3⟩
/-- `2·Rz(30°)`. -/
def Z : M3 := ⟨r3, z (-1), z 0,  z 1, r3, z 0,  z 0, z 0, z 2⟩

def scale (k : Int) (m : M3) : M3 :=
  ⟨Z3.mul (z k) m.e11, Z3.mul (z k) m.e12, Z3.mul (z k) m.e13,
   Z3.mul (z k) m.e21, Z3.mul (z k) m.e22, Z3.mul (z k) m.e23,
   Z3.mul (z k) m.e31, Z3.mul (z k) m.e32, Z3.mul (z k) m.e33⟩

/-- `Ry(90°)`, `Rz(90°)` and the diagonal turn `C = Ry(90°)·Rz(90°)`. -/
def Ry90 : M3 := ⟨z 0, z 0, z 1,  z 0, z 1, z 0,  z (-1), z 0, z 0⟩
def Rz90 : M3 := ⟨z 0, z (-1), z 0,  z 1, z 0, z 0,  z 0, z 0, z 1⟩
def C : M3 := ⟨z 0, z 0, z 1,  z 1, z 0, z 0,  z 0, z 1, z 0⟩

/-- 1. Three 30° turns are a quarter-turn. -/
theorem three_thirties_are_a_quarter :
    M3.mul Y (M3.mul Y Y) = scale 8 Ry90 ∧ M3.mul Z (M3.mul Z Z) = scale 8 Rz90 := by
  decide

/-- 2a. The two quarter-turns make the diagonal turn that cycles the axes. -/
theorem quarter_pair_is_the_diagonal_turn : M3.mul Ry90 Rz90 = C := by decide

/-- 2b. The diagonal turn relabels the y-move as the z-move. -/
theorem diagonal_turn_relabels_the_axes : M3.mul C Y = M3.mul Z C := by decide

def word : List M3 → M3
  | [] => ⟨z 1, z 0, z 0, z 0, z 1, z 0, z 0, z 0, z 1⟩
  | m :: rest => M3.mul m (word rest)

/-- 3. Two different seven-move routes, one rotation: YYYZZZY = ZYYYZZZ. -/
theorem seven_moves_forget_order :
    word [Y, Y, Y, Z, Z, Z, Y] = word [Z, Y, Y, Y, Z, Z, Z] := by decide +kernel

/-- The companion pair at seven: YZZZYYY = ZZZYYYZ. -/
theorem seven_moves_forget_order' :
    word [Y, Z, Z, Z, Y, Y, Y] = word [Z, Z, Z, Y, Y, Y, Z] := by decide +kernel

/-- Control: at one step the order still shows. -/
theorem one_step_remembers : M3.mul Y Z ≠ M3.mul Z Y := by decide

#print axioms three_thirties_are_a_quarter
#print axioms quarter_pair_is_the_diagonal_turn
#print axioms diagonal_turn_relabels_the_axes
#print axioms seven_moves_forget_order
#print axioms seven_moves_forget_order'
#print axioms one_step_remembers

end WhereTheGlobeForgets
