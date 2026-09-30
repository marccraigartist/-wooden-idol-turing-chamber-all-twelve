/-!
# THE FOUNDATION STONE — TEST 15X: THE ORDER RESIDUE (HOLONOMY) NEVER CANCELS

Runs in the Lean live editor with no imports (core Lean only). Input to Test 15C.

Test 15B shows the two 30° orders send the seat point to different places. Test 15C asks
whether ordered motion leaves an intrinsic defect. This file measures the cleanest one:
go round the little square loop

    turn back about y, turn back about z, turn forward about y, turn forward about z

(the commutator Rz·Ry·Rz⁻¹·Ry⁻¹). If order did not matter, this loop would do nothing.
No counter and no height: the state is only an exact point in ℤ[√3]³.

Order of results:
1. The loop, built from the four primitive turns (each scaled by 2, so 16 overall), is
   an exact matrix over ℤ[√3].
2. Its trace is (33 + 8√3)/16, so it turns by an angle with cosine 17/32 + √3/4
   (about 15.36°). It is not the identity: the order leaves a residue.
3. Going round the loop again and again NEVER brings the x-axis point back, and never
   revisits an earlier position. The residue does not cancel by repetition.
   (Same parity method as Bucket 3 and Test 14X.)

Precedent in the record: "holonomy = the area you enclosed", computed 24 July.
-/
namespace OrderResidue

structure Z3 where
  a : Int
  b : Int
deriving DecidableEq

structure V3 where
  x : Z3
  y : Z3
  z : Z3
deriving DecidableEq

def zadd (u v : Z3) : Z3 := ⟨u.a + v.a, u.b + v.b⟩
def zneg (u : Z3) : Z3 := ⟨-u.a, -u.b⟩
def zroot (u : Z3) : Z3 := ⟨3 * u.b, u.a⟩
def zscale (k : Int) (u : Z3) : Z3 := ⟨k * u.a, k * u.b⟩

/-- `2 Rz(30°)`, `2 Ry(30°)` and their reverses `2 Rz(−30°)`, `2 Ry(−30°)`. -/
def rz2 (v : V3) : V3 := ⟨zadd (zroot v.x) (zneg v.y), zadd v.x (zroot v.y), zscale 2 v.z⟩
def ry2 (v : V3) : V3 := ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩
def rz2back (v : V3) : V3 := ⟨zadd (zroot v.x) v.y, zadd (zneg v.x) (zroot v.y), zscale 2 v.z⟩
def ry2back (v : V3) : V3 := ⟨zadd (zroot v.x) (zneg v.z), zscale 2 v.y, zadd v.x (zroot v.z)⟩

/-- The square loop: back about y, back about z, forward about y, forward about z. -/
def loop (v : V3) : V3 := rz2 (ry2 (rz2back (ry2back v)))

/-- 1. The loop as one exact matrix (16 × the commutator). -/
theorem loop_matrix (v : V3) : loop v =
    ⟨⟨9 * v.x.a + 12 * v.x.b + 6 * v.y.a - 12 * v.y.b + 4 * v.z.a - 9 * v.z.b,
      4 * v.x.a + 9 * v.x.b - 4 * v.y.a + 6 * v.y.b - 3 * v.z.a + 4 * v.z.b⟩,
     ⟨-4 * v.x.a + 9 * v.x.b + 12 * v.y.a + 6 * v.y.b - 3 * v.z.a + 12 * v.z.b,
      3 * v.x.a - 4 * v.x.b + 2 * v.y.a + 12 * v.y.b + 4 * v.z.a - 3 * v.z.b⟩,
     ⟨-6 * v.x.a + 12 * v.x.b - 4 * v.y.a + 12 * v.z.a + 6 * v.z.b,
      4 * v.x.a - 6 * v.x.b - 4 * v.y.b + 2 * v.z.a + 12 * v.z.b⟩⟩ := by
  simp only [loop, rz2, ry2, rz2back, ry2back, zadd, zneg, zroot, zscale, V3.mk.injEq,
    Z3.mk.injEq]
  omega

def ex : V3 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
def ey : V3 := ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩
def ez : V3 := ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩⟩

/-- 2. Sixteen times the trace is 33 + 8√3, so the loop is a genuine turn (not 48). -/
theorem loop_trace :
    zadd (zadd (loop ex).x (loop ey).y) (loop ez).z = ⟨33, 8⟩ := by decide

theorem loop_is_not_nothing : loop ex ≠ ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ := by decide

/-! ## 3. The residue never cancels -/

def loops : Nat → V3 → V3
  | 0, v => v
  | n + 1, v => loop (loops n v)

def pow16 : Nat → Int
  | 0 => 1
  | n + 1 => 16 * pow16 n

def vscale (k : Int) (v : V3) : V3 := ⟨zscale k v.x, zscale k v.y, zscale k v.z⟩

/-- The invariant: `v.x.a + v.z.b` is odd. -/
abbrev OddR (v : V3) : Prop := (v.x.a + v.z.b) % 2 = 1

theorem loop_keeps (v : V3) (h : OddR v) : OddR (loop v) := by
  rw [loop_matrix]
  unfold OddR at *
  simp only
  omega

theorem loop_marks_x (v : V3) (h : OddR v) : (loop v).x.a % 2 = 1 := by
  rw [loop_matrix]
  unfold OddR at h
  simp only
  omega

theorem loops_keep (v : V3) (h : OddR v) : ∀ n, OddR (loops n v) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact loop_keeps _ ih

theorem pow16_even (n : Nat) : pow16 (n + 1) % 2 = 0 := by
  show (16 * pow16 n) % 2 = 0
  omega

theorem pow16_pos : ∀ n, 0 < pow16 n
  | 0 => by decide
  | n + 1 => by
    show 0 < 16 * pow16 n
    have := pow16_pos n
    omega

theorem pow16_add (m j : Nat) : pow16 (m + j) = pow16 m * pow16 j := by
  induction m with
  | zero => simp [pow16]
  | succ m ih =>
    rw [Nat.succ_add]
    show 16 * pow16 (m + j) = 16 * pow16 m * pow16 j
    rw [ih, Int.mul_assoc]

theorem loops_add (i : Nat) (w : V3) : ∀ j, loops (i + j) w = loops j (loops i w)
  | 0 => rfl
  | j + 1 => by
    show loop (loops (i + j) w) = loop (loops j (loops i w))
    rw [loops_add i w j]

/-- 3a. Going round the loop never brings the x-axis point back. -/
theorem residue_never_cancels (n : Nat) (hn : 0 < n) : loops n ex ≠ vscale (pow16 n) ex := by
  intro hr
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hodd := loop_marks_x _ (loops_keep ex (by decide) k)
  have hxa := congrArg (fun w => w.x.a) hr
  simp only [vscale, zscale] at hxa
  change (loops (k + 1) ex).x.a % 2 = 1 at hodd
  rw [hxa] at hodd
  have he := pow16_even k
  rw [Int.mul_emod, he] at hodd
  simp at hodd

/-- 3b. Nor does it ever revisit an earlier position. -/
theorem residue_never_revisits (m n : Nat) (hmn : m < n) :
    vscale (pow16 n) (loops m ex) ≠ vscale (pow16 m) (loops n ex) := by
  intro hs
  obtain ⟨j, rfl⟩ : ∃ j, n = m + (j + 1) := ⟨n - m - 1, by omega⟩
  have hxa := congrArg (fun w => w.x.a) hs
  simp only [vscale, zscale] at hxa
  rw [pow16_add, Int.mul_assoc] at hxa
  have hp : pow16 m ≠ 0 := Int.ne_of_gt (pow16_pos m)
  have ha := Int.eq_of_mul_eq_mul_left hp hxa
  have hodd := loop_marks_x _ (loops_keep (loops m ex) (loops_keep ex (by decide) m) j)
  change (loops (j + 1) (loops m ex)).x.a % 2 = 1 at hodd
  rw [loops_add] at ha
  rw [← ha] at hodd
  have he := pow16_even j
  rw [Int.mul_emod, he] at hodd
  simp at hodd

#print axioms loop_matrix
#print axioms loop_trace
#print axioms loop_is_not_nothing
#print axioms residue_never_cancels
#print axioms residue_never_revisits

end OrderResidue
