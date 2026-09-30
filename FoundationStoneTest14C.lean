/-!
# THE FOUNDATION STONE — TEST 14C: THE RELAY'S HANDEDNESS

Runs in the Lean live editor with no imports (core Lean only). Uses Test 14's own exact
matrices: `stepXYZ` = 8·Rz(30°)·Ry(30°)·Rx(30°) (X first) and `stepZYX` =
8·Rx(30°)·Ry(30°)·Rz(30°) (Z first). Entries are a + b√3.

With TWO clocks, swapping the order only moved the axis: Ry·Rz and Rz·Ry turn by the same
angle. With THREE clocks the order changes how much the carrier turns.

Order of results:
1. The traces differ: 19/8 for X→Y→Z and 17/8 for Z→Y→X. A rotation's trace is
   1 + 2·cos(angle), so the two relays turn by different amounts:
   cos = 11/16 (about 46.57°) and cos = 9/16 (about 55.77°).
   (A computer check of all six orders: the three cyclic relays X→Y→Z, Y→Z→X, Z→X→Y
   all turn 46.57°; the three reversed ones all turn 55.77°. Only the direction round the
   cycle matters, not where it starts.)
2. The hidden axes are exact: X→Y→Z turns about (1, √3, 1), leaning towards the middle
   clock Y; Z→Y→X turns about (√3, 1, √3), leaning away from it.
3. Both relays are dead globes: the x-axis seat point never returns under either.
   (Both cosines are rational and outside Niven's list {0, ±1/2, ±1}.)
-/
namespace RelayHandedness

structure Z3 where
  a : Int
  b : Int
deriving DecidableEq

structure V3 where
  x : Z3
  y : Z3
  z : Z3
deriving DecidableEq

def Z3.add (p q : Z3) : Z3 := ⟨p.a + q.a, p.b + q.b⟩

def stepXYZ (v : V3) : V3 :=
  ⟨⟨6 * v.x.a - 3 * v.y.b + 5 * v.z.a, 6 * v.x.b - v.y.a + 5 * v.z.b⟩,
   ⟨6 * v.x.b + 7 * v.y.a - 3 * v.z.b, 2 * v.x.a + 7 * v.y.b - v.z.a⟩,
   ⟨-4 * v.x.a + 6 * v.y.b + 6 * v.z.a, -4 * v.x.b + 2 * v.y.a + 6 * v.z.b⟩⟩

def stepZYX (v : V3) : V3 :=
  ⟨⟨6 * v.x.a - 6 * v.y.b + 4 * v.z.a, 6 * v.x.b - 2 * v.y.a + 4 * v.z.b⟩,
   ⟨9 * v.x.b + 5 * v.y.a - 6 * v.z.b, 3 * v.x.a + 5 * v.y.b - 2 * v.z.a⟩,
   ⟨-v.x.a + 9 * v.y.b + 6 * v.z.a, -v.x.b + 3 * v.y.a + 6 * v.z.b⟩⟩

def ex : V3 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
def ey : V3 := ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩
def ez : V3 := ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩⟩

/-- Eight times the trace, read off the three axis points. -/
def trace8 (f : V3 → V3) : Z3 := Z3.add (Z3.add (f ex).x (f ey).y) (f ez).z

/-- 1. The two relays have different traces, so they turn by different angles. -/
theorem the_relays_turn_by_different_amounts :
    trace8 stepXYZ = ⟨19, 0⟩ ∧ trace8 stepZYX = ⟨17, 0⟩ := by decide

def scale (k : Int) (v : V3) : V3 :=
  ⟨⟨k * v.x.a, k * v.x.b⟩, ⟨k * v.y.a, k * v.y.b⟩, ⟨k * v.z.a, k * v.z.b⟩⟩

/-- 2a. X→Y→Z turns about (1, √3, 1). -/
theorem xyz_axis : stepXYZ ⟨⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩⟩ = scale 8 ⟨⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩⟩ := by
  decide

/-- 2b. Z→Y→X turns about (√3, 1, √3). -/
theorem zyx_axis : stepZYX ⟨⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩⟩ = scale 8 ⟨⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩⟩ := by
  decide

/-! ## 3. Z→Y→X is also a dead globe (Test 14X covers X→Y→Z) -/

def moves : Nat → V3 → V3
  | 0, v => v
  | n + 1, v => stepZYX (moves n v)

def pow8 : Nat → Int
  | 0 => 1
  | n + 1 => 8 * pow8 n

/-- The invariant for the reversed relay: `v.x.a + v.y.b` is odd. -/
abbrev OddQ (v : V3) : Prop := (v.x.a + v.y.b) % 2 = 1

theorem step_keeps (v : V3) (h : OddQ v) : OddQ (stepZYX v) := by
  unfold OddQ stepZYX at *
  simp only
  omega

theorem step_marks_y (v : V3) (h : OddQ v) : (stepZYX v).y.b % 2 = 1 := by
  unfold OddQ stepZYX at *
  simp only
  omega

theorem moves_keep (v : V3) (h : OddQ v) : ∀ n, OddQ (moves n v) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact step_keeps _ ih

theorem pow8_even (n : Nat) : pow8 (n + 1) % 2 = 0 := by
  show (8 * pow8 n) % 2 = 0
  omega

/-- 3. Under the reversed relay the x-axis seat point never returns. -/
theorem zyx_x_seat_never_returns (n : Nat) (hn : 0 < n) :
    moves n ex ≠ scale (pow8 n) ex := by
  intro hr
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hodd := step_marks_y _ (moves_keep ex (by decide) k)
  have hyb := congrArg (fun w => w.y.b) hr
  simp only [scale] at hyb
  change (moves (k + 1) ex).y.b % 2 = 1 at hodd
  rw [hyb] at hodd
  have he := pow8_even k
  rw [Int.mul_emod, he] at hodd
  simp at hodd

#print axioms the_relays_turn_by_different_amounts
#print axioms xyz_axis
#print axioms zyx_axis
#print axioms zyx_x_seat_never_returns

end RelayHandedness
