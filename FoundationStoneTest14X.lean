/-!
# THE FOUNDATION STONE — TEST 14X: THE THREE-CLOCK GLOBE NEVER RETURNS

Runs in the Lean live editor with no imports (core Lean only). Closes the gap Test 14
names: its spatial non-return was checked only for three iterations.

The compound move is Test 14's own `stepXYZ` = 8 · Rz(30°)·Ry(30°)·Rx(30°), with
entries in ℤ[√3]. Everything is exact.

The key (the same idea as Bucket 3): reduce modulo 2. Write `p(v)` for the parity of
`v.y.b + v.z.a`.
1. One move keeps `p`.
2. After one move, the parity of the x-coordinate's whole-number part equals `p`.
3. So a point with `p` odd can never come back: after n ≥ 1 moves its x-coordinate
   has an odd whole part, while 8ⁿ times anything is even. It never revisits an earlier
   position either.
4. The z-axis seat point has `p` odd, so its orbit never closes, and no number of
   compound moves is the identity: the three-clock composite has infinite order.
5. Test 14's own starting point, the x-axis seat point, has `p` even, but one move sends
   it to twice a point with `p` odd. So it never returns either.

(Cross-check: the compound move turns by an angle whose cosine is exactly 11/16.)
-/
namespace ThreeClockGlobe

structure Z3 where
  a : Int
  b : Int
deriving DecidableEq

structure V3 where
  x : Z3
  y : Z3
  z : Z3
deriving DecidableEq

/-- Test 14's `stepXYZ`, copied: 8 · Rz(30°)·Ry(30°)·Rx(30°). -/
def stepXYZ (v : V3) : V3 :=
  ⟨⟨6 * v.x.a - 3 * v.y.b + 5 * v.z.a,
     6 * v.x.b - v.y.a + 5 * v.z.b⟩,
   ⟨6 * v.x.b + 7 * v.y.a - 3 * v.z.b,
     2 * v.x.a + 7 * v.y.b - v.z.a⟩,
   ⟨-4 * v.x.a + 6 * v.y.b + 6 * v.z.a,
     -4 * v.x.b + 2 * v.y.a + 6 * v.z.b⟩⟩

def moves : Nat → V3 → V3
  | 0, v => v
  | n + 1, v => stepXYZ (moves n v)

def pow8 : Nat → Int
  | 0 => 1
  | n + 1 => 8 * pow8 n

def scale (k : Int) (v : V3) : V3 :=
  ⟨⟨k * v.x.a, k * v.x.b⟩, ⟨k * v.y.a, k * v.y.b⟩, ⟨k * v.z.a, k * v.z.b⟩⟩

def ReturnsAfter (n : Nat) (v : V3) : Prop := moves n v = scale (pow8 n) v
def SamePlace (m n : Nat) (v : V3) : Prop :=
  scale (pow8 n) (moves m v) = scale (pow8 m) (moves n v)

/-- The invariant: `v.y.b + v.z.a` is odd. -/
abbrev OddP (v : V3) : Prop := (v.y.b + v.z.a) % 2 = 1

/-- 1. One move keeps the invariant. -/
theorem step_keeps (v : V3) (h : OddP v) : OddP (stepXYZ v) := by
  unfold OddP stepXYZ at *
  simp only
  omega

/-- 2. After one move, the x-coordinate's whole part is odd. -/
theorem step_marks_x (v : V3) (h : OddP v) : (stepXYZ v).x.a % 2 = 1 := by
  unfold OddP stepXYZ at *
  simp only
  omega

theorem moves_keep (v : V3) (h : OddP v) : ∀ n, OddP (moves n v) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact step_keeps _ ih

theorem x_odd_after (v : V3) (h : OddP v) (n : Nat) : (moves (n + 1) v).x.a % 2 = 1 :=
  step_marks_x _ (moves_keep v h n)

theorem pow8_even (n : Nat) : pow8 (n + 1) % 2 = 0 := by
  show (8 * pow8 n) % 2 = 0
  omega

theorem pow8_pos : ∀ n, 0 < pow8 n
  | 0 => by decide
  | n + 1 => by
    show 0 < 8 * pow8 n
    have := pow8_pos n
    omega

theorem pow8_add (m j : Nat) : pow8 (m + j) = pow8 m * pow8 j := by
  induction m with
  | zero => simp [pow8]
  | succ m ih =>
    rw [Nat.succ_add]
    show 8 * pow8 (m + j) = 8 * pow8 m * pow8 j
    rw [ih, Int.mul_assoc]

/-- 3a. A point with the invariant never returns. -/
theorem odd_never_returns (v : V3) (h : OddP v) (n : Nat) (hn : 0 < n) :
    ¬ ReturnsAfter n v := by
  intro hr
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hodd := x_odd_after v h k
  have hxa := congrArg (fun w => w.x.a) hr
  simp only [scale] at hxa
  rw [hxa] at hodd
  have he := pow8_even k
  rw [Int.mul_emod, he] at hodd
  simp at hodd

/-- Running i moves then j moves is running i + j moves. -/
theorem moves_add (i : Nat) (w : V3) : ∀ j, moves (i + j) w = moves j (moves i w)
  | 0 => rfl
  | j + 1 => by
    show stepXYZ (moves (i + j) w) = stepXYZ (moves j (moves i w))
    rw [moves_add i w j]

/-- 3b. A point with the invariant never revisits an earlier position. -/
theorem odd_never_revisits (v : V3) (h : OddP v) (m n : Nat) (hmn : m < n) :
    ¬ SamePlace m n v := by
  intro hs
  obtain ⟨j, rfl⟩ : ∃ j, n = m + (j + 1) := ⟨n - m - 1, by omega⟩
  have hxa := congrArg (fun w => w.x.a) hs
  simp only [scale] at hxa
  rw [pow8_add, Int.mul_assoc] at hxa
  have hp : pow8 m ≠ 0 := Int.ne_of_gt (pow8_pos m)
  have ha := Int.eq_of_mul_eq_mul_left hp hxa
  have hodd := x_odd_after (moves m v) (moves_keep v h m) j
  rw [moves_add] at ha
  rw [← ha] at hodd
  have he := pow8_even j
  rw [Int.mul_emod, he] at hodd
  simp at hodd

/-- The z-axis seat point. -/
def zSeat : V3 := ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩⟩

/-- 4a. The z-axis seat point never returns and never revisits. -/
theorem z_seat_never_returns (n : Nat) (hn : 0 < n) : ¬ ReturnsAfter n zSeat :=
  odd_never_returns zSeat (by decide) n hn

theorem z_seat_never_revisits (m n : Nat) (hmn : m < n) : ¬ SamePlace m n zSeat :=
  odd_never_revisits zSeat (by decide) m n hmn

/-- 4b. So no number of compound moves is the identity: infinite order. -/
theorem three_clock_move_has_infinite_order (n : Nat) (hn : 0 < n) :
    ¬ ∀ v : V3, ReturnsAfter n v :=
  fun hall => z_seat_never_returns n hn (hall zSeat)

/-- Test 14's x-axis seat point. -/
def xSeat : V3 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

/-- Half of its first image: (3, √3, −2), which carries the invariant. -/
def halfFirst : V3 := ⟨⟨3, 0⟩, ⟨0, 1⟩, ⟨-2, 0⟩⟩

theorem x_seat_first_move : stepXYZ xSeat = scale 2 halfFirst := by decide

theorem moves_scale (k : Int) : ∀ n v, moves n (scale k v) = scale k (moves n v) := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
    intro v
    show stepXYZ (moves n (scale k v)) = scale k (stepXYZ (moves n v))
    rw [ih]
    unfold stepXYZ scale
    simp only [V3.mk.injEq, Z3.mk.injEq]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [Int.mul_add, Int.mul_sub] <;>
      simp only [Int.mul_left_comm k]

/-- 5. Test 14's own x-axis seat point never returns either. -/
theorem x_seat_never_returns (n : Nat) (hn : 0 < n) : ¬ ReturnsAfter n xSeat := by
  intro hr
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  cases k with
  | zero =>
    have h1 : moves (0 + 1) xSeat ≠ scale (pow8 (0 + 1)) xSeat := by decide
    exact h1 hr
  | succ k =>
    have hsplit : moves (k + 1 + 1) xSeat = moves (k + 1) (stepXYZ xSeat) := by
      rw [show k + 1 + 1 = 1 + (k + 1) from by omega, moves_add]
      rfl
    unfold ReturnsAfter at hr
    rw [hsplit, x_seat_first_move, moves_scale] at hr
    have hxa := congrArg (fun w => w.x.a) hr
    simp only [scale] at hxa
    have hodd := x_odd_after halfFirst (by decide) k
    have h8 : pow8 (k + 1 + 1) = 2 * (4 * pow8 (k + 1)) := by
      show 8 * pow8 (k + 1) = 2 * (4 * pow8 (k + 1)); omega
    rw [h8] at hxa
    have hx : xSeat.x.a = 1 := rfl
    rw [hx, Int.mul_one] at hxa
    have hcancel := Int.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) hxa
    rw [hcancel] at hodd
    omega

#print axioms step_keeps
#print axioms odd_never_returns
#print axioms odd_never_revisits
#print axioms z_seat_never_returns
#print axioms z_seat_never_revisits
#print axioms three_clock_move_has_infinite_order
#print axioms x_seat_never_returns

end ThreeClockGlobe
