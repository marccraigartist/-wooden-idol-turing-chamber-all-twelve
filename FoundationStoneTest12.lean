import Mathlib

/-!
# THE ANGLE SPECTRUM — TEST 12: WHEN DOES THE GLOBE REALLY RETURN?

Tests 10 and 11 separated finite clock arithmetic from retained helix state.  This
test now asks the corresponding three-dimensional question.  A clock with `N`
seats always closes after `N` one-seat turns, but the Dead Globe move is not one
turn: it is an ordered composite of equal turns about two different axes.

The file has four layers.

1. An algebraic angle model proves, without numerical trigonometry, that the two
   orders `Ry · Rz` and `Rz · Ry` commute when the sine parameter is zero and
   disagree whenever it is nonzero (over an integral domain).
2. Exact controls classify three special members of the spectrum:
   * 360°: identity;
   * 180° (`N = 2`): the component turns commute and the composite has order two;
   * 90° (`N = 4`): order matters, but the composite closes after three moves.
3. Exact ℤ[√3] arithmetic restores the 30° (`N = 12`) Dead Globe result: its
   aligned seat point never returns and never revisits an earlier position.
4. A retained height/history lift separates spatial closure from complete return.
   Thus even the finite 180° and 90° controls do not return as complete processes.

The outcome is deliberately two-sided.  The finite clock shadow closes for every
positive `N`; the associated two-axis spatial composite can close or fail to close;
and every positive retained lift fails to return regardless.  Prime/composite clock
arithmetic therefore does not by itself classify the three-dimensional motion.

Honest scope:
* The general `N` bridge is conditional on the exact sine value being nonzero.  It
  proves the algebraic mechanism, not a formal library theorem about `sin (2π/N)`.
* The infinite-order spatial result is certified here for the exact 30° model.  No
  claim is made that every `N ≥ 3` composite has infinite order.
* Retained height and history are explicit modelling choices.  The test establishes
  their consequences, not a physical law and not a P-versus-NP result.
-/

namespace FoundationStoneTestTwelve

/-! ## Part 1 — the clock shadow closes for every modulus -/

def iterF {X : Type} (f : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => f (iterF f n x)

abbrev Clock (N : Nat) := ZMod N

def clockTurn {N : Nat} (x : Clock N) : Clock N := x + 1

theorem iter_clockTurn {N : Nat} (x : Clock N) :
    ∀ n, iterF clockTurn n x = x + n := by
  intro n
  induction n with
  | zero => simp [iterF]
  | succ n ih =>
      simp only [iterF, clockTurn, ih, Nat.cast_add, Nat.cast_one]
      ring

/-- The visible one-seat clock returns after `N` moves for every positive `N`. -/
theorem every_clock_shadow_closes (N : Nat) (_hN : 0 < N) (x : Clock N) :
    iterF clockTurn N x = x := by
  rw [iter_clockTurn]
  simp

/-! ## Part 2 — an exact algebraic model of the two ordered rotations -/

@[ext] structure Vec3 (R : Type) where
  x : R
  y : R
  z : R
deriving DecidableEq

/-- Rotation about y, written using abstract cosine and sine parameters. -/
def ry {R : Type} [CommRing R] (c s : R) (v : Vec3 R) : Vec3 R :=
  ⟨c * v.x + s * v.z, v.y, -s * v.x + c * v.z⟩

/-- Rotation about z, with the same abstract angle parameters. -/
def rz {R : Type} [CommRing R] (c s : R) (v : Vec3 R) : Vec3 R :=
  ⟨c * v.x - s * v.y, s * v.x + c * v.y, v.z⟩

def yz {R : Type} [CommRing R] (c s : R) (v : Vec3 R) : Vec3 R :=
  ry c s (rz c s v)

def zy {R : Type} [CommRing R] (c s : R) (v : Vec3 R) : Vec3 R :=
  rz c s (ry c s v)

def xAxis {R : Type} [Zero R] [One R] : Vec3 R := ⟨1, 0, 0⟩
def zAxis {R : Type} [Zero R] [One R] : Vec3 R := ⟨0, 0, 1⟩

/-- If the sine parameter vanishes, the two component rotations commute. -/
theorem zero_sine_orders_agree {R : Type} [CommRing R] (c : R) :
    ∀ v, yz c 0 v = zy c 0 v := by
  intro v
  ext <;> simp [yz, zy, ry, rz]

/-- If the sine parameter is nonzero in an integral domain, order is observable.
The z-axis point is a universal witness: one order gives y = 0 and the other y = s². -/
theorem nonzero_sine_orders_differ {R : Type} [CommRing R] [IsDomain R]
    (c s : R) (hs : s ≠ 0) : yz c s zAxis ≠ zy c s zAxis := by
  intro h
  have hy := congrArg Vec3.y h
  simp only [yz, zy, ry, rz, zAxis, mul_zero, mul_one,
    zero_add, add_zero, sub_zero] at hy
  exact hs (mul_self_eq_zero.mp hy.symm)

/-- A precise real-angle bridge.  Supplying a proof that the sine of `2π/N` is
nonzero is enough to certify that the two orders differ. -/
noncomputable def theta (N : Nat) : ℝ := 2 * Real.pi / N

noncomputable def nYZ (N : Nat) : Vec3 ℝ → Vec3 ℝ :=
  yz (Real.cos (theta N)) (Real.sin (theta N))

noncomputable def nZY (N : Nat) : Vec3 ℝ → Vec3 ℝ :=
  zy (Real.cos (theta N)) (Real.sin (theta N))

theorem n_orders_differ_of_sine_nonzero (N : Nat)
    (hs : Real.sin (theta N) ≠ 0) : nYZ N zAxis ≠ nZY N zAxis :=
  nonzero_sine_orders_differ _ _ hs

/-! ## Part 3 — exact 360°, 180° and 90° controls -/

def step360 : Vec3 ℤ → Vec3 ℤ := yz 1 0
def step180 : Vec3 ℤ → Vec3 ℤ := yz (-1) 0
def step90 : Vec3 ℤ → Vec3 ℤ := yz 0 1
def step90Reverse : Vec3 ℤ → Vec3 ℤ := zy 0 1

theorem three_sixty_is_identity : ∀ v, step360 v = v := by
  intro v
  ext <;> simp [step360, yz, ry, rz]

theorem one_eighty_orders_agree :
    ∀ v : Vec3 ℤ, yz (-1) 0 v = zy (-1) 0 v :=
  zero_sine_orders_agree (-1)

theorem one_eighty_closes_after_two : ∀ v, step180 (step180 v) = v := by
  intro v
  ext <;> simp [step180, yz, ry, rz]

theorem ninety_orders_differ : step90 zAxis ≠ step90Reverse zAxis :=
  nonzero_sine_orders_differ (0 : ℤ) 1 (by norm_num)

theorem ninety_closes_after_three :
    ∀ v, step90 (step90 (step90 v)) = v := by
  intro v
  ext <;> simp [step90, yz, ry, rz]

/-! ## Part 4 — exact 30° Dead Globe arithmetic in ℤ[√3] -/

/-- The exact number `a + b√3`. -/
structure Z3 where
  a : Int
  b : Int
deriving DecidableEq

structure V3 where
  x : Z3
  y : Z3
  z : Z3
deriving DecidableEq

/-- `4 · (Ry(30°) · Rz(30°))`. -/
def step30 (v : V3) : V3 :=
  ⟨⟨3 * v.x.a - 3 * v.y.b + 2 * v.z.a,
     3 * v.x.b - v.y.a + 2 * v.z.b⟩,
   ⟨2 * v.x.a + 6 * v.y.b,
     2 * v.x.b + 2 * v.y.a⟩,
   ⟨-3 * v.x.b + v.y.a + 6 * v.z.b,
     -v.x.a + v.y.b + 2 * v.z.a⟩⟩

/-- `4 · (Rz(30°) · Ry(30°))`, retained to test order. -/
def step30Reverse (v : V3) : V3 :=
  ⟨⟨3 * v.x.a - 2 * v.y.a + 3 * v.z.b,
     3 * v.x.b - 2 * v.y.b + v.z.a⟩,
   ⟨3 * v.x.b + 6 * v.y.b + v.z.a,
     v.x.a + 2 * v.y.a + v.z.b⟩,
   ⟨-2 * v.x.a + 6 * v.z.b,
     -2 * v.x.b + 2 * v.z.a⟩⟩

def seat30 : V3 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

theorem thirty_orders_differ : step30 seat30 ≠ step30Reverse seat30 := by
  decide

def moves30 : Nat → V3 → V3
  | 0, v => v
  | n + 1, v => step30 (moves30 n v)

def pow4 : Nat → Int
  | 0 => 1
  | n + 1 => 4 * pow4 n

def scale30 (k : Int) (v : V3) : V3 :=
  ⟨⟨k * v.x.a, k * v.x.b⟩,
   ⟨k * v.y.a, k * v.y.b⟩,
   ⟨k * v.z.a, k * v.z.b⟩⟩

def Returns30 (n : Nat) (v : V3) : Prop :=
  moves30 n v = scale30 (pow4 n) v

def SamePlace30 (m n : Nat) (v : V3) : Prop :=
  scale30 (pow4 n) (moves30 m v) = scale30 (pow4 m) (moves30 n v)

abbrev OddPair (v : V3) : Prop :=
  (v.x.a + v.x.b + v.y.a + v.y.b) % 2 = 1

theorem step30_keeps_odd (v : V3) (h : OddPair v) : OddPair (step30 v) := by
  unfold OddPair step30 at *
  simp only
  omega

theorem step30_makes_first_odd (v : V3) (h : OddPair v) :
    ((step30 v).x.a + (step30 v).x.b) % 2 = 1 := by
  unfold OddPair step30 at *
  simp only
  omega

theorem moves30_keep_odd (v : V3) (h : OddPair v) :
    ∀ n, OddPair (moves30 n v) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact step30_keeps_odd _ ih

theorem first_odd_after30 (v : V3) (h : OddPair v) (n : Nat) :
    ((moves30 (n + 1) v).x.a + (moves30 (n + 1) v).x.b) % 2 = 1 :=
  step30_makes_first_odd _ (moves30_keep_odd v h n)

theorem pow4_even (n : Nat) : pow4 (n + 1) % 2 = 0 := by
  show (4 * pow4 n) % 2 = 0
  omega

theorem pow4_pos : ∀ n, 0 < pow4 n
  | 0 => by decide
  | n + 1 => by
    show 0 < 4 * pow4 n
    have := pow4_pos n
    omega

theorem pow4_add (m j : Nat) : pow4 (m + j) = pow4 m * pow4 j := by
  induction m with
  | zero => simp [pow4]
  | succ m ih =>
    rw [Nat.succ_add]
    show 4 * pow4 (m + j) = 4 * pow4 m * pow4 j
    rw [ih, Int.mul_assoc]

theorem odd_never_returns30 (v : V3) (h : OddPair v) (n : Nat) (hn : 0 < n) :
    ¬ Returns30 n v := by
  intro hr
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hodd := first_odd_after30 v h k
  have hxa := congrArg (fun w => w.x.a) hr
  have hxb := congrArg (fun w => w.x.b) hr
  simp only [scale30] at hxa hxb
  rw [hxa, hxb] at hodd
  have he := pow4_even k
  rw [← Int.mul_add, Int.mul_emod, he] at hodd
  simp at hodd

theorem odd_never_revisits30 (v : V3) (h : OddPair v)
    (m n : Nat) (hmn : m < n) : ¬ SamePlace30 m n v := by
  intro hs
  obtain ⟨j, rfl⟩ : ∃ j, n = m + (j + 1) := ⟨n - m - 1, by omega⟩
  have hxa := congrArg (fun w => w.x.a) hs
  have hxb := congrArg (fun w => w.x.b) hs
  simp only [scale30] at hxa hxb
  rw [pow4_add, Int.mul_assoc] at hxa hxb
  have hp : pow4 m ≠ 0 := Int.ne_of_gt (pow4_pos m)
  have ha := Int.eq_of_mul_eq_mul_left hp hxa
  have hb := Int.eq_of_mul_eq_mul_left hp hxb
  have hodd := first_odd_after30 v h (m + j)
  rw [show m + j + 1 = m + (j + 1) from by omega] at hodd
  rw [← ha, ← hb, ← Int.mul_add] at hodd
  have he := pow4_even j
  rw [Int.mul_emod, he] at hodd
  simp at hodd

theorem thirty_seat_never_returns (n : Nat) (hn : 0 < n) :
    ¬ Returns30 n seat30 :=
  odd_never_returns30 seat30 (by decide) n hn

theorem thirty_seat_never_revisits (m n : Nat) (hmn : m < n) :
    ¬ SamePlace30 m n seat30 :=
  odd_never_revisits30 seat30 (by decide) m n hmn

/-! ## Part 5 — spatial return versus complete return -/

inductive MoveTag
  | halfTurn
  | quarterTurn
  | thirtyForward
  | thirtyReverse
deriving DecidableEq

structure LiftedState (X : Type) where
  point : X
  height : Nat
  history : List MoveTag
deriving DecidableEq

def liftOnce {X : Type} (tag : MoveTag) (move : X → X)
    (s : LiftedState X) : LiftedState X :=
  ⟨move s.point, s.height + 1, tag :: s.history⟩

def runLift {X : Type} (tag : MoveTag) (move : X → X) :
    Nat → LiftedState X → LiftedState X
  | 0, s => s
  | n + 1, s => liftOnce tag move (runLift tag move n s)

theorem lifted_point {X : Type} (tag : MoveTag) (move : X → X) :
    ∀ n s, (runLift tag move n s).point = iterF move n s.point := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      simp only [runLift, liftOnce, iterF]
      exact congrArg move (ih s)

theorem lifted_height {X : Type} (tag : MoveTag) (move : X → X) :
    ∀ n s, (runLift tag move n s).height = s.height + n := by
  intro n
  induction n with
  | zero => intro s; simp [runLift]
  | succ n ih =>
      intro s
      simp only [runLift, liftOnce]
      rw [ih]
      omega

theorem positive_lift_never_returns {X : Type} (tag : MoveTag) (move : X → X)
    (n : Nat) (hn : 0 < n) (s : LiftedState X) :
    runLift tag move n s ≠ s := by
  intro h
  have hh := congrArg LiftedState.height h
  rw [lifted_height] at hh
  omega

theorem one_eighty_shadow_returns_but_lift_does_not (s : LiftedState (Vec3 ℤ)) :
    (runLift .halfTurn step180 2 s).point = s.point ∧
    runLift .halfTurn step180 2 s ≠ s := by
  constructor
  · rw [lifted_point]
    exact one_eighty_closes_after_two s.point
  · exact positive_lift_never_returns .halfTurn step180 2 (by decide) s

theorem ninety_shadow_returns_but_lift_does_not (s : LiftedState (Vec3 ℤ)) :
    (runLift .quarterTurn step90 3 s).point = s.point ∧
    runLift .quarterTurn step90 3 s ≠ s := by
  constructor
  · rw [lifted_point]
    exact ninety_closes_after_three s.point
  · exact positive_lift_never_returns .quarterTurn step90 3 (by decide) s

/-! ## Certificate -/

theorem angle_spectrum_certificate :
    (∀ N : Nat, 0 < N → ∀ x : Clock N, iterF clockTurn N x = x) ∧
    (∀ (R : Type) [CommRing R] (c : R), ∀ v, yz c 0 v = zy c 0 v) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R] (c s : R),
      s ≠ 0 → yz c s zAxis ≠ zy c s zAxis) ∧
    (∀ v : Vec3 ℤ, step180 (step180 v) = v) ∧
    (step90 zAxis ≠ step90Reverse zAxis) ∧
    (∀ v : Vec3 ℤ, step90 (step90 (step90 v)) = v) ∧
    (∀ n, 0 < n → ¬ Returns30 n seat30) ∧
    (∀ m n, m < n → ¬ SamePlace30 m n seat30) ∧
    (∀ s : LiftedState (Vec3 ℤ),
      (runLift .quarterTurn step90 3 s).point = s.point ∧
      runLift .quarterTurn step90 3 s ≠ s) :=
  ⟨every_clock_shadow_closes,
   fun _ _ c => zero_sine_orders_agree c,
   fun _ _ _ c s hs => nonzero_sine_orders_differ c s hs,
   one_eighty_closes_after_two,
   ninety_orders_differ,
   ninety_closes_after_three,
   thirty_seat_never_returns,
   thirty_seat_never_revisits,
   ninety_shadow_returns_but_lift_does_not⟩

#print axioms every_clock_shadow_closes
#print axioms zero_sine_orders_agree
#print axioms nonzero_sine_orders_differ
#print axioms n_orders_differ_of_sine_nonzero
#print axioms three_sixty_is_identity
#print axioms one_eighty_closes_after_two
#print axioms ninety_orders_differ
#print axioms ninety_closes_after_three
#print axioms thirty_orders_differ
#print axioms thirty_seat_never_returns
#print axioms thirty_seat_never_revisits
#print axioms lifted_point
#print axioms positive_lift_never_returns
#print axioms one_eighty_shadow_returns_but_lift_does_not
#print axioms ninety_shadow_returns_but_lift_does_not
#print axioms angle_spectrum_certificate

end FoundationStoneTestTwelve
