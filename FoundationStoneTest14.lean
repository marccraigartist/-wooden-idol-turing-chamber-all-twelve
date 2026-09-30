import Mathlib

/-!
# THE THREE-CLOCK HELIX — TEST 14: X, Y, Z AND THE WELD CADENCE

This test follows Marc's proposal to place one twelve-seat clock about each of the
three Cartesian axes and let one helix process pass through all three.

The model keeps two layers separate and then joins them.

CLOCK LAYER
* the x-clock lies in the yz-plane, the y-clock in the xz-plane, and the z-clock
  in the xy-plane;
* seat `0` is B12;
* one compound iteration performs X, then Y, then Z;
* each submove advances only its own clock by one seat, advances the common helix
  height by one, and appends its axis to the ordered history;
* the weld square is `{B1, B4, B7, B10}`.

SPATIAL LAYER
* the same compound iteration is the exact ordered 30° move
  `Rz(30°) · Ry(30°) · Rx(30°)`;
* multiplying by eight gives a matrix over ℤ[√3], so the first three iterations
  are checked without floating point arithmetic.

Lean confirms:
1. one iteration advances all clocks to B1, height to 3, and history to X-Y-Z;
2. two and three iterations reach B2 and B3, with heights 6 and 9;
3. all three clocks meet the weld square together exactly at B1, B4, B7 and B10
   during the first twelve-iteration cycle;
4. among iterations one, two and three, only the first is a weld event;
5. the fourth iteration is the next weld event, at B4;
6. after twelve iterations the three clock shadows are back at B12, while the
   helix height is 36 and the 36-move history remains;
7. the ordered XYZ and ZYX spatial composites already disagree after one iteration;
8. the aligned spatial seat point is not home after one, two or three XYZ iterations.

Honest scope:
* an "iteration" is explicitly the ordered route X then Y then Z; simultaneous
  clock advancement is its end-of-iteration shadow, not simultaneous 3D rotation;
* the three nonreturn results are finite exact checks, not a proof that the XYZ
  spatial orbit has infinite order;
* the axis/seat orientation is a mathematical model.  A frame check against any
  particular Dead Globe renderer remains separate;
* this is not a P-versus-NP or physical claim.
-/

namespace FoundationStoneTestFourteen

/-! ## Part 1 — three twelve-seat clocks and one retained helix -/

abbrev Seat := Fin 12

inductive Axis
  | X
  | Y
  | Z
deriving DecidableEq, Repr

@[ext] structure TripleClockState where
  xSeat : Seat
  ySeat : Seat
  zSeat : Seat
  height : Nat
  history : List Axis
deriving DecidableEq

def startClock : TripleClockState :=
  ⟨0, 0, 0, 0, []⟩

def axisStep : Axis → TripleClockState → TripleClockState
  | .X, s => ⟨s.xSeat + 1, s.ySeat, s.zSeat,
      s.height + 1, s.history ++ [.X]⟩
  | .Y, s => ⟨s.xSeat, s.ySeat + 1, s.zSeat,
      s.height + 1, s.history ++ [.Y]⟩
  | .Z, s => ⟨s.xSeat, s.ySeat, s.zSeat + 1,
      s.height + 1, s.history ++ [.Z]⟩

/-- One complete iteration: x-axis clock, then y-axis clock, then z-axis clock. -/
def iteration (s : TripleClockState) : TripleClockState :=
  axisStep .Z (axisStep .Y (axisStep .X s))

def runIterations : Nat → TripleClockState → TripleClockState
  | 0, s => s
  | n + 1, s => iteration (runIterations n s)

theorem iteration_summary (s : TripleClockState) :
    iteration s =
      ⟨s.xSeat + 1, s.ySeat + 1, s.zSeat + 1,
       s.height + 3, s.history ++ [.X, .Y, .Z]⟩ := by
  ext <;> simp [iteration, axisStep]

theorem run_height : ∀ n s,
    (runIterations n s).height = s.height + 3 * n := by
  intro n
  induction n with
  | zero => intro s; simp [runIterations]
  | succ n ih =>
      intro s
      rw [runIterations, iteration_summary]
      simp only
      rw [ih]
      omega

theorem run_history_length : ∀ n s,
    (runIterations n s).history.length = s.history.length + 3 * n := by
  intro n
  induction n with
  | zero => intro s; simp [runIterations]
  | succ n ih =>
      intro s
      rw [runIterations, iteration_summary]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [ih]
      omega

/-- The first three complete iteration states, including the full ordered route. -/
theorem first_three_clock_states :
    runIterations 1 startClock =
      ⟨1, 1, 1, 3, [.X, .Y, .Z]⟩ ∧
    runIterations 2 startClock =
      ⟨2, 2, 2, 6, [.X, .Y, .Z, .X, .Y, .Z]⟩ ∧
    runIterations 3 startClock =
      ⟨3, 3, 3, 9, [.X, .Y, .Z, .X, .Y, .Z, .X, .Y, .Z]⟩ := by
  decide

/-! ## Part 2 — the weld square on all three clocks -/

def WeldSeat (s : Seat) : Prop :=
  s = 1 ∨ s = 4 ∨ s = 7 ∨ s = 10

def TripleWeld (s : TripleClockState) : Prop :=
  WeldSeat s.xSeat ∧ WeldSeat s.ySeat ∧ WeldSeat s.zSeat

instance weldSeatDecidable (s : Seat) : Decidable (WeldSeat s) := by
  unfold WeldSeat
  infer_instance

instance tripleWeldDecidable (s : TripleClockState) : Decidable (TripleWeld s) := by
  unfold TripleWeld
  infer_instance

/-- During one twelve-iteration cycle, the three clocks enter the weld square
together exactly at B1, B4, B7 and B10. -/
theorem weld_cadence_first_cycle :
    ∀ n : Fin 12,
      TripleWeld (runIterations n.val startClock) ↔
        n = 1 ∨ n = 4 ∨ n = 7 ∨ n = 10 := by
  decide

/-- Of the requested first three iterations, only iteration one is a weld event. -/
theorem first_three_weld_pattern :
    TripleWeld (runIterations 1 startClock) ∧
    ¬ TripleWeld (runIterations 2 startClock) ∧
    ¬ TripleWeld (runIterations 3 startClock) := by
  decide

/-- The next weld event occurs at iteration four, when every clock shows B4. -/
theorem fourth_iteration_is_B4_weld :
    runIterations 4 startClock =
      ⟨4, 4, 4, 12,
       [.X, .Y, .Z, .X, .Y, .Z, .X, .Y, .Z, .X, .Y, .Z]⟩ ∧
    TripleWeld (runIterations 4 startClock) := by
  decide

/-- Twelve circular shadows close, but the retained helix has climbed 36 steps and
kept 36 ordered axis events. -/
theorem twelve_shadows_home_helix_open :
    (runIterations 12 startClock).xSeat = 0 ∧
    (runIterations 12 startClock).ySeat = 0 ∧
    (runIterations 12 startClock).zSeat = 0 ∧
    (runIterations 12 startClock).height = 36 ∧
    (runIterations 12 startClock).history.length = 36 ∧
    runIterations 12 startClock ≠ startClock := by
  decide

/-! ## Part 3 — exact ordered XYZ geometry at 30° -/

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

/-- `8 · (Rz(30°) · Ry(30°) · Rx(30°))`.

    [[ 6,  -√3,  5 ],
     [2√3,  7,  -√3],
     [-4,  2√3,  6 ]]
-/
def stepXYZ (v : V3) : V3 :=
  ⟨⟨6 * v.x.a - 3 * v.y.b + 5 * v.z.a,
     6 * v.x.b - v.y.a + 5 * v.z.b⟩,
   ⟨6 * v.x.b + 7 * v.y.a - 3 * v.z.b,
     2 * v.x.a + 7 * v.y.b - v.z.a⟩,
   ⟨-4 * v.x.a + 6 * v.y.b + 6 * v.z.a,
     -4 * v.x.b + 2 * v.y.a + 6 * v.z.b⟩⟩

/-- `8 · (Rx(30°) · Ry(30°) · Rz(30°))`, the reverse axis order. -/
def stepZYX (v : V3) : V3 :=
  ⟨⟨6 * v.x.a - 6 * v.y.b + 4 * v.z.a,
     6 * v.x.b - 2 * v.y.a + 4 * v.z.b⟩,
   ⟨9 * v.x.b + 5 * v.y.a - 6 * v.z.b,
     3 * v.x.a + 5 * v.y.b - 2 * v.z.a⟩,
   ⟨-v.x.a + 9 * v.y.b + 6 * v.z.a,
     -v.x.b + 3 * v.y.a + 6 * v.z.b⟩⟩

def alignedSeat : V3 :=
  ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

/-- Axis order is already visible after one compound iteration. -/
theorem xyz_order_matters : stepXYZ alignedSeat ≠ stepZYX alignedSeat := by
  decide

def spatialMoves : Nat → V3 → V3
  | 0, v => v
  | n + 1, v => stepXYZ (spatialMoves n v)

def pow8 : Nat → Int
  | 0 => 1
  | n + 1 => 8 * pow8 n

def scaleV (k : Int) (v : V3) : V3 :=
  ⟨⟨k * v.x.a, k * v.x.b⟩,
   ⟨k * v.y.a, k * v.y.b⟩,
   ⟨k * v.z.a, k * v.z.b⟩⟩

def SpatialReturn (n : Nat) (v : V3) : Prop :=
  spatialMoves n v = scaleV (pow8 n) v

instance spatialReturnDecidable (n : Nat) (v : V3) :
    Decidable (SpatialReturn n v) := by
  unfold SpatialReturn
  infer_instance

/-- Exact numerator coordinates of the aligned point after one, two and three
XYZ iterations.  The actual coordinates are divided by 8, 64 and 512. -/
theorem first_three_spatial_numerators :
    spatialMoves 1 alignedSeat =
      ⟨⟨6, 0⟩, ⟨0, 2⟩, ⟨-4, 0⟩⟩ ∧
    spatialMoves 2 alignedSeat =
      ⟨⟨10, 0⟩, ⟨0, 30⟩, ⟨-36, 0⟩⟩ ∧
    spatialMoves 3 alignedSeat =
      ⟨⟨-210, 0⟩, ⟨0, 266⟩, ⟨-76, 0⟩⟩ := by
  decide

/-- The aligned spatial point is not home after any of the first three compound
iterations. -/
theorem first_three_spatial_nonreturns :
    ¬ SpatialReturn 1 alignedSeat ∧
    ¬ SpatialReturn 2 alignedSeat ∧
    ¬ SpatialReturn 3 alignedSeat := by
  decide

/-! ## Part 4 — the clock and spatial layers joined -/

structure CombinedState where
  clock : TripleClockState
  point : V3
deriving DecidableEq

def combinedStart : CombinedState :=
  ⟨startClock, alignedSeat⟩

def combinedIteration (s : CombinedState) : CombinedState :=
  ⟨iteration s.clock, stepXYZ s.point⟩

def runCombined : Nat → CombinedState → CombinedState
  | 0, s => s
  | n + 1, s => combinedIteration (runCombined n s)

theorem combined_projects_to_both : ∀ n s,
    (runCombined n s).clock = runIterations n s.clock ∧
    (runCombined n s).point = spatialMoves n s.point := by
  intro n
  induction n with
  | zero => intro s; exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro s
      simp only [runCombined, combinedIteration, runIterations, spatialMoves]
      exact ⟨congrArg iteration (ih s).1,
        congrArg stepXYZ (ih s).2⟩

/-- The requested first three combined observations: a B1 triple weld followed by
B2 and B3 non-weld states, all with new spatial positions and retained helix rise. -/
theorem combined_first_three_certificate :
    TripleWeld (runCombined 1 combinedStart).clock ∧
    ¬ TripleWeld (runCombined 2 combinedStart).clock ∧
    ¬ TripleWeld (runCombined 3 combinedStart).clock ∧
    (runCombined 1 combinedStart).clock.height = 3 ∧
    (runCombined 2 combinedStart).clock.height = 6 ∧
    (runCombined 3 combinedStart).clock.height = 9 ∧
    (runCombined 1 combinedStart).point ≠ scaleV 8 alignedSeat ∧
    (runCombined 2 combinedStart).point ≠ scaleV 64 alignedSeat ∧
    (runCombined 3 combinedStart).point ≠ scaleV 512 alignedSeat := by
  decide

/-! ## Certificate -/

theorem three_clock_helix_certificate :
    (runIterations 1 startClock =
      ⟨1, 1, 1, 3, [.X, .Y, .Z]⟩) ∧
    (∀ n : Fin 12,
      TripleWeld (runIterations n.val startClock) ↔
        n = 1 ∨ n = 4 ∨ n = 7 ∨ n = 10) ∧
    (TripleWeld (runIterations 1 startClock) ∧
      ¬ TripleWeld (runIterations 2 startClock) ∧
      ¬ TripleWeld (runIterations 3 startClock)) ∧
    ((runIterations 12 startClock).xSeat = 0 ∧
      (runIterations 12 startClock).ySeat = 0 ∧
      (runIterations 12 startClock).zSeat = 0 ∧
      (runIterations 12 startClock).height = 36 ∧
      (runIterations 12 startClock).history.length = 36 ∧
      runIterations 12 startClock ≠ startClock) ∧
    stepXYZ alignedSeat ≠ stepZYX alignedSeat ∧
    (¬ SpatialReturn 1 alignedSeat ∧
      ¬ SpatialReturn 2 alignedSeat ∧
      ¬ SpatialReturn 3 alignedSeat) :=
  ⟨first_three_clock_states.1,
   weld_cadence_first_cycle,
   first_three_weld_pattern,
   twelve_shadows_home_helix_open,
   xyz_order_matters,
   first_three_spatial_nonreturns⟩

#print axioms iteration_summary
#print axioms run_height
#print axioms run_history_length
#print axioms first_three_clock_states
#print axioms weld_cadence_first_cycle
#print axioms first_three_weld_pattern
#print axioms fourth_iteration_is_B4_weld
#print axioms twelve_shadows_home_helix_open
#print axioms xyz_order_matters
#print axioms first_three_spatial_numerators
#print axioms first_three_spatial_nonreturns
#print axioms combined_projects_to_both
#print axioms combined_first_three_certificate
#print axioms three_clock_helix_certificate

end FoundationStoneTestFourteen
