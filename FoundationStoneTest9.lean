import Mathlib

/-!
# THE CUT REMEMBERS — TEST 9: THE DEAD GLOBE LIFTED TO THE HELIX

This file welds the two asymmetries isolated in the previous tests.

* Dead Globe asymmetry: the exact 30° composites `Ry · Rz` and `Rz · Ry` are
  different ordered moves.
* Helix asymmetry: every move advances a height counter and lengthens the travelled
  segment beyond its circular shadow.

The lifted state retains three things:
1. the spatial point;
2. the helix height (how many levels have been climbed);
3. the ordered history (which move occurred).

Lean checks:
1. the two exact 30° orders disagree at the seat point;
2. projection of a lifted run is exactly the ordinary spatial run;
3. every positive lifted run changes height and therefore cannot return to the same
   full state;
4. the 90° control returns spatially after three moves but does not return as a lifted
   state;
5. projection is not injective: different journeys can have the same visible point;
6. nonzero rise contributes a strictly positive squared-length excess at every step,
   and this excess accumulates over every positive finite run.

Honest scope:
* `stepYZ` and `stepZY` are the exact numerator matrices for the Bucket 3 frame,
  scaled by four.  The frame check against `dead_globe.html` is still owed.
* Height and history are deliberately retained as state.  If they are forgotten, a
  spatial return is a return by definition; if retained, it is not.
* This is a finite dynamical/provenance theorem, not a P-versus-NP or undecidability
  result.
-/

namespace FoundationStoneTestNine

/-! ## Exact 30° Dead Globe arithmetic -/

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
def stepYZ (v : V3) : V3 :=
  ⟨⟨3 * v.x.a - 3 * v.y.b + 2 * v.z.a,
     3 * v.x.b - v.y.a + 2 * v.z.b⟩,
   ⟨2 * v.x.a + 6 * v.y.b,
     2 * v.x.b + 2 * v.y.a⟩,
   ⟨-3 * v.x.b + v.y.a + 6 * v.z.b,
     -v.x.a + v.y.b + 2 * v.z.a⟩⟩

/-- `4 · (Rz(30°) · Ry(30°))`. -/
def stepZY (v : V3) : V3 :=
  ⟨⟨3 * v.x.a - 2 * v.y.a + 3 * v.z.b,
     3 * v.x.b - 2 * v.y.b + v.z.a⟩,
   ⟨3 * v.x.b + 6 * v.y.b + v.z.a,
     v.x.a + 2 * v.y.a + v.z.b⟩,
   ⟨-2 * v.x.a + 6 * v.z.b,
     -2 * v.x.b + 2 * v.z.a⟩⟩

def seatPoint : V3 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

/-- The making is ordered: the two 30° composites are different at the aligned
seat point. -/
theorem thirty_degree_order_matters : stepYZ seatPoint ≠ stepZY seatPoint := by
  decide

/-- The 90° control from Bucket 3. -/
def step90 (v : V3) : V3 := ⟨v.z, v.x, v.y⟩

theorem ninety_shadow_closes_after_three :
    ∀ v : V3, step90 (step90 (step90 v)) = v :=
  fun _ => rfl

/-! ## The helix lift -/

inductive MoveTag
  | yz30
  | zy30
  | turn90
deriving DecidableEq

structure LiftedState (X : Type) where
  point : X
  height : Nat
  history : List MoveTag
deriving DecidableEq

/-- One lifted move: change the visible point, climb one level, and retain which move
was made. -/
def liftOnce {X : Type} (tag : MoveTag) (move : X → X)
    (s : LiftedState X) : LiftedState X :=
  ⟨move s.point, s.height + 1, tag :: s.history⟩

def iterF {X : Type} (f : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => f (iterF f n x)

def runLift {X : Type} (tag : MoveTag) (move : X → X) :
    Nat → LiftedState X → LiftedState X
  | 0, s => s
  | n + 1, s => liftOnce tag move (runLift tag move n s)

def forgetPoint {X : Type} (s : LiftedState X) : X := s.point

/-- Forgetting commutes exactly with running. -/
theorem projection_commutes_with_run {X : Type} (tag : MoveTag) (move : X → X) :
    ∀ n s, forgetPoint (runLift tag move n s) = iterF move n (forgetPoint s) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      simp only [runLift, liftOnce, forgetPoint, iterF]
      exact congrArg move (ih s)

/-- The helix level remembers exactly how many moves occurred. -/
theorem run_height {X : Type} (tag : MoveTag) (move : X → X) :
    ∀ n s, (runLift tag move n s).height = s.height + n := by
  intro n
  induction n with
  | zero => intro s; simp [runLift]
  | succ n ih =>
      intro s
      simp only [runLift, liftOnce]
      rw [ih]
      omega

/-- The ordered history is retained rather than reconstructed from the endpoint. -/
theorem run_history {X : Type} (tag : MoveTag) (move : X → X) :
    ∀ n s, (runLift tag move n s).history = List.replicate n tag ++ s.history := by
  intro n
  induction n with
  | zero => intro s; simp [runLift]
  | succ n ih =>
      intro s
      simp only [runLift, liftOnce, ih]
      simp [List.replicate_succ]

/-- No positive lifted run returns to the same full state, regardless of whether the
spatial shadow happens to close. -/
theorem positive_lift_never_returns {X : Type} (tag : MoveTag) (move : X → X)
    (n : Nat) (hn : 0 < n) (s : LiftedState X) : runLift tag move n s ≠ s := by
  intro hreturn
  have hh := congrArg LiftedState.height hreturn
  rw [run_height tag move n s] at hh
  omega

/-! ## Dead Globe consequences -/

def deadStart : LiftedState V3 := ⟨seatPoint, 0, []⟩

/-- The two ordered 30° moves differ as lifted acts as well as spatial maps. -/
theorem lifted_thirty_degree_orders_differ :
    liftOnce .yz30 stepYZ deadStart ≠ liftOnce .zy30 stepZY deadStart := by
  decide

theorem yz30_lift_never_returns (n : Nat) (hn : 0 < n) :
    runLift .yz30 stepYZ n deadStart ≠ deadStart :=
  positive_lift_never_returns .yz30 stepYZ n hn deadStart

theorem zy30_lift_never_returns (n : Nat) (hn : 0 < n) :
    runLift .zy30 stepZY n deadStart ≠ deadStart :=
  positive_lift_never_returns .zy30 stepZY n hn deadStart

/-- The decisive control: the 90° spatial shadow is home after three moves. -/
theorem ninety_lift_shadow_is_home (s : LiftedState V3) :
    forgetPoint (runLift .turn90 step90 3 s) = forgetPoint s := by
  change step90 (step90 (step90 s.point)) = s.point
  exact ninety_shadow_closes_after_three s.point

/-- But the lifted 90° state is not home: its height and history have advanced. -/
theorem ninety_lift_is_not_home (s : LiftedState V3) :
    runLift .turn90 step90 3 s ≠ s :=
  positive_lift_never_returns .turn90 step90 3 (by decide) s

/-- "Same place" and "same return" are formally different statements. -/
theorem ninety_same_shadow_not_same_return (s : LiftedState V3) :
    forgetPoint (runLift .turn90 step90 3 s) = forgetPoint s ∧
    runLift .turn90 step90 3 s ≠ s :=
  ⟨ninety_lift_shadow_is_home s, ninety_lift_is_not_home s⟩

/-- Projection manufactures apparent sameness by erasing height and history. -/
theorem projection_is_not_injective : ¬ Function.Injective (@forgetPoint V3) := by
  intro hinjective
  let low : LiftedState V3 := ⟨seatPoint, 0, []⟩
  let high : LiftedState V3 := ⟨seatPoint, 1, [.yz30]⟩
  have hs : forgetPoint low = forgetPoint high := rfl
  have hsame := hinjective hs
  have hh := congrArg LiftedState.height hsame
  simp [low, high] at hh

/-! ## The extra length -/

/-- Squared length of the circular shadow of one step. -/
def circleStepSq (horizontal : Nat) : Nat := horizontal * horizontal

/-- Squared length of the lifted helical step. -/
def helixStepSq (horizontal rise : Nat) : Nat :=
  horizontal * horizontal + rise * rise

theorem helix_squared_length_gap (horizontal rise : Nat) :
    helixStepSq horizontal rise = circleStepSq horizontal + rise * rise := rfl

theorem helix_step_has_extra_squared_length (horizontal rise : Nat)
    (hrise : 0 < rise) :
    circleStepSq horizontal < helixStepSq horizontal rise := by
  unfold circleStepSq helixStepSq
  have hriseSq : 0 < rise * rise := Nat.mul_pos hrise hrise
  omega

def accumulatedSq (steps stepSq : Nat) : Nat := steps * stepSq

theorem accumulated_helix_gap (steps horizontal rise : Nat) :
    accumulatedSq steps (helixStepSq horizontal rise) =
      accumulatedSq steps (circleStepSq horizontal) + steps * (rise * rise) := by
  simp [accumulatedSq, helixStepSq, circleStepSq, Nat.mul_add]

theorem positive_run_accumulates_extra_squared_length
    (steps horizontal rise : Nat) (hsteps : 0 < steps) (hrise : 0 < rise) :
    accumulatedSq steps (circleStepSq horizontal) <
      accumulatedSq steps (helixStepSq horizontal rise) := by
  rw [accumulated_helix_gap]
  have hriseSq : 0 < rise * rise := Nat.mul_pos hrise hrise
  have hextra : 0 < steps * (rise * rise) := Nat.mul_pos hsteps hriseSq
  omega

/-! ## Complete certificate -/

theorem foundation_stone_test_nine :
    stepYZ seatPoint ≠ stepZY seatPoint ∧
    (∀ (X : Type) (tag : MoveTag) (move : X → X) n s,
      forgetPoint (runLift tag move n s) = iterF move n (forgetPoint s)) ∧
    (∀ (X : Type) (tag : MoveTag) (move : X → X) n,
      0 < n → ∀ s, runLift tag move n s ≠ s) ∧
    (∀ s : LiftedState V3,
      forgetPoint (runLift .turn90 step90 3 s) = forgetPoint s ∧
      runLift .turn90 step90 3 s ≠ s) ∧
    (¬ Function.Injective (@forgetPoint V3)) ∧
    (∀ steps horizontal rise, 0 < steps → 0 < rise →
      accumulatedSq steps (circleStepSq horizontal) <
        accumulatedSq steps (helixStepSq horizontal rise)) :=
  ⟨thirty_degree_order_matters,
   (fun X tag move => projection_commutes_with_run (X := X) tag move),
   (fun X tag move n hn s =>
      positive_lift_never_returns (X := X) tag move n hn s),
   ninety_same_shadow_not_same_return,
   projection_is_not_injective,
   positive_run_accumulates_extra_squared_length⟩

#print axioms thirty_degree_order_matters
#print axioms projection_commutes_with_run
#print axioms run_height
#print axioms run_history
#print axioms positive_lift_never_returns
#print axioms lifted_thirty_degree_orders_differ
#print axioms yz30_lift_never_returns
#print axioms ninety_lift_shadow_is_home
#print axioms ninety_lift_is_not_home
#print axioms ninety_same_shadow_not_same_return
#print axioms projection_is_not_injective
#print axioms helix_step_has_extra_squared_length
#print axioms positive_run_accumulates_extra_squared_length
#print axioms foundation_stone_test_nine

end FoundationStoneTestNine
