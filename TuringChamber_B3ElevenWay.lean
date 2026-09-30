import TuringChamber_B124OneNativeSystem
import Mathlib

/-!
# THE TURING CHAMBER — B3 ELEVEN-WAY INTEGRATION
## A cyclic making chamber beside the unbounded native climber

This file extends the ten-way Chamber system with the exact K31 B3
predicate without weakening the already-earned constraints.

The obstruction is real: the existing native climber has a strict Nat level,
so no nonempty subset can be both forward invariant and backward stable under
that step. B3 therefore receives a second Chamber-native mode. In dynamic
mode the existing native climber advances. In making mode the lane is held
and the certified 12-seat clock quotient advances cyclically.

The B3 source is:
  making mode AND the fixed Chamber problem eventually halts.

It is forward invariant, backward stable via the previous clock seat, inhabited
by an explicit halting problem, and cannot be named by the internal language
of computably decidable predicates because doing so would decide the global
HelixHalts predicate.

The dynamic and making modes share one carrier and one total step.

No B5 claim is made.
No arithmetic-prime, zeta, or RH claim is made.
-/

namespace TuringChamberB3ElevenWay

set_option autoImplicit false

open FoundationStoneTest16AF
open FoundationStoneTest16BU
open TuringChamberForgetfulView
open TuringChamberB2NativeRecurrence
open TuringChamberB124OneSystem

def BackwardStable (S : System) (I : S.X → Prop) : Prop :=
  ∀ x, I x → ∃ y, I y ∧ S.step y = x

def canonicalB3 (S : System) : Prop :=
  ∃ I : S.X → Prop,
    MapInvariant S I ∧
    BackwardStable S I ∧
    (∃ body state, I state ∧
      S.recognises body state ∧ S.usableBy body state) ∧
    ¬ (∃ expression : S.Language, Denotes S expression I)

def everyStableSourceInternallyNamedControl (S : System) : Prop :=
  ∀ I : S.X → Prop,
    MapInvariant S I →
      ∃ expression : S.Language, Denotes S expression I

theorem internally_named_source_control_rejects_B3
    (S : System)
    (hnamed : everyStableSourceInternallyNamedControl S) :
    ¬ canonicalB3 S := by
  rintro ⟨I, hinvariant, _hbackward, _hrecognised, hunnamed⟩
  exact hunnamed (hnamed I hinvariant)

/-! ## 1. Expanded carrier -/

abbrev ExpandedState := Problem × (Bool × (LaneState × Seat))

def expandedProblem (s : ExpandedState) : Problem := s.1
def expandedMode (s : ExpandedState) : Bool := s.2.1
def expandedLane (s : ExpandedState) : LaneState := s.2.2.1
def expandedSeat (s : ExpandedState) : Seat := s.2.2.2

def dynamicState (q : Problem) (lane : LaneState) (seat : Seat) :
    ExpandedState :=
  (q, (false, (lane, seat)))

def makingState (q : Problem) (lane : LaneState) (seat : Seat) :
    ExpandedState :=
  (q, (true, (lane, seat)))

@[simp] theorem expandedProblem_dynamic
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedProblem (dynamicState q lane seat) = q := rfl

@[simp] theorem expandedProblem_making
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedProblem (makingState q lane seat) = q := rfl

@[simp] theorem expandedMode_dynamic
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedMode (dynamicState q lane seat) = false := rfl

@[simp] theorem expandedMode_making
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedMode (makingState q lane seat) = true := rfl

@[simp] theorem expandedLane_dynamic
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedLane (dynamicState q lane seat) = lane := rfl

@[simp] theorem expandedLane_making
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedLane (makingState q lane seat) = lane := rfl

@[simp] theorem expandedSeat_dynamic
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedSeat (dynamicState q lane seat) = seat := rfl

@[simp] theorem expandedSeat_making
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedSeat (makingState q lane seat) = seat := rfl

def expandedStep : ExpandedState → ExpandedState
  | (q, (false, (lane, seat))) =>
      dynamicState q (laneStep lane) seat
  | (q, (true, (lane, seat))) =>
      makingState q lane (clockStep seat)

@[simp] theorem expandedStep_dynamic
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedStep (dynamicState q lane seat) =
      dynamicState q (laneStep lane) seat := rfl

@[simp] theorem expandedStep_making
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedStep (makingState q lane seat) =
      makingState q lane (clockStep seat) := rfl

def expandedObserve : ExpandedState → Seat
  | (_, (false, (lane, _))) => laneObserve lane
  | (_, (true, (_, seat))) => seat

def expandedRelation : ExpandedState → ExpandedState → Prop
  | (qx, (false, (lx, sx))), (qy, (false, (ly, sy))) =>
      qx = qy ∧ sameLane lx ly ∧ sx = sy
  | (qx, (true, (lx, _))), (qy, (true, (ly, _))) =>
      qx = qy ∧ lx = ly
  | _, _ => False

def expandedBodyAt (s : ExpandedState) : Bool :=
  (expandedLane s).1

def expandedPhase : ExpandedState → CompletionPhase
  | (_, (false, (lane, _))) => episodePhase lane
  | (_, (true, _)) => .doing

def expandedMapId : ExpandedState → Nat
  | (_, (false, (lane, _))) => mapId124 lane
  | (_, (true, _)) => 0

def expandedRequired (_ : ExpandedState) : List Unit := [()]

def expandedPerformed : ExpandedState → List Unit
  | (_, (false, (lane, _))) => performed124 lane
  | (_, (true, _)) => [()]

def expandedHistory : ExpandedState → List Nat
  | (_, (false, (lane, _))) => history124 lane
  | (_, (true, _)) => []

def expandedEncounterId : ExpandedState → Nat
  | (_, (false, (lane, _))) => encounterId124 lane
  | (_, (true, _)) => 0

def expandedAvailableSeed (completed seed : ExpandedState) : Prop :=
  expandedMode completed = false ∧
    expandedPhase completed = .done ∧
    seed = expandedStep completed

def expandedLinkedTo (completed seed : ExpandedState) : Prop :=
  expandedProblem seed = expandedProblem completed ∧
    expandedMode seed = expandedMode completed ∧
    (expandedLane seed).1 = (expandedLane completed).1

def expandedContinuation (completed later : ExpandedState) : Prop :=
  expandedAvailableSeed completed later

def expandedRealised : ExpandedState → Prop
  | (_, (false, (lane, _))) => realised124 lane
  | (_, (true, (_, seat))) => clockStep seat ≠ seat

def expandedEncounterSite : ExpandedState → Nat
  | (_, (false, (lane, _))) => lane.2
  | (_, (true, (_, seat))) => seat.val

def expandedCoherent (s : ExpandedState) : Prop :=
  (expandedLane s).1 = false

def expandedTransport : ExpandedState → ExpandedState → ExpandedState
  | (qs, (false, (ls, ss))), (_, (false, (ld, _))) =>
      dynamicState qs (transport124 ls ld) ss
  | source, _ => source

def expandedOriginAt (s : ExpandedState) : ExpandedState :=
  (expandedProblem s,
    (expandedMode s,
      (((expandedLane s).1, 0), expandedSeat s)))

def expandedPossible (_ : ExpandedState) (_ : Bool) : Prop := True

def expandedRevealed (state : ExpandedState) (observation : Seat) : Prop :=
  expandedObserve state = observation

def expandedRefersToOutput : ExpandedState → ExpandedState → Prop
  | (q, (false, (lane, seat))), (q', (false, (lane', seat'))) =>
      q' = q ∧ lane' = laneStep lane ∧ seat' = seat
  | (q, (true, (lane, seat))), (q', (true, (lane', seat'))) =>
      q' = q ∧ lane' = lane ∧ seat' = clockStep seat
  | _, _ => False

def expandedRecognises (body : Bool) (state : ExpandedState) : Prop :=
  body = (expandedLane state).1

def expandedUsableBy (body : Bool) (state : ExpandedState) : Prop :=
  body = (expandedLane state).1

/-! ## 2. Clock facts: the making mode really has predecessors -/

theorem clockStep_back (s : Seat) :
    clockStep (back s) = s := by
  fin_cases s <;> decide

theorem back_clockStep (s : Seat) :
    back (clockStep s) = s := by
  fin_cases s <;> decide

theorem clockStep_no_fixed (s : Seat) :
    clockStep s ≠ s := by
  fin_cases s <;> decide

theorem clockStep_injective :
    Function.Injective clockStep := by
  intro x y h
  have hb := congrArg back h
  simpa [back_clockStep] using hb

def clockToZero (s : Seat) : Nat :=
  (12 - s.val) % 12

theorem clock_reaches_zero (s : Seat) :
    (clockStep^[clockToZero s]) s = (0 : Seat) := by
  fin_cases s <;> native_decide

/-! ## 3. Iteration in the two modes -/

theorem expanded_iterate_dynamic :
    ∀ n q lane seat,
      (expandedStep^[n]) (dynamicState q lane seat) =
        dynamicState q ((laneStep^[n]) lane) seat := by
  intro n
  induction n with
  | zero =>
      intro q lane seat
      rfl
  | succ n ih =>
      intro q lane seat
      rw [Function.iterate_succ_apply']
      rw [ih]
      simp [Function.iterate_succ_apply']

theorem expanded_iterate_making :
    ∀ n q lane seat,
      (expandedStep^[n]) (makingState q lane seat) =
        makingState q lane ((clockStep^[n]) seat) := by
  intro n
  induction n with
  | zero =>
      intro q lane seat
      rfl
  | succ n ih =>
      intro q lane seat
      rw [Function.iterate_succ_apply']
      rw [ih]
      simp [Function.iterate_succ_apply']

/-! ## 4. Internal language and one expanded System -/

structure ExpandedInternalExpr where
  pred : ExpandedState → Prop
  computable : ComputablePred pred

def expandedDen (e : ExpandedInternalExpr) (x : ExpandedState) : Prop :=
  e.pred x

theorem false_expanded_property_computable :
    ComputablePred (fun _ : ExpandedState => False) := by
  unfold ComputablePred
  refine ⟨inferInstance, ?_⟩
  simpa using
    (Computable.const false :
      Computable (fun _ : ExpandedState => false))

theorem true_expanded_property_computable :
    ComputablePred (fun _ : ExpandedState => True) := by
  unfold ComputablePred
  refine ⟨inferInstance, ?_⟩
  simpa using
    (Computable.const true :
      Computable (fun _ : ExpandedState => true))

theorem making_mode_property_computable :
    ComputablePred (fun x : ExpandedState => expandedMode x = true) := by
  rw [ComputablePred.computable_iff]
  refine ⟨expandedMode, ?_, ?_⟩
  · exact Computable.fst.comp Computable.snd
  · funext x
    apply propext
    simp [expandedMode]

def falseExpandedExpr : ExpandedInternalExpr where
  pred := fun _ => False
  computable := false_expanded_property_computable

def trueExpandedExpr : ExpandedInternalExpr where
  pred := fun _ => True
  computable := true_expanded_property_computable

def makingModeExpr : ExpandedInternalExpr where
  pred := fun x => expandedMode x = true
  computable := making_mode_property_computable

noncomputable section

local instance expandedStateDecidableEq : DecidableEq ExpandedState :=
  Classical.decEq ExpandedState

@[reducible] noncomputable def expandedSystemWithLanguage
    (L : Type)
    (denotation : L → ExpandedState → Prop)
    (falseExpr trueExpr : L) : System where
  X := ExpandedState
  K := Bool
  Site := Nat
  Origin := ExpandedState
  Language := L
  Possibility := Bool
  Observation := Seat
  step := expandedStep
  bodyAt := expandedBodyAt
  phase := expandedPhase
  mapId := expandedMapId
  requiredSteps := expandedRequired
  performedSteps := expandedPerformed
  history := expandedHistory
  encounterId := expandedEncounterId
  availableSeed := expandedAvailableSeed
  linkedTo := expandedLinkedTo
  continuation := expandedContinuation
  realised := expandedRealised
  encounterSite := expandedEncounterSite
  coherent := expandedCoherent
  transport := expandedTransport
  originAt := expandedOriginAt
  interp := TuringChamberB1NativeGlobalReachability.finiteInterp
  finuniversal :=
    TuringChamberB1NativeGlobalReachability.finiteInterp_finiteUniversal
  observe := expandedObserve
  den := denotation
  Prf := fun e => ∀ x, denotation e x
  falsum := falseExpr
  con := trueExpr
  refersToOutput := expandedRefersToOutput
  outputStep := expandedStep
  possible := expandedPossible
  revealed := expandedRevealed
  relation := expandedRelation
  recognises := expandedRecognises
  usableBy := expandedUsableBy

@[reducible] noncomputable def expandedSystem : System :=
  expandedSystemWithLanguage
    ExpandedInternalExpr expandedDen falseExpandedExpr trueExpandedExpr

def expandedStart : ExpandedState :=
  dynamicState climbProblem start124 (0 : Seat)

/-! ## 5. B1 and B2 survive in dynamic mode -/

def expandedRank (s : ExpandedState) : Nat :=
  if expandedMode s then 0 else (expandedLane s).2

def expandedEscapeLevel
    (s : Finset (ExpandedState × ExpandedState)) : Nat :=
  s.sup (fun pair => expandedRank pair.2) + 1

theorem expanded_start_reaches_level (k : Nat) :
    Reachable expandedSystem expandedStart
      (dynamicState climbProblem (false, k) (0 : Seat)) := by
  refine ⟨k, ?_⟩
  change
    (expandedStep^[k]) (dynamicState climbProblem start124 (0 : Seat)) =
      dynamicState climbProblem (false, k) (0 : Seat)
  rw [expanded_iterate_dynamic, lane_iterate]
  simp [start124]

theorem expanded_start_escape_not_mem
    (s : Finset (ExpandedState × ExpandedState)) :
    (expandedStart,
      dynamicState climbProblem (false, expandedEscapeLevel s) (0 : Seat)) ∉ s := by
  intro hmem
  have hraw :=
    Finset.le_sup
      (s := s)
      (f := fun pair : ExpandedState × ExpandedState =>
        expandedRank pair.2)
      hmem
  have hle :
      expandedEscapeLevel s ≤
        s.sup (fun pair => expandedRank pair.2) := by
    simpa [expandedRank, expandedMode, expandedLane, dynamicState] using hraw
  unfold expandedEscapeLevel at hle
  omega

theorem expanded_satisfies_B1 :
    canonicalB1 expandedSystem := by
  rintro ⟨table, htable⟩
  change
    (∀ x y : ExpandedState,
      TuringChamberB1NativeGlobalReachability.finiteInterp table x y = true ↔
        ∃ n : Nat, (expandedStep^[n]) x = y) at htable
  let s : Finset (ExpandedState × ExpandedState) :=
    TuringChamberB1NativeGlobalReachability.decodedRelation table
  let y : ExpandedState :=
    dynamicState climbProblem (false, expandedEscapeLevel s) (0 : Seat)
  have hyreach : ∃ n : Nat, (expandedStep^[n]) expandedStart = y := by
    change Reachable expandedSystem expandedStart y
    simpa [y] using
      expanded_start_reaches_level (expandedEscapeLevel s)
  have htrue :
      TuringChamberB1NativeGlobalReachability.finiteInterp
        table expandedStart y = true :=
    (htable expandedStart y).2 hyreach
  have hmem : (expandedStart, y) ∈ s := by
    simpa [TuringChamberB1NativeGlobalReachability.finiteInterp, s] using htrue
  exact (expanded_start_escape_not_mem s) (by simpa [y] using hmem)

theorem expanded_orbit_injective :
    Function.Injective
      (fun n : Nat => (expandedStep^[n]) expandedStart) := by
  intro i j h
  have hlane := congrArg expandedLane h
  have hlane' :
      (laneStep^[i]) start124 = (laneStep^[j]) start124 := by
    simpa [expandedStart, expanded_iterate_dynamic] using hlane
  exact start124_orbit_injective hlane'

theorem expanded_observation_nonconstant :
    ∃ i j : Nat,
      expandedObserve ((expandedStep^[i]) expandedStart) ≠
        expandedObserve ((expandedStep^[j]) expandedStart) := by
  refine ⟨0, 1, ?_⟩
  native_decide

theorem expanded_observation_recurs_arbitrarily_late :
    ∀ cutoff : Nat, ∃ later : Nat,
      cutoff < later ∧
        expandedObserve ((expandedStep^[later]) expandedStart) =
          expandedObserve expandedStart := by
  intro cutoff
  obtain ⟨later, hlater, hobs⟩ :=
    start124_observation_recurs_arbitrarily_late cutoff
  refine ⟨later, hlater, ?_⟩
  change
    expandedObserve
        ((expandedStep^[later])
          (dynamicState climbProblem start124 (0 : Seat))) =
      expandedObserve (dynamicState climbProblem start124 (0 : Seat))
  rw [expanded_iterate_dynamic]
  change laneObserve ((laneStep^[later]) start124) = laneObserve start124
  exact hobs

theorem expanded_satisfies_B2 :
    canonicalB2 expandedSystem :=
  ⟨expandedStart,
    expanded_orbit_injective,
    expanded_observation_nonconstant,
    expanded_observation_recurs_arbitrarily_late⟩

/-! ## 6. B4: one independently structural relation for both modes -/

theorem expanded_corecurrent_implies_relation
    {x y : ExpandedState}
    (h : CoRecurrent expandedSystem x y) :
    expandedRelation x y := by
  rcases x with ⟨qx, mx, lx, sx⟩
  rcases y with ⟨qy, my, ly, sy⟩
  cases mx <;> cases my
  · change ∃ n m : Nat,
      (expandedStep^[n]) (dynamicState qx lx sx) =
        (expandedStep^[m]) (dynamicState qy ly sy) at h
    rcases h with ⟨n, m, hmeet⟩
    rw [expanded_iterate_dynamic, expanded_iterate_dynamic] at hmeet
    have hq : qx = qy := by
      have hp := congrArg (fun z : ExpandedState => z.1) hmeet
      simpa [dynamicState] using hp
    have hs : sx = sy := by
      have hp := congrArg (fun z : ExpandedState => z.2.2.2) hmeet
      simpa [dynamicState] using hp
    have hlmeet :
        (laneStep^[n]) lx = (laneStep^[m]) ly := by
      have hp := congrArg (fun z : ExpandedState => z.2.2.1) hmeet
      simpa [dynamicState] using hp
    have hl : sameLane lx ly :=
      co_recurrent_implies_sameLane ⟨n, m, hlmeet⟩
    exact ⟨hq, hl, hs⟩
  · change ∃ n m : Nat,
      (expandedStep^[n]) (dynamicState qx lx sx) =
        (expandedStep^[m]) (makingState qy ly sy) at h
    rcases h with ⟨n, m, hmeet⟩
    rw [expanded_iterate_dynamic, expanded_iterate_making] at hmeet
    have hm := congrArg expandedMode hmeet
    cases hm
  · change ∃ n m : Nat,
      (expandedStep^[n]) (makingState qx lx sx) =
        (expandedStep^[m]) (dynamicState qy ly sy) at h
    rcases h with ⟨n, m, hmeet⟩
    rw [expanded_iterate_making, expanded_iterate_dynamic] at hmeet
    have hm := congrArg expandedMode hmeet
    cases hm
  · change ∃ n m : Nat,
      (expandedStep^[n]) (makingState qx lx sx) =
        (expandedStep^[m]) (makingState qy ly sy) at h
    rcases h with ⟨n, m, hmeet⟩
    rw [expanded_iterate_making, expanded_iterate_making] at hmeet
    have hq : qx = qy := by
      have hp := congrArg (fun z : ExpandedState => z.1) hmeet
      simpa [makingState] using hp
    have hl : lx = ly := by
      have hp := congrArg (fun z : ExpandedState => z.2.2.1) hmeet
      simpa [makingState] using hp
    exact ⟨hq, hl⟩

theorem expanded_relation_implies_corecurrent
    {x y : ExpandedState}
    (h : expandedRelation x y) :
    CoRecurrent expandedSystem x y := by
  rcases x with ⟨qx, mx, lx, sx⟩
  rcases y with ⟨qy, my, ly, sy⟩
  cases mx <;> cases my
  · rcases h with ⟨rfl, hlane, rfl⟩
    rcases sameLane_implies_co_recurrent hlane with ⟨n, m, hmeet⟩
    refine ⟨n, m, ?_⟩
    change
      (expandedStep^[n]) (dynamicState qx lx sx) =
        (expandedStep^[m]) (dynamicState qx ly sx)
    change (laneStep^[n]) lx = (laneStep^[m]) ly at hmeet
    rw [expanded_iterate_dynamic, expanded_iterate_dynamic]
    simp [hmeet]
  · exact False.elim h
  · exact False.elim h
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨clockToZero sx, clockToZero sy, ?_⟩
    change
      (expandedStep^[clockToZero sx]) (makingState qx lx sx) =
        (expandedStep^[clockToZero sy]) (makingState qx lx sy)
    rw [expanded_iterate_making, expanded_iterate_making,
      clock_reaches_zero, clock_reaches_zero]

theorem expanded_satisfies_B4 :
    canonicalB4 expandedSystem := by
  intro x y
  exact ⟨expanded_relation_implies_corecurrent,
    expanded_corecurrent_implies_relation⟩

/-! ## 7. B6 and B9 survive both modes -/

theorem expandedStep_changes_state (s : ExpandedState) :
    expandedStep s ≠ s := by
  rcases s with ⟨q, mode, lane, seat⟩
  cases mode
  · intro h
    have hl := congrArg (fun z : ExpandedState => z.2.2.1) h
    have hl' : laneStep lane = lane := by
      simpa [expandedStep, dynamicState] using hl
    exact laneStep_changes_state lane hl'
  · intro h
    have hs := congrArg (fun z : ExpandedState => z.2.2.2) h
    have hs' : clockStep seat = seat := by
      simpa [expandedStep, makingState] using hs
    exact clockStep_no_fixed seat hs'

theorem expanded_body_identity_preserved (s : ExpandedState) :
    expandedSystem.bodyAt (expandedSystem.step s) =
      expandedSystem.bodyAt s := by
  rcases s with ⟨q, mode, lane, seat⟩
  cases mode
  · change (laneStep lane).1 = lane.1
    rfl
  · rfl

theorem expanded_relation_step_invariant (x y : ExpandedState) :
    expandedSystem.relation (expandedSystem.step x) (expandedSystem.step y) ↔
      expandedSystem.relation x y := by
  rcases x with ⟨qx, mx, lx, sx⟩
  rcases y with ⟨qy, my, ly, sy⟩
  cases mx <;> cases my
  · change
      (qx = qy ∧ (laneStep lx).1 = (laneStep ly).1 ∧ sx = sy) ↔
        (qx = qy ∧ lx.1 = ly.1 ∧ sx = sy)
    simp [laneStep]
  · change False ↔ False
    rfl
  · change False ↔ False
    rfl
  · change (qx = qy ∧ lx = ly) ↔ (qx = qy ∧ lx = ly)
    rfl

theorem expanded_satisfies_B9 :
    canonicalB9 expandedSystem := by
  constructor
  · intro s
    exact ⟨expandedStep_changes_state s,
      expanded_body_identity_preserved s⟩
  · exact expanded_relation_step_invariant

theorem expanded_doing_requirements_covered
    (s : ExpandedState)
    (hdoing : expandedSystem.phase s = .doing) :
    EpisodeRequirementsCovered expandedSystem s := by
  rcases s with ⟨q, mode, lane, seat⟩
  cases mode
  · change episodePhase lane = .doing at hdoing
    change
      [()] ≠ [] ∧ [()].Nodup ∧
        ∀ requirement,
          requirement ∈ [()] →
            requirement ∈
              (if episodePhase lane = .doing then [()] else [])
    simp [hdoing]
  · simp [EpisodeRequirementsCovered, expandedSystem,
      expandedRequired, expandedPerformed]

theorem expanded_dynamic_retains_history
    (q : Problem) (lane : LaneState) (seat : Seat) :
    RetainsHistory expandedSystem
      (dynamicState q lane seat)
      (expandedStep (dynamicState q lane seat)) := by
  intro origin horigin
  change origin ∈ history124 lane at horigin
  change origin ∈ history124 (laneStep lane)
  exact laneStep_retains_history lane origin horigin

theorem expanded_dynamic_encounter_enters_history
    (q : Problem) (lane : LaneState) (seat : Seat) :
    expandedSystem.encounterId (dynamicState q lane seat) ∈
      expandedSystem.history
        (expandedSystem.step (dynamicState q lane seat)) := by
  exact encounter_enters_next_history lane

theorem expanded_start_earned_completion :
    EarnedCompletionTransition
      expandedSystem expandedStart (expandedStep expandedStart) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact expandedStep_changes_state expandedStart h.symm
  · change episodePhase start124 = .doing
    simp [episodePhase, start124]
  · change episodePhase (laneStep start124) = .done
    simp [episodePhase, laneStep, start124]
  · change mapId124 (laneStep start124) = mapId124 start124
    norm_num [mapId124, laneStep, start124]
  · rfl
  · exact expanded_doing_requirements_covered expandedStart (by
      change episodePhase start124 = .doing
      simp [episodePhase, start124])
  · exact expanded_dynamic_encounter_enters_history
      climbProblem start124 (0 : Seat)
  · exact expanded_dynamic_retains_history
      climbProblem start124 (0 : Seat)

theorem expanded_satisfies_B6 :
    canonicalB6 expandedSystem := by
  constructor
  · exact ⟨expandedStart, expandedStep expandedStart,
      expanded_start_earned_completion⟩
  · intro before hdoing hdone
    rcases before with ⟨q, mode, lane, seat⟩
    cases mode
    · exact expanded_doing_requirements_covered
        (dynamicState q lane seat) hdoing
    · change CompletionPhase.doing = CompletionPhase.done at hdone
      cases hdone

/-! ## 8. B8 provenance transport survives -/

def expandedB8Source : ExpandedState :=
  dynamicState climbProblem b8Source (0 : Seat)

def expandedB8Destination : ExpandedState :=
  dynamicState climbProblem b8Destination (0 : Seat)

theorem expanded_satisfies_B8 :
    canonicalB8 expandedSystem := by
  constructor
  · refine ⟨expandedB8Source, expandedB8Destination,
      ?_, ?_, ?_, ?_, ?_⟩
    · change (0 : Nat) ≠ 7
      norm_num
    · rfl
    · rfl
    · rfl
    · rfl
  · intro source destination htransport
    rcases source with ⟨qs, ms, ls, ss⟩
    rcases destination with ⟨qd, md, ld, sd⟩
    cases ms <;> cases md <;> exact htransport

/-! ## 9. B10 injective time and open possibility -/

theorem expandedStep_injective :
    Function.Injective expandedStep := by
  intro x y h
  rcases x with ⟨qx, mx, lx, sx⟩
  rcases y with ⟨qy, my, ly, sy⟩
  cases mx <;> cases my
  · have hq : qx = qy := by
      have hp := congrArg (fun z : ExpandedState => z.1) h
      simpa [expandedStep, dynamicState] using hp
    have hs : sx = sy := by
      have hp := congrArg (fun z : ExpandedState => z.2.2.2) h
      simpa [expandedStep, dynamicState] using hp
    have hlstep : laneStep lx = laneStep ly := by
      have hp := congrArg (fun z : ExpandedState => z.2.2.1) h
      simpa [expandedStep, dynamicState] using hp
    have hl : lx = ly := laneStep_injective hlstep
    subst qy
    subst ly
    subst sy
    rfl
  · have hm := congrArg expandedMode h
    cases hm
  · have hm := congrArg expandedMode h
    cases hm
  · have hq : qx = qy := by
      have hp := congrArg (fun z : ExpandedState => z.1) h
      simpa [expandedStep, makingState] using hp
    have hl : lx = ly := by
      have hp := congrArg (fun z : ExpandedState => z.2.2.1) h
      simpa [expandedStep, makingState] using hp
    have hsstep : clockStep sx = clockStep sy := by
      have hp := congrArg (fun z : ExpandedState => z.2.2.2) h
      simpa [expandedStep, makingState] using hp
    have hs : sx = sy := clockStep_injective hsstep
    subst qy
    subst ly
    subst sy
    rfl

theorem expanded_den_nontrivial :
    ∃ expression state,
      expandedSystem.den expression state ∧
        ¬ (∀ other, expandedSystem.den expression other) := by
  refine ⟨makingModeExpr,
    makingState climbProblem start124 (0 : Seat), rfl, ?_⟩
  intro hall
  have hbad := hall expandedStart
  change false = true at hbad
  cases hbad

theorem expanded_clock_reveals_next_observation :
    ∃ state observation,
      ¬ expandedSystem.revealed state observation ∧
        expandedSystem.revealed
          (expandedSystem.step state) observation := by
  refine ⟨expandedStart,
    expandedObserve (expandedStep expandedStart), ?_, rfl⟩
  change ¬ (laneObserve start124 = laneObserve (laneStep start124))
  native_decide

theorem expanded_possibilities_persist :
    ∀ state possibility,
      expandedSystem.possible state possibility →
        expandedSystem.possible (expandedSystem.step state) possibility := by
  intro _ _ _
  trivial

theorem expanded_two_possibilities_remain :
    ∀ state, ∃ first second : Bool,
      first ≠ second ∧
      expandedSystem.possible (expandedSystem.step state) first ∧
      expandedSystem.possible (expandedSystem.step state) second := by
  intro _
  exact ⟨false, true, by decide, trivial, trivial⟩

theorem expanded_satisfies_B10 :
    canonicalB10 expandedSystem :=
  ⟨expandedStep_injective,
    expanded_den_nontrivial,
    expanded_clock_reveals_next_observation,
    expanded_possibilities_persist,
    expanded_two_possibilities_remain⟩

/-! ## 10. B7 semantic consistency and output-reference -/

theorem expanded_consistent :
    Consistent expandedSystem := by
  intro hfalse
  exact hfalse expandedStart

theorem expanded_step_refers_to_output
    (x : ExpandedState) :
    expandedSystem.refersToOutput x (expandedSystem.outputStep x) := by
  rcases x with ⟨q, mode, lane, seat⟩
  cases mode <;> exact ⟨rfl, rfl, rfl⟩

theorem expanded_output_step_is_diagonal_operator
    (e : ExpandedState → ExpandedState → ExpandedState) :
    ¬ FoundationStone.CompleteListing e := by
  exact FoundationStone.diagonal
    expandedStep expandedStep_changes_state e

theorem expanded_satisfies_B7 :
    canonicalB7 expandedSystem :=
  ⟨⟨expandedStart⟩,
    expanded_consistent,
    expanded_step_refers_to_output,
    expandedStep_changes_state⟩

/-! ## 11. B11 global halting invariant survives both modes -/

def expandedHelixInvariant (s : ExpandedState) : Prop :=
  HelixHalts (expandedProblem s)

theorem expandedHelixInvariant_preserved :
    MapInvariant expandedSystem expandedHelixInvariant := by
  intro x hx
  rcases x with ⟨q, mode, lane, seat⟩
  cases mode <;> exact hx

def embedExpandedProblem (q : Problem) : ExpandedState :=
  dynamicState q start124 (0 : Seat)

theorem embedExpandedProblem_computable :
    Computable embedExpandedProblem := by
  unfold embedExpandedProblem dynamicState
  exact Computable.id.pair
    (Computable.const (false, (start124, (0 : Seat))))

theorem helix_to_expanded_invariant_is_effective :
    HelixHalts ≤₀ expandedHelixInvariant := by
  exact ⟨embedExpandedProblem, embedExpandedProblem_computable,
    fun _ => Iff.rfl⟩

theorem expandedHelixInvariant_not_computable :
    ¬ ComputablePred expandedHelixInvariant := by
  intro h
  exact helix_halting_is_not_computable
    (ComputablePred.computable_of_manyOneReducible
      helix_to_expanded_invariant_is_effective h)

theorem expandedHelixInvariant_not_false :
    expandedHelixInvariant ≠ (fun _ => False) := by
  intro h
  apply expandedHelixInvariant_not_computable
  rw [h]
  exact false_expanded_property_computable

theorem expandedHelixInvariant_not_true :
    expandedHelixInvariant ≠ (fun _ => True) := by
  intro h
  apply expandedHelixInvariant_not_computable
  rw [h]
  exact true_expanded_property_computable

theorem no_expanded_internal_expression_names_halting :
    ¬ (∃ expression : ExpandedInternalExpr,
      Denotes expandedSystem expression expandedHelixInvariant) := by
  rintro ⟨expression, hden⟩
  have heq : expression.pred = expandedHelixInvariant := by
    funext x
    apply propext
    exact hden x
  apply expandedHelixInvariant_not_computable
  rw [← heq]
  exact expression.computable

theorem expanded_satisfies_B11 :
    canonicalB11 expandedSystem := by
  refine ⟨expandedHelixInvariant,
    expandedHelixInvariant_preserved,
    expandedHelixInvariant_not_false,
    expandedHelixInvariant_not_true,
    no_expanded_internal_expression_names_halting⟩

/-! ## 12. B12 productive continuation remains in dynamic mode -/

theorem expanded_done_step_available
    (completed : ExpandedState)
    (hdone : expandedSystem.phase completed = .done) :
    AvailableLinkedSeed expandedSystem completed (expandedStep completed) := by
  rcases completed with ⟨q, mode, lane, seat⟩
  cases mode
  · change episodePhase lane = .done at hdone
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, hdone, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
    · change mapId124 (laneStep lane) ≠ mapId124 lane
      exact done_step_map_changes lane hdone
    · change episodePhase (laneStep lane) = .doing
      exact done_step_phase_doing lane hdone
    · exact expanded_dynamic_encounter_enters_history q lane seat
    · exact expanded_dynamic_retains_history q lane seat
  · simp [expandedSystem, expandedPhase] at hdone

theorem expanded_done_has_linked_seed
    (completed : ExpandedState)
    (hdone : expandedSystem.phase completed = .done) :
    ∃ seed, AvailableLinkedSeed expandedSystem completed seed :=
  ⟨expandedStep completed, expanded_done_step_available completed hdone⟩

theorem expanded_one_step_reachable (s : ExpandedState) :
    Reachable expandedSystem s (expandedStep s) :=
  ⟨1, rfl⟩

theorem expanded_continuation_characterisation
    (completed later : ExpandedState) :
    expandedSystem.continuation completed later ↔
      RealisedLinkedContinuation expandedSystem completed later := by
  constructor
  · intro hcont
    change expandedAvailableSeed completed later at hcont
    rcases hcont with ⟨hmode, hdone, hlater⟩
    subst later
    rcases completed with ⟨q, mode, lane, seat⟩
    cases mode
    · refine ⟨expanded_done_step_available
          (dynamicState q lane seat) ?_, ?_, ?_⟩
      · exact hdone
      · change realised124 (laneStep lane)
        exact lane_native_step (laneStep lane)
      · exact expanded_one_step_reachable
          (dynamicState q lane seat)
    · cases hmode
  · intro hreal
    exact hreal.1.1

theorem expanded_satisfies_B12 :
    canonicalB12 expandedSystem :=
  ⟨expanded_done_has_linked_seed,
    expanded_continuation_characterisation⟩

/-! ## 13. B3: stable making interval with unnameable source -/

def makingHaltingInvariant (s : ExpandedState) : Prop :=
  expandedMode s = true ∧ HelixHalts (expandedProblem s)

theorem makingHaltingInvariant_preserved :
    MapInvariant expandedSystem makingHaltingInvariant := by
  intro x hx
  rcases x with ⟨q, mode, lane, seat⟩
  rcases hx with ⟨hmode, hhalt⟩
  cases mode
  · cases hmode
  · exact ⟨rfl, hhalt⟩

theorem makingHaltingInvariant_backward :
    BackwardStable expandedSystem makingHaltingInvariant := by
  intro x hx
  rcases x with ⟨q, mode, lane, seat⟩
  rcases hx with ⟨hmode, hhalt⟩
  cases mode
  · cases hmode
  · refine ⟨makingState q lane (back seat), ?_, ?_⟩
    · exact ⟨rfl, hhalt⟩
    · change makingState q lane (clockStep (back seat)) =
        makingState q lane seat
      rw [clockStep_back]

def simpleHaltProblem : Problem :=
  ([halt], (0, 0))

theorem simpleHaltProblem_halts :
    HelixHalts simpleHaltProblem := by
  refine ⟨1, ?_⟩
  rfl

def makingWitness : ExpandedState :=
  makingState simpleHaltProblem (false, 0) (0 : Seat)

theorem making_witness_recognised_and_usable :
    makingHaltingInvariant makingWitness ∧
      expandedSystem.recognises false makingWitness ∧
      expandedSystem.usableBy false makingWitness := by
  exact ⟨⟨rfl, simpleHaltProblem_halts⟩, rfl, rfl⟩

def embedMakingProblem (q : Problem) : ExpandedState :=
  makingState q (false, 0) (0 : Seat)

theorem embedMakingProblem_computable :
    Computable embedMakingProblem := by
  unfold embedMakingProblem makingState
  exact Computable.id.pair
    (Computable.const (true, (((false, 0) : LaneState), (0 : Seat))))

theorem helix_to_making_invariant_is_effective :
    HelixHalts ≤₀ makingHaltingInvariant := by
  refine ⟨embedMakingProblem, embedMakingProblem_computable, ?_⟩
  intro q
  simp [makingHaltingInvariant, embedMakingProblem]

theorem makingHaltingInvariant_not_computable :
    ¬ ComputablePred makingHaltingInvariant := by
  intro h
  exact helix_halting_is_not_computable
    (ComputablePred.computable_of_manyOneReducible
      helix_to_making_invariant_is_effective h)

theorem no_expanded_expression_names_making_source :
    ¬ (∃ expression : ExpandedInternalExpr,
      Denotes expandedSystem expression makingHaltingInvariant) := by
  rintro ⟨expression, hden⟩
  have heq : expression.pred = makingHaltingInvariant := by
    funext x
    apply propext
    exact hden x
  apply makingHaltingInvariant_not_computable
  rw [← heq]
  exact expression.computable

theorem expanded_satisfies_B3 :
    canonicalB3 expandedSystem := by
  refine ⟨makingHaltingInvariant,
    makingHaltingInvariant_preserved,
    makingHaltingInvariant_backward,
    ?_,
    no_expanded_expression_names_making_source⟩
  exact ⟨false, makingWitness,
    making_witness_recognised_and_usable.1,
    making_witness_recognised_and_usable.2.1,
    making_witness_recognised_and_usable.2.2⟩

/-! B3 red control: unrestricted language names every stable source. -/

@[reducible] noncomputable def expandedUnrestrictedSystem : System :=
  expandedSystemWithLanguage
    (ExpandedState → Prop)
    (fun P x => P x)
    (fun _ => False)
    (fun _ => True)

theorem expanded_unrestricted_names_every_property
    (I : ExpandedState → Prop) :
    ∃ expression : expandedUnrestrictedSystem.Language,
      Denotes expandedUnrestrictedSystem expression I :=
  ⟨I, fun _ => Iff.rfl⟩

theorem expanded_unrestricted_fails_B3 :
    ¬ canonicalB3 expandedUnrestrictedSystem := by
  rintro ⟨I, _hinvariant, _hbackward, _hrecognised, hunnamed⟩
  exact hunnamed (expanded_unrestricted_names_every_property I)

/-! ## 14. Eleven-way certificate -/

theorem B12346789101112_one_chamber_system_certificate :
    canonicalB1 expandedSystem ∧
    canonicalB2 expandedSystem ∧
    canonicalB3 expandedSystem ∧
    canonicalB4 expandedSystem ∧
    canonicalB6 expandedSystem ∧
    canonicalB7 expandedSystem ∧
    canonicalB8 expandedSystem ∧
    canonicalB9 expandedSystem ∧
    canonicalB10 expandedSystem ∧
    canonicalB11 expandedSystem ∧
    canonicalB12 expandedSystem ∧
    ¬ canonicalB3 expandedUnrestrictedSystem := by
  exact ⟨expanded_satisfies_B1,
    expanded_satisfies_B2,
    expanded_satisfies_B3,
    expanded_satisfies_B4,
    expanded_satisfies_B6,
    expanded_satisfies_B7,
    expanded_satisfies_B8,
    expanded_satisfies_B9,
    expanded_satisfies_B10,
    expanded_satisfies_B11,
    expanded_satisfies_B12,
    expanded_unrestricted_fails_B3⟩

#print axioms clockStep_back
#print axioms expanded_satisfies_B1
#print axioms expanded_satisfies_B2
#print axioms expanded_satisfies_B3
#print axioms expanded_satisfies_B4
#print axioms expanded_satisfies_B6
#print axioms expanded_satisfies_B7
#print axioms expanded_satisfies_B8
#print axioms expanded_satisfies_B9
#print axioms expanded_satisfies_B10
#print axioms expanded_satisfies_B11
#print axioms expanded_satisfies_B12
#print axioms makingHaltingInvariant_not_computable
#print axioms expanded_unrestricted_fails_B3
#print axioms B12346789101112_one_chamber_system_certificate

end
end TuringChamberB3ElevenWay
