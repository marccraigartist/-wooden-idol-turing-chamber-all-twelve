import TuringChamber_B1NativeGlobalReachability
import TuringChamber_B11HaltingInvariant
import FoundationStoneTest1
import Mathlib

/-!
# THE TURING CHAMBER — B1 / B2 / B3 / B4 / B6 / B7 / B8 / B9 / B10 / B11 / B12 ON ONE CHAMBER SYSTEM
## First simultaneous Wooden Idol constraint cluster

PURPOSE

B1, B2, B4 and B9 are already separately green on Chamber-derived adapters.
This file asks the stronger architectural question:

  can ONE system, with one carrier, one step, one body identity, one
  observation, one relation and one finite-table interpreter, satisfy
  B1, B2, B4 and B9 simultaneously?

The common carrier is two native 16AF climber lanes, each with an unbounded
level. The Bool lane marker is stored in Body B and is untouched by the
climber program; the level is realised by repeated native climbing of Body A.

The same system is then required to satisfy:

* B1: no single finite table decides its complete reachability relation;
* B2: one rich orbit is injective, observation is nonconstant, and the
      12-seat observation recurs arbitrarily late;
* B4: the independently declared relation "same lane" is exactly
      co-recurrence;
* B9: every full state changes, the lane/body identity is preserved, and
      the same relation is invariant under simultaneous stepping.

This is not four imported certificates. The four K31-shaped predicates below
are proved directly on the same record.

CLAIMS DISCIPLINE

* The step is realised step-for-step by actual 16AF climber execution.
* relation is defined independently as equality of the preserved lane marker;
  it is not defined to be CoRecurrent.
* B1 remains at exact K31 no-single-finite-table strength; it is not silently
  upgraded to general algorithmic undecidability.
* The individual B1/B2/B4/B9 files retain their separate failure controls.
* This is the first reduced one-system cluster, not yet a full Stage3.System
  AllTwelve witness.
* No zeta or RH claim is used.
-/

namespace TuringChamberB124OneSystem

set_option autoImplicit false

open FoundationStoneTest16AF
open TuringChamberForgetfulView
open TuringChamberB2NativeRecurrence


/-! ## 1. One common K31-visible system slice -/

inductive CompletionPhase where
  | doing
  | done
deriving DecidableEq, Repr

structure System where
  X : Type
  K : Type
  Site : Type
  Origin : Type
  Language : Type
  Possibility : Type
  Observation : Type
  step : X → X
  bodyAt : X → K
  phase : X → CompletionPhase
  mapId : X → Nat
  requiredSteps : X → List Unit
  performedSteps : X → List Unit
  history : X → List Nat
  encounterId : X → Nat
  availableSeed : X → X → Prop
  linkedTo : X → X → Prop
  continuation : X → X → Prop
  realised : X → Prop
  encounterSite : X → Site
  coherent : X → Prop
  transport : X → X → X
  originAt : X → Origin
  interp : Nat → X → X → Bool
  finuniversal : ∀ Q : X → X → Prop,
    (∀ x y, Decidable (Q x y)) →
      ∀ finiteWindow : Finset X, ∃ table,
        ∀ x ∈ finiteWindow, ∀ y ∈ finiteWindow,
          interp table x y = true ↔ Q x y
  observe : X → Observation
  den : Language → X → Prop
  Prf : Language → Prop
  falsum : Language
  con : Language
  refersToOutput : X → X → Prop
  outputStep : X → X
  possible : X → Possibility → Prop
  revealed : X → Observation → Prop
  relation : X → X → Prop
  recognises : K → X → Prop
  usableBy : K → X → Prop

def Reachable (S : System) (x y : S.X) : Prop :=
  ∃ n : Nat, (S.step^[n]) x = y

def CoRecurrent (S : System) (x y : S.X) : Prop :=
  ∃ n m : Nat, (S.step^[n]) x = (S.step^[m]) y

def canonicalB1 (S : System) : Prop :=
  ¬ (∃ table : Nat, ∀ x y,
    S.interp table x y = true ↔ Reachable S x y)

def canonicalB2 (S : System) : Prop :=
  ∃ x : S.X,
    Function.Injective (fun n : Nat => (S.step^[n]) x) ∧
    (∃ i j : Nat,
      S.observe ((S.step^[i]) x) ≠
        S.observe ((S.step^[j]) x)) ∧
    ∀ cutoff : Nat, ∃ later : Nat,
      cutoff < later ∧
        S.observe ((S.step^[later]) x) = S.observe x

def canonicalB4 (S : System) : Prop :=
  ∀ x y, S.relation x y ↔ CoRecurrent S x y

def canonicalB9 (S : System) : Prop :=
  (∀ x, S.step x ≠ x ∧ S.bodyAt (S.step x) = S.bodyAt x) ∧
    ∀ x y,
      S.relation (S.step x) (S.step y) ↔ S.relation x y

def RetainsHistory (S : System) (before after : S.X) : Prop :=
  ∀ origin, origin ∈ S.history before → origin ∈ S.history after

def EpisodeRequirementsCovered (S : System) (state : S.X) : Prop :=
  S.requiredSteps state ≠ [] ∧
    (S.requiredSteps state).Nodup ∧
    ∀ requirement,
      requirement ∈ S.requiredSteps state →
        requirement ∈ S.performedSteps state

def EarnedCompletionTransition (S : System) (before after : S.X) : Prop :=
  after = S.step before ∧
    before ≠ after ∧
    S.phase before = .doing ∧
    S.phase after = .done ∧
    S.mapId after = S.mapId before ∧
    S.bodyAt after = S.bodyAt before ∧
    EpisodeRequirementsCovered S before ∧
    S.encounterId before ∈ S.history after ∧
    RetainsHistory S before after

def canonicalB6 (S : System) : Prop :=
  (∃ before after, EarnedCompletionTransition S before after) ∧
    ∀ before,
      S.phase before = .doing →
      S.phase (S.step before) = .done →
        EpisodeRequirementsCovered S before

def AvailableLinkedSeed (S : System) (completed seed : S.X) : Prop :=
  S.availableSeed completed seed ∧
    S.linkedTo completed seed ∧
    S.mapId seed ≠ S.mapId completed ∧
    S.phase seed = .doing ∧
    S.encounterId completed ∈ S.history seed ∧
    RetainsHistory S completed seed

def RealisedLinkedContinuation (S : System) (completed later : S.X) : Prop :=
  AvailableLinkedSeed S completed later ∧
    S.realised later ∧
    Reachable S completed later

def canonicalB12 (S : System) : Prop :=
  (∀ completed,
    S.phase completed = .done →
      ∃ seed, AvailableLinkedSeed S completed seed) ∧
  ∀ completed later,
    S.continuation completed later ↔
      RealisedLinkedContinuation S completed later

def canonicalB8 (S : System) : Prop :=
  (∃ source destination,
    S.encounterSite source ≠ S.encounterSite destination ∧
    S.coherent source ∧
    S.coherent (S.transport source destination) ∧
    S.encounterSite (S.transport source destination) =
      S.encounterSite destination ∧
    S.originAt (S.transport source destination) = S.originAt source) ∧
  ∀ source destination,
    S.coherent (S.transport source destination) → S.coherent source

def manufacturedCoherenceControl (S : System) : Prop :=
  ∃ source destination,
    S.coherent (S.transport source destination) ∧
      ¬ S.coherent source

theorem manufactured_coherence_control_rejects_B8
    (S : System) (hcontrol : manufacturedCoherenceControl S) :
    ¬ canonicalB8 S := by
  rintro ⟨_htransport, hnoncreative⟩
  obtain ⟨source, destination, hcoherent, hsource⟩ := hcontrol
  exact hsource (hnoncreative source destination hcoherent)

def canonicalB10 (S : System) : Prop :=
  Function.Injective S.step ∧
    (∃ expression state,
      S.den expression state ∧
        ¬ (∀ other, S.den expression other)) ∧
    (∃ state observation,
      ¬ S.revealed state observation ∧
        S.revealed (S.step state) observation) ∧
    (∀ state possibility,
      S.possible state possibility →
        S.possible (S.step state) possibility) ∧
    ∀ state, ∃ first second,
      first ≠ second ∧
      S.possible (S.step state) first ∧
      S.possible (S.step state) second

def possibilityDeletionControl (S : System) : Prop :=
  ∃ state possibility,
    S.possible state possibility ∧
      ¬ S.possible (S.step state) possibility

theorem possibility_deletion_control_rejects_B10
    (S : System) (hcontrol : possibilityDeletionControl S) :
    ¬ canonicalB10 S := by
  rintro ⟨_hinjective, _hnontrivial, _hreveals, hretains, _hopen⟩
  obtain ⟨state, possibility, hpossible, hdeleted⟩ := hcontrol
  exact hdeleted (hretains state possibility hpossible)

def Consistent (S : System) : Prop :=
  ¬ S.Prf S.falsum

def canonicalB7 (S : System) : Prop :=
  Nonempty S.X ∧
    Consistent S ∧
    (∀ x, S.refersToOutput x (S.outputStep x)) ∧
    ∀ x, S.outputStep x ≠ x

def extensionalSelfReferenceControl (S : System) : Prop :=
  ∀ x, S.outputStep (S.outputStep x) = S.outputStep x

theorem extensional_self_reference_control_rejects_B7
    (S : System) (hextensional : extensionalSelfReferenceControl S) :
    ¬ canonicalB7 S := by
  rintro ⟨hnonempty, _hconsistent, _hrefers, hnofixed⟩
  obtain ⟨x⟩ := hnonempty
  exact hnofixed (S.outputStep x) (hextensional x)

/-! ## 2. One native two-lane climber carrier -/

abbrev LaneState := Bool × Nat

def laneMarker : Bool → BodyState
  | false => ⟨0, 0⟩
  | true => ⟨1, 0⟩

def laneStart (b : Bool) : LiveClimber where
  state :=
    { helixStart climbProblem with
      bodyB := laneMarker b }
  pc_zero := rfl

def laneToLive (s : LaneState) : LiveClimber :=
  (climberStep^[s.2]) (laneStart s.1)

def laneStep (s : LaneState) : LaneState :=
  (s.1, s.2 + 1)

def laneObserve (s : LaneState) : Seat :=
  clockView (laneToLive s)

def sameLane (x y : LaneState) : Prop :=
  x.1 = y.1

def start124 : LaneState := (false, 0)

/-- Episode phase is an overlay on native step parity.  Even native levels are
doing states; the next native step completes the episode. -/
def episodePhase (s : LaneState) : CompletionPhase :=
  if s.2 % 2 = 0 then .doing else .done

/-- Two adjacent states 2k and 2k+1 belong to the same map episode. -/
def mapId124 (s : LaneState) : Nat :=
  s.2 / 2

def required124 (_ : LaneState) : List Unit := [()]

/-- The one episode requirement is recorded as performed in the doing phase. -/
def performed124 (s : LaneState) : List Unit :=
  if episodePhase s = .doing then [()] else []

/-- Native progress monotonically accumulates encounter provenance. -/
def history124 (s : LaneState) : List Nat :=
  List.range (s.2 + 1)

def encounterId124 (s : LaneState) : Nat :=
  s.2

def availableSeed124 (completed seed : LaneState) : Prop :=
  episodePhase completed = .done ∧
    seed = laneStep completed

def linkedTo124 (completed seed : LaneState) : Prop :=
  sameLane completed seed ∧
    seed.2 = completed.2 + 1

def continuation124 (completed later : LaneState) : Prop :=
  availableSeed124 completed later

/-- Productivity is the existence of the actual next native helix transition,
not a stored productivity label. -/
def realised124 (state : LaneState) : Prop :=
  hstep climber (laneToLive state).state =
    some (laneToLive (laneStep state)).state

/-- B8 site is the current encounter level. -/
def encounterSite124 (s : LaneState) : Nat :=
  s.2

/-- The origin is the zero-level seed of the lane carrying the state. -/
def originAt124 (s : LaneState) : LaneState :=
  (s.1, 0)

/-- Coherence is defined independently of transport: one provenance class is
accepted as coherent before any movement occurs. -/
def coherent124 (s : LaneState) : Prop :=
  s.1 = false

/-- Transport relocates a source to the destination site while retaining the
source lane/origin. -/
def transport124 (source destination : LaneState) : LaneState :=
  (source.1, destination.2)

/-- Forged transport manufactures the coherent provenance class regardless of
the source and is used only as the B8 red control. -/
def forgedTransport124 (_source destination : LaneState) : LaneState :=
  (false, destination.2)

/-- B10 language names the two provenance/lane classes. -/
def den124 (expression : Bool) (state : LaneState) : Prop :=
  state.1 = expression

/-- A revealed observation is the actual clock observation at this state. -/
def revealed124 (state : LaneState) (observation : Seat) : Prop :=
  laneObserve state = observation

/-- The possibility frame forgets the lane coordinate, so both lane hypotheses
remain open at every time. -/
def possible124 (_state : LaneState) (_possibility : Bool) : Prop :=
  True

/-- Negative control: one lane hypothesis is deleted when time advances. -/
def deletingPossible124 (state : LaneState) (possibility : Bool) : Prop :=
  if state.2 % 2 = 0 then possibility = false else possibility = true

def semanticPrf124 (expression : Bool) : Prop :=
  ∀ state : LaneState, den124 expression state

def refersToOutput124 (source output : LaneState) : Prop :=
  output.1 = source.1 ∧
    output.2 = source.2 + 1

theorem laneToLive_step (s : LaneState) :
    laneToLive (laneStep s) = climberStep (laneToLive s) := by
  simp [laneToLive, laneStep, Function.iterate_succ_apply']

theorem lane_native_step (s : LaneState) :
    hstep climber (laneToLive s).state =
      some (laneToLive (laneStep s)).state := by
  rw [laneToLive_step]
  exact climberStep_is_native_hstep (laneToLive s)

theorem lane_iterate :
    ∀ n (s : LaneState),
      (laneStep^[n]) s = (s.1, s.2 + n) := by
  intro n
  induction n with
  | zero =>
      intro s
      simp
  | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply']
      rw [ih]
      simp [laneStep, Nat.add_assoc]

theorem laneToLive_iterate :
    ∀ n (s : LaneState),
      laneToLive ((laneStep^[n]) s) =
        (climberStep^[n]) (laneToLive s) := by
  intro n
  induction n with
  | zero =>
      intro s
      rfl
  | succ n ih =>
      intro s
      simp only [Function.iterate_succ_apply']
      rw [laneToLive_step, ih]

theorem laneObserve_iterate (n : Nat) (s : LaneState) :
    laneObserve ((laneStep^[n]) s) =
      (clockStep^[n]) (laneObserve s) := by
  unfold laneObserve
  rw [laneToLive_iterate]
  exact clockView_iterate_commutes n (laneToLive s)

/-! ## 3. The single system -/

noncomputable def chamber124 : System where
  X := LaneState
  K := Bool
  Site := Nat
  Origin := LaneState
  Language := Bool
  Possibility := Bool
  Observation := Seat
  step := laneStep
  bodyAt := Prod.fst
  phase := episodePhase
  mapId := mapId124
  requiredSteps := required124
  performedSteps := performed124
  history := history124
  encounterId := encounterId124
  availableSeed := availableSeed124
  linkedTo := linkedTo124
  continuation := continuation124
  realised := realised124
  encounterSite := encounterSite124
  coherent := coherent124
  transport := transport124
  originAt := originAt124
  interp := TuringChamberB1NativeGlobalReachability.finiteInterp
  finuniversal := TuringChamberB1NativeGlobalReachability.finiteInterp_finiteUniversal
  observe := laneObserve
  den := den124
  Prf := semanticPrf124
  falsum := false
  con := true
  refersToOutput := refersToOutput124
  outputStep := laneStep
  possible := possible124
  revealed := revealed124
  relation := sameLane
  recognises := fun body state => body = state.1
  usableBy := fun body state => body = state.1

/-! ## 4. B1 on the common system -/

def escapeLevel (s : Finset (LaneState × LaneState)) : Nat :=
  s.sup (fun pair : LaneState × LaneState => pair.2.2) + 1

theorem start_reaches_level (k : Nat) :
    Reachable chamber124 start124 (false, k) := by
  refine ⟨k, ?_⟩
  change (laneStep^[k]) start124 = (false, k)
  rw [lane_iterate]
  simp [start124]

theorem start_escape_not_mem (s : Finset (LaneState × LaneState)) :
    (start124, (false, escapeLevel s)) ∉ s := by
  intro hmem
  have hle :
      escapeLevel s ≤
        s.sup (fun pair : LaneState × LaneState => pair.2.2) := by
    simpa [start124] using
      (Finset.le_sup
        (s := s)
        (f := fun pair : LaneState × LaneState => pair.2.2)
        hmem)
  unfold escapeLevel at hle
  omega

theorem chamber124_satisfies_B1 :
    canonicalB1 chamber124 := by
  rintro ⟨table, htable⟩
  change
    (∀ x y : LaneState,
      TuringChamberB1NativeGlobalReachability.finiteInterp table x y = true ↔
        ∃ n : Nat, (laneStep^[n]) x = y) at htable
  let s : Finset (LaneState × LaneState) :=
    TuringChamberB1NativeGlobalReachability.decodedRelation table
  let y : LaneState := (false, escapeLevel s)
  have hyreach :
      ∃ n : Nat, (laneStep^[n]) start124 = y := by
    change Reachable chamber124 start124 y
    simpa [y] using start_reaches_level (escapeLevel s)
  have htrue : TuringChamberB1NativeGlobalReachability.finiteInterp table start124 y = true :=
    (htable start124 y).2 hyreach
  have hmem : (start124, y) ∈ s := by
    simpa [TuringChamberB1NativeGlobalReachability.finiteInterp, s] using htrue
  exact (start_escape_not_mem s) (by simpa [y] using hmem)

/-! ## 5. B2 on the very same system -/

theorem start124_orbit_injective :
    Function.Injective (fun n : Nat => (laneStep^[n]) start124) := by
  intro i j h
  have hh := congrArg Prod.snd h
  simpa [lane_iterate, start124] using hh

theorem start124_observation_nonconstant :
    ∃ i j : Nat,
      laneObserve ((laneStep^[i]) start124) ≠
        laneObserve ((laneStep^[j]) start124) := by
  refine ⟨0, 1, ?_⟩
  native_decide

theorem start124_observation_recurs_arbitrarily_late :
    ∀ cutoff : Nat, ∃ later : Nat,
      cutoff < later ∧
        laneObserve ((laneStep^[later]) start124) =
          laneObserve start124 := by
  intro cutoff
  refine ⟨12 * (cutoff + 1), ?_, ?_⟩
  · omega
  · rw [laneObserve_iterate]
    exact clock_iterate_twelve_mul (cutoff + 1) (laneObserve start124)

theorem chamber124_satisfies_B2 :
    canonicalB2 chamber124 := by
  refine ⟨start124, ?_, ?_, ?_⟩
  · change Function.Injective
      (fun n : Nat => (laneStep^[n]) start124)
    exact start124_orbit_injective
  · change ∃ i j : Nat,
      laneObserve ((laneStep^[i]) start124) ≠
        laneObserve ((laneStep^[j]) start124)
    exact start124_observation_nonconstant
  · change ∀ cutoff : Nat, ∃ later : Nat,
      cutoff < later ∧
        laneObserve ((laneStep^[later]) start124) =
          laneObserve start124
    exact start124_observation_recurs_arbitrarily_late

/-! ## 6. B4 on the same system, with an independently declared relation -/

theorem co_recurrent_implies_sameLane
    {x y : LaneState}
    (h : CoRecurrent chamber124 x y) :
    sameLane x y := by
  change ∃ n m : Nat,
    (laneStep^[n]) x = (laneStep^[m]) y at h
  rcases h with ⟨n, m, hmeet⟩
  rw [lane_iterate, lane_iterate] at hmeet
  have hlane := congrArg Prod.fst hmeet
  simpa [sameLane] using hlane

theorem sameLane_implies_co_recurrent
    {x y : LaneState}
    (h : sameLane x y) :
    CoRecurrent chamber124 x y := by
  change ∃ n m : Nat,
    (laneStep^[n]) x = (laneStep^[m]) y
  refine ⟨y.2, x.2, ?_⟩
  rw [lane_iterate, lane_iterate]
  rcases x with ⟨xl, xlevel⟩
  rcases y with ⟨yl, ylevel⟩
  change xl = yl at h
  subst yl
  simp [Nat.add_comm]

theorem chamber124_satisfies_B4 :
    canonicalB4 chamber124 := by
  intro x y
  constructor
  · exact sameLane_implies_co_recurrent
  · exact co_recurrent_implies_sameLane

/-! ## 7. B9 on the same system -/

theorem laneStep_changes_state (s : LaneState) :
    laneStep s ≠ s := by
  intro h
  have hh : s.2 + 1 = s.2 := by
    simpa [laneStep] using congrArg Prod.snd h
  omega

theorem lane_body_identity_preserved (s : LaneState) :
    chamber124.bodyAt (chamber124.step s) =
      chamber124.bodyAt s := by
  change (laneStep s).1 = s.1
  rfl

theorem sameLane_step_invariant (x y : LaneState) :
    chamber124.relation (chamber124.step x) (chamber124.step y) ↔
      chamber124.relation x y := by
  change sameLane (laneStep x) (laneStep y) ↔ sameLane x y
  simp [sameLane, laneStep]

theorem chamber124_satisfies_B9 :
    canonicalB9 chamber124 := by
  constructor
  · intro s
    exact ⟨laneStep_changes_state s, lane_body_identity_preserved s⟩
  · exact sameLane_step_invariant

/-! ## 8. B6 on the same system -/

theorem doing_requirements_covered
    (s : LaneState)
    (hdoing : chamber124.phase s = .doing) :
    EpisodeRequirementsCovered chamber124 s := by
  change episodePhase s = .doing at hdoing
  change
    [()] ≠ [] ∧
      [()].Nodup ∧
      ∀ requirement,
        requirement ∈ [()] →
          requirement ∈
            (if episodePhase s = .doing then [()] else [])
  simp [hdoing]

theorem laneStep_retains_history (s : LaneState) :
    RetainsHistory chamber124 s (laneStep s) := by
  intro origin horigin
  change origin ∈ history124 s at horigin
  change origin ∈ history124 (laneStep s)
  simp [history124, laneStep] at horigin ⊢
  omega

theorem encounter_enters_next_history (s : LaneState) :
    chamber124.encounterId s ∈ chamber124.history (chamber124.step s) := by
  change encounterId124 s ∈ history124 (laneStep s)
  simp [encounterId124, history124, laneStep]

theorem start124_earned_completion :
    EarnedCompletionTransition
      chamber124 start124 (laneStep start124) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact laneStep_changes_state start124 h.symm
  · change episodePhase start124 = .doing
    simp [episodePhase, start124]
  · change episodePhase (laneStep start124) = .done
    simp [episodePhase, laneStep, start124]
  · change mapId124 (laneStep start124) = mapId124 start124
    norm_num [mapId124, laneStep, start124]
  · exact lane_body_identity_preserved start124
  · exact doing_requirements_covered start124 (by
      change episodePhase start124 = .doing
      simp [episodePhase, start124])
  · exact encounter_enters_next_history start124
  · exact laneStep_retains_history start124

theorem chamber124_satisfies_B6 :
    canonicalB6 chamber124 := by
  constructor
  · exact ⟨start124, laneStep start124, start124_earned_completion⟩
  · intro before hdoing _hdone
    exact doing_requirements_covered before hdoing

/-! ## 9. B12 on the same system -/

theorem done_mod_two_eq_one
    (completed : LaneState)
    (hdone : episodePhase completed = .done) :
    completed.2 % 2 = 1 := by
  unfold episodePhase at hdone
  by_cases hzero : completed.2 % 2 = 0
  · simp [hzero] at hdone
  · have hlt : completed.2 % 2 < 2 :=
      Nat.mod_lt _ (by decide)
    omega

theorem done_step_phase_doing
    (completed : LaneState)
    (hdone : episodePhase completed = .done) :
    episodePhase (laneStep completed) = .doing := by
  have hmod := done_mod_two_eq_one completed hdone
  have hnext : (completed.2 + 1) % 2 = 0 := by
    omega
  simp [episodePhase, laneStep, hnext]

theorem done_step_map_changes
    (completed : LaneState)
    (hdone : episodePhase completed = .done) :
    mapId124 (laneStep completed) ≠ mapId124 completed := by
  have hmod := done_mod_two_eq_one completed hdone
  change (completed.2 + 1) / 2 ≠ completed.2 / 2
  omega

theorem done_step_linked (completed : LaneState) :
    linkedTo124 completed (laneStep completed) := by
  constructor
  · simp [sameLane, laneStep]
  · rfl

theorem native_successor_realised (s : LaneState) :
    realised124 s := by
  exact lane_native_step s

theorem done_step_available
    (completed : LaneState)
    (hdone : chamber124.phase completed = .done) :
    AvailableLinkedSeed chamber124 completed (laneStep completed) := by
  change episodePhase completed = .done at hdone
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change availableSeed124 completed (laneStep completed)
    exact ⟨hdone, rfl⟩
  · change linkedTo124 completed (laneStep completed)
    exact done_step_linked completed
  · change mapId124 (laneStep completed) ≠ mapId124 completed
    exact done_step_map_changes completed hdone
  · change episodePhase (laneStep completed) = .doing
    exact done_step_phase_doing completed hdone
  · exact encounter_enters_next_history completed
  · exact laneStep_retains_history completed

theorem done_has_linked_seed
    (completed : LaneState)
    (hdone : chamber124.phase completed = .done) :
    ∃ seed, AvailableLinkedSeed chamber124 completed seed :=
  ⟨laneStep completed, done_step_available completed hdone⟩

theorem one_step_reachable (s : LaneState) :
    Reachable chamber124 s (laneStep s) := by
  refine ⟨1, ?_⟩
  rfl

theorem continuation_characterisation
    (completed later : LaneState) :
    chamber124.continuation completed later ↔
      RealisedLinkedContinuation chamber124 completed later := by
  constructor
  · intro hcont
    change availableSeed124 completed later at hcont
    rcases hcont with ⟨hdone, rfl⟩
    refine ⟨done_step_available completed ?_, ?_, ?_⟩
    · change episodePhase completed = .done
      exact hdone
    · change realised124 (laneStep completed)
      exact native_successor_realised (laneStep completed)
    · exact one_step_reachable completed
  · intro hreal
    exact hreal.1.1

theorem chamber124_satisfies_B12 :
    canonicalB12 chamber124 := by
  constructor
  · exact done_has_linked_seed
  · exact continuation_characterisation

/-! ## 10. B8 on the same system -/

theorem transport124_preserves_site
    (source destination : LaneState) :
    encounterSite124 (transport124 source destination) =
      encounterSite124 destination := by
  rfl

theorem transport124_preserves_origin
    (source destination : LaneState) :
    originAt124 (transport124 source destination) =
      originAt124 source := by
  rfl

theorem transport124_preserves_coherence
    (source destination : LaneState)
    (hsource : coherent124 source) :
    coherent124 (transport124 source destination) := by
  exact hsource

theorem transport124_cannot_manufacture_coherence
    (source destination : LaneState)
    (htransport : coherent124 (transport124 source destination)) :
    coherent124 source := by
  exact htransport

def b8Source : LaneState := (false, 0)
def b8Destination : LaneState := (true, 7)

theorem chamber124_satisfies_B8 :
    canonicalB8 chamber124 := by
  constructor
  · refine ⟨b8Source, b8Destination, ?_, ?_, ?_, ?_, ?_⟩
    · change encounterSite124 b8Source ≠ encounterSite124 b8Destination
      norm_num [encounterSite124, b8Source, b8Destination]
    · rfl
    · rfl
    · exact transport124_preserves_site b8Source b8Destination
    · exact transport124_preserves_origin b8Source b8Destination
  · intro source destination htransport
    change coherent124 (transport124 source destination) at htransport
    change coherent124 source
    exact transport124_cannot_manufacture_coherence source destination htransport

noncomputable def forgedB8System : System :=
  { chamber124 with transport := forgedTransport124 }

theorem forged_transport_manufactures_coherence :
    manufacturedCoherenceControl forgedB8System := by
  refine ⟨(true, 0), (false, 5), ?_, ?_⟩
  · rfl
  · change ¬ coherent124 (true, 0)
    change ¬ (true = false)
    intro h
    cases h

theorem forged_transport_fails_B8 :
    ¬ canonicalB8 forgedB8System :=
  manufactured_coherence_control_rejects_B8
    forgedB8System forged_transport_manufactures_coherence

/-! ## 11. B10 on the same system -/

theorem laneStep_injective :
    Function.Injective laneStep := by
  rintro ⟨xb, xn⟩ ⟨yb, yn⟩ h
  simp [laneStep] at h ⊢
  exact h

theorem den124_nontrivial :
    ∃ expression state,
      den124 expression state ∧
        ¬ (∀ other, den124 expression other) := by
  refine ⟨false, (false, 0), rfl, ?_⟩
  intro hall
  have hbad := hall (true, 0)
  change true = false at hbad
  cases hbad

theorem clock_reveals_next_observation :
    ∃ state observation,
      ¬ revealed124 state observation ∧
        revealed124 (laneStep state) observation := by
  refine ⟨start124, laneObserve (laneStep start124), ?_, rfl⟩
  change ¬ (laneObserve start124 = laneObserve (laneStep start124))
  native_decide

theorem possibilities_persist :
    ∀ state possibility,
      possible124 state possibility →
        possible124 (laneStep state) possibility := by
  intro _state _possibility _h
  trivial

theorem two_possibilities_remain :
    ∀ state, ∃ first second : Bool,
      first ≠ second ∧
      possible124 (laneStep state) first ∧
      possible124 (laneStep state) second := by
  intro _state
  refine ⟨false, true, ?_, trivial, trivial⟩
  intro h
  cases h

theorem chamber124_satisfies_B10 :
    canonicalB10 chamber124 := by
  refine ⟨?_, den124_nontrivial, clock_reveals_next_observation,
    possibilities_persist, two_possibilities_remain⟩
  change Function.Injective laneStep
  exact laneStep_injective

noncomputable def deletingPossibilitySystem : System :=
  { chamber124 with possible := deletingPossible124 }

theorem deleting_possibility_control :
    possibilityDeletionControl deletingPossibilitySystem := by
  refine ⟨(false, 0), false, ?_, ?_⟩
  · change deletingPossible124 (false, 0) false
    simp [deletingPossible124]
  · change ¬ deletingPossible124 (laneStep (false, 0)) false
    simp [deletingPossible124, laneStep]

theorem deleting_possibility_fails_B10 :
    ¬ canonicalB10 deletingPossibilitySystem :=
  possibility_deletion_control_rejects_B10
    deletingPossibilitySystem deleting_possibility_control

/-! ## 12. One-system certificate -/

theorem relation_is_nontrivial :
    chamber124.relation (false, 0) (false, 7) ∧
      ¬ chamber124.relation (false, 0) (true, 0) := by
  change (false = false) ∧ ¬ (false = true)
  constructor
  · rfl
  · intro h
    cases h

theorem B124_one_native_system_certificate :
    (∀ s : LaneState,
      hstep climber (laneToLive s).state =
        some (laneToLive (laneStep s)).state) ∧
    canonicalB1 chamber124 ∧
    canonicalB2 chamber124 ∧
    canonicalB4 chamber124 ∧
    chamber124.relation (false, 0) (false, 7) ∧
    ¬ chamber124.relation (false, 0) (true, 0) := by
  exact ⟨lane_native_step,
    chamber124_satisfies_B1,
    chamber124_satisfies_B2,
    chamber124_satisfies_B4,
    relation_is_nontrivial.1,
    relation_is_nontrivial.2⟩

theorem B1249_one_native_system_certificate :
    (∀ s : LaneState,
      hstep climber (laneToLive s).state =
        some (laneToLive (laneStep s)).state) ∧
    canonicalB1 chamber124 ∧
    canonicalB2 chamber124 ∧
    canonicalB4 chamber124 ∧
    canonicalB9 chamber124 ∧
    chamber124.relation (false, 0) (false, 7) ∧
    ¬ chamber124.relation (false, 0) (true, 0) := by
  exact ⟨lane_native_step,
    chamber124_satisfies_B1,
    chamber124_satisfies_B2,
    chamber124_satisfies_B4,
    chamber124_satisfies_B9,
    relation_is_nontrivial.1,
    relation_is_nontrivial.2⟩

theorem B12469_one_native_system_certificate :
    (∀ s : LaneState,
      hstep climber (laneToLive s).state =
        some (laneToLive (laneStep s)).state) ∧
    canonicalB1 chamber124 ∧
    canonicalB2 chamber124 ∧
    canonicalB4 chamber124 ∧
    canonicalB6 chamber124 ∧
    canonicalB9 chamber124 ∧
    chamber124.relation (false, 0) (false, 7) ∧
    ¬ chamber124.relation (false, 0) (true, 0) := by
  exact ⟨lane_native_step,
    chamber124_satisfies_B1,
    chamber124_satisfies_B2,
    chamber124_satisfies_B4,
    chamber124_satisfies_B6,
    chamber124_satisfies_B9,
    relation_is_nontrivial.1,
    relation_is_nontrivial.2⟩

theorem B1246912_one_native_system_certificate :
    (∀ s : LaneState,
      hstep climber (laneToLive s).state =
        some (laneToLive (laneStep s)).state) ∧
    canonicalB1 chamber124 ∧
    canonicalB2 chamber124 ∧
    canonicalB4 chamber124 ∧
    canonicalB6 chamber124 ∧
    canonicalB9 chamber124 ∧
    canonicalB12 chamber124 ∧
    chamber124.relation (false, 0) (false, 7) ∧
    ¬ chamber124.relation (false, 0) (true, 0) := by
  exact ⟨lane_native_step,
    chamber124_satisfies_B1,
    chamber124_satisfies_B2,
    chamber124_satisfies_B4,
    chamber124_satisfies_B6,
    chamber124_satisfies_B9,
    chamber124_satisfies_B12,
    relation_is_nontrivial.1,
    relation_is_nontrivial.2⟩

theorem B1246812_one_native_system_certificate :
    (∀ s : LaneState,
      hstep climber (laneToLive s).state =
        some (laneToLive (laneStep s)).state) ∧
    canonicalB1 chamber124 ∧
    canonicalB2 chamber124 ∧
    canonicalB4 chamber124 ∧
    canonicalB6 chamber124 ∧
    canonicalB8 chamber124 ∧
    canonicalB9 chamber124 ∧
    canonicalB12 chamber124 ∧
    ¬ canonicalB8 forgedB8System ∧
    chamber124.relation (false, 0) (false, 7) ∧
    ¬ chamber124.relation (false, 0) (true, 0) := by
  exact ⟨lane_native_step,
    chamber124_satisfies_B1,
    chamber124_satisfies_B2,
    chamber124_satisfies_B4,
    chamber124_satisfies_B6,
    chamber124_satisfies_B8,
    chamber124_satisfies_B9,
    chamber124_satisfies_B12,
    forged_transport_fails_B8,
    relation_is_nontrivial.1,
    relation_is_nontrivial.2⟩

theorem B124681012_one_native_system_certificate :
    (∀ s : LaneState,
      hstep climber (laneToLive s).state =
        some (laneToLive (laneStep s)).state) ∧
    canonicalB1 chamber124 ∧
    canonicalB2 chamber124 ∧
    canonicalB4 chamber124 ∧
    canonicalB6 chamber124 ∧
    canonicalB8 chamber124 ∧
    canonicalB9 chamber124 ∧
    canonicalB10 chamber124 ∧
    canonicalB12 chamber124 ∧
    ¬ canonicalB8 forgedB8System ∧
    ¬ canonicalB10 deletingPossibilitySystem ∧
    chamber124.relation (false, 0) (false, 7) ∧
    ¬ chamber124.relation (false, 0) (true, 0) := by
  exact ⟨lane_native_step,
    chamber124_satisfies_B1,
    chamber124_satisfies_B2,
    chamber124_satisfies_B4,
    chamber124_satisfies_B6,
    chamber124_satisfies_B8,
    chamber124_satisfies_B9,
    chamber124_satisfies_B10,
    chamber124_satisfies_B12,
    forged_transport_fails_B8,
    deleting_possibility_fails_B10,
    relation_is_nontrivial.1,
    relation_is_nontrivial.2⟩

#print axioms lane_native_step
#print axioms chamber124_satisfies_B1
#print axioms chamber124_satisfies_B2
#print axioms chamber124_satisfies_B4
#print axioms chamber124_satisfies_B6
#print axioms chamber124_satisfies_B8
#print axioms chamber124_satisfies_B9
#print axioms chamber124_satisfies_B10
#print axioms chamber124_satisfies_B12
#print axioms forged_transport_fails_B8
#print axioms deleting_possibility_fails_B10
#print axioms B124_one_native_system_certificate
#print axioms B1249_one_native_system_certificate
#print axioms B12469_one_native_system_certificate
#print axioms B1246912_one_native_system_certificate
#print axioms B1246812_one_native_system_certificate
#print axioms B124681012_one_native_system_certificate


/-! ## 13. B11 integration: add the genuine Chamber halting parameter

The eight-way green system above remains untouched.  The stronger carrier below
adds one fixed FoundationStoneTest16AF.Problem coordinate to every native
climber state.  The native step changes only the climber coordinate, so the
existing B1/B2/B4/B6/B8/B9/B10/B12 architecture survives without defining B4
from relay co-recurrence.  B11's invariant is the actual global HelixHalts
predicate of the fixed problem coordinate.
-/

open FoundationStoneTest16BU

def MapInvariant (S : System) (I : S.X → Prop) : Prop :=
  ∀ x, I x → I (S.step x)

def Denotes (S : System) (expression : S.Language)
    (property : S.X → Prop) : Prop :=
  ∀ x, S.den expression x ↔ property x

def canonicalB11 (S : System) : Prop :=
  ∃ I : S.X → Prop,
    MapInvariant S I ∧
    I ≠ (fun _ => False) ∧
    I ≠ (fun _ => True) ∧
    ¬ (∃ expression : S.Language, Denotes S expression I)

abbrev UnifiedState := Problem × LaneState

noncomputable section

local instance unifiedStateDecidableEq :
    DecidableEq UnifiedState :=
  Classical.decEq UnifiedState

def unifiedStep (s : UnifiedState) : UnifiedState :=
  (s.1, laneStep s.2)

def unifiedObserve (s : UnifiedState) : Seat :=
  laneObserve s.2

def unifiedRelation (x y : UnifiedState) : Prop :=
  x.1 = y.1 ∧ sameLane x.2 y.2

def unifiedPhase (s : UnifiedState) : CompletionPhase :=
  episodePhase s.2

def unifiedMapId (s : UnifiedState) : Nat :=
  mapId124 s.2

def unifiedBodyAt (s : UnifiedState) : Bool :=
  s.2.1

def unifiedRequired (_ : UnifiedState) : List Unit := [()]

def unifiedPerformed (s : UnifiedState) : List Unit :=
  performed124 s.2

def unifiedHistory (s : UnifiedState) : List Nat :=
  history124 s.2

def unifiedEncounterId (s : UnifiedState) : Nat :=
  encounterId124 s.2

def unifiedAvailableSeed (completed seed : UnifiedState) : Prop :=
  completed.1 = seed.1 ∧
    availableSeed124 completed.2 seed.2

def unifiedLinkedTo (completed seed : UnifiedState) : Prop :=
  completed.1 = seed.1 ∧
    linkedTo124 completed.2 seed.2

def unifiedContinuation (completed later : UnifiedState) : Prop :=
  unifiedAvailableSeed completed later

def unifiedRealised (state : UnifiedState) : Prop :=
  realised124 state.2

def unifiedEncounterSite (s : UnifiedState) : Nat :=
  s.2.2

def unifiedCoherent (s : UnifiedState) : Prop :=
  coherent124 s.2

def unifiedTransport (source destination : UnifiedState) : UnifiedState :=
  (source.1, transport124 source.2 destination.2)

def unifiedOriginAt (s : UnifiedState) : UnifiedState :=
  (s.1, originAt124 s.2)

def unifiedPossible (_state : UnifiedState) (_possibility : Bool) : Prop :=
  True

def unifiedRevealed (state : UnifiedState) (observation : Seat) : Prop :=
  unifiedObserve state = observation

/-- Output-reference is structural and independent of outputStep: an output
retains the Chamber problem and lane identity and advances one native level. -/
def unifiedRefersToOutput (source output : UnifiedState) : Prop :=
  output.1 = source.1 ∧
    output.2.1 = source.2.1 ∧
    output.2.2 = source.2.2 + 1

structure UnifiedInternalExpr where
  pred : UnifiedState → Prop
  computable : ComputablePred pred

def unifiedDen (e : UnifiedInternalExpr) (x : UnifiedState) : Prop :=
  e.pred x

theorem lane_true_property_computable :
    ComputablePred (fun x : UnifiedState => x.2.1 = true) := by
  unfold ComputablePred
  refine ⟨inferInstance, ?_⟩
  have hproj : Computable (fun x : UnifiedState => x.2.1) := by
    exact Computable.fst.comp Computable.snd
  simpa using hproj

def laneTrueExpr : UnifiedInternalExpr where
  pred := fun x => x.2.1 = true
  computable := lane_true_property_computable

theorem false_unified_property_computable :
    ComputablePred (fun _ : UnifiedState => False) := by
  unfold ComputablePred
  refine ⟨inferInstance, ?_⟩
  simpa using
    (Computable.const false :
      Computable (fun _ : UnifiedState => false))

theorem true_unified_property_computable :
    ComputablePred (fun _ : UnifiedState => True) := by
  unfold ComputablePred
  refine ⟨inferInstance, ?_⟩
  simpa using
    (Computable.const true :
      Computable (fun _ : UnifiedState => true))

def falseUnifiedExpr : UnifiedInternalExpr where
  pred := fun _ => False
  computable := false_unified_property_computable

def trueUnifiedExpr : UnifiedInternalExpr where
  pred := fun _ => True
  computable := true_unified_property_computable

@[reducible] noncomputable def unifiedSystemWithLanguage
    (L : Type)
    (denotation : L → UnifiedState → Prop)
    (falseExpr trueExpr : L) : System where
  X := UnifiedState
  K := Bool
  Site := Nat
  Origin := UnifiedState
  Language := L
  Possibility := Bool
  Observation := Seat
  step := unifiedStep
  bodyAt := unifiedBodyAt
  phase := unifiedPhase
  mapId := unifiedMapId
  requiredSteps := unifiedRequired
  performedSteps := unifiedPerformed
  history := unifiedHistory
  encounterId := unifiedEncounterId
  availableSeed := unifiedAvailableSeed
  linkedTo := unifiedLinkedTo
  continuation := unifiedContinuation
  realised := unifiedRealised
  encounterSite := unifiedEncounterSite
  coherent := unifiedCoherent
  transport := unifiedTransport
  originAt := unifiedOriginAt
  interp := TuringChamberB1NativeGlobalReachability.finiteInterp
  finuniversal :=
    TuringChamberB1NativeGlobalReachability.finiteInterp_finiteUniversal
  observe := unifiedObserve
  den := denotation
  Prf := fun e => ∀ x, denotation e x
  falsum := falseExpr
  con := trueExpr
  refersToOutput := unifiedRefersToOutput
  outputStep := unifiedStep
  possible := unifiedPossible
  revealed := unifiedRevealed
  relation := unifiedRelation
  recognises := fun body state => body = unifiedBodyAt state
  usableBy := fun body state => body = unifiedBodyAt state

@[reducible] noncomputable def chamber12411 : System :=
  unifiedSystemWithLanguage
    UnifiedInternalExpr unifiedDen falseUnifiedExpr trueUnifiedExpr

def unifiedStart : UnifiedState :=
  (climbProblem, start124)

theorem unified_native_step (s : UnifiedState) :
    hstep climber (laneToLive s.2).state =
      some (laneToLive (laneStep s.2)).state :=
  lane_native_step s.2

theorem unified_iterate :
    ∀ n (s : UnifiedState),
      (unifiedStep^[n]) s = (s.1, (laneStep^[n]) s.2) := by
  intro n
  induction n with
  | zero =>
      intro s
      rfl
  | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply']
      rw [ih]
      simp [unifiedStep, Function.iterate_succ_apply']

/-! ### B1 survives on the stronger carrier -/

def unifiedEscapeLevel
    (s : Finset (UnifiedState × UnifiedState)) : Nat :=
  s.sup (fun pair : UnifiedState × UnifiedState => pair.2.2.2) + 1

theorem unified_start_reaches_level (k : Nat) :
    Reachable chamber12411 unifiedStart (climbProblem, (false, k)) := by
  refine ⟨k, ?_⟩
  change (unifiedStep^[k]) unifiedStart = (climbProblem, (false, k))
  rw [unified_iterate, lane_iterate]
  simp [unifiedStart, start124]

theorem unified_start_escape_not_mem
    (s : Finset (UnifiedState × UnifiedState)) :
    (unifiedStart, (climbProblem, (false, unifiedEscapeLevel s))) ∉ s := by
  intro hmem
  have hle :
      unifiedEscapeLevel s ≤
        s.sup (fun pair : UnifiedState × UnifiedState => pair.2.2.2) := by
    simpa [unifiedStart] using
      (Finset.le_sup
        (s := s)
        (f := fun pair : UnifiedState × UnifiedState => pair.2.2.2)
        hmem)
  unfold unifiedEscapeLevel at hle
  omega

theorem chamber12411_satisfies_B1 :
    canonicalB1 chamber12411 := by
  rintro ⟨table, htable⟩
  change
    (∀ x y : UnifiedState,
      TuringChamberB1NativeGlobalReachability.finiteInterp table x y = true ↔
        ∃ n : Nat, (unifiedStep^[n]) x = y) at htable
  let s : Finset (UnifiedState × UnifiedState) :=
    TuringChamberB1NativeGlobalReachability.decodedRelation table
  let y : UnifiedState :=
    (climbProblem, (false, unifiedEscapeLevel s))
  have hyreach :
      ∃ n : Nat, (unifiedStep^[n]) unifiedStart = y := by
    change Reachable chamber12411 unifiedStart y
    simpa [y] using unified_start_reaches_level (unifiedEscapeLevel s)
  have htrue :
      TuringChamberB1NativeGlobalReachability.finiteInterp
        table unifiedStart y = true :=
    (htable unifiedStart y).2 hyreach
  have hmem : (unifiedStart, y) ∈ s := by
    simpa [TuringChamberB1NativeGlobalReachability.finiteInterp, s] using htrue
  exact (unified_start_escape_not_mem s) (by simpa [y] using hmem)

/-! ### B2 survives -/

theorem unified_orbit_injective :
    Function.Injective
      (fun n : Nat => (unifiedStep^[n]) unifiedStart) := by
  intro i j h
  have hlane := congrArg (fun z : UnifiedState => z.2) h
  have hlane' :
      (laneStep^[i]) start124 = (laneStep^[j]) start124 := by
    simpa [unified_iterate, unifiedStart] using hlane
  exact start124_orbit_injective hlane'

theorem unified_observation_nonconstant :
    ∃ i j : Nat,
      unifiedObserve ((unifiedStep^[i]) unifiedStart) ≠
        unifiedObserve ((unifiedStep^[j]) unifiedStart) := by
  refine ⟨0, 1, ?_⟩
  native_decide

theorem unified_observation_recurs_arbitrarily_late :
    ∀ cutoff : Nat, ∃ later : Nat,
      cutoff < later ∧
        unifiedObserve ((unifiedStep^[later]) unifiedStart) =
          unifiedObserve unifiedStart := by
  intro cutoff
  obtain ⟨later, hlater, hobs⟩ :=
    start124_observation_recurs_arbitrarily_late cutoff
  refine ⟨later, hlater, ?_⟩
  simpa [unifiedObserve, unifiedStart, unified_iterate] using hobs

theorem chamber12411_satisfies_B2 :
    canonicalB2 chamber12411 := by
  refine ⟨unifiedStart, ?_, ?_, ?_⟩
  · change Function.Injective
      (fun n : Nat => (unifiedStep^[n]) unifiedStart)
    exact unified_orbit_injective
  · exact unified_observation_nonconstant
  · exact unified_observation_recurs_arbitrarily_late

/-! ### B4 survives without defining relation from co-recurrence -/

theorem unified_corecurrent_implies_relation
    {x y : UnifiedState}
    (h : CoRecurrent chamber12411 x y) :
    unifiedRelation x y := by
  change ∃ n m : Nat,
    (unifiedStep^[n]) x = (unifiedStep^[m]) y at h
  rcases h with ⟨n, m, hmeet⟩
  rw [unified_iterate, unified_iterate] at hmeet
  have hproblem : x.1 = y.1 := by
    simpa using
      congrArg (fun z : UnifiedState => z.1) hmeet
  have hlaneMeet :
      (laneStep^[n]) x.2 = (laneStep^[m]) y.2 := by
    simpa using
      congrArg (fun z : UnifiedState => z.2) hmeet
  have hlane : sameLane x.2 y.2 :=
    co_recurrent_implies_sameLane ⟨n, m, hlaneMeet⟩
  exact ⟨hproblem, hlane⟩

theorem unified_relation_implies_corecurrent
    {x y : UnifiedState}
    (h : unifiedRelation x y) :
    CoRecurrent chamber12411 x y := by
  have hlane : CoRecurrent chamber124 x.2 y.2 :=
    sameLane_implies_co_recurrent h.2
  rcases hlane with ⟨n, m, hmeet⟩
  refine ⟨n, m, ?_⟩
  rw [unified_iterate, unified_iterate]
  exact Prod.ext h.1 hmeet

theorem chamber12411_satisfies_B4 :
    canonicalB4 chamber12411 := by
  intro x y
  constructor
  · exact unified_relation_implies_corecurrent
  · exact unified_corecurrent_implies_relation

/-! ### B6 and B9 survive -/

theorem unifiedStep_changes_state (s : UnifiedState) :
    unifiedStep s ≠ s := by
  intro h
  have hlane := congrArg (fun z : UnifiedState => z.2) h
  exact laneStep_changes_state s.2 hlane

theorem unified_body_identity_preserved (s : UnifiedState) :
    chamber12411.bodyAt (chamber12411.step s) =
      chamber12411.bodyAt s := by
  rfl

theorem unified_relation_step_invariant (x y : UnifiedState) :
    chamber12411.relation (chamber12411.step x) (chamber12411.step y) ↔
      chamber12411.relation x y := by
  change unifiedRelation (unifiedStep x) (unifiedStep y) ↔
    unifiedRelation x y
  simp [unifiedRelation, unifiedStep, sameLane, laneStep]

theorem chamber12411_satisfies_B9 :
    canonicalB9 chamber12411 := by
  constructor
  · intro s
    exact ⟨unifiedStep_changes_state s,
      unified_body_identity_preserved s⟩
  · exact unified_relation_step_invariant

theorem unified_doing_requirements_covered
    (s : UnifiedState)
    (hdoing : chamber12411.phase s = .doing) :
    EpisodeRequirementsCovered chamber12411 s := by
  change episodePhase s.2 = .doing at hdoing
  change
    [()] ≠ [] ∧
      [()].Nodup ∧
      ∀ requirement,
        requirement ∈ [()] →
          requirement ∈
            (if episodePhase s.2 = .doing then [()] else [])
  simp [hdoing]

theorem unifiedStep_retains_history (s : UnifiedState) :
    RetainsHistory chamber12411 s (unifiedStep s) := by
  intro origin horigin
  change origin ∈ history124 s.2 at horigin
  change origin ∈ history124 (laneStep s.2)
  exact laneStep_retains_history s.2 origin horigin

theorem unified_encounter_enters_next_history (s : UnifiedState) :
    chamber12411.encounterId s ∈
      chamber12411.history (chamber12411.step s) := by
  exact encounter_enters_next_history s.2

theorem unified_start_earned_completion :
    EarnedCompletionTransition
      chamber12411 unifiedStart (unifiedStep unifiedStart) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact unifiedStep_changes_state unifiedStart h.symm
  · change episodePhase start124 = .doing
    simp [episodePhase, start124]
  · change episodePhase (laneStep start124) = .done
    simp [episodePhase, laneStep, start124]
  · change mapId124 (laneStep start124) = mapId124 start124
    norm_num [mapId124, laneStep, start124]
  · rfl
  · exact unified_doing_requirements_covered unifiedStart (by
      change episodePhase start124 = .doing
      simp [episodePhase, start124])
  · exact unified_encounter_enters_next_history unifiedStart
  · exact unifiedStep_retains_history unifiedStart

theorem chamber12411_satisfies_B6 :
    canonicalB6 chamber12411 := by
  constructor
  · exact ⟨unifiedStart, unifiedStep unifiedStart,
      unified_start_earned_completion⟩
  · intro before hdoing _hdone
    exact unified_doing_requirements_covered before hdoing

/-! ### B8 survives with problem provenance included in origin -/

def unifiedB8Source : UnifiedState :=
  (climbProblem, b8Source)

def unifiedB8Destination : UnifiedState :=
  (climbProblem, b8Destination)

theorem chamber12411_satisfies_B8 :
    canonicalB8 chamber12411 := by
  constructor
  · refine ⟨unifiedB8Source, unifiedB8Destination, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num [unifiedEncounterSite, unifiedB8Source,
        unifiedB8Destination, b8Source, b8Destination]
    · rfl
    · rfl
    · rfl
    · rfl
  · intro source destination htransport
    exact htransport

def unifiedForgedTransport
    (source destination : UnifiedState) : UnifiedState :=
  (source.1, (false, destination.2.2))

@[reducible] noncomputable def forgedUnifiedB8System : System :=
  { chamber12411 with transport := unifiedForgedTransport }

theorem forged_unified_transport_manufactures_coherence :
    manufacturedCoherenceControl forgedUnifiedB8System := by
  refine ⟨(climbProblem, (true, 0)),
    (climbProblem, (false, 5)), ?_, ?_⟩
  · rfl
  · change ¬ (true = false)
    intro h
    cases h

theorem forged_unified_transport_fails_B8 :
    ¬ canonicalB8 forgedUnifiedB8System :=
  manufactured_coherence_control_rejects_B8
    forgedUnifiedB8System
    forged_unified_transport_manufactures_coherence

/-! ### B10 survives in the computable internal language -/

theorem unifiedStep_injective :
    Function.Injective unifiedStep := by
  intro x y h
  change (x.1, laneStep x.2) = (y.1, laneStep y.2) at h
  have hproblem : x.1 = y.1 := by
    simpa using
      congrArg (fun z : UnifiedState => z.1) h
  have hlaneStep : laneStep x.2 = laneStep y.2 := by
    simpa using
      congrArg (fun z : UnifiedState => z.2) h
  have hlane : x.2 = y.2 := laneStep_injective hlaneStep
  exact Prod.ext hproblem hlane

theorem unified_den_nontrivial :
    ∃ expression state,
      chamber12411.den expression state ∧
        ¬ (∀ other, chamber12411.den expression other) := by
  refine ⟨laneTrueExpr, (climbProblem, (true, 0)), ?_, ?_⟩
  · rfl
  · intro hall
    have hbad := hall (climbProblem, (false, 0))
    change false = true at hbad
    cases hbad

theorem unified_clock_reveals_next_observation :
    ∃ state observation,
      ¬ chamber12411.revealed state observation ∧
        chamber12411.revealed (chamber12411.step state) observation := by
  refine ⟨unifiedStart,
    unifiedObserve (unifiedStep unifiedStart), ?_, rfl⟩
  change ¬ (laneObserve start124 = laneObserve (laneStep start124))
  native_decide

theorem unified_possibilities_persist :
    ∀ state possibility,
      chamber12411.possible state possibility →
        chamber12411.possible (chamber12411.step state) possibility := by
  intro _state _possibility _h
  trivial

theorem unified_two_possibilities_remain :
    ∀ state, ∃ first second : Bool,
      first ≠ second ∧
      chamber12411.possible (chamber12411.step state) first ∧
      chamber12411.possible (chamber12411.step state) second := by
  intro _state
  refine ⟨false, true, ?_, trivial, trivial⟩
  intro h
  cases h

theorem chamber12411_satisfies_B10 :
    canonicalB10 chamber12411 := by
  exact ⟨unifiedStep_injective,
    unified_den_nontrivial,
    unified_clock_reveals_next_observation,
    unified_possibilities_persist,
    unified_two_possibilities_remain⟩

def unifiedDeletingPossible
    (state : UnifiedState) (possibility : Bool) : Prop :=
  deletingPossible124 state.2 possibility

@[reducible] noncomputable def deletingUnifiedPossibilitySystem : System :=
  { chamber12411 with possible := unifiedDeletingPossible }

theorem unified_deleting_possibility_control :
    possibilityDeletionControl deletingUnifiedPossibilitySystem := by
  refine ⟨(climbProblem, (false, 0)), false, ?_, ?_⟩
  · change deletingPossible124 (false, 0) false
    simp [deletingPossible124]
  · change ¬ deletingPossible124 (laneStep (false, 0)) false
    simp [deletingPossible124, laneStep]

theorem deleting_unified_possibility_fails_B10 :
    ¬ canonicalB10 deletingUnifiedPossibilitySystem :=
  possibility_deletion_control_rejects_B10
    deletingUnifiedPossibilitySystem
    unified_deleting_possibility_control

/-! ### B12 survives -/

theorem unified_done_step_available
    (completed : UnifiedState)
    (hdone : chamber12411.phase completed = .done) :
    AvailableLinkedSeed chamber12411 completed (unifiedStep completed) := by
  change episodePhase completed.2 = .done at hdone
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change unifiedAvailableSeed completed (unifiedStep completed)
    exact ⟨rfl, ⟨hdone, rfl⟩⟩
  · change unifiedLinkedTo completed (unifiedStep completed)
    exact ⟨rfl, done_step_linked completed.2⟩
  · change mapId124 (laneStep completed.2) ≠ mapId124 completed.2
    exact done_step_map_changes completed.2 hdone
  · change episodePhase (laneStep completed.2) = .doing
    exact done_step_phase_doing completed.2 hdone
  · exact unified_encounter_enters_next_history completed
  · exact unifiedStep_retains_history completed

theorem unified_done_has_linked_seed
    (completed : UnifiedState)
    (hdone : chamber12411.phase completed = .done) :
    ∃ seed, AvailableLinkedSeed chamber12411 completed seed :=
  ⟨unifiedStep completed, unified_done_step_available completed hdone⟩

theorem unified_one_step_reachable (s : UnifiedState) :
    Reachable chamber12411 s (unifiedStep s) := by
  exact ⟨1, rfl⟩

theorem unified_native_successor_realised (s : UnifiedState) :
    chamber12411.realised s := by
  exact lane_native_step s.2

theorem unified_continuation_characterisation
    (completed later : UnifiedState) :
    chamber12411.continuation completed later ↔
      RealisedLinkedContinuation chamber12411 completed later := by
  constructor
  · intro hcont
    change unifiedAvailableSeed completed later at hcont
    rcases hcont with ⟨hproblem, hlane⟩
    rcases hlane with ⟨hdone, hlater⟩
    have hlaterEq : later = unifiedStep completed := by
      apply Prod.ext
      · simpa [unifiedStep] using hproblem.symm
      · simpa [unifiedStep] using hlater
    subst later
    refine ⟨unified_done_step_available completed ?_, ?_, ?_⟩
    · change episodePhase completed.2 = .done
      exact hdone
    · exact unified_native_successor_realised (unifiedStep completed)
    · exact unified_one_step_reachable completed
  · intro hreal
    exact hreal.1.1

theorem chamber12411_satisfies_B12 :
    canonicalB12 chamber12411 := by
  exact ⟨unified_done_has_linked_seed,
    unified_continuation_characterisation⟩

/-! ### B11: genuine global Chamber halting invariant -/

def unifiedHelixInvariant (s : UnifiedState) : Prop :=
  HelixHalts s.1

theorem unifiedHelixInvariant_preserved :
    ∀ x, unifiedHelixInvariant x →
      unifiedHelixInvariant (unifiedStep x) := by
  intro x hx
  exact hx

def embedUnifiedProblem (q : Problem) : UnifiedState :=
  (q, start124)

theorem embedUnifiedProblem_computable :
    Computable embedUnifiedProblem := by
  unfold embedUnifiedProblem
  exact Computable.id.pair (Computable.const start124)

theorem helix_to_unified_invariant_is_effective :
    HelixHalts ≤₀ unifiedHelixInvariant := by
  exact ⟨embedUnifiedProblem, embedUnifiedProblem_computable,
    fun _ => Iff.rfl⟩

theorem unifiedHelixInvariant_not_computable :
    ¬ ComputablePred unifiedHelixInvariant := by
  intro h
  exact helix_halting_is_not_computable
    (ComputablePred.computable_of_manyOneReducible
      helix_to_unified_invariant_is_effective h)

theorem unifiedHelixInvariant_not_false :
    unifiedHelixInvariant ≠ (fun _ => False) := by
  intro h
  apply unifiedHelixInvariant_not_computable
  rw [h]
  exact false_unified_property_computable

theorem unifiedHelixInvariant_not_true :
    unifiedHelixInvariant ≠ (fun _ => True) := by
  intro h
  apply unifiedHelixInvariant_not_computable
  rw [h]
  exact true_unified_property_computable

theorem no_unified_internal_expression_names_halting :
    ¬ (∃ expression : UnifiedInternalExpr,
      Denotes chamber12411 expression unifiedHelixInvariant) := by
  rintro ⟨expression, hden⟩
  have heq : expression.pred = unifiedHelixInvariant := by
    funext x
    apply propext
    exact hden x
  apply unifiedHelixInvariant_not_computable
  rw [← heq]
  exact expression.computable

theorem chamber12411_satisfies_B11 :
    canonicalB11 chamber12411 := by
  refine ⟨unifiedHelixInvariant, ?_, ?_, ?_, ?_⟩
  · exact unifiedHelixInvariant_preserved
  · exact unifiedHelixInvariant_not_false
  · exact unifiedHelixInvariant_not_true
  · exact no_unified_internal_expression_names_halting

@[reducible] noncomputable def unrestrictedUnifiedSystem : System :=
  unifiedSystemWithLanguage
    (UnifiedState → Prop)
    (fun P x => P x)
    (fun _ => False)
    (fun _ => True)

theorem unrestricted_unified_language_names_every_property
    (I : UnifiedState → Prop) :
    ∃ expression : unrestrictedUnifiedSystem.Language,
      Denotes unrestrictedUnifiedSystem expression I := by
  exact ⟨I, fun _ => Iff.rfl⟩

theorem unrestricted_unified_language_fails_B11 :
    ¬ canonicalB11 unrestrictedUnifiedSystem := by
  rintro ⟨I, _hinvariant, _hnonfalse, _hnontrue, hunnamed⟩
  exact hunnamed
    (unrestricted_unified_language_names_every_property I)

/-! ### B7: output-reference, consistency, and diagonal derangement -/

theorem chamber12411_semantic_proof_sound
    (e : UnifiedInternalExpr)
    (h : chamber12411.Prf e) :
    ∀ x, chamber12411.den e x := by
  exact h

theorem chamber12411_consistent :
    Consistent chamber12411 := by
  intro hfalse
  have h := hfalse unifiedStart
  exact h

theorem unified_step_refers_to_output
    (x : UnifiedState) :
    chamber12411.refersToOutput x (chamber12411.outputStep x) := by
  change unifiedRefersToOutput x (unifiedStep x)
  rcases x with ⟨problem, lane, level⟩
  exact ⟨rfl, rfl, rfl⟩

theorem unified_output_step_has_no_fixed_point
    (x : UnifiedState) :
    chamber12411.outputStep x ≠ x := by
  exact unifiedStep_changes_state x

theorem unified_output_step_is_diagonal_operator
    (e : UnifiedState → UnifiedState → UnifiedState) :
    ¬ FoundationStone.CompleteListing e := by
  exact FoundationStone.diagonal
    unifiedStep unifiedStep_changes_state e

theorem chamber12411_satisfies_B7 :
    canonicalB7 chamber12411 := by
  exact ⟨⟨unifiedStart⟩,
    chamber12411_consistent,
    unified_step_refers_to_output,
    unified_output_step_has_no_fixed_point⟩

@[reducible] noncomputable def extensionalUnifiedB7System : System :=
  { chamber12411 with
      outputStep := fun x => x }

theorem extensional_unified_B7_control :
    extensionalSelfReferenceControl extensionalUnifiedB7System := by
  intro x
  rfl

theorem extensional_unified_system_fails_B7 :
    ¬ canonicalB7 extensionalUnifiedB7System :=
  extensional_self_reference_control_rejects_B7
    extensionalUnifiedB7System
    extensional_unified_B7_control

/-! ### Ten-way unified certificate -/

theorem B12468101112_one_native_system_certificate :
    (∀ s : UnifiedState,
      hstep climber (laneToLive s.2).state =
        some (laneToLive (laneStep s.2)).state) ∧
    canonicalB1 chamber12411 ∧
    canonicalB2 chamber12411 ∧
    canonicalB4 chamber12411 ∧
    canonicalB6 chamber12411 ∧
    canonicalB8 chamber12411 ∧
    canonicalB9 chamber12411 ∧
    canonicalB10 chamber12411 ∧
    canonicalB11 chamber12411 ∧
    canonicalB12 chamber12411 ∧
    ¬ canonicalB8 forgedUnifiedB8System ∧
    ¬ canonicalB10 deletingUnifiedPossibilitySystem ∧
    ¬ canonicalB11 unrestrictedUnifiedSystem := by
  exact ⟨unified_native_step,
    chamber12411_satisfies_B1,
    chamber12411_satisfies_B2,
    chamber12411_satisfies_B4,
    chamber12411_satisfies_B6,
    chamber12411_satisfies_B8,
    chamber12411_satisfies_B9,
    chamber12411_satisfies_B10,
    chamber12411_satisfies_B11,
    chamber12411_satisfies_B12,
    forged_unified_transport_fails_B8,
    deleting_unified_possibility_fails_B10,
    unrestricted_unified_language_fails_B11⟩

theorem B1246789101112_one_native_system_certificate :
    (∀ s : UnifiedState,
      hstep climber (laneToLive s.2).state =
        some (laneToLive (laneStep s.2)).state) ∧
    canonicalB1 chamber12411 ∧
    canonicalB2 chamber12411 ∧
    canonicalB4 chamber12411 ∧
    canonicalB6 chamber12411 ∧
    canonicalB7 chamber12411 ∧
    canonicalB8 chamber12411 ∧
    canonicalB9 chamber12411 ∧
    canonicalB10 chamber12411 ∧
    canonicalB11 chamber12411 ∧
    canonicalB12 chamber12411 ∧
    ¬ canonicalB7 extensionalUnifiedB7System ∧
    ¬ canonicalB8 forgedUnifiedB8System ∧
    ¬ canonicalB10 deletingUnifiedPossibilitySystem ∧
    ¬ canonicalB11 unrestrictedUnifiedSystem := by
  exact ⟨unified_native_step,
    chamber12411_satisfies_B1,
    chamber12411_satisfies_B2,
    chamber12411_satisfies_B4,
    chamber12411_satisfies_B6,
    chamber12411_satisfies_B7,
    chamber12411_satisfies_B8,
    chamber12411_satisfies_B9,
    chamber12411_satisfies_B10,
    chamber12411_satisfies_B11,
    chamber12411_satisfies_B12,
    extensional_unified_system_fails_B7,
    forged_unified_transport_fails_B8,
    deleting_unified_possibility_fails_B10,
    unrestricted_unified_language_fails_B11⟩

#print axioms chamber12411_satisfies_B1
#print axioms chamber12411_satisfies_B2
#print axioms chamber12411_satisfies_B4
#print axioms chamber12411_satisfies_B6
#print axioms chamber12411_satisfies_B7
#print axioms chamber12411_satisfies_B8
#print axioms chamber12411_satisfies_B9
#print axioms chamber12411_satisfies_B10
#print axioms chamber12411_satisfies_B11
#print axioms chamber12411_satisfies_B12
#print axioms unifiedHelixInvariant_not_computable
#print axioms unrestricted_unified_language_fails_B11
#print axioms unified_output_step_is_diagonal_operator
#print axioms extensional_unified_system_fails_B7
#print axioms B12468101112_one_native_system_certificate
#print axioms B1246789101112_one_native_system_certificate

end
end TuringChamberB124OneSystem
