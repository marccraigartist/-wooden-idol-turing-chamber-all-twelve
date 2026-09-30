import WoodenIdolTuringBridgePhase2B

/-!
# THE WOODEN IDOL × TURING CHAMBER — PHASE 2C

Phase 2B constructed a complete breath around the unchanged 16AF helix:

    B12 → B3 → B6 → B9 → B12.

This file performs the remaining Gate 2 removal test.  It does not merely
observe that a station and a direction are stored in the frame.  It refines
the four boundaries with their required incoming directions and proves that
two valid framed states can have the same phase-blind machine view while only
one admits the next directed boundary.

Consequently both station and direction carry operational information.  The
result is deliberately architectural: it does not claim any canonical B
predicate and it does not alter the already certified Turing Chamber kernel.
-/

namespace WoodenIdolTuringBridgePhase2C

open FoundationStoneTest16AF
open WoodenIdolTuringBridgePhase2
open WoodenIdolTuringBridgePhase2B

/-! ## Directed boundary discipline -/

def DirectedIntake {p : Program} (s t : BreathState p) : Prop :=
  s.chamber.frame.direction = .outward ∧ Intake s t

def DirectedMaking {p : Program} (s t : BreathState p) : Prop :=
  s.chamber.frame.direction = .inward ∧ Making s t

def DirectedRelease {p : Program} (s t : BreathState p) : Prop :=
  s.chamber.frame.direction = .inward ∧ ReleaseBoundary s t

def DirectedReception {p : Program} (s t : BreathState p) : Prop :=
  s.chamber.frame.direction = .outward ∧ Reception s t

def DirectedBreath {p : Program} (start finish : BreathState p) : Prop :=
  ∃ atB3 atB6 atB9,
    DirectedIntake start atB3 ∧
    DirectedMaking atB3 atB6 ∧
    DirectedRelease atB6 atB9 ∧
    DirectedReception atB9 finish

theorem directedBreath_is_breath {p : Program} {start finish : BreathState p}
    (h : DirectedBreath start finish) : Breath start finish := by
  rcases h with ⟨atB3, atB6, atB9, ⟨_, hi⟩, ⟨_, hm⟩, ⟨_, hr⟩, ⟨_, hc⟩⟩
  exact ⟨atB3, atB6, atB9, hi, hm, hr, hc⟩

/-- The Phase 2B construction already installs the three internal directions.
Only the direction of the externally supplied starting state is an input. -/
theorem breath_is_directed_of_start_outward {p : Program}
    {start finish : BreathState p} (h : Breath start finish)
    (hout : start.chamber.frame.direction = .outward) :
    DirectedBreath start finish := by
  rcases h with ⟨atB3, atB6, atB9, hi, hm, hr, hc⟩
  have hB3 : atB3.chamber.frame.direction = .inward := by
    rcases hi with ⟨_, seed, _, rfl⟩
    rfl
  have hB6 : atB6.chamber.frame.direction = .inward := by
    rcases hm with ⟨_, n, core, hrun, hhalt, rfl⟩
    rfl
  have hB9 : atB9.chamber.frame.direction = .outward := by
    rcases hr with ⟨_, rfl⟩
    rfl
  exact ⟨atB3, atB6, atB9, ⟨hout, hi⟩, ⟨hB3, hm⟩,
    ⟨hB6, hr⟩, ⟨hB9, hc⟩⟩

/-! ## Valid comparison states and the phase-blind view -/

def frameAt (source : Nat) (station : Seat) (direction : Direction) :
    EncounterFrame where
  station := station
  direction := direction
  roleA := .maker
  roleB := .receiver
  source := source
  route := [⟨source, station⟩]

theorem frameAt_honest (source : Nat) (station : Seat) (direction : Direction) :
    RouteHonest (frameAt source station direction) := by
  refine ⟨by simp [frameAt], ?_, by simp [frameAt]⟩
  intro m hm
  simp only [frameAt, List.mem_singleton] at hm
  subst m
  rfl

def chamberAt (p : Program) (core : HState) (source : Nat)
    (station : Seat) (direction : Direction) : ChamberState p where
  core := core
  frame := frameAt source station direction
  status := observedStatus p core
  status_exact := rfl
  route_honest := frameAt_honest source station direction

def breathAt (p : Program) (core : HState) (station : Seat)
    (direction : Direction) (seed : LinkedSeed) : BreathState p where
  chamber := chamberAt p core seed.source station direction
  linked := some seed
  linked_honest := by rfl

/-- What remains after erasing station, direction, roles and route while
retaining the native machine, the source identifier and the linked payload. -/
structure PhaseBlindState where
  core : HState
  source : Nat
  linked : Option LinkedSeed
deriving DecidableEq, Repr

def forgetPhase {p : Program} (s : BreathState p) : PhaseBlindState :=
  ⟨s.chamber.core, s.chamber.frame.source, s.linked⟩

/-! ## Red controls: station and direction cannot be erased -/

/-- Two honest states with the same phase-blind view disagree about whether
directed intake is enabled solely because their stations differ. -/
theorem station_erasure_loses_enabled_boundary (p : Program) (core : HState)
    (seed : LinkedSeed) :
    let ready := breathAt p core B12 .outward seed
    let wrong := breathAt p core B3 .outward seed
    forgetPhase ready = forgetPhase wrong ∧
      (∃ next, DirectedIntake ready next) ∧
      ¬ ∃ next, DirectedIntake wrong next := by
  dsimp
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨intakeState (breathAt p core B12 .outward seed) seed,
      rfl, rfl, seed, rfl, rfl⟩
  · rintro ⟨next, _, hintake⟩
    have hne : B3 ≠ B12 := by decide
    apply hne
    simpa [breathAt, chamberAt, frameAt] using hintake.1

/-- Even at the same station, two honest states with the same phase-blind view
disagree about whether directed intake is enabled solely because their
directions differ. -/
theorem direction_erasure_loses_enabled_boundary (p : Program) (core : HState)
    (seed : LinkedSeed) :
    let ready := breathAt p core B12 .outward seed
    let wrong := breathAt p core B12 .inward seed
    forgetPhase ready = forgetPhase wrong ∧
      (∃ next, DirectedIntake ready next) ∧
      ¬ ∃ next, DirectedIntake wrong next := by
  dsimp
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨intakeState (breathAt p core B12 .outward seed) seed,
      rfl, rfl, seed, rfl, rfl⟩
  · rintro ⟨next, hdirection, _⟩
    have hne : Direction.inward ≠ Direction.outward := by decide
    apply hne
    simpa [breathAt, chamberAt, frameAt] using hdirection

/-- Gate 2 closes at the shared-object level: native execution is recovered by
forgetting the frame (Phase 2A), provenance is lost by that erasure (2A/2B),
and erasing either station or direction loses boundary enablement (this file).
-/
theorem phase2C_irreducibility_certificate :
    (∀ (p : Program) (start finish : BreathState p),
      DirectedBreath start finish → Breath start finish) ∧
    (∀ (p : Program) (start finish : BreathState p),
      Breath start finish →
      start.chamber.frame.direction = .outward →
      DirectedBreath start finish) ∧
    (∀ (p : Program) (core : HState) (seed : LinkedSeed),
      let ready := breathAt p core B12 .outward seed
      let wrongStation := breathAt p core B3 .outward seed
      let wrongDirection := breathAt p core B12 .inward seed
      forgetPhase ready = forgetPhase wrongStation ∧
      forgetPhase ready = forgetPhase wrongDirection ∧
      (∃ next, DirectedIntake ready next) ∧
      (¬ ∃ next, DirectedIntake wrongStation next) ∧
      (¬ ∃ next, DirectedIntake wrongDirection next)) := by
  refine ⟨fun _ _ _ => directedBreath_is_breath,
    fun _ _ _ => breath_is_directed_of_start_outward, ?_⟩
  intro p core seed
  have hs := station_erasure_loses_enabled_boundary p core seed
  have hd := direction_erasure_loses_enabled_boundary p core seed
  dsimp at hs hd ⊢
  exact ⟨hs.1, hd.1, hs.2.1, hs.2.2, hd.2.2⟩

#print axioms directedBreath_is_breath
#print axioms breath_is_directed_of_start_outward
#print axioms station_erasure_loses_enabled_boundary
#print axioms direction_erasure_loses_enabled_boundary
#print axioms phase2C_irreducibility_certificate

end WoodenIdolTuringBridgePhase2C
