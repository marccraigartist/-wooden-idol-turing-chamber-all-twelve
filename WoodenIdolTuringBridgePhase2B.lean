import WoodenIdolTuringBridgePhase2

/-!
# THE WOODEN IDOL × TURING CHAMBER — PHASE 2B

Phase 2A attached an honest provenance frame to the unchanged 16AF helix kernel
and certified the first completion-to-release boundary.  This file types the
other three boundaries and composes all four into one complete breath:

    B12 → B3 → B6 → B9 → B12.

The computation occurs only on B3 → B6 and is witnessed by native `16AF.hrun`.
B12 → B3 admits an external linked seed; B6 → B9 releases the completed state;
B9 → B12 makes its two body heights available as a later seed.  Thus external
continuation is not identified with internal machine non-halting.

No canonical B predicate is claimed in this file.
-/

namespace WoodenIdolTuringBridgePhase2B

open FoundationStoneTest16AF
open WoodenIdolTuringBridgePhase2

def B3 : Seat := ⟨2, by decide⟩
def B12 : Seat := ⟨11, by decide⟩

def advanceMark (f : EncounterFrame) (target : Seat) : RouteMark :=
  ⟨f.source, target⟩

def advanceFrame (f : EncounterFrame) (target : Seat)
    (direction : Direction) : EncounterFrame :=
  { f with
    station := target
    direction := direction
    route := f.route ++ [advanceMark f target] }

theorem advanceFrame_honest {f : EncounterFrame} (h : RouteHonest f)
    (target : Seat) (direction : Direction) :
    RouteHonest (advanceFrame f target direction) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [advanceFrame]
  · intro m hm
    simp only [advanceFrame, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h.sources m hm
    · rfl
  · simp [advanceFrame, advanceMark]

/-- Change the native core at an explicitly typed encounter boundary and
recompute its exact running/halting status. -/
def advanceState {p : Program} (s : ChamberState p) (core : HState)
    (target : Seat) (direction : Direction) : ChamberState p where
  core := core
  frame := advanceFrame s.frame target direction
  status := observedStatus p core
  status_exact := rfl
  route_honest := advanceFrame_honest s.route_honest target direction

structure LinkedSeed where
  source : Nat
  bodyA : Nat
  bodyB : Nat
deriving DecidableEq, Repr

def SeedHonest {p : Program} (c : ChamberState p) : Option LinkedSeed → Prop
  | none => True
  | some seed => seed.source = c.frame.source

structure BreathState (p : Program) where
  chamber : ChamberState p
  linked : Option LinkedSeed
  linked_honest : SeedHonest chamber linked

def seedStart (p : Program) (seed : LinkedSeed) : HState :=
  helixStart (p, (seed.bodyA, seed.bodyB))

def outputSeed {p : Program} (c : ChamberState p) : LinkedSeed :=
  ⟨c.frame.source, c.core.bodyA.height, c.core.bodyB.height⟩

def intakeState {p : Program} (s : BreathState p) (seed : LinkedSeed) :
    BreathState p where
  chamber := advanceState s.chamber (seedStart p seed) B3 .inward
  linked := none
  linked_honest := trivial

def completeState {p : Program} (s : BreathState p) (core : HState) :
    BreathState p where
  chamber := advanceState s.chamber core B6 .inward
  linked := none
  linked_honest := trivial

def releaseBreathState {p : Program} (s : BreathState p) : BreathState p where
  chamber := release s.chamber
  linked := none
  linked_honest := trivial

def receiveState {p : Program} (s : BreathState p) : BreathState p where
  chamber := advanceState s.chamber s.chamber.core B12 .outward
  linked := some (outputSeed s.chamber)
  linked_honest := by rfl

/-! ## The four typed boundaries -/

def Intake {p : Program} (s t : BreathState p) : Prop :=
  s.chamber.frame.station = B12 ∧
    ∃ seed, s.linked = some seed ∧ t = intakeState s seed

/-- Making is the only interval that runs the internal machine.  A completed
making interval ends at a genuine native halted core. -/
def Making {p : Program} (s t : BreathState p) : Prop :=
  s.chamber.frame.station = B3 ∧
    ∃ n core,
      hrun p n s.chamber.core = some core ∧
      hstep p core = none ∧
      t = completeState s core

def ReleaseBoundary {p : Program} (s t : BreathState p) : Prop :=
  s.chamber.frame.station = B6 ∧ t = releaseBreathState s

def Reception {p : Program} (s t : BreathState p) : Prop :=
  s.chamber.frame.station = B9 ∧ t = receiveState s

def Breath {p : Program} (start finish : BreathState p) : Prop :=
  ∃ atB3 atB6 atB9,
    Intake start atB3 ∧
    Making atB3 atB6 ∧
    ReleaseBoundary atB6 atB9 ∧
    Reception atB9 finish

/-! ## Boundary laws -/

theorem intake_retains_source {p : Program} {s t : BreathState p}
    (h : Intake s t) :
    t.chamber.frame.source = s.chamber.frame.source := by
  rcases h with ⟨_, seed, _, rfl⟩
  rfl

theorem making_retains_source {p : Program} {s t : BreathState p}
    (h : Making s t) :
    t.chamber.frame.source = s.chamber.frame.source := by
  rcases h with ⟨_, n, core, hrun, hhalt, rfl⟩
  rfl

theorem release_retains_source {p : Program} {s t : BreathState p}
    (h : ReleaseBoundary s t) :
    t.chamber.frame.source = s.chamber.frame.source := by
  rcases h with ⟨_, rfl⟩
  rfl

theorem reception_retains_source {p : Program} {s t : BreathState p}
    (h : Reception s t) :
    t.chamber.frame.source = s.chamber.frame.source := by
  rcases h with ⟨_, rfl⟩
  rfl

theorem making_projects_to_native_run {p : Program} {s t : BreathState p}
    (h : Making s t) :
    ∃ n,
      hrun p n s.chamber.core = some t.chamber.core ∧
      hstep p t.chamber.core = none := by
  rcases h with ⟨_, n, core, hrun, hhalt, rfl⟩
  exact ⟨n, hrun, hhalt⟩

theorem reception_exposes_linked_output {p : Program} {s t : BreathState p}
    (h : Reception s t) :
    t.linked = some (outputSeed s.chamber) := by
  rcases h with ⟨_, rfl⟩
  rfl

theorem breath_retains_source {p : Program} {start finish : BreathState p}
    (h : Breath start finish) :
    finish.chamber.frame.source = start.chamber.frame.source := by
  rcases h with ⟨atB3, atB6, atB9, hi, hm, hr, hc⟩
  calc
    finish.chamber.frame.source = atB9.chamber.frame.source :=
      reception_retains_source hc
    _ = atB6.chamber.frame.source := release_retains_source hr
    _ = atB3.chamber.frame.source := making_retains_source hm
    _ = start.chamber.frame.source := intake_retains_source hi

theorem breath_returns_to_B12 {p : Program} {start finish : BreathState p}
    (h : Breath start finish) :
    finish.chamber.frame.station = B12 := by
  rcases h with ⟨atB3, atB6, atB9, hi, hm, hr, hc⟩
  rcases hc with ⟨_, rfl⟩
  rfl

/-- A complete breath contains a genuine finite native computation ending at a
halted core.  The later release and reception do not counterfeit that run. -/
theorem breath_contains_native_completed_run {p : Program}
    {start finish : BreathState p} (h : Breath start finish) :
    ∃ atB3 atB6 n,
      Intake start atB3 ∧
      Making atB3 atB6 ∧
      hrun p n atB3.chamber.core = some atB6.chamber.core ∧
      hstep p atB6.chamber.core = none := by
  rcases h with ⟨atB3, atB6, atB9, hi, hm, hr, hc⟩
  obtain ⟨n, hrun, hhalt⟩ := making_projects_to_native_run hm
  exact ⟨atB3, atB6, n, hi, hm, hrun, hhalt⟩

/-- The next linked seed is formed only after the completed core was released;
its payload is the two released helix heights. -/
theorem breath_exposes_released_output {p : Program}
    {start finish : BreathState p} (h : Breath start finish) :
    ∃ atB6 atB9 : BreathState p,
      ReleaseBoundary atB6 atB9 ∧
      hstep p atB6.chamber.core = none ∧
      atB9.chamber.core = atB6.chamber.core ∧
      finish.linked = some (outputSeed atB9.chamber) := by
  rcases h with ⟨atB3, atB6, atB9, hi, hm, hr, hc⟩
  obtain ⟨n, hrun, hhalt⟩ := making_projects_to_native_run hm
  refine ⟨atB6, atB9, hr, hhalt, ?_, reception_exposes_linked_output hc⟩
  rcases hr with ⟨_, rfl⟩
  rfl

/-! ## Red control: an unrelated next seed -/

def forgeSeed (seed : LinkedSeed) (falseSource : Nat) : LinkedSeed :=
  { seed with source := falseSource }

abbrev RawBreathState (p : Program) := ChamberState p × Option LinkedSeed

def rawBreathForget {p : Program} (s : RawBreathState p) : HState :=
  s.1.core

def installForgedSeed {p : Program} (s : RawBreathState p)
    (seed : LinkedSeed) (falseSource : Nat) : RawBreathState p :=
  (s.1, some (forgeSeed seed falseSource))

theorem forged_seed_preserves_machine {p : Program} (s : RawBreathState p)
    (seed : LinkedSeed) (falseSource : Nat) :
    rawBreathForget (installForgedSeed s seed falseSource) = rawBreathForget s := rfl

theorem unrelated_seed_is_rejected {p : Program} (c : ChamberState p)
    (seed : LinkedSeed) (falseSource : Nat)
    (hne : falseSource ≠ c.frame.source) :
    ¬ SeedHonest c (some (forgeSeed seed falseSource)) := by
  simpa [SeedHonest, forgeSeed] using hne

theorem phase2B_breath_certificate :
    (∀ (p : Program) (start finish : BreathState p), Breath start finish →
      finish.chamber.frame.station = B12 ∧
      finish.chamber.frame.source = start.chamber.frame.source) ∧
    (∀ (p : Program) (start finish : BreathState p), Breath start finish →
      ∃ atB3 atB6 n,
        Intake start atB3 ∧
        Making atB3 atB6 ∧
        hrun p n atB3.chamber.core = some atB6.chamber.core ∧
        hstep p atB6.chamber.core = none) ∧
    (∀ (p : Program) (s : RawBreathState p) (seed : LinkedSeed)
      (falseSource : Nat),
      rawBreathForget (installForgedSeed s seed falseSource) = rawBreathForget s) := by
  exact ⟨fun _ _ _ h => ⟨breath_returns_to_B12 h, breath_retains_source h⟩,
    fun _ _ _ => breath_contains_native_completed_run,
    fun p s seed falseSource =>
      forged_seed_preserves_machine (p := p) s seed falseSource⟩

#print axioms making_projects_to_native_run
#print axioms breath_retains_source
#print axioms breath_contains_native_completed_run
#print axioms breath_exposes_released_output
#print axioms unrelated_seed_is_rejected
#print axioms phase2B_breath_certificate

end WoodenIdolTuringBridgePhase2B
