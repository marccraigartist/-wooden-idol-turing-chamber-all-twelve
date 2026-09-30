import FoundationStoneTest16AF

/-!
# THE WOODEN IDOL × TURING CHAMBER — PHASE 2A

This file begins the shared-object construction without altering the certified
Turing Chamber kernel.  It adds an encounter/provenance frame around the exact
`FoundationStoneTest16AF.HState`, supplies an explicit forgetting map, and
proves that a framed kernel step projects to the native 16AF helix step.

The frame is deliberately not claimed to satisfy B1–B12.  Its first job is to
make the Gate 2 removal test precise: machine execution survives forgetting,
while honest source provenance does not.
-/

namespace WoodenIdolTuringBridgePhase2

open FoundationStoneTest16AF

inductive RunStatus where
  | running
  | halted
deriving DecidableEq, Repr

def observedStatus (p : Program) (h : HState) : RunStatus :=
  match hstep p h with
  | some _ => .running
  | none => .halted

inductive Direction where
  | inward
  | outward
deriving DecidableEq, Repr

inductive BodyRole where
  | maker
  | receiver
deriving DecidableEq, Repr

structure RouteMark where
  source : Nat
  station : Seat
deriving DecidableEq, Repr

structure EncounterFrame where
  station : Seat
  direction : Direction
  roleA : BodyRole
  roleB : BodyRole
  source : Nat
  route : List RouteMark
deriving DecidableEq, Repr

/-- Every retained route mark names the actual source, and the final mark names
the current station. -/
structure RouteHonest (f : EncounterFrame) : Prop where
  nonempty : f.route ≠ []
  sources : ∀ m ∈ f.route, m.source = f.source
  endsAt : f.route.getLast? = some ⟨f.source, f.station⟩

/-- The first shared state uses the native 16AF helix state unchanged. -/
structure ChamberState (p : Program) where
  core : HState
  frame : EncounterFrame
  status : RunStatus
  status_exact : status = observedStatus p core
  route_honest : RouteHonest frame

/-- Erasing the encounter layer recovers exactly the certified helix state. -/
def forgetFrame {p : Program} (s : ChamberState p) : HState := s.core

theorem status_halted_iff {p : Program} (s : ChamberState p) :
    s.status = .halted ↔ hstep p (forgetFrame s) = none := by
  rw [s.status_exact]
  unfold observedStatus forgetFrame
  cases h : hstep p s.core <;> simp

/-- A kernel step changes only the native helix state.  Encounter boundaries
are represented separately rather than forcing twelve stations onto opcodes. -/
def KernelStep (p : Program) (s t : ChamberState p) : Prop :=
  hstep p s.core = some t.core ∧ t.frame = s.frame

theorem forget_kernel_step {p : Program} {s t : ChamberState p}
    (h : KernelStep p s t) :
    hstep p (forgetFrame s) = some (forgetFrame t) := h.1

theorem kernel_step_preserves_source {p : Program} {s t : ChamberState p}
    (h : KernelStep p s t) :
    t.frame.source = s.frame.source := by
  rw [h.2]

/-! ## A first typed encounter boundary: B6 completion to B9 release -/

def B6 : Seat := ⟨5, by decide⟩
def B9 : Seat := ⟨8, by decide⟩

def releaseMark (f : EncounterFrame) : RouteMark := ⟨f.source, B9⟩

def releaseFrame (f : EncounterFrame) : EncounterFrame :=
  { f with
    station := B9
    direction := .outward
    route := f.route ++ [releaseMark f] }

theorem releaseFrame_honest {f : EncounterFrame} (h : RouteHonest f) :
    RouteHonest (releaseFrame f) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [releaseFrame]
  · intro m hm
    simp only [releaseFrame, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h.sources m hm
    · rfl
  · simp [releaseFrame, releaseMark]

def release {p : Program} (s : ChamberState p) : ChamberState p where
  core := s.core
  frame := releaseFrame s.frame
  status := s.status
  status_exact := s.status_exact
  route_honest := releaseFrame_honest s.route_honest

/-- `Released` is an episode boundary, not a native counter instruction. -/
def Released {p : Program} (s t : ChamberState p) : Prop :=
  s.frame.station = B6 ∧ t = release s

theorem released_forgets_to_same_core {p : Program} {s t : ChamberState p}
    (h : Released s t) :
    forgetFrame t = forgetFrame s := by
  rcases h with ⟨_, rfl⟩
  rfl

theorem released_result_retains_source {p : Program} {s t : ChamberState p}
    (h : Released s t) :
    t.frame.source = s.frame.source := by
  rcases h with ⟨_, rfl⟩
  rfl

/-! ## Gate 2 red control: forge provenance without changing the machine -/

abbrev RawChamberState := HState × EncounterFrame

def rawForget (s : RawChamberState) : HState := s.1

def forgeFrame (f : EncounterFrame) (falseSource : Nat) : EncounterFrame :=
  { f with source := falseSource }

def forgeSource (s : RawChamberState) (falseSource : Nat) : RawChamberState :=
  (s.1, forgeFrame s.2 falseSource)

theorem forged_source_preserves_machine
    (s : RawChamberState) (falseSource : Nat) :
    rawForget (forgeSource s falseSource) = rawForget s := rfl

/-- A forged source survives machine erasure but cannot satisfy route honesty. -/
theorem forged_release_is_not_honest (f : EncounterFrame) (falseSource : Nat)
    (hne : falseSource ≠ f.source) :
    ¬ RouteHonest (forgeFrame (releaseFrame f) falseSource) := by
  intro h
  have hs : f.source = falseSource := by
    simpa [forgeFrame, releaseFrame, releaseMark] using h.endsAt
  exact hne hs.symm

theorem phase2A_gate_certificate :
    (∀ (p : Program) (s t : ChamberState p), KernelStep p s t →
      hstep p (forgetFrame s) = some (forgetFrame t)) ∧
    (∀ (p : Program) (s t : ChamberState p), Released s t →
      forgetFrame t = forgetFrame s ∧ t.frame.source = s.frame.source) ∧
    (∀ (s : RawChamberState) (falseSource : Nat),
      rawForget (forgeSource s falseSource) = rawForget s) := by
  exact ⟨fun _ _ _ => forget_kernel_step,
    fun _ _ _ h => ⟨released_forgets_to_same_core h, released_result_retains_source h⟩,
    forged_source_preserves_machine⟩

#print axioms forget_kernel_step
#print axioms released_result_retains_source
#print axioms forged_release_is_not_honest
#print axioms phase2A_gate_certificate

end WoodenIdolTuringBridgePhase2
