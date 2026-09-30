import WoodenIdolTuringBridgeB12

/-!
# THE WOODEN IDOL × TURING CHAMBER — K31 B12 SLICE

This module uses a reduced record containing the fields used by K31 B12.
Its formulae follow:
`lean/checkpoints/step11/Stage3KSpike31.lean`
at Stage 3 commit:
`66bce34c4b90865682bed5e8e4b63f6b2a9952f5`.

The connection between this reduced record and the original Stage3.System
remains a separate verification obligation. Successful compilation of this
module alone does not close the full canonical K31 bridge.

The Chamber continuation is DirectedIntake. Its relationship to linked,
realised, reachable continuation is proved below.
-/

namespace CanonicalK31B12

set_option autoImplicit false

inductive CompletionPhase where
  | doing
  | done
deriving DecidableEq, Repr

structure System where
  X : Type
  EncounterId : Type
  step : X → X
  phase : X → CompletionPhase
  mapId : X → Nat
  history : X → List EncounterId
  encounterId : X → EncounterId
  availableSeed : X → X → Prop
  linkedTo : X → X → Prop
  continuation : X → X → Prop
  realised : X → Prop

def Reachable (S : System) (x y : S.X) : Prop :=
  ∃ n : Nat, (S.step^[n]) x = y

def RetainsHistory (S : System) (before after : S.X) : Prop :=
  ∀ origin, origin ∈ S.history before → origin ∈ S.history after

def AvailableLinkedSeed (S : System) (completed seed : S.X) : Prop :=
  S.availableSeed completed seed ∧
    S.linkedTo completed seed ∧
    S.mapId seed ≠ S.mapId completed ∧
    S.phase seed = .doing ∧
    S.encounterId completed ∈ S.history seed ∧
    RetainsHistory S completed seed

def RealisedLinkedContinuation (S : System)
    (completed later : S.X) : Prop :=
  AvailableLinkedSeed S completed later ∧
    S.realised later ∧
    Reachable S completed later

namespace Constraint

def completedMapAdmitsLinkedProductiveContinuation (S : System) : Prop :=
  (∀ completed,
    S.phase completed = .done →
      ∃ seed, AvailableLinkedSeed S completed seed) ∧
  ∀ completed later,
    S.continuation completed later ↔
      RealisedLinkedContinuation S completed later

def unrelatedSeedControl (S : System) : Prop :=
  ∃ completed,
    S.phase completed = .done ∧
    ∀ seed, S.availableSeed completed seed →
      ¬ (S.linkedTo completed seed)

def idleContinuationControl (S : System) : Prop :=
  ∃ completed later,
    S.continuation completed later ∧ ¬ (S.realised later)

theorem unrelated_seed_control_rejects_constraint
    (S : System) (hcontrol : unrelatedSeedControl S) :
    ¬ (completedMapAdmitsLinkedProductiveContinuation S) := by
  rintro ⟨havailable, _hrealised⟩
  obtain ⟨completed, hdone, hunrelated⟩ := hcontrol
  obtain ⟨seed, hseed⟩ := havailable completed hdone
  exact hunrelated seed hseed.1 hseed.2.1

theorem idle_continuation_control_rejects_constraint
    (S : System) (hcontrol : idleContinuationControl S) :
    ¬ (completedMapAdmitsLinkedProductiveContinuation S) := by
  rintro ⟨_havailable, hcharacterises⟩
  obtain ⟨completed, later, hcontinuation, hidle⟩ := hcontrol
  exact hidle ((hcharacterises completed later).mp hcontinuation).2.1

end Constraint
end CanonicalK31B12

namespace WoodenIdolTuringBridgeCanonicalB12

open FoundationStoneTest16AF
open WoodenIdolTuringBridgePhase2
open WoodenIdolTuringBridgePhase2B
open WoodenIdolTuringBridgePhase2C
open WoodenIdolTuringBridgeB12
open CanonicalK31B12

def nextIntake {p : Program} (s : BreathState p) : BreathState p :=
  match s.linked with
  | some seed => intakeState s seed
  | none => s

noncomputable def chamberPhase {p : Program} (s : BreathState p) :
    CompletionPhase := by
  classical
  exact if B12Ready s then .done else .doing

def chamberRealised {p : Program} (s : BreathState p) : Prop :=
  s.chamber.frame.station = B3 ∧
    s.chamber.frame.direction = .inward

noncomputable def chamberDataSystem (p : Program) : CanonicalK31B12.System where
  X := BreathState p
  EncounterId := Nat
  step := nextIntake
  phase := chamberPhase
  mapId := fun s => s.chamber.frame.station.val
  history := fun s => [s.chamber.frame.source]
  encounterId := fun s => s.chamber.frame.source
  availableSeed := DirectedIntake
  linkedTo := fun completed seed =>
    seed.chamber.frame.source = completed.chamber.frame.source
  continuation := fun _ _ => False
  realised := chamberRealised

noncomputable def chamberSystem (p : Program) : CanonicalK31B12.System :=
  { chamberDataSystem p with
    continuation := DirectedIntake }

theorem chamberPhase_done_iff {p : Program} (s : BreathState p) :
    chamberPhase s = .done ↔ B12Ready s := by
  classical
  simp [chamberPhase]

theorem directed_intake_is_nextIntake {p : Program}
    {completed seed : BreathState p} (h : DirectedIntake completed seed) :
    nextIntake completed = seed := by
  rcases h with ⟨_hdirection, _hstation, payload, hlinked, rfl⟩
  simp [nextIntake, hlinked]

theorem directed_intake_realised {p : Program}
    {completed seed : BreathState p} (h : DirectedIntake completed seed) :
    chamberRealised seed := by
  rcases h with ⟨_hdirection, _hstation, payload, hlinked, rfl⟩
  exact ⟨rfl, rfl⟩

theorem directed_intake_changes_map {p : Program}
    {completed seed : BreathState p} (h : DirectedIntake completed seed) :
    seed.chamber.frame.station.val ≠ completed.chamber.frame.station.val := by
  rcases h with ⟨_hdirection, hstation, payload, hlinked, rfl⟩
  rw [hstation]
  simp only [intakeState, advanceState, advanceFrame]
  decide

theorem directed_intake_seed_is_doing {p : Program}
    {completed seed : BreathState p} (h : DirectedIntake completed seed) :
    chamberPhase seed = .doing := by
  classical
  unfold chamberPhase
  apply if_neg
  rcases h with ⟨_hdirection, _hstation, payload, hlinked, rfl⟩
  intro hready
  have hne : B3 ≠ B12 := by decide
  apply hne
  simpa [intakeState, advanceState, advanceFrame] using hready.1

theorem directed_intake_retains_history {p : Program}
    {completed seed : BreathState p} (h : DirectedIntake completed seed) :
    CanonicalK31B12.RetainsHistory (chamberDataSystem p) completed seed := by
  intro origin horigin
  change origin ∈ [completed.chamber.frame.source] at horigin
  change origin ∈ [seed.chamber.frame.source]
  rw [intake_retains_source h.2]
  exact horigin

theorem directed_intake_is_available_linked_seed {p : Program}
    {completed seed : BreathState p} (h : DirectedIntake completed seed) :
    AvailableLinkedSeed (chamberDataSystem p) completed seed := by
  refine ⟨h, intake_retains_source h.2, directed_intake_changes_map h,
    directed_intake_seed_is_doing h, ?_, directed_intake_retains_history h⟩
  change completed.chamber.frame.source ∈ [seed.chamber.frame.source]
  rw [intake_retains_source h.2]
  exact List.Mem.head _

theorem directed_intake_is_reachable {p : Program}
    {completed seed : BreathState p} (h : DirectedIntake completed seed) :
    Reachable (chamberDataSystem p) completed seed := by
  refine ⟨1, ?_⟩
  simpa [chamberDataSystem] using
    directed_intake_is_nextIntake h

theorem directed_intake_is_realised_continuation {p : Program}
    {completed seed : BreathState p} (h : DirectedIntake completed seed) :
    RealisedLinkedContinuation (chamberDataSystem p) completed seed := by
  exact ⟨directed_intake_is_available_linked_seed h,
    directed_intake_realised h, directed_intake_is_reachable h⟩

theorem b12_ready_has_canonical_seed {p : Program} (completed : BreathState p)
    (hdone : (chamberSystem p).phase completed = .done) :
    ∃ seed, AvailableLinkedSeed (chamberSystem p) completed seed := by
  have hready : B12Ready completed :=
    (chamberPhase_done_iff completed).mp hdone
  obtain ⟨seed, hintake⟩ := (b12Ready_iff_next_intake completed).mp hready
  exact ⟨seed, directed_intake_is_available_linked_seed hintake⟩

theorem chamber_continuation_characterisation (p : Program)
    (completed later : BreathState p) :
    (chamberSystem p).continuation completed later ↔
      RealisedLinkedContinuation (chamberSystem p) completed later := by
  constructor
  · intro h
    change RealisedLinkedContinuation (chamberDataSystem p) completed later
    exact directed_intake_is_realised_continuation h
  · intro h
    exact h.1.1

theorem chamber_satisfies_canonical_K31_B12 (p : Program) :
    CanonicalK31B12.Constraint.completedMapAdmitsLinkedProductiveContinuation
      (chamberSystem p) := by
  exact ⟨b12_ready_has_canonical_seed, chamber_continuation_characterisation p⟩

def erasedPhase {p : Program} (ready : BreathState p)
    (s : BreathState p) : CompletionPhase :=
  if forgetPhase s = forgetPhase ready then .done else .doing

noncomputable def stationErasedSystem (p : Program) (ready : BreathState p) :
    CanonicalK31B12.System :=
  { chamberSystem p with phase := erasedPhase ready }

theorem erasedPhase_done_of_same_view {p : Program}
    {ready wrong : BreathState p} (h : forgetPhase wrong = forgetPhase ready) :
    (stationErasedSystem p ready).phase wrong = .done := by
  simp [stationErasedSystem, erasedPhase, h]

theorem station_erasure_breaks_canonical_K31_B12
    (p : Program) (core : HState) (payload : LinkedSeed) :
    let ready := breathAt p core B12 .outward payload
    let wrong := breathAt p core B3 .outward payload
    ¬ CanonicalK31B12.Constraint.completedMapAdmitsLinkedProductiveContinuation
      (stationErasedSystem p ready) := by
  dsimp
  intro hcanonical
  have hremoval := station_erasure_loses_enabled_boundary p core payload
  dsimp at hremoval
  have hdone :
      (stationErasedSystem p (breathAt p core B12 .outward payload)).phase
        (breathAt p core B3 .outward payload) = .done :=
    erasedPhase_done_of_same_view hremoval.1.symm
  obtain ⟨seed, hseed⟩ := hcanonical.1 _ hdone
  exact hremoval.2.2 ⟨seed, hseed.1⟩

theorem canonical_K31_B12_bridge_certificate :
    (∀ p : Program,
      CanonicalK31B12.Constraint.completedMapAdmitsLinkedProductiveContinuation
        (chamberSystem p)) ∧
    (∀ (p : Program) (core : HState) (payload : LinkedSeed),
      let ready := breathAt p core B12 .outward payload
      ¬ CanonicalK31B12.Constraint.completedMapAdmitsLinkedProductiveContinuation
        (stationErasedSystem p ready)) := by
  exact ⟨chamber_satisfies_canonical_K31_B12,
    station_erasure_breaks_canonical_K31_B12⟩

#print axioms CanonicalK31B12.Constraint.unrelated_seed_control_rejects_constraint
#print axioms chamber_satisfies_canonical_K31_B12
#print axioms station_erasure_breaks_canonical_K31_B12
#print axioms canonical_K31_B12_bridge_certificate

end WoodenIdolTuringBridgeCanonicalB12
