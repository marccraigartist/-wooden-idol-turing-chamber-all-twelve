import WoodenIdolTuringBridgePhase2C

/-!
# THE WOODEN IDOL × TURING CHAMBER — B12 BRIDGE

This file formalises the approved operational reading of B12:

> reception at the external boundary opens a genuine subsequent continuation.

It deliberately does **not** reuse the old Stage 2 predicate equating B12 with
eventual non-stillness. In this bridge, the internal 16AF helix computation
may halt. Renewal occurs because the honestly received two-body output is
available as the linked seed of a later intake.

The positive bridge is accompanied by three controls:

* a B12-shaped state with no received seed is a dead end;
* the B9 release boundary is not B12 reception;
* a seed carrying an unrelated source cannot inhabit the honest breath state.

Thus B12 is neither stored as a Boolean flag nor identified with B9 or with
machine non-halting.
-/

namespace WoodenIdolTuringBridgeB12

open FoundationStoneTest16AF
open WoodenIdolTuringBridgePhase2
open WoodenIdolTuringBridgePhase2B
open WoodenIdolTuringBridgePhase2C

/-! ## The canonical operational predicate -/

/-- A state is ready at B12 precisely when it is at the outward reception
boundary and carries an honest linked seed from its own provenance source.

This definition mentions no future state and no transition. The theorem
`b12Ready_iff_next_intake` below proves that it is exactly the condition under
which a subsequent directed intake exists. -/
def B12Ready {p : Program} (s : BreathState p) : Prop :=
  s.chamber.frame.station = B12 ∧
  s.chamber.frame.direction = .outward ∧
  ∃ seed, s.linked = some seed ∧
    seed.source = s.chamber.frame.source

/-- B12 readiness is neither decorative nor a stored continuation field: it
is equivalent to the existence of an actual next directed intake. -/
theorem b12Ready_iff_next_intake {p : Program} (s : BreathState p) :
    B12Ready s ↔ ∃ next, DirectedIntake s next := by
  constructor
  · rintro ⟨hstation, hdirection, seed, hlinked, _⟩
    exact ⟨intakeState s seed, hdirection, hstation, seed, hlinked, rfl⟩
  · rintro ⟨next, hdirection, hstation, seed, hlinked, _⟩
    refine ⟨hstation, hdirection, seed, hlinked, ?_⟩
    simpa [SeedHonest, hlinked] using s.linked_honest

/-! ## The positive bridge -/

/-- Native directed reception constructs B12 readiness; readiness is derived
from the received output and its honest source, not postulated separately. -/
theorem directed_reception_is_B12 {p : Program}
    {released received : BreathState p}
    (h : DirectedReception released received) : B12Ready received := by
  rcases h with ⟨_, hstation, rfl⟩
  exact ⟨rfl, rfl, outputSeed released.chamber, rfl, rfl⟩

/-- Every genuine reception opens a concrete next intake. -/
theorem directed_reception_opens_next_intake {p : Program}
    {released received : BreathState p}
    (h : DirectedReception released received) :
    ∃ next, DirectedIntake received next :=
  (b12Ready_iff_next_intake received).mp
    (directed_reception_is_B12 h)

/-- A complete directed breath therefore returns to a B12 boundary from which
another breath can begin. -/
theorem directed_breath_ends_B12Ready {p : Program}
    {start finish : BreathState p}
    (h : DirectedBreath start finish) :
    B12Ready finish := by
  rcases h with ⟨atB3, atB6, atB9, hi, hm, hr, hc⟩
  exact directed_reception_is_B12 hc

/-- The linked output really becomes the native start core of the next breath.
This rules out interpreting "continuation" as mere storage of a payload. -/
theorem B12_continuation_installs_received_seed {p : Program}
    {received : BreathState p} (h : B12Ready received) :
    ∃ seed next,
      received.linked = some seed ∧
      DirectedIntake received next ∧
      next.chamber.core = seedStart p seed := by
  rcases h with ⟨hstation, hdirection, seed, hlinked, hsource⟩
  refine ⟨seed, intakeState received seed, hlinked, ?_, rfl⟩
  exact ⟨hdirection, hstation, seed, hlinked, rfl⟩

/-! ## Halting and renewal are different -/

theorem release_preserves_core {p : Program} {s t : BreathState p}
    (h : ReleaseBoundary s t) :
    t.chamber.core = s.chamber.core := by
  rcases h with ⟨_, rfl⟩
  rfl

theorem reception_preserves_core {p : Program} {s t : BreathState p}
    (h : Reception s t) :
    t.chamber.core = s.chamber.core := by
  rcases h with ⟨_, rfl⟩
  rfl

/-- A complete breath ends with a halted native core *and* a renewed external
continuation. This is the formal separation between machine halting and B12. -/
theorem B12_allows_halted_internal_core {p : Program}
    {start finish : BreathState p}
    (h : DirectedBreath start finish) :
    hstep p finish.chamber.core = none ∧ B12Ready finish := by
  rcases h with ⟨atB3, atB6, atB9, hi, hm, hr, hc⟩
  obtain ⟨n, hrun, hhalt⟩ := making_projects_to_native_run hm.2
  have hrelease : atB9.chamber.core = atB6.chamber.core :=
    release_preserves_core hr.2
  have hreceive : finish.chamber.core = atB9.chamber.core :=
    reception_preserves_core hc.2
  refine ⟨?_, directed_reception_is_B12 hc⟩
  rw [hreceive, hrelease]
  exact hhalt

/-! ## Red controls -/

/-- A valid framed state may look like B12 and retain the native machine while
carrying no received seed. It is deliberately a dead end. -/
def deadReceptionState (p : Program) (core : HState) (source : Nat) :
    BreathState p where
  chamber := chamberAt p core source B12 .outward
  linked := none
  linked_honest := trivial

theorem dead_reception_is_not_B12Ready
    (p : Program) (core : HState) (source : Nat) :
    ¬ B12Ready (deadReceptionState p core source) := by
  rintro ⟨_, _, seed, hlinked, _⟩
  simp [deadReceptionState] at hlinked

theorem dead_reception_opens_no_intake
    (p : Program) (core : HState) (source : Nat) :
    ¬ ∃ next, DirectedIntake (deadReceptionState p core source) next := by
  rw [← b12Ready_iff_next_intake]
  exact dead_reception_is_not_B12Ready p core source

/-- Release is at B9. Even though it carries the same completed native core,
it is not reception and cannot satisfy the canonical B12 predicate. -/
theorem directed_release_is_not_B12 {p : Program}
    {completed released : BreathState p}
    (h : DirectedRelease completed released) :
    ¬ B12Ready released := by
  intro hready
  rcases h with ⟨_, hstation, rfl⟩
  have hne : B9 ≠ B12 := by decide
  apply hne
  simpa [releaseBreathState, release, releaseFrame] using hready.1

/-- The provenance red control is inherited from the shared object: changing
only the source of the linked seed leaves the native machine unchanged but
violates the condition required to form a `BreathState`. -/
theorem forged_reception_is_rejected {p : Program}
    (c : ChamberState p)
    (seed : LinkedSeed)
    (falseSource : Nat)
    (hne : falseSource ≠ c.frame.source) :
    ¬ SeedHonest c (some (forgeSeed seed falseSource)) :=
  unrelated_seed_is_rejected c seed falseSource hne

/-! ## Claims certificate -/

/-- Earned claim: in the formally defined Turing Chamber, genuine B9-to-B12
reception is exactly the honest outward condition that opens a later intake.
This certificate does not claim that all twelve Wooden Idol predicates hold. -/
theorem turing_chamber_B12_bridge_certificate :
    (∀ (p : Program) (released received : BreathState p),
      DirectedReception released received →
      B12Ready received ∧ ∃ next, DirectedIntake received next) ∧
    (∀ (p : Program) (start finish : BreathState p),
      DirectedBreath start finish →
      hstep p finish.chamber.core = none ∧ B12Ready finish) ∧
    (∀ (p : Program) (core : HState) (source : Nat),
      ¬ B12Ready (deadReceptionState p core source)) ∧
    (∀ (p : Program) (completed released : BreathState p),
      DirectedRelease completed released → ¬ B12Ready released) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p released received h
    exact
      ⟨directed_reception_is_B12 (p := p) h,
       directed_reception_opens_next_intake (p := p) h⟩
  · intro p start finish h
    exact B12_allows_halted_internal_core (p := p) h
  · intro p core source
    exact dead_reception_is_not_B12Ready p core source
  · intro p completed released h
    exact directed_release_is_not_B12 (p := p) h

#print axioms b12Ready_iff_next_intake
#print axioms directed_reception_is_B12
#print axioms B12_continuation_installs_received_seed
#print axioms B12_allows_halted_internal_core
#print axioms dead_reception_opens_no_intake
#print axioms directed_release_is_not_B12
#print axioms forged_reception_is_rejected
#print axioms turing_chamber_B12_bridge_certificate

end WoodenIdolTuringBridgeB12
