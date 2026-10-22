import Phase6Godel
import Phase6Kernel

/-!
Chapter 7: actual Phase6 Body/Shadow integration on a 6+6 advancing network.
Every live passenger contains the unmodified original Phase6Kernel.Body,
including the retained method library, local history, prepared Shadow,
inbox, and outbox. The complete network is the Payload of the native
Phase6Frame, with no projection to a smaller certified system.

Indefinite continuation is the total function `run` indexed by Nat, given a
supplied task stream. No RSI efficacy, unbounded novelty, or endogenous task
creation is asserted.
-/

namespace Chapter7Phase6Native
open Phase6Kernel MemoryLadder
open TuringChamberB124OneSystem Phase5InterfaceControls Phase5HelixLabels
set_option autoImplicit false

structure Passenger where
  id : Nat
  entryRound : Nat
  body : Body
  deriving DecidableEq, Repr, Encodable

structure Lane where
  b3 : Option Passenger := none
  b4 : Option Passenger := none
  b5 : Option Passenger := none
  b6 : Option Passenger := none
  b7 : Option Passenger := none
  b8 : Option Passenger := none
  released : List Passenger := []
  deriving DecidableEq, Repr, Encodable

structure Network where
  a : Lane := {}
  b : Lane := {}
  completed : Nat := 0
  toA : Option Packet := none
  toB : Option Packet := none
  deriving DecidableEq, Repr, Encodable

/-- New agents carry a Phase 6 library, empty history, prepared shadow, and
    only the received packet they are allowed to observe. -/
def newPassenger (id round : Nat) (received : Option Packet) : Passenger :=
  ⟨id, round, { initialBody with inbox := received }⟩

/-- One position's real, imported Phase 6 learning/artist-shadow transition. -/
def encounter (round : Nat) (sender : Bool) (tasks : List Word)
    (p : Passenger) : Passenger :=
  let observation := observeLocal tasks p.body
  { p with body := finishLocal sender round true p.body observation }

def station (round : Nat) (sender : Bool) (tasks : List Word)
    (p : Option Passenger) : Option Passenger :=
  p.map (encounter round sender tasks)

/-- The B8 departure retains the original Body with its complete local
    history and latest prospective shadow. -/
def Lane.tick (round : Nat) (sender : Bool) (tasks : List Word)
    (arrival : Passenger) (l : Lane) : Lane :=
  let done8 := station round sender tasks l.b8
  { b3 := some arrival
    b4 := station round sender tasks l.b3
    b5 := station round sender tasks l.b4
    b6 := station round sender tasks l.b5
    b7 := station round sender tasks l.b6
    b8 := station round sender tasks l.b7
    released := done8.toList ++ l.released }

/-- Only a released packet crosses the two situated bodies' boundaries. -/
def Lane.departingPacket (round : Nat) (sender : Bool)
    (tasks : List Word) (l : Lane) : Option Packet :=
  (station round sender tasks l.b8).bind fun p => p.body.outbox

/-- A newly emitted packet is available to the opposite side at a following
    tick, never simultaneously to the current arrival. -/
def Network.tick (tasks : Nat → Bool → List Word) (net : Network) : Network :=
  let n := net.completed
  let releasedA := net.a.departingPacket n false (tasks n false)
  let releasedB := net.b.departingPacket n true (tasks n true)
  let arrivalA := newPassenger (2*n) n net.toA
  let arrivalB := newPassenger (2*n+1) n net.toB
  { a := net.a.tick n false (tasks n false) arrivalA
    b := net.b.tick n true (tasks n true) arrivalB
    completed := n+1
    toA := releasedB
    toB := releasedA }

/-- Mathematical continuation for every Nat; does not claim infinitely much
    physical computation is executed. -/
def run (tasks : Nat → Bool → List Word) : Nat → Network
  | 0 => {}
  | n+1 => (run tasks n).tick tasks

theorem run_succ (tasks : Nat → Bool → List Word) (n : Nat) :
    run tasks (n+1) = (run tasks n).tick tasks := rfl

theorem run_completed (tasks : Nat → Bool → List Word) (n : Nat) :
    (run tasks n).completed = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run_succ, Network.tick, ih]

theorem network_new_pair (tasks : Nat → Bool → List Word) (n : Nat) :
    (run tasks (n+1)).a.b3 = some
      (newPassenger (2*n) n (run tasks n).toA) ∧
    (run tasks (n+1)).b.b3 = some
      (newPassenger (2*n+1) n (run tasks n).toB) := by
  simp [run_succ, Network.tick, run_completed, Lane.tick]

theorem station_keeps_identity (round : Nat) (sender : Bool) (tasks : List Word)
    (p : Passenger) :
    (encounter round sender tasks p).id = p.id := rfl

theorem station_occupancy (round : Nat) (sender : Bool) (tasks : List Word)
    (p : Option Passenger) :
    (station round sender tasks p).isSome = p.isSome := by
  cases p <;> rfl

def Lane.full (l : Lane) : Prop :=
  l.b3.isSome = true ∧ l.b4.isSome = true ∧ l.b5.isSome = true ∧
  l.b6.isSome = true ∧ l.b7.isSome = true ∧ l.b8.isSome = true

theorem Lane.full_tick (l : Lane) (round : Nat) (side : Bool)
    (tasks : List Word) (arrival : Passenger) (h : l.full) :
    (l.tick round side tasks arrival).full := by
  rcases h with ⟨h3,h4,h5,h6,h7,_⟩
  change (some arrival).isSome = true ∧
    (station round side tasks l.b3).isSome = true ∧
    (station round side tasks l.b4).isSome = true ∧
    (station round side tasks l.b5).isSome = true ∧
    (station round side tasks l.b6).isSome = true ∧
    (station round side tasks l.b7).isSome = true
  simp only [station_occupancy]
  exact ⟨rfl,h3,h4,h5,h6,h7⟩

theorem Lane.retains_releases (l : Lane) (round : Nat) (side : Bool)
    (tasks : List Word) (p : Passenger) :
    l.released <:+ (l.tick round side tasks p).released := by
  simp [Lane.tick, List.suffix_append]

/-- The entire native 6+6 network is passed as the actual Phase6Frame payload,
    not outside the scope of the imported All12 certificate. -/
def nativeConfig (tasks : Nat → Bool → List Word) :
    Phase6Frame.Config Network :=
  { initial := {}
    observe := fun n s => [n,s.completed,s.a.released.length,s.b.released.length]
    advance := fun _ s _ => s.tick tasks }

noncomputable def nativeSystem (tasks : Nat → Bool → List Word) : System :=
  Phase6Godel.chamber (nativeConfig tasks)

/-- Canonical B1...B12 on the ACTUAL expanded carrier (conditional on
    successful compilation of this source with its original Phase 6 imports). -/
theorem native_all_twelve (tasks : Nat → Bool → List Word) :
    FrozenAll12 (nativeSystem tasks) :=
  Phase6Godel.all_twelve (nativeConfig tasks)

theorem native_event_helix (tasks : Nat → Bool → List Word) :
    EventHelix (nativeSystem tasks)
      (.inl (Phase6Frame.init (nativeConfig tasks))) :=
  Phase6Godel.realised_event_helix (nativeConfig tasks)

theorem payload_after_is_run (tasks : Nat → Bool → List Word) (n : Nat) :
    Phase6Frame.payloadAfter (nativeConfig tasks) n = run tasks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (run tasks n).tick tasks = run tasks (n+1)
      exact (run_succ tasks n).symm

/-- Actual native Frame.step reaches exactly the indexed pipeline state at
    each two-step completion/reset, not merely an isomorphic side simulation. -/
theorem native_reset_is_run (tasks : Nat → Bool → List Word) (n : Nat) :
    (((Phase6Frame.step (nativeConfig tasks))^[2*n])
      (Phase6Frame.init (nativeConfig tasks))).payload = run tasks n := by
  rw [Phase6Frame.trajectory_state]
  exact payload_after_is_run tasks n

theorem native_each_reset_retains (tasks : Nat → Bool → List Word) (n : Nat) :
    let s := (Phase6Frame.step (nativeConfig tasks))^[2*n]
      (Phase6Frame.init (nativeConfig tasks))
    s.phase = .doing ∧ s.round = n ∧
    s.records.length = n ∧ s.log.length = n :=
  Phase6Frame.all_resets_ready (nativeConfig tasks) n

/-- One theorem combining certified canonical predicates, realised renewal
    and exact all-natural-numbered operational correspondence. -/
theorem chapter7_phase6_headline (tasks : Nat → Bool → List Word) :
    FrozenAll12 (nativeSystem tasks) ∧
    EventHelix (nativeSystem tasks)
      (.inl (Phase6Frame.init (nativeConfig tasks))) ∧
    (∀ n : Nat, (((Phase6Frame.step (nativeConfig tasks))^[2*n])
      (Phase6Frame.init (nativeConfig tasks))).payload = run tasks n) :=
  ⟨native_all_twelve tasks, native_event_helix tasks,
    native_reset_is_run tasks⟩

#print axioms native_all_twelve
#print axioms native_event_helix
#print axioms native_reset_is_run
#print axioms chapter7_phase6_headline
end Chapter7Phase6Native