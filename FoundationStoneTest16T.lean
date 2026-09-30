import Mathlib

/-!
# THE THIRD REGISTER IN THE TWO-BODY CHAMBER — FOUNDATION STONE TEST 16T

Test 16S certified the finite macro substrate: relocation, linking, clear and
unbounded transfer.  Test 16T asks whether two physical counters can carry a
richer logical register state without losing the invariant needed by a future
universal compiler.

Three unbounded logical registers `(r0,r1,r2)` are packed into one natural
number using Mathlib's bijective `Nat.pair`.  The canonical two-counter frame is

    A = encode(r0,r1,r2),   B = 0.

The second counter is scratch space.  The endpoint equations proved for 16S's
transfer macro are represented here as `moveAtoB` and `moveBtoA`.

Lean certifies:

1. encode/decode are exact inverses, so the three-register state is neither
   collided nor approximated;
2. the canonical representation is unique and decodable;
3. a one-way A→B transfer breaks the strict canonical invariant whenever the
   payload is nonzero, but preserves a wider transport invariant saying that
   the whole packed payload is in exactly one body;
4. decoding the sum `A+B` recovers all three registers on either side;
5. B→A restores the strict invariant exactly; hence the verified transfer
   round trip implements the identity logical macro;
6. clearing the empty scratch counter preserves every canonical state;
7. clearing the payload counter destroys every nonzero represented state;
8. macro specifications compose at representation boundaries;
9. RED CONTROL — forgetting which body carries the payload preserves the
   decoded content but erases the route/frame distinction.

This does NOT yet provide instruction sequences for incrementing or testing an
individual packed register.  The file isolates those remaining obligations:
an arithmetic macro must manipulate the code, use B as scratch, and restore B
to zero before returning.  Thus 16T proves the codec and invariant discipline,
not the universal compiler itself.
-/

namespace FoundationStoneTest16T

/-! ## 1. A bijective three-register codec -/

structure Registers3 where
  r0 : Nat
  r1 : Nat
  r2 : Nat
deriving DecidableEq, Repr

def encode (r : Registers3) : Nat := Nat.pair r.r0 (Nat.pair r.r1 r.r2)

def decode (n : Nat) : Registers3 :=
  let outer := Nat.unpair n
  let inner := Nat.unpair outer.2
  ⟨outer.1, inner.1, inner.2⟩

theorem decode_encode (r : Registers3) : decode (encode r) = r := by
  rcases r with ⟨r0, r1, r2⟩
  simp [encode, decode, Nat.unpair_pair]

theorem encode_decode (n : Nat) : encode (decode n) = n := by
  unfold encode decode
  simp only
  rw [Nat.pair_unpair]
  rw [Nat.pair_unpair]

theorem encode_injective : Function.Injective encode := by
  intro x y h
  have := congrArg decode h
  simpa [decode_encode] using this

theorem decode_surjective : Function.Surjective decode := by
  intro r
  exact ⟨encode r, decode_encode r⟩

/-! ## 2. Strict boundary and wider transport frames -/

structure Counters where
  a : Nat
  b : Nat
deriving DecidableEq, Repr

inductive Carrier
  | atA
  | atB
deriving DecidableEq, Repr

def carried (side : Carrier) (r : Registers3) : Counters :=
  match side with
  | .atA => ⟨encode r, 0⟩
  | .atB => ⟨0, encode r⟩

/-- Strict macro-boundary representation: payload in A, scratch B empty. -/
def Represents (c : Counters) (r : Registers3) : Prop := c = carried .atA r

/-- Wider in-flight representation: record which body currently carries it. -/
def TransitRepresents (c : Counters) (side : Carrier) (r : Registers3) : Prop :=
  c = carried side r

theorem canonical_is_unique (r s : Registers3) :
    carried .atA r = carried .atA s ↔ r = s := by
  constructor
  · intro h
    have ha := congrArg Counters.a h
    exact encode_injective ha
  · intro h
    rw [h]

theorem transport_is_unique (side : Carrier) (r s : Registers3) :
    carried side r = carried side s ↔ r = s := by
  constructor
  · intro h
    cases side with
    | atA =>
        have hc := (canonical_is_unique r s).mp h
        exact hc
    | atB =>
        have hb := congrArg Counters.b h
        exact encode_injective hb
  · intro h
    rw [h]

theorem represented_state_decodes (c : Counters) (r : Registers3)
    (h : Represents c r) : decode c.a = r ∧ c.b = 0 := by
  rw [h]
  exact ⟨decode_encode r, rfl⟩

/-! ## 3. The endpoint semantics of 16S's verified transfer macro -/

/-- Move all of A into B. -/
def moveAtoB (c : Counters) : Counters := ⟨0, c.b + c.a⟩

/-- Move all of B into A. -/
def moveBtoA (c : Counters) : Counters := ⟨c.a + c.b, 0⟩

theorem move_out_changes_carrier (r : Registers3) :
    moveAtoB (carried .atA r) = carried .atB r := by
  simp [moveAtoB, carried]

theorem move_back_changes_carrier (r : Registers3) :
    moveBtoA (carried .atB r) = carried .atA r := by
  simp [moveBtoA, carried]

theorem transfer_round_trip_restores (r : Registers3) :
    moveBtoA (moveAtoB (carried .atA r)) = carried .atA r := by
  rw [move_out_changes_carrier, move_back_changes_carrier]

theorem transfer_preserves_transport_invariant (r : Registers3) :
    TransitRepresents (moveAtoB (carried .atA r)) .atB r ∧
    TransitRepresents (moveBtoA (carried .atB r)) .atA r := by
  exact ⟨move_out_changes_carrier r, move_back_changes_carrier r⟩

/-! ## 4. The shadow remembers content but forgets carrier -/

def shadowCode (c : Counters) : Nat := c.a + c.b
def shadowDecode (c : Counters) : Registers3 := decode (shadowCode c)

theorem shadow_decodes_either_carrier (side : Carrier) (r : Registers3) :
    shadowDecode (carried side r) = r := by
  cases side <;> simp [shadowDecode, shadowCode, carried, decode_encode]

theorem transfer_keeps_shadow (r : Registers3) :
    shadowDecode (moveAtoB (carried .atA r)) = r ∧
    shadowDecode (moveBtoA (carried .atB r)) = r := by
  rw [move_out_changes_carrier, move_back_changes_carrier]
  exact ⟨shadow_decodes_either_carrier .atB r,
    shadow_decodes_either_carrier .atA r⟩

/-- Nonzero payloads expose the distinction hidden by the shadow. -/
theorem opposite_carriers_are_distinct (r : Registers3) (hcode : encode r ≠ 0) :
    carried .atA r ≠ carried .atB r := by
  intro h
  have ha := congrArg Counters.a h
  simp [carried] at ha
  exact hcode ha

/-- RED CONTROL: equal decoded content does not recover which body carried it. -/
theorem shadow_forgets_the_frame (r : Registers3) (hcode : encode r ≠ 0) :
    shadowDecode (carried .atA r) = shadowDecode (carried .atB r) ∧
    carried .atA r ≠ carried .atB r := by
  exact ⟨by rw [shadow_decodes_either_carrier, shadow_decodes_either_carrier],
    opposite_carriers_are_distinct r hcode⟩

/-! ## 5. Strict invariant: broken in flight, restored at the boundary -/

theorem one_way_breaks_strict_representation (r : Registers3)
    (hcode : encode r ≠ 0) :
    ¬ Represents (moveAtoB (carried .atA r)) r := by
  intro h
  unfold Represents at h
  rw [move_out_changes_carrier] at h
  exact opposite_carriers_are_distinct r hcode h.symm

theorem round_trip_restores_strict_representation (r : Registers3) :
    Represents (moveBtoA (moveAtoB (carried .atA r))) r := by
  exact transfer_round_trip_restores r

/-! ## 6. Scratch discipline -/

def clearA (c : Counters) : Counters := ⟨0, c.b⟩
def clearB (c : Counters) : Counters := ⟨c.a, 0⟩

/-- Clearing the already-empty scratch register is a representation-preserving no-op. -/
theorem clear_scratch_preserves (r : Registers3) :
    clearB (carried .atA r) = carried .atA r := by
  rfl

/-- Clearing the payload counter destroys every nonzero represented payload. -/
theorem clear_payload_destroys (r : Registers3) (hcode : encode r ≠ 0) :
    clearA (carried .atA r) ≠ carried .atA r := by
  intro h
  have ha := congrArg Counters.a h
  simp [clearA, carried] at ha
  exact hcode ha.symm

/-- A concrete nonzero register state for executable red controls. -/
def sample : Registers3 := ⟨1, 2, 3⟩

theorem sample_code_nonzero : encode sample ≠ 0 := by decide

theorem sample_control :
    decode (encode sample) = sample ∧
    shadowDecode (moveAtoB (carried .atA sample)) = sample ∧
    ¬ Represents (moveAtoB (carried .atA sample)) sample ∧
    Represents (moveBtoA (moveAtoB (carried .atA sample))) sample := by
  exact ⟨decode_encode sample, transfer_keeps_shadow sample |>.1,
    one_way_breaks_strict_representation sample sample_code_nonzero,
    round_trip_restores_strict_representation sample⟩

/-! ## 7. Boundary macro contracts and composition -/

abbrev LogicalOp := Registers3 → Registers3
abbrev PhysicalMacro := Counters → Counters

/-- A physical macro implements a logical operation at strict boundaries. -/
def Implements (physical : PhysicalMacro) (logical : LogicalOp) : Prop :=
  ∀ r, physical (carried .atA r) = carried .atA (logical r)

def composePhysical (g f : PhysicalMacro) : PhysicalMacro := fun c => g (f c)
def composeLogical (g f : LogicalOp) : LogicalOp := fun r => g (f r)

theorem implements_compose {F G : PhysicalMacro} {f g : LogicalOp}
    (hF : Implements F f) (hG : Implements G g) :
    Implements (composePhysical G F) (composeLogical g f) := by
  intro r
  unfold composePhysical composeLogical
  rw [hF, hG]

def transferRoundTrip : PhysicalMacro := fun c => moveBtoA (moveAtoB c)

theorem round_trip_implements_identity : Implements transferRoundTrip id := by
  intro r
  exact transfer_round_trip_restores r

theorem clear_scratch_implements_identity : Implements clearB id := by
  intro r
  exact clear_scratch_preserves r

/-- Any future packed-register macro can be safely surrounded by already
verified boundary-preserving macros. -/
theorem boundary_context_preserves_spec {F : PhysicalMacro} {f : LogicalOp}
    (hF : Implements F f) :
    Implements (composePhysical clearB (composePhysical F transferRoundTrip)) f := by
  intro r
  unfold composePhysical transferRoundTrip
  rw [transfer_round_trip_restores, hF, clear_scratch_preserves]

/-! ## 8. The remaining arithmetic macro obligations -/

def incR0 (r : Registers3) : Registers3 := { r with r0 := r.r0 + 1 }
def incR1 (r : Registers3) : Registers3 := { r with r1 := r.r1 + 1 }
def incR2 (r : Registers3) : Registers3 := { r with r2 := r.r2 + 1 }

/-- This type states the exact next compiler obligation without pretending to
inhabit it: supply concrete physical macros for the three packed increments. -/
structure PackedIncrementKit where
  macro0 : PhysicalMacro
  macro1 : PhysicalMacro
  macro2 : PhysicalMacro
  correct0 : Implements macro0 incR0
  correct1 : Implements macro1 incR1
  correct2 : Implements macro2 incR2

/-- If such a kit is supplied, arbitrary finite sequences of the three logical
increments can be assembled compositionally without reopening the codec proof. -/
inductive RegName
  | r0 | r1 | r2
deriving DecidableEq

def logicalOf : RegName → LogicalOp
  | .r0 => incR0
  | .r1 => incR1
  | .r2 => incR2

def physicalOf (kit : PackedIncrementKit) : RegName → PhysicalMacro
  | .r0 => kit.macro0
  | .r1 => kit.macro1
  | .r2 => kit.macro2

theorem kit_instruction_correct (kit : PackedIncrementKit) (name : RegName) :
    Implements (physicalOf kit name) (logicalOf name) := by
  cases name with
  | r0 => exact kit.correct0
  | r1 => exact kit.correct1
  | r2 => exact kit.correct2

/-! ## Certificate -/

theorem richer_register_invariant_certificate :
    (∀ r, decode (encode r) = r) ∧
    (∀ n, encode (decode n) = n) ∧
    Function.Injective encode ∧
    (∀ side r, shadowDecode (carried side r) = r) ∧
    (∀ r, moveAtoB (carried .atA r) = carried .atB r) ∧
    (∀ r, moveBtoA (moveAtoB (carried .atA r)) = carried .atA r) ∧
    (∀ r, clearB (carried .atA r) = carried .atA r) ∧
    (∀ r, encode r ≠ 0 → ¬ Represents (moveAtoB (carried .atA r)) r) ∧
    (∀ r, encode r ≠ 0 →
      shadowDecode (carried .atA r) = shadowDecode (carried .atB r) ∧
      carried .atA r ≠ carried .atB r) ∧
    Implements transferRoundTrip id :=
  ⟨decode_encode, encode_decode, encode_injective,
   shadow_decodes_either_carrier, move_out_changes_carrier,
   transfer_round_trip_restores, clear_scratch_preserves,
   one_way_breaks_strict_representation, shadow_forgets_the_frame,
   round_trip_implements_identity⟩

#print axioms decode_encode
#print axioms encode_decode
#print axioms encode_injective
#print axioms canonical_is_unique
#print axioms transport_is_unique
#print axioms move_out_changes_carrier
#print axioms transfer_round_trip_restores
#print axioms shadow_decodes_either_carrier
#print axioms shadow_forgets_the_frame
#print axioms one_way_breaks_strict_representation
#print axioms clear_payload_destroys
#print axioms sample_control
#print axioms implements_compose
#print axioms boundary_context_preserves_spec
#print axioms kit_instruction_correct
#print axioms richer_register_invariant_certificate

end FoundationStoneTest16T
