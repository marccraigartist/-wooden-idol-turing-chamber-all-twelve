/-!
# THE RECEIVING BODY — FOUNDATION STONE TEST 16E

Runs in the Lean live editor with no imports (core Lean only).

Test 16D made the signed orientation bit proof-carrying.  Test 16E puts that packet
through a genuine two-body boundary:

* the SENDER supplies an untrusted packet;
* the RECEIVER knows only the public transition rules;
* the receiver checks the route, recomputes the bend and returns its own answer.

Order of results:

1. A valid packet is accepted, and the receiver's result is forced to be the native
   orientation belonging to the checked route.  The receiver never needs to trust the
   sender's announced bit.
2. Honest A and B transmissions are accepted with different orientations.
3. Three adversarial transmissions are rejected: flipped answer, invented stationary
   trace, and route relabelling.  An answer-only receiver remains blind to the invented
   trace.
4. THE LIMIT.  A sender can construct the complete valid packet for either route as
   data, without the model containing a historical performance event.  The receiver
   accepts it.  Two worlds with different histories but the identical transmitted
   packet are indistinguishable to EVERY packet-only observer.

So the receiver establishes DERIVABILITY from the public rules, not OCCURRENCE in
history.  This is the exact opening for a later commitment/challenge test.

Guardrail: body labels are routing labels, not identities or signatures.  This file
contains no cryptographic authentication, trusted clock, physical sensor or hidden
challenge.  It therefore does not prove who acted, or that anyone acted at all.
-/
namespace FoundationStoneSixteenE

/-! ## Exact 30-degree geometry over Z[sqrt 3] -/

structure Z3 where
  a : Int
  b : Int
deriving DecidableEq

structure V3 where
  x : Z3
  y : Z3
  z : Z3
deriving DecidableEq

def zzero : Z3 := ⟨0, 0⟩
def zone : Z3 := ⟨1, 0⟩
def zadd (u v : Z3) : Z3 := ⟨u.a + v.a, u.b + v.b⟩
def zneg (u : Z3) : Z3 := ⟨-u.a, -u.b⟩
def zsub (u v : Z3) : Z3 := zadd u (zneg v)
def zscale (k : Int) (u : Z3) : Z3 := ⟨k * u.a, k * u.b⟩
def zroot (u : Z3) : Z3 := ⟨3 * u.b, u.a⟩
def zmul (u v : Z3) : Z3 :=
  ⟨u.a * v.a + 3 * u.b * v.b, u.a * v.b + u.b * v.a⟩

/-- Twice a 30-degree turn about z. -/
def rzP (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.y, zadd v.x (zroot v.y), zscale 2 v.z⟩

/-- Twice a 30-degree turn about y. -/
def ryP (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩

/-- Triple product u dot (v cross w). -/
def det3 (u v w : V3) : Z3 :=
  zadd (zadd (zmul u.x (zsub (zmul v.y w.z) (zmul v.z w.y)))
             (zmul u.y (zsub (zmul v.z w.x) (zmul v.x w.z))))
       (zmul u.z (zsub (zmul v.x w.y) (zmul v.y w.x)))

def xPoint : V3 := ⟨zone, zzero, zzero⟩
def positiveBend : Z3 := ⟨0, 1⟩

inductive Route
  | A  -- z first, then y
  | B  -- y first, then z
deriving DecidableEq

def firstStep : Route → V3 → V3
  | .A, v => rzP v
  | .B, v => ryP v

def secondStep : Route → V3 → V3
  | .A, v => ryP v
  | .B, v => rzP v

def nativeMid (r : Route) : V3 := firstStep r xPoint
def nativeFinish (r : Route) : V3 := secondStep r (nativeMid r)
def nativeBend (r : Route) : Z3 := det3 xPoint (nativeMid r) (nativeFinish r)
def nativeBit (r : Route) : Bool := nativeBend r == positiveBend

theorem the_two_native_orientations :
    nativeBend .A = ⟨0, -1⟩ ∧ nativeBit .A = false ∧
    nativeBend .B = ⟨0, 1⟩ ∧ nativeBit .B = true := by
  decide

/-! ## The sender's untrusted packet -/

structure Evidence where
  route : Route
  start : V3
  midpoint : V3
  finish : V3
  bend : Z3
  bit : Bool
deriving DecidableEq

def Valid (p : Evidence) : Prop :=
  p.start = xPoint ∧
  p.midpoint = firstStep p.route p.start ∧
  p.finish = secondStep p.route p.midpoint ∧
  p.bend = det3 p.start p.midpoint p.finish ∧
  p.bit = (p.bend == positiveBend)

instance (p : Evidence) : Decidable (Valid p) := by
  unfold Valid
  infer_instance

def nativeEvidence (r : Route) : Evidence :=
  ⟨r, xPoint, nativeMid r, nativeFinish r, nativeBend r, nativeBit r⟩

theorem native_evidence_valid : ∀ r, Valid (nativeEvidence r) := by
  intro r
  cases r <;> decide

def recomputedBit (p : Evidence) : Bool :=
  det3 p.start p.midpoint p.finish == positiveBend

theorem valid_recomputed_bit_is_native (p : Evidence) (h : Valid p) :
    recomputedBit p = nativeBit p.route := by
  rcases h with ⟨hs, hm, hf, hb, hbit⟩
  unfold recomputedBit nativeBit nativeBend nativeFinish nativeMid
  rw [← hs, ← hm, ← hf]

/-! ## The independent receiving body -/

/-- The receiver either rejects, or returns the checked route and its own recomputation.
It does not return the sender's `p.bit` field. -/
def receive (p : Evidence) : Option (Route × Bool) :=
  if Valid p then some (p.route, recomputedBit p) else none

/-- 1a. On any valid packet the receiver's independently computed result is native. -/
theorem receiver_sound_on_valid (p : Evidence) (h : Valid p) :
    receive p = some (p.route, nativeBit p.route) := by
  unfold receive
  simp only [h, ↓reduceIte]
  rw [valid_recomputed_bit_is_native p h]

/-- 1b. Acceptance is exactly validity; the checker is neither always-true nor mute. -/
theorem receiver_accepts_iff_valid (p : Evidence) :
    (∃ out, receive p = some out) ↔ Valid p := by
  unfold receive
  by_cases h : Valid p
  · simp [h]
  · simp [h]

inductive Body
  | sender
  | receiver
deriving DecidableEq

structure Transmission where
  source : Body
  destination : Body
  packet : Evidence
deriving DecidableEq

def send (p : Evidence) : Transmission := ⟨.sender, .receiver, p⟩

/-- The boundary first checks that this is the intended direction, then invokes the
receiver's independent checker. -/
def receiveAtBoundary (t : Transmission) : Option (Route × Bool) :=
  if t.source = .sender ∧ t.destination = .receiver then receive t.packet else none

/-- 2. Both honest route orders cross the boundary, with distinct checked answers. -/
theorem honest_transmissions_are_distinguished :
    receiveAtBoundary (send (nativeEvidence .A)) = some (.A, false) ∧
    receiveAtBoundary (send (nativeEvidence .B)) = some (.B, true) := by
  decide

/-! ## Adversarial transmissions -/

def flipBit (p : Evidence) : Evidence := { p with bit := !p.bit }

def idleEvidence (r : Route) : Evidence :=
  ⟨r, xPoint, xPoint, xPoint, zzero, nativeBit r⟩

def swapRoute : Route → Route
  | .A => .B
  | .B => .A

def relabelRoute (r : Route) : Evidence :=
  { nativeEvidence r with route := swapRoute r }

/-- The old receiver sees only the sender's announced answer. -/
def answerOnly (p : Evidence) : Bool := p.bit

/-- 3a. Answer-only reception cannot distinguish the native trace from an invented one. -/
theorem answer_only_is_blind_to_idle_trace :
    ∀ r, answerOnly (nativeEvidence r) = answerOnly (idleEvidence r) := by
  intro r
  rfl

/-- 3b. The independent receiver rejects all three adversarial packets. -/
theorem receiver_rejects_all_three_attacks :
    (∀ r, receiveAtBoundary (send (flipBit (nativeEvidence r))) = none) ∧
    (∀ r, receiveAtBoundary (send (idleEvidence r)) = none) ∧
    (∀ r, receiveAtBoundary (send (relabelRoute r)) = none) := by
  constructor
  · intro r; cases r <;> decide
  · constructor
    · intro r; cases r <;> decide
    · intro r; cases r <;> decide

/-! ## The historical limit: verification is not occurrence -/

inductive History
  | performed (route : Route)
  | idle
deriving DecidableEq

/-- A world contains an actual-history field that is NOT transmitted, and a packet that is. -/
structure World where
  history : History
  packet : Evidence
deriving DecidableEq

def honestWorld (r : Route) : World := ⟨.performed r, nativeEvidence r⟩

/-- The very same packet, but in a world whose history says no journey occurred. -/
def fabricatedWorld (r : Route) : World := ⟨.idle, nativeEvidence r⟩

def HistoricallyHonest (w : World) : Prop :=
  match w.history with
  | .performed r => w.packet = nativeEvidence r
  | .idle => False

instance (w : World) : Decidable (HistoricallyHonest w) := by
  unfold HistoricallyHonest
  cases w.history <;> infer_instance

theorem honest_world_is_historically_honest :
    ∀ r, HistoricallyHonest (honestWorld r) := by
  intro r
  rfl

theorem fabricated_world_is_not_historically_honest :
    ∀ r, ¬ HistoricallyHonest (fabricatedWorld r) := by
  intro r
  exact id

/-- 4a. The transmitted bytes are identical although the modelled histories differ. -/
theorem same_packet_different_history :
    ∀ r, (honestWorld r).packet = (fabricatedWorld r).packet ∧
      (honestWorld r).history ≠ (fabricatedWorld r).history := by
  intro r
  exact ⟨rfl, by cases r <;> decide⟩

/-- 4b. Therefore EVERY observer whose input is only the packet gives the same answer
in the two worlds.  This is an information boundary, not a weakness of this verifier. -/
theorem every_packet_only_observer_is_blind {α : Type} (observer : Evidence → α) :
    ∀ r, observer (honestWorld r).packet = observer (fabricatedWorld r).packet := by
  intro r
  rfl

/-- 4c. In particular, the independent receiver accepts the fabricated packet. -/
theorem receiver_accepts_derivable_fabrication :
    ∀ r, receiveAtBoundary (send (fabricatedWorld r).packet) =
      some (r, nativeBit r) := by
  intro r
  exact receiver_sound_on_valid (nativeEvidence r) (native_evidence_valid r)

/-- 4d. Validity does not imply historical honesty.  A valid counterexample exists for
each route. -/
theorem validity_does_not_imply_occurrence :
    ∀ r, Valid (fabricatedWorld r).packet ∧
      ¬ HistoricallyHonest (fabricatedWorld r) := by
  intro r
  exact ⟨native_evidence_valid r, fabricated_world_is_not_historically_honest r⟩

/-! ## Certificate -/

theorem receiving_body_certificate :
    (∀ p, Valid p → receive p = some (p.route, nativeBit p.route)) ∧
    ((receiveAtBoundary (send (nativeEvidence .A)) = some (.A, false)) ∧
      receiveAtBoundary (send (nativeEvidence .B)) = some (.B, true)) ∧
    ((∀ r, receiveAtBoundary (send (flipBit (nativeEvidence r))) = none) ∧
      (∀ r, receiveAtBoundary (send (idleEvidence r)) = none) ∧
      (∀ r, receiveAtBoundary (send (relabelRoute r)) = none)) ∧
    (∀ r, answerOnly (nativeEvidence r) = answerOnly (idleEvidence r)) ∧
    (∀ r, (honestWorld r).packet = (fabricatedWorld r).packet ∧
      (honestWorld r).history ≠ (fabricatedWorld r).history) ∧
    (∀ r, receiveAtBoundary (send (fabricatedWorld r).packet) =
      some (r, nativeBit r)) ∧
    (∀ r, Valid (fabricatedWorld r).packet ∧
      ¬ HistoricallyHonest (fabricatedWorld r)) :=
  ⟨receiver_sound_on_valid, honest_transmissions_are_distinguished,
   receiver_rejects_all_three_attacks, answer_only_is_blind_to_idle_trace,
   same_packet_different_history, receiver_accepts_derivable_fabrication,
   validity_does_not_imply_occurrence⟩

#print axioms the_two_native_orientations
#print axioms native_evidence_valid
#print axioms valid_recomputed_bit_is_native
#print axioms receiver_sound_on_valid
#print axioms receiver_accepts_iff_valid
#print axioms honest_transmissions_are_distinguished
#print axioms answer_only_is_blind_to_idle_trace
#print axioms receiver_rejects_all_three_attacks
#print axioms honest_world_is_historically_honest
#print axioms fabricated_world_is_not_historically_honest
#print axioms same_packet_different_history
#print axioms every_packet_only_observer_is_blind
#print axioms receiver_accepts_derivable_fabrication
#print axioms validity_does_not_imply_occurrence
#print axioms receiving_body_certificate

end FoundationStoneSixteenE
