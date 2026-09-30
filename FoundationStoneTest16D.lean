/-!
# THE PROOF-CARRYING BIT — FOUNDATION STONE TEST 16D

Runs in the Lean live editor with no imports (core Lean only).

Test 16C found the exact boundary: one orientation bit recovers the two route orders,
but the naked bit cannot say whether it was computed from the journey or glued on later.
This file makes the bit proof-carrying.

An evidence packet contains:

* the claimed route order;
* start, midpoint and finish;
* the signed bend computed from those three points;
* the orientation bit.

`Valid` checks the packet against the native two-turn process.  A `Certified` packet is
an evidence packet together with a Lean proof of `Valid`.

Order of results:

1. Native packets for both orders validate and enter the certified type.
2. Every certified packet returns the orientation computed by its certified route.
3. Three red controls are rejected:
   * flip the bit but retain the journey;
   * supply the correct naked bit with an invented stationary journey;
   * relabel an A journey as B, or a B journey as A.
4. Erasing the trace makes the native and invented packets indistinguishable again.
   The additional capability belongs to checked provenance, not the Boolean value alone.

Guardrail: this certifies algebraic consistency with the declared route.  It is not
cryptographic authentication and does not prove which historical person or machine ran
the journey, or when.  That requires an external trust or signing layer.
-/
namespace FoundationStoneSixteenD

/-! ## Exact geometry over Z[sqrt 3] -/

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

theorem native_bends : nativeBend .A = ⟨0, -1⟩ ∧ nativeBend .B = ⟨0, 1⟩ := by
  decide

theorem native_bits : nativeBit .A = false ∧ nativeBit .B = true := by
  decide

/-! ## Evidence and its checker -/

structure Evidence where
  route : Route
  start : V3
  midpoint : V3
  finish : V3
  bend : Z3
  bit : Bool
deriving DecidableEq

/-- The packet is internally consistent with the exact native production route. -/
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

/-- 1a. Both genuine journeys produce valid evidence. -/
theorem native_evidence_valid : ∀ r, Valid (nativeEvidence r) := by
  intro r
  cases r <;> decide

/-- A Boolean checker suitable for a receiving boundary. -/
def verify (p : Evidence) : Bool := decide (Valid p)

theorem verifier_accepts_native : ∀ r, verify (nativeEvidence r) = true := by
  intro r
  cases r <;> decide

/-- A proof-carrying packet: evidence plus kernel-checked validity. -/
abbrev Certified := {p : Evidence // Valid p}

def certifyNative (r : Route) : Certified := ⟨nativeEvidence r, native_evidence_valid r⟩
def readCertified (p : Certified) : Bool := p.val.bit

/-- 1b. The receiver obtains the native orientation from either certified journey. -/
theorem certified_native_values :
    readCertified (certifyNative .A) = false ∧
    readCertified (certifyNative .B) = true := by
  decide

/-! ## Soundness of the carried proof -/

/-- 2a. Validity forces the bit to be the one recomputed from the packet's own trace. -/
theorem valid_bit_is_recomputed (p : Evidence) (h : Valid p) :
    p.bit = (det3 p.start p.midpoint p.finish == positiveBend) := by
  calc
    p.bit = (p.bend == positiveBend) := h.2.2.2.2
    _ = (det3 p.start p.midpoint p.finish == positiveBend) :=
      congrArg (fun b => b == positiveBend) h.2.2.2.1

/-- 2b. More strongly, validity forces the native bit belonging to the certified route. -/
theorem valid_bit_is_native (p : Evidence) (h : Valid p) : p.bit = nativeBit p.route := by
  rcases h with ⟨hs, hm, hf, hb, hbit⟩
  unfold nativeBit nativeBend nativeFinish nativeMid
  rw [← hs, ← hm, ← hf, ← hb]
  exact hbit

theorem every_certified_bit_is_native (p : Certified) :
    readCertified p = nativeBit p.val.route :=
  valid_bit_is_native p.val p.property

/-! ## Three red controls -/

/-- Keep the entire journey but reverse its reported answer. -/
def flipBit (p : Evidence) : Evidence := { p with bit := !p.bit }

/-- Report the correct naked answer but invent a journey that stood still. -/
def idleEvidence (r : Route) : Evidence :=
  ⟨r, xPoint, xPoint, xPoint, zzero, nativeBit r⟩

def swapRoute : Route → Route
  | .A => .B
  | .B => .A

/-- Keep the genuine trace but claim it belongs to the opposite route. -/
def relabelRoute (r : Route) : Evidence := { nativeEvidence r with route := swapRoute r }

/-- 3a. The old answer-only channel cannot see that the invented packet is false. -/
theorem naked_bit_cannot_see_idle_forgery :
    ∀ r, (nativeEvidence r).bit = (idleEvidence r).bit := by
  intro r
  rfl

/-- 3b. The proof-carrying checker rejects a flipped answer. -/
theorem flipped_bit_is_rejected : ∀ r, ¬ Valid (flipBit (nativeEvidence r)) := by
  intro r
  cases r <;> decide

/-- 3c. It rejects the correct answer when the claimed journey was invented. -/
theorem idle_trace_is_rejected : ∀ r, ¬ Valid (idleEvidence r) := by
  intro r
  cases r <;> decide

/-- 3d. It rejects relabelling one order's trace as the other order. -/
theorem relabelled_route_is_rejected : ∀ r, ¬ Valid (relabelRoute r) := by
  intro r
  cases r <;> decide

theorem verifier_rejects_all_three_controls :
    (∀ r, verify (flipBit (nativeEvidence r)) = false) ∧
    (∀ r, verify (idleEvidence r) = false) ∧
    (∀ r, verify (relabelRoute r) = false) := by
  constructor
  · intro r; cases r <;> decide
  · constructor
    · intro r; cases r <;> decide
    · intro r; cases r <;> decide

/-! ## Erasure restores the old blindness -/

def eraseToBit (p : Evidence) : Bool := p.bit

/-- 4a. Native and invented histories become identical when only the answer is sent. -/
theorem erasure_identifies_native_and_idle :
    ∀ r, eraseToBit (nativeEvidence r) = eraseToBit (idleEvidence r) :=
  naked_bit_cannot_see_idle_forgery

/-- 4b. Yet their verification results are opposite.  This is the capability supplied by
checked provenance beyond trusting the answer alone. -/
theorem provenance_changes_acceptance :
    ∀ r, verify (nativeEvidence r) = true ∧ verify (idleEvidence r) = false := by
  intro r
  cases r <;> decide

/-! ## Certificate -/

theorem proof_carrying_bit_certificate :
    (∀ r, Valid (nativeEvidence r)) ∧
    (readCertified (certifyNative .A) = false ∧
      readCertified (certifyNative .B) = true) ∧
    (∀ p : Certified, readCertified p = nativeBit p.val.route) ∧
    (∀ r, ¬ Valid (flipBit (nativeEvidence r))) ∧
    (∀ r, ¬ Valid (idleEvidence r)) ∧
    (∀ r, ¬ Valid (relabelRoute r)) ∧
    (∀ r, eraseToBit (nativeEvidence r) = eraseToBit (idleEvidence r)) ∧
    (∀ r, verify (nativeEvidence r) = true ∧ verify (idleEvidence r) = false) :=
  ⟨native_evidence_valid, certified_native_values, every_certified_bit_is_native,
   flipped_bit_is_rejected, idle_trace_is_rejected, relabelled_route_is_rejected,
   erasure_identifies_native_and_idle, provenance_changes_acceptance⟩

#print axioms native_bends
#print axioms native_bits
#print axioms native_evidence_valid
#print axioms verifier_accepts_native
#print axioms certified_native_values
#print axioms valid_bit_is_recomputed
#print axioms valid_bit_is_native
#print axioms every_certified_bit_is_native
#print axioms naked_bit_cannot_see_idle_forgery
#print axioms flipped_bit_is_rejected
#print axioms idle_trace_is_rejected
#print axioms relabelled_route_is_rejected
#print axioms verifier_rejects_all_three_controls
#print axioms erasure_identifies_native_and_idle
#print axioms provenance_changes_acceptance
#print axioms proof_carrying_bit_certificate

end FoundationStoneSixteenD
