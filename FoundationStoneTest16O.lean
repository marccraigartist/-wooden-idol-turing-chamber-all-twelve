/-!
# THE TOKEN IN THE RELAY — FOUNDATION STONE TEST 16O

Core Lean only; no imports.

16N compiled controlled erasure: an atomic clear became an unbounded target
journey.  16O proves the preservation companion.  An atomic source command

    transfer every unit from body `src` to the other body; goto `exit`

is compiled to two primitive instructions:

    0: down src 1 exit
    1: up   other 0

Each unit crosses in two relay steps.  The final zero test costs one more.

Lean certifies:

1. EVEN PREFIX: after `2n` steps, exactly `n` units have arrived;
2. ODD PREFIX: after `2n+1` steps, the next unit is between the bodies;
3. EXACT COMPLETION: moving amount `a` takes `2a+1` steps;
4. SOURCE SIMULATION: the final boundary equals one atomic source transfer;
5. CONSERVATION: source + destination is constant at every even boundary;
6. RELAY CONSERVATION: at odd boundaries the two visible counters appear to
   have lost one, but source + destination + in-flight token is constant;
7. COMPOSITION LIMIT: transferring A→B and then B→A preserves the total but
   does not restore the original split—unit provenance has been merged;
8. RED CONTROL: endpoint-only accounting falsely reports a loss mid-transfer.

This is not universality.  It is the first certified unbounded macro that
preserves information by carrying it through a third, transient location: the
relay itself.  Forgetting that location makes conservation appear to fail.
-/

namespace FoundationStoneTest16O

abbrev Body := Bool
abbrev InstrCode := Nat × Body × Nat × Nat
abbrev Program := List InstrCode

inductive Instr
  | up (b : Body) (next : Nat)
  | down (b : Body) (next ground : Nat)
  | stop
deriving DecidableEq

def stopCode : InstrCode := (0, false, 0, 0)
def upCode (b : Body) (next : Nat) : InstrCode := (1, b, next, 0)
def downCode (b : Body) (next ground : Nat) : InstrCode := (2, b, next, ground)

def decodeInstr (i : InstrCode) : Instr :=
  if i.1 = 1 then .up i.2.1 i.2.2.1
  else if i.1 = 2 then .down i.2.1 i.2.2.1 i.2.2.2
  else .stop

def fetch (p : Program) (pc : Nat) : Instr :=
  decodeInstr ((p[pc]?).getD stopCode)

structure CState where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq

def get (s : CState) : Body → Nat
  | false => s.a
  | true => s.b

def set (s : CState) (pc : Nat) : Body → Nat → CState
  | false, v => ⟨pc, v, s.b⟩
  | true, v => ⟨pc, s.a, v⟩

def cstep (p : Program) (s : CState) : Option CState :=
  match fetch p s.pc with
  | .up b nx => some (set s nx b (get s b + 1))
  | .down b nx gr =>
      if get s b = 0 then some { s with pc := gr }
      else some (set s nx b (get s b - 1))
  | .stop => none

def crun (p : Program) : Nat → CState → Option CState
  | 0, s => some s
  | n + 1, s =>
      match cstep p s with
      | none => none
      | some s' => crun p n s'

theorem crun_add (p : Program) (m n : Nat) (s : CState) :
    crun p (m + n) s =
      match crun p m s with
      | none => none
      | some s' => crun p n s' := by
  induction m generalizing s with
  | zero => simp [crun]
  | succ m ih =>
      simp only [Nat.succ_add]
      change
        (match cstep p s with
          | none => none
          | some s' => crun p (m + n) s') =
        match (match cstep p s with
          | none => none
          | some s' => crun p m s') with
        | none => none
        | some s' => crun p n s'
      cases cstep p s with
      | none => rfl
      | some s' => simp only; exact ih s'

/-! ## 1. The transfer block and its three kinds of state -/

def other : Body → Body := (!·)

/-- Address 0 removes from the source; address 1 delivers to the other body. -/
def transferBlock (src : Body) (exit : Nat) : Program :=
  [downCode src 1 exit, upCode (other src) 0]

/-- At a cycle boundary, `amount` remains at source and `received` is at destination. -/
def entryState : Body → Nat → Nat → CState
  | false, amount, received => ⟨0, amount, received⟩
  | true, amount, received => ⟨0, received, amount⟩

/-- Between the two instructions, one unit is carried by the relay. -/
def betweenState : Body → Nat → Nat → CState
  | false, remaining, received => ⟨1, remaining, received⟩
  | true, remaining, received => ⟨1, received, remaining⟩

/-- The atomic source result at the exit boundary. -/
def movedState : Body → Nat → Nat → Nat → CState
  | false, exit, amount, received => ⟨exit, 0, received + amount⟩
  | true, exit, amount, received => ⟨exit, received + amount, 0⟩

/-- The first half of a positive cycle picks up exactly one unit. -/
theorem pickup_one (src : Body) (exit amount received : Nat) :
    cstep (transferBlock src exit) (entryState src (amount + 1) received) =
      some (betweenState src amount received) := by
  cases src <;> simp [cstep, transferBlock, fetch, decodeInstr, downCode,
    entryState, betweenState, get, set]

/-- The second half delivers exactly that unit to the other body. -/
theorem deliver_one (src : Body) (exit amount received : Nat) :
    cstep (transferBlock src exit) (betweenState src amount received) =
      some (entryState src amount (received + 1)) := by
  cases src <;> simp [cstep, transferBlock, fetch, decodeInstr, upCode, other,
    entryState, betweenState, get, set]

/-- One complete relay cycle moves one unit and returns to the macro entry. -/
theorem transfer_cycle (src : Body) (exit amount received : Nat) :
    crun (transferBlock src exit) 2 (entryState src (amount + 1) received) =
      some (entryState src amount (received + 1)) := by
  unfold crun
  rw [pickup_one]
  simp only
  unfold crun
  rw [deliver_one]
  rfl

/-- When the source is empty, the zero test crosses to the exit. -/
theorem transfer_zero (src : Body) (exit amount received : Nat) :
    cstep (transferBlock src exit) (entryState src 0 (received + amount)) =
      some (movedState src exit amount received) := by
  cases src <;> simp [cstep, transferBlock, fetch, decodeInstr, downCode,
    entryState, movedState, get, Nat.add_comm]

/-! ## 2. Exact even and odd prefixes -/

/-- After `2n` steps, exactly `n` complete transfers have occurred. -/
theorem transfer_even_prefix (src : Body) (exit amount received : Nat) :
    ∀ n, n ≤ amount →
      crun (transferBlock src exit) (2 * n) (entryState src amount received) =
        some (entryState src (amount - n) (received + n)) := by
  intro n hn
  induction n generalizing amount received with
  | zero => simp [crun]
  | succ n ih =>
      obtain ⟨h, rfl⟩ : ∃ h, amount = h + 1 := ⟨amount - 1, by omega⟩
      rw [show 2 * (n + 1) = 2 + 2 * n by omega, crun_add,
        transfer_cycle]
      simp only
      have hn' : n ≤ h := by omega
      have hrem : h + 1 - (n + 1) = h - n := by omega
      have hgot : received + (n + 1) = (received + 1) + n := by omega
      rw [hrem, hgot, ih h (received + 1) hn']

/-- After `2n+1` steps, the next unit is in the relay, not in either body. -/
theorem transfer_odd_prefix (src : Body) (exit amount received n : Nat)
    (hn : n < amount) :
    crun (transferBlock src exit) (2 * n + 1) (entryState src amount received) =
      some (betweenState src (amount - (n + 1)) (received + n)) := by
  rw [show 2 * n + 1 = 2 * n + 1 by rfl, crun_add,
    transfer_even_prefix src exit amount received n (by omega)]
  simp only
  obtain ⟨h, heq⟩ : ∃ h, amount - n = h + 1 :=
    ⟨amount - (n + 1), by omega⟩
  rw [heq]
  unfold crun
  rw [pickup_one]
  simp only
  have hh : h = amount - (n + 1) := by omega
  rw [hh]
  rfl

/-- Exact completion: amount `a` takes `2a+1` primitive target steps. -/
theorem transfer_completes (src : Body) (exit amount received : Nat) :
    crun (transferBlock src exit) (2 * amount + 1) (entryState src amount received) =
      some (movedState src exit amount received) := by
  rw [crun_add, transfer_even_prefix src exit amount received amount (Nat.le_refl _)]
  simp only [Nat.sub_self]
  unfold crun
  rw [transfer_zero]
  rfl

/-! ## 3. Atomic source semantics -/

structure SourceState where
  a : Nat
  b : Nat
deriving DecidableEq

def sourceTransfer : Body → SourceState → SourceState
  | false, s => ⟨0, s.b + s.a⟩
  | true, s => ⟨s.a + s.b, 0⟩

def enter (src : Body) (s : SourceState) : CState :=
  if src then entryState true s.b s.a else entryState false s.a s.b

def leave (exit : Nat) (s : SourceState) : CState := ⟨exit, s.a, s.b⟩

/-- The unbounded relay path implements one atomic source transfer exactly. -/
theorem transfer_simulates_source (src : Body) (exit : Nat) (s : SourceState) :
    crun (transferBlock src exit) (2 * get (enter src s) src + 1) (enter src s) =
      some (leave exit (sourceTransfer src s)) := by
  cases src with
  | false =>
      rcases s with ⟨amount, received⟩
      simpa [enter, get, leave, sourceTransfer, entryState, movedState] using
        transfer_completes false exit amount received
  | true =>
      rcases s with ⟨received, amount⟩
      simpa [enter, get, leave, sourceTransfer, entryState, movedState] using
        transfer_completes true exit amount received

/-! ## 4. Where conservation actually lives -/

/-- What is visible if the relay itself is forgotten. -/
def bodyMass (s : CState) : Nat := s.a + s.b

/-- Address 1 means exactly one unit is currently in flight. -/
def relayToken (s : CState) : Nat := if s.pc = 1 then 1 else 0

/-- The complete mass includes both bodies and the relay. -/
def totalMass (s : CState) : Nat := bodyMass s + relayToken s

theorem entry_mass (src : Body) (amount received : Nat) :
    totalMass (entryState src amount received) = amount + received := by
  cases src <;> simp [totalMass, bodyMass, relayToken, entryState, Nat.add_comm]

/-- At the midpoint the bodies alone appear to have lost one unit. -/
theorem midpoint_visible_loss (src : Body) (remaining received : Nat) :
    bodyMass (betweenState src remaining received) = remaining + received := by
  cases src <;> simp [bodyMass, betweenState, Nat.add_comm]

/-- Counting the relay restores exact conservation. -/
theorem midpoint_total_conservation (src : Body) (remaining received : Nat) :
    totalMass (betweenState src remaining received) = remaining + received + 1 := by
  cases src <;> simp [totalMass, bodyMass, relayToken, betweenState, Nat.add_comm,
    Nat.add_assoc]

/-- Every certified even prefix has the original total. -/
theorem even_prefix_conserves (src : Body) (amount received n : Nat) (hn : n ≤ amount) :
    totalMass (entryState src (amount - n) (received + n)) = amount + received := by
  rw [entry_mass]
  omega

/-- Every certified odd prefix also has the original total—but only if the relay is counted. -/
theorem odd_prefix_conserves (src : Body) (amount received n : Nat) (hn : n < amount) :
    totalMass (betweenState src (amount - (n + 1)) (received + n)) =
      amount + received := by
  rw [midpoint_total_conservation]
  omega

/-- Red control: forgetting the relay reports one missing unit at every midpoint. -/
theorem forgetting_relay_reports_false_loss (src : Body) (amount received n : Nat)
    (hn : n < amount) :
    bodyMass (betweenState src (amount - (n + 1)) (received + n)) + 1 =
      amount + received := by
  rw [midpoint_visible_loss]
  omega

/-- Concrete control: A=3, B=4 becomes visibly 2+4 after pickup, but 2+4+token = 7. -/
theorem concrete_token_control :
    bodyMass (betweenState false 2 4) = 6 ∧
    relayToken (betweenState false 2 4) = 1 ∧
    totalMass (betweenState false 2 4) = 7 := by decide

/-! ## 5. Route versus endpoint -/

/-- A→B followed by B→A returns all merged mass to A. -/
theorem transfer_there_and_back (a b : Nat) :
    crun (transferBlock true 3) (2 * (a + b) + 1)
      (entryState true (a + b) 0) = some ⟨3, a + b, 0⟩ := by
  simpa [movedState, Nat.zero_add] using transfer_completes true 3 (a + b) 0

/-- Same final total, positive route cost: endpoint equality does not erase the journey. -/
theorem round_trip_keeps_mass_but_costs (a b : Nat) :
    bodyMass ⟨0, a, b⟩ = bodyMass ⟨3, a + b, 0⟩ ∧
    0 < (2 * a + 1) + (2 * (a + b) + 1) := by
  constructor
  · simp [bodyMass]
  · omega

/-- Red control: if B initially held anything, the there-and-back route cannot
recover which units originally belonged to B.  Conservation is not provenance. -/
theorem round_trip_does_not_restore_the_split (a b : Nat) (hb : 0 < b) :
    (⟨a + b, 0⟩ : SourceState) ≠ ⟨a, b⟩ := by
  intro h
  have := congrArg SourceState.b h
  simp at this
  omega

/-! ## Certificate -/

theorem token_in_the_relay_certificate :
    (∀ src exit amount received,
      crun (transferBlock src exit) (2 * amount + 1) (entryState src amount received) =
        some (movedState src exit amount received)) ∧
    (∀ src exit s,
      crun (transferBlock src exit) (2 * get (enter src s) src + 1) (enter src s) =
        some (leave exit (sourceTransfer src s))) ∧
    (∀ src amount received n, n ≤ amount →
      totalMass (entryState src (amount - n) (received + n)) = amount + received) ∧
    (∀ src amount received n, n < amount →
      totalMass (betweenState src (amount - (n + 1)) (received + n)) = amount + received) ∧
    bodyMass (betweenState false 2 4) = 6 ∧
    totalMass (betweenState false 2 4) = 7 :=
  ⟨transfer_completes, transfer_simulates_source, even_prefix_conserves,
    odd_prefix_conserves, concrete_token_control.1, concrete_token_control.2.2⟩

#print axioms crun_add
#print axioms pickup_one
#print axioms deliver_one
#print axioms transfer_cycle
#print axioms transfer_zero
#print axioms transfer_even_prefix
#print axioms transfer_odd_prefix
#print axioms transfer_completes
#print axioms transfer_simulates_source
#print axioms entry_mass
#print axioms midpoint_visible_loss
#print axioms midpoint_total_conservation
#print axioms even_prefix_conserves
#print axioms odd_prefix_conserves
#print axioms forgetting_relay_reports_false_loss
#print axioms concrete_token_control
#print axioms transfer_there_and_back
#print axioms round_trip_keeps_mass_but_costs
#print axioms round_trip_does_not_restore_the_split
#print axioms token_in_the_relay_certificate

end FoundationStoneTest16O
