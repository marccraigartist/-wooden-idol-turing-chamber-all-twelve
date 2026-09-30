import Mathlib

/-!
# THE RADIX RELAY — FOUNDATION STONE TEST 16X

Test 16W encoded Mathlib's four-symbol Turing stacks in base five:

    push(d,n) = d + 5n,      d in {1,2,3,4}.

This test makes that arithmetic run as finite two-counter `INC/JZDEC` code.
The two counters are not artificially returned to one preferred side.  Every
stack operation exchanges the carrier:

* PUSH consumes `n` from the source body, writes `5n+d` to the other body;
* POP consumes `5q+d`, writes `q` to the other body, and its exit label records
  the popped digit `d`.

Lean certifies, for every natural payload and all four symbols:

1. the push macro has the exact endpoint and exact runtime `6n+d+1`;
2. the pop macro has the exact endpoint and exact runtime `6q+d+1`;
3. pop after push recovers both the symbol and the original payload, while the
   carrier crosses the chamber twice;
4. both directions A-to-B and B-to-A obey the same theorem;
5. RED CONTROL: a fourfold multiplier cannot implement the base-five stack.

This closes the first OPERATIONAL slice of the Turing-to-relay door.  It does
not yet compile Mathlib's complete four-stack transition table: four logical
stack codes and the finite control label still have to be packed, selected and
updated within the two-counter representation.
-/

namespace FoundationStoneTest16X

/-! ## 1. Two-counter relay language -/

inductive Body
  | A
  | B
deriving DecidableEq, Repr

def other : Body → Body
  | .A => .B
  | .B => .A

inductive Instr
  | inc (b : Body) (next : Nat)
  | dec (b : Body) (next zeroLabel : Nat)
  | halt
deriving DecidableEq, Repr

abbrev Program := List Instr

structure State where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq, Repr

def get (s : State) : Body → Nat
  | .A => s.a
  | .B => s.b

def set (s : State) (pc : Nat) : Body → Nat → State
  | .A, v => ⟨pc, v, s.b⟩
  | .B, v => ⟨pc, s.a, v⟩

def fetch (p : Program) (pc : Nat) : Instr := (p[pc]?).getD .halt

def execute (i : Instr) (s : State) : Option State :=
  match i with
  | .inc b next => some (set s next b (get s b + 1))
  | .dec b next zeroLabel =>
      if get s b = 0 then some { s with pc := zeroLabel }
      else some (set s next b (get s b - 1))
  | .halt => none

def step (p : Program) (s : State) : Option State := execute (fetch p s.pc) s

def run (p : Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
      match step p s with
      | none => none
      | some s' => run p n s'

theorem run_add (p : Program) (m n : Nat) (s : State) :
    run p (m + n) s =
      match run p m s with
      | none => none
      | some s' => run p n s' := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih =>
      simp only [Nat.succ_add]
      change
        (match step p s with
          | none => none
          | some s' => run p (m + n) s') =
        match (match step p s with
          | none => none
          | some s' => run p m s') with
        | none => none
        | some s' => run p n s'
      cases step p s with
      | none => rfl
      | some s' => simp only; exact ih s'

/-- View the same theorem from either carrier. -/
def oriented : Body → Nat → Nat → Nat → State
  | .A, pc, payload, scratch => ⟨pc, payload, scratch⟩
  | .B, pc, payload, scratch => ⟨pc, scratch, payload⟩

theorem oriented_get_source (src : Body) (pc payload scratch : Nat) :
    get (oriented src pc payload scratch) src = payload := by cases src <;> rfl

theorem oriented_get_other (src : Body) (pc payload scratch : Nat) :
    get (oriented src pc payload scratch) (other src) = scratch := by cases src <;> rfl

/-! ## 2. Four symbols, as in Test 16W -/

inductive Sym
  | consₗ
  | cons
  | bit0
  | bit1
deriving DecidableEq, Repr

def digit : Sym → Nat
  | .consₗ => 1
  | .cons => 2
  | .bit0 => 3
  | .bit1 => 4

theorem digit_bounds (s : Sym) : 0 < digit s ∧ digit s < 5 := by cases s <;> decide

def pushCode (s : Sym) (n : Nat) : Nat := digit s + 5 * n

/-! ## 3. Executable push -/

/-- The six-instruction multiplication loop.  Address 6 begins the digit tail. -/
def pushCore (src : Body) : Program :=
  [.dec src 1 6,
   .inc (other src) 2,
   .inc (other src) 3,
   .inc (other src) 4,
   .inc (other src) 5,
   .inc (other src) 0]

/-- Add the nonzero digit and exit at address `6 + digit`. -/
def digitTail (src : Body) : Sym → Program
  | .consₗ => [.inc (other src) 7]
  | .cons => [.inc (other src) 7, .inc (other src) 8]
  | .bit0 => [.inc (other src) 7, .inc (other src) 8,
      .inc (other src) 9]
  | .bit1 => [.inc (other src) 7, .inc (other src) 8,
      .inc (other src) 9, .inc (other src) 10]

def pushMacro (src : Body) (s : Sym) : Program := pushCore src ++ digitTail src s

def pushExit (s : Sym) : Nat := 6 + digit s

/-- Six primitive instructions consume one unit and create five. -/
theorem push_cycle (src : Body) (s : Sym) (n received : Nat) :
    run (pushMacro src s) 6 (oriented src 0 (n + 1) received) =
      some (oriented src 0 n (received + 5)) := by
  cases src <;> cases s <;>
    simp [run, step, execute, fetch, pushMacro, pushCore, digitTail, other,
      oriented, get, set]

/-- Repeating the six-step cycle performs multiplication by five. -/
theorem push_loops (src : Body) (s : Sym) : ∀ n received,
    run (pushMacro src s) (6 * n) (oriented src 0 n received) =
      some (oriented src 0 0 (received + 5 * n)) := by
  intro n
  induction n with
  | zero => intro received; simp [run]
  | succ n ih =>
      intro received
      rw [show 6 * (n + 1) = 6 + 6 * n by omega, run_add,
        push_cycle src s n received]
      simp only
      rw [ih (received + 5)]
      cases src <;> simp [oriented] <;> omega

/-- The zero test enters the tail; the tail adds exactly the symbol digit. -/
theorem push_tail (src : Body) (s : Sym) (received : Nat) :
    run (pushMacro src s) (digit s + 1) (oriented src 0 0 received) =
      some (oriented src (pushExit s) 0 (received + digit s)) := by
  cases src <;> cases s <;>
    simp [run, step, execute, fetch, pushMacro, pushCore, digitTail, pushExit,
      digit, other, oriented, get, set]

/-- Exact executable PUSH, from either body to the other. -/
theorem push_exact (src : Body) (s : Sym) (n : Nat) :
    run (pushMacro src s) (6 * n + digit s + 1) (oriented src 0 n 0) =
      some (oriented src (pushExit s) 0 (pushCode s n)) := by
  rw [show 6 * n + digit s + 1 = 6 * n + (digit s + 1) by omega, run_add,
    push_loops src s n 0]
  simp only [Nat.zero_add]
  rw [push_tail]
  cases src <;> simp [oriented, pushCode, Nat.add_comm]

/-! ## 4. Executable pop -/

/-- Five probes, then one quotient increment.  Exits 6--10 report remainders
0--4.  Valid nonempty stack codes use only exits 7--10. -/
def popMacro (src : Body) : Program :=
  [.dec src 1 6,
   .dec src 2 7,
   .dec src 3 8,
   .dec src 4 9,
   .dec src 5 10,
   .inc (other src) 0]

def popExit (s : Sym) : Nat := 6 + digit s

/-- Six steps consume a complete group of five and count one quotient unit. -/
theorem pop_cycle (src : Body) (n quotient : Nat) :
    run (popMacro src) 6 (oriented src 0 (n + 5) quotient) =
      some (oriented src 0 n (quotient + 1)) := by
  cases src <;>
    simp [run, step, execute, fetch, popMacro, other, oriented, get, set]

/-- Repeating complete groups leaves the remainder in the source body. -/
theorem pop_loops_general (src : Body) (s : Sym) : ∀ q received,
    run (popMacro src) (6 * q)
      (oriented src 0 (5 * q + digit s) received) =
      some (oriented src 0 (digit s) (received + q)) := by
  intro q
  induction q with
  | zero => intro received; simp [run]
  | succ q ih =>
      intro received
      rw [show 6 * (q + 1) = 6 + 6 * q by omega]
      rw [show 5 * (q + 1) + digit s = (5 * q + digit s) + 5 by omega]
      rw [run_add, pop_cycle src (5 * q + digit s) received]
      simp only
      rw [ih (received + 1)]
      cases src <;> simp [oriented] <;> omega

theorem pop_loops (src : Body) (s : Sym) (q : Nat) :
    run (popMacro src) (6 * q)
      (oriented src 0 (5 * q + digit s) 0) =
      some (oriented src 0 (digit s) q) := by
  simpa using pop_loops_general src s q 0

/-- The final partial group reports exactly which nonzero digit remained. -/
theorem pop_remainder (src : Body) (s : Sym) (q : Nat) :
    run (popMacro src) (digit s + 1) (oriented src 0 (digit s) q) =
      some (oriented src (popExit s) 0 q) := by
  cases src <;> cases s <;>
    simp [run, step, execute, fetch, popMacro, popExit, digit, other, oriented,
      get, set]

/-- Exact executable POP on every valid encoded top symbol. -/
theorem pop_exact (src : Body) (s : Sym) (q : Nat) :
    run (popMacro src) (6 * q + digit s + 1)
      (oriented src 0 (pushCode s q) 0) =
      some (oriented src (popExit s) 0 q) := by
  rw [show 6 * q + digit s + 1 = 6 * q + (digit s + 1) by omega, run_add]
  have hcode : pushCode s q = 5 * q + digit s := by
    simp [pushCode, Nat.add_comm]
  rw [hcode, pop_loops src s q]
  simp only
  exact pop_remainder src s q

/-! ## 5. The exchange law -/

/-- Read an endpoint from the opposite body's viewpoint, resetting the local pc. -/
def handoff (src : Body) (s : State) : State :=
  oriented (other src) 0 (get s (other src)) (get s src)

theorem handoff_after_push (src : Body) (s : Sym) (n : Nat) :
    handoff src (oriented src (pushExit s) 0 (pushCode s n)) =
      oriented (other src) 0 (pushCode s n) 0 := by
  cases src <;> rfl

/-- PUSH followed by the opposite-direction POP recovers both symbol and payload.
The exit label `6 + digit s` is the returned symbol. -/
theorem push_then_pop_round_trip (src : Body) (s : Sym) (n : Nat) :
    run (popMacro (other src)) (6 * n + digit s + 1)
      (handoff src (oriented src (pushExit s) 0 (pushCode s n))) =
      some (oriented (other src) (popExit s) 0 n) := by
  rw [handoff_after_push]
  exact pop_exact (other src) s n

/-! ## 6. Red control -/

/-- Wrong on purpose: a fourfold multiplier with the same digit. -/
def badPushCode (s : Sym) (n : Nat) : Nat := digit s + 4 * n

theorem wrong_multiplier_fails :
    badPushCode .bit0 2 ≠ pushCode .bit0 2 := by decide

/-- The executable macro really produces base five, not the bad base four. -/
theorem relay_rejects_wrong_multiplier :
    run (pushMacro .A .bit0) (6 * 2 + digit .bit0 + 1)
      (oriented .A 0 2 0) ≠
      some (oriented .A (pushExit .bit0) 0 (badPushCode .bit0 2)) := by
  rw [push_exact]
  intro h
  have hb := congrArg State.b (Option.some.inj h)
  exact wrong_multiplier_fails hb.symm

/-! ## Certificate -/

theorem radix_relay_certificate :
    (∀ src s n,
      run (pushMacro src s) (6 * n + digit s + 1) (oriented src 0 n 0) =
        some (oriented src (pushExit s) 0 (pushCode s n))) ∧
    (∀ src s q,
      run (popMacro src) (6 * q + digit s + 1)
        (oriented src 0 (pushCode s q) 0) =
        some (oriented src (popExit s) 0 q)) ∧
    (∀ src s n,
      run (popMacro (other src)) (6 * n + digit s + 1)
        (handoff src (oriented src (pushExit s) 0 (pushCode s n))) =
        some (oriented (other src) (popExit s) 0 n)) ∧
    run (pushMacro .A .bit0) (6 * 2 + digit .bit0 + 1)
      (oriented .A 0 2 0) ≠
      some (oriented .A (pushExit .bit0) 0 (badPushCode .bit0 2)) :=
  ⟨push_exact, pop_exact, push_then_pop_round_trip,
   relay_rejects_wrong_multiplier⟩

#print axioms push_cycle
#print axioms push_exact
#print axioms pop_cycle
#print axioms pop_exact
#print axioms push_then_pop_round_trip
#print axioms relay_rejects_wrong_multiplier
#print axioms radix_relay_certificate

end FoundationStoneTest16X
