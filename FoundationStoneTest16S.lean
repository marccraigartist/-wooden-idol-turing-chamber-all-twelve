/-!
# THE VERIFIED MACRO LIBRARY — FOUNDATION STONE TEST 16S

Core Lean only; no imports.

Tests 16M–16R supplied the assembler, unbounded clear and transfer journeys,
and the exact price of provenance.  Test 16S consolidates the executable layer
needed by the proposed Turing chamber.

The intermediate language has exactly three instructions:

* `inc b next`       — increment counter `b`, then jump;
* `dec b next zero`  — if zero jump to `zero`, otherwise decrement and jump
                       to `next`;
* `halt`.

A macro is a finite list whose labels are local, starting at zero.  `relocate`
adds a base address to every jump.  `link p q` appends `q` after `p` and
relocates all of `q`'s labels by `p.length`.

Lean certifies:

1. relocation commutes with fetching and composes additively;
2. linked fetching is exact on both the left and right blocks;
3. increment and decrement/zero branch have their declared one-step meanings;
4. `clear` sets either counter to zero in exactly `height+1` steps;
5. `transfer` moves every unit to the other counter in exactly `2*amount+1`
   steps, including its final zero test;
6. the clear and transfer macros compose: clear A, then transfer B→A, then
   halt, with an exact runtime and endpoint;
7. RED CONTROL — naïve concatenation without relocation reaches the wrong
   program counter and repeats the second increment;
8. RED CONTROL — relocating only the loop label but not the zero/exit label
   sends an empty clear block to address 1 instead of its relocated exit.

This is still not Minsky universality.  It is the verified macro substrate on
which the remaining source-machine compiler can be built without hiding
control-flow arithmetic inside an informal assembler.
-/

namespace FoundationStoneTest16S

/-! ## 1. Instructions, relocation and linking -/

inductive Body
  | A
  | B
deriving DecidableEq, Repr

inductive Instr
  | inc (b : Body) (next : Nat)
  | dec (b : Body) (next zeroLabel : Nat)
  | halt
deriving DecidableEq, Repr

abbrev Program := List Instr

def fetch (p : Program) (pc : Nat) : Instr := (p[pc]?).getD .halt

def shiftInstr (d : Nat) : Instr → Instr
  | .inc b next => .inc b (d + next)
  | .dec b next zeroLabel => .dec b (d + next) (d + zeroLabel)
  | .halt => .halt

def relocate (d : Nat) (p : Program) : Program := p.map (shiftInstr d)

/-- The right block is installed immediately after the left block. -/
def link (p q : Program) : Program := p ++ relocate p.length q

theorem shift_zero (i : Instr) : shiftInstr 0 i = i := by
  cases i <;> simp [shiftInstr]

theorem shift_add (a b : Nat) (i : Instr) :
    shiftInstr a (shiftInstr b i) = shiftInstr (a + b) i := by
  cases i <;> simp [shiftInstr, Nat.add_assoc]

theorem relocate_zero (p : Program) : relocate 0 p = p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
      unfold relocate at ih ⊢
      simp only [List.map_cons, shift_zero, ih]

theorem relocate_add (a b : Nat) (p : Program) :
    relocate a (relocate b p) = relocate (a + b) p := by
  simp [relocate, List.map_map, Function.comp_def, shift_add]

theorem relocate_length (d : Nat) (p : Program) :
    (relocate d p).length = p.length := by
  simp [relocate]

theorem fetch_relocate (d : Nat) (p : Program) (i : Nat) :
    fetch (relocate d p) i = shiftInstr d (fetch p i) := by
  simp [fetch, relocate]
  cases p[i]? <;> rfl

theorem fetch_link_left (p q : Program) (i : Nat) (hi : i < p.length) :
    fetch (link p q) i = fetch p i := by
  simp [fetch, link, List.getElem?_append, hi]

theorem fetch_link_right (p q : Program) (i : Nat) :
    fetch (link p q) (p.length + i) = shiftInstr p.length (fetch q i) := by
  have hnot : ¬ p.length + i < p.length := by omega
  simp [fetch, link, List.getElem?_append, relocate, hnot]
  cases q[i]? <;> rfl

theorem link_length (p q : Program) :
    (link p q).length = p.length + q.length := by
  simp [link, relocate]

/-! ## 2. Machine semantics -/

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

/-! ## 3. Primitive macro specifications -/

/-- A one-instruction increment block; local exit is 1. -/
def incMacro (b : Body) : Program := [.inc b 1]

/-- A one-instruction conditional decrement with caller-supplied local labels. -/
def decBranchMacro (b : Body) (nonzero zeroLabel : Nat) : Program :=
  [.dec b nonzero zeroLabel]

theorem increment_spec (p : Program) (b : Body) (entry exit : Nat)
    (hf : fetch p entry = .inc b exit) (s : State) (hpc : s.pc = entry) :
    step p s = some (set s exit b (get s b + 1)) := by
  unfold step
  rw [hpc, hf]
  rfl

theorem decrement_positive_spec (p : Program) (b : Body) (entry next zeroLabel : Nat)
    (hf : fetch p entry = .dec b next zeroLabel) (s : State)
    (hpc : s.pc = entry) (hpos : get s b ≠ 0) :
    step p s = some (set s next b (get s b - 1)) := by
  unfold step
  rw [hpc, hf]
  simp [execute, hpos]

theorem decrement_zero_spec (p : Program) (b : Body) (entry next zeroLabel : Nat)
    (hf : fetch p entry = .dec b next zeroLabel) (s : State)
    (hpc : s.pc = entry) (hz : get s b = 0) :
    step p s = some { s with pc := zeroLabel } := by
  unfold step
  rw [hpc, hf]
  simp [execute, hz]

/-! ## 4. Clear macro -/

/-- Local address 0 loops while positive; local address 1 is the exit. -/
def clearMacro (b : Body) : Program := [.dec b 0 1]

def orientedState : Body → Nat → Nat → Nat → State
  | .A, pc, amount, other => ⟨pc, amount, other⟩
  | .B, pc, amount, other => ⟨pc, other, amount⟩

theorem clear_step_positive (p : Program) (b : Body) (entry exit amount other : Nat)
    (hf : fetch p entry = .dec b entry exit) :
    step p (orientedState b entry (amount + 1) other) =
      some (orientedState b entry amount other) := by
  cases b <;> simp [step, execute, orientedState, get, set, hf]

theorem clear_step_zero (p : Program) (b : Body) (entry exit other : Nat)
    (hf : fetch p entry = .dec b entry exit) :
    step p (orientedState b entry 0 other) =
      some (orientedState b exit 0 other) := by
  cases b <;> simp [step, execute, orientedState, get, hf]

/-- Clear takes one decrement per unit plus its final zero test. -/
theorem clear_exact (p : Program) (b : Body) (entry exit amount other : Nat)
    (hf : fetch p entry = .dec b entry exit) :
    run p (amount + 1) (orientedState b entry amount other) =
      some (orientedState b exit 0 other) := by
  induction amount with
  | zero =>
      unfold run
      rw [clear_step_zero p b entry exit other hf]
      rfl
  | succ amount ih =>
      unfold run
      rw [clear_step_positive p b entry exit amount other hf]
      exact ih

/-! ## 5. Transfer macro -/

def other : Body → Body
  | .A => .B
  | .B => .A

/-- Local 0 picks up, local 1 delivers, local 2 exits. -/
def transferMacro (src : Body) : Program :=
  [.dec src 1 2, .inc (other src) 0]

def transferEntry : Body → Nat → Nat → Nat → State
  | .A, pc, amount, received => ⟨pc, amount, received⟩
  | .B, pc, amount, received => ⟨pc, received, amount⟩

def transferBetween : Body → Nat → Nat → Nat → State
  | .A, pc, remaining, received => ⟨pc, remaining, received⟩
  | .B, pc, remaining, received => ⟨pc, received, remaining⟩

def transferMoved : Body → Nat → Nat → State
  | .A, exit, total => ⟨exit, 0, total⟩
  | .B, exit, total => ⟨exit, total, 0⟩

theorem transfer_pickup (p : Program) (src : Body) (entry middle exit amount received : Nat)
    (h0 : fetch p entry = .dec src middle exit) :
    step p (transferEntry src entry (amount + 1) received) =
      some (transferBetween src middle amount received) := by
  cases src <;> simp [step, execute, transferEntry, transferBetween, get, set, h0]

theorem transfer_delivery (p : Program) (src : Body)
    (entry middle amount received : Nat)
    (h1 : fetch p middle = .inc (other src) entry) :
    step p (transferBetween src middle amount received) =
      some (transferEntry src entry amount (received + 1)) := by
  cases src <;> simp [step, execute, transferEntry, transferBetween, get, set, other, h1]

theorem transfer_cycle (p : Program) (src : Body) (entry middle exit amount received : Nat)
    (h0 : fetch p entry = .dec src middle exit)
    (h1 : fetch p middle = .inc (other src) entry) :
    run p 2 (transferEntry src entry (amount + 1) received) =
      some (transferEntry src entry amount (received + 1)) := by
  unfold run
  rw [transfer_pickup p src entry middle exit amount received h0]
  simp only
  unfold run
  rw [transfer_delivery p src entry middle amount received h1]
  rfl

theorem transfer_zero (p : Program) (src : Body) (entry middle exit total : Nat)
    (h0 : fetch p entry = .dec src middle exit) :
    step p (transferEntry src entry 0 total) =
      some (transferMoved src exit total) := by
  cases src <;> simp [step, execute, transferEntry, transferMoved, get, h0]

theorem transfer_even_prefix (p : Program) (src : Body)
    (entry middle exit amount received : Nat)
    (h0 : fetch p entry = .dec src middle exit)
    (h1 : fetch p middle = .inc (other src) entry) :
    ∀ n, n ≤ amount →
      run p (2 * n) (transferEntry src entry amount received) =
        some (transferEntry src entry (amount - n) (received + n)) := by
  intro n hn
  induction n generalizing amount received with
  | zero => simp [run]
  | succ n ih =>
      obtain ⟨h, rfl⟩ : ∃ h, amount = h + 1 := ⟨amount - 1, by omega⟩
      rw [show 2 * (n + 1) = 2 + 2 * n by omega, run_add,
        transfer_cycle p src entry middle exit h received h0 h1]
      simp only
      have hn' : n ≤ h := by omega
      have hrem : h + 1 - (n + 1) = h - n := by omega
      have hgot : received + (n + 1) = (received + 1) + n := by omega
      rw [hrem, hgot, ih h (received + 1) hn']

/-- Transfer takes two steps per unit plus its final zero test. -/
theorem transfer_exact (p : Program) (src : Body)
    (entry middle exit amount received : Nat)
    (h0 : fetch p entry = .dec src middle exit)
    (h1 : fetch p middle = .inc (other src) entry) :
    run p (2 * amount + 1) (transferEntry src entry amount received) =
      some (transferMoved src exit (received + amount)) := by
  rw [run_add,
    transfer_even_prefix p src entry middle exit amount received h0 h1 amount (Nat.le_refl _)]
  simp only [Nat.sub_self]
  unfold run
  rw [transfer_zero p src entry middle exit (received + amount) h0]
  rfl

/-! ## 6. Composition: clear A, transfer B→A, halt -/

def clearA : Program := clearMacro .A
def moveBtoA : Program := transferMacro .B
def clearThenTransfer : Program := link clearA moveBtoA

theorem composed_code_is_exact :
    clearThenTransfer = [.dec .A 0 1, .dec .B 2 3, .inc .A 1] := by
  decide

theorem composed_fetches :
    fetch clearThenTransfer 0 = .dec .A 0 1 ∧
    fetch clearThenTransfer 1 = .dec .B 2 3 ∧
    fetch clearThenTransfer 2 = .inc .A 1 ∧
    fetch clearThenTransfer 3 = .halt := by
  decide

/-- Exact composite endpoint before executing the implicit halt at address 3. -/
theorem clear_then_transfer_exact (a b : Nat) :
    run clearThenTransfer ((a + 1) + (2 * b + 1)) ⟨0, a, b⟩ =
      some ⟨3, b, 0⟩ := by
  rw [run_add]
  have hc : run clearThenTransfer (a + 1) ⟨0, a, b⟩ = some ⟨1, 0, b⟩ := by
    simpa [orientedState] using
      clear_exact clearThenTransfer .A 0 1 a b composed_fetches.1
  rw [hc]
  simp only
  simpa [transferEntry, transferMoved] using
    transfer_exact clearThenTransfer .B 1 2 3 b 0
      composed_fetches.2.1 composed_fetches.2.2.1

theorem clear_then_transfer_halts (a b : Nat) :
    run clearThenTransfer ((a + 1) + (2 * b + 1) + 1) ⟨0, a, b⟩ = none := by
  rw [run_add]
  rw [clear_then_transfer_exact]
  rfl

/-! ## 7. Red controls -/

def firstIncrement : Program := incMacro .A
def secondIncrement : Program := incMacro .B
def correctlyLinkedIncrements : Program := link firstIncrement secondIncrement
def naivelyAppendedIncrements : Program := firstIncrement ++ secondIncrement

/-- Correct linking relocates the second exit from local 1 to global 2. -/
theorem linked_increment_control :
    correctlyLinkedIncrements = [.inc .A 1, .inc .B 2] ∧
    run correctlyLinkedIncrements 2 ⟨0, 0, 0⟩ = some ⟨2, 1, 1⟩ := by
  decide

/-- Naïve append collides with the old label: after two steps it remains at 1,
and a third step increments B again. -/
theorem naive_append_fails :
    naivelyAppendedIncrements = [.inc .A 1, .inc .B 1] ∧
    run naivelyAppendedIncrements 2 ⟨0, 0, 0⟩ = some ⟨1, 1, 1⟩ ∧
    run naivelyAppendedIncrements 3 ⟨0, 0, 0⟩ = some ⟨1, 1, 2⟩ ∧
    run naivelyAppendedIncrements 2 ⟨0, 0, 0⟩ ≠ some ⟨2, 1, 1⟩ := by
  decide

/-- A dishonest relocation that shifts the loop target but forgets the zero target. -/
def badShiftInstr (d : Nat) : Instr → Instr
  | .inc b next => .inc b (d + next)
  | .dec b next zeroLabel => .dec b (d + next) zeroLabel
  | .halt => .halt

def badlyRelocatedClearAtFive : Program :=
  List.replicate 5 .halt ++ (clearMacro .A).map (badShiftInstr 5)

def correctlyRelocatedClearAtFive : Program :=
  List.replicate 5 .halt ++ relocate 5 (clearMacro .A)

theorem malformed_relocation_fails :
    fetch badlyRelocatedClearAtFive 5 = .dec .A 5 1 ∧
    fetch correctlyRelocatedClearAtFive 5 = .dec .A 5 6 ∧
    step badlyRelocatedClearAtFive ⟨5, 0, 7⟩ = some ⟨1, 0, 7⟩ ∧
    step correctlyRelocatedClearAtFive ⟨5, 0, 7⟩ = some ⟨6, 0, 7⟩ := by
  decide

/-! ## Certificate -/

theorem verified_macro_library_certificate :
    (∀ d p i, fetch (relocate d p) i = shiftInstr d (fetch p i)) ∧
    (∀ p q i, i < p.length → fetch (link p q) i = fetch p i) ∧
    (∀ p q i,
      fetch (link p q) (p.length + i) = shiftInstr p.length (fetch q i)) ∧
    (∀ p b entry exit amount other,
      fetch p entry = .dec b entry exit →
      run p (amount + 1) (orientedState b entry amount other) =
        some (orientedState b exit 0 other)) ∧
    (∀ p src entry middle exit amount received,
      fetch p entry = .dec src middle exit →
      fetch p middle = .inc (other src) entry →
      run p (2 * amount + 1) (transferEntry src entry amount received) =
        some (transferMoved src exit (received + amount))) ∧
    (∀ a b,
      run clearThenTransfer ((a + 1) + (2 * b + 1) + 1) ⟨0, a, b⟩ = none) ∧
    run naivelyAppendedIncrements 2 ⟨0, 0, 0⟩ ≠ some ⟨2, 1, 1⟩ ∧
    step badlyRelocatedClearAtFive ⟨5, 0, 7⟩ = some ⟨1, 0, 7⟩ :=
  ⟨fetch_relocate, fetch_link_left, fetch_link_right, clear_exact,
   transfer_exact, clear_then_transfer_halts,
   naive_append_fails.2.2.2, malformed_relocation_fails.2.2.1⟩

#print axioms shift_add
#print axioms relocate_add
#print axioms fetch_relocate
#print axioms fetch_link_left
#print axioms fetch_link_right
#print axioms increment_spec
#print axioms decrement_positive_spec
#print axioms decrement_zero_spec
#print axioms clear_exact
#print axioms transfer_exact
#print axioms composed_code_is_exact
#print axioms clear_then_transfer_exact
#print axioms clear_then_transfer_halts
#print axioms linked_increment_control
#print axioms naive_append_fails
#print axioms malformed_relocation_fails
#print axioms verified_macro_library_certificate

end FoundationStoneTest16S
