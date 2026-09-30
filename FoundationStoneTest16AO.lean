import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AO: A PRIME GATE IN LITERAL MM2

Lean 4.35.0-rc2 / pinned Mathlib.

This is the first physical gate for the prime-exponent representation of 16AM.
It uses only the standard two-counter instructions: increment, and
decrement-with-zero-fallthrough.  The program divides counter A by two, leaves
the quotient in B, and exposes the remainder in its exit label.

The theorem is deliberately about a literal instruction list.  Division and
remainder occur only in the specification proved about that list; they are not
operations available to the machine.
-/

namespace FoundationStoneTest16AO

abbrev Body := Bool
abbrev Instr := Body ⊕ (Body × Nat)
abbrev Program := List Instr

structure State where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq, Repr

def get (s : State) (body : Body) : Nat := if body then s.b else s.a

def set (s : State) (pc : Nat) (body : Body) (value : Nat) : State :=
  if body then ⟨pc, s.a, value⟩ else ⟨pc, value, s.b⟩

def fetch (p : Program) (pc : Nat) : Option Instr :=
  if pc = 0 then none else p[pc - 1]?

def execute (i : Instr) (s : State) : State :=
  match i with
  | .inl body => set s (s.pc + 1) body (get s body + 1)
  | .inr (body, positive) =>
      if get s body = 0 then { s with pc := s.pc + 1 }
      else set s positive body (get s body - 1)

def step (p : Program) (s : State) : Option State :=
  (fetch p s.pc).map fun i => execute i s

def run (p : Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
      match step p s with
      | none => none
      | some s' => run p n s'

theorem run_add (p : Program) (m : Nat) :
    ∀ n s, run p (m + n) s =
      match run p m s with
      | none => none
      | some s' => run p n s' := by
  intro n
  induction m with
  | zero => intro s; simp [run]
  | succ m ih =>
      intro s
      simp only [Nat.succ_add, run]
      cases step p s with
      | none => rfl
      | some s' => exact ih s'

/-! Two decrement sites count modulo two.  Each zero fallthrough enters an
`inc A; dec A exit` trampoline: it restores A to zero and jumps to a distinct
out-of-range halt label. -/

def div2Program : Program :=
  [ .inr (false, 4), .inl false, .inr (false, 10),
    .inr (false, 7), .inl false, .inr (false, 11),
    .inl true, .inl false, .inr (false, 1) ]

theorem div2_cycle (a b : Nat) (h : 2 ≤ a) :
    run div2Program 5 ⟨1, a, b⟩ = some ⟨1, a - 2, b + 1⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 + k := ⟨a - 2, by omega⟩
  simp [run, step, fetch, div2Program, execute, get, set]

theorem div2_remainder (r b : Nat) (hr : r < 2) :
    run div2Program (r + 3) ⟨1, r, b⟩ = some ⟨10 + r, 0, b⟩ := by
  interval_cases r <;>
    simp [run, step, fetch, div2Program, execute, get, set]

theorem div2_groups (q r b : Nat) :
    run div2Program (5 * q) ⟨1, 2 * q + r, b⟩ =
      some ⟨1, r, b + q⟩ := by
  induction q generalizing b with
  | zero => simp [run]
  | succ q ih =>
      rw [show 5 * (q + 1) = 5 + 5 * q by omega, run_add]
      rw [div2_cycle]
      · have ha : 2 * (q + 1) + r - 2 = 2 * q + r := by omega
        rw [ha]
        simp only
        rw [ih (b + 1)]
        congr 2
        omega
      · omega

theorem div2_qr (q r b : Nat) (hr : r < 2) :
    run div2Program (5 * q + (r + 3)) ⟨1, 2 * q + r, b⟩ =
      some ⟨10 + r, 0, b + q⟩ := by
  rw [run_add, div2_groups]
  exact div2_remainder _ _ hr

theorem div2_exact (n b : Nat) :
    run div2Program (5 * (n / 2) + (n % 2 + 3)) ⟨1, n, b⟩ =
      some ⟨10 + n % 2, 0, b + n / 2⟩ := by
  have hn : 2 * (n / 2) + n % 2 = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n 2
  simpa [hn] using
    div2_qr (n / 2) (n % 2) b (Nat.mod_lt _ (by decide))

/-- Exit 10 means divisible by two; exit 11 means not divisible by two. -/
theorem exit_decides_two_divisibility (n b : Nat) :
    (10 + n % 2 = 10 ↔ 2 ∣ n) ∧
    (10 + n % 2 = 11 ↔ ¬ 2 ∣ n) := by
  constructor
  · omega
  · have hr := Nat.mod_lt n (by decide : 0 < 2)
    omega

/-! Red control: if both remainder paths use the same exit, the resulting
machine state cannot distinguish an even input from an odd one. -/

def forgetExit (s : State) : State := { s with pc := 10 }

theorem forgetting_exit_collapses_remainders :
    forgetExit ⟨10, 0, 0⟩ = forgetExit ⟨11, 0, 0⟩ := rfl

theorem turing_chamber_16AO_certificate (n b : Nat) :
    run div2Program (5 * (n / 2) + (n % 2 + 3)) ⟨1, n, b⟩ =
      some ⟨10 + n % 2, 0, b + n / 2⟩ ∧
    (10 + n % 2 = 10 ↔ 2 ∣ n) ∧
    forgetExit ⟨10, 0, 0⟩ = forgetExit ⟨11, 0, 0⟩ :=
  ⟨div2_exact n b, (exit_decides_two_divisibility n b).1,
   forgetting_exit_collapses_remainders⟩

#print axioms div2_exact
#print axioms exit_decides_two_divisibility
#print axioms turing_chamber_16AO_certificate

end FoundationStoneTest16AO
