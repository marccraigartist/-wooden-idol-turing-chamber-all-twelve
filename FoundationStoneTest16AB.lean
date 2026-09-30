import Mathlib

/-!
# THE STANDARD MM2 DOOR — FOUNDATION STONE TEST 16AB

This ports the operational core of the Coq Library of Undecidable Problems'
`MM2` model into Lean and connects it exactly to the Wooden Idol relay language.

The standard instruction set is:
* increment A or B, then continue to the following instruction;
* decrement A or B; on a positive counter jump to a stored label, and on zero
  continue to the following instruction.

Standard programs are one-indexed.  The compiler pads address zero with HALT
and lowers every instruction at address `pc` to the relay's explicit
`inc/dec/halt` instruction.

Lean certifies exact instruction fetch, one-step execution, every bounded run,
and halting.  No universality theorem is assumed here.
-/

namespace FoundationStoneTest16AB

inductive Body | A | B deriving DecidableEq, Repr

inductive MM2Instr
  | incA | incB
  | decA (jump : Nat)
  | decB (jump : Nat)
deriving DecidableEq, Repr

abbrev MM2Program := List MM2Instr

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

def mm2Fetch (p : MM2Program) (pc : Nat) : Option MM2Instr :=
  if pc = 0 then none else p[pc - 1]?

def mm2Execute (i : MM2Instr) (s : State) : State :=
  match i with
  | .incA => set s (s.pc + 1) .A (s.a + 1)
  | .incB => set s (s.pc + 1) .B (s.b + 1)
  | .decA jump =>
      if s.a = 0 then { s with pc := s.pc + 1 }
      else set s jump .A (s.a - 1)
  | .decB jump =>
      if s.b = 0 then { s with pc := s.pc + 1 }
      else set s jump .B (s.b - 1)

def mm2Step (p : MM2Program) (s : State) : Option State :=
  (mm2Fetch p s.pc).map fun i => mm2Execute i s

def mm2Run (p : MM2Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
      match mm2Step p s with
      | none => none
      | some s' => mm2Run p n s'

def MM2Halts (p : MM2Program) (a b : Nat) : Prop :=
  ∃ n, mm2Run p n ⟨1, a, b⟩ = none

/-! ## The relay target -/

inductive Instr
  | inc (b : Body) (next : Nat)
  | dec (b : Body) (next zeroLabel : Nat)
  | halt
deriving DecidableEq, Repr

abbrev Program := List Instr

def lowerAt (pc : Nat) : MM2Instr → Instr
  | .incA => .inc .A (pc + 1)
  | .incB => .inc .B (pc + 1)
  | .decA jump => .dec .A jump (pc + 1)
  | .decB jump => .dec .B jump (pc + 1)

def lowerFrom : Nat → MM2Program → Program
  | _, [] => []
  | pc, i :: rest => lowerAt pc i :: lowerFrom (pc + 1) rest

def compile (p : MM2Program) : Program := .halt :: lowerFrom 1 p

def fetch (p : Program) (pc : Nat) : Instr := (p[pc]?).getD .halt

def execute : Instr → State → Option State
  | .inc b next, s => some (set s next b (get s b + 1))
  | .dec b next zeroLabel, s =>
      if get s b = 0 then some { s with pc := zeroLabel }
      else some (set s next b (get s b - 1))
  | .halt, _ => none

def step (p : Program) (s : State) : Option State := execute (fetch p s.pc) s

def run (p : Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
      match step p s with
      | none => none
      | some s' => run p n s'

def RelayHalts (p : Program) (a b : Nat) : Prop :=
  ∃ n, run p n ⟨1, a, b⟩ = none

/-! ## Exact compiler -/

theorem lowerFrom_get? : ∀ (p : MM2Program) base k,
    (lowerFrom base p)[k]? = (p[k]?).map (lowerAt (base + k)) := by
  intro p
  induction p with
  | nil => intro base k; simp [lowerFrom]
  | cons i rest ih =>
      intro base k
      cases k with
      | zero => simp [lowerFrom]
      | succ k =>
          simp only [lowerFrom, List.getElem?_cons_succ, Option.map]
          rw [ih (base + 1) k]
          rw [show base + 1 + k = base + (k + 1) by omega]
          cases rest[k]? <;> rfl

theorem fetch_compile (p : MM2Program) (pc : Nat) :
    fetch (compile p) pc =
      match mm2Fetch p pc with
      | none => .halt
      | some i => lowerAt pc i := by
  cases pc with
  | zero => rfl
  | succ k =>
      simp only [fetch, compile, List.getElem?_cons_succ, mm2Fetch,
        Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      rw [lowerFrom_get?]
      simp only [Nat.add_comm 1 k]
      cases p[k]? <;> rfl

theorem execute_lower (pc : Nat) (i : MM2Instr) (s : State) (hpc : s.pc = pc) :
    execute (lowerAt pc i) s = some (mm2Execute i s) := by
  subst pc
  cases i with
  | incA => rfl
  | incB => rfl
  | decA jump => by_cases h : s.a = 0 <;> simp [lowerAt, execute, mm2Execute, get, set, h]
  | decB jump => by_cases h : s.b = 0 <;> simp [lowerAt, execute, mm2Execute, get, set, h]

theorem step_compiles (p : MM2Program) (s : State) :
    step (compile p) s = mm2Step p s := by
  unfold step mm2Step
  rw [fetch_compile]
  cases h : mm2Fetch p s.pc with
  | none => rfl
  | some i =>
      simp only [Option.map_some]
      exact execute_lower s.pc i s rfl

theorem run_compiles (p : MM2Program) : ∀ n s,
    run (compile p) n s = mm2Run p n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      unfold run mm2Run
      rw [step_compiles]
      cases mm2Step p s with
      | none => rfl
      | some s' => exact ih s'

theorem halting_compiles (p : MM2Program) (a b : Nat) :
    MM2Halts p a b ↔ RelayHalts (compile p) a b := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · rw [run_compiles, hn]
  · rw [run_compiles] at hn
    exact hn

/-! Controls -/

def stopper : MM2Program := []
def climber : MM2Program := [.incA, .decA 1]

theorem stopper_control : MM2Halts stopper 0 0 := ⟨1, rfl⟩

theorem climber_prefix (n a : Nat) :
    mm2Run climber (2 * n) ⟨1, a, 0⟩ = some ⟨1, a, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change mm2Run climber (2 * n) ⟨1, a, 0⟩ = some ⟨1, a, 0⟩
      exact ih

/-- RED CONTROL: deleting the padding HALT shifts every standard label. -/
def badCompile (p : MM2Program) : Program := lowerFrom 1 p

theorem missing_padding_breaks_labels :
    step (badCompile [.incA]) ⟨1, 0, 0⟩ = none ∧
    step (compile [.incA]) ⟨1, 0, 0⟩ = some ⟨2, 1, 0⟩ := by decide

theorem standard_mm2_door_certificate :
    (∀ p s, step (compile p) s = mm2Step p s) ∧
    (∀ p n s, run (compile p) n s = mm2Run p n s) ∧
    (∀ p a b, MM2Halts p a b ↔ RelayHalts (compile p) a b) ∧
    step (badCompile [.incA]) ⟨1, 0, 0⟩ = none :=
  ⟨step_compiles, run_compiles, halting_compiles, missing_padding_breaks_labels.1⟩

#print axioms fetch_compile
#print axioms step_compiles
#print axioms run_compiles
#print axioms halting_compiles
#print axioms missing_padding_breaks_labels
#print axioms standard_mm2_door_certificate

end FoundationStoneTest16AB
