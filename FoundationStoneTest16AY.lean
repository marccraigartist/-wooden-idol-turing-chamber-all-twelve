import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AY: THE TYPED BLOCK LINKER

Lean 4.35.0-rc2 / pinned Mathlib.

This is the reusable hinge requested at the 16AS–16AX boundary.  A source
machine has `k` counters and an arbitrary control-label type `L`.  Every source
label owns a nonempty, finite block of primitive counter instructions.

The block language makes three destinations distinct in the type:

* `local i` stays inside the current finite block;
* `exit l` enters the declared block for source label `l`;
* `halt` is an explicit instruction.

Consequently an out-of-range program counter is not representable, and a
mis-patched integer label cannot silently become a halt.

The main theorem is deliberately generic.  If every halted source state halts
at its linked entry, and every running source step is implemented by a
positive linked run to the next encoded entry, then the linked machine
`Respects` the source.  Mathlib's `tr_eval_dom` then lifts the instruction-wise
contracts to termination equivalence for arbitrary runs.

The positive run is a `Relation.TransGen` of genuine target steps.  Thus the
contract also says that a block cannot halt internally before its nominated
exit.  The same theorem is intended to be instantiated twice:

1. five-counter macros → primitive five-counter Minsky machine;
2. primitive k-counter machine → prime-packed MM2.
-/

namespace FoundationStoneTest16AY

open StateTransition

/-! ## Primitive typed counter machines -/

inductive Instr (k : Nat) (L : Type)
  | inc (counter : Fin k) (next : L)
  | dec (counter : Fin k) (positive zero : L)
  | halt
deriving Repr

structure State (k : Nat) (L : Type) where
  pc : L
  counters : Fin k → Nat

def Instr.map {k : Nat} {L K : Type} (f : L → K) : Instr k L → Instr k K
  | .inc i next => .inc i (f next)
  | .dec i positive zero => .dec i (f positive) (f zero)
  | .halt => .halt

def State.map {k : Nat} {L K : Type} (f : L → K) (s : State k L) : State k K :=
  ⟨f s.pc, s.counters⟩

def setCounter {k : Nat} {L : Type} (s : State k L)
    (pc : L) (i : Fin k) (value : Nat) : State k L :=
  ⟨pc, Function.update s.counters i value⟩

def step {k : Nat} {L : Type} (P : L → Instr k L) (s : State k L) :
    Option (State k L) :=
  match P s.pc with
  | .halt => none
  | .inc i next => some (setCounter s next i (s.counters i + 1))
  | .dec i positive zero =>
      if s.counters i = 0 then some { s with pc := zero }
      else some (setCounter s positive i (s.counters i - 1))

def run {k : Nat} {L : Type} (P : L → Instr k L) :
    Nat → State k L → Option (State k L)
  | 0, s => some s
  | n + 1, s =>
      match step P s with
      | none => none
      | some s' => run P n s'

/-- Halting is caused exactly by the explicit `halt` constructor. -/
theorem step_eq_none_iff_halt {k : Nat} {L : Type} (P : L → Instr k L)
    (s : State k L) : step P s = none ↔ P s.pc = .halt := by
  unfold step
  cases h : P s.pc with
  | halt => simp
  | inc i next => simp
  | dec i positive zero =>
      by_cases hz : s.counters i = 0 <;> simp [hz]

/-! ## Finite local blocks and their typed exits -/

/-- A local target either stays in the current block or exits to a declared
source label.  There is deliberately no raw natural-number jump target. -/
inductive Target (L I : Type)
  | local (i : I)
  | exit (label : L)
deriving Repr

/-- One nonempty finite primitive block for each source label. -/
structure BlockFamily (k : Nat) (L : Type) where
  width : L → Nat
  nonempty : ∀ l, 0 < width l
  code : ∀ l, Fin (width l) → Instr k (Target L (Fin (width l)))

/-- Linked labels remember both their owning source instruction and their
finite local position. -/
abbrev LinkedLabel {k : Nat} {L : Type} (B : BlockFamily k L) :=
  Σ l, Fin (B.width l)

def entry {k : Nat} {L : Type} (B : BlockFamily k L) (l : L) : LinkedLabel B :=
  ⟨l, ⟨0, B.nonempty l⟩⟩

def resolve {k : Nat} {L : Type} (B : BlockFamily k L) (owner : L) :
    Target L (Fin (B.width owner)) → LinkedLabel B
  | .local i => ⟨owner, i⟩
  | .exit l => entry B l

def linkInstr {k : Nat} {L : Type} (B : BlockFamily k L) (owner : L) :
    Instr k (Target L (Fin (B.width owner))) → Instr k (LinkedLabel B) :=
  Instr.map (resolve B owner)

/-- The linked primitive program.  Every possible program counter denotes an
actual instruction in an actual source-owned block. -/
def linkedProgram {k : Nat} {L : Type} (B : BlockFamily k L) :
    LinkedLabel B → Instr k (LinkedLabel B)
  | ⟨owner, position⟩ => linkInstr B owner (B.code owner position)

theorem linked_halts_only_explicitly {k : Nat} {L : Type}
    (B : BlockFamily k L) (s : State k (LinkedLabel B)) :
    step (linkedProgram B) s = none ↔ linkedProgram B s.pc = .halt :=
  step_eq_none_iff_halt _ _

/-- With finite source control, the linked control space is finite too. -/
noncomputable def linkedLabelEquivFin {k : Nat} {L : Type} [Fintype L]
    (B : BlockFamily k L) :
    LinkedLabel B ≃ Fin (Fintype.card (LinkedLabel B)) :=
  Fintype.equivFin _

/-! ## One linker theorem, reusable at both compiler layers -/

def Encodes {k : Nat} {L : Type} (B : BlockFamily k L)
    (s : State k L) (t : State k (LinkedLabel B)) : Prop :=
  State.map (entry B) s = t

/-- A block implementation contract.  The `advance` field is a nonempty chain
of actual target steps, so it simultaneously supplies progress and rules out
an internal halt before the nominated exit. -/
structure ExpansionContract {k : Nat} {L : Type}
    (P : L → Instr k L) (B : BlockFamily k L) : Prop where
  halted : ∀ s : State k L, step P s = none →
    step (linkedProgram B) (State.map (entry B) s) = none
  advance : ∀ s s' : State k L, step P s = some s' →
    Relation.TransGen
      (fun u v => step (linkedProgram B) u = some v)
      (State.map (entry B) s) (State.map (entry B) s')

/-- Instruction-wise block correctness implies Mathlib's simulation relation. -/
theorem expansion_respects {k : Nat} {L : Type}
    (P : L → Instr k L) (B : BlockFamily k L)
    (h : ExpansionContract P B) :
    StateTransition.Respects (step P) (step (linkedProgram B)) (Encodes B) := by
  intro s t hst
  subst t
  cases hs : step P s with
  | none => exact h.halted s hs
  | some s' =>
      exact ⟨State.map (entry B) s', rfl, h.advance s s' hs⟩

def Terminates {k : Nat} {L : Type} (P : L → Instr k L) (s : State k L) : Prop :=
  (StateTransition.eval (step P) s).Dom

/-- The generic run-lifting result used by both future compiler layers. -/
theorem expansion_termination_iff {k : Nat} {L : Type}
    (P : L → Instr k L) (B : BlockFamily k L)
    (h : ExpansionContract P B) (s : State k L) :
    Terminates P s ↔
      Terminates (linkedProgram B) (State.map (entry B) s) := by
  unfold Terminates
  exact (StateTransition.tr_eval_dom (expansion_respects P B h) rfl).symm

/-! ## The certificate -/

theorem turing_chamber_16AY_certificate :
    (∀ {k : Nat} {L : Type} (P : L → Instr k L) (B : BlockFamily k L),
      ExpansionContract P B →
      StateTransition.Respects (step P) (step (linkedProgram B)) (Encodes B)) ∧
    (∀ {k : Nat} {L : Type} (P : L → Instr k L) (B : BlockFamily k L)
      (_h : ExpansionContract P B) (s : State k L),
      Terminates P s ↔
        Terminates (linkedProgram B) (State.map (entry B) s)) ∧
    (∀ {k : Nat} {L : Type} (B : BlockFamily k L)
      (s : State k (LinkedLabel B)),
      step (linkedProgram B) s = none ↔ linkedProgram B s.pc = .halt) :=
  ⟨fun P B h => expansion_respects P B h,
   fun P B h s => expansion_termination_iff P B h s,
   fun B s => linked_halts_only_explicitly B s⟩

#print axioms step_eq_none_iff_halt
#print axioms linked_halts_only_explicitly
#print axioms expansion_respects
#print axioms expansion_termination_iff
#print axioms turing_chamber_16AY_certificate

end FoundationStoneTest16AY
