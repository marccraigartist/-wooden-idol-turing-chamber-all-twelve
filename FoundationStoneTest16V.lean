import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Computability.Halting

/-!
# THE TURING FRONT DOOR — FOUNDATION STONE TEST 16V

Test 16U reduced the missing Turing chamber to an honest universality compiler.
The local Mathlib audit found no two-counter/Minsky formalisation, but it did find
something stronger than a citation: Mathlib already contains a verified compiler
from its sequential partial-recursive language to a four-stack Turing machine.

This test exposes and checks that route without pretending it is already a
two-counter compiler.

Lean certifies:

1. the Turing machine halts exactly when the source program is defined;
2. when it halts, its returned stack is exactly the source result;
3. every compiled source program uses only a finite set of machine labels;
4. the machine itself is fixed — program and input live in the initial state;
5. identity-program controls preserve the complete input list;
6. RED CONTROL: changing the encoded input changes the returned result, so the
   initial-state translation is semantically active and cannot be erased.

The remaining bridge is stated exactly at the end: compile this finite four-stack
machine into Test 16U's conventional `INC/JZDEC/HALT` programs, computably and
halting-preservingly.  16V does not inhabit that bridge.
-/

open Relation StateTransition

namespace FoundationStoneTest16V

abbrev SourceCode := Turing.ToPartrec.Code
abbrev TMCfg := Turing.PartrecToTM2.Cfg'

/-! ## 1. The source and the already-formal Turing execution -/

def SourceRun (c : SourceCode) (input : List Nat) : Part (List Nat) := c.eval input

def TMRun (c : SourceCode) (input : List Nat) : Part TMCfg :=
  StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
    (Turing.PartrecToTM2.init c input)

def SourceHalts (c : SourceCode) (input : List Nat) : Prop :=
  (SourceRun c input).Dom

def TMHalts (c : SourceCode) (input : List Nat) : Prop :=
  (TMRun c input).Dom

def TMReturns (c : SourceCode) (input output : List Nat) : Prop :=
  Turing.PartrecToTM2.halt output ∈ TMRun c input

def TMReachesFinal (c : SourceCode) (input : List Nat) (final : TMCfg) : Prop :=
  final ∈ TMRun c input

/-- Imported foundation, named explicitly: Mathlib's evaluator theorem. -/
theorem mathlib_turing_compiler_exact (c : SourceCode) (input : List Nat) :
    TMRun c input = Turing.PartrecToTM2.halt <$> SourceRun c input := by
  exact Turing.PartrecToTM2.tr_eval c input

/-- Derived consequence: the Turing run exists exactly when source evaluation exists. -/
theorem tm_halts_iff_source_halts (c : SourceCode) (input : List Nat) :
    TMHalts c input ↔ SourceHalts c input := by
  have h := congrArg Part.Dom (mathlib_turing_compiler_exact c input)
  simpa [TMHalts, SourceHalts] using h

/-- Stronger than equal halting status: final configurations are precisely encoded
source results.  This formulation needs no unproved decoder for Mathlib's stack encoding. -/
theorem tm_final_cfg_iff_source_result (c : SourceCode) (input : List Nat) (final : TMCfg) :
    TMReachesFinal c input final ↔
      ∃ output, output ∈ SourceRun c input ∧ Turing.PartrecToTM2.halt output = final := by
  rw [TMReachesFinal, mathlib_turing_compiler_exact]
  simp only [Part.map_eq_map, Part.mem_map_iff]

/-! ## 2. The finite machine hidden inside the general interpreter -/

/-- Each source program has an explicit finite support of accessible Turing labels. -/
def labelSupport (c : SourceCode) : Finset Turing.PartrecToTM2.Λ' :=
  Turing.PartrecToTM2.codeSupp c Turing.PartrecToTM2.Cont'.halt

theorem compiled_entry_is_in_support (c : SourceCode) :
    Turing.PartrecToTM2.trNormal c Turing.PartrecToTM2.Cont'.halt ∈ labelSupport c := by
  exact (Turing.PartrecToTM2.tr_supports c Turing.PartrecToTM2.Cont'.halt).1

theorem compiled_program_has_finite_support (c : SourceCode) :
    ∀ q ∈ labelSupport c,
      Turing.TM2.SupportsStmt (labelSupport c) (Turing.PartrecToTM2.tr q) := by
  exact (Turing.PartrecToTM2.tr_supports c Turing.PartrecToTM2.Cont'.halt).2

/-- The transition table is one fixed machine; only the initial configuration changes. -/
theorem one_machine_all_programs :
    ∀ _c₁ _c₂ : SourceCode,
      (Turing.PartrecToTM2.tr :
        Turing.PartrecToTM2.Λ' → Turing.PartrecToTM2.Stmt') =
        Turing.PartrecToTM2.tr := by
  intro _ _
  rfl

/-! ## 2b. This really is a universal Turing chamber -/

/-- Every Mathlib partial-recursive function of a fixed finite arity is realised
by a finite-support execution of this Turing machine.  This composes Mathlib's
constructive source-code theorem with the halting equivalence proved above. -/
theorem every_partial_recursive_function_has_a_turing_machine
    {arity : Nat} {f : List.Vector Nat arity →. Nat} (hf : Nat.Partrec' f) :
    ∃ c : SourceCode, ∀ input : List.Vector Nat arity,
      TMHalts c input.1 ↔ (f input).Dom := by
  obtain ⟨c, hc⟩ := Turing.ToPartrec.Code.exists_code hf
  refine ⟨c, fun input => ?_⟩
  rw [tm_halts_iff_source_halts]
  unfold SourceHalts SourceRun
  rw [hc input]
  rfl

/-! ## 3. Controls: data really crosses the front door -/

def idCode : SourceCode := Turing.ToPartrec.Code.id

theorem identity_source_returns_its_input (input : List Nat) :
    SourceRun idCode input = Part.some input := by
  simp [SourceRun, idCode]

theorem identity_tm_returns_its_input (input : List Nat) :
    TMRun idCode input = Part.some (Turing.PartrecToTM2.halt input) := by
  rw [mathlib_turing_compiler_exact, identity_source_returns_its_input]
  rfl

theorem identity_tm_halts (input : List Nat) : TMHalts idCode input := by
  rw [tm_halts_iff_source_halts]
  simp [SourceHalts, SourceRun, idCode]

/-- A deliberately corrupted initial-state translation. -/
def badInput (input : List Nat) : List Nat := input.map Nat.succ

def BadTMRun (c : SourceCode) (input : List Nat) : Part TMCfg :=
  TMRun c (badInput input)

theorem bad_identity_returns_changed_data :
    BadTMRun idCode [7, 11] =
      Part.some (Turing.PartrecToTM2.halt [8, 12]) := by
  change TMRun idCode [8, 12] = _
  exact identity_tm_returns_its_input [8, 12]

/-- RED CONTROL: erasing the exact input translation changes observable output. -/
theorem bad_input_translation_fails :
    BadTMRun idCode [7, 11] ≠ TMRun idCode [7, 11] := by
  rw [bad_identity_returns_changed_data, identity_tm_returns_its_input]
  intro h
  have hh : Turing.PartrecToTM2.halt [8, 12] =
      Turing.PartrecToTM2.halt [7, 11] := Part.some_injective h
  have hs := congrArg
    (fun cfg : TMCfg => cfg.stk Turing.PartrecToTM2.K'.main) hh
  exact (by decide : Turing.PartrecToTM2.trList [8, 12] ≠
    Turing.PartrecToTM2.trList [7, 11]) hs

/-! ## 4. The remaining two-counter door -/

/-- Test 16U's conventional two-counter instruction shape, repeated only so this
file states its remaining obligation without importing an uncommitted live bucket.
`none` is halt, `some (b, none)` is increment, and `some (b, some z)` is JZDEC. -/
abbrev CounterInstr := Option (Bool × Option Nat)
abbrev CounterProgram := List CounterInstr

structure CounterState where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq

def counterStart : CounterState := ⟨0, 0, 0⟩

def counterGet (s : CounterState) : Bool → Nat
  | false => s.a
  | true => s.b

def counterSet (s : CounterState) (pc : Nat) : Bool → Nat → CounterState
  | false, v => ⟨pc, v, s.b⟩
  | true, v => ⟨pc, s.a, v⟩

def counterFetch (p : CounterProgram) (pc : Nat) : CounterInstr :=
  (p[pc]?).getD none

def counterStep (p : CounterProgram) (s : CounterState) : Option CounterState :=
  match counterFetch p s.pc with
  | none => none
  | some (body, none) =>
      some (counterSet s (s.pc + 1) body (counterGet s body + 1))
  | some (body, some zeroTarget) =>
      if counterGet s body = 0 then some { s with pc := zeroTarget }
      else some (counterSet s (s.pc + 1) body (counterGet s body - 1))

def counterRun (p : CounterProgram) : Nat → CounterState → Option CounterState
  | 0, s => some s
  | n + 1, s =>
      match counterStep p s with
      | none => none
      | some s' => counterRun p n s'

def CounterHalts (p : CounterProgram) : Prop :=
  ∃ n, counterRun p n counterStart = none

/-- The exact semantic final obligation.  An inhabitant must supply executable
finite counter code and semantic correctness.  A repository integration must
add a concrete numeric coding of `SourceCode` before the compiler's Mathlib
computability can be stated; Mathlib currently supplies no `Primcodable` instance
for this syntax. -/
structure FourStackToCounterBridge where
  compile : SourceCode → List Nat → CounterProgram
  correct : ∀ c input, TMHalts c input ↔ CounterHalts (compile c input)

/-- Any authentic inhabitant immediately transfers source halting to two counters. -/
theorem bridge_reaches_two_counters (B : FourStackToCounterBridge)
    (c : SourceCode) (input : List Nat) :
    SourceHalts c input ↔ CounterHalts (B.compile c input) := by
  rw [← tm_halts_iff_source_halts]
  exact B.correct c input

/-! ## Certificate -/

theorem turing_front_door_certificate :
    (∀ c input, TMHalts c input ↔ SourceHalts c input) ∧
    (∀ c input final, TMReachesFinal c input final ↔
      ∃ output, output ∈ SourceRun c input ∧
        Turing.PartrecToTM2.halt output = final) ∧
    (∀ c q, q ∈ labelSupport c →
      Turing.TM2.SupportsStmt (labelSupport c) (Turing.PartrecToTM2.tr q)) ∧
    (∀ input, TMRun idCode input =
      Part.some (Turing.PartrecToTM2.halt input)) ∧
    BadTMRun idCode [7, 11] ≠ TMRun idCode [7, 11] :=
  ⟨tm_halts_iff_source_halts, tm_final_cfg_iff_source_result,
   compiled_program_has_finite_support, identity_tm_returns_its_input,
   bad_input_translation_fails⟩

#print axioms mathlib_turing_compiler_exact
#print axioms tm_halts_iff_source_halts
#print axioms tm_final_cfg_iff_source_result
#print axioms compiled_program_has_finite_support
#print axioms every_partial_recursive_function_has_a_turing_machine
#print axioms identity_tm_returns_its_input
#print axioms bad_input_translation_fails
#print axioms bridge_reaches_two_counters
#print axioms turing_front_door_certificate

end FoundationStoneTest16V
