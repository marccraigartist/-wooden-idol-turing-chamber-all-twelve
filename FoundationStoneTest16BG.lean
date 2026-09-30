import FoundationStoneTest16BF

/-!
# THE TURING CHAMBER — TEST 16BG: THE FINITE STACK-BLOCK SUITE

Lean 4.35.0-rc2 / pinned Mathlib.

Push, pop and peek are now packaged into one operation-tagged finite primitive
program.  The tag is part of control: pop and peek deliberately share their
first arithmetic phase, but they are not the same instruction.

The combined control has 164 labels:

* four copies of the 14-label push block;
* one 23-label pop block;
* one 85-label peek block.

Lean transports every exact run theorem into this common program and then
installs the whole suite in any chosen logical stack register of the primitive
five-counter machine.  Typed control means there are no raw numeric jump
targets; halting still occurs only at an explicit `halt` instruction.

This completes the finite stack-block library of Layer B1.  It does not yet
allocate these blocks behind arbitrary TM2 source labels.  That next compiler
pass must choose the source continuation for each `done`, `empty` and `bad`
outcome and prove the resulting 16AY `ExpansionContract`.
-/

namespace FoundationStoneTest16BG

open FoundationStoneTest16AW

abbrev Digit := Fin 4

inductive StackLabel
  | push (digit : Digit) (label : FoundationStoneTest16BD.PushLabel)
  | pop (label : FoundationStoneTest16BE.PopLabel)
  | peek (label : FoundationStoneTest16BF.PeekLabel)
deriving DecidableEq, Repr, Fintype

def pushName (d : Digit) (l : FoundationStoneTest16BD.PushLabel) : StackLabel :=
  .push d l

def popName (l : FoundationStoneTest16BE.PopLabel) : StackLabel := .pop l
def peekName (l : FoundationStoneTest16BF.PeekLabel) : StackLabel := .peek l

theorem pushName_injective (d : Digit) : Function.Injective (pushName d) := by
  intro x y h
  injection h

theorem popName_injective : Function.Injective popName := by
  intro x y h
  injection h

theorem peekName_injective : Function.Injective peekName := by
  intro x y h
  injection h

/-- One finite two-register program containing every stack block. -/
def stackProgram : StackLabel → Instr StackLabel
  | .push d l => FoundationStoneTest16BC.mapInstr (pushName d)
      (FoundationStoneTest16BD.pushProgram d l)
  | .pop l => FoundationStoneTest16BC.mapInstr popName
      (FoundationStoneTest16BE.popProgram l)
  | .peek l => FoundationStoneTest16BC.mapInstr peekName
      (FoundationStoneTest16BF.peekProgram l)

theorem push_part_matches (d : Digit) : ∀ l,
    stackProgram (pushName d l) = FoundationStoneTest16BC.mapInstr (pushName d)
      (FoundationStoneTest16BD.pushProgram d l) := fun _ => rfl

theorem pop_part_matches : ∀ l,
    stackProgram (popName l) = FoundationStoneTest16BC.mapInstr popName
      (FoundationStoneTest16BE.popProgram l) := fun _ => rfl

theorem peek_part_matches : ∀ l,
    stackProgram (peekName l) = FoundationStoneTest16BC.mapInstr peekName
      (FoundationStoneTest16BF.peekProgram l) := fun _ => rfl

/-! ## Exact runs in the combined control -/

theorem suite_push_exact (d : Digit) (n : Nat) :
    run stackProgram (16 * n + d.val + 3)
        ⟨StackLabel.push d .mulLoop, n, 0⟩ =
      some ⟨StackLabel.push d .done, FoundationStoneTest16AI.pushCode d n, 0⟩ := by
  have h := FoundationStoneTest16BC.run_relabels (pushName d)
    (FoundationStoneTest16BD.pushProgram d) stackProgram (push_part_matches d)
    (16 * n + d.val + 3)
    (⟨FoundationStoneTest16BD.PushLabel.mulLoop, n, 0⟩ :
      State FoundationStoneTest16BD.PushLabel)
  rw [FoundationStoneTest16BD.push_exact d n] at h
  simpa [FoundationStoneTest16BC.mapState, pushName] using h

theorem suite_pop_exact (d : Digit) (n : Nat) :
    run stackProgram (8 * n + d.val + 3)
        ⟨StackLabel.pop .start, FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨StackLabel.pop (.done d), n, 0⟩ := by
  have h := FoundationStoneTest16BC.run_relabels popName
    FoundationStoneTest16BE.popProgram stackProgram pop_part_matches
    (8 * n + d.val + 3)
    (⟨FoundationStoneTest16BE.PopLabel.start,
      FoundationStoneTest16AI.pushCode d n, 0⟩ :
      State FoundationStoneTest16BE.PopLabel)
  rw [FoundationStoneTest16BE.pop_exact d n] at h
  simpa [FoundationStoneTest16BC.mapState, popName] using h

theorem suite_pop_empty :
    run stackProgram 1 ⟨StackLabel.pop .start, 0, 0⟩ =
      some ⟨StackLabel.pop .empty, 0, 0⟩ := by
  have h := FoundationStoneTest16BC.run_relabels popName
    FoundationStoneTest16BE.popProgram stackProgram pop_part_matches 1
    (⟨FoundationStoneTest16BE.PopLabel.start, 0, 0⟩ :
      State FoundationStoneTest16BE.PopLabel)
  rw [FoundationStoneTest16BE.pop_empty] at h
  simpa [FoundationStoneTest16BC.mapState, popName] using h

theorem suite_peek_exact (d : Digit) (n : Nat) :
    run stackProgram (24 * n + 2 * d.val + 6)
        ⟨StackLabel.peek (.pop .start), FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨StackLabel.peek (.done d), FoundationStoneTest16AI.pushCode d n, 0⟩ := by
  have h := FoundationStoneTest16BC.run_relabels peekName
    FoundationStoneTest16BF.peekProgram stackProgram peek_part_matches
    (24 * n + 2 * d.val + 6)
    (⟨FoundationStoneTest16BF.PeekLabel.pop .start,
      FoundationStoneTest16AI.pushCode d n, 0⟩ :
      State FoundationStoneTest16BF.PeekLabel)
  rw [FoundationStoneTest16BF.peek_exact d n] at h
  simpa [FoundationStoneTest16BC.mapState, peekName] using h

theorem suite_peek_empty :
    run stackProgram 1 ⟨StackLabel.peek (.pop .start), 0, 0⟩ =
      some ⟨StackLabel.peek .empty, 0, 0⟩ := by
  have h := FoundationStoneTest16BC.run_relabels peekName
    FoundationStoneTest16BF.peekProgram stackProgram peek_part_matches 1
    (⟨FoundationStoneTest16BF.PeekLabel.pop .start, 0, 0⟩ :
      State FoundationStoneTest16BF.PeekLabel)
  rw [FoundationStoneTest16BF.peek_empty] at h
  simpa [FoundationStoneTest16BC.mapState, peekName] using h

/-! ## Installation in the typed primitive five-counter machine -/

def fiveStackProgram (i : FoundationStoneTest16BB.StackReg) :
    StackLabel → FoundationStoneTest16AY.Instr 5 StackLabel :=
  FoundationStoneTest16BB.liftAWProgram i stackProgram

theorem five_suite_push_exact (i : FoundationStoneTest16BB.StackReg)
    (base : FoundationStoneTest16BB.Reg5 → Nat) (d : Digit) (n : Nat) :
    FoundationStoneTest16AY.run (fiveStackProgram i) (16 * n + d.val + 3)
        (FoundationStoneTest16BB.embed i base (StackLabel.push d .mulLoop) n 0) =
      some (FoundationStoneTest16BB.embed i base (StackLabel.push d .done)
        (FoundationStoneTest16AI.pushCode d n) 0) := by
  have h := FoundationStoneTest16BB.run_lift_AW i base stackProgram
    (16 * n + d.val + 3)
    (⟨StackLabel.push d .mulLoop, n, 0⟩ : State StackLabel)
  rw [suite_push_exact d n] at h
  simpa [fiveStackProgram, FoundationStoneTest16BB.embedAW] using h

theorem five_suite_pop_exact (i : FoundationStoneTest16BB.StackReg)
    (base : FoundationStoneTest16BB.Reg5 → Nat) (d : Digit) (n : Nat) :
    FoundationStoneTest16AY.run (fiveStackProgram i) (8 * n + d.val + 3)
        (FoundationStoneTest16BB.embed i base (StackLabel.pop .start)
          (FoundationStoneTest16AI.pushCode d n) 0) =
      some (FoundationStoneTest16BB.embed i base (StackLabel.pop (.done d)) n 0) := by
  have h := FoundationStoneTest16BB.run_lift_AW i base stackProgram
    (8 * n + d.val + 3)
    (⟨StackLabel.pop .start, FoundationStoneTest16AI.pushCode d n, 0⟩ :
      State StackLabel)
  rw [suite_pop_exact d n] at h
  simpa [fiveStackProgram, FoundationStoneTest16BB.embedAW] using h

theorem five_suite_peek_exact (i : FoundationStoneTest16BB.StackReg)
    (base : FoundationStoneTest16BB.Reg5 → Nat) (d : Digit) (n : Nat) :
    FoundationStoneTest16AY.run (fiveStackProgram i)
        (24 * n + 2 * d.val + 6)
        (FoundationStoneTest16BB.embed i base (StackLabel.peek (.pop .start))
          (FoundationStoneTest16AI.pushCode d n) 0) =
      some (FoundationStoneTest16BB.embed i base (StackLabel.peek (.done d))
        (FoundationStoneTest16AI.pushCode d n) 0) := by
  have h := FoundationStoneTest16BB.run_lift_AW i base stackProgram
    (24 * n + 2 * d.val + 6)
    (⟨StackLabel.peek (.pop .start), FoundationStoneTest16AI.pushCode d n, 0⟩ :
      State StackLabel)
  rw [suite_peek_exact d n] at h
  simpa [fiveStackProgram, FoundationStoneTest16BB.embedAW] using h

/-- The typed five-counter semantics cannot halt through a missing or
out-of-range numeric label: only an explicit `halt` can produce `none`. -/
theorem five_suite_halts_only_explicitly (i : FoundationStoneTest16BB.StackReg)
    (s : FoundationStoneTest16AY.State 5 StackLabel) :
    FoundationStoneTest16AY.step (fiveStackProgram i) s = none ↔
      fiveStackProgram i s.pc = .halt :=
  FoundationStoneTest16AY.step_eq_none_iff_halt _ _

set_option maxRecDepth 10000 in
theorem stack_suite_is_finite : Fintype.card StackLabel = 164 := by decide

/-! Red control: erasing the operation tag collapses pop and peek entries. -/

inductive ErasedEntry
  | popLike (label : FoundationStoneTest16BE.PopLabel)
  | pushLike (digit : Digit) (label : FoundationStoneTest16BD.PushLabel)
  | other
deriving DecidableEq

def eraseOperation : StackLabel → ErasedEntry
  | .pop l => .popLike l
  | .peek (.pop l) => .popLike l
  | .push d l => .pushLike d l
  | _ => .other

theorem erasing_operation_collapses_pop_and_peek :
    eraseOperation (.pop .start) = eraseOperation (.peek (.pop .start)) ∧
    (StackLabel.pop .start) ≠ .peek (.pop .start) := by decide

theorem turing_chamber_16BG_certificate :
    Fintype.card StackLabel = 164 ∧
    (∀ d n, run stackProgram (16 * n + d.val + 3)
      ⟨StackLabel.push d .mulLoop, n, 0⟩ =
        some ⟨StackLabel.push d .done, FoundationStoneTest16AI.pushCode d n, 0⟩) ∧
    (∀ d n, run stackProgram (8 * n + d.val + 3)
      ⟨StackLabel.pop .start, FoundationStoneTest16AI.pushCode d n, 0⟩ =
        some ⟨StackLabel.pop (.done d), n, 0⟩) ∧
    (∀ d n, run stackProgram (24 * n + 2 * d.val + 6)
      ⟨StackLabel.peek (.pop .start), FoundationStoneTest16AI.pushCode d n, 0⟩ =
        some ⟨StackLabel.peek (.done d), FoundationStoneTest16AI.pushCode d n, 0⟩) ∧
    eraseOperation (.pop .start) = eraseOperation (.peek (.pop .start)) ∧
    (StackLabel.pop .start) ≠ .peek (.pop .start) :=
  ⟨stack_suite_is_finite, suite_push_exact, suite_pop_exact, suite_peek_exact,
   erasing_operation_collapses_pop_and_peek.1,
   erasing_operation_collapses_pop_and_peek.2⟩

#print axioms suite_push_exact
#print axioms suite_pop_exact
#print axioms suite_peek_exact
#print axioms five_suite_halts_only_explicitly
#print axioms turing_chamber_16BG_certificate

end FoundationStoneTest16BG
