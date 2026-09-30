import FoundationStoneTest16AY

/-!
# THE TURING CHAMBER — TEST 16BA: A LINKED MACHINE RUNS CLEANLY

Lean 4.35.0-rc2 / pinned Mathlib.  Depends on 16AY.

This is the positive smoke test following 16AZ's bad patch.

The source has two labels:

* `false`: increment counter A once, then go to `true`;
* `true`: halt.

Its compiled `false` block has three primitive instructions.  It increments A,
borrows counter B for a two-instruction continuation bridge, restores B exactly,
and exits to the declared `true` block.  The `true` block contains an explicit
halt.  Thus this is a real multi-instruction expansion rather than the source
machine copied one instruction at a time.

Lean proves the block contract for arbitrary initial counter contents, obtains
`Respects` and termination equivalence from 16AY, and evaluates one concrete
run end to end.  The source halts after two steps; the linked machine halts
after four, with the same logical result at the linked entry after three.
-/

namespace FoundationStoneTest16BA

open FoundationStoneTest16AY

abbrev Label := Bool

def sourceProgram : Label → Instr 2 Label
  | false => .inc 0 true
  | true => .halt

/-- Three slots per block.  Only the entry of the halt block is reachable. -/
def goodBlocks : BlockFamily 2 Label where
  width := fun _ => 3
  nonempty := by intro; decide
  code := fun owner position =>
    match owner, position.val with
    | false, 0 => .inc 0 (.local ⟨1, by decide⟩)
    | false, 1 => .inc 1 (.local ⟨2, by decide⟩)
    | false, _ => .dec 1 (.exit true) (.exit true)
    | true, _ => .halt

def mid1 (c : Fin 2 → Nat) : State 2 (LinkedLabel goodBlocks) :=
  ⟨⟨false, ⟨1, by decide⟩⟩, Function.update c 0 (c 0 + 1)⟩

def mid2 (c : Fin 2 → Nat) : State 2 (LinkedLabel goodBlocks) :=
  ⟨⟨false, ⟨2, by decide⟩⟩,
    Function.update (Function.update c 0 (c 0 + 1)) 1 (c 1 + 1)⟩

def sourceAfter (c : Fin 2 → Nat) : State 2 Label :=
  ⟨true, Function.update c 0 (c 0 + 1)⟩

theorem linked_step_one (c : Fin 2 → Nat) :
    step (linkedProgram goodBlocks)
      (State.map (entry goodBlocks) ⟨false, c⟩) = some (mid1 c) := by
  rfl

theorem linked_step_two (c : Fin 2 → Nat) :
    step (linkedProgram goodBlocks) (mid1 c) = some (mid2 c) := by
  rfl

theorem linked_step_three (c : Fin 2 → Nat) :
    step (linkedProgram goodBlocks) (mid2 c) =
      some (State.map (entry goodBlocks) (sourceAfter c)) := by
  simp [step, linkedProgram, linkInstr, Instr.map, resolve, goodBlocks,
    mid2, sourceAfter, State.map, entry, setCounter]

theorem source_false_step (c : Fin 2 → Nat) :
    step sourceProgram ⟨false, c⟩ = some (sourceAfter c) := by
  rfl

theorem source_true_halts (c : Fin 2 → Nat) :
    step sourceProgram ⟨true, c⟩ = none := by
  rfl

theorem linked_true_halts (c : Fin 2 → Nat) :
    step (linkedProgram goodBlocks)
      (State.map (entry goodBlocks) ⟨true, c⟩) = none := by
  rfl

/-- The three-instruction block is a positive chain of genuine linked steps. -/
theorem false_block_path (c : Fin 2 → Nat) :
    Relation.TransGen
      (fun u v => step (linkedProgram goodBlocks) u = some v)
      (State.map (entry goodBlocks) ⟨false, c⟩)
      (State.map (entry goodBlocks) (sourceAfter c)) := by
  exact Relation.TransGen.tail
    (Relation.TransGen.tail
      (Relation.TransGen.single (linked_step_one c))
      (linked_step_two c))
    (linked_step_three c)

/-- All source instructions satisfy 16AY's reusable expansion contract. -/
theorem good_blocks_meet_the_contract :
    ExpansionContract sourceProgram goodBlocks := by
  constructor
  · intro s hs
    rcases s with ⟨pc, c⟩
    cases pc with
    | false => simp [step, sourceProgram] at hs
    | true => exact linked_true_halts c
  · intro s s' hs
    rcases s with ⟨pc, c⟩
    cases pc with
    | false =>
        rw [source_false_step] at hs
        have heq : s' = sourceAfter c := Option.some.inj hs.symm
        subst s'
        exact false_block_path c
    | true => simp [step, sourceProgram] at hs

theorem smoke_respects :
    StateTransition.Respects
      (step sourceProgram) (step (linkedProgram goodBlocks))
      (Encodes goodBlocks) :=
  expansion_respects sourceProgram goodBlocks good_blocks_meet_the_contract

/-! ## Concrete end-to-end execution -/

def zeroCounters : Fin 2 → Nat := fun _ => 0
def sourceStart : State 2 Label := ⟨false, zeroCounters⟩
def linkedStart : State 2 (LinkedLabel goodBlocks) :=
  State.map (entry goodBlocks) sourceStart
def finishedSource : State 2 Label := sourceAfter zeroCounters
def finishedLinked : State 2 (LinkedLabel goodBlocks) :=
  State.map (entry goodBlocks) finishedSource

theorem source_reaches_halt_entry :
    run sourceProgram 1 sourceStart = some finishedSource := by
  rfl

theorem linked_reaches_halt_entry :
    run (linkedProgram goodBlocks) 3 linkedStart = some finishedLinked := by
  unfold linkedStart sourceStart finishedLinked finishedSource
  simp only [run]
  rw [linked_step_one zeroCounters]
  simp only
  rw [linked_step_two zeroCounters]
  simp only
  rw [linked_step_three zeroCounters]

theorem source_halts_after_two : run sourceProgram 2 sourceStart = none := by
  rfl

theorem linked_halts_after_four :
    run (linkedProgram goodBlocks) 4 linkedStart = none := by
  unfold linkedStart sourceStart
  simp only [run]
  rw [linked_step_one zeroCounters]
  simp only
  rw [linked_step_two zeroCounters]
  simp only
  rw [linked_step_three zeroCounters]
  simp only
  have hh : step (linkedProgram goodBlocks)
      (State.map (entry goodBlocks) (sourceAfter zeroCounters)) = none := by
    simpa [sourceAfter] using
      linked_true_halts (Function.update zeroCounters 0 (zeroCounters 0 + 1))
  rw [hh]

theorem counters_agree_at_exit :
    finishedLinked.counters 0 = 1 ∧ finishedLinked.counters 1 = 0 := by
  decide

-- Executable smoke output: `(halt-entry label, A, B) = (true, 1, 0)`.
#eval (run (linkedProgram goodBlocks) 3 linkedStart).map
  (fun s => (s.pc.1, s.counters 0, s.counters 1))

theorem smoke_termination_equivalence :
    Terminates sourceProgram sourceStart ↔
      Terminates (linkedProgram goodBlocks) linkedStart :=
  expansion_termination_iff sourceProgram goodBlocks
    good_blocks_meet_the_contract sourceStart

theorem turing_chamber_16BA_certificate :
    StateTransition.Respects
      (step sourceProgram) (step (linkedProgram goodBlocks))
      (Encodes goodBlocks) ∧
    run sourceProgram 1 sourceStart = some finishedSource ∧
    run (linkedProgram goodBlocks) 3 linkedStart = some finishedLinked ∧
    run sourceProgram 2 sourceStart = none ∧
    run (linkedProgram goodBlocks) 4 linkedStart = none ∧
    (finishedLinked.counters 0 = 1 ∧ finishedLinked.counters 1 = 0) ∧
    (Terminates sourceProgram sourceStart ↔
      Terminates (linkedProgram goodBlocks) linkedStart) :=
  ⟨smoke_respects, source_reaches_halt_entry, linked_reaches_halt_entry,
   source_halts_after_two, linked_halts_after_four, counters_agree_at_exit,
   smoke_termination_equivalence⟩

#print axioms linked_step_three
#print axioms false_block_path
#print axioms good_blocks_meet_the_contract
#print axioms smoke_respects
#print axioms smoke_termination_equivalence
#print axioms turing_chamber_16BA_certificate

end FoundationStoneTest16BA
