import FoundationStoneTest16AY

/-!
# THE TURING CHAMBER — TEST 16AZ: THE MIS-PATCHED EXIT

Lean 4.35.0-rc2 / pinned Mathlib.  Depends on 16AY.

16AY's typed labels prevent an out-of-range jump from silently becoming a
halt.  They cannot, and should not, make a semantically wrong in-range exit
correct.  This red control deliberately patches the first source instruction
to the genuine halt block instead of its genuine continuation.

The source program is:

* label 0: increment counter 0 and go to label 1;
* label 1: increment counter 0 and stay at label 1 forever;
* label 2: halt.

The bad linked program changes only the exit from label 0: it goes to label 2.
Lean proves that the source is still running after two steps while the linked
program has halted, and that this block family cannot satisfy 16AY's expansion
contract.  Therefore the linker contract is necessary, not decorative.
-/

namespace FoundationStoneTest16AZ

open FoundationStoneTest16AY

abbrev Label := Fin 3

def sourceProgram (l : Label) : Instr 1 Label :=
  if l = 2 then .halt else .inc 0 1

/-- Every source instruction receives exactly one local instruction. -/
def badBlocks : BlockFamily 1 Label where
  width := fun _ => 1
  nonempty := by intro; decide
  code := fun owner _ =>
    if owner = 2 then .halt
    else if owner = 0 then .inc 0 (.exit 2) -- the deliberate bad patch
    else .inc 0 (.exit 1)

def registers (n : Nat) : Fin 1 → Nat := fun _ => n

def source0 : State 1 Label := ⟨0, registers 0⟩
def source1 : State 1 Label := ⟨1, registers 1⟩
def source2 : State 1 Label := ⟨1, registers 2⟩

def linked0 : State 1 (LinkedLabel badBlocks) := State.map (entry badBlocks) source0
def linkedDead : State 1 (LinkedLabel badBlocks) :=
  ⟨entry badBlocks 2, registers 1⟩

/-- The source's first step goes to its live continuation. -/
theorem source_first_step : step sourceProgram source0 = some source1 := by
  simp [step, sourceProgram, source0, source1, registers, setCounter]
  funext i
  fin_cases i
  rfl

/-- The source is still running after its second step. -/
theorem source_two_steps : run sourceProgram 2 source0 = some source2 := by
  simp [run, step, sourceProgram, source0, source2, registers, setCounter]
  funext i
  fin_cases i
  rfl

/-- The wrong exit sends the linked execution to the real halt block. -/
theorem bad_first_step :
    step (linkedProgram badBlocks) linked0 = some linkedDead := by
  simp [step, linkedProgram, linkInstr, Instr.map, resolve, badBlocks,
    linked0, linkedDead, source0, registers, State.map, entry, setCounter]
  funext i
  fin_cases i
  rfl

theorem dead_block_really_halts :
    step (linkedProgram badBlocks) linkedDead = none := by
  rfl

/-- Observable failure: the linked machine halts on the second step. -/
theorem bad_link_false_halt :
    run (linkedProgram badBlocks) 2 linked0 = none := by
  rw [show run (linkedProgram badBlocks) 2 linked0 =
      run (linkedProgram badBlocks) 1 linkedDead by
        simp only [run, bad_first_step]]
  simp [run, dead_block_really_halts]

/-! ## The contract itself rejects the bad linker -/

/-- From `linked0`, every nonempty linked path ends immediately at
`linkedDead`: that state has no successor. -/
theorem only_bad_destination
    (t : State 1 (LinkedLabel badBlocks))
    (h : Relation.TransGen
      (fun u v => step (linkedProgram badBlocks) u = some v)
      linked0 t) : t = linkedDead := by
  induction h with
  | single hstep =>
      rw [bad_first_step] at hstep
      exact (Option.some.inj hstep).symm
  | tail hpath hlast ih =>
      subst ih
      rw [dead_block_really_halts] at hlast
      contradiction

theorem intended_entry_is_not_dead :
    State.map (entry badBlocks) source1 ≠ linkedDead := by
  intro h
  have hp := congrArg (fun s => s.pc.1) h
  simp [source1, linkedDead, State.map, entry] at hp

/-- The semantic block hypothesis of 16AY detects the bad patch. -/
theorem bad_blocks_fail_the_contract :
    ¬ ExpansionContract sourceProgram badBlocks := by
  intro h
  have path := h.advance source0 source1 source_first_step
  have hend := only_bad_destination _ path
  exact intended_entry_is_not_dead hend

/-- This is not an out-of-range accident: 16AY's syntactic halt theorem still
holds.  The error is precisely the wrong, but well-typed, exit. -/
theorem false_halt_is_explicit :
    linkedProgram badBlocks linkedDead.pc = .halt :=
  (linked_halts_only_explicitly badBlocks linkedDead).mp dead_block_really_halts

theorem turing_chamber_16AZ_certificate :
    run sourceProgram 2 source0 = some source2 ∧
    run (linkedProgram badBlocks) 2 linked0 = none ∧
    ¬ ExpansionContract sourceProgram badBlocks ∧
    linkedProgram badBlocks linkedDead.pc = .halt :=
  ⟨source_two_steps, bad_link_false_halt, bad_blocks_fail_the_contract,
   false_halt_is_explicit⟩

#print axioms source_first_step
#print axioms source_two_steps
#print axioms bad_first_step
#print axioms bad_link_false_halt
#print axioms bad_blocks_fail_the_contract
#print axioms turing_chamber_16AZ_certificate

end FoundationStoneTest16AZ
