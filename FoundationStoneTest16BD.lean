import FoundationStoneTest16BC
import FoundationStoneTest16AI

/-!
# THE TURING CHAMBER — TEST 16BD: ONE COMPLETE FINITE PUSH BLOCK

Lean 4.35.0-rc2 / pinned Mathlib.

16BC made the arithmetic cores genuinely finite.  This test performs the
first complete exit patching: multiplication by five, restoration from the
scratch counter, and insertion of one shifted base-five digit are one finite
primitive program with one entry and one typed `done` continuation.

For a digit `d : Fin 4` and an encoded stack `n`, the program starts with

    A = n, B = 0

and reaches

    A = (d+1) + 5*n, B = 0.

The run length is exact: `16*n + d.val + 3`.  Every step is increment or
zero-test/decrement.  The same program is then embedded in any of the four
logical stack registers of the primitive five-counter machine from 16BB;
the other three stacks are unchanged and register 4 is restored to zero.

The red control deliberately patches the zero exit directly to `done`.  On
the empty stack it returns zero instead of the code for `[0]`, proving that
the exit wiring is a semantic obligation rather than decorative bookkeeping.

Scope: this is the first complete Layer-B1 stack instruction, `push`.  Pop and
peek still require the finite division remainder to be carried through the
restoration phase; they are not claimed here.
-/

namespace FoundationStoneTest16BD

abbrev Digit := Fin 4

/-- All labels of the stitched push block. -/
inductive PushLabel
  | mulLoop
  | mulAdd (slot : Fin 5)
  | restoreLoop
  | restoreCredit
  | addDigit (slot : Fin 4)
  | done
  | bad
deriving DecidableEq, Repr, Fintype

/-- One complete primitive push program.  `slot` counts the remaining
increments minus one. -/
def pushProgram (d : Digit) : PushLabel → FoundationStoneTest16AW.Instr PushLabel
  | .mulLoop => .dec false (.mulAdd 4) .restoreLoop
  | .mulAdd slot =>
      .inc true (if slot.val = 0 then .mulLoop
        else .mulAdd ⟨slot.val - 1, by omega⟩)
  | .restoreLoop => .dec true .restoreCredit (.addDigit d)
  | .restoreCredit => .inc false .restoreLoop
  | .addDigit slot =>
      .inc false (if slot.val = 0 then .done
        else .addDigit ⟨slot.val - 1, by omega⟩)
  | .done => .halt
  | .bad => .halt

/-! ## Multiplication phase -/

theorem mul_add_exact (d : Digit) (slot : Fin 5) (a b : Nat) :
    FoundationStoneTest16AW.run (pushProgram d) (slot.val + 1) ⟨.mulAdd slot, a, b⟩ =
      some ⟨.mulLoop, a, b + slot.val + 1⟩ := by
  fin_cases slot <;> simp [FoundationStoneTest16AW.run, FoundationStoneTest16AW.step, pushProgram, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

theorem mul_cycle (d : Digit) (a b : Nat) (ha : 0 < a) :
    FoundationStoneTest16AW.run (pushProgram d) 6 ⟨.mulLoop, a, b⟩ =
      some ⟨.mulLoop, a - 1, b + 5⟩ := by
  rw [show 6 = 1 + 5 by omega, FoundationStoneTest16AW.run_add]
  simp [FoundationStoneTest16AW.run, FoundationStoneTest16AW.step, pushProgram, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set, ha.ne']

theorem mul_groups (d : Digit) : ∀ n b,
    FoundationStoneTest16AW.run (pushProgram d) (6 * n) ⟨.mulLoop, n, b⟩ =
      some ⟨.mulLoop, 0, b + 5 * n⟩ := by
  intro n
  induction n with
  | zero => intro b; simp [FoundationStoneTest16AW.run]
  | succ n ih =>
      intro b
      rw [show 6 * (n + 1) = 6 + 6 * n by omega, FoundationStoneTest16AW.run_add,
        mul_cycle d (n + 1) b (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [ih (b + 5)]
      congr 2
      omega

theorem multiply_enters_restore (d : Digit) (n : Nat) :
    FoundationStoneTest16AW.run (pushProgram d) (6 * n + 1) ⟨.mulLoop, n, 0⟩ =
      some ⟨.restoreLoop, 0, 5 * n⟩ := by
  rw [FoundationStoneTest16AW.run_add, mul_groups]
  simp [FoundationStoneTest16AW.run, FoundationStoneTest16AW.step, pushProgram, FoundationStoneTest16AW.get]

/-! ## Restoration phase -/

theorem restore_cycle (d : Digit) (a b : Nat) (hb : 0 < b) :
    FoundationStoneTest16AW.run (pushProgram d) 2 ⟨.restoreLoop, a, b⟩ =
      some ⟨.restoreLoop, a + 1, b - 1⟩ := by
  simp [FoundationStoneTest16AW.run, FoundationStoneTest16AW.step, pushProgram, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set, hb.ne']

theorem restore_groups (d : Digit) : ∀ q a,
    FoundationStoneTest16AW.run (pushProgram d) (2 * q) ⟨.restoreLoop, a, q⟩ =
      some ⟨.restoreLoop, a + q, 0⟩ := by
  intro q
  induction q with
  | zero => intro a; simp [FoundationStoneTest16AW.run]
  | succ q ih =>
      intro a
      rw [show 2 * (q + 1) = 2 + 2 * q by omega, FoundationStoneTest16AW.run_add,
        restore_cycle d a (q + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [ih (a + 1)]
      congr 2
      omega

theorem restore_enters_digit (d : Digit) (q : Nat) :
    FoundationStoneTest16AW.run (pushProgram d) (2 * q + 1) ⟨.restoreLoop, 0, q⟩ =
      some ⟨.addDigit d, q, 0⟩ := by
  rw [FoundationStoneTest16AW.run_add, restore_groups]
  simp [FoundationStoneTest16AW.run, FoundationStoneTest16AW.step, pushProgram, FoundationStoneTest16AW.get]

/-! ## Shifted digit and complete contract -/

theorem add_digit_exact (d slot : Digit) (a : Nat) :
    FoundationStoneTest16AW.run (pushProgram d) (slot.val + 1) ⟨.addDigit slot, a, 0⟩ =
      some ⟨.done, a + slot.val + 1, 0⟩ := by
  fin_cases slot <;> simp [FoundationStoneTest16AW.run, FoundationStoneTest16AW.step, pushProgram, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

/-- The complete two-register push contract. -/
theorem push_exact (d : Digit) (n : Nat) :
    FoundationStoneTest16AW.run (pushProgram d) (16 * n + d.val + 3) ⟨.mulLoop, n, 0⟩ =
      some ⟨.done, FoundationStoneTest16AI.pushCode d n, 0⟩ := by
  rw [show 16 * n + d.val + 3 =
      (6 * n + 1) + ((10 * n + 1) + (d.val + 1)) by omega,
    FoundationStoneTest16AW.run_add, multiply_enters_restore]
  simp only
  rw [FoundationStoneTest16AW.run_add]
  have hr := restore_enters_digit d (5 * n)
  have hr' : FoundationStoneTest16AW.run (pushProgram d) (10 * n + 1)
      ⟨PushLabel.restoreLoop, 0, 5 * n⟩ =
      some ⟨PushLabel.addDigit d, 5 * n, 0⟩ := by
    have heq : 2 * (5 * n) + 1 = 10 * n + 1 := by ring
    rw [← heq]
    exact hr
  rw [hr']
  simp only
  rw [add_digit_exact d d]
  unfold FoundationStoneTest16AI.pushCode
  congr 2
  omega

/-! ## Installation in the primitive five-counter machine -/

def fivePushProgram (i : FoundationStoneTest16BB.StackReg) (d : Digit) :
    PushLabel → FoundationStoneTest16AY.Instr 5 PushLabel :=
  FoundationStoneTest16BB.liftAWProgram i (pushProgram d)

theorem five_push_exact (i : FoundationStoneTest16BB.StackReg) (base : FoundationStoneTest16BB.Reg5 → Nat)
    (d : Digit) (n : Nat) :
    FoundationStoneTest16AY.run (fivePushProgram i d) (16 * n + d.val + 3)
        (FoundationStoneTest16BB.embed i base PushLabel.mulLoop n 0) =
      some (FoundationStoneTest16BB.embed i base PushLabel.done (FoundationStoneTest16AI.pushCode d n) 0) := by
  have h := FoundationStoneTest16BB.run_lift_AW i base (pushProgram d)
    (16 * n + d.val + 3)
    (⟨PushLabel.mulLoop, n, 0⟩ : FoundationStoneTest16AW.State PushLabel)
  rw [push_exact d n] at h
  simpa [fivePushProgram, FoundationStoneTest16BB.embedAW] using h

theorem five_push_boundary (i : FoundationStoneTest16BB.StackReg) (base : FoundationStoneTest16BB.Reg5 → Nat)
    (d : Digit) (n : Nat) :
    let out := FoundationStoneTest16BB.embed i base PushLabel.done (FoundationStoneTest16AI.pushCode d n) 0
    out.counters (FoundationStoneTest16BB.stackReg i) = FoundationStoneTest16AI.pushCode d n ∧
    out.counters FoundationStoneTest16BB.tempReg = 0 ∧
    ∀ j, j ≠ FoundationStoneTest16BB.stackReg i → j ≠ FoundationStoneTest16BB.tempReg → out.counters j = base j := by
  simp only [FoundationStoneTest16BB.embed, FoundationStoneTest16BB.install_stack, FoundationStoneTest16BB.install_temp, true_and]
  intro j hji hjt
  exact FoundationStoneTest16BB.install_other i base (FoundationStoneTest16AI.pushCode d n) 0 j hji hjt

/-! ## Finiteness and a bad-patch red control -/

theorem push_control_is_finite : Fintype.card PushLabel = 14 := by decide

/-- The tempting bad linker jumps from the multiplication zero exit directly
to `done`, omitting restoration and the shifted digit. -/
def brokenPushProgram (d : Digit) : PushLabel → FoundationStoneTest16AW.Instr PushLabel
  | .mulLoop => .dec false (.mulAdd 4) .done
  | l => pushProgram d l

theorem bad_patch_fails_on_empty_zero_digit :
    FoundationStoneTest16AW.run (brokenPushProgram 0) 1 ⟨PushLabel.mulLoop, 0, 0⟩ =
      some ⟨PushLabel.done, 0, 0⟩ ∧
    FoundationStoneTest16AI.pushCode 0 0 = 1 := by
  decide

theorem bad_patch_does_not_push :
    (FoundationStoneTest16AW.run (brokenPushProgram 0) 1 ⟨PushLabel.mulLoop, 0, 0⟩).map
        (fun s => s.a) ≠ some (FoundationStoneTest16AI.pushCode 0 0) := by
  decide

theorem turing_chamber_16BD_certificate :
    Fintype.card PushLabel = 14 ∧
    (∀ d n, FoundationStoneTest16AW.run (pushProgram d) (16 * n + d.val + 3)
      ⟨PushLabel.mulLoop, n, 0⟩ =
        some ⟨PushLabel.done, FoundationStoneTest16AI.pushCode d n, 0⟩) ∧
    (∀ i base d n, FoundationStoneTest16AY.run (fivePushProgram i d) (16 * n + d.val + 3)
      (FoundationStoneTest16BB.embed i base PushLabel.mulLoop n 0) =
        some (FoundationStoneTest16BB.embed i base PushLabel.done (FoundationStoneTest16AI.pushCode d n) 0)) ∧
    (∀ i base d n,
      let out := FoundationStoneTest16BB.embed i base PushLabel.done (FoundationStoneTest16AI.pushCode d n) 0
      out.counters (FoundationStoneTest16BB.stackReg i) = FoundationStoneTest16AI.pushCode d n ∧
      out.counters FoundationStoneTest16BB.tempReg = 0 ∧
      ∀ j, j ≠ FoundationStoneTest16BB.stackReg i → j ≠ FoundationStoneTest16BB.tempReg → out.counters j = base j) ∧
    (FoundationStoneTest16AW.run (brokenPushProgram 0) 1 ⟨PushLabel.mulLoop, 0, 0⟩).map
      (fun s => s.a) ≠ some (FoundationStoneTest16AI.pushCode 0 0) :=
  ⟨push_control_is_finite, push_exact, five_push_exact, five_push_boundary,
   bad_patch_does_not_push⟩

#print axioms push_exact
#print axioms five_push_exact
#print axioms five_push_boundary
#print axioms bad_patch_does_not_push
#print axioms turing_chamber_16BD_certificate

end FoundationStoneTest16BD
