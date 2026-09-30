import FoundationStoneTest16BD

/-!
# THE TURING CHAMBER — TEST 16BE: ONE COMPLETE FINITE POP BLOCK

Lean 4.35.0-rc2 / pinned Mathlib.

This is the inverse companion to 16BD.  A single finite primitive program:

1. distinguishes the empty stack;
2. removes the shifted end-marker offset;
3. divides by five;
4. carries the remainder in finite control;
5. restores the quotient to the selected stack register;
6. restores the scratch register to zero.

For every digit `d : Fin 4` and numeric stack tail `n`, Lean proves

    pushCode d n  ↦  (d, n)

in exactly `8*n + d.val + 3` primitive steps.  Empty input takes one step to
its distinct `empty` continuation.  The finite remainder label `4` is routed
to `bad`; it is unreachable for valid shifted stack codes.

The division phase reuses 16BC by a shadow program.  A general lemma proves
that every successful shadow run remains a run after its terminal labels are
patched into restoration code.  Thus exit patching is proved, not inferred.
-/

namespace FoundationStoneTest16BE

open FoundationStoneTest16AW

abbrev Digit := Fin 4

inductive PopLabel
  | start
  | scan (slot : Fin 5)
  | credit
  | restore (remainder : Fin 5)
  | restoreCredit (remainder : Fin 5)
  | empty
  | done (digit : Digit)
  | bad
deriving DecidableEq, Repr, Fintype

def popProgram : PopLabel → Instr PopLabel
  | .start => .dec false (.scan 0) .empty
  | .scan slot =>
      if h : slot.val < 4 then
        .dec false (.scan ⟨slot.val + 1, by omega⟩) (.restore slot)
      else .dec false .credit (.restore slot)
  | .credit => .inc true (.scan 0)
  | .restore remainder =>
      .dec true (.restoreCredit remainder)
        (if h : remainder.val < 4 then .done ⟨remainder.val, h⟩ else .bad)
  | .restoreCredit remainder => .inc false (.restore remainder)
  | .empty => .halt
  | .done _ => .halt
  | .bad => .halt

/-! ## Arithmetic identities for shifted base-five digits -/

theorem push_sub_one (d : Digit) (n : Nat) :
    FoundationStoneTest16AI.pushCode d n - 1 = d.val + 5 * n := by
  unfold FoundationStoneTest16AI.pushCode
  omega

theorem push_quotient (d : Digit) (n : Nat) :
    (FoundationStoneTest16AI.pushCode d n - 1) / 5 = n := by
  rw [push_sub_one, Nat.add_mul_div_left _ _ (by decide)]
  rw [Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem push_remainder (d : Digit) (n : Nat) :
    (FoundationStoneTest16AI.pushCode d n - 1) % 5 = d.val := by
  rw [push_sub_one, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## The finite division shadow and the patch theorem -/

def divName : FoundationStoneTest16BC.D5 → PopLabel
  | .scan slot => .scan slot
  | .credit => .credit
  | .exit remainder => .restore remainder
  | .bad => .bad

theorem divName_injective : Function.Injective divName := by
  intro x y h
  cases x <;> cases y <;> simp_all [divName]

/-- Before patching, the remainder exits halt. -/
def divShadow : PopLabel → Instr PopLabel
  | .scan slot => FoundationStoneTest16BC.mapInstr divName
      (FoundationStoneTest16BC.div5 (.scan slot))
  | .credit => FoundationStoneTest16BC.mapInstr divName
      (FoundationStoneTest16BC.div5 .credit)
  | .restore remainder => FoundationStoneTest16BC.mapInstr divName
      (FoundationStoneTest16BC.div5 (.exit remainder))
  | .bad => FoundationStoneTest16BC.mapInstr divName
      (FoundationStoneTest16BC.div5 .bad)
  | _ => .halt

theorem divShadow_matches : ∀ l,
    divShadow (divName l) =
      FoundationStoneTest16BC.mapInstr divName (FoundationStoneTest16BC.div5 l) := by
  intro l
  cases l <;> rfl

theorem div_shadow_exact (m : Nat) :
    run divShadow (6 * (m / 5) + (m % 5 + 1)) ⟨PopLabel.scan 0, m, 0⟩ =
      some ⟨PopLabel.restore ⟨m % 5, Nat.mod_lt m (by decide)⟩, 0, m / 5⟩ := by
  have h := FoundationStoneTest16BC.run_relabels divName FoundationStoneTest16BC.div5
    divShadow divShadow_matches
    (6 * (m / 5) + (m % 5 + 1))
    (⟨FoundationStoneTest16BC.D5.scan 0, m, 0⟩ : State FoundationStoneTest16BC.D5)
  rw [FoundationStoneTest16BC.div5_exact m] at h
  simpa [FoundationStoneTest16BC.mapState, divName] using h

/-- If a shadow step succeeds, patching its terminal labels cannot change that
step.  The only changed labels halted in the shadow, so they cannot satisfy the
premise. -/
theorem shadow_success_is_pop_success (s t : State PopLabel)
    (h : step divShadow s = some t) : step popProgram s = some t := by
  obtain ⟨pc, a, b⟩ := s
  cases pc with
  | start => simp [step, divShadow] at h
  | scan slot =>
      fin_cases slot <;>
        simpa [step, divShadow, popProgram, divName,
          FoundationStoneTest16BC.mapInstr, FoundationStoneTest16BC.div5,
          FoundationStoneTest16AW.get, FoundationStoneTest16AW.set] using h
  | credit => simpa [step, divShadow, popProgram, divName,
      FoundationStoneTest16BC.mapInstr, FoundationStoneTest16BC.div5,
      FoundationStoneTest16AW.get, FoundationStoneTest16AW.set] using h
  | restore remainder => simp [step, divShadow, divName,
      FoundationStoneTest16BC.mapInstr, FoundationStoneTest16BC.div5] at h
  | restoreCredit remainder => simp [step, divShadow] at h
  | empty => simp [step, divShadow] at h
  | done digit => simp [step, divShadow] at h
  | bad => simp [step, divShadow, divName, FoundationStoneTest16BC.mapInstr,
      FoundationStoneTest16BC.div5] at h

theorem successful_run_survives_patch : ∀ n s t,
    run divShadow n s = some t → run popProgram n s = some t := by
  intro n
  induction n with
  | zero => intro s t h; simpa [run] using h
  | succ n ih =>
      intro s t h
      unfold run at h ⊢
      cases hs : step divShadow s with
      | none => simp [hs] at h
      | some s' =>
          rw [hs] at h
          rw [shadow_success_is_pop_success s s' hs]
          exact ih s' t h

theorem division_enters_restore (d : Digit) (n : Nat) :
    run popProgram (6 * n + (d.val + 1))
        ⟨PopLabel.scan 0, FoundationStoneTest16AI.pushCode d n - 1, 0⟩ =
      some ⟨PopLabel.restore ⟨d.val, by omega⟩, 0, n⟩ := by
  have h := div_shadow_exact (FoundationStoneTest16AI.pushCode d n - 1)
  have hp := successful_run_survives_patch _ _ _ h
  simpa [push_quotient, push_remainder] using hp

/-! ## Restoration and complete contracts -/

theorem restore_cycle (r : Fin 5) (a b : Nat) (hb : 0 < b) :
    run popProgram 2 ⟨PopLabel.restore r, a, b⟩ =
      some ⟨PopLabel.restore r, a + 1, b - 1⟩ := by
  simp [run, step, popProgram, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set, hb.ne']

theorem restore_groups (r : Fin 5) : ∀ q a,
    run popProgram (2 * q) ⟨PopLabel.restore r, a, q⟩ =
      some ⟨PopLabel.restore r, a + q, 0⟩ := by
  intro q
  induction q with
  | zero => intro a; simp [run]
  | succ q ih =>
      intro a
      rw [show 2 * (q + 1) = 2 + 2 * q by omega, run_add,
        restore_cycle r a (q + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [ih (a + 1)]
      congr 2
      omega

theorem restore_valid_digit (d : Digit) (n : Nat) :
    run popProgram (2 * n + 1) ⟨PopLabel.restore ⟨d.val, by omega⟩, 0, n⟩ =
      some ⟨PopLabel.done d, n, 0⟩ := by
  rw [run_add, restore_groups]
  simp [run, step, popProgram, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

theorem pop_empty :
    run popProgram 1 ⟨PopLabel.start, 0, 0⟩ =
      some ⟨PopLabel.empty, 0, 0⟩ := by decide

theorem start_nonempty (d : Digit) (n : Nat) :
    run popProgram 1
        ⟨PopLabel.start, FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨PopLabel.scan 0, FoundationStoneTest16AI.pushCode d n - 1, 0⟩ := by
  simp [run, step, popProgram, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set, FoundationStoneTest16AI.pushCode]

/-- The complete two-register pop contract. -/
theorem pop_exact (d : Digit) (n : Nat) :
    run popProgram (8 * n + d.val + 3)
        ⟨PopLabel.start, FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨PopLabel.done d, n, 0⟩ := by
  rw [show 8 * n + d.val + 3 =
      1 + ((6 * n + (d.val + 1)) + (2 * n + 1)) by omega,
    run_add, start_nonempty]
  simp only
  rw [run_add, division_enters_restore]
  simp only
  rw [restore_valid_digit]

/-! ## Five-counter installation -/

def fivePopProgram (i : FoundationStoneTest16BB.StackReg) :
    PopLabel → FoundationStoneTest16AY.Instr 5 PopLabel :=
  FoundationStoneTest16BB.liftAWProgram i popProgram

theorem five_pop_exact (i : FoundationStoneTest16BB.StackReg)
    (base : FoundationStoneTest16BB.Reg5 → Nat) (d : Digit) (n : Nat) :
    FoundationStoneTest16AY.run (fivePopProgram i) (8 * n + d.val + 3)
        (FoundationStoneTest16BB.embed i base PopLabel.start
          (FoundationStoneTest16AI.pushCode d n) 0) =
      some (FoundationStoneTest16BB.embed i base (PopLabel.done d) n 0) := by
  have h := FoundationStoneTest16BB.run_lift_AW i base popProgram
    (8 * n + d.val + 3)
    (⟨PopLabel.start, FoundationStoneTest16AI.pushCode d n, 0⟩ : State PopLabel)
  rw [pop_exact d n] at h
  simpa [fivePopProgram, FoundationStoneTest16BB.embedAW] using h

theorem pop_control_is_finite : Fintype.card PopLabel = 23 := by decide

/-! Red control: treating the shifted code as an unshifted base-five number
returns the wrong top digit on the first symbol. -/
theorem missing_subtract_one_reads_wrong_digit :
    FoundationStoneTest16AI.pushCode 0 0 % 5 = 1 ∧ (0 : Digit).val = 0 := by decide

theorem turing_chamber_16BE_certificate :
    Fintype.card PopLabel = 23 ∧
    run popProgram 1 ⟨PopLabel.start, 0, 0⟩ = some ⟨PopLabel.empty, 0, 0⟩ ∧
    (∀ d n, run popProgram (8 * n + d.val + 3)
      ⟨PopLabel.start, FoundationStoneTest16AI.pushCode d n, 0⟩ =
        some ⟨PopLabel.done d, n, 0⟩) ∧
    (∀ i base d n,
      FoundationStoneTest16AY.run (fivePopProgram i) (8 * n + d.val + 3)
        (FoundationStoneTest16BB.embed i base PopLabel.start
          (FoundationStoneTest16AI.pushCode d n) 0) =
        some (FoundationStoneTest16BB.embed i base (PopLabel.done d) n 0)) ∧
    FoundationStoneTest16AI.pushCode 0 0 % 5 ≠ (0 : Digit).val :=
  ⟨pop_control_is_finite, pop_empty, pop_exact, five_pop_exact, by decide⟩

#print axioms pop_exact
#print axioms five_pop_exact
#print axioms successful_run_survives_patch
#print axioms turing_chamber_16BE_certificate

end FoundationStoneTest16BE
