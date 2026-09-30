import FoundationStoneTest16BE

/-!
# THE TURING CHAMBER — TEST 16BF: ONE COMPLETE FINITE PEEK BLOCK

Lean 4.35.0-rc2 / pinned Mathlib.

Peek is not a new arithmetic primitive.  It is the proved composition:

    pop the shifted digit; then push exactly that digit back.

The popped digit is retained in finite control while the tail is restored.
For every `d : Fin 4` and tail code `n`, the finite program reaches a `done d`
continuation with the original stack code and zero scratch.  The exact cost is

    24*n + 2*d.val + 6.

Empty input reaches a separate `empty` continuation in one step.  A shadow
program that stops after pop is the red control: it knows the top digit but has
changed the stack, so observation without restoration is not peek.
-/

namespace FoundationStoneTest16BF

open FoundationStoneTest16AW

abbrev Digit := Fin 4

inductive PeekLabel
  | pop (label : FoundationStoneTest16BE.PopLabel)
  | push (digit : Digit) (label : FoundationStoneTest16BD.PushLabel)
  | empty
  | done (digit : Digit)
  | bad
deriving DecidableEq, Repr, Fintype

/-- Relabel pop's outcomes: a successful pop enters the matching push block. -/
def popName : FoundationStoneTest16BE.PopLabel → PeekLabel
  | .empty => .empty
  | .done d => .push d .mulLoop
  | .bad => .bad
  | l => .pop l

/-- Relabel one digit-specific push block into peek. -/
def pushName (d : Digit) : FoundationStoneTest16BD.PushLabel → PeekLabel
  | .done => .done d
  | .bad => .bad
  | l => .push d l

def peekProgram : PeekLabel → Instr PeekLabel
  | .pop l => FoundationStoneTest16BC.mapInstr popName
      (FoundationStoneTest16BE.popProgram l)
  | .push d l => FoundationStoneTest16BC.mapInstr (pushName d)
      (FoundationStoneTest16BD.pushProgram d l)
  | .empty => .halt
  | .done _ => .halt
  | .bad => .halt

/-! ## Pop prefix -/

/-- The shadow has the same pop code but halts at every handoff target. -/
def popShadow : PeekLabel → Instr PeekLabel
  | .pop l => FoundationStoneTest16BC.mapInstr popName
      (FoundationStoneTest16BE.popProgram l)
  | _ => .halt

theorem popShadow_matches : ∀ l,
    popShadow (popName l) = FoundationStoneTest16BC.mapInstr popName
      (FoundationStoneTest16BE.popProgram l) := by
  intro l
  cases l <;> rfl

theorem pop_shadow_exact (d : Digit) (n : Nat) :
    run popShadow (8 * n + d.val + 3)
        ⟨PeekLabel.pop .start, FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨PeekLabel.push d .mulLoop, n, 0⟩ := by
  have h := FoundationStoneTest16BC.run_relabels popName
    FoundationStoneTest16BE.popProgram popShadow popShadow_matches
    (8 * n + d.val + 3)
    (⟨FoundationStoneTest16BE.PopLabel.start,
      FoundationStoneTest16AI.pushCode d n, 0⟩ :
      State FoundationStoneTest16BE.PopLabel)
  rw [FoundationStoneTest16BE.pop_exact d n] at h
  simpa [FoundationStoneTest16BC.mapState, popName] using h

theorem pop_shadow_success_is_peek_success (s t : State PeekLabel)
    (h : step popShadow s = some t) : step peekProgram s = some t := by
  obtain ⟨pc, a, b⟩ := s
  cases pc with
  | pop l => simpa [step, popShadow, peekProgram] using h
  | push d l => simp [step, popShadow] at h
  | empty => simp [step, popShadow] at h
  | done d => simp [step, popShadow] at h
  | bad => simp [step, popShadow] at h

theorem successful_pop_run_enters_peek : ∀ n s t,
    run popShadow n s = some t → run peekProgram n s = some t := by
  intro n
  induction n with
  | zero => intro s t h; simpa [run] using h
  | succ n ih =>
      intro s t h
      unfold run at h ⊢
      cases hs : step popShadow s with
      | none => simp [hs] at h
      | some s' =>
          rw [hs] at h
          rw [pop_shadow_success_is_peek_success s s' hs]
          exact ih s' t h

theorem pop_enters_matching_push (d : Digit) (n : Nat) :
    run peekProgram (8 * n + d.val + 3)
        ⟨PeekLabel.pop .start, FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨PeekLabel.push d .mulLoop, n, 0⟩ :=
  successful_pop_run_enters_peek _ _ _ (pop_shadow_exact d n)

/-! ## Push suffix -/

theorem pushName_injective (d : Digit) : Function.Injective (pushName d) := by
  intro x y h
  cases x <;> cases y <;> simp_all [pushName]

theorem push_inside_matches (d : Digit) : ∀ l,
    peekProgram (pushName d l) = FoundationStoneTest16BC.mapInstr (pushName d)
      (FoundationStoneTest16BD.pushProgram d l) := by
  intro l
  cases l with
  | mulLoop => rfl
  | mulAdd slot => rfl
  | restoreLoop => rfl
  | restoreCredit => rfl
  | addDigit slot => rfl
  | done => rfl
  | bad => rfl

theorem push_inside_exact (d : Digit) (n : Nat) :
    run peekProgram (16 * n + d.val + 3)
        ⟨PeekLabel.push d .mulLoop, n, 0⟩ =
      some ⟨PeekLabel.done d, FoundationStoneTest16AI.pushCode d n, 0⟩ := by
  have h := FoundationStoneTest16BC.run_relabels (pushName d)
    (FoundationStoneTest16BD.pushProgram d) peekProgram (push_inside_matches d)
    (16 * n + d.val + 3)
    (⟨FoundationStoneTest16BD.PushLabel.mulLoop, n, 0⟩ :
      State FoundationStoneTest16BD.PushLabel)
  rw [FoundationStoneTest16BD.push_exact d n] at h
  simpa [FoundationStoneTest16BC.mapState, pushName] using h

/-! ## Complete contracts -/

theorem peek_exact (d : Digit) (n : Nat) :
    run peekProgram (24 * n + 2 * d.val + 6)
        ⟨PeekLabel.pop .start, FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨PeekLabel.done d, FoundationStoneTest16AI.pushCode d n, 0⟩ := by
  rw [show 24 * n + 2 * d.val + 6 =
      (8 * n + d.val + 3) + (16 * n + d.val + 3) by omega,
    run_add, pop_enters_matching_push]
  simp only
  exact push_inside_exact d n

theorem peek_empty :
    run peekProgram 1 ⟨PeekLabel.pop .start, 0, 0⟩ =
      some ⟨PeekLabel.empty, 0, 0⟩ := by decide

def fivePeekProgram (i : FoundationStoneTest16BB.StackReg) :
    PeekLabel → FoundationStoneTest16AY.Instr 5 PeekLabel :=
  FoundationStoneTest16BB.liftAWProgram i peekProgram

theorem five_peek_exact (i : FoundationStoneTest16BB.StackReg)
    (base : FoundationStoneTest16BB.Reg5 → Nat) (d : Digit) (n : Nat) :
    FoundationStoneTest16AY.run (fivePeekProgram i)
        (24 * n + 2 * d.val + 6)
        (FoundationStoneTest16BB.embed i base (PeekLabel.pop .start)
          (FoundationStoneTest16AI.pushCode d n) 0) =
      some (FoundationStoneTest16BB.embed i base (PeekLabel.done d)
        (FoundationStoneTest16AI.pushCode d n) 0) := by
  have h := FoundationStoneTest16BB.run_lift_AW i base peekProgram
    (24 * n + 2 * d.val + 6)
    (⟨PeekLabel.pop .start, FoundationStoneTest16AI.pushCode d n, 0⟩ :
      State PeekLabel)
  rw [peek_exact d n] at h
  simpa [fivePeekProgram, FoundationStoneTest16BB.embedAW] using h

theorem peek_control_is_finite : Fintype.card PeekLabel = 85 := by decide

/-! Red control: stopping after pop discovers the digit but fails to restore
the original stack. -/
theorem pop_without_push_is_not_peek :
    (run popShadow (8 * 1 + (0 : Digit).val + 3)
      ⟨PeekLabel.pop .start, FoundationStoneTest16AI.pushCode 0 1, 0⟩).map
        (fun s => s.a) = some 1 ∧
    FoundationStoneTest16AI.pushCode 0 1 = 6 := by
  decide

theorem turing_chamber_16BF_certificate :
    Fintype.card PeekLabel = 85 ∧
    run peekProgram 1 ⟨PeekLabel.pop .start, 0, 0⟩ =
      some ⟨PeekLabel.empty, 0, 0⟩ ∧
    (∀ d n, run peekProgram (24 * n + 2 * d.val + 6)
      ⟨PeekLabel.pop .start, FoundationStoneTest16AI.pushCode d n, 0⟩ =
        some ⟨PeekLabel.done d, FoundationStoneTest16AI.pushCode d n, 0⟩) ∧
    (∀ i base d n,
      FoundationStoneTest16AY.run (fivePeekProgram i)
        (24 * n + 2 * d.val + 6)
        (FoundationStoneTest16BB.embed i base (PeekLabel.pop .start)
          (FoundationStoneTest16AI.pushCode d n) 0) =
        some (FoundationStoneTest16BB.embed i base (PeekLabel.done d)
          (FoundationStoneTest16AI.pushCode d n) 0)) ∧
    FoundationStoneTest16AI.pushCode 0 1 = 6 :=
  ⟨peek_control_is_finite, peek_empty, peek_exact, five_peek_exact, by decide⟩

#print axioms peek_exact
#print axioms five_peek_exact
#print axioms pop_without_push_is_not_peek
#print axioms turing_chamber_16BF_certificate

end FoundationStoneTest16BF
