import FoundationStoneTest16BH

/-!
# THE TURING CHAMBER — TEST 16BI: STACK BLOCKS RESPECT THEIR MACROS

Lean 4.35.0-rc2 / pinned Mathlib.

16BH proved bounded executions.  This file turns them into the semantic form
needed by the linker: a positive `Relation.TransGen` of genuine primitive
steps.  A small typed macro machine has one source step for push, pop or peek;
its completed states halt.  The routed 16BG program simulates every source
step and halts exactly at the corresponding typed continuation.

Mathlib's `StateTransition.tr_eval_dom` then lifts the local block proofs to
halting equivalence for arbitrary runs.  This is an actual `Respects` theorem,
not merely three numerical test executions.
-/

namespace FoundationStoneTest16BI

open FoundationStoneTest16AW
open FoundationStoneTest16BG
open FoundationStoneTest16BH

theorem run_succ_gives_reaches {L : Type} (P : L → Instr L) :
    ∀ n (s t : State L), run P (n + 1) s = some t →
      Relation.TransGen (fun u v => step P u = some v) s t := by
  intro n
  induction n with
  | zero =>
      intro s t h
      unfold run at h
      cases hs : step P s with
      | none => rw [hs] at h; contradiction
      | some s' =>
          rw [hs] at h
          simp only [run, Option.some.injEq] at h
          subst t
          exact Relation.TransGen.single hs
  | succ n ih =>
      intro s t h
      unfold run at h
      cases hs : step P s with
      | none => rw [hs] at h; contradiction
      | some s' =>
          rw [hs] at h
          exact Relation.TransGen.head hs (ih s' t h)

theorem positive_run_gives_reaches {L : Type} (P : L → Instr L)
    (n : Nat) (hn : 0 < n) (s t : State L) (h : run P n s = some t) :
    Relation.TransGen (fun u v => step P u = some v) s t := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact run_succ_gives_reaches P k s t h

inductive MacroCfg
  | push (d : Digit) (n : Nat)
  | pop (d : Digit) (n : Nat)
  | peek (d : Digit) (n : Nat)
  | done (exit : StackLabel) (a b : Nat)
deriving Repr

def macroStep : MacroCfg → Option MacroCfg
  | .push d n => some (.done (.push d .done) (FoundationStoneTest16AI.pushCode d n) 0)
  | .pop d n => some (.done (.pop (.done d)) n 0)
  | .peek d n => some (.done (.peek (.done d)) (FoundationStoneTest16AI.pushCode d n) 0)
  | .done _ _ _ => none

def encode : MacroCfg → State (RoutedLabel StackLabel)
  | .push d n => ⟨.work (.push d .mulLoop), n, 0⟩
  | .pop d n => ⟨.work (.pop .start), FoundationStoneTest16AI.pushCode d n, 0⟩
  | .peek d n =>
      ⟨.work (.peek (.pop .start)), FoundationStoneTest16AI.pushCode d n, 0⟩
  | .done exit a b => ⟨.next exit, a, b⟩

def Encodes (s : MacroCfg) (t : State (RoutedLabel StackLabel)) : Prop := encode s = t

theorem stack_blocks_respect_macros :
    StateTransition.Respects macroStep
      (step (routedProgram terminalOutcome)) Encodes := by
  intro s t hst
  subst t
  cases s with
  | push d n =>
      refine ⟨encode (.done (.push d .done)
        (FoundationStoneTest16AI.pushCode d n) 0), rfl, ?_⟩
      apply positive_run_gives_reaches _ (16 * n + d.val + 5) (by omega)
      exact routed_push_exact d n
  | pop d n =>
      refine ⟨encode (.done (.pop (.done d)) n 0), rfl, ?_⟩
      apply positive_run_gives_reaches _ (8 * n + d.val + 5) (by omega)
      exact routed_pop_exact d n
  | peek d n =>
      refine ⟨encode (.done (.peek (.done d))
        (FoundationStoneTest16AI.pushCode d n) 0), rfl, ?_⟩
      apply positive_run_gives_reaches _ (24 * n + 2 * d.val + 8) (by omega)
      exact routed_peek_exact d n
  | done exit a b => rfl

def MacroTerminates (s : MacroCfg) : Prop :=
  (StateTransition.eval macroStep s).Dom

def PrimitiveTerminates (s : State (RoutedLabel StackLabel)) : Prop :=
  (StateTransition.eval (step (routedProgram terminalOutcome)) s).Dom

theorem stack_macro_halting_iff (s : MacroCfg) :
    MacroTerminates s ↔ PrimitiveTerminates (encode s) := by
  unfold MacroTerminates PrimitiveTerminates
  exact (StateTransition.tr_eval_dom stack_blocks_respect_macros rfl).symm

/-! Red control: zero primitive steps cannot implement a nontrivial push. -/
theorem push_is_not_zero_steps (d : Digit) (n : Nat) :
    encode (.push d n) ≠ encode (.done (.push d .done)
      (FoundationStoneTest16AI.pushCode d n) 0) := by
  intro h
  have := congrArg (fun s => s.pc) h
  contradiction

theorem turing_chamber_16BI_certificate :
    StateTransition.Respects macroStep
      (step (routedProgram terminalOutcome)) Encodes ∧
    (∀ s, MacroTerminates s ↔ PrimitiveTerminates (encode s)) ∧
    (∀ d n, encode (.push d n) ≠ encode (.done (.push d .done)
      (FoundationStoneTest16AI.pushCode d n) 0)) :=
  ⟨stack_blocks_respect_macros, stack_macro_halting_iff, push_is_not_zero_steps⟩

#print axioms run_succ_gives_reaches
#print axioms positive_run_gives_reaches
#print axioms stack_blocks_respect_macros
#print axioms stack_macro_halting_iff
#print axioms turing_chamber_16BI_certificate

end FoundationStoneTest16BI
