import FoundationStoneTest16BG

/-!
# THE TURING CHAMBER — TEST 16BH: TYPED STACK CONTINUATIONS

Lean 4.35.0-rc2 / pinned Mathlib.

16BG's stack blocks ended at explicit local halts.  A compiler must instead
continue at a source-selected label.  This file replaces every local terminal
by a two-instruction, counter-preserving bridge to a typed continuation.

There are no raw program counters.  `work l` is owned by the finite 16BG
block, `restore l` is its private bridge state, and `next k` is an explicitly
typed source continuation.  Lean proves that every nonhalting prefix is
transported unchanged and that push, pop and peek reach their chosen
continuations with both counters exactly as specified.
-/

namespace FoundationStoneTest16BH

open FoundationStoneTest16AW
open FoundationStoneTest16BG

inductive RoutedLabel (K : Type)
  | work (l : StackLabel)
  | restore (l : StackLabel)
  | next (k : K)
deriving Repr

def routeInstr {K : Type} : Instr StackLabel → Instr (RoutedLabel K)
  | .inc body next => .inc body (.work next)
  | .dec body positive zero => .dec body (.work positive) (.work zero)
  | .halt => .halt

/-- Replace a local halt by an increment/decrement bridge.  The temporary
increment is on A, and the following decrement restores A exactly. -/
def routedProgram {K : Type} (exit : StackLabel → K) : RoutedLabel K → Instr (RoutedLabel K)
  | .work l =>
      match stackProgram l with
      | .halt => .inc false (.restore l)
      | i => routeInstr i
  | .restore l => .dec false (.next (exit l)) (.next (exit l))
  | .next _ => .halt

def mapWork {K : Type} (s : State StackLabel) : State (RoutedLabel K) :=
  ⟨.work s.pc, s.a, s.b⟩

theorem step_work_of_some {K : Type} (exit : StackLabel → K)
    (s t : State StackLabel) (h : step stackProgram s = some t) :
    step (routedProgram exit) (mapWork s) = some (mapWork t) := by
  rcases s with ⟨pc, a, b⟩
  rcases t with ⟨pc', a', b'⟩
  unfold step at h ⊢
  cases hi : stackProgram pc with
  | halt => simp [hi] at h
  | inc body next =>
      cases body <;> simp_all [routedProgram, routeInstr, mapWork,
        FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
  | dec body positive zero =>
      cases body with
      | false =>
          by_cases hz : a = 0 <;>
            simp_all [routedProgram, routeInstr, mapWork,
              FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
      | true =>
          by_cases hz : b = 0 <;>
            simp_all [routedProgram, routeInstr, mapWork,
              FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

theorem run_work_of_some {K : Type} (exit : StackLabel → K) :
    ∀ n s t, run stackProgram n s = some t →
      run (routedProgram exit) n (mapWork s) = some (mapWork t) := by
  intro n
  induction n with
  | zero =>
      intro s t h
      simp only [run, Option.some.injEq] at h ⊢
      subst t
      rfl
  | succ n ih =>
      intro s t h
      unfold run at h ⊢
      cases hs : step stackProgram s with
      | none => rw [hs] at h; contradiction
      | some s' =>
          rw [hs] at h
          rw [step_work_of_some exit s s' hs]
          exact ih s' t h

theorem terminal_bridge {K : Type} (exit : StackLabel → K)
    (l : StackLabel) (a b : Nat) (hl : stackProgram l = .halt) :
    run (routedProgram exit) 2 ⟨RoutedLabel.work l, a, b⟩ =
      some ⟨RoutedLabel.next (exit l), a, b⟩ := by
  simp [run, step, routedProgram, hl, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

def terminalOutcome : StackLabel → StackLabel
  | .push d .done => .push d .done
  | .pop (.done d) => .pop (.done d)
  | .pop .empty => .pop .empty
  | .peek (.done d) => .peek (.done d)
  | .peek .empty => .peek .empty
  | l => l

theorem push_terminal (d : Digit) : stackProgram (.push d .done) = .halt := rfl
theorem pop_terminal (d : Digit) : stackProgram (.pop (.done d)) = .halt := rfl
theorem pop_empty_terminal : stackProgram (.pop .empty) = .halt := rfl
theorem peek_terminal (d : Digit) : stackProgram (.peek (.done d)) = .halt := rfl
theorem peek_empty_terminal : stackProgram (.peek .empty) = .halt := rfl

theorem routed_push_exact (d : Digit) (n : Nat) :
    run (routedProgram terminalOutcome) (16 * n + d.val + 5)
        ⟨RoutedLabel.work (.push d .mulLoop), n, 0⟩ =
      some ⟨RoutedLabel.next (.push d .done),
        FoundationStoneTest16AI.pushCode d n, 0⟩ := by
  rw [show 16 * n + d.val + 5 = (16 * n + d.val + 3) + 2 by omega, run_add]
  have h := run_work_of_some terminalOutcome _ _ _ (suite_push_exact d n)
  simp only [mapWork] at h
  rw [h]
  exact terminal_bridge terminalOutcome (.push d .done) _ _ (push_terminal d)

theorem routed_pop_exact (d : Digit) (n : Nat) :
    run (routedProgram terminalOutcome) (8 * n + d.val + 5)
        ⟨RoutedLabel.work (.pop .start), FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨RoutedLabel.next (.pop (.done d)), n, 0⟩ := by
  rw [show 8 * n + d.val + 5 = (8 * n + d.val + 3) + 2 by omega, run_add]
  have h := run_work_of_some terminalOutcome _ _ _ (suite_pop_exact d n)
  simp only [mapWork] at h
  rw [h]
  exact terminal_bridge terminalOutcome (.pop (.done d)) _ _ (pop_terminal d)

theorem routed_peek_exact (d : Digit) (n : Nat) :
    run (routedProgram terminalOutcome) (24 * n + 2 * d.val + 8)
        ⟨RoutedLabel.work (.peek (.pop .start)),
          FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨RoutedLabel.next (.peek (.done d)),
        FoundationStoneTest16AI.pushCode d n, 0⟩ := by
  rw [show 24 * n + 2 * d.val + 8 = (24 * n + 2 * d.val + 6) + 2 by omega,
    run_add]
  have h := run_work_of_some terminalOutcome _ _ _ (suite_peek_exact d n)
  simp only [mapWork] at h
  rw [h]
  exact terminal_bridge terminalOutcome (.peek (.done d)) _ _ (peek_terminal d)

/-! Red control: a one-instruction jump implemented by increment alone changes
the data counter.  The restoring half of the bridge is semantically necessary. -/
theorem one_half_bridge_corrupts (K : Type) (k : K) (a b : Nat) :
    step (fun _ : Unit => Instr.inc false ()) ⟨(), a, b⟩ =
      some ⟨(), a + 1, b⟩ := by
  simp [step, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

theorem turing_chamber_16BH_certificate :
    (∀ d n, run (routedProgram terminalOutcome) (16 * n + d.val + 5)
      ⟨RoutedLabel.work (.push d .mulLoop), n, 0⟩ =
        some ⟨RoutedLabel.next (.push d .done),
          FoundationStoneTest16AI.pushCode d n, 0⟩) ∧
    (∀ d n, run (routedProgram terminalOutcome) (8 * n + d.val + 5)
      ⟨RoutedLabel.work (.pop .start), FoundationStoneTest16AI.pushCode d n, 0⟩ =
        some ⟨RoutedLabel.next (.pop (.done d)), n, 0⟩) ∧
    (∀ d n, run (routedProgram terminalOutcome) (24 * n + 2 * d.val + 8)
      ⟨RoutedLabel.work (.peek (.pop .start)), FoundationStoneTest16AI.pushCode d n, 0⟩ =
        some ⟨RoutedLabel.next (.peek (.done d)),
          FoundationStoneTest16AI.pushCode d n, 0⟩) :=
  ⟨routed_push_exact, routed_pop_exact, routed_peek_exact⟩

#print axioms run_work_of_some
#print axioms terminal_bridge
#print axioms routed_push_exact
#print axioms routed_pop_exact
#print axioms routed_peek_exact
#print axioms turing_chamber_16BH_certificate

end FoundationStoneTest16BH
