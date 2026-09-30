import FoundationStoneTest16BI

/-!
# THE TURING CHAMBER — TEST 16BP: DIGIT-ROUTED FIVE-COUNTER BLOCKS

Lean 4.35.0-rc2 / pinned Mathlib.

This file closes the operation-level seam between the stack macros used by
16AU and the primitive five-counter language of 16AY.

The source instruction set has push, pop, peek and halt.  Pop and peek carry
five distinct continuations: one empty-stack continuation and one continuation
for each of the four digits.  A separate bad continuation receives the
unreachable residue of an invalid stack code, and `BadTargetsLoop` requires
the assembler to point it at a certified self-loop rather than a halt.  Thus
the digit read by pop or peek is part of the exit route; it is not forgotten
and reconstructed later.

Every source label owns a genuine `16AY.BlockFamily`.  Slot zero is its entry.
The remaining finite slots encode 16BH's routed stack labels.  The selected
stack counter and the sole temporary counter execute the operation; the other
three counters are an arbitrary frame and are unchanged.  Entry, successful
exit and every certified operation boundary have temporary counter zero.

This is deliberately the operation compiler.  The next assembly pass places
these certified blocks recursively behind the seven constructors of a
supported TM2 statement tree.
-/

namespace FoundationStoneTest16BP

open FoundationStoneTest16AY
open FoundationStoneTest16BG
open FoundationStoneTest16BH

abbrev Digit := Fin 4
abbrev StackReg := FoundationStoneTest16BB.StackReg
abbrev Reg5 := FoundationStoneTest16BB.Reg5

/-! ## Executable finite indexing

`Fintype.equivFin` extracts an equivalence from a truncation and is therefore
noncomputable, even when the `Fintype` itself was derived.  Serialization needs
more than abstract finiteness, so owners supply an explicit finite index.
-/

class FiniteIndex (K : Type) [Fintype K] where
  equivFin : K ≃ Fin (Fintype.card K)

instance finFiniteIndex (n : Nat) : FiniteIndex (Fin n) where
  equivFin := by simpa using (Equiv.refl (Fin n))

instance finiteIndexDecidableEq (K : Type) [Fintype K] [FiniteIndex K] :
    DecidableEq K := FiniteIndex.equivFin.decidableEq

def unitEquivFinOne : Unit ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => ()
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; fin_cases x; rfl

def sumFinEquiv {A B : Type} {m n : Nat}
    (ea : A ≃ Fin m) (eb : B ≃ Fin n) : A ⊕ B ≃ Fin (m + n) :=
  (ea.sumCongr eb).trans finSumFinEquiv

def prodFinEquiv {A B : Type} {m n : Nat}
    (ea : A ≃ Fin m) (eb : B ≃ Fin n) : A × B ≃ Fin (m * n) :=
  (ea.prodCongr eb).trans finProdFinEquiv

abbrev PushShape := Unit ⊕ Fin 5 ⊕ Unit ⊕ Unit ⊕ Fin 4 ⊕ Unit ⊕ Unit

def pushShapeEquiv : FoundationStoneTest16BD.PushLabel ≃ PushShape where
  toFun
    | .mulLoop => .inl ()
    | .mulAdd i => .inr (.inl i)
    | .restoreLoop => .inr (.inr (.inl ()))
    | .restoreCredit => .inr (.inr (.inr (.inl ())))
    | .addDigit i => .inr (.inr (.inr (.inr (.inl i))))
    | .done => .inr (.inr (.inr (.inr (.inr (.inl ())))))
    | .bad => .inr (.inr (.inr (.inr (.inr (.inr ())))))
  invFun
    | .inl _ => .mulLoop
    | .inr (.inl i) => .mulAdd i
    | .inr (.inr (.inl _)) => .restoreLoop
    | .inr (.inr (.inr (.inl _))) => .restoreCredit
    | .inr (.inr (.inr (.inr (.inl i)))) => .addDigit i
    | .inr (.inr (.inr (.inr (.inr (.inl _))))) => .done
    | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .bad
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with x | x
    · cases x; rfl
    · rcases x with x | x
      · rfl
      · rcases x with x | x
        · cases x; rfl
        · rcases x with x | x
          · cases x; rfl
          · rcases x with x | x
            · rfl
            · rcases x with x | x <;> cases x <;> rfl

def pushLabelEquivFin : FoundationStoneTest16BD.PushLabel ≃ Fin 14 :=
  pushShapeEquiv.trans <|
    sumFinEquiv unitEquivFinOne <|
    sumFinEquiv (Equiv.refl _) <|
    sumFinEquiv unitEquivFinOne <|
    sumFinEquiv unitEquivFinOne <|
    sumFinEquiv (Equiv.refl _) <|
    sumFinEquiv unitEquivFinOne unitEquivFinOne

abbrev PopShape := Unit ⊕ Fin 5 ⊕ Unit ⊕ Fin 5 ⊕ Fin 5 ⊕ Unit ⊕ Fin 4 ⊕ Unit

def popShapeEquiv : FoundationStoneTest16BE.PopLabel ≃ PopShape where
  toFun
    | .start => .inl ()
    | .scan i => .inr (.inl i)
    | .credit => .inr (.inr (.inl ()))
    | .restore i => .inr (.inr (.inr (.inl i)))
    | .restoreCredit i => .inr (.inr (.inr (.inr (.inl i))))
    | .empty => .inr (.inr (.inr (.inr (.inr (.inl ())))))
    | .done i => .inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))
    | .bad => .inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))
  invFun
    | .inl _ => .start
    | .inr (.inl i) => .scan i
    | .inr (.inr (.inl _)) => .credit
    | .inr (.inr (.inr (.inl i))) => .restore i
    | .inr (.inr (.inr (.inr (.inl i)))) => .restoreCredit i
    | .inr (.inr (.inr (.inr (.inr (.inl _))))) => .empty
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))) => .done i
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))) => .bad
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with x | x
    · cases x; rfl
    · rcases x with x | x
      · rfl
      · rcases x with x | x
        · cases x; rfl
        · rcases x with x | x
          · rfl
          · rcases x with x | x
            · rfl
            · rcases x with x | x
              · cases x; rfl
              · rcases x with x | x
                · rfl
                · cases x; rfl

def popLabelEquivFin : FoundationStoneTest16BE.PopLabel ≃ Fin 23 :=
  popShapeEquiv.trans <|
    sumFinEquiv unitEquivFinOne <|
    sumFinEquiv (Equiv.refl _) <|
    sumFinEquiv unitEquivFinOne <|
    sumFinEquiv (Equiv.refl _) <|
    sumFinEquiv (Equiv.refl _) <|
    sumFinEquiv unitEquivFinOne <|
    sumFinEquiv (Equiv.refl _) unitEquivFinOne

abbrev PeekShape := FoundationStoneTest16BE.PopLabel ⊕
  (Fin 4 × FoundationStoneTest16BD.PushLabel) ⊕ Unit ⊕ Fin 4 ⊕ Unit

def peekShapeEquiv : FoundationStoneTest16BF.PeekLabel ≃ PeekShape where
  toFun
    | .pop l => .inl l
    | .push d l => .inr (.inl (d, l))
    | .empty => .inr (.inr (.inl ()))
    | .done d => .inr (.inr (.inr (.inl d)))
    | .bad => .inr (.inr (.inr (.inr ())))
  invFun
    | .inl l => .pop l
    | .inr (.inl x) => .push x.1 x.2
    | .inr (.inr (.inl _)) => .empty
    | .inr (.inr (.inr (.inl d))) => .done d
    | .inr (.inr (.inr (.inr _))) => .bad
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with x | x
    · rfl
    · rcases x with x | x
      · rcases x with ⟨d, l⟩; rfl
      · rcases x with x | x
        · cases x; rfl
        · rcases x with x | x
          · rfl
          · cases x; rfl

def peekLabelEquivFin : FoundationStoneTest16BF.PeekLabel ≃ Fin 85 :=
  peekShapeEquiv.trans <|
    sumFinEquiv popLabelEquivFin <|
    sumFinEquiv (prodFinEquiv (Equiv.refl _) pushLabelEquivFin) <|
    sumFinEquiv unitEquivFinOne <|
    sumFinEquiv (Equiv.refl _) unitEquivFinOne

abbrev StackShape := (Fin 4 × FoundationStoneTest16BD.PushLabel) ⊕
  FoundationStoneTest16BE.PopLabel ⊕ FoundationStoneTest16BF.PeekLabel

def stackShapeEquiv : StackLabel ≃ StackShape where
  toFun
    | .push d l => .inl (d, l)
    | .pop l => .inr (.inl l)
    | .peek l => .inr (.inr l)
  invFun
    | .inl x => .push x.1 x.2
    | .inr (.inl l) => .pop l
    | .inr (.inr l) => .peek l
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with x | x
    · rcases x with ⟨d, l⟩; rfl
    · rcases x with x | x <;> rfl

def stackLabelEquivFin : StackLabel ≃ Fin 164 :=
  stackShapeEquiv.trans <|
    sumFinEquiv (prodFinEquiv (Equiv.refl _) pushLabelEquivFin) <|
    sumFinEquiv popLabelEquivFin peekLabelEquivFin

/-! ## Finite routed positions -/

def routedEquiv (K : Type) :
    RoutedLabel K ≃ (StackLabel ⊕ StackLabel ⊕ K) where
  toFun
    | .work l => .inl l
    | .restore l => .inr (.inl l)
    | .next k => .inr (.inr k)
  invFun
    | .inl l => .work l
    | .inr (.inl l) => .restore l
    | .inr (.inr k) => .next k
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with x | x
    · rfl
    · rcases x with x | x <;> rfl

instance routedFintype (K : Type) [Fintype K] :
    Fintype (RoutedLabel K) :=
  Fintype.ofEquiv _ (routedEquiv K).symm

def routedFinEquiv (K : Type) [Fintype K] [FiniteIndex K] :
    RoutedLabel K ≃ Fin (164 + (164 + Fintype.card K)) :=
  (routedEquiv K).trans <|
    sumFinEquiv stackLabelEquivFin <|
      sumFinEquiv stackLabelEquivFin FiniteIndex.equivFin

def routedIndex (K : Type) [Fintype K] [FiniteIndex K]
    (r : RoutedLabel K) : Fin ((164 + (164 + Fintype.card K)) + 1) :=
  (routedFinEquiv K r).succ

def routedDecode (K : Type) [Fintype K] [FiniteIndex K]
    (i : Fin (164 + (164 + Fintype.card K))) : RoutedLabel K :=
  (routedFinEquiv K).symm i

@[simp] theorem routedDecode_encode (K : Type) [Fintype K] [FiniteIndex K]
    (r : RoutedLabel K) :
    routedDecode K (routedFinEquiv K r) = r := by
  simp [routedDecode]

/-! ## A macro instruction with honest result-dependent exits -/

inductive MacroInstr (K : Type)
  | push (register : StackReg) (digit : Digit) (next bad : K)
  | pop (register : StackReg) (empty : K) (digit : Digit → K) (bad : K)
  | peek (register : StackReg) (empty : K) (digit : Digit → K) (bad : K)
  | loop (anchor : K)
  | halt (sink : K)

def operationRegister {K : Type} : MacroInstr K → StackReg
  | .push i _ _ _ => i
  | .pop i _ _ _ => i
  | .peek i _ _ _ => i
  | .loop _ => 0
  | .halt _ => 0

def operationEntry {K : Type} : MacroInstr K → RoutedLabel K
  | .push _ d _ _ => .work (.push d .mulLoop)
  | .pop _ _ _ _ => .work (.pop .start)
  | .peek _ _ _ _ => .work (.peek (.pop .start))
  | .loop _ => .work (.pop .empty)
  | .halt _ => .work (.pop .empty)

/-- Pop and peek route to a distinct continuation for every observed digit,
plus separate empty and bad exits. -/
def operationExit {K : Type} : MacroInstr K → StackLabel → K
  | .push _ expected next bad, .push actual .done =>
      if actual = expected then next else bad
  | .push _ _ _ bad, _ => bad
  | .pop _ empty _ _, .pop .empty => empty
  | .pop _ _ digit _, .pop (.done d) => digit d
  | .pop _ _ _ bad, _ => bad
  | .peek _ empty _ _, .peek .empty => empty
  | .peek _ _ digit _, .peek (.done d) => digit d
  | .peek _ _ _ bad, _ => bad
  | .loop anchor, _ => anchor
  | .halt sink, _ => sink

def badTarget {K : Type} : MacroInstr K → Option K
  | .push _ _ _ bad => some bad
  | .pop _ _ _ bad => some bad
  | .peek _ _ _ bad => some bad
  | .loop _ => none
  | .halt _ => none

/-- The assembler must discharge this syntactic safety condition: every bad
route names a dedicated looping owner, never an explicit halt owner. -/
def BadTargetsLoop {K : Type} (P : K → MacroInstr K) : Prop :=
  ∀ owner bad, badTarget (P owner) = some bad → P bad = .loop bad

@[simp] theorem push_exit_correct {K : Type} (i : StackReg) (d : Digit)
    (next bad : K) :
    operationExit (.push i d next bad) (.push d .done) = next := by
  simp [operationExit]

@[simp] theorem pop_empty_exit_correct {K : Type} (i : StackReg)
    (empty bad : K) (next : Digit → K) :
    operationExit (.pop i empty next bad) (.pop .empty) = empty := rfl

@[simp] theorem pop_digit_exit_correct {K : Type} (i : StackReg)
    (empty bad : K) (next : Digit → K) (d : Digit) :
    operationExit (.pop i empty next bad) (.pop (.done d)) = next d := rfl

@[simp] theorem peek_empty_exit_correct {K : Type} (i : StackReg)
    (empty bad : K) (next : Digit → K) :
    operationExit (.peek i empty next bad) (.peek .empty) = empty := rfl

@[simp] theorem peek_digit_exit_correct {K : Type} (i : StackReg)
    (empty bad : K) (next : Digit → K) (d : Digit) :
    operationExit (.peek i empty next bad) (.peek (.done d)) = next d := rfl

/-! ## One typed 16AY block family -/

def localTarget (K : Type) [Fintype K] [FiniteIndex K] (r : RoutedLabel K) :
    Target K (Fin ((164 + (164 + Fintype.card K)) + 1)) :=
  .local (routedIndex K r)

def entryCode {K : Type} [Fintype K] [FiniteIndex K]
    (instruction : MacroInstr K) :
    Instr 5 (Target K (Fin ((164 + (164 + Fintype.card K)) + 1))) :=
  match instruction with
  | .halt _ => .halt
  | instruction =>
      .dec FoundationStoneTest16BB.tempReg
        (localTarget K (operationEntry instruction))
        (localTarget K (operationEntry instruction))

def routedCode {K : Type} [Fintype K] [FiniteIndex K]
    (instruction : MacroInstr K) (r : RoutedLabel K) :
    Instr 5 (Target K (Fin ((164 + (164 + Fintype.card K)) + 1))) :=
  match instruction with
  | .halt _ => .halt
  | instruction =>
      match r with
      | .next k =>
          .dec FoundationStoneTest16BB.tempReg (.exit k) (.exit k)
      | r =>
          Instr.map (localTarget K)
            (FoundationStoneTest16BB.liftAWInstr
              (operationRegister instruction)
              (routedProgram (operationExit instruction) r))

def operationBlocks {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) : BlockFamily 5 K where
  width := fun _ => (164 + (164 + Fintype.card K)) + 1
  nonempty := by intro; omega
  code := fun owner position =>
    Fin.cases (entryCode (P owner))
      (fun i => routedCode (P owner) (routedDecode K i)) position

abbrev Linked {K : Type} [Fintype K] [FiniteIndex K] (P : K → MacroInstr K) :=
  LinkedLabel (operationBlocks P)

theorem operation_control_is_finite {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) : Finite (Linked P) :=
  inferInstance

theorem operation_control_card {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) :
    Fintype.card (Linked P) =
      Fintype.card K * ((164 + (164 + Fintype.card K)) + 1) := by
  change Fintype.card (Σ _ : K,
    Fin ((164 + (164 + Fintype.card K)) + 1)) = _
  rw [Fintype.card_sigma]
  simp

def localLabel {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (r : RoutedLabel K) : Linked P :=
  ⟨owner, routedIndex K r⟩

def entryState {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (counters : Reg5 → Nat) :
    State 5 (Linked P) :=
  State.map (entry (operationBlocks P)) ⟨owner, counters⟩

def localState {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (r : RoutedLabel K)
    (counters : Reg5 → Nat) : State 5 (Linked P) :=
  ⟨localLabel P owner r, counters⟩

theorem entry_push_step {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg) (d : Digit)
    (next bad : K) (hP : P owner = .push i d next bad)
    (counters : Reg5 → Nat)
    (hzero : counters FoundationStoneTest16BB.tempReg = 0) :
    step (linkedProgram (operationBlocks P)) (entryState P owner counters) =
      some (localState P owner (.work (.push d .mulLoop)) counters) := by
  simp [entryState, State.map, entry, linkedProgram, operationBlocks,
    entryCode, hP, step, linkInstr, Instr.map, resolve, localState,
    localLabel, localTarget, operationEntry, routedIndex, hzero] <;> rfl

theorem entry_pop_step {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty bad : K) (next : Digit → K)
    (hP : P owner = .pop i empty next bad) (counters : Reg5 → Nat)
    (hzero : counters FoundationStoneTest16BB.tempReg = 0) :
    step (linkedProgram (operationBlocks P)) (entryState P owner counters) =
      some (localState P owner (.work (.pop .start)) counters) := by
  simp [entryState, State.map, entry, linkedProgram, operationBlocks,
    entryCode, hP, step, linkInstr, Instr.map, resolve, localState,
    localLabel, localTarget, operationEntry, routedIndex, hzero] <;> rfl

theorem entry_peek_step {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty bad : K) (next : Digit → K)
    (hP : P owner = .peek i empty next bad) (counters : Reg5 → Nat)
    (hzero : counters FoundationStoneTest16BB.tempReg = 0) :
    step (linkedProgram (operationBlocks P)) (entryState P owner counters) =
      some (localState P owner (.work (.peek (.pop .start))) counters) := by
  simp [entryState, State.map, entry, linkedProgram, operationBlocks,
    entryCode, hP, step, linkInstr, Instr.map, resolve, localState,
    localLabel, localTarget, operationEntry, routedIndex, hzero] <;> rfl

theorem entry_halt_step {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner sink : K)
    (hP : P owner = .halt sink) (counters : Reg5 → Nat) :
    step (linkedProgram (operationBlocks P)) (entryState P owner counters) = none := by
  simp [entryState, State.map, entry, linkedProgram, operationBlocks,
    entryCode, hP, step, linkInstr, Instr.map, resolve]

/-! ## The frame and scratch invariants -/

theorem frame_once (i : StackReg) (base : Reg5 → Nat)
    (pc : Type) (label : pc) (a b : Nat) (j : Reg5)
    (hji : j ≠ FoundationStoneTest16BB.stackReg i)
    (hjt : j ≠ FoundationStoneTest16BB.tempReg) :
    (FoundationStoneTest16BB.embed i base label a b).counters j = base j :=
  FoundationStoneTest16BB.install_other i base a b j hji hjt

@[simp] theorem embedded_temp_zero (i : StackReg) (base : Reg5 → Nat)
    {L : Type} (label : L) (a : Nat) :
    (FoundationStoneTest16BB.embed i base label a 0).counters
      FoundationStoneTest16BB.tempReg = 0 := by
  simp [FoundationStoneTest16BB.embed, FoundationStoneTest16BB.install_temp]

/-! ## Local execution agrees with the already-certified routed program -/

def embedLocal {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (base : Reg5 → Nat) (s : FoundationStoneTest16AW.State (RoutedLabel K)) :
    State 5 (Linked P) :=
  localState P owner s.pc
    (FoundationStoneTest16BB.install i base s.a s.b)

theorem run_add {k : Nat} {L : Type} (P : L → Instr k L) (m n : Nat)
    (s : State k L) :
    run P (m + n) s =
      match run P m s with
      | none => none
      | some s' => run P n s' := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih =>
      simp only [Nat.succ_add, run]
      cases step P s with
      | none => rfl
      | some s' => exact ih s'

theorem run_succ_gives_reaches {k : Nat} {L : Type} (P : L → Instr k L) :
    ∀ n (s t : State k L), run P (n + 1) s = some t →
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

theorem positive_run_gives_reaches {k : Nat} {L : Type}
    (P : L → Instr k L) (n : Nat) (hn : 0 < n)
    (s t : State k L) (h : run P n s = some t) :
    Relation.TransGen (fun u v => step P u = some v) s t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact run_succ_gives_reaches P m s t h

@[simp] theorem resolve_localTarget {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (r : RoutedLabel K) :
    resolve (operationBlocks P) owner (localTarget K r) =
      localLabel P owner r := by
  rfl

theorem link_map_local {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K)
    (instruction : Instr 5 (RoutedLabel K)) :
    Instr.map (resolve (operationBlocks P) owner)
        (Instr.map (localTarget K) instruction) =
      Instr.map (localLabel P owner) instruction := by
  cases instruction <;> simp [Instr.map]

theorem step_map_at {k : Nat} {L M : Type}
    (P : L → Instr k L) (Q : M → Instr k M) (f : L → M)
    (s : State k L)
    (hcode : Q (f s.pc) = Instr.map f (P s.pc)) :
    step Q (State.map f s) = Option.map (State.map f) (step P s) := by
  rcases s with ⟨pc, counters⟩
  simp only [State.map] at hcode ⊢
  unfold step
  rw [hcode]
  cases hP : P pc with
  | halt => rfl
  | inc counter next => rfl
  | dec counter positive zero =>
      by_cases hz : counters counter = 0 <;>
        simp [Instr.map, hP, hz, State.map, setCounter]

theorem linked_code_push_work {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg) (d : Digit)
    (next bad : K) (hP : P owner = .push i d next bad) (l : StackLabel) :
    linkedProgram (operationBlocks P)
        (localLabel P owner (.work l)) =
      Instr.map (localLabel P owner)
        (FoundationStoneTest16BB.liftAWInstr i
          (routedProgram (operationExit (.push i d next bad)) (.work l))) := by
  simp only [linkedProgram, operationBlocks, localLabel, routedIndex,
    Fin.cases_succ, routedDecode_encode, routedCode, hP, linkInstr]
  exact link_map_local P owner _

theorem linked_code_push_restore {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg) (d : Digit)
    (next bad : K) (hP : P owner = .push i d next bad) (l : StackLabel) :
    linkedProgram (operationBlocks P)
        (localLabel P owner (.restore l)) =
      Instr.map (localLabel P owner)
        (FoundationStoneTest16BB.liftAWInstr i
          (routedProgram (operationExit (.push i d next bad)) (.restore l))) := by
  simp only [linkedProgram, operationBlocks, localLabel, routedIndex,
    Fin.cases_succ, routedDecode_encode, routedCode, hP, linkInstr]
  exact link_map_local P owner _

theorem linked_code_active_work {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (instruction : MacroInstr K)
    (hP : P owner = instruction)
    (hactive : ∀ sink, instruction ≠ .halt sink) (l : StackLabel) :
    linkedProgram (operationBlocks P)
        (localLabel P owner (.work l)) =
      Instr.map (localLabel P owner)
        (FoundationStoneTest16BB.liftAWInstr (operationRegister instruction)
          (routedProgram (operationExit instruction) (.work l))) := by
  cases instruction with
  | push i d next bad =>
      simpa [operationRegister] using
        linked_code_push_work P owner i d next bad hP l
  | pop i empty digit bad =>
      simp only [linkedProgram, operationBlocks, localLabel, routedIndex,
        Fin.cases_succ, routedDecode_encode, routedCode, hP, linkInstr]
      exact link_map_local P owner _
  | peek i empty digit bad =>
      simp only [linkedProgram, operationBlocks, localLabel, routedIndex,
        Fin.cases_succ, routedDecode_encode, routedCode, hP, linkInstr]
      exact link_map_local P owner _
  | loop anchor =>
      simp only [linkedProgram, operationBlocks, localLabel, routedIndex,
        Fin.cases_succ, routedDecode_encode, routedCode, hP, linkInstr]
      exact link_map_local P owner _
  | halt sink => exact (hactive sink rfl).elim

theorem linked_code_active_restore {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (instruction : MacroInstr K)
    (hP : P owner = instruction)
    (hactive : ∀ sink, instruction ≠ .halt sink) (l : StackLabel) :
    linkedProgram (operationBlocks P)
        (localLabel P owner (.restore l)) =
      Instr.map (localLabel P owner)
        (FoundationStoneTest16BB.liftAWInstr (operationRegister instruction)
          (routedProgram (operationExit instruction) (.restore l))) := by
  cases instruction with
  | push i d next bad =>
      simpa [operationRegister] using
        linked_code_push_restore P owner i d next bad hP l
  | pop i empty digit bad =>
      simp only [linkedProgram, operationBlocks, localLabel, routedIndex,
        Fin.cases_succ, routedDecode_encode, routedCode, hP, linkInstr]
      exact link_map_local P owner _
  | peek i empty digit bad =>
      simp only [linkedProgram, operationBlocks, localLabel, routedIndex,
        Fin.cases_succ, routedDecode_encode, routedCode, hP, linkInstr]
      exact link_map_local P owner _
  | loop anchor =>
      simp only [linkedProgram, operationBlocks, localLabel, routedIndex,
        Fin.cases_succ, routedDecode_encode, routedCode, hP, linkInstr]
      exact link_map_local P owner _
  | halt sink => exact (hactive sink rfl).elim

theorem local_step_active_of_some {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (instruction : MacroInstr K)
    (hP : P owner = instruction)
    (hactive : ∀ sink, instruction ≠ .halt sink)
    (base : Reg5 → Nat)
    (s t : FoundationStoneTest16AW.State (RoutedLabel K))
    (h : FoundationStoneTest16AW.step
      (routedProgram (operationExit instruction)) s = some t) :
    step (linkedProgram (operationBlocks P))
        (embedLocal P owner (operationRegister instruction) base s) =
      some (embedLocal P owner (operationRegister instruction) base t) := by
  have h5 := FoundationStoneTest16BB.step_lift_AW
    (operationRegister instruction) base
    (routedProgram (operationExit instruction)) s
  rw [h] at h5
  rcases s with ⟨pc, a, b⟩
  cases pc with
  | next k =>
      simp [FoundationStoneTest16AW.step, routedProgram] at h
  | work l =>
      calc
        step (linkedProgram (operationBlocks P))
            (embedLocal P owner (operationRegister instruction) base
              ⟨.work l, a, b⟩) =
          Option.map (State.map (localLabel P owner))
            (step (FoundationStoneTest16BB.liftAWProgram
              (operationRegister instruction)
              (routedProgram (operationExit instruction)))
              (FoundationStoneTest16BB.embedAW
                (operationRegister instruction) base ⟨.work l, a, b⟩)) := by
                  change step (linkedProgram (operationBlocks P))
                    (State.map (localLabel P owner)
                      (FoundationStoneTest16BB.embedAW
                        (operationRegister instruction) base
                        ⟨.work l, a, b⟩)) = _
                  apply step_map_at
                  exact linked_code_active_work P owner instruction hP hactive l
        _ = some (embedLocal P owner (operationRegister instruction) base t) := by
          rw [h5]
          simp [embedLocal, localState, FoundationStoneTest16BB.embedAW,
            FoundationStoneTest16BB.embed, State.map]
  | restore l =>
      calc
        step (linkedProgram (operationBlocks P))
            (embedLocal P owner (operationRegister instruction) base
              ⟨.restore l, a, b⟩) =
          Option.map (State.map (localLabel P owner))
            (step (FoundationStoneTest16BB.liftAWProgram
              (operationRegister instruction)
              (routedProgram (operationExit instruction)))
              (FoundationStoneTest16BB.embedAW
                (operationRegister instruction) base ⟨.restore l, a, b⟩)) := by
                  change step (linkedProgram (operationBlocks P))
                    (State.map (localLabel P owner)
                      (FoundationStoneTest16BB.embedAW
                        (operationRegister instruction) base
                        ⟨.restore l, a, b⟩)) = _
                  apply step_map_at
                  exact linked_code_active_restore P owner instruction hP hactive l
        _ = some (embedLocal P owner (operationRegister instruction) base t) := by
          rw [h5]
          simp [embedLocal, localState, FoundationStoneTest16BB.embedAW,
            FoundationStoneTest16BB.embed, State.map]

theorem local_run_active_of_some {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (instruction : MacroInstr K)
    (hP : P owner = instruction)
    (hactive : ∀ sink, instruction ≠ .halt sink)
    (base : Reg5 → Nat) : ∀ n
    (s t : FoundationStoneTest16AW.State (RoutedLabel K)),
    FoundationStoneTest16AW.run
      (routedProgram (operationExit instruction)) n s = some t →
    run (linkedProgram (operationBlocks P)) n
        (embedLocal P owner (operationRegister instruction) base s) =
      some (embedLocal P owner (operationRegister instruction) base t) := by
  intro n
  induction n with
  | zero =>
      intro s t h
      simp only [FoundationStoneTest16AW.run, Option.some.injEq] at h
      subst t
      rfl
  | succ n ih =>
      intro s t h
      unfold FoundationStoneTest16AW.run at h
      cases hs : FoundationStoneTest16AW.step
          (routedProgram (operationExit instruction)) s with
      | none => rw [hs] at h; contradiction
      | some s' =>
          rw [hs] at h
          unfold run
          rw [local_step_active_of_some P owner instruction hP hactive
            base s s' hs]
          exact ih s' t h

theorem entry_active_step {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (instruction : MacroInstr K)
    (hP : P owner = instruction)
    (hactive : ∀ sink, instruction ≠ .halt sink)
    (counters : Reg5 → Nat)
    (hzero : counters FoundationStoneTest16BB.tempReg = 0) :
    step (linkedProgram (operationBlocks P)) (entryState P owner counters) =
      some (localState P owner (operationEntry instruction) counters) := by
  cases instruction with
  | push i d next bad =>
      simpa [operationEntry] using
        entry_push_step P owner i d next bad hP counters hzero
  | pop i empty digit bad =>
      simpa [operationEntry] using
        entry_pop_step P owner i empty bad digit hP counters hzero
  | peek i empty digit bad =>
      simpa [operationEntry] using
        entry_peek_step P owner i empty bad digit hP counters hzero
  | loop anchor =>
      simp [entryState, State.map, entry, linkedProgram, operationBlocks,
        entryCode, hP, step, linkInstr, Instr.map, resolve, localState,
        localLabel, localTarget, operationEntry, routedIndex, hzero] <;> rfl
  | halt sink => exact (hactive sink rfl).elim

theorem next_step_to_entry {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (instruction : MacroInstr K)
    (hP : P owner = instruction)
    (hactive : ∀ sink, instruction ≠ .halt sink)
    (base : Reg5 → Nat) (target : K) (a : Nat) :
    step (linkedProgram (operationBlocks P))
        (embedLocal P owner (operationRegister instruction) base
          ⟨.next target, a, 0⟩) =
      some (entryState P target
        (FoundationStoneTest16BB.install
          (operationRegister instruction) base a 0)) := by
  cases instruction with
  | push i d next bad =>
      simp [embedLocal, localState, linkedProgram, operationBlocks,
        localLabel, routedIndex, routedDecode_encode, routedCode, hP,
        linkInstr, Instr.map, resolve, step, entryState, State.map, entry,
        operationRegister, FoundationStoneTest16BB.install_temp] <;> rfl
  | pop i empty digit bad =>
      simp [embedLocal, localState, linkedProgram, operationBlocks,
        localLabel, routedIndex, routedDecode_encode, routedCode, hP,
        linkInstr, Instr.map, resolve, step, entryState, State.map, entry,
        operationRegister, FoundationStoneTest16BB.install_temp] <;> rfl
  | peek i empty digit bad =>
      simp [embedLocal, localState, linkedProgram, operationBlocks,
        localLabel, routedIndex, routedDecode_encode, routedCode, hP,
        linkInstr, Instr.map, resolve, step, entryState, State.map, entry,
        operationRegister, FoundationStoneTest16BB.install_temp] <;> rfl
  | loop anchor =>
      simp [embedLocal, localState, linkedProgram, operationBlocks,
        localLabel, routedIndex, routedDecode_encode, routedCode, hP,
        linkInstr, Instr.map, resolve, step, entryState, State.map, entry,
        operationRegister, FoundationStoneTest16BB.install_temp] <;> rfl
  | halt sink => exact (hactive sink rfl).elim

theorem operation_reaches_of_run {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (instruction : MacroInstr K)
    (hP : P owner = instruction)
    (hactive : ∀ sink, instruction ≠ .halt sink)
    (base : Reg5 → Nat) (n : Nat) (hn : 0 < n)
    (a b : Nat) (target : K)
    (hrun : FoundationStoneTest16AW.run
      (routedProgram (operationExit instruction)) n
        ⟨operationEntry instruction, a, 0⟩ =
      some ⟨.next target, b, 0⟩) :
    Relation.TransGen
      (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
      (entryState P owner
        (FoundationStoneTest16BB.install
          (operationRegister instruction) base a 0))
      (entryState P target
        (FoundationStoneTest16BB.install
          (operationRegister instruction) base b 0)) := by
  let countersA := FoundationStoneTest16BB.install
    (operationRegister instruction) base a 0
  have hzero : countersA FoundationStoneTest16BB.tempReg = 0 := by
    simp [countersA, FoundationStoneTest16BB.install_temp]
  have hentry : step (linkedProgram (operationBlocks P))
      (entryState P owner countersA) =
      some (embedLocal P owner (operationRegister instruction) base
        ⟨operationEntry instruction, a, 0⟩) := by
    simpa [countersA, embedLocal, localState] using
      entry_active_step P owner instruction hP hactive countersA hzero
  have hlocalRun := local_run_active_of_some P owner instruction hP hactive
    base n ⟨operationEntry instruction, a, 0⟩
      ⟨.next target, b, 0⟩ hrun
  have hlocal := positive_run_gives_reaches
    (linkedProgram (operationBlocks P)) n hn
    (embedLocal P owner (operationRegister instruction) base
      ⟨operationEntry instruction, a, 0⟩)
    (embedLocal P owner (operationRegister instruction) base
      ⟨.next target, b, 0⟩) hlocalRun
  have hexit := next_step_to_entry P owner instruction hP hactive base target b
  have hentryPath : Relation.TransGen
      (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
      (entryState P owner countersA)
      (embedLocal P owner (operationRegister instruction) base
        ⟨operationEntry instruction, a, 0⟩) :=
    Relation.TransGen.single hentry
  exact (hentryPath.trans hlocal).tail hexit

theorem local_step_push_of_some {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg) (d : Digit)
    (next bad : K) (hP : P owner = .push i d next bad)
    (base : Reg5 → Nat)
    (s t : FoundationStoneTest16AW.State (RoutedLabel K))
    (h : FoundationStoneTest16AW.step
      (routedProgram (operationExit (.push i d next bad))) s = some t) :
    step (linkedProgram (operationBlocks P))
        (embedLocal P owner i base s) =
      some (embedLocal P owner i base t) := by
  have h5 := FoundationStoneTest16BB.step_lift_AW i base
    (routedProgram (operationExit (.push i d next bad))) s
  rw [h] at h5
  rcases s with ⟨pc, a, b⟩
  cases pc with
  | next k =>
      simp [FoundationStoneTest16AW.step, routedProgram] at h
  | work l =>
      calc
        step (linkedProgram (operationBlocks P))
            (embedLocal P owner i base ⟨.work l, a, b⟩) =
          Option.map (State.map (localLabel P owner))
            (step (FoundationStoneTest16BB.liftAWProgram i
              (routedProgram (operationExit (.push i d next bad))))
              (FoundationStoneTest16BB.embedAW i base ⟨.work l, a, b⟩)) := by
                change step (linkedProgram (operationBlocks P))
                    (State.map (localLabel P owner)
                      (FoundationStoneTest16BB.embedAW i base ⟨.work l, a, b⟩)) = _
                apply step_map_at
                exact linked_code_push_work P owner i d next bad hP l
        _ = some (embedLocal P owner i base t) := by
          rw [h5]
          simp [embedLocal, localState, FoundationStoneTest16BB.embedAW,
            FoundationStoneTest16BB.embed, State.map]
  | restore l =>
      calc
        step (linkedProgram (operationBlocks P))
            (embedLocal P owner i base ⟨.restore l, a, b⟩) =
          Option.map (State.map (localLabel P owner))
            (step (FoundationStoneTest16BB.liftAWProgram i
              (routedProgram (operationExit (.push i d next bad))))
              (FoundationStoneTest16BB.embedAW i base ⟨.restore l, a, b⟩)) := by
                change step (linkedProgram (operationBlocks P))
                    (State.map (localLabel P owner)
                      (FoundationStoneTest16BB.embedAW i base ⟨.restore l, a, b⟩)) = _
                apply step_map_at
                exact linked_code_push_restore P owner i d next bad hP l
        _ = some (embedLocal P owner i base t) := by
          rw [h5]
          simp [embedLocal, localState, FoundationStoneTest16BB.embedAW,
            FoundationStoneTest16BB.embed, State.map]

/-! The following routed contracts generalise 16BH from its diagnostic
`terminalOutcome` to the result-dependent exit map of an arbitrary owner. -/

theorem routed_push_exact_to {K : Type} (exit : StackLabel → K)
    (d : Digit) (n : Nat) :
    FoundationStoneTest16AW.run (routedProgram exit) (16 * n + d.val + 5)
        ⟨RoutedLabel.work (.push d .mulLoop), n, 0⟩ =
      some ⟨RoutedLabel.next (exit (.push d .done)),
        FoundationStoneTest16AI.pushCode d n, 0⟩ := by
  rw [show 16 * n + d.val + 5 = (16 * n + d.val + 3) + 2 by omega,
    FoundationStoneTest16AW.run_add]
  have h := run_work_of_some exit _ _ _ (suite_push_exact d n)
  simp only [mapWork] at h
  rw [h]
  exact terminal_bridge exit (.push d .done) _ _ (push_terminal d)

theorem routed_pop_exact_to {K : Type} (exit : StackLabel → K)
    (d : Digit) (n : Nat) :
    FoundationStoneTest16AW.run (routedProgram exit) (8 * n + d.val + 5)
        ⟨RoutedLabel.work (.pop .start), FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨RoutedLabel.next (exit (.pop (.done d))), n, 0⟩ := by
  rw [show 8 * n + d.val + 5 = (8 * n + d.val + 3) + 2 by omega,
    FoundationStoneTest16AW.run_add]
  have h := run_work_of_some exit _ _ _ (suite_pop_exact d n)
  simp only [mapWork] at h
  rw [h]
  exact terminal_bridge exit (.pop (.done d)) _ _ (pop_terminal d)

theorem routed_pop_empty_to {K : Type} (exit : StackLabel → K) :
    FoundationStoneTest16AW.run (routedProgram exit) 3
        ⟨RoutedLabel.work (.pop .start), 0, 0⟩ =
      some ⟨RoutedLabel.next (exit (.pop .empty)), 0, 0⟩ := by
  rw [show 3 = 1 + 2 by omega, FoundationStoneTest16AW.run_add]
  have h := run_work_of_some exit _ _ _ suite_pop_empty
  simp only [mapWork] at h
  rw [h]
  exact terminal_bridge exit (.pop .empty) _ _ pop_empty_terminal

theorem routed_peek_exact_to {K : Type} (exit : StackLabel → K)
    (d : Digit) (n : Nat) :
    FoundationStoneTest16AW.run (routedProgram exit) (24 * n + 2 * d.val + 8)
        ⟨RoutedLabel.work (.peek (.pop .start)),
          FoundationStoneTest16AI.pushCode d n, 0⟩ =
      some ⟨RoutedLabel.next (exit (.peek (.done d))),
        FoundationStoneTest16AI.pushCode d n, 0⟩ := by
  rw [show 24 * n + 2 * d.val + 8 = (24 * n + 2 * d.val + 6) + 2 by omega,
    FoundationStoneTest16AW.run_add]
  have h := run_work_of_some exit _ _ _ (suite_peek_exact d n)
  simp only [mapWork] at h
  rw [h]
  exact terminal_bridge exit (.peek (.done d)) _ _ (peek_terminal d)

theorem routed_peek_empty_to {K : Type} (exit : StackLabel → K) :
    FoundationStoneTest16AW.run (routedProgram exit) 3
        ⟨RoutedLabel.work (.peek (.pop .start)), 0, 0⟩ =
      some ⟨RoutedLabel.next (exit (.peek .empty)), 0, 0⟩ := by
  rw [show 3 = 1 + 2 by omega, FoundationStoneTest16AW.run_add]
  have h := run_work_of_some exit _ _ _ suite_peek_empty
  simp only [mapWork] at h
  rw [h]
  exact terminal_bridge exit (.peek .empty) _ _ peek_empty_terminal

/-! ## The certified operation-level paths

The five operation theorems below are the interface consumed by the recursive
statement assembler.  Their endpoints are source-block entries, not local
halts.  A sixth theorem certifies the dedicated bad-route loop.
-/

theorem primitive_push_reaches {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg) (d : Digit)
    (next bad : K) (hP : P owner = .push i d next bad)
    (base : Reg5 → Nat) (n : Nat) :
    Relation.TransGen
      (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
      (entryState P owner (FoundationStoneTest16BB.install i base n 0))
      (entryState P next (FoundationStoneTest16BB.install i base
        (FoundationStoneTest16AI.pushCode d n) 0)) := by
  refine operation_reaches_of_run P owner (.push i d next bad) hP ?_
    base (16 * n + d.val + 5) (by omega) n
    (FoundationStoneTest16AI.pushCode d n) next ?_
  · intro sink
    simp
  · simpa [operationEntry, operationExit] using
      routed_push_exact_to (operationExit (.push i d next bad)) d n

theorem primitive_pop_digit_reaches {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty bad : K) (digit : Digit → K)
    (hP : P owner = .pop i empty digit bad)
    (base : Reg5 → Nat) (d : Digit) (n : Nat) :
    Relation.TransGen
      (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
      (entryState P owner (FoundationStoneTest16BB.install i base
        (FoundationStoneTest16AI.pushCode d n) 0))
      (entryState P (digit d)
        (FoundationStoneTest16BB.install i base n 0)) := by
  refine operation_reaches_of_run P owner (.pop i empty digit bad) hP ?_
    base (8 * n + d.val + 5) (by omega)
    (FoundationStoneTest16AI.pushCode d n) n (digit d) ?_
  · intro sink
    simp
  · simpa [operationEntry, operationExit] using
      routed_pop_exact_to (operationExit (.pop i empty digit bad)) d n

theorem primitive_pop_empty_reaches {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty bad : K) (digit : Digit → K)
    (hP : P owner = .pop i empty digit bad) (base : Reg5 → Nat) :
    Relation.TransGen
      (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
      (entryState P owner (FoundationStoneTest16BB.install i base 0 0))
      (entryState P empty (FoundationStoneTest16BB.install i base 0 0)) := by
  refine operation_reaches_of_run P owner (.pop i empty digit bad) hP ?_
    base 3 (by omega) 0 0 empty ?_
  · intro sink
    simp
  · simpa [operationEntry, operationExit] using
      routed_pop_empty_to (operationExit (.pop i empty digit bad))

theorem primitive_peek_digit_reaches {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty bad : K) (digit : Digit → K)
    (hP : P owner = .peek i empty digit bad)
    (base : Reg5 → Nat) (d : Digit) (n : Nat) :
    Relation.TransGen
      (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
      (entryState P owner (FoundationStoneTest16BB.install i base
        (FoundationStoneTest16AI.pushCode d n) 0))
      (entryState P (digit d) (FoundationStoneTest16BB.install i base
        (FoundationStoneTest16AI.pushCode d n) 0)) := by
  refine operation_reaches_of_run P owner (.peek i empty digit bad) hP ?_
    base (24 * n + 2 * d.val + 8) (by omega)
    (FoundationStoneTest16AI.pushCode d n)
    (FoundationStoneTest16AI.pushCode d n) (digit d) ?_
  · intro sink
    simp
  · simpa [operationEntry, operationExit] using
      routed_peek_exact_to (operationExit (.peek i empty digit bad)) d n

theorem primitive_peek_empty_reaches {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty bad : K) (digit : Digit → K)
    (hP : P owner = .peek i empty digit bad) (base : Reg5 → Nat) :
    Relation.TransGen
      (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
      (entryState P owner (FoundationStoneTest16BB.install i base 0 0))
      (entryState P empty (FoundationStoneTest16BB.install i base 0 0)) := by
  refine operation_reaches_of_run P owner (.peek i empty digit bad) hP ?_
    base 3 (by omega) 0 0 empty ?_
  · intro sink
    simp
  · simpa [operationEntry, operationExit] using
      routed_peek_empty_to (operationExit (.peek i empty digit bad))

theorem primitive_loop_reaches_self {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (anchor : K)
    (hP : P anchor = .loop anchor) (base : Reg5 → Nat) (a : Nat) :
    Relation.TransGen
      (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
      (entryState P anchor
        (FoundationStoneTest16BB.install 0 base a 0))
      (entryState P anchor
        (FoundationStoneTest16BB.install 0 base a 0)) := by
  refine operation_reaches_of_run P anchor (.loop anchor) hP ?_
    base 2 (by omega) a a anchor ?_
  · intro sink
    simp
  · simpa [operationEntry, operationExit] using
      terminal_bridge (operationExit (.loop anchor)) (.pop .empty) a 0
        pop_empty_terminal

theorem declared_bad_target_cycles {K : Type}
    [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (hsafe : BadTargetsLoop P)
    (owner bad : K) (hbad : badTarget (P owner) = some bad)
    (base : Reg5 → Nat) (a : Nat) :
    Relation.TransGen
      (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
      (entryState P bad (FoundationStoneTest16BB.install 0 base a 0))
      (entryState P bad (FoundationStoneTest16BB.install 0 base a 0)) :=
  primitive_loop_reaches_self P bad (hsafe owner bad hbad) base a

theorem pop_first_instruction_is_zero_test {K : Type}
    [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty : K) (digit : Digit → K) (bad : K)
    (hP : P owner = .pop i empty digit bad) :
    linkedProgram (operationBlocks P)
        (localLabel P owner (.work (.pop .start))) =
      .dec (FoundationStoneTest16BB.stackReg i)
        (localLabel P owner (.work (.pop (.scan 0))))
        (localLabel P owner (.work (.pop .empty))) := by
  simp [linkedProgram, operationBlocks, localLabel, routedIndex,
    routedDecode_encode, routedCode, hP, linkInstr, localTarget, resolve,
    operationRegister, routedProgram, stackProgram,
    FoundationStoneTest16BE.popProgram, FoundationStoneTest16BH.routeInstr,
    FoundationStoneTest16BC.mapInstr, FoundationStoneTest16BG.popName,
    FoundationStoneTest16BB.liftAWInstr, FoundationStoneTest16BB.activeReg,
    Instr.map]

theorem installed_empty_stack_is_zero {K : Type}
    [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty : K) (digit : Digit → K) (bad : K)
    (_hP : P owner = .pop i empty digit bad) (base : Reg5 → Nat) :
    (entryState P owner
      (FoundationStoneTest16BB.install i base 0 0)).counters
        (FoundationStoneTest16BB.stackReg i) = 0 := by
  simp [entryState, State.map, FoundationStoneTest16BB.install_stack]

structure PrimitiveContracts : Prop where
  push : ∀ {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg) (d : Digit)
    (next bad : K), P owner = .push i d next bad →
    ∀ (base : Reg5 → Nat) (n : Nat),
      Relation.TransGen
        (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
        (entryState P owner (FoundationStoneTest16BB.install i base n 0))
        (entryState P next (FoundationStoneTest16BB.install i base
          (FoundationStoneTest16AI.pushCode d n) 0))
  popDigit : ∀ {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty bad : K) (digit : Digit → K),
    P owner = .pop i empty digit bad →
    ∀ (base : Reg5 → Nat) (d : Digit) (n : Nat),
      Relation.TransGen
        (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
        (entryState P owner (FoundationStoneTest16BB.install i base
          (FoundationStoneTest16AI.pushCode d n) 0))
        (entryState P (digit d)
          (FoundationStoneTest16BB.install i base n 0))
  popEmpty : ∀ {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty bad : K) (digit : Digit → K),
    P owner = .pop i empty digit bad →
    ∀ (base : Reg5 → Nat),
      Relation.TransGen
        (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
        (entryState P owner (FoundationStoneTest16BB.install i base 0 0))
        (entryState P empty (FoundationStoneTest16BB.install i base 0 0))
  peekDigit : ∀ {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty bad : K) (digit : Digit → K),
    P owner = .peek i empty digit bad →
    ∀ (base : Reg5 → Nat) (d : Digit) (n : Nat),
      Relation.TransGen
        (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
        (entryState P owner (FoundationStoneTest16BB.install i base
          (FoundationStoneTest16AI.pushCode d n) 0))
        (entryState P (digit d) (FoundationStoneTest16BB.install i base
          (FoundationStoneTest16AI.pushCode d n) 0))
  peekEmpty : ∀ {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty bad : K) (digit : Digit → K),
    P owner = .peek i empty digit bad →
    ∀ (base : Reg5 → Nat),
      Relation.TransGen
        (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
        (entryState P owner (FoundationStoneTest16BB.install i base 0 0))
        (entryState P empty (FoundationStoneTest16BB.install i base 0 0))
  loop : ∀ {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (anchor : K),
    P anchor = .loop anchor →
    ∀ (base : Reg5 → Nat) (a : Nat),
      Relation.TransGen
        (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
        (entryState P anchor
          (FoundationStoneTest16BB.install 0 base a 0))
        (entryState P anchor
          (FoundationStoneTest16BB.install 0 base a 0))
  badCycle : ∀ {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K), BadTargetsLoop P →
    ∀ (owner bad : K), badTarget (P owner) = some bad →
    ∀ (base : Reg5 → Nat) (a : Nat),
      Relation.TransGen
        (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
        (entryState P bad (FoundationStoneTest16BB.install 0 base a 0))
        (entryState P bad (FoundationStoneTest16BB.install 0 base a 0))
  popZeroTest : ∀ {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner : K) (i : StackReg)
    (empty : K) (digit : Digit → K) (bad : K),
    P owner = .pop i empty digit bad →
      linkedProgram (operationBlocks P)
          (localLabel P owner (.work (.pop .start))) =
        .dec (FoundationStoneTest16BB.stackReg i)
          (localLabel P owner (.work (.pop (.scan 0))))
          (localLabel P owner (.work (.pop .empty)))

theorem primitive_contracts : PrimitiveContracts where
  push := primitive_push_reaches
  popDigit := primitive_pop_digit_reaches
  popEmpty := primitive_pop_empty_reaches
  peekDigit := primitive_peek_digit_reaches
  peekEmpty := primitive_peek_empty_reaches
  loop := primitive_loop_reaches_self
  badCycle := declared_bad_target_cycles
  popZeroTest := pop_first_instruction_is_zero_test

def computableSmokeProgram : Fin 1 → MacroInstr (Fin 1) := fun _ =>
  .push 0 0 0 0

#eval (operationBlocks computableSmokeProgram).code 0
  ⟨0, by simp [operationBlocks]⟩

/-! A full `StateTransition.Respects` theorem is intentionally deferred to the
statement-tree assembler: its source state includes the selected continuation
subtree.  Here the blocks and every result-dependent exit are concrete and
finite, so that assembler has no arithmetic or routing assumption left. -/

theorem turing_chamber_16BP_certificate :
    PrimitiveContracts ∧
    (∀ (K : Type) (_ : Fintype K) (_ : FiniteIndex K), Nonempty
      (Fin ((164 + (164 + Fintype.card K)) + 1))) ∧
    (∀ (K : Type) (_ : Fintype K) (i : StackReg)
      (empty bad : K) (next : Digit → K),
      operationExit (.pop i empty next bad) (.pop .empty) = empty) ∧
    (∀ (K : Type) (_ : Fintype K) (i : StackReg)
      (empty bad : K) (next : Digit → K) (d : Digit),
      operationExit (.pop i empty next bad) (.pop (.done d)) = next d) ∧
    (∀ (K : Type) (_ : Fintype K) (i : StackReg)
      (empty bad : K) (next : Digit → K) (d : Digit),
      operationExit (.peek i empty next bad) (.peek (.done d)) = next d) ∧
    (∀ (i : StackReg) (base : Reg5 → Nat) {L : Type} (label : L) (a : Nat),
      (FoundationStoneTest16BB.embed i base label a 0).counters
        FoundationStoneTest16BB.tempReg = 0) := by
  refine ⟨primitive_contracts, ?_, ?_, ?_, ?_, embedded_temp_zero⟩
  intro K inst index
  letI := inst
  letI := index
  exact ⟨0⟩
  · intro K inst i empty bad next
    exact pop_empty_exit_correct i empty bad next
  · intro K inst i empty bad next d
    exact pop_digit_exit_correct i empty bad next d
  · intro K inst i empty bad next d
    exact peek_digit_exit_correct i empty bad next d

#print axioms routedDecode_encode
#print axioms operation_control_is_finite
#print axioms operation_control_card
#print axioms frame_once
#print axioms embedded_temp_zero
#print axioms local_step_active_of_some
#print axioms local_run_active_of_some
#print axioms operation_reaches_of_run
#print axioms routed_push_exact_to
#print axioms routed_pop_exact_to
#print axioms routed_pop_empty_to
#print axioms routed_peek_exact_to
#print axioms routed_peek_empty_to
#print axioms primitive_push_reaches
#print axioms primitive_pop_digit_reaches
#print axioms primitive_pop_empty_reaches
#print axioms primitive_peek_digit_reaches
#print axioms primitive_peek_empty_reaches
#print axioms primitive_loop_reaches_self
#print axioms declared_bad_target_cycles
#print axioms primitive_contracts
#print axioms pop_first_instruction_is_zero_test
#print axioms installed_empty_stack_is_zero
#print axioms turing_chamber_16BP_certificate

end FoundationStoneTest16BP
