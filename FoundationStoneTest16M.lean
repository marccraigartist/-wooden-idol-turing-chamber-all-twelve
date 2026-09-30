import Mathlib.Computability.Halting

/-!
# THE VERIFIED ASSEMBLER — FOUNDATION STONE TEST 16M

Test 16L exposed one exact open socket: a computable, halting-preserving compiler
from a universal source into the encoded two-counter relay.  This test closes the
first half of that socket.  It does not claim Minsky universality.

The source is now a genuinely structured two-counter assembly language:

* `none`                         — halt;
* `some (inl (body,next))`       — increment and jump;
* `some (inr (body,next,zero))`  — decrement-or-zero-test.

The target is 16L's primitive tuple code `(tag,body,next,ground)`.  Lean proves:

1. every source instruction is decoded back exactly after lowering;
2. fetching commutes with assembly, including falling off the end;
3. one step, every finite run, and halting are preserved exactly;
4. the assembler is primitive recursive, hence computable;
5. stopper and climber controls survive assembly;
6. red control: an assembler that merely emits `stop` fails on the climber.

This removes representation/encoding from the Minsky gap.  The remaining open
work is mathematical rather than syntactic: compile a known universal model into
this structured two-counter assembly and prove its simulation invariant.
-/

namespace FoundationStoneTest16M

/-! ## 1. Source and target languages -/

abbrev Body := Bool

/-- `none` is halt; the left sum is increment; the right sum is decrement/test. -/
abbrev AsmInstr := Option ((Body × Nat) ⊕ (Body × Nat × Nat))
abbrev AsmProgram := List AsmInstr

def halt : AsmInstr := none
def inc (b : Body) (next : Nat) : AsmInstr := some (.inl (b, next))
def dec (b : Body) (next ground : Nat) : AsmInstr := some (.inr (b, next, ground))

abbrev InstrCode := Nat × Body × Nat × Nat
abbrev Program := List InstrCode

inductive Instr
  | up (b : Body) (next : Nat)
  | down (b : Body) (next ground : Nat)
  | stop
deriving DecidableEq

def stopCode : InstrCode := (0, false, 0, 0)
def upCode (b : Body) (next : Nat) : InstrCode := (1, b, next, 0)
def downCode (b : Body) (next ground : Nat) : InstrCode := (2, b, next, ground)

def decodeInstr (i : InstrCode) : Instr :=
  if i.1 = 1 then .up i.2.1 i.2.2.1
  else if i.1 = 2 then .down i.2.1 i.2.2.1 i.2.2.2
  else .stop

def lowerInstr : AsmInstr → InstrCode
  | none => stopCode
  | some (.inl (b, next)) => upCode b next
  | some (.inr (b, next, ground)) => downCode b next ground

def compile (p : AsmProgram) : Program := p.map lowerInstr

/-- Lowering then decoding recovers the structured instruction exactly. -/
theorem decode_lower : ∀ i : AsmInstr,
    decodeInstr (lowerInstr i) =
      match i with
      | none => .stop
      | some (.inl (b, next)) => .up b next
      | some (.inr (b, next, ground)) => .down b next ground := by
  intro i
  rcases i with _ | (_ | _) <;> rfl

def sourceFetch (p : AsmProgram) (pc : Nat) : AsmInstr := (p[pc]?).getD halt
def targetFetch (p : Program) (pc : Nat) : Instr := decodeInstr ((p[pc]?).getD stopCode)

def meaning : AsmInstr → Instr
  | none => .stop
  | some (.inl (b, next)) => .up b next
  | some (.inr (b, next, ground)) => .down b next ground

/-- Fetching through the assembled code has exactly the source meaning. -/
theorem fetch_compiles (p : AsmProgram) (pc : Nat) :
    targetFetch (compile p) pc = meaning (sourceFetch p pc) := by
  cases h : p[pc]? with
  | none => simp [targetFetch, compile, sourceFetch, h, halt, stopCode, decodeInstr, meaning]
  | some i =>
      simpa [targetFetch, compile, sourceFetch, h, meaning] using decode_lower i

/-! ## 2. Exact operational simulation -/

structure CState where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq

def get (s : CState) : Body → Nat
  | false => s.a
  | true => s.b

def set (s : CState) (pc : Nat) : Body → Nat → CState
  | false, v => ⟨pc, v, s.b⟩
  | true, v => ⟨pc, s.a, v⟩

def execute (i : Instr) (s : CState) : Option CState :=
  match i with
  | .up b nx => some (set s nx b (get s b + 1))
  | .down b nx gr =>
      if get s b = 0 then some { s with pc := gr }
      else some (set s nx b (get s b - 1))
  | .stop => none

def astep (p : AsmProgram) (s : CState) : Option CState :=
  execute (meaning (sourceFetch p s.pc)) s

def cstep (p : Program) (s : CState) : Option CState :=
  execute (targetFetch p s.pc) s

/-- Assembly preserves one machine step, not merely the final answer. -/
theorem step_compiles (p : AsmProgram) (s : CState) :
    cstep (compile p) s = astep p s := by
  unfold cstep astep
  rw [fetch_compiles]

def arun (p : AsmProgram) : Nat → CState → Option CState
  | 0, s => some s
  | n + 1, s =>
      match astep p s with
      | none => none
      | some s' => arun p n s'

def crun (p : Program) : Nat → CState → Option CState
  | 0, s => some s
  | n + 1, s =>
      match cstep p s with
      | none => none
      | some s' => crun p n s'

/-- Assembly preserves every bounded execution exactly. -/
theorem run_compiles (p : AsmProgram) :
    ∀ n s, crun (compile p) n s = arun p n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      unfold crun arun
      rw [step_compiles]
      cases astep p s with
      | none => rfl
      | some s' => exact ih s'

def AsmHalts (p : AsmProgram) (s : CState) : Prop := ∃ n, arun p n s = none
def CodeHalts (p : Program) (s : CState) : Prop := ∃ n, crun p n s = none

/-- Assembly neither creates nor destroys halting. -/
theorem halting_compiles (p : AsmProgram) (s : CState) :
    AsmHalts p s ↔ CodeHalts (compile p) s := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · rw [run_compiles, hn]
  · rw [run_compiles] at hn
    exact hn

/-! ## 3. The compiler is effective -/

/-- The instruction lowerer is primitive recursive. -/
def lowerSome : ((Body × Nat) ⊕ (Body × Nat × Nat)) → InstrCode
  | .inl (b, next) => upCode b next
  | .inr (b, next, ground) => downCode b next ground

theorem lowerSome_primrec : Primrec lowerSome := by
  have hup : Primrec (fun q : Body × Nat => upCode q.1 q.2) :=
    (Primrec.const (1 : Nat)).pair
      (Primrec.fst.pair (Primrec.snd.pair (Primrec.const 0)))
  have hdown : Primrec (fun q : Body × Nat × Nat => downCode q.1 q.2.1 q.2.2) :=
    (Primrec.const (2 : Nat)).pair
      (Primrec.fst.pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd)))
  refine (Primrec.sumCasesOn Primrec.id
    (Primrec.comp₂ hup Primrec₂.right) (Primrec.comp₂ hdown Primrec₂.right)).of_eq ?_
  intro x
  rcases x with x | x <;> rfl

theorem lowerInstr_primrec : Primrec lowerInstr := by
  -- The proof follows the actual three constructors; no semantic oracle occurs.
  refine (Primrec.option_casesOn Primrec.id (Primrec.const stopCode)
    (Primrec.comp₂ lowerSome_primrec Primrec₂.right)).of_eq ?_
  intro x
  cases x with
  | none => rfl
  | some s =>
      cases s with
      | inl q => rcases q with ⟨b, next⟩; rfl
      | inr q => rcases q with ⟨b, next, ground⟩; rfl

theorem compile_primrec : Primrec compile := by
  exact Primrec.list_map Primrec.id (lowerInstr_primrec.comp Primrec.snd |>.to₂)

theorem compile_computable : Computable compile := compile_primrec.to_comp

/-! ## 4. Controls and the red assembler -/

def start : CState := ⟨0, 0, 0⟩
def stopper : AsmProgram := [halt]
def climber : AsmProgram := [inc false 0]

theorem stopper_survives :
    arun stopper 1 start = none ∧ crun (compile stopper) 1 start = none := by decide

theorem arun_climber_from (n height : Nat) :
    arun climber n ⟨0, height, 0⟩ = some ⟨0, height + n, 0⟩ := by
  induction n generalizing height with
  | zero => simp [arun]
  | succ n ih =>
      change arun climber n ⟨0, height + 1, 0⟩ = some ⟨0, height + (n + 1), 0⟩
      rw [ih]
      congr 2
      omega

theorem arun_climber (n : Nat) : arun climber n start = some ⟨0, n, 0⟩ := by
  simpa [start] using arun_climber_from n 0

theorem climber_survives (n : Nat) :
    arun climber n start ≠ none ∧ crun (compile climber) n start ≠ none := by
  constructor
  · rw [arun_climber]
    simp
  · rw [run_compiles]
    rw [arun_climber]
    simp

/-- A superficially well-typed but dishonest assembler: erase every instruction. -/
def eraseCompile (p : AsmProgram) : Program := p.map (fun _ => stopCode)

/-- Red control: emitting code is not enough; semantic preservation can fail. -/
theorem erasing_compiler_fails :
    crun (eraseCompile climber) 1 start ≠ arun climber 1 start := by decide

/-! ## Certificate -/

theorem verified_assembler_certificate :
    Computable compile ∧
    (∀ p s, cstep (compile p) s = astep p s) ∧
    (∀ p n s, crun (compile p) n s = arun p n s) ∧
    (∀ p s, AsmHalts p s ↔ CodeHalts (compile p) s) ∧
    crun (eraseCompile climber) 1 start ≠ arun climber 1 start :=
  ⟨compile_computable, step_compiles, run_compiles, halting_compiles,
    erasing_compiler_fails⟩

#print axioms decode_lower
#print axioms fetch_compiles
#print axioms step_compiles
#print axioms run_compiles
#print axioms halting_compiles
#print axioms lowerInstr_primrec
#print axioms compile_primrec
#print axioms compile_computable
#print axioms stopper_survives
#print axioms climber_survives
#print axioms erasing_compiler_fails
#print axioms verified_assembler_certificate

end FoundationStoneTest16M
