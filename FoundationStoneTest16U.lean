import Mathlib.Computability.Halting

/-!
# THE LAST ADAPTER — FOUNDATION STONE TEST 16U

Tests 16L–16M prove that the two-body helix exactly simulates an explicit-label
two-counter relay, and that its tuple-code assembler is computable.  This test
connects that relay to the conventional Minsky normal form:

* `halt`
* `inc b` — increment counter `b`, then continue at `pc + 1`
* `jzdec b zero` — if counter `b` is zero jump to `zero`; otherwise decrement it
  and continue at `pc + 1`.

The source syntax deliberately does NOT contain the fall-through label.  The
compiler must calculate it from the instruction's address.  Lean certifies:

1. indexed lowering inserts exactly `pc + 1`;
2. fetching commutes with compilation, including past the program's end;
3. one step, every bounded run, and halting are preserved exactly;
4. the address-sensitive compiler is primitive recursive, hence computable;
5. a concrete increment/decrement/zero program survives the translation;
6. RED CONTROL: a compiler that sends the nonzero decrement branch back to its
   own address disagrees with the source after two steps.

This closes the normal-form/representation part of the Turing chamber.  It does
NOT prove two-counter universality.  The remaining theorem socket is now only:
a computable, halting-preserving compiler from Mathlib's partial-recursive codes
to this conventional `MProgram`.
-/

namespace FoundationStoneTest16U

abbrev Body := Bool

/-! ## 1. Conventional source and explicit relay target -/

/-- `none` is halt; `some (b, none)` is increment; `some (b, some z)` is
decrement-or-zero-test with zero target `z`. -/
abbrev MInstr := Option (Body × Option Nat)
abbrev MProgram := List MInstr

def halt : MInstr := none
def inc (b : Body) : MInstr := some (b, none)
def jzdec (b : Body) (zero : Nat) : MInstr := some (b, some zero)

/-- Explicit-label relay assembly, the source language of Test 16M. -/
abbrev AsmInstr := Option ((Body × Nat) ⊕ (Body × Nat × Nat))
abbrev AsmProgram := List AsmInstr

def ahalt : AsmInstr := none
def ainc (b : Body) (next : Nat) : AsmInstr := some (.inl (b, next))
def adec (b : Body) (next zero : Nat) : AsmInstr := some (.inr (b, next, zero))

/-- Lower one instruction at its actual address. -/
def lowerAt (pc : Nat) : MInstr → AsmInstr
  | none => ahalt
  | some (b, none) => ainc b (pc + 1)
  | some (b, some zero) => adec b (pc + 1) zero

/-- Address-sensitive compiler. -/
def compileFrom : Nat → MProgram → AsmProgram
  | _, [] => []
  | pc, i :: rest => lowerAt pc i :: compileFrom (pc + 1) rest

def compile (p : MProgram) : AsmProgram := compileFrom 0 p

theorem compileFrom_length (base : Nat) : ∀ p : MProgram,
    (compileFrom base p).length = p.length := by
  intro p
  induction p generalizing base with
  | nil => rfl
  | cons i rest ih => simp [compileFrom, ih]

/-- The instruction at offset `n` is lowered at address `base + n`. -/
theorem compileFrom_get (base : Nat) (p : MProgram) (n : Nat) :
    (compileFrom base p)[n]? = (p[n]?).map (lowerAt (base + n)) := by
  induction p generalizing base n with
  | nil => simp [compileFrom]
  | cons i rest ih =>
      cases n with
      | zero => simp [compileFrom]
      | succ n =>
          simp only [compileFrom, List.getElem?_cons_succ]
          rw [ih]
          congr 2
          omega

theorem compile_get (p : MProgram) (pc : Nat) :
    (compile p)[pc]? = (p[pc]?).map (lowerAt pc) := by
  simpa [compile] using compileFrom_get 0 p pc

def sourceFetch (p : MProgram) (pc : Nat) : MInstr := (p[pc]?).getD halt
def targetFetch (p : AsmProgram) (pc : Nat) : AsmInstr := (p[pc]?).getD ahalt

/-- Fetching compiled code has exactly the indexed meaning of source fetch. -/
theorem fetch_compiles (p : MProgram) (pc : Nat) :
    targetFetch (compile p) pc = lowerAt pc (sourceFetch p pc) := by
  unfold targetFetch sourceFetch
  rw [compile_get]
  cases h : p[pc]? with
  | none => simp [targetFetch, sourceFetch, h, halt, ahalt, lowerAt]
  | some i => simp [targetFetch, sourceFetch, h]

/-! ## 2. Exact operational simulation -/

structure State where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq

def get (s : State) : Body → Nat
  | false => s.a
  | true => s.b

def set (s : State) (pc : Nat) : Body → Nat → State
  | false, v => ⟨pc, v, s.b⟩
  | true, v => ⟨pc, s.a, v⟩

def mexec (i : MInstr) (s : State) : Option State :=
  match i with
  | none => none
  | some (b, none) => some (set s (s.pc + 1) b (get s b + 1))
  | some (b, some zero) =>
      if get s b = 0 then some { s with pc := zero }
      else some (set s (s.pc + 1) b (get s b - 1))

def aexec (i : AsmInstr) (s : State) : Option State :=
  match i with
  | none => none
  | some (.inl (b, next)) => some (set s next b (get s b + 1))
  | some (.inr (b, next, zero)) =>
      if get s b = 0 then some { s with pc := zero }
      else some (set s next b (get s b - 1))

theorem lower_executes (pc : Nat) (i : MInstr) (s : State) (hpc : s.pc = pc) :
    aexec (lowerAt pc i) s = mexec i s := by
  subst pc
  rcases i with _ | ⟨b, _ | zero⟩ <;> rfl

def mstep (p : MProgram) (s : State) : Option State := mexec (sourceFetch p s.pc) s
def astep (p : AsmProgram) (s : State) : Option State := aexec (targetFetch p s.pc) s

/-- The conventional machine and compiled relay agree at every state. -/
theorem step_compiles (p : MProgram) (s : State) :
    astep (compile p) s = mstep p s := by
  unfold astep mstep
  rw [fetch_compiles]
  exact lower_executes s.pc (sourceFetch p s.pc) s rfl

def mrun (p : MProgram) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
      match mstep p s with
      | none => none
      | some s' => mrun p n s'

def arun (p : AsmProgram) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
      match astep p s with
      | none => none
      | some s' => arun p n s'

/-- Every finite execution is preserved, including the first stopping time. -/
theorem run_compiles (p : MProgram) :
    ∀ n s, arun (compile p) n s = mrun p n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      unfold arun mrun
      rw [step_compiles]
      cases mstep p s with
      | none => rfl
      | some s' => exact ih s'

def MHalts (p : MProgram) (s : State) : Prop := ∃ n, mrun p n s = none
def AsmHalts (p : AsmProgram) (s : State) : Prop := ∃ n, arun p n s = none

theorem halting_compiles (p : MProgram) (s : State) :
    MHalts p s ↔ AsmHalts (compile p) s := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · rw [run_compiles, hn]
  · rw [run_compiles] at hn
    exact hn

/-! ## 3. The address-sensitive compiler is effective -/

/-- Lowering at an address is primitive recursive in both inputs. -/
theorem lowerAt_primrec : Primrec₂ lowerAt := by
  -- The proof follows the three constructors; `pc + 1` is the only calculation.
  have hinc : Primrec (fun q : Nat × Body => ainc q.2 (q.1 + 1)) := by
    exact Primrec.option_some.comp (Primrec.sumInl.comp
      (Primrec.snd.pair (Primrec.succ.comp Primrec.fst)))
  have hdec : Primrec (fun q : (Nat × Body) × Nat =>
      adec q.1.2 (q.1.1 + 1) q.2) := by
    exact Primrec.option_some.comp (Primrec.sumInr.comp
      ((Primrec.snd.comp Primrec.fst).pair
        ((Primrec.succ.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)))
  have hpayload : Primrec (fun q : Nat × (Body × Option Nat) =>
      match q.2.2 with
      | none => ainc q.2.1 (q.1 + 1)
      | some z => adec q.2.1 (q.1 + 1) z) := by
    have hg : Primrec₂ (fun (q : Nat × (Body × Option Nat)) (z : Nat) =>
        adec q.2.1 (q.1 + 1) z) :=
      (hdec.comp
        (((Primrec.fst.comp Primrec.fst).pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)).to₂
    refine (Primrec.option_casesOn (Primrec.snd.comp Primrec.snd)
      (hinc.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      hg).of_eq ?_
    · intro q
      rcases q with ⟨pc, b, _ | z⟩ <;> rfl
  have hg : Primrec₂ (fun (q : Nat × MInstr) (payload : Body × Option Nat) =>
      match payload.2 with
      | none => ainc payload.1 (q.1 + 1)
      | some z => adec payload.1 (q.1 + 1) z) :=
    (hpayload.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  refine (Primrec.option_casesOn Primrec.snd (Primrec.const ahalt)
    hg).to₂.of_eq ?_
  · intro pc i
    rcases i with _ | ⟨b, _ | z⟩ <;> rfl

/-- A fold state stores the next address and the reversed output accumulated so far. -/
abbrev CompileState := Nat × AsmProgram

def compileFold (st : CompileState) (i : MInstr) : CompileState :=
  (st.1 + 1, lowerAt st.1 i :: st.2)

def compileViaFold (p : MProgram) : AsmProgram :=
  (p.foldl compileFold (0, [])).2.reverse

theorem compileViaFold_eq_compile (p : MProgram) : compileViaFold p = compile p := by
  unfold compileViaFold compile
  have aux : ∀ (xs : MProgram) (base : Nat) (out : AsmProgram),
      (xs.foldl compileFold (base, out)).2.reverse =
        out.reverse ++ compileFrom base xs := by
    intro xs
    induction xs with
    | nil => intro base out; simp [compileFold, compileFrom]
    | cons i rest ih =>
        intro base out
        simp only [List.foldl_cons, compileFold]
        rw [ih]
        simp [compileFrom, List.reverse_cons, List.append_assoc]
  simpa using aux p 0 []

theorem compileFold_primrec : Primrec₂ compileFold := by
  exact ((Primrec.succ.comp (Primrec.fst.comp Primrec.fst)).pair
    (Primrec.list_cons.comp
      (lowerAt_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.snd.comp Primrec.fst))).to₂

theorem compileViaFold_primrec : Primrec compileViaFold := by
  unfold compileViaFold
  have hstep : Primrec₂ (fun (_ : MProgram) (q : CompileState × MInstr) =>
      compileFold q.1 q.2) :=
    (compileFold_primrec.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_reverse.comp
    (Primrec.snd.comp
      (Primrec.list_foldl Primrec.id (Primrec.const (0, [])) hstep))

theorem compile_primrec : Primrec compile := by
  exact compileViaFold_primrec.of_eq compileViaFold_eq_compile

theorem compile_computable : Computable compile := compile_primrec.to_comp

/-! ## 4. Controls and a red compiler -/

def start : State := ⟨0, 0, 0⟩

/-- Increment A; decrement it; halt on the fall-through; zero branch also halts. -/
def sample : MProgram := [inc false, jzdec false 3, halt, halt]

theorem sample_source_trace :
    mrun sample 2 start = some ⟨2, 0, 0⟩ ∧ mrun sample 3 start = none := by decide

theorem sample_compiled_trace :
    arun (compile sample) 2 start = some ⟨2, 0, 0⟩ ∧
      arun (compile sample) 3 start = none := by decide

/-- Wrong on purpose: after a successful decrement it jumps back to itself. -/
def badLowerAt (pc : Nat) : MInstr → AsmInstr
  | none => ahalt
  | some (b, none) => ainc b (pc + 1)
  | some (b, some zero) => adec b pc zero

def badCompileFrom : Nat → MProgram → AsmProgram
  | _, [] => []
  | pc, i :: rest => badLowerAt pc i :: badCompileFrom (pc + 1) rest

def badCompile (p : MProgram) : AsmProgram := badCompileFrom 0 p

/-- RED CONTROL: representation similarity is insufficient; the branch target matters. -/
theorem bad_compiler_fails :
    arun (badCompile sample) 2 start = some ⟨1, 0, 0⟩ ∧
      arun (badCompile sample) 2 start ≠ mrun sample 2 start := by decide

/-! ## 5. Exact remaining socket -/

open Nat.Partrec (Code)

def SourceHalts (input : Nat) (c : Code) : Prop :=
  (Nat.Partrec.Code.eval c input).Dom

/-- The sole mathematical bridge still owed after 16U. -/
structure ConventionalMinskyBridge (input : Nat) where
  translate : Code → MProgram
  translate_computable : Computable translate
  correct : ∀ c, SourceHalts input c ↔ MHalts (translate c) start

/-- 16U composes any future genuine universality bridge with the verified adapter. -/
theorem bridge_reaches_explicit_relay (input : Nat) (B : ConventionalMinskyBridge input)
    (c : Code) :
    SourceHalts input c ↔ AsmHalts (compile (B.translate c)) start := by
  rw [B.correct c, halting_compiles]

theorem last_adapter_certificate :
    Computable compile ∧
    (∀ p s, astep (compile p) s = mstep p s) ∧
    (∀ p n s, arun (compile p) n s = mrun p n s) ∧
    (∀ p s, MHalts p s ↔ AsmHalts (compile p) s) ∧
    arun (badCompile sample) 2 start ≠ mrun sample 2 start :=
  ⟨compile_computable, step_compiles, run_compiles, halting_compiles,
   bad_compiler_fails.2⟩

#print axioms compileFrom_get
#print axioms fetch_compiles
#print axioms step_compiles
#print axioms run_compiles
#print axioms halting_compiles
#print axioms compile_primrec
#print axioms compile_computable
#print axioms sample_compiled_trace
#print axioms bad_compiler_fails
#print axioms bridge_reaches_explicit_relay
#print axioms last_adapter_certificate

end FoundationStoneTest16U
