import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AG: THE EFFECTIVE MM2–RELAY DOOR

Lean 4.35.0-rc2 / Mathlib.

Test 16AB proved that the standard one-indexed MM2 instruction set compiles
step-for-step into the Wooden Idol relay.  Test 16AE showed that an undecidability
transfer also requires the compiler itself to be computable.  This file supplies
that missing certificate.

All syntax uses transparent Mathlib `Primcodable` sums, products and lists:

* MM2: `Bool ⊕ (Bool × Nat)` — increment, or decrement with positive jump;
* relay: `Unit ⊕ ((Bool × Nat) ⊕ (Bool × Nat × Nat))` — halt, increment,
  or decrement with explicit positive and zero successors.

`false` is body A and `true` is body B.

Lean certifies:

1. the indexed compiler is primitive recursive (therefore computable);
2. instruction fetch, one step, every bounded run and halting are exact;
3. compilation of whole problem instances is computable;
4. MM2 halting is computably many-one reducible to relay halting;
5. MM2 noncomputability therefore transfers to the relay;
6. red control: deleting address-zero padding breaks standard labels.

Combined with 16AF, the whole MM2→relay→helix tail is now an effective exact
reduction.  The remaining front-door obligation is the universality compiler
from Mathlib partial-recursive/Turing codes into MM2.
-/

namespace FoundationStoneTest16AG

abbrev Body := Bool
abbrev MM2Instr := Body ⊕ (Body × Nat)
abbrev MM2Program := List MM2Instr
abbrev Instr := Unit ⊕ ((Body × Nat) ⊕ (Body × Nat × Nat))
abbrev Program := List Instr

def halt : Instr := .inl ()
def inc (body : Body) (next : Nat) : Instr := .inr (.inl (body, next))
def dec (body : Body) (next zero : Nat) : Instr := .inr (.inr (body, next, zero))

def lowerAt (pc : Nat) : MM2Instr → Instr
  | .inl body => inc body (pc + 1)
  | .inr (body, jump) => dec body jump (pc + 1)

/-! ## 1. The compiler is primitive recursive -/

theorem incPair_prim : Primrec (fun p : Body × Nat => inc p.1 p.2) := by
  change Primrec (fun p : Body × Nat => (Sum.inr (Sum.inl p) : Instr))
  exact Primrec.sumInr.comp (Primrec.sumInl.comp Primrec.id)

theorem decPair_prim :
    Primrec (fun p : Body × (Nat × Nat) => dec p.1 p.2.1 p.2.2) := by
  change Primrec (fun p : Body × (Nat × Nat) => (Sum.inr (Sum.inr p) : Instr))
  exact Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.id)

theorem lowerAt_prim : Primrec₂ lowerAt := by
  have hleft : Primrec₂ (fun (x : Nat × MM2Instr) (body : Body) =>
      inc body (x.1 + 1)) := by
    exact (incPair_prim.comp
      (Primrec.pair Primrec.snd
        (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)))).to₂.of_eq
      (by intro x body; rfl)
  have hright : Primrec₂ (fun (x : Nat × MM2Instr) (q : Body × Nat) =>
      dec q.1 q.2 (x.1 + 1)) := by
    have hpack : Primrec (fun z : (Nat × MM2Instr) × (Body × Nat) =>
        (z.2.1, (z.2.2, z.1.1 + 1))) :=
      Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.snd.comp Primrec.snd)
          (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)))
    exact (decPair_prim.comp hpack).to₂.of_eq (by intro x q; rfl)
  have h := Primrec.sumCasesOn
    (Primrec.snd : Primrec (fun x : Nat × MM2Instr => x.2)) hleft hright
  exact h.to₂.of_eq (by intro pc i; cases i <;> rfl)

abbrev CompileAcc := Nat × List Instr

def accStep (acc : CompileAcc) (i : MM2Instr) : CompileAcc :=
  (acc.1 + 1, lowerAt acc.1 i :: acc.2)

theorem accStep_prim : Primrec₂ accStep := by
  exact (Primrec.pair
    (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.list_cons.comp
      (lowerAt_prim.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.snd.comp Primrec.fst))).to₂.of_eq (by intro acc i; rfl)

/-- The compiler traverses left-to-right while accumulating its output in reverse. -/
def lowerReverse (p : MM2Program) : Program :=
  (p.foldl accStep (1, [])).2

theorem lowerReverse_prim : Primrec lowerReverse := by
  have hhUnary : Primrec (fun pair : MM2Program × (CompileAcc × MM2Instr) =>
      accStep pair.2.1 pair.2.2) :=
    accStep_prim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hh : Primrec₂ (fun (_ : MM2Program) (z : CompileAcc × MM2Instr) =>
      accStep z.1 z.2) := hhUnary.to₂
  have hfold : Primrec (fun p : MM2Program => p.foldl accStep (1, [])) :=
    Primrec.list_foldl Primrec.id (Primrec.const (1, [])) hh
  exact Primrec.snd.comp hfold

/-- Address zero is padded with HALT, preserving MM2's one-indexed labels. -/
def compile (p : MM2Program) : Program := halt :: (lowerReverse p).reverse

theorem compile_prim : Primrec compile := by
  exact Primrec.list_cons.comp (Primrec.const halt)
    (Primrec.list_reverse.comp lowerReverse_prim)

theorem compile_computable : Computable compile := compile_prim.to_comp

/-! ## A recursive presentation used to prove semantic correctness -/

def lowerFrom : Nat → MM2Program → Program
  | _, [] => []
  | pc, i :: rest => lowerAt pc i :: lowerFrom (pc + 1) rest

theorem fold_acc : ∀ (p : MM2Program) (pc : Nat) (out : Program),
    p.foldl accStep (pc, out) =
      (pc + p.length, (lowerFrom pc p).reverse ++ out) := by
  intro p
  induction p with
  | nil => intro pc out; simp [lowerFrom]
  | cons i rest ih =>
      intro pc out
      simp only [List.foldl_cons, accStep]
      rw [ih]
      simp only [lowerFrom, List.reverse_cons, List.length_cons]
      apply Prod.ext
      · simp; omega
      · simp [List.append_assoc]

theorem compile_eq_recursive (p : MM2Program) :
    compile p = halt :: lowerFrom 1 p := by
  unfold compile lowerReverse
  rw [fold_acc]
  simp

/-! ## 2. Source and target operational semantics -/

structure State where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq, Repr

def get (s : State) (body : Body) : Nat := if body then s.b else s.a

def set (s : State) (pc : Nat) (body : Body) (value : Nat) : State :=
  if body then ⟨pc, s.a, value⟩ else ⟨pc, value, s.b⟩

def mm2Fetch (p : MM2Program) (pc : Nat) : Option MM2Instr :=
  if pc = 0 then none else p[pc - 1]?

def mm2Execute (i : MM2Instr) (s : State) : State :=
  match i with
  | .inl body => set s (s.pc + 1) body (get s body + 1)
  | .inr (body, jump) =>
      if get s body = 0 then { s with pc := s.pc + 1 }
      else set s jump body (get s body - 1)

def mm2Step (p : MM2Program) (s : State) : Option State :=
  (mm2Fetch p s.pc).map fun i => mm2Execute i s

def mm2Run (p : MM2Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
      match mm2Step p s with
      | none => none
      | some s' => mm2Run p n s'

def fetch (p : Program) (pc : Nat) : Instr := (p[pc]?).getD halt

def execute (i : Instr) (s : State) : Option State :=
  match i with
  | .inl _ => none
  | .inr (.inl (body, next)) => some (set s next body (get s body + 1))
  | .inr (.inr (body, next, zero)) =>
      if get s body = 0 then some { s with pc := zero }
      else some (set s next body (get s body - 1))

def step (p : Program) (s : State) : Option State := execute (fetch p s.pc) s

def run (p : Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
      match step p s with
      | none => none
      | some s' => run p n s'

theorem lowerFrom_get? : ∀ (p : MM2Program) base k,
    (lowerFrom base p)[k]? = (p[k]?).map (lowerAt (base + k)) := by
  intro p
  induction p with
  | nil => intro base k; simp [lowerFrom]
  | cons i rest ih =>
      intro base k
      cases k with
      | zero => simp [lowerFrom]
      | succ k =>
          simp only [lowerFrom, List.getElem?_cons_succ, Option.map]
          rw [ih (base + 1) k]
          rw [show base + 1 + k = base + (k + 1) by omega]
          cases rest[k]? <;> rfl

theorem fetch_compile (p : MM2Program) (pc : Nat) :
    fetch (compile p) pc =
      match mm2Fetch p pc with
      | none => halt
      | some i => lowerAt pc i := by
  rw [compile_eq_recursive]
  cases pc with
  | zero => rfl
  | succ k =>
      simp only [fetch, List.getElem?_cons_succ, mm2Fetch,
        Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      rw [lowerFrom_get?]
      simp only [Nat.add_comm 1 k]
      cases p[k]? <;> rfl

theorem execute_lower (pc : Nat) (i : MM2Instr) (s : State) (hpc : s.pc = pc) :
    execute (lowerAt pc i) s = some (mm2Execute i s) := by
  subst pc
  cases i with
  | inl body => cases body <;> rfl
  | inr payload =>
      obtain ⟨body, jump⟩ := payload
      cases body with
      | false =>
          by_cases h : s.a = 0 <;>
            simp [lowerAt, dec, execute, mm2Execute, get, set, h]
      | true =>
          by_cases h : s.b = 0 <;>
            simp [lowerAt, dec, execute, mm2Execute, get, set, h]

theorem step_compiles (p : MM2Program) (s : State) :
    step (compile p) s = mm2Step p s := by
  unfold step mm2Step
  rw [fetch_compile]
  cases h : mm2Fetch p s.pc with
  | none => rfl
  | some i =>
      simp only [Option.map_some]
      exact execute_lower s.pc i s rfl

theorem run_compiles (p : MM2Program) : ∀ n s,
    run (compile p) n s = mm2Run p n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      unfold run mm2Run
      rw [step_compiles]
      cases mm2Step p s with
      | none => rfl
      | some s' => exact ih s'

/-! ## 3–5. Effective many-one reduction of problem instances -/

abbrev MM2Problem := MM2Program × (Nat × Nat)
abbrev RelayProblem := Program × (Nat × Nat)

def MM2Halts (q : MM2Problem) : Prop :=
  ∃ n, mm2Run q.1 n ⟨1, q.2.1, q.2.2⟩ = none

def RelayHalts (q : RelayProblem) : Prop :=
  ∃ n, run q.1 n ⟨1, q.2.1, q.2.2⟩ = none

def compileProblem (q : MM2Problem) : RelayProblem := (compile q.1, q.2)

theorem compileProblem_prim : Primrec compileProblem := by
  exact Primrec.pair (compile_prim.comp Primrec.fst) Primrec.snd

theorem compileProblem_computable : Computable compileProblem :=
  compileProblem_prim.to_comp

theorem halting_compiles (q : MM2Problem) :
    MM2Halts q ↔ RelayHalts (compileProblem q) := by
  unfold MM2Halts RelayHalts compileProblem
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · rw [run_compiles, hn]
  · rw [run_compiles] at hn
    exact hn

theorem mm2_to_relay_is_effective : MM2Halts ≤₀ RelayHalts :=
  ⟨compileProblem, compileProblem_computable, halting_compiles⟩

theorem mm2_noncomputability_transfers
    (mm2Undecidable : ¬ ComputablePred MM2Halts) :
    ¬ ComputablePred RelayHalts := by
  intro relayDecidable
  exact mm2Undecidable
    (ComputablePred.computable_of_manyOneReducible mm2_to_relay_is_effective
      relayDecidable)

/-! ## Red control: address-zero padding is semantically necessary -/

def badCompile (p : MM2Program) : Program := lowerFrom 1 p
def incA : MM2Instr := .inl false

theorem missing_padding_breaks_labels :
    step (badCompile [incA]) ⟨1, 0, 0⟩ = none ∧
    step (compile [incA]) ⟨1, 0, 0⟩ = some ⟨2, 1, 0⟩ := by
  decide

theorem effective_mm2_relay_door_certificate :
    Primrec compileProblem ∧
    (∀ q, MM2Halts q ↔ RelayHalts (compileProblem q)) ∧
    MM2Halts ≤₀ RelayHalts ∧
    (¬ ComputablePred MM2Halts → ¬ ComputablePred RelayHalts) ∧
    step (badCompile [incA]) ⟨1, 0, 0⟩ = none :=
  ⟨compileProblem_prim, halting_compiles, mm2_to_relay_is_effective,
   mm2_noncomputability_transfers, missing_padding_breaks_labels.1⟩

#print axioms lowerAt_prim
#print axioms compile_prim
#print axioms compile_computable
#print axioms fetch_compile
#print axioms step_compiles
#print axioms run_compiles
#print axioms compileProblem_prim
#print axioms halting_compiles
#print axioms mm2_to_relay_is_effective
#print axioms mm2_noncomputability_transfers
#print axioms missing_padding_breaks_labels
#print axioms effective_mm2_relay_door_certificate

end FoundationStoneTest16AG
