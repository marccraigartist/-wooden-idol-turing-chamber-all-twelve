/-!
# THE STUTTERING BRIDGE — FOUNDATION STONE TEST 16N

Core Lean only; no imports.

16M proved an exact one-source-step/one-target-step assembler.  Universality
needs a stronger kind of simulation: one atomic source operation may require
an unbounded number of primitive two-counter instructions.  This file builds
and verifies that first macro layer.

The atomic source command `clear body; goto exit` is compiled to the single
primitive relay instruction

    down body entry exit

which loops at `entry` while the body is positive and exits only at zero.
The code has constant size, but its execution length is data-dependent.

Lean certifies:

1. exact prefixes: after `n ≤ height` relay steps, the remaining height is
   exactly `height - n` and the machine is still inside the macro;
2. exact completion: the exit is reached after `h + 1` steps; when the exit
   differs from the entry, no earlier prefix has reached it;
3. the same proof works for either body;
4. sequential composition clears both bodies in exactly `a + b + 2` steps;
5. boundary states agree with the atomic source semantics;
6. red controls: one relay step cannot clear height two, and no fixed step
   bound implements clear for every input.

This is not Minsky universality.  It is the first genuine simulation invariant
needed by that port: a source step is represented by a finite but unbounded
target path, with entry/exit boundaries and its hidden work kept visible.
-/

namespace FoundationStoneTest16N

abbrev Body := Bool
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

def fetch (p : Program) (pc : Nat) : Instr :=
  decodeInstr ((p[pc]?).getD stopCode)

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

def cstep (p : Program) (s : CState) : Option CState :=
  match fetch p s.pc with
  | .up b nx => some (set s nx b (get s b + 1))
  | .down b nx gr =>
      if get s b = 0 then some { s with pc := gr }
      else some (set s nx b (get s b - 1))
  | .stop => none

def crun (p : Program) : Nat → CState → Option CState
  | 0, s => some s
  | n + 1, s =>
      match cstep p s with
      | none => none
      | some s' => crun p n s'

/-! ## 1. One atomic clear macro -/

/-- The compiled block occupies address 0 and exits to `exit`. -/
def clearBlock (b : Body) (exit : Nat) : Program := [downCode b 0 exit]

/-- A canonical entry state: selected body has `height`; the other has `other`. -/
def entryState : Body → Nat → Nat → CState
  | false, height, other => ⟨0, height, other⟩
  | true, height, other => ⟨0, other, height⟩

/-- The atomic source result at the macro boundary. -/
def clearedState : Body → Nat → Nat → CState
  | false, exit, other => ⟨exit, 0, other⟩
  | true, exit, other => ⟨exit, other, 0⟩

/-- While positive, one target step removes exactly one unit and stays inside. -/
theorem clear_one_positive (b : Body) (exit height other : Nat) :
    cstep (clearBlock b exit) (entryState b (height + 1) other) =
      some (entryState b height other) := by
  cases b <;> simp [cstep, clearBlock, fetch, decodeInstr, downCode, entryState, get, set]

/-- At zero, one target step crosses the boundary to the source result. -/
theorem clear_one_zero (b : Body) (exit other : Nat) :
    cstep (clearBlock b exit) (entryState b 0 other) =
      some (clearedState b exit other) := by
  cases b <;> simp [cstep, clearBlock, fetch, decodeInstr, downCode, entryState,
    clearedState, get]

/-- Exact prefix invariant: before the boundary, elapsed work is not forgotten. -/
theorem clear_prefix (b : Body) (exit height other : Nat) :
    ∀ n, n ≤ height →
      crun (clearBlock b exit) n (entryState b height other) =
        some (entryState b (height - n) other) := by
  intro n hn
  induction n generalizing height with
  | zero => simp [crun]
  | succ n ih =>
      obtain ⟨h, rfl⟩ : ∃ h, height = h + 1 :=
        ⟨height - 1, by omega⟩
      unfold crun
      rw [clear_one_positive]
      simp only
      have hn' : n ≤ h := by omega
      have heq : h + 1 - (n + 1) = h - n := by omega
      rw [heq, ih h hn']

/-- If entry and exit are distinct, no prefix through step `height` is already
at the completed boundary.  Thus `height + 1` is the first completion time. -/
theorem clear_not_finished_early (b : Body) (exit height other n : Nat)
    (hexit : exit ≠ 0) (hn : n ≤ height) :
    crun (clearBlock b exit) n (entryState b height other) ≠
      some (clearedState b exit other) := by
  rw [clear_prefix b exit height other n hn]
  intro he
  have hs := Option.some.inj he
  have hpc := congrArg CState.pc hs
  cases b <;> simp [entryState, clearedState] at hpc
  · exact hexit hpc.symm
  · exact hexit hpc.symm

/-- Exact completion: source clear is simulated in `height + 1` target steps. -/
theorem clear_completes (b : Body) (exit height other : Nat) :
    crun (clearBlock b exit) (height + 1) (entryState b height other) =
      some (clearedState b exit other) := by
  induction height with
  | zero =>
      unfold crun
      rw [clear_one_zero]
      rfl
  | succ h ih =>
      unfold crun
      rw [clear_one_positive]
      exact ih

/-! ## 2. The atomic source/target relation -/

structure SourceState where
  a : Nat
  b : Nat
deriving DecidableEq

def sourceClear : Body → SourceState → SourceState
  | false, s => ⟨0, s.b⟩
  | true, s => ⟨s.a, 0⟩

def enter (b : Body) (s : SourceState) : CState :=
  if b then entryState true s.b s.a else entryState false s.a s.b

def leave (exit : Nat) (s : SourceState) : CState := ⟨exit, s.a, s.b⟩

/-- The macro boundary agrees exactly with one atomic source transition. -/
theorem clear_simulates_source (b : Body) (exit : Nat) (s : SourceState) :
    crun (clearBlock b exit) (get (enter b s) b + 1) (enter b s) =
      some (leave exit (sourceClear b s)) := by
  cases b with
  | false =>
      rcases s with ⟨a, other⟩
      simpa [enter, get, sourceClear, leave, entryState, clearedState] using
        clear_completes false exit a other
  | true =>
      rcases s with ⟨other, height⟩
      simpa [enter, get, sourceClear, leave, entryState, clearedState] using
        clear_completes true exit height other

/-! ## 3. Sequential composition: both bodies -/

/-- Clear A at address 0, then clear B at address 1, then exit to 2. -/
def clearBoth : Program := [downCode false 0 1, downCode true 1 2]

theorem clearA_phase : ∀ a b,
    crun clearBoth (a + 1) ⟨0, a, b⟩ = some ⟨1, 0, b⟩ := by
  intro a
  induction a with
  | zero => intro b; rfl
  | succ a ih =>
      intro b
      unfold crun
      change crun clearBoth (a + 1) ⟨0, a, b⟩ = some ⟨1, 0, b⟩
      exact ih b

theorem clearB_phase : ∀ a b,
    crun clearBoth (b + 1) ⟨1, a, b⟩ = some ⟨2, a, 0⟩ := by
  intro a b
  induction b with
  | zero => rfl
  | succ b ih =>
      unfold crun
      change crun clearBoth (b + 1) ⟨1, a, b⟩ = some ⟨2, a, 0⟩
      exact ih

theorem crun_add (p : Program) (m n : Nat) (s : CState) :
    crun p (m + n) s =
      match crun p m s with
      | none => none
      | some s' => crun p n s' := by
  induction m generalizing s with
  | zero => simp [crun]
  | succ m ih =>
      simp only [Nat.succ_add]
      change
        (match cstep p s with
          | none => none
          | some s' => crun p (m + n) s') =
        match (match cstep p s with
          | none => none
          | some s' => crun p m s') with
        | none => none
        | some s' => crun p n s'
      cases cstep p s with
      | none => rfl
      | some s' =>
          simp only
          exact ih s'

/-- Two atomic clears compose, and the exact hidden work is `a + b + 2`. -/
theorem clear_both_completes (a b : Nat) :
    crun clearBoth (a + b + 2) ⟨0, a, b⟩ = some ⟨2, 0, 0⟩ := by
  rw [show a + b + 2 = (a + 1) + (b + 1) by omega]
  rw [crun_add, clearA_phase]
  simp only
  rw [clearB_phase]

/-! ## 4. Red controls -/

/-- One primitive relay step cannot pretend to be the atomic clear at height two. -/
theorem one_step_is_not_atomic_clear :
    crun (clearBlock false 1) 1 (entryState false 2 0) ≠
      some (clearedState false 1 0) := by decide

/-- No fixed number of relay steps clears every input: choose a height above the bound. -/
theorem no_fixed_step_bound (k : Nat) :
    crun (clearBlock false 1) k (entryState false (k + 1) 0) ≠
      some (clearedState false 1 0) := by
  have hp := clear_prefix false 1 (k + 1) 0 k (by omega)
  rw [show k + 1 - k = 1 by omega] at hp
  rw [hp]
  decide

/-- The code remains one instruction even though its required run is unbounded. -/
theorem constant_code_unbounded_execution :
    (clearBlock false 1).length = 1 ∧
    ∀ k, crun (clearBlock false 1) k (entryState false (k + 1) 0) ≠
      some (clearedState false 1 0) :=
  ⟨rfl, no_fixed_step_bound⟩

/-! ## Certificate -/

theorem stuttering_bridge_certificate :
    (∀ b exit height other,
      crun (clearBlock b exit) (height + 1) (entryState b height other) =
        some (clearedState b exit other)) ∧
    (∀ b exit s,
      crun (clearBlock b exit) (get (enter b s) b + 1) (enter b s) =
        some (leave exit (sourceClear b s))) ∧
    (∀ a b, crun clearBoth (a + b + 2) ⟨0, a, b⟩ = some ⟨2, 0, 0⟩) ∧
    (∀ k, crun (clearBlock false 1) k (entryState false (k + 1) 0) ≠
      some (clearedState false 1 0)) :=
  ⟨clear_completes, clear_simulates_source, clear_both_completes, no_fixed_step_bound⟩

#print axioms clear_one_positive
#print axioms clear_one_zero
#print axioms clear_prefix
#print axioms clear_not_finished_early
#print axioms clear_completes
#print axioms clear_simulates_source
#print axioms clearA_phase
#print axioms clearB_phase
#print axioms crun_add
#print axioms clear_both_completes
#print axioms one_step_is_not_atomic_clear
#print axioms no_fixed_step_bound
#print axioms constant_code_unbounded_execution
#print axioms stuttering_bridge_certificate

end FoundationStoneTest16N
