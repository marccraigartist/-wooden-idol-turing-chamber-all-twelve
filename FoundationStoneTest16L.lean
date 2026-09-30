import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

/-!
# THE TURING BRIDGE — FOUNDATION STONE TEST 16L

Imports Mathlib's machine-checked halting theorem.

This test connects three layers without identifying them by assertion:

1. A two-body helix machine carries two unbounded heights and two twelve-seat
   shadows.  Forgetting the clocks commutes with every step and every run.
2. Therefore a helix instance halts exactly when its two-counter shadow halts.
3. Mathlib proves that the universal partial-recursive halting predicate is not
   computable.  A `MinskyBridge` is the exact remaining port obligation: a
   COMPUTABLE compiler from Mathlib programs to the encoded two-counter
   programs below, with a proof that it preserves halting.

For every such bridge Lean proves a computable many-one reduction from the
standard halting problem to closed two-body-helix halting, and hence proves
that closed helix halting is not computable.

What is and is not green:

* GREEN: counter/helix equivalence, the many-one transfer, the conditional
  noncomputability theorem, and halting/non-halting controls.
* OPEN: construction of an inhabitant of `MinskyBridge`.  That is precisely
  the Minsky two-counter universality port.  It is no longer hidden in prose.

The result concerns the FAMILY of encoded programs.  Every fixed finite run is
still exactly computable; the stopper halts and the climber continues forever.
-/

namespace FoundationStoneTest16L

/-! ## 1. An effectively coded relay language -/

/-- `false` is body A and `true` is body B. -/
abbrev Body := Bool

/--
An instruction is a primitive tuple `(tag, body, next, ground)`.

* tag 0 (and every tag other than 1 or 2): stop;
* tag 1: increment `body`, then jump to `next`;
* tag 2: if `body` is zero jump to `ground`, otherwise decrement it and jump
  to `next`.

Using tuples rather than an opaque instruction type makes the program syntax
an ordinary `Primcodable` type, so a compiler into it can genuinely be required
to be computable.
-/
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

/-! ## 2. The two-body helix and its counter shadow -/

abbrev Seat := Fin 12

def forward (k : Seat) : Seat := k + 1
def back (k : Seat) : Seat := k + 11

structure BodyState where
  height : Nat
  seat : Seat
deriving DecidableEq

structure HState where
  pc : Nat
  bodyA : BodyState
  bodyB : BodyState
deriving DecidableEq

def bget (h : HState) : Body → BodyState
  | false => h.bodyA
  | true => h.bodyB

def bset (h : HState) (pc : Nat) : Body → BodyState → HState
  | false, v => ⟨pc, v, h.bodyB⟩
  | true, v => ⟨pc, h.bodyA, v⟩

def climb (s : BodyState) : BodyState := ⟨s.height + 1, forward s.seat⟩
def descend (s : BodyState) : BodyState := ⟨s.height - 1, back s.seat⟩

def hstep (p : Program) (h : HState) : Option HState :=
  match fetch p h.pc with
  | .up b nx => some (bset h nx b (climb (bget h b)))
  | .down b nx gr =>
      if (bget h b).height = 0 then some { h with pc := gr }
      else some (bset h nx b (descend (bget h b)))
  | .stop => none

structure CState where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq

def cget (s : CState) : Body → Nat
  | false => s.a
  | true => s.b

def cset (s : CState) (pc : Nat) : Body → Nat → CState
  | false, v => ⟨pc, v, s.b⟩
  | true, v => ⟨pc, s.a, v⟩

def cstep (p : Program) (s : CState) : Option CState :=
  match fetch p s.pc with
  | .up b nx => some (cset s nx b (cget s b + 1))
  | .down b nx gr =>
      if cget s b = 0 then some { s with pc := gr }
      else some (cset s nx b (cget s b - 1))
  | .stop => none

def forget (h : HState) : CState := ⟨h.pc, h.bodyA.height, h.bodyB.height⟩

theorem cget_forget (h : HState) (b : Body) :
    cget (forget h) b = (bget h b).height := by
  cases b <;> rfl

theorem forget_bset (h : HState) (pc : Nat) (b : Body) (v : BodyState) :
    forget (bset h pc b v) = cset (forget h) pc b v.height := by
  cases b <;> rfl

/-- The clocks contribute no hidden branch: forgetting commutes with one step. -/
theorem step_forgets_to_counter (p : Program) (h : HState) :
    (hstep p h).map forget = cstep p (forget h) := by
  unfold hstep cstep
  show _ = (match fetch p h.pc with
    | .up b nx => some (cset (forget h) nx b (cget (forget h) b + 1))
    | .down b nx gr =>
        if cget (forget h) b = 0 then some { forget h with pc := gr }
        else some (cset (forget h) nx b (cget (forget h) b - 1))
    | .stop => none)
  cases fetch p h.pc with
  | up b nx =>
      simp only [Option.map_some, forget_bset, cget_forget, climb]
  | down b nx gr =>
      simp only [cget_forget]
      split
      · rfl
      · simp only [Option.map_some, forget_bset, descend]
  | stop => rfl

def hrun (p : Program) : Nat → HState → Option HState
  | 0, h => some h
  | n + 1, h =>
      match hstep p h with
      | none => none
      | some h' => hrun p n h'

def crun (p : Program) : Nat → CState → Option CState
  | 0, s => some s
  | n + 1, s =>
      match cstep p s with
      | none => none
      | some s' => crun p n s'

/-- Forgetting commutes with every finite run. -/
theorem run_forgets_to_counter (p : Program) :
    ∀ (n : Nat) (h : HState), (hrun p n h).map forget = crun p n (forget h) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      have hs := step_forgets_to_counter p h
      unfold hrun crun
      cases e : hstep p h with
      | none =>
          rw [e] at hs
          simp only [Option.map_none] at hs
          rw [← hs]
          rfl
      | some h' =>
          rw [e] at hs
          simp only [Option.map_some] at hs
          rw [← hs]
          exact ih h'

def HelixHalts (p : Program) (h : HState) : Prop :=
  ∃ n, hrun p n h = none

def CounterHalts (p : Program) (s : CState) : Prop :=
  ∃ n, crun p n s = none

/-- Halting is neither gained nor lost by the clock projection. -/
theorem helix_halts_iff_counter_halts (p : Program) (h : HState) :
    HelixHalts p h ↔ CounterHalts p (forget h) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hr := run_forgets_to_counter p n h
    rw [hn] at hr
    simpa using hr.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hr := run_forgets_to_counter p n h
    rw [hn] at hr
    cases e : hrun p n h with
    | none => rfl
    | some h' =>
        rw [e] at hr
        simp at hr

def seatOfHeight (n : Nat) : Seat := ⟨n % 12, Nat.mod_lt _ (by decide)⟩

def liftCounter (s : CState) : HState :=
  ⟨s.pc, ⟨s.a, seatOfHeight s.a⟩, ⟨s.b, seatOfHeight s.b⟩⟩

theorem forget_liftCounter (s : CState) : forget (liftCounter s) = s := rfl

theorem lifted_helix_halts_iff_counter_halts (p : Program) (s : CState) :
    HelixHalts p (liftCounter s) ↔ CounterHalts p s := by
  simpa [forget_liftCounter] using helix_halts_iff_counter_halts p (liftCounter s)

def counterStart : CState := ⟨0, 0, 0⟩
def helixStart : HState := liftCounter counterStart

def ClosedCounterHalts (p : Program) : Prop := CounterHalts p counterStart
def ClosedHelixHalts (p : Program) : Prop := HelixHalts p helixStart

theorem closed_helix_halts_iff_counter_halts (p : Program) :
    ClosedHelixHalts p ↔ ClosedCounterHalts p :=
  lifted_helix_halts_iff_counter_halts p counterStart

/-! ## 3. Red controls: finite execution is exact, and programs differ -/

def stopper : Program := [stopCode]
def climber : Program := [upCode false 0]

theorem stopper_halts : ClosedHelixHalts stopper := ⟨1, rfl⟩

theorem climber_step (h : HState) (hpc : h.pc = 0) :
    hstep climber h = some (bset h 0 false (climb h.bodyA)) := by
  unfold hstep fetch climber decodeInstr stopCode upCode
  rw [hpc]
  rfl

theorem climber_runs (n : Nat) (h : HState) (hpc : h.pc = 0) :
    hrun climber n h ≠ none := by
  induction n generalizing h with
  | zero => simp [hrun]
  | succ n ih =>
      unfold hrun
      rw [climber_step h hpc]
      exact ih _ rfl

theorem climber_does_not_halt : ¬ ClosedHelixHalts climber := by
  rintro ⟨n, hn⟩
  exact climber_runs n helixStart rfl hn

theorem controls_separate_halting :
    ClosedHelixHalts stopper ∧ ¬ ClosedHelixHalts climber :=
  ⟨stopper_halts, climber_does_not_halt⟩

/-! ## 4. The exact Minsky port obligation -/

open Nat.Partrec (Code)

def SourceHalts (input : Nat) (c : Code) : Prop :=
  (Nat.Partrec.Code.eval c input).Dom

/--
An inhabitant is not a citation: it must supply executable program syntax, a
Mathlib-computable compiler into that syntax, and a proof that the compiled
two-counter program halts exactly when the source program halts.
-/
structure MinskyBridge (input : Nat) where
  compile : Code → Program
  compile_computable : Computable compile
  correct : ∀ c, SourceHalts input c ↔ ClosedCounterHalts (compile c)

/-- The standard halting problem many-one reduces to closed helix halting. -/
theorem source_reduces_to_closed_helix (input : Nat) (B : MinskyBridge input) :
    SourceHalts input ≤₀ ClosedHelixHalts := by
  refine ⟨B.compile, B.compile_computable, fun c => ?_⟩
  rw [B.correct c]
  exact (closed_helix_halts_iff_counter_halts (B.compile c)).symm

/-- The promised Turing-strength conclusion: once the explicit compiler is
constructed, no computable predicate decides halting for all closed helix
programs. -/
theorem closed_helix_halting_not_computable (input : Nat) (B : MinskyBridge input) :
    ¬ ComputablePred ClosedHelixHalts := by
  intro hhelix
  have hsource : ComputablePred (SourceHalts input) :=
    ComputablePred.computable_of_manyOneReducible
      (source_reduces_to_closed_helix input B) hhelix
  exact ComputablePred.halting_problem input hsource

/-- In the repaired-B1 style: no Mathlib-computable Boolean answer function
can correctly decide the whole closed helix family. -/
def DecidesClosedHelixHalting (answer : Program → Bool) : Prop :=
  ∀ p, answer p = true ↔ ClosedHelixHalts p

theorem no_computable_boolean_helix_decider (input : Nat) (B : MinskyBridge input)
    (answer : Program → Bool) (hcomp : Computable answer) :
    ¬ DecidesClosedHelixHalting answer := by
  intro hdec
  apply closed_helix_halting_not_computable input B
  have hanswer : ComputablePred (fun p => answer p = true) := by
    refine ⟨inferInstance, ?_⟩
    simpa using hcomp
  exact hanswer.of_eq hdec

/-! ## 5. Certificate -/

theorem turing_bridge_certificate (input : Nat) (B : MinskyBridge input) :
    (∀ p s, HelixHalts p (liftCounter s) ↔ CounterHalts p s) ∧
    ClosedHelixHalts stopper ∧
    ¬ ClosedHelixHalts climber ∧
    SourceHalts input ≤₀ ClosedHelixHalts ∧
    ¬ ComputablePred ClosedHelixHalts :=
  ⟨lifted_helix_halts_iff_counter_halts,
   stopper_halts,
   climber_does_not_halt,
   source_reduces_to_closed_helix input B,
   closed_helix_halting_not_computable input B⟩

#print axioms step_forgets_to_counter
#print axioms run_forgets_to_counter
#print axioms helix_halts_iff_counter_halts
#print axioms lifted_helix_halts_iff_counter_halts
#print axioms stopper_halts
#print axioms climber_does_not_halt
#print axioms controls_separate_halting
#print axioms source_reduces_to_closed_helix
#print axioms closed_helix_halting_not_computable
#print axioms no_computable_boolean_helix_decider
#print axioms turing_bridge_certificate

end FoundationStoneTest16L
