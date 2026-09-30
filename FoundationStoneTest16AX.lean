import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AX: RELOCATABLE TWO-COUNTER BLOCKS

Lean 4.35.0-rc2 / pinned Mathlib.

Verified arithmetic blocks are useful only if their local labels can be moved
into a common finite program without changing execution.  This file proves
that any injective relabelling preserving the instruction table transports
one step, every bounded run, reachability, and halting exactly.

The theorem is generic over label types and therefore applies uniformly to
the division, multiplication and transfer blocks.
-/

namespace FoundationStoneTest16AX

abbrev Body := Bool

inductive Instr (L : Type)
  | inc (body : Body) (next : L)
  | dec (body : Body) (positive zero : L)
  | halt
deriving Repr

structure State (L : Type) where
  pc : L
  a : Nat
  b : Nat
deriving Repr

def Instr.map {L K : Type} (f : L → K) : Instr L → Instr K
  | .inc body next => .inc body (f next)
  | .dec body pos zero => .dec body (f pos) (f zero)
  | .halt => .halt

def State.map {L K : Type} (f : L → K) (s : State L) : State K :=
  ⟨f s.pc, s.a, s.b⟩

def get {L : Type} (s : State L) (body : Body) : Nat := if body then s.b else s.a

def set {L : Type} (s : State L) (pc : L) (body : Body) (value : Nat) : State L :=
  if body then ⟨pc, s.a, value⟩ else ⟨pc, value, s.b⟩

def step {L : Type} (P : L → Instr L) (s : State L) : Option (State L) :=
  match P s.pc with
  | .halt => none
  | .inc body next => some (set s next body (get s body + 1))
  | .dec body pos zero =>
      if get s body = 0 then some { s with pc := zero }
      else some (set s pos body (get s body - 1))

def run {L : Type} (P : L → Instr L) : Nat → State L → Option (State L)
  | 0, s => some s
  | n + 1, s =>
      match step P s with
      | none => none
      | some s' => run P n s'

/-- A target table implements a source table under label embedding `f`. -/
def Implements {L K : Type} (f : L → K) (P : L → Instr L)
    (Q : K → Instr K) : Prop :=
  ∀ l, Q (f l) = (P l).map f

theorem map_get {L K : Type} (f : L → K) (s : State L) (body : Body) :
    get (s.map f) body = get s body := by
  cases body <;> rfl

theorem map_set {L K : Type} (f : L → K) (s : State L)
    (pc : L) (body : Body) (value : Nat) :
    (set s pc body value).map f = set (s.map f) (f pc) body value := by
  cases body <;> rfl

theorem step_relocates {L K : Type} (f : L → K)
    (P : L → Instr L) (Q : K → Instr K) (h : Implements f P Q)
    (s : State L) :
    step Q (s.map f) = (step P s).map (State.map f) := by
  unfold step
  simp only [State.map]
  rw [h s.pc]
  cases hi : P s.pc with
  | halt => rfl
  | inc body next =>
      cases body <;> simp [Instr.map, State.map, get, set]
  | dec body pos zero =>
      cases body with
      | false =>
          by_cases hz : s.a = 0 <;>
            simp [Instr.map, State.map, get, set, hz]
      | true =>
          by_cases hz : s.b = 0 <;>
            simp [Instr.map, State.map, get, set, hz]

theorem run_relocates {L K : Type} (f : L → K)
    (P : L → Instr L) (Q : K → Instr K) (h : Implements f P Q) :
    ∀ n s, run Q n (s.map f) = (run P n s).map (State.map f) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      unfold run
      rw [step_relocates f P Q h]
      cases hs : step P s with
      | none => rfl
      | some s' =>
          simp only [Option.map_some]
          exact ih s'

def Terminates {L : Type} (P : L → Instr L) (s : State L) : Prop :=
  (StateTransition.eval (step P) s).Dom

theorem relocation_respects {L K : Type} (f : L → K)
    (P : L → Instr L) (Q : K → Instr K) (h : Implements f P Q) :
    StateTransition.Respects (step P) (step Q)
      (fun s t => s.map f = t) := by
  intro s t hst
  subst t
  cases hs : step P s with
  | none =>
      have hstep := step_relocates f P Q h s
      calc
        step Q (s.map f) = (step P s).map (State.map f) := hstep
        _ = none := by rw [hs]; rfl
  | some s' =>
      refine ⟨s'.map f, rfl, ?_⟩
      apply Relation.TransGen.single
      have hstep := step_relocates f P Q h s
      calc
        step Q (s.map f) = (step P s).map (State.map f) := hstep
        _ = some (s'.map f) := by rw [hs]; rfl

theorem termination_relocates {L K : Type} (f : L → K)
    (P : L → Instr L) (Q : K → Instr K) (h : Implements f P Q)
    (s : State L) :
    Terminates P s ↔ Terminates Q (s.map f) := by
  unfold Terminates
  exact (StateTransition.tr_eval_dom (relocation_respects f P Q h) rfl).symm

/-! A two-instruction continuation bridge preserves both counters while
jumping from an arbitrary exit to an arbitrary next block. -/

inductive BridgeLabel (K : Type)
  | entry
  | restore
  | next (k : K)
deriving Repr

def bridge (target : K) : BridgeLabel K → Instr (BridgeLabel K)
  | .entry => .inc false .restore
  | .restore => .dec false (.next target) (.next target)
  | .next _ => .halt

theorem bridge_preserves_counters (target : K) (a b : Nat) :
    run (bridge target) 2 ⟨BridgeLabel.entry, a, b⟩ =
      some ⟨BridgeLabel.next target, a, b⟩ := by
  simp [run, step, bridge, get, set]

/-! Red control: a non-injective relabelling can collapse distinct control
states, so injection must be checked when allocating global labels. -/

def collapse : Bool → Unit := fun _ => ()

theorem collapse_not_injective : ¬ Function.Injective collapse := by
  intro h
  have := h (a₁ := false) (a₂ := true) rfl
  contradiction

theorem turing_chamber_16AX_certificate :
    (∀ {L K : Type} (f : L → K) (P : L → Instr L) (Q : K → Instr K),
      Implements f P Q → ∀ n s,
        run Q n (s.map f) = (run P n s).map (State.map f)) ∧
    (∀ (target : Nat) a b,
      run (bridge target) 2 ⟨BridgeLabel.entry, a, b⟩ =
        some ⟨BridgeLabel.next target, a, b⟩) ∧
    ¬ Function.Injective collapse :=
  ⟨fun f P Q h n s => run_relocates f P Q h n s,
   bridge_preserves_counters, collapse_not_injective⟩

#print axioms step_relocates
#print axioms run_relocates
#print axioms relocation_respects
#print axioms termination_relocates
#print axioms bridge_preserves_counters
#print axioms turing_chamber_16AX_certificate

end FoundationStoneTest16AX
