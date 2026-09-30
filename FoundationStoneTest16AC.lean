import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AC: THE RELAY ENTERS THE HELIX

Mathlib / Lean 4.35.0-rc2.

Test 16AB gives the exact operational compilation from the standard two-register
Minsky machine (MM2) into the Wooden Idol relay language.  This file closes the
other side of that doorway: the relay is lifted into the two-body helix.

Lean certifies:

1. Forgetting the two clock faces after one helix step gives exactly the relay's
   two-counter step.
2. The same is true after every finite number of steps.
3. Therefore relay halting and helix halting are equivalent from every state.
4. The canonical lift displays each counter modulo twelve, and the shadow is
   preserved by every reached helix state.
5. Red control: after twelve increments the clock is home but the height is 12.
   Clock return is not machine-state return.

This is a semantics theorem, not yet Minsky's universality theorem.  Together
with 16AB it says that a standard MM2 computation has an exact helix execution.
-/

namespace FoundationStoneTest16AC

abbrev Seat := Fin 12

def forward (k : Seat) : Seat := k + 1
def back (k : Seat) : Seat := k + 11

inductive Body
  | A
  | B
deriving DecidableEq, Repr

inductive Instr
  | inc (body : Body) (next : Nat)
  | dec (body : Body) (next zero : Nat)
  | halt
deriving DecidableEq, Repr

abbrev Program := List Instr

def fetch (p : Program) (pc : Nat) : Instr := (p[pc]?).getD .halt

/-! ## The relay counters -/

structure CState where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq, Repr

def cget (s : CState) : Body → Nat
  | .A => s.a
  | .B => s.b

def cset (s : CState) (pc : Nat) : Body → Nat → CState
  | .A, value => ⟨pc, value, s.b⟩
  | .B, value => ⟨pc, s.a, value⟩

def cstep (p : Program) (s : CState) : Option CState :=
  match fetch p s.pc with
  | .inc body next => some (cset s next body (cget s body + 1))
  | .dec body next zero =>
      if cget s body = 0 then some { s with pc := zero }
      else some (cset s next body (cget s body - 1))
  | .halt => none

def crun (p : Program) : Nat → CState → Option CState
  | 0, s => some s
  | n + 1, s =>
      match cstep p s with
      | none => none
      | some s' => crun p n s'

/-! ## The two-body helix -/

structure BodyState where
  height : Nat
  seat : Seat
deriving DecidableEq, Repr

structure HState where
  pc : Nat
  bodyA : BodyState
  bodyB : BodyState
deriving DecidableEq, Repr

def climb (s : BodyState) : BodyState := ⟨s.height + 1, forward s.seat⟩
def descend (s : BodyState) : BodyState := ⟨s.height - 1, back s.seat⟩

def bget (h : HState) : Body → BodyState
  | .A => h.bodyA
  | .B => h.bodyB

def bset (h : HState) (pc : Nat) : Body → BodyState → HState
  | .A, value => ⟨pc, value, h.bodyB⟩
  | .B, value => ⟨pc, h.bodyA, value⟩

def hstep (p : Program) (h : HState) : Option HState :=
  match fetch p h.pc with
  | .inc body next => some (bset h next body (climb (bget h body)))
  | .dec body next zero =>
      if (bget h body).height = 0 then some { h with pc := zero }
      else some (bset h next body (descend (bget h body)))
  | .halt => none

def hrun (p : Program) : Nat → HState → Option HState
  | 0, h => some h
  | n + 1, h =>
      match hstep p h with
      | none => none
      | some h' => hrun p n h'

def forget (h : HState) : CState := ⟨h.pc, h.bodyA.height, h.bodyB.height⟩

theorem cget_forget (h : HState) (body : Body) :
    cget (forget h) body = (bget h body).height := by
  cases body <;> rfl

theorem forget_bset (h : HState) (pc : Nat) (body : Body) (value : BodyState) :
    forget (bset h pc body value) = cset (forget h) pc body value.height := by
  cases body <;> rfl

/-- 1. Forgetting the clocks commutes with one operational step. -/
theorem step_forgets_exactly (p : Program) (h : HState) :
    (hstep p h).map forget = cstep p (forget h) := by
  unfold hstep cstep
  show _ = (match fetch p h.pc with
    | .inc body next => some (cset (forget h) next body (cget (forget h) body + 1))
    | .dec body next zero =>
        if cget (forget h) body = 0 then some { forget h with pc := zero }
        else some (cset (forget h) next body (cget (forget h) body - 1))
    | .halt => none)
  cases fetch p h.pc with
  | inc body next =>
      simp only [Option.map_some, forget_bset, cget_forget, climb]
  | dec body next zero =>
      simp only [cget_forget]
      split
      · rfl
      · simp only [Option.map_some, forget_bset, descend]
  | halt => rfl

/-- 2. Forgetting the clocks commutes with every bounded run. -/
theorem run_forgets_exactly (p : Program) :
    ∀ n h, (hrun p n h).map forget = crun p n (forget h) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      have hs := step_forgets_exactly p h
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

def CounterHalts (p : Program) (s : CState) : Prop := ∃ n, crun p n s = none
def HelixHalts (p : Program) (h : HState) : Prop := ∃ n, hrun p n h = none

/-- 3. The clocks add no halting power and remove none. -/
theorem halting_is_exactly_preserved (p : Program) (h : HState) :
    HelixHalts p h ↔ CounterHalts p (forget h) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hcomm := run_forgets_exactly p n h
    rw [hn] at hcomm
    simpa using hcomm.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hcomm := run_forgets_exactly p n h
    rw [hn] at hcomm
    cases e : hrun p n h with
    | none => rfl
    | some h' => rw [e] at hcomm; simp at hcomm

/-! ## Canonical lifts and the twelve-seat shadow -/

def seatOf (n : Nat) : Seat := ⟨n % 12, Nat.mod_lt _ (by decide)⟩

def lift (s : CState) : HState :=
  ⟨s.pc, ⟨s.a, seatOf s.a⟩, ⟨s.b, seatOf s.b⟩⟩

theorem forget_lift (s : CState) : forget (lift s) = s := rfl

def Shadow (s : BodyState) : Prop := s.seat.val = s.height % 12
def BothShadow (h : HState) : Prop := Shadow h.bodyA ∧ Shadow h.bodyB

theorem lift_has_shadow (s : CState) : BothShadow (lift s) := ⟨rfl, rfl⟩

theorem climb_keeps_shadow (s : BodyState) (hs : Shadow s) : Shadow (climb s) := by
  unfold Shadow climb forward at *
  rw [Fin.val_add]
  simp only [Fin.val_one]
  omega

theorem descend_keeps_shadow (s : BodyState) (hs : Shadow s) (hpos : s.height ≠ 0) :
    Shadow (descend s) := by
  unfold Shadow descend back at *
  dsimp only
  rw [Fin.val_add]
  have h11 : (11 : Seat).val = 11 := rfl
  rw [h11]
  omega

theorem step_keeps_shadow (p : Program) (h h' : HState) (hs : BothShadow h)
    (e : hstep p h = some h') : BothShadow h' := by
  unfold hstep at e
  cases hf : fetch p h.pc with
  | inc body next =>
      rw [hf] at e
      cases body <;> (simp only [Option.some.injEq] at e; subst e) <;>
        exact ⟨by first | exact climb_keeps_shadow _ hs.1 | exact hs.1,
               by first | exact climb_keeps_shadow _ hs.2 | exact hs.2⟩
  | dec body next zero =>
      rw [hf] at e
      simp only at e
      split at e
      · simp only [Option.some.injEq] at e
        subst e
        exact hs
      · rename_i hne
        cases body <;> (simp only [Option.some.injEq] at e; subst e) <;>
          exact ⟨by first | exact descend_keeps_shadow _ hs.1 hne | exact hs.1,
                 by first | exact descend_keeps_shadow _ hs.2 hne | exact hs.2⟩
  | halt => rw [hf] at e; simp at e

theorem run_keeps_shadow (p : Program) :
    ∀ n h h', BothShadow h → hrun p n h = some h' → BothShadow h' := by
  intro n
  induction n with
  | zero =>
      intro h h' hs e
      simp only [hrun, Option.some.injEq] at e
      subst e
      exact hs
  | succ n ih =>
      intro h h' hs e
      unfold hrun at e
      cases e1 : hstep p h with
      | none => rw [e1] at e; simp at e
      | some h1 =>
          rw [e1] at e
          exact ih h1 h' (step_keeps_shadow p h h1 hs e1) e

/-! ## Red control: the circle closes while the helix does not -/

def zero : CState := ⟨0, 0, 0⟩
def climber : Program := [.inc .A 0]

theorem twelve_climbs_clock_home_height_twelve :
    (hrun climber 12 (lift zero)).map
      (fun h => (h.bodyA.seat, h.bodyA.height)) = some (0, 12) := by
  decide

theorem clock_home_does_not_mean_state_home :
    (hrun climber 12 (lift zero)).map (fun h => h.bodyA.seat) = some 0 ∧
    (hrun climber 12 (lift zero)).map (fun h => h.bodyA.height) = some 12 ∧
    hrun climber 12 (lift zero) ≠ some (lift zero) := by
  decide

theorem turing_chamber_16AC :
    (∀ p h, (hstep p h).map forget = cstep p (forget h)) ∧
    (∀ p n h, (hrun p n h).map forget = crun p n (forget h)) ∧
    (∀ p h, HelixHalts p h ↔ CounterHalts p (forget h)) ∧
    (∀ s, BothShadow (lift s)) ∧
    hrun climber 12 (lift zero) ≠ some (lift zero) :=
  ⟨step_forgets_exactly, run_forgets_exactly, halting_is_exactly_preserved,
   lift_has_shadow, clock_home_does_not_mean_state_home.2.2⟩

#print axioms step_forgets_exactly
#print axioms run_forgets_exactly
#print axioms halting_is_exactly_preserved
#print axioms run_keeps_shadow
#print axioms twelve_climbs_clock_home_height_twelve
#print axioms clock_home_does_not_mean_state_home
#print axioms turing_chamber_16AC

end FoundationStoneTest16AC
