import Mathlib.Computability.Reduce

/-!
# THE TURING CHAMBER — TEST 16AF: THE EFFECTIVE HELIX DOOR

Lean 4.35.0-rc2 / Mathlib.

Test 16AC proved that forgetting the clock faces commutes with every relay run.
Test 16AE then required more: the translation used in an undecidability argument
must itself be computable.  This file supplies that missing certificate for the
relay-to-helix half of the chamber.

To prevent computability being hidden inside a custom encoding, instructions use
only Mathlib `Primcodable` components:

    Unit ⊕ ((Bool × Nat) ⊕ (Bool × Nat × Nat)).

These are respectively HALT, INC, and DEC/zero-branch.  `false` is body A and
`true` is body B.  A problem instance is a program plus two initial heights.

Lean certifies:

1. forgetting clocks commutes with one step and every finite run;
2. counter halting and helix halting agree on every encoded instance;
3. the identity translation between those two questions is computable;
4. hence relay halting is computably many-one reducible to helix halting;
5. any noncomputability theorem for relay halting transfers to the helix;
6. red control: twelve climbs return the clock to B12 but not the helix height.

No universality theorem is claimed here.  This closes the EFFECTIVE BACK DOOR.
The remaining front door is the computable partial-recursive/Turing-to-MM2
compiler isolated by 16AE, followed by the effective certification of 16AB.
-/

namespace FoundationStoneTest16AF

abbrev Body := Bool
abbrev Seat := Fin 12

/-- `inl ()` = halt; `inr (inl (body,next))` = increment;
`inr (inr (body,next,zero))` = decrement/zero-test. -/
abbrev Instr := Unit ⊕ ((Body × Nat) ⊕ (Body × Nat × Nat))
abbrev Program := List Instr
abbrev Problem := Program × (Nat × Nat)

def halt : Instr := .inl ()
def inc (body : Body) (next : Nat) : Instr := .inr (.inl (body, next))
def dec (body : Body) (next zero : Nat) : Instr := .inr (.inr (body, next, zero))

def fetch (p : Program) (pc : Nat) : Instr := (p[pc]?).getD halt

/-! ## The two-counter relay -/

structure CState where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq, Repr

def cget (s : CState) (body : Body) : Nat := if body then s.b else s.a

def cset (s : CState) (pc : Nat) (body : Body) (value : Nat) : CState :=
  if body then ⟨pc, s.a, value⟩ else ⟨pc, value, s.b⟩

def cstep (p : Program) (s : CState) : Option CState :=
  match fetch p s.pc with
  | .inl _ => none
  | .inr (.inl (body, next)) =>
      some (cset s next body (cget s body + 1))
  | .inr (.inr (body, next, zero)) =>
      if cget s body = 0 then some { s with pc := zero }
      else some (cset s next body (cget s body - 1))

def crun (p : Program) : Nat → CState → Option CState
  | 0, s => some s
  | n + 1, s =>
      match cstep p s with
      | none => none
      | some s' => crun p n s'

/-! ## The two-body helix -/

def forward (k : Seat) : Seat := k + 1
def back (k : Seat) : Seat := k + 11

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

def bget (h : HState) (body : Body) : BodyState := if body then h.bodyB else h.bodyA

def bset (h : HState) (pc : Nat) (body : Body) (value : BodyState) : HState :=
  if body then ⟨pc, h.bodyA, value⟩ else ⟨pc, value, h.bodyB⟩

def hstep (p : Program) (h : HState) : Option HState :=
  match fetch p h.pc with
  | .inl _ => none
  | .inr (.inl (body, next)) =>
      some (bset h next body (climb (bget h body)))
  | .inr (.inr (body, next, zero)) =>
      if (bget h body).height = 0 then some { h with pc := zero }
      else some (bset h next body (descend (bget h body)))

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

/-- 1a. Forgetting clocks commutes with a single step. -/
theorem step_forgets_exactly (p : Program) (h : HState) :
    (hstep p h).map forget = cstep p (forget h) := by
  unfold hstep cstep
  show _ = (match fetch p h.pc with
    | .inl _ => none
    | .inr (.inl (body, next)) =>
        some (cset (forget h) next body (cget (forget h) body + 1))
    | .inr (.inr (body, next, zero)) =>
        if cget (forget h) body = 0 then some { forget h with pc := zero }
        else some (cset (forget h) next body (cget (forget h) body - 1)))
  cases fetch p h.pc with
  | inl u => rfl
  | inr command =>
      cases command with
      | inl payload =>
          obtain ⟨body, next⟩ := payload
          simp only [Option.map_some, forget_bset, cget_forget, climb]
      | inr payload =>
          obtain ⟨body, next, zero⟩ := payload
          simp only [cget_forget]
          split
          · rfl
          · simp only [Option.map_some, forget_bset, descend]

/-- 1b. Forgetting clocks commutes with every bounded run. -/
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

/-! ## The computable problem translation -/

def seatOf (n : Nat) : Seat := ⟨n % 12, Nat.mod_lt _ (by decide)⟩

def liftState (s : CState) : HState :=
  ⟨s.pc, ⟨s.a, seatOf s.a⟩, ⟨s.b, seatOf s.b⟩⟩

theorem forget_liftState (s : CState) : forget (liftState s) = s := rfl

def counterStart (q : Problem) : CState := ⟨0, q.2.1, q.2.2⟩
def helixStart (q : Problem) : HState := liftState (counterStart q)

def RelayHalts (q : Problem) : Prop :=
  ∃ n, crun q.1 n (counterStart q) = none

def HelixHalts (q : Problem) : Prop :=
  ∃ n, hrun q.1 n (helixStart q) = none

/-- 2. The two halting questions agree pointwise. -/
theorem relay_halts_iff_helix_halts (q : Problem) :
    RelayHalts q ↔ HelixHalts q := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hcomm := run_forgets_exactly q.1 n (helixStart q)
    have hforget : forget (helixStart q) = counterStart q := rfl
    rw [hforget, hn] at hcomm
    cases e : hrun q.1 n (helixStart q) with
    | none => rfl
    | some h' => rw [e] at hcomm; simp at hcomm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hcomm := run_forgets_exactly q.1 n (helixStart q)
    have hforget : forget (helixStart q) = counterStart q := rfl
    rw [hforget, hn] at hcomm
    simpa using hcomm.symm

/-- 3–4. The encoding is literally identity and Mathlib certifies it computable.
This is a genuine effective many-one reduction, not an oracle function. -/
theorem relay_to_helix_is_effective : RelayHalts ≤₀ HelixHalts := by
  exact ⟨id, Computable.id, relay_halts_iff_helix_halts⟩

/-- 5. Noncomputability now crosses the helix door without any further premise
about the translation. -/
theorem relay_noncomputability_transfers
    (relayUndecidable : ¬ ComputablePred RelayHalts) :
    ¬ ComputablePred HelixHalts := by
  intro helixDecidable
  exact relayUndecidable
    (ComputablePred.computable_of_manyOneReducible relay_to_helix_is_effective
      helixDecidable)

/-! ## Red control: a clock return is not a helix-state return -/

def climber : Program := [inc false 0]
def climbProblem : Problem := (climber, (0, 0))

theorem twelve_climbs_clock_home_height_twelve :
    (hrun climber 12 (helixStart climbProblem)).map
      (fun h => (h.bodyA.seat, h.bodyA.height)) = some (0, 12) := by
  decide

theorem twelve_climbs_not_state_home :
    hrun climber 12 (helixStart climbProblem) ≠ some (helixStart climbProblem) := by
  decide

theorem effective_helix_door_certificate :
    (∀ q, RelayHalts q ↔ HelixHalts q) ∧
    RelayHalts ≤₀ HelixHalts ∧
    (¬ ComputablePred RelayHalts → ¬ ComputablePred HelixHalts) ∧
    hrun climber 12 (helixStart climbProblem) ≠ some (helixStart climbProblem) :=
  ⟨relay_halts_iff_helix_halts, relay_to_helix_is_effective,
   relay_noncomputability_transfers, twelve_climbs_not_state_home⟩

#print axioms step_forgets_exactly
#print axioms run_forgets_exactly
#print axioms relay_halts_iff_helix_halts
#print axioms relay_to_helix_is_effective
#print axioms relay_noncomputability_transfers
#print axioms twelve_climbs_clock_home_height_twelve
#print axioms twelve_climbs_not_state_home
#print axioms effective_helix_door_certificate

end FoundationStoneTest16AF
