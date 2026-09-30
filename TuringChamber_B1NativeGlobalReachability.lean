import TuringChamber_B2NativeRecurrence
import Mathlib

/-!
# THE TURING CHAMBER — B1 NATIVE GLOBAL REACHABILITY
## No single finite table decides the complete native-climber reachability relation

PURPOSE

K31 B1 is deliberately at "no finite table" strength:

  ¬ ∃ table : Nat, ∀ x y,
      interp table x y = true ↔ Reachable x y.

This file tests that exact strength on the already certified native 16AF climber.
The carrier is the climber's unbounded level parameter, with an explicit
step-preserving embedding back into actual 16AF helix states.

The interpreter is a genuine finite-table interpreter: a natural number decodes
to a finite relation. It also satisfies the K31 finite-window universality
condition: every decidable relation can be represented exactly on every finite
window.

The positive theorem says no one such finite table captures the whole infinite
reachability relation of the native climber orbit. The red control is a finite
two-state identity system, where finite-window universality really does provide
one table deciding all reachability.

CLAIMS DISCIPLINE

* This proves the exact K31 B1 finite-table shape, not the stronger theorem that
  no algorithm can decide reachability.
* The unbounded level dynamics are realised step-for-step by the actual certified
  16AF climber.
* The finite interpreter is not assumed to contain the desired conclusion.
* The finite red control demonstrates that B1 is not automatic.
* This is a reduced B1-visible adapter, not yet a full Stage3.System adapter.
* No zeta or RH statement is used.
-/

namespace TuringChamberB1NativeGlobalReachability

set_option autoImplicit false

open FoundationStoneTest16AF
open TuringChamberForgetfulView
open TuringChamberB2NativeRecurrence

/-! ## 1. Exact B1-visible K31 slice -/

structure B1System where
  X : Type
  step : X → X
  interp : Nat → X → X → Bool
  finuniversal : ∀ Q : X → X → Prop,
    (∀ x y, Decidable (Q x y)) →
      ∀ finiteWindow : Finset X, ∃ table,
        ∀ x ∈ finiteWindow, ∀ y ∈ finiteWindow,
          interp table x y = true ↔ Q x y

def Reachable (S : B1System) (x y : S.X) : Prop :=
  ∃ n : Nat, (S.step^[n]) x = y

def canonicalB1 (S : B1System) : Prop :=
  ¬ (∃ table : Nat, ∀ x y,
    S.interp table x y = true ↔ Reachable S x y)

def finiteMapDecisionControl (S : B1System) : Prop :=
  ∃ table : Nat, ∀ x y,
    S.interp table x y = true ↔ Reachable S x y

theorem finite_map_decision_control_rejects_B1
    (S : B1System) (hcontrol : finiteMapDecisionControl S) :
    ¬ canonicalB1 S := by
  intro h
  exact h hcontrol

/-! ## 2. Generic finite-table interpreter -/

noncomputable def decodedRelation
    {X : Type} [Encodable X] [DecidableEq X]
    (table : Nat) : Finset (X × X) :=
  (Encodable.decode table : Option (Finset (X × X))).getD ∅

noncomputable def finiteInterp
    {X : Type} [Encodable X] [DecidableEq X]
    (table : Nat) (x y : X) : Bool := by
  classical
  exact decide ((x, y) ∈ decodedRelation table)

theorem finiteInterp_finiteUniversal
    {X : Type} [Encodable X] [DecidableEq X]
    (Q : X → X → Prop)
    (hdecidable : ∀ x y, Decidable (Q x y))
    (finiteWindow : Finset X) :
    ∃ table, ∀ x ∈ finiteWindow, ∀ y ∈ finiteWindow,
      finiteInterp table x y = true ↔ Q x y := by
  classical
  let _ : DecidablePred (fun pair : X × X => Q pair.1 pair.2) :=
    fun pair => hdecidable pair.1 pair.2
  let relationTable : Finset (X × X) :=
    (finiteWindow.product finiteWindow).filter
      (fun pair => Q pair.1 pair.2)
  refine ⟨Encodable.encode relationTable, ?_⟩
  intro x hx y hy
  simp [finiteInterp, decodedRelation, relationTable,
    Encodable.encodek, hx, hy]

/-! ## 3. The unbounded native-climber orbit as a B1 system -/

def levelStep (n : Nat) : Nat := n + 1

def levelToLive (n : Nat) : LiveClimber :=
  (climberStep^[n]) startLive

theorem levelToLive_step (n : Nat) :
    levelToLive (levelStep n) =
      climberStep (levelToLive n) := by
  simp [levelToLive, levelStep, Function.iterate_succ_apply']

theorem level_native_step (n : Nat) :
    hstep climber (levelToLive n).state =
      some (levelToLive (levelStep n)).state := by
  rw [levelToLive_step]
  exact climberStep_is_native_hstep (levelToLive n)

noncomputable def levelB1System : B1System where
  X := Nat
  step := levelStep
  interp := finiteInterp
  finuniversal := finiteInterp_finiteUniversal

theorem level_iterate :
    ∀ k n : Nat, (levelStep^[k]) n = n + k := by
  intro k
  induction k with
  | zero =>
      intro n
      rfl
  | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply']
      rw [ih]
      simp [levelStep, Nat.add_assoc]

theorem level_reachable_from_zero (y : Nat) :
    ∃ n : Nat, (levelStep^[n]) 0 = y := by
  refine ⟨y, ?_⟩
  rw [level_iterate]
  simp

def escapeSecond (s : Finset (Nat × Nat)) : Nat :=
  s.sup (fun pair : Nat × Nat => pair.2) + 1

theorem zero_escape_not_mem (s : Finset (Nat × Nat)) :
    (0, escapeSecond s) ∉ s := by
  intro hmem
  have hle :
      escapeSecond s ≤
        s.sup (fun pair : Nat × Nat => pair.2) := by
    simpa using
      (Finset.le_sup (s := s)
        (f := fun pair : Nat × Nat => pair.2) hmem)
  unfold escapeSecond at hle
  omega

theorem native_climber_satisfies_canonical_B1 :
    canonicalB1 levelB1System := by
  rintro ⟨table, htable⟩
  change
    (∀ x y : Nat,
      finiteInterp table x y = true ↔
        ∃ n : Nat, (levelStep^[n]) x = y) at htable
  let s : Finset (Nat × Nat) := decodedRelation table
  let y : Nat := escapeSecond s
  have hyreach : ∃ n : Nat, (levelStep^[n]) 0 = y :=
    level_reachable_from_zero y
  have htrue : finiteInterp table 0 y = true :=
    (htable 0 y).2 hyreach
  have hmem : (0, y) ∈ s := by
    simpa [finiteInterp, s] using htrue
  exact (zero_escape_not_mem s) hmem

/-! ## 4. Red control: a genuinely finite global state can be table-decided -/

abbrev Tiny := Fin 2

def tinyStep (x : Tiny) : Tiny := x

noncomputable def tinyB1System : B1System where
  X := Tiny
  step := tinyStep
  interp := finiteInterp
  finuniversal := finiteInterp_finiteUniversal

theorem tiny_iterate :
    ∀ n : Nat, ∀ x : Tiny, (tinyStep^[n]) x = x := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      rw [ih]
      rfl

theorem tiny_reachable_iff (x y : Tiny) :
    Reachable tinyB1System x y ↔ x = y := by
  constructor
  · rintro ⟨n, h⟩
    change (tinyStep^[n]) x = y at h
    rw [tiny_iterate] at h
    exact h
  · intro h
    subst y
    refine ⟨0, ?_⟩
    rfl

theorem tiny_has_global_finite_map_decision :
    finiteMapDecisionControl tinyB1System := by
  classical
  obtain ⟨table, htable⟩ :=
    finiteInterp_finiteUniversal
      (X := Tiny)
      (fun x y : Tiny => x = y)
      (fun _ _ => inferInstance)
      (Finset.univ : Finset Tiny)
  refine ⟨table, ?_⟩
  change ∀ x y : Tiny,
    finiteInterp table x y = true ↔
      ∃ n : Nat, (tinyStep^[n]) x = y
  intro x y
  rw [htable x (by simp) y (by simp)]
  exact (tiny_reachable_iff x y).symm

theorem tiny_fails_canonical_B1 :
    ¬ canonicalB1 tinyB1System :=
  finite_map_decision_control_rejects_B1
    tinyB1System tiny_has_global_finite_map_decision

/-! ## 5. Certificate -/

theorem B1_native_global_reachability_certificate :
    (∀ n : Nat,
      hstep climber (levelToLive n).state =
        some (levelToLive (levelStep n)).state) ∧
    canonicalB1 levelB1System ∧
    finiteMapDecisionControl tinyB1System ∧
    ¬ canonicalB1 tinyB1System := by
  exact ⟨level_native_step,
    native_climber_satisfies_canonical_B1,
    tiny_has_global_finite_map_decision,
    tiny_fails_canonical_B1⟩

#print axioms finiteInterp_finiteUniversal
#print axioms level_native_step
#print axioms level_iterate
#print axioms zero_escape_not_mem
#print axioms native_climber_satisfies_canonical_B1
#print axioms tiny_has_global_finite_map_decision
#print axioms tiny_fails_canonical_B1
#print axioms B1_native_global_reachability_certificate

end TuringChamberB1NativeGlobalReachability
