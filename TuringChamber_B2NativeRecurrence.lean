import TuringChamber_ForgetfulViewContract
import Mathlib

/-!
# THE TURING CHAMBER — B2 NATIVE RECURRENCE
## Exact K31-shaped non-convergence from one actual 16AF climber orbit

PURPOSE

K31 B2 asks for one orbit which:
* never repeats as a rich state;
* has a genuinely nonconstant observation;
* returns to its starting observation arbitrarily late.

This file tests that exact shape on the already certified native 16AF climber.
The rich state remembers unbounded Body A height. The observation remembers only
the 12-seat clock position.

Thus the expected phenomenon is:

  rich orbit: injective forever,
  observation: nonconstant but recurrent every 12 steps.

This is a B2/Turing-Chamber test. The recurrence is the same structural feature
that later supports quotient-cycle counting, but no zeta or RH statement is
used here. 
CLAIMS DISCIPLINE

* The step is the actual certified native 16AF climber step.
* The observation is the previously certified clock-seat view.
* Arbitrarily-late recurrence is proved, not inferred from one 12-step return.
* No full Stage3.System adapter is claimed in this file.
* No RH claim is asserted.
-/

namespace TuringChamberB2NativeRecurrence

set_option autoImplicit false

open FoundationStoneTest16AF
open TuringChamberForgetfulView

structure B2System where
  X : Type
  Observation : Type
  step : X → X
  observe : X → Observation

def canonicalB2 (S : B2System) : Prop :=
  ∃ x : S.X,
    Function.Injective (fun n : Nat => (S.step^[n]) x) ∧
    (∃ i j : Nat,
      S.observe ((S.step^[i]) x) ≠
        S.observe ((S.step^[j]) x)) ∧
    ∀ cutoff : Nat, ∃ later : Nat,
      cutoff < later ∧
        S.observe ((S.step^[later]) x) = S.observe x

def constantObservationControl (S : B2System) : Prop :=
  ∀ x y, S.observe x = S.observe y

def injectiveObservationControl (S : B2System) : Prop :=
  Function.Injective S.observe

theorem constant_observation_control_rejects_B2
    (S : B2System) (hconstant : constantObservationControl S) :
    ¬ canonicalB2 S := by
  rintro ⟨x, _horbit, ⟨i, j, hdifferent⟩, _hrecur⟩
  exact hdifferent (hconstant _ _)

theorem injective_observation_control_rejects_B2
    (S : B2System) (hinjective : injectiveObservationControl S) :
    ¬ canonicalB2 S := by
  rintro ⟨x, horbit, _hnonconstant, hrecur⟩
  obtain ⟨later, hlater, hobservation⟩ := hrecur 0
  have hstate : (S.step^[later]) x = (S.step^[0]) x := by
    apply hinjective
    simpa using hobservation
  have hindex : later = 0 := horbit hstate
  omega

def climberB2System : B2System where
  X := LiveClimber
  Observation := Seat
  step := climberStep
  observe := clockView

theorem iterate_eq_run {X : Type} (step : X → X) :
    ∀ n (x : X), (step^[n]) x = run step n x := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply]
      exact ih (step x)

theorem climber_iterate_height (n : Nat) (x : LiveClimber) :
    ((climberStep^[n]) x).state.bodyA.height =
      x.state.bodyA.height + n := by
  rw [iterate_eq_run]
  exact climber_run_height n x

theorem climber_orbit_injective :
    Function.Injective (fun n : Nat => (climberStep^[n]) startLive) := by
  intro i j h
  have hh := congrArg
    (fun z : LiveClimber => z.state.bodyA.height) h
  rw [climber_iterate_height i startLive,
    climber_iterate_height j startLive] at hh
  omega

theorem clock_observation_nonconstant :
    ∃ i j : Nat,
      clockView ((climberStep^[i]) startLive) ≠
        clockView ((climberStep^[j]) startLive) := by
  refine ⟨0, 1, ?_⟩
  decide

theorem clock_iterate_twelve_identity (s : Seat) :
    (clockStep^[12]) s = s := by
  fin_cases s <;> decide

theorem clock_iterate_twelve_mul (k : Nat) (s : Seat) :
    (clockStep^[12 * k]) s = s := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply,
        clock_iterate_twelve_identity]
      exact ih

theorem clockView_iterate_commutes (n : Nat) (x : LiveClimber) :
    clockView ((climberStep^[n]) x) =
      (clockStep^[n]) (clockView x) := by
  rw [iterate_eq_run, iterate_eq_run]
  exact view_run_commutes clockContract n x

theorem clock_observation_recurs_arbitrarily_late :
    ∀ cutoff : Nat, ∃ later : Nat,
      cutoff < later ∧
        clockView ((climberStep^[later]) startLive) =
          clockView startLive := by
  intro cutoff
  refine ⟨12 * (cutoff + 1), ?_, ?_⟩
  · omega
  · rw [clockView_iterate_commutes,
      clock_iterate_twelve_mul]

theorem native_climber_satisfies_canonical_B2 :
    canonicalB2 climberB2System := by
  refine ⟨startLive, ?_, ?_, ?_⟩
  · exact climber_orbit_injective
  · exact clock_observation_nonconstant
  · exact clock_observation_recurs_arbitrarily_late

theorem B2_native_recurrence_certificate :
    (∀ x : LiveClimber,
      hstep climber x.state = some (climberStep x).state) ∧
    Function.Injective
      (fun n : Nat => (climberStep^[n]) startLive) ∧
    (∃ i j : Nat,
      clockView ((climberStep^[i]) startLive) ≠
        clockView ((climberStep^[j]) startLive)) ∧
    (∀ cutoff : Nat, ∃ later : Nat,
      cutoff < later ∧
        clockView ((climberStep^[later]) startLive) =
          clockView startLive) ∧
    canonicalB2 climberB2System := by
  exact ⟨climberStep_is_native_hstep,
    climber_orbit_injective,
    clock_observation_nonconstant,
    clock_observation_recurs_arbitrarily_late,
    native_climber_satisfies_canonical_B2⟩

#print axioms iterate_eq_run
#print axioms climber_orbit_injective
#print axioms clock_observation_nonconstant
#print axioms clock_iterate_twelve_identity
#print axioms clock_iterate_twelve_mul
#print axioms clock_observation_recurs_arbitrarily_late
#print axioms native_climber_satisfies_canonical_B2
#print axioms B2_native_recurrence_certificate

end TuringChamberB2NativeRecurrence
