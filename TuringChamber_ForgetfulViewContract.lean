import FoundationStoneTest16AF
import Mathlib

/-!
# THE TURING CHAMBER — FORGETFUL VIEW CONTRACT
## Projection, return, and the information lost in coming home

PURPOSE

Two constructions exhibit the same pattern:

* the clock-seat view returns while the full helix state continues;
* the ownership view returns while the provenance/history state continues.

This file factors that pattern into one generic contract.

A view consists of a richer state X, a visible state V, dynamics on both, and a
projection view : X → V which commutes with one step.  From that, the projection
commutes with every finite run.

The key distinction is then explicit:

  native period  => view period

but the converse need not hold.

Two witnesses are supplied.

A. Native 16AF climber → Body A clock seat.
   The view has period 12, while Body A height is a strict rank and the richer
   state has no positive period.

B. History/provenance K-lock → current ownership.
   The view has period 2, while ledger length is a strict rank and the richer
   history state has no positive period.

CLAIMS DISCIPLINE

* A projected return is a return only in the named view.
* No projected cycle is silently promoted to a native cycle.
* The projection must carry an explicit commutation theorem.
* Information loss is witnessed by distinct rich states with the same view.
* This file constructs no zeta function and makes no RH claim.
-/

namespace TuringChamberForgetfulView

set_option autoImplicit false

open FoundationStoneTest16AF

/-! ## 1. Generic finite dynamics and views -/

def run {X : Type} (step : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => run step n (step x)

structure ViewContract where
  X : Type
  V : Type
  stepX : X → X
  stepV : V → V
  view : X → V
  commutes : ∀ x, view (stepX x) = stepV (view x)

def NativePeriodAt (C : ViewContract) (n : Nat) (x : C.X) : Prop :=
  0 < n ∧ run C.stepX n x = x

def ViewPeriodAt (C : ViewContract) (n : Nat) (x : C.X) : Prop :=
  0 < n ∧ run C.stepV n (C.view x) = C.view x

def HasNativePeriod (C : ViewContract) (x : C.X) : Prop :=
  ∃ n, NativePeriodAt C n x

def HasViewPeriod (C : ViewContract) (x : C.X) : Prop :=
  ∃ n, ViewPeriodAt C n x

def ForgetsInformation (C : ViewContract) : Prop :=
  ∃ x y : C.X, x ≠ y ∧ C.view x = C.view y

theorem view_run_commutes (C : ViewContract) :
    ∀ n (x : C.X),
      C.view (run C.stepX n x) =
        run C.stepV n (C.view x) := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      simp only [run]
      rw [ih (C.stepX x), C.commutes x]

theorem native_period_implies_view_period
    (C : ViewContract) (n : Nat) (x : C.X)
    (h : NativePeriodAt C n x) :
    ViewPeriodAt C n x := by
  refine ⟨h.1, ?_⟩
  rw [← view_run_commutes C n x, h.2]

theorem view_period_without_native_period
    (C : ViewContract) (n : Nat) (x : C.X)
    (hview : ViewPeriodAt C n x)
    (hnative : run C.stepX n x ≠ x) :
    ViewPeriodAt C n x ∧ ¬ NativePeriodAt C n x := by
  refine ⟨hview, ?_⟩
  intro h
  exact hnative h.2

/-! ## 2. Witness A: native 16AF climber → clock seat -/

structure LiveClimber where
  state : HState
  pc_zero : state.pc = 0

def climberStep (x : LiveClimber) : LiveClimber where
  state := bset x.state 0 false (climb x.state.bodyA)
  pc_zero := by rfl

theorem climberStep_is_native_hstep (x : LiveClimber) :
    hstep climber x.state = some (climberStep x).state := by
  rcases x with ⟨⟨pc, a, b⟩, hpc⟩
  change pc = 0 at hpc
  subst pc
  rfl

theorem climber_run_is_hrun :
    ∀ n (x : LiveClimber),
      hrun climber n x.state =
        some (run climberStep n x).state := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      unfold hrun
      rw [climberStep_is_native_hstep x]
      simpa [run] using ih (climberStep x)

def clockView (x : LiveClimber) : Seat :=
  x.state.bodyA.seat

def clockStep : Seat → Seat :=
  forward

theorem clockView_commutes (x : LiveClimber) :
    clockView (climberStep x) = clockStep (clockView x) := by
  rfl

def clockContract : ViewContract where
  X := LiveClimber
  V := Seat
  stepX := climberStep
  stepV := clockStep
  view := clockView
  commutes := clockView_commutes

def startLive : LiveClimber where
  state := helixStart climbProblem
  pc_zero := rfl

theorem climber_run_height :
    ∀ n (x : LiveClimber),
      (run climberStep n x).state.bodyA.height =
        x.state.bodyA.height + n := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      change
        (run climberStep n (climberStep x)).state.bodyA.height =
          x.state.bodyA.height + (n + 1)
      rw [ih (climberStep x)]
      simp [climberStep, bset, climb]
      omega

theorem climber_no_positive_return
    (n : Nat) (hn : 0 < n) (x : LiveClimber) :
    run climberStep n x ≠ x := by
  intro h
  have hh := congrArg
    (fun z : LiveClimber => z.state.bodyA.height) h
  rw [climber_run_height n x] at hh
  omega

theorem clock_view_period_twelve :
    ViewPeriodAt clockContract 12 startLive := by
  constructor
  · decide
  · change run clockStep 12 (clockView startLive) = clockView startLive
    decide

theorem clock_native_not_period_twelve :
    ¬ NativePeriodAt clockContract 12 startLive := by
  intro h
  exact climber_no_positive_return 12 (by decide) startLive h.2

theorem clock_projection_period_not_native_period :
    ViewPeriodAt clockContract 12 startLive ∧
      ¬ NativePeriodAt clockContract 12 startLive :=
  ⟨clock_view_period_twelve, clock_native_not_period_twelve⟩

theorem clock_contract_forgets_information :
    ForgetsInformation clockContract := by
  refine ⟨startLive, run climberStep 12 startLive, ?_, ?_⟩
  · intro h
    exact climber_no_positive_return 12 (by decide) startLive h.symm
  · exact clock_view_period_twelve.2.symm

/-! ## 3. Witness B: provenance/history → ownership -/

structure Ownership (K : Type) where
  a : K
  b : K
deriving Repr

def swapOwnership {K : Type} (o : Ownership K) : Ownership K :=
  ⟨o.b, o.a⟩

structure HistoryState (K : Type) where
  current : Ownership K
  ledger : List (Ownership K)
deriving Repr

def historyStep {K : Type} (s : HistoryState K) : HistoryState K :=
  let next := swapOwnership s.current
  ⟨next, next :: s.ledger⟩

def ownershipView {K : Type} (s : HistoryState K) : Ownership K :=
  s.current

theorem ownershipView_commutes {K : Type} (s : HistoryState K) :
    ownershipView (historyStep s) =
      swapOwnership (ownershipView s) := by
  rfl

def historyContract (K : Type) : ViewContract where
  X := HistoryState K
  V := Ownership K
  stepX := historyStep
  stepV := swapOwnership
  view := ownershipView
  commutes := ownershipView_commutes

theorem ownership_two_steps {K : Type} (o : Ownership K) :
    run swapOwnership 2 o = o := by
  cases o
  rfl

theorem history_run_length {K : Type} :
    ∀ n (s : HistoryState K),
      (run historyStep n s).ledger.length =
        s.ledger.length + n := by
  intro n
  induction n with
  | zero =>
      intro s
      rfl
  | succ n ih =>
      intro s
      change
        (run historyStep n (historyStep s)).ledger.length =
          s.ledger.length + (n + 1)
      rw [ih (historyStep s)]
      simp [historyStep]
      omega

theorem history_no_positive_return {K : Type}
    (n : Nat) (hn : 0 < n) (s : HistoryState K) :
    run historyStep n s ≠ s := by
  intro h
  have hlen := congrArg
    (fun t : HistoryState K => t.ledger.length) h
  rw [history_run_length n s] at hlen
  omega

theorem ownership_view_period_two {K : Type}
    (s : HistoryState K) :
    ViewPeriodAt (historyContract K) 2 s := by
  refine ⟨by decide, ?_⟩
  exact ownership_two_steps s.current

theorem history_native_not_period_two {K : Type}
    (s : HistoryState K) :
    ¬ NativePeriodAt (historyContract K) 2 s := by
  intro h
  exact history_no_positive_return 2 (by decide) s h.2

theorem ownership_projection_period_not_history_period {K : Type}
    (s : HistoryState K) :
    ViewPeriodAt (historyContract K) 2 s ∧
      ¬ NativePeriodAt (historyContract K) 2 s :=
  ⟨ownership_view_period_two s, history_native_not_period_two s⟩

theorem history_contract_forgets_information {K : Type}
    (s : HistoryState K) :
    ForgetsInformation (historyContract K) := by
  refine ⟨s, run historyStep 2 s, ?_, ?_⟩
  · intro h
    exact history_no_positive_return 2 (by decide) s h.symm
  · exact (ownership_view_period_two s).2.symm

/-! ## 4. One generic certificate with both witnesses -/

theorem forgetful_view_contract_certificate :
    (∀ (C : ViewContract) (n : Nat) (x : C.X),
      NativePeriodAt C n x → ViewPeriodAt C n x) ∧
    (ViewPeriodAt clockContract 12 startLive ∧
      ¬ NativePeriodAt clockContract 12 startLive) ∧
    ForgetsInformation clockContract ∧
    (∀ (K : Type) (s : HistoryState K),
      ViewPeriodAt (historyContract K) 2 s ∧
        ¬ NativePeriodAt (historyContract K) 2 s) ∧
    (∀ (K : Type) (s : HistoryState K),
      ForgetsInformation (historyContract K)) := by
  refine ⟨?_, clock_projection_period_not_native_period,
    clock_contract_forgets_information, ?_, ?_⟩
  · intro C n x h
    exact native_period_implies_view_period C n x h
  · intro K s
    exact ownership_projection_period_not_history_period s
  · intro K s
    exact history_contract_forgets_information s

#print axioms view_run_commutes
#print axioms native_period_implies_view_period
#print axioms climberStep_is_native_hstep
#print axioms climber_run_is_hrun
#print axioms climber_run_height
#print axioms clock_projection_period_not_native_period
#print axioms clock_contract_forgets_information
#print axioms history_run_length
#print axioms ownership_projection_period_not_history_period
#print axioms history_contract_forgets_information
#print axioms forgetful_view_contract_certificate

end TuringChamberForgetfulView
