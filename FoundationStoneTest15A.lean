import Mathlib

/-!
# THE RETURN DEFECT — TEST 15A

This is the abstract foundation.  It contains no Wooden Idol station names and
no spatial matrix.  The purpose is to test one proposed mechanism on its own:

  a visible process may return while an accumulated charge does not.

`iter F n s` is the complete state after `n` steps.  An observer sees only
`project s`.  A charge changes by the same element `d` at every step.

Lean confirms:
1. the charge after `n` steps is `charge s + n • d`;
2. accumulated defects compose additively;
3. if no positive multiple of `d` is zero, no positive full return is possible;
4. a periodic shadow plus a nonzero accumulated defect produces a return defect;
5. the twelve-clock lift is a concrete instance: its shadow returns after twelve
   steps while its height is twelve and its full state does not return;
6. two full states can share one shadow while carrying different charges, so the
   shadow cannot reconstruct the charge;
7. RED CONTROL: an irrelevant counter glued to an identity process manufactures
   the same formal phenomenon.  Therefore Test 15A identifies a valid mechanism,
   but cannot by itself certify that a chosen charge belongs intrinsically to the
   process.  That modelling debt is intentionally exposed, not hidden.

The red control is part of the result.  A later test must distinguish a charge
derived from the actual transition from arbitrary padding.
-/

namespace FoundationStoneTestFifteenA

/-! ## Part 1 — iteration and the observable/full distinction -/

def iter {S : Type} (F : S → S) : Nat → S → S
  | 0, s => s
  | n + 1, s => F (iter F n s)

theorem iter_add {S : Type} (F : S → S) (m n : Nat) (s : S) :
    iter F (m + n) s = iter F m (iter F n s) := by
  induction m with
  | zero => simp [iter]
  | succ m ih =>
      simp only [Nat.succ_add, iter]
      rw [ih]

def ShadowReturn {S O : Type} (project : S → O) (F : S → S)
    (n : Nat) (s : S) : Prop :=
  project (iter F n s) = project s

def FullReturn {S : Type} (F : S → S) (n : Nat) (s : S) : Prop :=
  iter F n s = s

structure ReturnDefect {S O : Type} (project : S → O) (F : S → S)
    (n : Nat) (s : S) : Prop where
  shadowReturns : ShadowReturn project F n s
  fullDoesNotReturn : ¬ FullReturn F n s

theorem full_return_descends {S O : Type} (project : S → O) (F : S → S)
    (n : Nat) (s : S) :
    FullReturn F n s → ShadowReturn project F n s := by
  intro h
  exact congrArg project h

/-! ## Part 2 — constant charge change and its cocycle law -/

def ChargeStep {S A : Type} [AddMonoid A]
    (charge : S → A) (F : S → S) (d : A) : Prop :=
  ∀ s, charge (F s) = charge s + d

def Accumulated {A : Type} [AddMonoid A] (d : A) (n : Nat) : A :=
  n • d

/-- The proposed foundation: a local constant change integrates to a global
accumulated defect. -/
theorem charge_after_iter {S A : Type} [AddMonoid A]
    (charge : S → A) (F : S → S) (d : A)
    (hstep : ChargeStep charge F d) :
    ∀ n s, charge (iter F n s) = charge s + Accumulated d n := by
  intro n
  induction n with
  | zero => intro s; simp [iter, Accumulated]
  | succ n ih =>
      intro s
      rw [iter, hstep, ih]
      unfold Accumulated
      rw [succ_nsmul]
      rw [add_assoc]

/-- The accumulated quantity is a cocycle: consecutive pieces add. -/
theorem accumulated_add {A : Type} [AddMonoid A] (d : A) (m n : Nat) :
    Accumulated d (m + n) = Accumulated d m + Accumulated d n := by
  simp [Accumulated, add_nsmul]

/-- If positive multiples of `d` never vanish, the complete state never returns. -/
theorem no_positive_full_return {S A : Type} [AddLeftCancelMonoid A]
    (charge : S → A) (F : S → S) (d : A)
    (hstep : ChargeStep charge F d)
    (hseparates : ∀ n, 0 < n → Accumulated d n ≠ 0) :
    ∀ n, 0 < n → ∀ s, ¬ FullReturn F n s := by
  intro n hn s hreturn
  have hc := congrArg charge hreturn
  rw [charge_after_iter charge F d hstep n s] at hc
  have hz : charge s + Accumulated d n = charge s + 0 := by simpa using hc
  have : Accumulated d n = 0 := add_left_cancel hz
  exact hseparates n hn this

/-- Visible periodicity plus separated accumulated charge gives the promised
return defect. -/
theorem return_defect_of_shadow_period {S O A : Type} [AddLeftCancelMonoid A]
    (project : S → O) (charge : S → A) (F : S → S) (d : A)
    (q : Nat) (s : S)
    (hshadow : ShadowReturn project F q s)
    (hq : 0 < q)
    (hstep : ChargeStep charge F d)
    (hseparates : ∀ n, 0 < n → Accumulated d n ≠ 0) :
    ReturnDefect project F q s := by
  exact ⟨hshadow, no_positive_full_return charge F d hstep hseparates q hq s⟩

/-! ## Part 3 — information hidden in a fibre -/

def HiddenChargeWitness {S O A : Type} (project : S → O) (charge : S → A) : Prop :=
  ∃ s t, project s = project t ∧ charge s ≠ charge t

def ChargeReconstructible {S O A : Type} (project : S → O) (charge : S → A) : Prop :=
  ∃ read : O → A, ∀ s, read (project s) = charge s

theorem hidden_charge_not_reconstructible {S O A : Type}
    (project : S → O) (charge : S → A)
    (hhidden : HiddenChargeWitness project charge) :
    ¬ ChargeReconstructible project charge := by
  intro ⟨read, hread⟩
  obtain ⟨s, t, hsame, hdiff⟩ := hhidden
  apply hdiff
  rw [← hread s, ← hread t, hsame]

/-! ## Part 4 — a genuine geometric prototype: the twelve-clock lift -/

structure ClockLift where
  phase : Fin 12
  height : Nat
deriving DecidableEq

def clockStart : ClockLift := ⟨0, 0⟩

def climb (s : ClockLift) : ClockLift :=
  ⟨s.phase + 1, s.height + 1⟩

def clockShadow (s : ClockLift) : Fin 12 := s.phase
def clockCharge (s : ClockLift) : Nat := s.height

theorem climb_charge_step : ChargeStep clockCharge climb 1 := by
  intro s
  rfl

theorem positive_nat_defect_separates :
    ∀ n, 0 < n → Accumulated (1 : Nat) n ≠ 0 := by
  intro n hn
  simpa [Accumulated] using Nat.ne_of_gt hn

theorem clock_shadow_returns_at_twelve :
    ShadowReturn clockShadow climb 12 clockStart := by
  unfold ShadowReturn
  decide

theorem clock_full_state_at_twelve :
    iter climb 12 clockStart = ⟨0, 12⟩ := by
  decide

theorem clock_has_return_defect_at_twelve :
    ReturnDefect clockShadow climb 12 clockStart := by
  exact return_defect_of_shadow_period
    clockShadow clockCharge climb 1 12 clockStart
    clock_shadow_returns_at_twelve (by decide)
    climb_charge_step positive_nat_defect_separates

theorem clock_never_fully_returns (n : Nat) (hn : 0 < n) :
    ¬ FullReturn climb n clockStart :=
  no_positive_full_return clockCharge climb 1
    climb_charge_step positive_nat_defect_separates n hn clockStart

theorem clock_height_is_hidden :
    HiddenChargeWitness clockShadow clockCharge := by
  exact ⟨⟨0, 0⟩, ⟨0, 12⟩, rfl, by decide⟩

theorem clock_shadow_cannot_reconstruct_height :
    ¬ ChargeReconstructible clockShadow clockCharge :=
  hidden_charge_not_reconstructible clockShadow clockCharge clock_height_is_hidden

/-! ## Part 5 — RED CONTROL: arbitrary padding manufactures the same pattern -/

structure Padded (S : Type) where
  base : S
  pad : Nat
deriving DecidableEq

def paddedIdentityStep (s : Padded Unit) : Padded Unit :=
  ⟨s.base, s.pad + 1⟩

def forgetPadding (s : Padded Unit) : Unit := s.base
def paddingCharge (s : Padded Unit) : Nat := s.pad
def paddedStart : Padded Unit := ⟨(), 0⟩

theorem padding_charge_step : ChargeStep paddingCharge paddedIdentityStep 1 := by
  intro s
  rfl

/-- The visible base does absolutely nothing, but the glued counter creates a
formal return defect after one step. -/
theorem fake_counter_manufactures_return_defect :
    ReturnDefect forgetPadding paddedIdentityStep 1 paddedStart := by
  apply return_defect_of_shadow_period
    forgetPadding paddingCharge paddedIdentityStep 1 1 paddedStart
  · rfl
  · decide
  · exact padding_charge_step
  · exact positive_nat_defect_separates

theorem fake_padding_is_hidden :
    HiddenChargeWitness forgetPadding paddingCharge := by
  exact ⟨⟨(), 0⟩, ⟨(), 1⟩, rfl, by decide⟩

/-- Even hiddenness cannot distinguish the genuine lift from irrelevant padding. -/
theorem fake_shadow_cannot_reconstruct_padding :
    ¬ ChargeReconstructible forgetPadding paddingCharge :=
  hidden_charge_not_reconstructible forgetPadding paddingCharge fake_padding_is_hidden

/-! ## Part 6 — zero-defect control -/

def flatClockStep (s : ClockLift) : ClockLift :=
  ⟨s.phase + 1, s.height⟩

theorem flat_clock_really_returns :
    FullReturn flatClockStep 12 clockStart := by
  unfold FullReturn
  decide

theorem zero_accumulation_does_not_separate :
    ¬ (∀ n, 0 < n → Accumulated (0 : Nat) n ≠ 0) := by
  intro h
  exact h 1 (by decide) (by simp [Accumulated])

/-! ## Certificate -/

theorem return_defect_test_15A_certificate :
    (∀ {S A : Type} [AddMonoid A]
      (charge : S → A) (F : S → S) (d : A),
      ChargeStep charge F d →
      ∀ n s, charge (iter F n s) = charge s + Accumulated d n) ∧
    (∀ {A : Type} [AddMonoid A] (d : A) (m n : Nat),
      Accumulated d (m + n) = Accumulated d m + Accumulated d n) ∧
    ReturnDefect clockShadow climb 12 clockStart ∧
    (¬ ChargeReconstructible clockShadow clockCharge) ∧
    ReturnDefect forgetPadding paddedIdentityStep 1 paddedStart ∧
    (¬ ChargeReconstructible forgetPadding paddingCharge) ∧
    FullReturn flatClockStep 12 clockStart :=
  ⟨charge_after_iter,
   accumulated_add,
   clock_has_return_defect_at_twelve,
   clock_shadow_cannot_reconstruct_height,
   fake_counter_manufactures_return_defect,
   fake_shadow_cannot_reconstruct_padding,
   flat_clock_really_returns⟩

#print axioms iter_add
#print axioms full_return_descends
#print axioms charge_after_iter
#print axioms accumulated_add
#print axioms no_positive_full_return
#print axioms return_defect_of_shadow_period
#print axioms hidden_charge_not_reconstructible
#print axioms clock_shadow_returns_at_twelve
#print axioms clock_full_state_at_twelve
#print axioms clock_has_return_defect_at_twelve
#print axioms clock_never_fully_returns
#print axioms clock_shadow_cannot_reconstruct_height
#print axioms fake_counter_manufactures_return_defect
#print axioms fake_shadow_cannot_reconstruct_padding
#print axioms flat_clock_really_returns
#print axioms zero_accumulation_does_not_separate
#print axioms return_defect_test_15A_certificate

end FoundationStoneTestFifteenA
