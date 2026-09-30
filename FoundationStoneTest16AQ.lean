import Mathlib.Computability.StateTransition

/-!
# THE TURING CHAMBER — TEST 16AQ: THE RUN-LIFTING HINGE

Lean 4.35.0-rc2 / pinned Mathlib.

This file fixes the exact proof interface for the remaining TM2-to-MM2
compiler.  Mathlib's `StateTransition.Respects` requires both:

* every source step is simulated by a nonempty finite target run;
* a source halt maps to an immediate target halt.

Mathlib's `tr_eval_dom` then supplies termination equivalence for arbitrary
runs.  We package that result without inventing a second run induction.
-/

namespace FoundationStoneTest16AQ

open StateTransition

def Terminates {S : Type} (step : S → Option S) (s : S) : Prop :=
  (eval step s).Dom

/-- The exact theorem the TM2-to-MM2 compiler must discharge. -/
theorem respects_gives_halting_iff
    {S T : Type} {source : S → Option S} {target : T → Option T}
    {R : S → T → Prop}
    (hR : Respects source target R) {s : S} {t : T} (hst : R s t) :
    Terminates source s ↔ Terminates target t := by
  unfold Terminates
  exact (tr_eval_dom hR hst).symm

/-- Functional form: an encoding need not simulate one-for-one; each source
step may take any positive number of target steps. -/
theorem functional_respects_gives_halting_iff
    {S T : Type} {source : S → Option S} {target : T → Option T}
    (encode : S → T)
    (hsim : ∀ s,
      match source s with
      | some s' => Reaches₁ target (encode s) (encode s')
      | none => target (encode s) = none) (s : S) :
    Terminates source s ↔ Terminates target (encode s) := by
  apply respects_gives_halting_iff (R := fun x y => encode x = y)
  · intro a b hab
    subst b
    cases h : source a with
    | none => simpa [h] using hsim a
    | some a' =>
        refine ⟨encode a', rfl, ?_⟩
        simpa [h] using hsim a
  · rfl

/-! ## Red control: positive-step simulation without halt preservation is not
enough.  The source below halts at zero; the target loops forever everywhere.
The step case can be simulated, but a `Respects` proof is impossible exactly
at the source halt. -/

def sourceToy : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

def targetLoop (n : Nat) : Option Nat := some n

theorem targetLoop_never_halts (n : Nat) : targetLoop n ≠ none := by
  simp [targetLoop]

theorem no_respects_without_halt_preservation :
    ¬ Respects sourceToy targetLoop (fun s t => s = t) := by
  intro h
  have hz := h (a₁ := 0) (a₂ := 0) rfl
  simpa [sourceToy, targetLoop] using hz

/-- This is the precise open certificate type.  Constructing a value of this
type for Mathlib's fixed TM2 and the emitted MM2 program completes the middle
door; no additional arbitrary-run proof will then be required. -/
def CompilerObligation {S T : Type}
    (source : S → Option S) (target : T → Option T) (encode : S → T) : Prop :=
  ∀ s,
    match source s with
    | some s' => Reaches₁ target (encode s) (encode s')
    | none => target (encode s) = none

theorem obligation_closes_runs {S T : Type}
    (source : S → Option S) (target : T → Option T) (encode : S → T)
    (h : CompilerObligation source target encode) (s : S) :
    Terminates source s ↔ Terminates target (encode s) :=
  functional_respects_gives_halting_iff encode h s

theorem turing_chamber_16AQ_certificate :
    (∀ {S T : Type} {source : S → Option S} {target : T → Option T}
      (encode : S → T),
      CompilerObligation source target encode →
      ∀ s, Terminates source s ↔ Terminates target (encode s)) ∧
    ¬ Respects sourceToy targetLoop (fun s t => s = t) :=
  ⟨fun encode h s => obligation_closes_runs _ _ encode h s,
   no_respects_without_halt_preservation⟩

#print axioms respects_gives_halting_iff
#print axioms functional_respects_gives_halting_iff
#print axioms no_respects_without_halt_preservation
#print axioms turing_chamber_16AQ_certificate

end FoundationStoneTest16AQ
