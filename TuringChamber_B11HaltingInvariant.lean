import FoundationStoneTest16BU
import Mathlib

/-!
# THE TURING CHAMBER — B11 HALTING INVARIANT
## A direct reduced bridge from global helix undecidability to K31 B11 shape

Uses the established 16BU global helix-halting theorem.

PURPOSE

K31 B11 has the logical shape:

  there exists a nontrivial invariant I
  preserved by the map
  for which no internal expression denotes I.

This file asks whether the Turing Chamber itself supplies such an invariant.

The invariant is not invented from a finite quotient. It is the established
global predicate FoundationStoneTest16AF.HelixHalts.

To keep the map nontrivial while preserving the underlying Chamber problem, the
carrier is a problem paired with an observation index. One step increments only
that index. Thus the map visibly changes on every state while the halting
property of the underlying helix problem is invariant.

The internal language is explicitly restricted to predicates that Mathlib
certifies computable. If one of those expressions denoted the lifted helix
halting invariant, the established theorem
FoundationStoneTest16BU.helix_halting_is_not_computable would be contradicted.

This is a reduced B11 bridge. It does not yet instantiate the full K31
Stage3.System, and its step is an observation-index step rather than native
hstep. The invariant itself, however, is exactly the Chamber's global halting
predicate and the non-naming argument is exactly its certified
noncomputability.

CLAIMS DISCIPLINE

* This is a B11/Turing-Chamber test, not an RH test.
* The internal language is the declared language of computable predicates.
* "Unnamed" means not denotable by any expression in that declared language.
* No claim is made about all conceivable formal languages.
* No claim is made that the observation-index step is native helix execution.
* -/

namespace TuringChamberB11HaltingInvariant

set_option autoImplicit false

open FoundationStoneTest16AF
open FoundationStoneTest16BU

/-! ## 1. Exact reduced K31 B11 logical shape -/

structure B11System where
  X : Type
  Language : Type
  step : X → X
  den : Language → X → Prop

def MapInvariant (S : B11System) (I : S.X → Prop) : Prop :=
  ∀ x, I x → I (S.step x)

def Denotes (S : B11System) (expression : S.Language)
    (property : S.X → Prop) : Prop :=
  ∀ x, S.den expression x ↔ property x

def canonicalB11 (S : B11System) : Prop :=
  ∃ I : S.X → Prop,
    MapInvariant S I ∧
    I ≠ (fun _ => False) ∧
    I ≠ (fun _ => True) ∧
    ¬ (∃ expression : S.Language, Denotes S expression I)

/-! ## 2. Chamber problems with a changing observation index -/

abbrev TimedProblem := Problem × Nat

def timedStep : TimedProblem → TimedProblem
  | (q, t) => (q, t + 1)

theorem timedStep_changes (x : TimedProblem) :
    timedStep x ≠ x := by
  rcases x with ⟨q, t⟩
  simp [timedStep]

def timedHelixInvariant (x : TimedProblem) : Prop :=
  HelixHalts x.1

theorem timedHelixInvariant_preserved :
    ∀ x, timedHelixInvariant x → timedHelixInvariant (timedStep x) := by
  intro x hx
  exact hx

/-! ## 3. The internal language: exactly computable predicates -/

structure InternalExpr where
  pred : TimedProblem → Prop
  computable : ComputablePred pred

def internalDen (e : InternalExpr) (x : TimedProblem) : Prop :=
  e.pred x

def chamberB11System : B11System where
  X := TimedProblem
  Language := InternalExpr
  step := timedStep
  den := internalDen

/-! ## 4. Lift the established noncomputability theorem -/

def embedProblem (q : Problem) : TimedProblem :=
  (q, 0)

theorem embedProblem_computable :
    Computable embedProblem := by
  unfold embedProblem
  exact Computable.id.pair (Computable.const 0)

theorem helix_to_timed_invariant_is_effective :
    HelixHalts ≤₀ timedHelixInvariant := by
  exact ⟨embedProblem, embedProblem_computable, fun _ => Iff.rfl⟩

theorem timedHelixInvariant_not_computable :
    ¬ ComputablePred timedHelixInvariant := by
  intro h
  exact helix_halting_is_not_computable
    (ComputablePred.computable_of_manyOneReducible
      helix_to_timed_invariant_is_effective h)

/-! ## 5. Nontriviality follows from noncomputability -/

theorem false_property_computable :
    ComputablePred (fun _ : TimedProblem => False) := by
  unfold ComputablePred
  refine ⟨inferInstance, ?_⟩
  simpa using
    (Computable.const false :
      Computable (fun _ : TimedProblem => false))

theorem true_property_computable :
    ComputablePred (fun _ : TimedProblem => True) := by
  unfold ComputablePred
  refine ⟨inferInstance, ?_⟩
  simpa using
    (Computable.const true :
      Computable (fun _ : TimedProblem => true))

theorem timedHelixInvariant_not_false :
    timedHelixInvariant ≠ (fun _ => False) := by
  intro h
  apply timedHelixInvariant_not_computable
  rw [h]
  exact false_property_computable

theorem timedHelixInvariant_not_true :
    timedHelixInvariant ≠ (fun _ => True) := by
  intro h
  apply timedHelixInvariant_not_computable
  rw [h]
  exact true_property_computable

/-! ## 6. No computable internal expression names the invariant -/

theorem no_internal_expression_names_timed_halting :
    ¬ (∃ expression : InternalExpr,
      Denotes chamberB11System expression timedHelixInvariant) := by
  rintro ⟨expression, hden⟩
  have heq : expression.pred = timedHelixInvariant := by
    funext x
    apply propext
    exact hden x
  apply timedHelixInvariant_not_computable
  rw [← heq]
  exact expression.computable

theorem chamber_halting_satisfies_reduced_canonical_B11 :
    canonicalB11 chamberB11System := by
  refine ⟨timedHelixInvariant, ?_, ?_, ?_, ?_⟩
  · exact timedHelixInvariant_preserved
  · exact timedHelixInvariant_not_false
  · exact timedHelixInvariant_not_true
  · exact no_internal_expression_names_timed_halting

/-! ## 7. Red control: an unrestricted language destroys B11 unnamedness -/

def unrestrictedB11System : B11System where
  X := TimedProblem
  Language := TimedProblem → Prop
  step := timedStep
  den := fun P x => P x

theorem unrestricted_language_names_every_property
    (I : TimedProblem → Prop) :
    ∃ expression : unrestrictedB11System.Language,
      Denotes unrestrictedB11System expression I := by
  exact ⟨I, fun _ => Iff.rfl⟩

theorem unrestricted_language_fails_canonical_B11 :
    ¬ canonicalB11 unrestrictedB11System := by
  rintro ⟨I, _hinvariant, _hnonfalse, _hnontrue, hunnamed⟩
  exact hunnamed (unrestricted_language_names_every_property I)

/-! ## 8. Certificate -/

theorem B11_halting_invariant_certificate :
    (∀ x : TimedProblem, timedStep x ≠ x) ∧
    (∀ x, timedHelixInvariant x →
      timedHelixInvariant (timedStep x)) ∧
    ¬ ComputablePred timedHelixInvariant ∧
    canonicalB11 chamberB11System ∧
    ¬ canonicalB11 unrestrictedB11System := by
  exact ⟨timedStep_changes,
    timedHelixInvariant_preserved,
    timedHelixInvariant_not_computable,
    chamber_halting_satisfies_reduced_canonical_B11,
    unrestricted_language_fails_canonical_B11⟩

#print axioms embedProblem_computable
#print axioms helix_to_timed_invariant_is_effective
#print axioms timedHelixInvariant_not_computable
#print axioms timedHelixInvariant_not_false
#print axioms timedHelixInvariant_not_true
#print axioms no_internal_expression_names_timed_halting
#print axioms chamber_halting_satisfies_reduced_canonical_B11
#print axioms unrestricted_language_fails_canonical_B11
#print axioms B11_halting_invariant_certificate

end TuringChamberB11HaltingInvariant
