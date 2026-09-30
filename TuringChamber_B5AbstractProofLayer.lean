import TuringChamber_B3ElevenWay
import Mathlib

/-!
# THE TURING CHAMBER — ABSTRACT B5 PROOF LAYER

Purpose: separate the *structural* question
  "can a genuine, productive B5 proof layer coexist with the eleven-way Chamber?"
from the expensive *arithmetic certification* question
  "does IΣ1 supply such a layer via Gödel II?"

The first question is the intended parametric theorem below.  Certification
of this revision requires a successful build and an audit of its axiom output.

A ProofLayer supplies:
* a sentence type;
* point-independent sentence truth on Chamber states;
* an internal proof predicate;
* falsum and a consistency sentence;
* consistency (falsum is not provable);
* unprovability of the consistency sentence;
* productivity (something is provable).

No Foundation/Gödel library is imported in this file.

Given ANY such layer, we attach it to the eleven-way Chamber
without changing the Chamber state dynamics.  The one-system theorem
asserts B1..B12, including B5, and keeps a productive proof system.

A separate tiny adapter can instantiate this interface with IΣ1 and
Foundation's formalized Gödel-II theorem.  That isolates heavy proof-theory
compilation from the Chamber integration itself.  The abstract interface
assumes its B5 facts; it does not derive Gödel II from Chamber geometry.
-/

open Function

namespace TuringChamberB5AbstractLayer

set_option autoImplicit false

open FoundationStoneTest16AF
open TuringChamberB124OneSystem
open TuringChamberB3ElevenWay

structure ProofLayer where
  Sentence : Type
  truth : Sentence -> Prop
  Prf : Sentence -> Prop
  falsum : Sentence
  con : Sentence
  consistent : ¬ Prf falsum
  con_unprovable : ¬ Prf con
  productive : ∃ p : Sentence, Prf p

inductive FinalLanguage (L : ProofLayer) where
  | chamber : ExpandedInternalExpr -> FinalLanguage L
  | proof : L.Sentence -> FinalLanguage L

def finalDen (L : ProofLayer) : FinalLanguage L -> ExpandedState -> Prop
  | .chamber e, x => e.pred x
  | .proof p, _ => L.truth p

def finalPrf (L : ProofLayer) : FinalLanguage L -> Prop
  | .chamber _ => False
  | .proof p => L.Prf p

@[reducible] noncomputable def finalSystem (L : ProofLayer) : System :=
  { expandedSystemWithLanguage
      (FinalLanguage L)
      (finalDen L)
      (FinalLanguage.proof L.falsum)
      (FinalLanguage.proof L.con) with
    Prf := finalPrf L
    falsum := FinalLanguage.proof L.falsum
    con := FinalLanguage.proof L.con }

def canonicalB5 (S : System) : Prop :=
  Consistent S ∧ ¬ S.Prf S.con

def ProductiveProofSystem (S : System) : Prop :=
  ∃ p : S.Language, S.Prf p

/-! ## B5 itself, abstractly -/

theorem finalSystem_consistent (L : ProofLayer) :
    Consistent (finalSystem L) := by
  simpa [Consistent, finalSystem, finalPrf] using L.consistent

theorem finalSystem_cannot_prove_own_consistency (L : ProofLayer) :
    ¬ (finalSystem L).Prf (finalSystem L).con := by
  simpa [finalSystem, finalPrf] using L.con_unprovable

theorem finalSystem_satisfies_B5 (L : ProofLayer) :
    canonicalB5 (finalSystem L) :=
  ⟨finalSystem_consistent L,
    finalSystem_cannot_prove_own_consistency L⟩

theorem finalSystem_proof_layer_is_productive (L : ProofLayer) :
    ProductiveProofSystem (finalSystem L) := by
  obtain ⟨p, hp⟩ := L.productive
  exact ⟨FinalLanguage.proof p, hp⟩

theorem finalSystem_proof_layer_is_not_mute (L : ProofLayer) :
    ¬ (∀ p : (finalSystem L).Language,
      ¬ (finalSystem L).Prf p) := by
  intro hm
  obtain ⟨p, hp⟩ := finalSystem_proof_layer_is_productive L
  exact hm p hp

/-! ## The old dynamical constraints transport definitionally

Each `change` below asks Lean to check definitional equality for the particular
predicate being transported.  These predicates use unchanged state/dynamical
fields.  This is not an equality of the two Systems, and it does not transport
language-sensitive constraints wholesale.  In particular, B3, B5, B7, B10 and
B11 are handled separately below.  Avoid broad simplification of product-state
quantifiers merely to expose the same unchanged projections.
-/

theorem finalSystem_satisfies_B1 (L : ProofLayer) :
    canonicalB1 (finalSystem L) := by
  change canonicalB1 expandedSystem
  exact expanded_satisfies_B1

theorem finalSystem_satisfies_B2 (L : ProofLayer) :
    canonicalB2 (finalSystem L) := by
  change canonicalB2 expandedSystem
  exact expanded_satisfies_B2

theorem finalSystem_satisfies_B4 (L : ProofLayer) :
    canonicalB4 (finalSystem L) := by
  change canonicalB4 expandedSystem
  exact expanded_satisfies_B4

theorem finalSystem_satisfies_B6 (L : ProofLayer) :
    canonicalB6 (finalSystem L) := by
  change canonicalB6 expandedSystem
  exact expanded_satisfies_B6

theorem finalSystem_satisfies_B8 (L : ProofLayer) :
    canonicalB8 (finalSystem L) := by
  change canonicalB8 expandedSystem
  exact expanded_satisfies_B8

theorem finalSystem_satisfies_B9 (L : ProofLayer) :
    canonicalB9 (finalSystem L) := by
  change canonicalB9 expandedSystem
  exact expanded_satisfies_B9

theorem finalSystem_satisfies_B12 (L : ProofLayer) :
    canonicalB12 (finalSystem L) := by
  change canonicalB12 expandedSystem
  exact expanded_satisfies_B12

/-! ## B10 survives because the Chamber-predicate sector remains present -/

theorem final_den_nontrivial (L : ProofLayer) :
    ∃ expression state,
      (finalSystem L).den expression state ∧
        ¬ (∀ other, (finalSystem L).den expression other) := by
  refine ⟨FinalLanguage.chamber makingModeExpr,
    makingState climbProblem start124 (0 : Seat), ?_, ?_⟩
  · rfl
  · intro hall
    have hbad := hall expandedStart
    change false = true at hbad
    cases hbad

theorem finalSystem_satisfies_B10 (L : ProofLayer) :
    canonicalB10 (finalSystem L) := by
  refine ⟨expandedStep_injective,
    final_den_nontrivial L,
    ?_, ?_, ?_⟩
  · simpa [finalSystem] using expanded_clock_reveals_next_observation
  · simpa [finalSystem] using expanded_possibilities_persist
  · simpa [finalSystem] using expanded_two_possibilities_remain

/-! ## B7 shares the same non-mute consistent proof layer -/

theorem final_step_refers_to_output
    (L : ProofLayer) (x : ExpandedState) :
    (finalSystem L).refersToOutput x ((finalSystem L).outputStep x) := by
  simpa [finalSystem] using expanded_step_refers_to_output x

theorem finalSystem_satisfies_B7 (L : ProofLayer) :
    canonicalB7 (finalSystem L) := by
  exact ⟨⟨expandedStart⟩,
    finalSystem_consistent L,
    final_step_refers_to_output L,
    expandedStep_changes_state⟩

/-! ## Point-independent proof sentences cannot collapse B3 -/

theorem makingHaltingInvariant_not_false :
    makingHaltingInvariant ≠ (fun _ => False) := by
  intro h
  apply makingHaltingInvariant_not_computable
  rw [h]
  exact false_expanded_property_computable

theorem makingHaltingInvariant_not_true :
    makingHaltingInvariant ≠ (fun _ => True) := by
  intro h
  apply makingHaltingInvariant_not_computable
  rw [h]
  exact true_expanded_property_computable

theorem no_final_expression_names_making_source
    (L : ProofLayer) :
    ¬ (∃ expression : FinalLanguage L,
      Denotes (finalSystem L) expression makingHaltingInvariant) := by
  classical
  rintro ⟨expression, hden⟩
  cases expression with
  | chamber e =>
      have heq : e.pred = makingHaltingInvariant := by
        funext x
        apply propext
        exact hden x
      apply makingHaltingInvariant_not_computable
      rw [← heq]
      exact e.computable
  | proof p =>
      by_cases hp : L.truth p
      · apply makingHaltingInvariant_not_true
        funext x
        apply propext
        constructor
        · intro _
          trivial
        · intro _
          exact (hden x).mp hp
      · apply makingHaltingInvariant_not_false
        funext x
        apply propext
        constructor
        · intro hx
          exact False.elim (hp ((hden x).mpr hx))
        · intro hx
          exact False.elim hx

theorem finalSystem_satisfies_B3 (L : ProofLayer) :
    canonicalB3 (finalSystem L) := by
  refine ⟨makingHaltingInvariant,
    ?_, ?_, ?_, no_final_expression_names_making_source L⟩
  · change MapInvariant expandedSystem makingHaltingInvariant
    exact makingHaltingInvariant_preserved
  · change BackwardStable expandedSystem makingHaltingInvariant
    exact makingHaltingInvariant_backward
  · exact ⟨false, makingWitness,
      making_witness_recognised_and_usable.1,
      making_witness_recognised_and_usable.2.1,
      making_witness_recognised_and_usable.2.2⟩

/-! ## Point-independent proof sentences cannot collapse B11 -/

theorem no_final_expression_names_global_halting
    (L : ProofLayer) :
    ¬ (∃ expression : FinalLanguage L,
      Denotes (finalSystem L) expression expandedHelixInvariant) := by
  classical
  rintro ⟨expression, hden⟩
  cases expression with
  | chamber e =>
      have heq : e.pred = expandedHelixInvariant := by
        funext x
        apply propext
        exact hden x
      apply expandedHelixInvariant_not_computable
      rw [← heq]
      exact e.computable
  | proof p =>
      by_cases hp : L.truth p
      · apply expandedHelixInvariant_not_true
        funext x
        apply propext
        constructor
        · intro _
          trivial
        · intro _
          exact (hden x).mp hp
      · apply expandedHelixInvariant_not_false
        funext x
        apply propext
        constructor
        · intro hx
          exact False.elim (hp ((hden x).mpr hx))
        · intro hx
          exact False.elim hx

theorem finalSystem_satisfies_B11 (L : ProofLayer) :
    canonicalB11 (finalSystem L) := by
  refine ⟨expandedHelixInvariant,
    ?_,
    expandedHelixInvariant_not_false,
    expandedHelixInvariant_not_true,
    no_final_expression_names_global_halting L⟩
  change MapInvariant expandedSystem expandedHelixInvariant
  exact expandedHelixInvariant_preserved

/-! ## Structural all-twelve theorem -/

theorem ALL_TWELVE_from_any_B5_proof_layer (L : ProofLayer) :
    canonicalB1 (finalSystem L) ∧
    canonicalB2 (finalSystem L) ∧
    canonicalB3 (finalSystem L) ∧
    canonicalB4 (finalSystem L) ∧
    canonicalB5 (finalSystem L) ∧
    canonicalB6 (finalSystem L) ∧
    canonicalB7 (finalSystem L) ∧
    canonicalB8 (finalSystem L) ∧
    canonicalB9 (finalSystem L) ∧
    canonicalB10 (finalSystem L) ∧
    canonicalB11 (finalSystem L) ∧
    canonicalB12 (finalSystem L) ∧
    ProductiveProofSystem (finalSystem L) := by
  exact ⟨finalSystem_satisfies_B1 L,
    finalSystem_satisfies_B2 L,
    finalSystem_satisfies_B3 L,
    finalSystem_satisfies_B4 L,
    finalSystem_satisfies_B5 L,
    finalSystem_satisfies_B6 L,
    finalSystem_satisfies_B7 L,
    finalSystem_satisfies_B8 L,
    finalSystem_satisfies_B9 L,
    finalSystem_satisfies_B10 L,
    finalSystem_satisfies_B11 L,
    finalSystem_satisfies_B12 L,
    finalSystem_proof_layer_is_productive L⟩

#print axioms finalSystem_satisfies_B5
#print axioms finalSystem_satisfies_B3
#print axioms finalSystem_satisfies_B7
#print axioms finalSystem_satisfies_B11
#print axioms ALL_TWELVE_from_any_B5_proof_layer

end TuringChamberB5AbstractLayer
