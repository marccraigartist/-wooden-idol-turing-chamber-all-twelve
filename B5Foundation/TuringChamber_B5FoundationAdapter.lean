import TuringChamber_B5AbstractProofLayer
import B5FoundationArithmetic
import Mathlib

/-!
# THE TURING CHAMBER — GENUINE B5 FOUNDATION ADAPTER

Heavy proof-theory adapter, isolated from the main Chamber package.

The intended structural theorem says that ANY productive proof layer with
consistency and unprovability of its designated consistency sentence can be
attached to the eleven-way Chamber while preserving the named B1..B12
predicates.  The abstract theorem assumes these facts.

This file supplies the genuine arithmetic instance.

Sentence type: closed arithmetic sentences.
Proof predicate: IΣ₁ derivability.
Falsum: arithmetic bottom.
Consistency sentence: the actual internal IΣ₁ consistency sentence,
  (𝗜𝚺₁).consistent.val.

The arithmetic-only package checks the two B5 facts and productivity
before this combined adapter runs.  Both packages use the same pinned
Foundation revision.  Its public namespace is FFL, not the older LO namespace.

The `truth` field below intentionally retains the existing state-independent
provability interpretation.  It is not standard-model arithmetic truth.  The
Gödel-II fact comes from Foundation, not from that denotation field.

The final declaration is the all-twelve endpoint. It concerns the
explicitly attached arithmetic proof sector, not Gödel II derived from the
wheel geometry or an arithmetic proof checker executed by the Chamber.

No prime, RH, P-vs-NP, consciousness or physical-world claim is made here.
-/

open Function
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace TuringChamberB5FoundationAdapter

set_option autoImplicit false

open TuringChamberB5AbstractLayer

noncomputable def isigma1ProofLayer : ProofLayer where
  Sentence := ArithmeticSentence
  truth := fun sigma => 𝗜𝚺₁ ⊢ sigma
  Prf := fun sigma => 𝗜𝚺₁ ⊢ sigma
  falsum := (⊥ : ArithmeticSentence)
  con := (𝗜𝚺₁).consistent.val
  consistent := TuringChamberGodelArithmetic.isigma1_falsum_unprovable
  con_unprovable := TuringChamberGodelArithmetic.isigma1_consistency_unprovable
  productive := by
    exact ⟨(⊤ : ArithmeticSentence),
      TuringChamberGodelArithmetic.isigma1_verum_provable⟩

theorem adapter_falsum_is_arithmetic_bottom :
    isigma1ProofLayer.falsum = (⊥ : ArithmeticSentence) := rfl

theorem adapter_con_is_internal_isigma1_consistency :
    isigma1ProofLayer.con = (𝗜𝚺₁).consistent.val := rfl

theorem adapter_prf_is_actual_isigma1_derivability
    (sigma : ArithmeticSentence) :
    isigma1ProofLayer.Prf sigma ↔ 𝗜𝚺₁ ⊢ sigma := Iff.rfl

theorem adapter_is_consistent :
    ¬ isigma1ProofLayer.Prf isigma1ProofLayer.falsum :=
  isigma1ProofLayer.consistent

theorem adapter_cannot_prove_internal_consistency :
    ¬ isigma1ProofLayer.Prf isigma1ProofLayer.con :=
  isigma1ProofLayer.con_unprovable

theorem adapter_is_productive :
    ∃ sigma : isigma1ProofLayer.Sentence,
      isigma1ProofLayer.Prf sigma :=
  isigma1ProofLayer.productive

/--
The intended endpoint: genuine Gödel-II B5 instantiated into the structurally
integrated Chamber, yielding the named twelve constraints on one system.
-/
theorem GENUINE_GODEL_B5_ALL_TWELVE :
    TuringChamberB124OneSystem.canonicalB1
      (finalSystem isigma1ProofLayer) ∧
    TuringChamberB124OneSystem.canonicalB2
      (finalSystem isigma1ProofLayer) ∧
    TuringChamberB3ElevenWay.canonicalB3
      (finalSystem isigma1ProofLayer) ∧
    TuringChamberB124OneSystem.canonicalB4
      (finalSystem isigma1ProofLayer) ∧
    canonicalB5
      (finalSystem isigma1ProofLayer) ∧
    TuringChamberB124OneSystem.canonicalB6
      (finalSystem isigma1ProofLayer) ∧
    TuringChamberB124OneSystem.canonicalB7
      (finalSystem isigma1ProofLayer) ∧
    TuringChamberB124OneSystem.canonicalB8
      (finalSystem isigma1ProofLayer) ∧
    TuringChamberB124OneSystem.canonicalB9
      (finalSystem isigma1ProofLayer) ∧
    TuringChamberB124OneSystem.canonicalB10
      (finalSystem isigma1ProofLayer) ∧
    TuringChamberB124OneSystem.canonicalB11
      (finalSystem isigma1ProofLayer) ∧
    TuringChamberB124OneSystem.canonicalB12
      (finalSystem isigma1ProofLayer) ∧
    ProductiveProofSystem
      (finalSystem isigma1ProofLayer) := by
  exact ALL_TWELVE_from_any_B5_proof_layer isigma1ProofLayer

#print axioms adapter_is_consistent
#print axioms adapter_cannot_prove_internal_consistency
#print axioms adapter_is_productive
#print axioms GENUINE_GODEL_B5_ALL_TWELVE

end TuringChamberB5FoundationAdapter
