import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

/-!
# THE TURING CHAMBER — TEST 16AE: THE AUTHENTIC SOURCE SEAL

Lean 4.35.0-rc2 / Mathlib.

This test repairs an important boundary in 16AD.  Merely exhibiting a function
`α → Bool` does not show that the function is computable: it may be an oracle.
The authentic notion is Mathlib's `ComputablePred`, and the authentic bridge is
a computable many-one reduction `≤₀`.

Lean certifies:

1. Mathlib's partial-recursive halting predicate at input zero is not computable.
2. Computable exact bridges compose.
3. If that source predicate reduces effectively through an MM2/relay layer and
   then through the helix layer, helix halting is not computable.
4. The final result has no undecidability premise: it consumes Mathlib's proved
   halting theorem directly.
5. Red control: classical logic can manufacture a Boolean halting oracle that is
   extensionally exact, but Lean proves that oracle is not computable.  Thus an
   exact Boolean table is not an effective compiler.

What remains deliberately visible: constructing the first effective bridge from
Mathlib's partial-recursive codes to the chosen standard two-counter/MM2 syntax.
Tests 16AB and 16AC prove the operational relay and helix bridges, but 16AE does
not pretend that the missing universality compiler has already been constructed.
-/

namespace FoundationStoneTest16AE

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- The authenticated source problem: does code `c` halt on input zero? -/
def SourceHalts (c : Code) : Prop := (eval c 0).Dom

/-- 1. Mathlib's genuine halting theorem, specialised to our source problem. -/
theorem source_halting_is_not_computable : ¬ ComputablePred SourceHalts := by
  exact ComputablePred.halting_problem 0

/-- A named wrapper for Mathlib's computable exact many-one reduction. -/
abbrev EffectiveExactBridge {α β : Type} [Primcodable α] [Primcodable β]
    (P : α → Prop) (Q : β → Prop) := P ≤₀ Q

/-- 2. Effective exact bridges compose, including computability of the composite
encoder—not merely extensional agreement. -/
theorem effective_bridges_compose
    {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    {P : α → Prop} {Q : β → Prop} {R : γ → Prop}
    (ab : EffectiveExactBridge P Q) (bc : EffectiveExactBridge Q R) :
    EffectiveExactBridge P R :=
  ab.trans bc

/-- A candidate Turing chamber must carry two *computable* exact translations. -/
structure EffectiveTuringChamber
    (RelayInstance HelixInstance : Type)
    [Primcodable RelayInstance] [Primcodable HelixInstance]
    (RelayHalts : RelayInstance → Prop) (HelixHalts : HelixInstance → Prop) where
  sourceToRelay : EffectiveExactBridge SourceHalts RelayHalts
  relayToHelix : EffectiveExactBridge RelayHalts HelixHalts

def EffectiveTuringChamber.fullBridge
    {RelayInstance HelixInstance : Type}
    [Primcodable RelayInstance] [Primcodable HelixInstance]
    {RelayHalts : RelayInstance → Prop} {HelixHalts : HelixInstance → Prop}
    (chamber : EffectiveTuringChamber RelayInstance HelixInstance RelayHalts HelixHalts) :
    EffectiveExactBridge SourceHalts HelixHalts :=
  effective_bridges_compose chamber.sourceToRelay chamber.relayToHelix

/-- 3–4. Once the effective operational bridges are supplied, the helix halting
problem is genuinely noncomputable.  No undecidability assumption appears here. -/
theorem authentic_turing_chamber
    {RelayInstance HelixInstance : Type}
    [Primcodable RelayInstance] [Primcodable HelixInstance]
    {RelayHalts : RelayInstance → Prop} {HelixHalts : HelixInstance → Prop}
    (chamber : EffectiveTuringChamber RelayInstance HelixInstance RelayHalts HelixHalts) :
    ¬ ComputablePred HelixHalts := by
  intro helixDecidable
  exact source_halting_is_not_computable
    (ComputablePred.computable_of_manyOneReducible chamber.fullBridge helixDecidable)

/-! ## The exact remaining compiler contract -/

/-- The source-to-MM2 object still owed by the programme.  Its `computable` field
is the crucial strengthening over an arbitrary encoding function. -/
structure PartrecToMM2Compiler
    (MM2Instance : Type) [Primcodable MM2Instance]
    (MM2Halts : MM2Instance → Prop) where
  compile : Code → MM2Instance
  computable : Computable compile
  correct : ∀ c, SourceHalts c ↔ MM2Halts (compile c)

def PartrecToMM2Compiler.bridge
    {MM2Instance : Type} [Primcodable MM2Instance]
    {MM2Halts : MM2Instance → Prop}
    (compiler : PartrecToMM2Compiler MM2Instance MM2Halts) :
    EffectiveExactBridge SourceHalts MM2Halts :=
  ⟨compiler.compile, compiler.computable, compiler.correct⟩

/-- Given the missing compiler plus the already-targeted MM2→relay and relay→helix
effective bridges, the complete chamber seals immediately. -/
theorem compiler_seals_the_chamber
    {MM2Instance RelayInstance HelixInstance : Type}
    [Primcodable MM2Instance] [Primcodable RelayInstance] [Primcodable HelixInstance]
    {MM2Halts : MM2Instance → Prop}
    {RelayHalts : RelayInstance → Prop}
    {HelixHalts : HelixInstance → Prop}
    (front : PartrecToMM2Compiler MM2Instance MM2Halts)
    (middle : EffectiveExactBridge MM2Halts RelayHalts)
    (back : EffectiveExactBridge RelayHalts HelixHalts) :
    ¬ ComputablePred HelixHalts := by
  let chamber : EffectiveTuringChamber RelayInstance HelixInstance RelayHalts HelixHalts :=
    ⟨front.bridge.trans middle, back⟩
  exact authentic_turing_chamber chamber

/-! ## Red control: an exact oracle is not a computable reduction -/

/-- Classical logic can answer the halting question extensionally.  This is an
oracle definition, not an algorithm. -/
noncomputable def haltingOracle (c : Code) : Bool :=
  @decide (SourceHalts c) (Classical.propDecidable _)

theorem haltingOracle_is_extensionally_exact (c : Code) :
    haltingOracle c = true ↔ SourceHalts c := by
  unfold haltingOracle
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- 5. Mathlib's halting theorem detects the cheat: the exact oracle is not a
computable function. -/
theorem haltingOracle_is_not_computable : ¬ Computable haltingOracle := by
  intro oracleComputable
  apply source_halting_is_not_computable
  rw [ComputablePred.computable_iff]
  refine ⟨haltingOracle, oracleComputable, ?_⟩
  funext c
  apply propext
  exact (haltingOracle_is_extensionally_exact c).symm

/-- The Boolean schema used in 16AD is therefore strictly weaker than an
effective decision procedure: its exact witness exists classically here, while
computability of that witness is refuted. -/
theorem exact_boolean_witness_without_algorithm :
    (∃ oracle : Code → Bool, ∀ c, oracle c = true ↔ SourceHalts c) ∧
    ¬ Computable haltingOracle := by
  exact ⟨⟨haltingOracle, haltingOracle_is_extensionally_exact⟩,
    haltingOracle_is_not_computable⟩

theorem turing_chamber_16AE_source_certificate :
    ¬ ComputablePred SourceHalts :=
  source_halting_is_not_computable

#print axioms source_halting_is_not_computable
#print axioms effective_bridges_compose
#print axioms authentic_turing_chamber
#print axioms PartrecToMM2Compiler.bridge
#print axioms compiler_seals_the_chamber
#print axioms haltingOracle_is_extensionally_exact
#print axioms haltingOracle_is_not_computable
#print axioms exact_boolean_witness_without_algorithm
#print axioms turing_chamber_16AE_source_certificate

end FoundationStoneTest16AE
