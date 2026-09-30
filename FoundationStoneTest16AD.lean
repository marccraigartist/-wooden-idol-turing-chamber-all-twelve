import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AD: THE DOOR AND THE MISSING SEAL

Mathlib / Lean 4.35.0-rc2.

Tests 16AB and 16AC establish two exact semantic bridges:

    standard MM2  ↔  Wooden Idol relay  ↔  two-body helix.

This file proves the metatheorem that makes those bridges computationally sharp.
If a source problem reduces to a target problem with an exact yes/no equivalence,
then a target decider would give a source decider.  Consequently undecidability
travels across the chamber in the forward direction.

Lean certifies:

1. exact semantic bridges compose;
2. Boolean decision procedures pull back across an exact bridge;
3. undecidability pushes forward across an exact bridge;
4. the two bridges AB and AC therefore transfer MM2-halting undecidability to
   helix-halting;
5. one-way soundness is not enough (red control);
6. naming the missing premise does not prove it: the chamber is Lean-sealed only
   after a Lean theorem establishing undecidability of the chosen standard MM2
   halting problem is supplied.

There are no custom axioms and no `sorry`.  The final theorem takes MM2
undecidability as a premise, visibly.  That premise is the outstanding Minsky port.
-/

namespace FoundationStoneTest16AD

/-- A Boolean program decides `P` when it returns true exactly on `P`. -/
def BoolDecidable {α : Type} (P : α → Prop) : Prop :=
  ∃ decideP : α → Bool, ∀ x, decideP x = true ↔ P x

/-- An exact many-one bridge: the source question and translated target question
have the same answer on every input. -/
structure ExactBridge {α β : Type} (P : α → Prop) (Q : β → Prop) where
  encode : α → β
  exact : ∀ x, P x ↔ Q (encode x)

/-- 1. Exact bridges compose. -/
def ExactBridge.comp {α β γ : Type} {P : α → Prop} {Q : β → Prop} {R : γ → Prop}
    (ab : ExactBridge P Q) (bc : ExactBridge Q R) : ExactBridge P R where
  encode := bc.encode ∘ ab.encode
  exact := fun x => (ab.exact x).trans (bc.exact (ab.encode x))

/-- 2. A target decider pulls back to a source decider. -/
theorem decider_pulls_back {α β : Type} {P : α → Prop} {Q : β → Prop}
    (bridge : ExactBridge P Q) : BoolDecidable Q → BoolDecidable P := by
  rintro ⟨decideQ, hQ⟩
  refine ⟨fun x => decideQ (bridge.encode x), fun x => ?_⟩
  exact (hQ (bridge.encode x)).trans (bridge.exact x).symm

/-- 3. Therefore source undecidability pushes forward to the target. -/
theorem undecidability_pushes_forward {α β : Type} {P : α → Prop} {Q : β → Prop}
    (bridge : ExactBridge P Q) (sourceUndecidable : ¬ BoolDecidable P) :
    ¬ BoolDecidable Q := by
  intro targetDecidable
  exact sourceUndecidable (decider_pulls_back bridge targetDecidable)

/-! ## The three chamber predicates are kept abstract here on purpose.

16AB supplies `mm2ToRelay` and its exact halting equivalence.
16AC supplies `relayToHelix` and its exact halting equivalence.
This theorem is their logical composition, independently checkable from the
operational details of either machine.
-/

variable {MM2Instance RelayInstance HelixInstance : Type}
variable (MM2Halts : MM2Instance → Prop)
variable (RelayHalts : RelayInstance → Prop)
variable (HelixHalts : HelixInstance → Prop)

/-- 4a. The two operational bridges make one exact chamber. -/
def chamberBridge
    (AB : ExactBridge MM2Halts RelayHalts)
    (AC : ExactBridge RelayHalts HelixHalts) :
    ExactBridge MM2Halts HelixHalts :=
  AB.comp AC

/-- 4b. The Turing transfer theorem.  The final hypothesis is precisely the theorem
that must be ported from a formal Minsky development (or proved directly in Lean). -/
theorem turing_chamber_transfer
    (AB : ExactBridge MM2Halts RelayHalts)
    (AC : ExactBridge RelayHalts HelixHalts)
    (mm2HaltingUndecidable : ¬ BoolDecidable MM2Halts) :
    ¬ BoolDecidable HelixHalts :=
  undecidability_pushes_forward (chamberBridge MM2Halts RelayHalts HelixHalts AB AC)
    mm2HaltingUndecidable

/-- The operational chamber can be closed without pretending that its source
undecidability theorem has already been proved in Lean. -/
structure OperationalChamber where
  AB : ExactBridge MM2Halts RelayHalts
  AC : ExactBridge RelayHalts HelixHalts

def OperationalChamber.fullBridge
    (c : OperationalChamber MM2Halts RelayHalts HelixHalts) :
    ExactBridge MM2Halts HelixHalts :=
  chamberBridge MM2Halts RelayHalts HelixHalts c.AB c.AC

/-- A sealed Turing chamber is an operational chamber plus the authentic source
undecidability theorem.  This definition prevents an operational green tick from
being reported as an undecidability green tick. -/
structure SealedTuringChamber extends
    OperationalChamber MM2Halts RelayHalts HelixHalts where
  sourceUndecidable : ¬ BoolDecidable MM2Halts

theorem sealed_chamber_has_undecidable_helix
    (c : SealedTuringChamber MM2Halts RelayHalts HelixHalts) :
    ¬ BoolDecidable HelixHalts :=
  turing_chamber_transfer MM2Halts RelayHalts HelixHalts c.toOperationalChamber.AB
    c.toOperationalChamber.AC c.sourceUndecidable

/-! ## Red control: one-way preservation cannot carry undecidability -/

/-- A merely sound translation only promises `P x → Q (f x)`. -/
structure SoundBridge {α β : Type} (P : α → Prop) (Q : β → Prop) where
  encode : α → β
  sound : ∀ x, P x → Q (encode x)

/-- Every predicate soundly maps into the constant-true target. -/
def toConstantTrue {α : Type} (P : α → Prop) : SoundBridge P (fun _ : Unit => True) where
  encode := fun _ => ()
  sound := fun _ _ => trivial

theorem constant_true_is_decidable : BoolDecidable (fun _ : Unit => True) := by
  exact ⟨fun _ => true, by intro; simp⟩

/-- 5. Red control: target decidability plus one-way soundness says nothing about
source decidability.  Exactness—not a suggestive simulation—is the load-bearing part. -/
theorem sound_bridge_red_control {α : Type} (P : α → Prop) :
    (∃ bridge : SoundBridge P (fun _ : Unit => True),
      BoolDecidable (fun _ : Unit => True)) :=
  ⟨toConstantTrue P, constant_true_is_decidable⟩

/-! ## A finite sanity check for the direction of transfer -/

def Even (n : Nat) : Prop := n % 2 = 0
def IsFalse (b : Bool) : Prop := b = false

def parityBridge : ExactBridge Even IsFalse where
  encode := fun n => decide (n % 2 ≠ 0)
  exact := by
    intro n
    simp only [Even, IsFalse]
    by_cases h : n % 2 = 0
    · simp [h]
    · have hlt : n % 2 < 2 := Nat.mod_lt _ (by decide)
      have hone : n % 2 = 1 := by omega
      simp [h, hone]

theorem finite_sanity_check : BoolDecidable Even :=
  decider_pulls_back parityBridge ⟨fun b => !b, by intro b; cases b <;> simp [IsFalse]⟩

theorem turing_chamber_16AD :
    (∀ {α β : Type} {P : α → Prop} {Q : β → Prop}
      (bridge : ExactBridge P Q), BoolDecidable Q → BoolDecidable P) ∧
    (∀ {α β : Type} {P : α → Prop} {Q : β → Prop}
      (bridge : ExactBridge P Q), ¬ BoolDecidable P → ¬ BoolDecidable Q) :=
  ⟨decider_pulls_back, undecidability_pushes_forward⟩

#print axioms ExactBridge.comp
#print axioms decider_pulls_back
#print axioms undecidability_pushes_forward
#print axioms chamberBridge
#print axioms turing_chamber_transfer
#print axioms sealed_chamber_has_undecidable_helix
#print axioms sound_bridge_red_control
#print axioms finite_sanity_check
#print axioms turing_chamber_16AD

end FoundationStoneTest16AD
