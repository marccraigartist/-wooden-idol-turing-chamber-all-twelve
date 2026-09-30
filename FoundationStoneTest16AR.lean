import Mathlib.Computability.Halting

/-!
# THE TURING CHAMBER — TEST 16AR: THE CLAIMS LOCK

Lean 4.35.0-rc2 / pinned Mathlib.

This file prevents the nearly-complete chamber from being overstated.  It
formalises the final composition theorem and isolates its one remaining input:
an effective, halting-preserving TM2-to-MM2 compiler.

Already certified elsewhere in the 16-series:

* authenticated Mathlib source halting iff the fixed evaluator TM2 halts (16AH);
* exact/effective MM2 -> relay -> helix translations (16AG, 16AF);
* injective stack and prime-exponent state encodings (16AI--16AM);
* finite supported control (16AN);
* literal prime division gate and effective packed input (16AO--16AP);
* Mathlib run lifting from `StateTransition.Respects` (16AQ).

Still not supplied: one value of 16AQ's `CompilerObligation` for every
statement of the supported Mathlib TM2.  Consequently this is a claims lock,
not a declaration that the Turing Chamber is finished.
-/

namespace FoundationStoneTest16AR

/-- A computable map carrying membership in `P` exactly to membership in `Q`. -/
structure ManyOne {A B : Type} [Primcodable A] [Primcodable B]
    (P : A → Prop) (Q : B → Prop) where
  map : A → B
  computable : Computable map
  correct : ∀ a, P a ↔ Q (map a)

def ManyOne.trans {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    {P : A → Prop} {Q : B → Prop} {R : C → Prop}
    (f : ManyOne P Q) (g : ManyOne Q R) : ManyOne P R where
  map := g.map ∘ f.map
  computable := g.computable.comp f.computable
  correct := fun a => (f.correct a).trans (g.correct (f.map a))

theorem target_computable_implies_source_computable
    {A B : Type} [Primcodable A] [Primcodable B]
    {P : A → Prop} {Q : B → Prop}
    (r : ManyOne P Q) (hQ : ComputablePred Q) : ComputablePred P := by
  classical
  rcases hQ with ⟨dQ, hQ⟩
  letI : DecidablePred Q := dQ
  letI : DecidablePred P := fun a => decidable_of_iff (Q (r.map a)) (r.correct a).symm
  apply Computable.computablePred
  have hc : Computable (fun a => decide (Q (r.map a))) := hQ.comp r.computable
  apply hc.of_eq
  intro a
  simp only [decide_eq_decide]
  exact (r.correct a).symm

theorem noncomputability_transfers
    {A B : Type} [Primcodable A] [Primcodable B]
    {P : A → Prop} {Q : B → Prop}
    (r : ManyOne P Q) (hP : ¬ ComputablePred P) : ¬ ComputablePred Q := by
  intro hQ
  exact hP (target_computable_implies_source_computable r hQ)

/-- The chamber's four doors.  The middle door is intentionally a field, not
an axiom hidden in a theorem. -/
structure ChamberChain
    {Source TM MM Relay Helix : Type}
    [Primcodable Source] [Primcodable TM] [Primcodable MM]
    [Primcodable Relay] [Primcodable Helix]
    (sourceHalts : Source → Prop) (tmHalts : TM → Prop)
    (mmHalts : MM → Prop) (relayHalts : Relay → Prop)
    (helixHalts : Helix → Prop) where
  source_to_tm : ManyOne sourceHalts tmHalts
  /-- This is the remaining TM2 -> MM2 theorem. -/
  tm_to_mm2 : ManyOne tmHalts mmHalts
  mm2_to_relay : ManyOne mmHalts relayHalts
  relay_to_helix : ManyOne relayHalts helixHalts

def ChamberChain.whole
    {Source TM MM Relay Helix : Type}
    [Primcodable Source] [Primcodable TM] [Primcodable MM]
    [Primcodable Relay] [Primcodable Helix]
    {sourceHalts : Source → Prop} {tmHalts : TM → Prop}
    {mmHalts : MM → Prop} {relayHalts : Relay → Prop}
    {helixHalts : Helix → Prop}
    (c : ChamberChain sourceHalts tmHalts mmHalts relayHalts helixHalts) :
    ManyOne sourceHalts helixHalts :=
  (((c.source_to_tm.trans c.tm_to_mm2).trans c.mm2_to_relay).trans c.relay_to_helix)

theorem completed_chamber_makes_helix_halting_noncomputable
    {Source TM MM Relay Helix : Type}
    [Primcodable Source] [Primcodable TM] [Primcodable MM]
    [Primcodable Relay] [Primcodable Helix]
    {sourceHalts : Source → Prop} {tmHalts : TM → Prop}
    {mmHalts : MM → Prop} {relayHalts : Relay → Prop}
    {helixHalts : Helix → Prop}
    (c : ChamberChain sourceHalts tmHalts mmHalts relayHalts helixHalts)
    (hsource : ¬ ComputablePred sourceHalts) :
    ¬ ComputablePred helixHalts :=
  noncomputability_transfers c.whole hsource

/-! Red control: mere computability of the maps is insufficient.  A constant
map can be computable while failing the semantic equivalence. -/

def badMap (_ : Nat) : Nat := 0

theorem badMap_computable : Computable badMap := Computable.const 0

theorem badMap_not_halting_reduction :
    ¬ ∀ n : Nat, (n = 1 ↔ badMap n = 1) := by
  intro h
  have := h 1
  simp [badMap] at this

/-- Final status theorem: supplying the missing middle reduction is exactly
what turns the already-proved front and tail into a full reduction. -/
def one_missing_door
    {Source TM MM Relay Helix : Type}
    [Primcodable Source] [Primcodable TM] [Primcodable MM]
    [Primcodable Relay] [Primcodable Helix]
    {sourceHalts : Source → Prop} {tmHalts : TM → Prop}
    {mmHalts : MM → Prop} {relayHalts : Relay → Prop}
    {helixHalts : Helix → Prop}
    (front : ManyOne sourceHalts tmHalts)
    (tail₁ : ManyOne mmHalts relayHalts)
    (tail₂ : ManyOne relayHalts helixHalts) :
    ManyOne tmHalts mmHalts → ManyOne sourceHalts helixHalts := by
  intro middle
  exact (front.trans middle).trans (tail₁.trans tail₂)

#print axioms ManyOne.trans
#print axioms target_computable_implies_source_computable
#print axioms noncomputability_transfers
#print axioms completed_chamber_makes_helix_halting_noncomputable
#print axioms one_missing_door

end FoundationStoneTest16AR
