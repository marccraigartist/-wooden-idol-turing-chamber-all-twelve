import FoundationStoneTest16AN
import FoundationStoneTest16AU
import FoundationStoneTest16AH

/-!
# THE TURING CHAMBER — TEST 16BO: FINITE SUPPORTED FIVE-COUNTER CONTROL

Lean 4.35.0-rc2 / pinned Mathlib.

16AU faithfully replaces Mathlib's four stacks by five natural-number
counters, but its ambient label type `PartrecToTM2.Λ'` is infinite and its
finite local store is still a separate field.  This file performs exactly the
missing restriction step.

For a fixed list-code `c`, 16AN supplies the closed finite support of the
Mathlib evaluator.  We replace an ambient active label by a member of that
support and fold `var : Option Γ'` into the finite control.  A distinguished
`none` label records explicit termination while retaining the local store.

The arithmetic is not reimplemented.  One finite-control step delegates to
16AU's `cstepAux`; support closure proves that its successor can be lifted back
into the finite control.  Lean then certifies a `StateTransition.Respects`
refinement and exact halting equivalence.
-/

namespace FoundationStoneTest16BO

open Turing
open Turing.PartrecToTM2

abbrev ExactStmt := FoundationStoneTest16AU.ExactStmt
abbrev FiveCounters := FoundationStoneTest16AT.FiveCounters

/-- The Mathlib evaluator with its opaque `Stmt'` wrapper exposed at the exact
statement type consumed by 16AU. -/
def evaluatorProgram : Λ' → ExactStmt := fun q => Turing.PartrecToTM2.tr q

/-- Active supported labels, plus the explicit halted label, with the finite
TM2 local store folded into the program counter. -/
abbrev FiniteControl (c : Turing.ToPartrec.Code) :=
  Option (FoundationStoneTest16AN.SupportedLabel c) × Option Γ'

theorem finite_control_is_finite (c : Turing.ToPartrec.Code) :
    Finite (FiniteControl c) := inferInstance

theorem finite_control_nonempty (c : Turing.ToPartrec.Code) :
    Nonempty (FiniteControl c) :=
  ⟨(some (FoundationStoneTest16AN.initialSupportedLabel c), none)⟩

/-- Folding the four-symbol optional local store multiplies the supported
label control by exactly five; the extra `Option` on labels is the explicit
halted control. -/
theorem finite_control_card (c : Turing.ToPartrec.Code) :
    Fintype.card (FiniteControl c) =
      (Fintype.card (FoundationStoneTest16AN.SupportedLabel c) + 1) * 5 := by
  change Fintype.card
      (Option (FoundationStoneTest16AN.SupportedLabel c) × Option Γ') = _
  rw [Fintype.card_prod, Fintype.card_option, Fintype.card_option]
  norm_num [show Fintype.card Γ' = 4 by decide]

/-- Five arithmetic counters whose entire non-arithmetic state is finite
control. -/
structure FiniteCounterCfg (c : Turing.ToPartrec.Code) where
  pc : FiniteControl c
  ctr : FiveCounters

/-- Forget only the proof that an active label lies in the finite support.
The local store is retained. -/
def eraseCfg {c : Turing.ToPartrec.Code} (s : FiniteCounterCfg c) :
    FoundationStoneTest16AU.CounterCfg :=
  ⟨s.pc.1.map Subtype.val, s.pc.2, s.ctr⟩

/-- A full five-counter configuration is closed when every active ambient
label it carries belongs to the fixed finite support. -/
def ClosedCfg (c : Turing.ToPartrec.Code)
    (s : FoundationStoneTest16AU.CounterCfg) : Prop :=
  ∀ q, s.l = some q → q ∈ FoundationStoneTest16AN.support c

/-- Closure of a statement is preserved by 16AU's exact arithmetic
execution. -/
theorem cstepAux_closed (c : Turing.ToPartrec.Code) (q : ExactStmt)
    (hq : Turing.TM2.SupportsStmt (FoundationStoneTest16AN.support c) q)
    (v : Option Γ') (C : FiveCounters) :
    ClosedCfg c (FoundationStoneTest16AU.cstepAux q v C) := by
  induction q generalizing v C with
  | push k f q ih =>
      exact ih hq v
        (FoundationStoneTest16AT.set C k
          (FoundationStoneTest16AT.pushCode (f v)
            (FoundationStoneTest16AT.get C k)))
  | peek k f q ih =>
      exact ih hq
        (f v (FoundationStoneTest16AT.readTop
          (FoundationStoneTest16AT.get C k))) C
  | pop k f q ih =>
      exact ih hq
        (f v (FoundationStoneTest16AT.readTop
          (FoundationStoneTest16AT.get C k)))
        (FoundationStoneTest16AT.set C k
          (FoundationStoneTest16AT.popCode
            (FoundationStoneTest16AT.get C k)))
  | load f q ih =>
      exact ih hq (f v) C
  | branch p q₁ q₂ ih₁ ih₂ =>
      simp only [FoundationStoneTest16AU.cstepAux]
      split
      · exact ih₁ hq.1 v C
      · exact ih₂ hq.2 v C
  | goto f =>
      intro target htarget
      simp only [FoundationStoneTest16AU.cstepAux] at htarget
      cases htarget
      exact hq v
  | halt =>
      intro target htarget
      simp only [FoundationStoneTest16AU.cstepAux] at htarget
      contradiction

/-- Lift a closed ambient configuration into the finite supported control. -/
def liftClosed (c : Turing.ToPartrec.Code)
    (s : FoundationStoneTest16AU.CounterCfg) (h : ClosedCfg c s) :
    FiniteCounterCfg c :=
  match hs : s.l with
  | none => ⟨(none, s.var), s.ctr⟩
  | some q => ⟨(some ⟨q, h q hs⟩, s.var), s.ctr⟩

theorem erase_liftClosed (c : Turing.ToPartrec.Code)
    (s : FoundationStoneTest16AU.CounterCfg) (h : ClosedCfg c s) :
    eraseCfg (liftClosed c s h) = s := by
  cases s with
  | mk l v C =>
      cases l <;> rfl

/-- A `goto` target is selected from the current folded local store before
the successor control is constructed.  It is not deferred to a later step. -/
theorem goto_is_folded_at_current_var (c : Turing.ToPartrec.Code)
    (f : Option Γ' → Λ')
    (hf : ∀ v, f v ∈ FoundationStoneTest16AN.support c)
    (v : Option Γ') (C : FiveCounters) :
    liftClosed c
      (FoundationStoneTest16AU.cstepAux (.goto f) v C)
      (cstepAux_closed c (.goto f) hf v C) =
      ⟨(some ⟨f v, hf v⟩, v), C⟩ := by
  rfl

/-- The finite-control version of 16AU's macro five-counter transition. -/
def finiteStep (c : Turing.ToPartrec.Code) :
    FiniteCounterCfg c → Option (FiniteCounterCfg c)
  | ⟨(none, _), _⟩ => none
  | ⟨(some q, v), C⟩ =>
      let next := FoundationStoneTest16AU.cstepAux (evaluatorProgram q.val) v C
      some (liftClosed c next
        (cstepAux_closed c (evaluatorProgram q.val)
          (FoundationStoneTest16AN.supported_statement_closed c q) v C))

def Encodes (c : Turing.ToPartrec.Code)
    (s : FoundationStoneTest16AU.CounterCfg) (t : FiniteCounterCfg c) : Prop :=
  eraseCfg t = s

/-- Restricting to supported finite control changes neither the arithmetic nor
the transition semantics. -/
theorem counter_respects_finite (c : Turing.ToPartrec.Code) :
    StateTransition.Respects
      (FoundationStoneTest16AU.cstep evaluatorProgram)
      (finiteStep c) (Encodes c) := by
  intro s t hst
  subst s
  cases t with
  | mk pc C =>
      rcases pc with ⟨l, v⟩
      cases l with
      | none => rfl
      | some q =>
          let next := FoundationStoneTest16AU.cstepAux (evaluatorProgram q.val) v C
          let hclosed := cstepAux_closed c (evaluatorProgram q.val)
            (FoundationStoneTest16AN.supported_statement_closed c q) v C
          refine ⟨liftClosed c next hclosed, ?_, Relation.TransGen.single rfl⟩
          exact erase_liftClosed c next hclosed

def CounterTerminates (s : FoundationStoneTest16AU.CounterCfg) : Prop :=
  (StateTransition.eval
    (FoundationStoneTest16AU.cstep evaluatorProgram) s).Dom

def FiniteTerminates (c : Turing.ToPartrec.Code)
    (s : FiniteCounterCfg c) : Prop :=
  (StateTransition.eval (finiteStep c) s).Dom

theorem finite_halting_iff (c : Turing.ToPartrec.Code)
    (s : FiniteCounterCfg c) :
    CounterTerminates (eraseCfg s) ↔ FiniteTerminates c s := by
  unfold CounterTerminates FiniteTerminates
  exact (StateTransition.tr_eval_dom (counter_respects_finite c) rfl).symm

/-- The previous TM2-to-counter theorem composes with the finite restriction
without any new arithmetic assumptions. -/
def TM2Encodes (c : Turing.ToPartrec.Code)
    (s : PartrecToTM2.Cfg') (t : FiniteCounterCfg c) : Prop :=
  eraseCfg t = FoundationStoneTest16AU.encodeCfg s

/-- Exact halting equivalence from Mathlib TM2 to finite-control five-counter
macros, for every pair of related configurations. -/
theorem tm2_finite_halting_iff (c : Turing.ToPartrec.Code)
    (s : PartrecToTM2.Cfg') (t : FiniteCounterCfg c)
    (h : TM2Encodes c s t) :
    FoundationStoneTest16AU.TM2Terminates evaluatorProgram s ↔
      FiniteTerminates c t := by
  rw [FoundationStoneTest16AU.halting_iff evaluatorProgram s]
  rw [← h]
  exact finite_halting_iff c t

/-! ## The authenticated 16AH entry really is inside the restricted machine -/

theorem source_entry_closed (d : Nat.Partrec.Code) :
    ClosedCfg FoundationStoneTest16AH.universalListCode
      (FoundationStoneTest16AU.encodeCfg
        (FoundationStoneTest16AH.sourceInit d)) := by
  unfold ClosedCfg
  intro q hq
  rw [FoundationStoneTest16AH.sourceInit_fields] at hq
  change some (trNormal FoundationStoneTest16AH.universalListCode Cont'.halt) =
    some q at hq
  have hq' : q = trNormal FoundationStoneTest16AH.universalListCode Cont'.halt := by
    exact Option.some.inj hq.symm
  subst q
  exact (FoundationStoneTest16AN.initialSupportedLabel
    FoundationStoneTest16AH.universalListCode).property

noncomputable def finiteSourceInit (d : Nat.Partrec.Code) :
    FiniteCounterCfg FoundationStoneTest16AH.universalListCode :=
  liftClosed FoundationStoneTest16AH.universalListCode
    (FoundationStoneTest16AU.encodeCfg
      (FoundationStoneTest16AH.sourceInit d))
    (source_entry_closed d)

theorem erase_finiteSourceInit (d : Nat.Partrec.Code) :
    eraseCfg (finiteSourceInit d) =
      FoundationStoneTest16AU.encodeCfg
        (FoundationStoneTest16AH.sourceInit d) := by
  exact erase_liftClosed _ _ _

/-- The restricted finite-control machine starts from the exact authenticated
16AH entry and terminates precisely when the source code halts. -/
theorem source_halts_iff_finite (d : Nat.Partrec.Code) :
    FoundationStoneTest16AH.SourceHalts d ↔
      FiniteTerminates FoundationStoneTest16AH.universalListCode
        (finiteSourceInit d) := by
  rw [FoundationStoneTest16AH.source_halts_iff_tm2]
  change FoundationStoneTest16AU.TM2Terminates evaluatorProgram
      (FoundationStoneTest16AH.sourceInit d) ↔ _
  exact tm2_finite_halting_iff _ _ _ (erase_finiteSourceInit d)

/-! Red control: deleting the local store still collapses distinct finite
controls, even after the ambient label restriction. -/

def forgetStore {c : Turing.ToPartrec.Code} (x : FiniteControl c) := x.1

theorem forgetting_store_not_injective (c : Turing.ToPartrec.Code) :
    ¬ Function.Injective (@forgetStore c) := by
  intro h
  let q := FoundationStoneTest16AN.initialSupportedLabel c
  have he : forgetStore (some q, none) =
      forgetStore (some q, some Γ'.cons) := rfl
  have hp := h he
  have hs := congrArg Prod.snd hp
  simp at hs

theorem turing_chamber_16BO_certificate (c : Turing.ToPartrec.Code) :
    Finite (FiniteControl c) ∧
    Nonempty (FiniteControl c) ∧
    (Fintype.card (FiniteControl c) =
      (Fintype.card (FoundationStoneTest16AN.SupportedLabel c) + 1) * 5) ∧
    StateTransition.Respects
      (FoundationStoneTest16AU.cstep evaluatorProgram)
      (finiteStep c) (Encodes c) ∧
    (∀ s : FiniteCounterCfg c,
      CounterTerminates (eraseCfg s) ↔ FiniteTerminates c s) ∧
    (∀ (s : PartrecToTM2.Cfg') (t : FiniteCounterCfg c),
      TM2Encodes c s t →
      (FoundationStoneTest16AU.TM2Terminates evaluatorProgram s ↔
        FiniteTerminates c t)) ∧
    ¬ Function.Injective (@forgetStore c) :=
  ⟨finite_control_is_finite c, finite_control_nonempty c,
   finite_control_card c,
   counter_respects_finite c, finite_halting_iff c,
   tm2_finite_halting_iff c,
   forgetting_store_not_injective c⟩

/-- The specialised authenticated entry certificate used by the full
halting reduction. -/
theorem turing_chamber_16BO_entry_certificate :
    (∀ d : Nat.Partrec.Code,
      ClosedCfg FoundationStoneTest16AH.universalListCode
        (FoundationStoneTest16AU.encodeCfg
          (FoundationStoneTest16AH.sourceInit d))) ∧
    (∀ d : Nat.Partrec.Code,
      FoundationStoneTest16AH.SourceHalts d ↔
        FiniteTerminates FoundationStoneTest16AH.universalListCode
          (finiteSourceInit d)) :=
  ⟨source_entry_closed, source_halts_iff_finite⟩

#print axioms cstepAux_closed
#print axioms finite_control_card
#print axioms goto_is_folded_at_current_var
#print axioms counter_respects_finite
#print axioms finite_halting_iff
#print axioms tm2_finite_halting_iff
#print axioms source_entry_closed
#print axioms source_halts_iff_finite
#print axioms forgetting_store_not_injective
#print axioms turing_chamber_16BO_certificate
#print axioms turing_chamber_16BO_entry_certificate

end FoundationStoneTest16BO
