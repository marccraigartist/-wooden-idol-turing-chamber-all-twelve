import FoundationStoneTest16AT

/-!
# THE TURING CHAMBER — TEST 16AU: TM2 TO FIVE LOGICAL COUNTERS

Lean 4.35.0-rc2 / pinned Mathlib.  Depends on 16AT.

This is Layer A of the compiler.  It mirrors the exact constructors of
Mathlib's `TM2.Stmt` using arithmetic operations on the four base-five stack
counters.  The local store remains finite control; the fifth counter is zero
scratch at source-state boundaries.

Lean proves that encoding commutes with `TM2.stepAux` and with the complete
TM2 step function.  The resulting equality relation is a genuine
`StateTransition.Respects`, hence Mathlib lifts it to arbitrary-run halting
equivalence.

This layer uses macro arithmetic (`pushCode`, `popCode`, `readTop`).  Refining
those macros to primitive counter instructions is Layer B's remaining job.
-/

namespace FoundationStoneTest16AU

open Turing
open Turing.PartrecToTM2
open StateTransition

abbrev ExactStmt := TM2.Stmt (fun _ : K' => Γ') Λ' (Option Γ')

structure CounterCfg where
  l : Option Λ'
  var : Option Γ'
  ctr : FoundationStoneTest16AT.FiveCounters

def encodeCfg (c : PartrecToTM2.Cfg') : CounterCfg :=
  ⟨c.l, c.var, FoundationStoneTest16AT.encodeStacks c.stk⟩

/-- Arithmetic execution of the exact seven TM2 statement constructors. -/
def cstepAux : ExactStmt → Option Γ' →
    FoundationStoneTest16AT.FiveCounters → CounterCfg
  | .push k f q, v, C =>
      cstepAux q v (FoundationStoneTest16AT.set C k
        (FoundationStoneTest16AT.pushCode (f v) (FoundationStoneTest16AT.get C k)))
  | .peek k f q, v, C =>
      cstepAux q (f v (FoundationStoneTest16AT.readTop
        (FoundationStoneTest16AT.get C k))) C
  | .pop k f q, v, C =>
      cstepAux q (f v (FoundationStoneTest16AT.readTop
        (FoundationStoneTest16AT.get C k)))
        (FoundationStoneTest16AT.set C k
          (FoundationStoneTest16AT.popCode (FoundationStoneTest16AT.get C k)))
  | .load f q, v, C => cstepAux q (f v) C
  | .branch p q₁ q₂, v, C =>
      if p v then cstepAux q₁ v C else cstepAux q₂ v C
  | .goto f, v, C => ⟨some (f v), v, C⟩
  | .halt, v, C => ⟨none, v, C⟩

def cstep (M : Λ' → ExactStmt) : CounterCfg → Option CounterCfg
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, C⟩ => some (cstepAux (M l) v C)

theorem cstepAux_encode (q : ExactStmt) :
    ∀ (v : Option Γ') (S : ∀ _ : K', List Γ'),
      cstepAux q v (FoundationStoneTest16AT.encodeStacks S) =
        encodeCfg (TM2.stepAux q v S) := by
  induction q with
  | push k f q ih =>
      intro v S
      simp only [cstepAux, TM2.stepAux]
      rw [← FoundationStoneTest16AT.push_contract]
      exact ih v (FoundationStoneTest16AT.pushAt S k (f v))
  | peek k f q ih =>
      intro v S
      simp only [cstepAux, TM2.stepAux]
      rw [FoundationStoneTest16AT.get_encode, FoundationStoneTest16AT.readTop_exact]
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      intro v S
      simp only [cstepAux, TM2.stepAux]
      rw [FoundationStoneTest16AT.get_encode, FoundationStoneTest16AT.readTop_exact]
      have hp := FoundationStoneTest16AT.pop_contract S k
      rw [FoundationStoneTest16AT.get_encode] at hp
      rw [← hp]
      exact ih (f v (S k).head?) (FoundationStoneTest16AT.popAt S k)
  | load f q ih =>
      intro v S
      simp only [cstepAux, TM2.stepAux]
      exact ih (f v) S
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro v S
      simp only [cstepAux, TM2.stepAux]
      cases h : p v
      · simp only [h, Bool.false_eq_true, ite_false]
        exact ih₂ v S
      · simp only [h, ite_true]
        exact ih₁ v S
  | goto f => intro v S; rfl
  | halt => intro v S; rfl

theorem step_encode (M : Λ' → ExactStmt) (c : PartrecToTM2.Cfg') :
    cstep M (encodeCfg c) = (TM2.step M c).map encodeCfg := by
  cases c with
  | mk l v S =>
      cases l with
      | none => rfl
      | some l =>
          simp only [encodeCfg, cstep, TM2.step, Option.map_some]
          exact congrArg some (cstepAux_encode (M l) v S)

def Encodes (s : PartrecToTM2.Cfg') (t : CounterCfg) : Prop := encodeCfg s = t

theorem tm2_respects_five_counters (M : Λ' → ExactStmt) :
    StateTransition.Respects (TM2.step M) (cstep M) Encodes := by
  intro s t hst
  subst t
  cases hs : TM2.step M s with
  | none =>
      have h := step_encode M s
      change cstep M (encodeCfg s) = none
      calc
        cstep M (encodeCfg s) = (TM2.step M s).map encodeCfg := h
        _ = none := by rw [hs]; rfl
  | some s' =>
      refine ⟨encodeCfg s', rfl, ?_⟩
      apply Relation.TransGen.single
      have h := step_encode M s
      calc
        cstep M (encodeCfg s) = (TM2.step M s).map encodeCfg := h
        _ = some (encodeCfg s') := by rw [hs]; rfl

def TM2Terminates (M : Λ' → ExactStmt) (c : PartrecToTM2.Cfg') : Prop :=
  (StateTransition.eval (TM2.step M) c).Dom

def CounterTerminates (M : Λ' → ExactStmt) (c : CounterCfg) : Prop :=
  (StateTransition.eval (cstep M) c).Dom

theorem halting_iff (M : Λ' → ExactStmt) (c : PartrecToTM2.Cfg') :
    TM2Terminates M c ↔ CounterTerminates M (encodeCfg c) := by
  unfold TM2Terminates CounterTerminates
  exact (StateTransition.tr_eval_dom (tm2_respects_five_counters M) rfl).symm

/-! Red control: forgetting the finite local store does not define a faithful
configuration encoding. -/

def forgetVar (c : CounterCfg) : Option Λ' × FoundationStoneTest16AT.FiveCounters :=
  (c.l, c.ctr)

theorem forgetVar_collision (l : Option Λ')
    (C : FoundationStoneTest16AT.FiveCounters) :
    forgetVar ⟨l, none, C⟩ = forgetVar ⟨l, some .cons, C⟩ := rfl

theorem turing_chamber_16AU_certificate :
    (∀ q v S, cstepAux q v (FoundationStoneTest16AT.encodeStacks S) =
      encodeCfg (TM2.stepAux q v S)) ∧
    (∀ M c, TM2Terminates M c ↔ CounterTerminates M (encodeCfg c)) ∧
    (∀ l C, forgetVar ⟨l, none, C⟩ = forgetVar ⟨l, some .cons, C⟩) :=
  ⟨cstepAux_encode, halting_iff, forgetVar_collision⟩

#print axioms cstepAux_encode
#print axioms step_encode
#print axioms tm2_respects_five_counters
#print axioms halting_iff
#print axioms turing_chamber_16AU_certificate

end FoundationStoneTest16AU
