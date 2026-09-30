import FoundationStoneTest16BQ

/-!
# 16BR — Correctness of the supported statement-tree assembler

The source is exactly 16BO.finiteStep, and the target is exactly the linked
16BQ.macroProgram. Simulation is restricted to valid four-stack encodings;
the fifth counter is zero at every related boundary.

Verified with Lean 4.35.0-rc2 and Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55.
Imports unchanged 16BQ SHA-256:
45cdaabec157d4fa0027736ac0b51472db13e8548f5717297e183c70f7545f83.

Claims boundary:
* executable_respects and executable_halting_iff close the assembler's
  semantic seam on valid encoded source configurations.
* source_halts_iff_primitive composes this with the authenticated 16AH entry.
* sourceFiniteIndex supplies the previously missing executable index for any
  given list-code. Its support list is proved equal in membership to 16AN's
  support, not assumed to be a replacement for it.
* 16AH.universalListCode remains a fixed Classical.choose witness. This file
  does not extract a literal universal interpreter, serialize a program,
  prove the final packed-input reduction effective, or prove relay/helix
  undecidability. initialCounters is kept separate from that fixed witness;
  finiteSourceInit_counters proves their semantic agreement.

Indexing provenance: Fin.sum is Batteries/Data/Fin/Basic.lean;
Fin.encodeSigma, Fin.decodeSigma and their two inverse theorems are
Batteries/Data/Fin/Coding.lean, imported by pinned Mathlib, not Chamber axioms.
-/
namespace FoundationStoneTest16BR
open Turing Turing.PartrecToTM2
open FoundationStoneTest16BQ FoundationStoneTest16BP FoundationStoneTest16AY

@[simp] theorem focus_append {s : ExactStmt} (p : StmtPos s)
    (r : StmtPos (focus p)) : focus (append p r) = focus r := by
  induction p with
  | root => rfl
  | pushNext p ih => exact ih r
  | peekNext p ih => exact ih r
  | popNext p ih => exact ih r
  | loadNext p ih => exact ih r
  | branchLeft p ih => exact ih r
  | branchRight p ih => exact ih r

theorem append_assoc {s : ExactStmt} (p : StmtPos s)
    (r : StmtPos (focus p)) (t : StmtPos (focus r)) :
    append p (append r t) = append (append p r)
      (cast (congrArg StmtPos (focus_append p r).symm) t) := by
  induction p with
  | root => rfl
  | pushNext p ih => exact congrArg StmtPos.pushNext (ih r t)
  | peekNext p ih => exact congrArg StmtPos.peekNext (ih r t)
  | popNext p ih => exact congrArg StmtPos.popNext (ih r t)
  | loadNext p ih => exact congrArg StmtPos.loadNext (ih r t)
  | branchLeft p ih => exact congrArg StmtPos.branchLeft (ih r t)
  | branchRight p ih => exact congrArg StmtPos.branchRight (ih r t)

theorem compiler_shift {K : Type} {F : Finset Λ'} {s : ExactStmt}
    (p : StmtPos s) (hs : TM2.SupportsStmt F s)
    (place : Option Γ' → StmtPos s → K)
    (finish : {q : Λ' // q ∈ F} → Option Γ' → K)
    (stop : Option Γ' → K) (bad : K)
    (r : StmtPos (focus p)) (v : Option Γ') :
    compileStmt (focus (append p r)) v (positionSupports hs (append p r))
      (fun v' t => place v' (append (append p r) t)) finish stop bad =
    compileStmt (focus r) v (positionSupports (positionSupports hs p) r)
      (fun v' t => place v' (append p (append r t))) finish stop bad := by
  induction p with
  | root => rfl
  | pushNext p ih => exact ih hs (fun v t => place v (.pushNext t)) r
  | peekNext p ih => exact ih hs (fun v t => place v (.peekNext t)) r
  | popNext p ih => exact ih hs (fun v t => place v (.popNext t)) r
  | loadNext p ih => exact ih hs (fun v t => place v (.loadNext t)) r
  | branchLeft p ih => exact ih hs.1 (fun v t => place v (.branchLeft t)) r
  | branchRight p ih => exact ih hs.2 (fun v t => place v (.branchRight t)) r

abbrev Stacks := K' → List Γ'
abbrev Cfg (c : Turing.ToPartrec.Code) := FoundationStoneTest16BO.FiniteCounterCfg c

def evalStmt (c : Turing.ToPartrec.Code) (s : ExactStmt)
    (hs : TM2.SupportsStmt (FoundationStoneTest16AN.support c) s)
    (v : Option Γ') (S : Stacks) : Cfg c :=
  FoundationStoneTest16BO.liftClosed c
    (FoundationStoneTest16AU.cstepAux s v (FoundationStoneTest16AT.encodeStacks S))
    (FoundationStoneTest16BO.cstepAux_closed c s hs v _)

theorem liftClosed_congr (c : Turing.ToPartrec.Code)
    {a b : FoundationStoneTest16AU.CounterCfg}
    (ha : FoundationStoneTest16BO.ClosedCfg c a)
    (hb : FoundationStoneTest16BO.ClosedCfg c b) (h : a = b) :
    FoundationStoneTest16BO.liftClosed c a ha =
      FoundationStoneTest16BO.liftClosed c b hb := by cases h; rfl

theorem evalStmt_push (c : Turing.ToPartrec.Code) (k f q v S)
    (hs : TM2.SupportsStmt (FoundationStoneTest16AN.support c) (.push k f q)) :
    evalStmt c (.push k f q) hs v S =
      evalStmt c q hs v (FoundationStoneTest16AT.pushAt S k (f v)) := by
  apply liftClosed_congr
  simp only [FoundationStoneTest16AU.cstepAux, FoundationStoneTest16AT.push_contract]

theorem evalStmt_peek (c : Turing.ToPartrec.Code) (k f q v S)
    (hs : TM2.SupportsStmt (FoundationStoneTest16AN.support c) (.peek k f q)) :
    evalStmt c (.peek k f q) hs v S =
      evalStmt c q hs (f v (S k).head?) S := by
  apply liftClosed_congr
  simp only [FoundationStoneTest16AU.cstepAux, FoundationStoneTest16AT.get_encode,
    FoundationStoneTest16AT.readTop_exact]

theorem evalStmt_pop (c : Turing.ToPartrec.Code) (k f q v S)
    (hs : TM2.SupportsStmt (FoundationStoneTest16AN.support c) (.pop k f q)) :
    evalStmt c (.pop k f q) hs v S =
      evalStmt c q hs (f v (S k).head?) (FoundationStoneTest16AT.popAt S k) := by
  apply liftClosed_congr
  simp only [FoundationStoneTest16AU.cstepAux, FoundationStoneTest16AT.get_encode,
    FoundationStoneTest16AT.readTop_exact, FoundationStoneTest16AT.pop_contract]

theorem evalStmt_branch (c : Turing.ToPartrec.Code) (test q₁ q₂ v S)
    (hs : TM2.SupportsStmt (FoundationStoneTest16AN.support c) (.branch test q₁ q₂)) :
    evalStmt c (.branch test q₁ q₂) hs v S =
      if test v then evalStmt c q₁ hs.1 v S else evalStmt c q₂ hs.2 v S := by
  cases ht : test v <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals apply liftClosed_congr; simp [FoundationStoneTest16AU.cstepAux, ht]

section Simulation
variable (c : Turing.ToPartrec.Code)
variable [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)]

abbrev P := macroProgram c
abbrev nextStep := step (linkedProgram (operationBlocks (P c)))
abbrev atOwner (k : AsmLabel c) (S : Stacks) :=
  entryState (P c) k (packCounters (FoundationStoneTest16AT.encodeStacks S))
def atCfg (s : Cfg c) :=
  entryState (P c) (entryOwner s.pc) (packCounters s.ctr)

def finish (q : FoundationStoneTest16AN.SupportedLabel c) (v : Option Γ') :=
  entryOwner (some q, v)
def stop (v : Option Γ') : AsmLabel c := entryOwner (none, v)

/-- All positions of a subtree have their expected installed instruction. -/
def Installed (s : ExactStmt)
    (hs : TM2.SupportsStmt (FoundationStoneTest16AN.support c) s)
    (place : Option Γ' → StmtPos s → AsmLabel c) : Prop :=
  ∀ v p, P c (place v p) =
    compileStmt (focus p) v (positionSupports hs p)
      (fun v' r => place v' (append p r)) (finish c) (stop c) trap

omit [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] in
theorem installed_shift {s : ExactStmt}
    (hs : TM2.SupportsStmt (FoundationStoneTest16AN.support c) s)
    (place : Option Γ' → StmtPos s → AsmLabel c)
    (hi : Installed c s hs place) (p : StmtPos s) :
    Installed c (focus p) (positionSupports hs p)
      (fun v r => place v (append p r)) := by
  intro v r
  exact (hi v (append p r)).trans (compiler_shift p hs place _ _ _ r v)

omit [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] in
theorem installed_program (q : FoundationStoneTest16AN.SupportedLabel c) :
    Installed c (FoundationStoneTest16BO.evaluatorProgram q.val)
      (FoundationStoneTest16AN.supported_statement_closed c q)
      (fun v p => placeOwner (q := q) (v := v) p) := by
  intro v p
  rfl

theorem set_get (C : FoundationStoneTest16AT.FiveCounters) (k : K') :
    FoundationStoneTest16AT.set C k (FoundationStoneTest16AT.get C k) = C := by
  cases k <;> rfl

theorem install_current (S : Stacks) (k : K') :
    FoundationStoneTest16BB.install (stackIndex k)
      (packCounters (FoundationStoneTest16AT.encodeStacks S))
      (FoundationStoneTest16AT.code (S k)) 0 =
    packCounters (FoundationStoneTest16AT.encodeStacks S) := by
  rw [install_pack_set, ← FoundationStoneTest16AT.get_encode, set_get]

theorem install_push (S : Stacks) (k : K') (g : Γ') :
    FoundationStoneTest16BB.install (stackIndex k)
      (packCounters (FoundationStoneTest16AT.encodeStacks S))
      (FoundationStoneTest16AI.pushCode (FoundationStoneTest16AT.digit g)
        (FoundationStoneTest16AT.code (S k))) 0 =
    packCounters (FoundationStoneTest16AT.encodeStacks
      (FoundationStoneTest16AT.pushAt S k g)) := by
  rw [install_pack_set, FoundationStoneTest16AT.push_contract,
    FoundationStoneTest16AT.get_encode]
  rfl

theorem install_pop (S : Stacks) (k : K') (g : Γ') (rest : List Γ')
    (hk : S k = g :: rest) :
    FoundationStoneTest16BB.install (stackIndex k)
      (packCounters (FoundationStoneTest16AT.encodeStacks S))
      (FoundationStoneTest16AT.code rest) 0 =
    packCounters (FoundationStoneTest16AT.encodeStacks
      (FoundationStoneTest16AT.popAt S k)) := by
  rw [install_pack_set, FoundationStoneTest16AT.pop_contract,
    FoundationStoneTest16AT.get_encode, hk, FoundationStoneTest16AT.pop_exact]

theorem popAt_empty (S : Stacks) (k : K') (hk : S k = []) :
    FoundationStoneTest16AT.popAt S k = S := by
  unfold FoundationStoneTest16AT.popAt
  have he : (S k).tail = S k := by rw [hk]; rfl
  rw [he, Function.update_eq_self]

theorem push_reaches (owner next bad : AsmLabel c) (k : K') (g : Γ')
    (hP : P c owner = .push (stackIndex k) (FoundationStoneTest16AT.digit g) next bad)
    (S : Stacks) :
    Relation.TransGen (fun u w => nextStep c u = some w)
      (atOwner c owner S)
      (atOwner c next (FoundationStoneTest16AT.pushAt S k g)) := by
  have h := primitive_push_reaches (P c) owner (stackIndex k)
    (FoundationStoneTest16AT.digit g) next bad hP
    (packCounters (FoundationStoneTest16AT.encodeStacks S))
    (FoundationStoneTest16AT.code (S k))
  rw [install_current, install_push] at h
  exact h

theorem pop_digit_reaches (owner empty bad : AsmLabel c) (k : K')
    (route : Digit → AsmLabel c)
    (hP : P c owner = .pop (stackIndex k) empty route bad)
    (S : Stacks) (g : Γ') (rest : List Γ') (hk : S k = g :: rest) :
    Relation.TransGen (fun u w => nextStep c u = some w)
      (atOwner c owner S)
      (atOwner c (route (FoundationStoneTest16AT.digit g))
        (FoundationStoneTest16AT.popAt S k)) := by
  have h := primitive_pop_digit_reaches (P c) owner (stackIndex k)
    empty bad route hP (packCounters (FoundationStoneTest16AT.encodeStacks S))
    (FoundationStoneTest16AT.digit g) (FoundationStoneTest16AT.code rest)
  have he : FoundationStoneTest16AI.pushCode (FoundationStoneTest16AT.digit g)
      (FoundationStoneTest16AT.code rest) = FoundationStoneTest16AT.code (S k) := by
    rw [hk]; rfl
  rw [he, install_current, install_pop S k g rest hk] at h
  exact h

theorem pop_empty_reaches (owner empty bad : AsmLabel c) (k : K')
    (route : Digit → AsmLabel c)
    (hP : P c owner = .pop (stackIndex k) empty route bad)
    (S : Stacks) (hk : S k = []) :
    Relation.TransGen (fun u w => nextStep c u = some w)
      (atOwner c owner S) (atOwner c empty S) := by
  have h := primitive_pop_empty_reaches (P c) owner (stackIndex k)
    empty bad route hP (packCounters (FoundationStoneTest16AT.encodeStacks S))
  have he : FoundationStoneTest16AT.code (S k) = 0 := by rw [hk]; rfl
  have hi := install_current S k
  rw [he] at hi
  rw [hi] at h
  exact h

theorem peek_digit_reaches (owner empty bad : AsmLabel c) (k : K')
    (route : Digit → AsmLabel c)
    (hP : P c owner = .peek (stackIndex k) empty route bad)
    (S : Stacks) (g : Γ') (rest : List Γ') (hk : S k = g :: rest) :
    Relation.TransGen (fun u w => nextStep c u = some w)
      (atOwner c owner S)
      (atOwner c (route (FoundationStoneTest16AT.digit g)) S) := by
  have h := primitive_peek_digit_reaches (P c) owner (stackIndex k)
    empty bad route hP (packCounters (FoundationStoneTest16AT.encodeStacks S))
    (FoundationStoneTest16AT.digit g) (FoundationStoneTest16AT.code rest)
  have he : FoundationStoneTest16AI.pushCode (FoundationStoneTest16AT.digit g)
      (FoundationStoneTest16AT.code rest) = FoundationStoneTest16AT.code (S k) := by
    rw [hk]; rfl
  rw [he, install_current] at h
  exact h

theorem peek_empty_reaches (owner empty bad : AsmLabel c) (k : K')
    (route : Digit → AsmLabel c)
    (hP : P c owner = .peek (stackIndex k) empty route bad)
    (S : Stacks) (hk : S k = []) :
    Relation.TransGen (fun u w => nextStep c u = some w)
      (atOwner c owner S) (atOwner c empty S) := by
  have h := primitive_peek_empty_reaches (P c) owner (stackIndex k)
    empty bad route hP (packCounters (FoundationStoneTest16AT.encodeStacks S))
  have he : FoundationStoneTest16AT.code (S k) = 0 := by rw [hk]; rfl
  have hi := install_current S k
  rw [he] at hi
  rw [hi] at h
  exact h

theorem route_reaches (owner next : AsmLabel c)
    (hP : P c owner = .loop next) (S : Stacks) :
    Relation.TransGen (fun u w => nextStep c u = some w)
      (atOwner c owner S) (atOwner c next S) := by
  have h := primitive_route_reaches (P c) owner next hP
    (packCounters (FoundationStoneTest16AT.encodeStacks S))
    (FoundationStoneTest16AT.code (S .main))
  change Relation.TransGen _
    (entryState _ _ (FoundationStoneTest16BB.install (stackIndex .main) _ _ _))
    (entryState _ _ (FoundationStoneTest16BB.install (stackIndex .main) _ _ _)) at h
  rw [install_current] at h
  exact h

/-- A complete source statement runs to the next source control entry.
The arbitrary starting owner is essential: load/branch are folded into its
instruction, so their recursive calls do not insert an artificial jump. -/
theorem statement_reaches (s : ExactStmt) :
    ∀ (hs : TM2.SupportsStmt (FoundationStoneTest16AN.support c) s)
      (place : Option Γ' → StmtPos s → AsmLabel c),
      Installed c s hs place → ∀ (v : Option Γ') (owner : AsmLabel c),
      P c owner = compileStmt s v hs place (finish c) (stop c) trap →
      ∀ S : Stacks,
      Relation.TransGen (fun u w => nextStep c u = some w)
        (atOwner c owner S) (atCfg c (evalStmt c s hs v S)) := by
  induction s with
  | push k f q ih =>
      intro hs place hi v owner hP S
      rw [evalStmt_push]
      have hiq := installed_shift c hs place hi (.pushNext (.root q))
      have hnext := ih hs (fun v' p => place v' (.pushNext p)) hiq v
        (place v (.pushNext (.root q))) (hiq v (.root q))
        (FoundationStoneTest16AT.pushAt S k (f v))
      exact (push_reaches c owner _ trap k (f v) hP S).trans hnext
  | peek k f q ih =>
      intro hs place hi v owner hP S
      rw [evalStmt_peek]
      have hiq := installed_shift c hs place hi (.peekNext (.root q))
      cases hk : S k with
      | nil =>
          simp only [List.head?_nil]
          exact (peek_empty_reaches c owner _ trap k _ hP S hk).trans
            (ih hs (fun v' p => place v' (.peekNext p)) hiq (f v none)
              _ (hiq (f v none) (.root q)) S)
      | cons g rest =>
          simp only [List.head?_cons]
          have hop := peek_digit_reaches c owner _ trap k _ hP S g rest hk
          simp only [FoundationStoneTest16AT.symbol_digit] at hop
          exact hop.trans
            (ih hs (fun v' p => place v' (.peekNext p)) hiq (f v (some g))
              _ (hiq (f v (some g)) (.root q)) S)
  | pop k f q ih =>
      intro hs place hi v owner hP S
      rw [evalStmt_pop]
      have hiq := installed_shift c hs place hi (.popNext (.root q))
      cases hk : S k with
      | nil =>
          simp only [List.head?_nil, popAt_empty S k hk]
          exact (pop_empty_reaches c owner _ trap k _ hP S hk).trans
            (ih hs (fun v' p => place v' (.popNext p)) hiq (f v none)
              _ (hiq (f v none) (.root q)) S)
      | cons g rest =>
          simp only [List.head?_cons]
          have hop := pop_digit_reaches c owner _ trap k _ hP S g rest hk
          simp only [FoundationStoneTest16AT.symbol_digit] at hop
          exact hop.trans
            (ih hs (fun v' p => place v' (.popNext p)) hiq (f v (some g))
              _ (hiq (f v (some g)) (.root q)) (FoundationStoneTest16AT.popAt S k))
  | load f q ih =>
      intro hs place hi v owner hP S
      have hiq := installed_shift c hs place hi (.loadNext (.root q))
      exact ih hs (fun v' p => place v' (.loadNext p)) hiq (f v) owner hP S
  | branch test q₁ q₂ ih₁ ih₂ =>
      intro hs place hi v owner hP S
      rw [evalStmt_branch]
      cases ht : test v
      · simp only [Bool.false_eq_true, ite_false]
        have hiq := installed_shift c hs place hi (.branchRight (.root q₂))
        apply ih₂ hs.2 (fun v' p => place v' (.branchRight p)) hiq v owner _ S
        simpa only [compileStmt_branch, ht, Bool.false_eq_true, ite_false] using hP
      · simp only [ite_true]
        have hiq := installed_shift c hs place hi (.branchLeft (.root q₁))
        apply ih₁ hs.1 (fun v' p => place v' (.branchLeft p)) hiq v owner _ S
        simpa only [compileStmt_branch, ht, ite_true] using hP
  | goto f =>
      intro hs place hi v owner hP S
      exact route_reaches c owner (finish c ⟨f v, hs v⟩ v) hP S
  | halt =>
      intro hs place hi v owner hP S
      exact route_reaches c owner (stop c v) hP S

def Valid (s : Cfg c) : Prop :=
  ∃ S : Stacks, s.ctr = FoundationStoneTest16AT.encodeStacks S

omit [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] in
theorem evalStmt_valid (s : ExactStmt)
    (hs : TM2.SupportsStmt (FoundationStoneTest16AN.support c) s)
    (v : Option Γ') (S : Stacks) : Valid c (evalStmt c s hs v S) := by
  refine ⟨(TM2.stepAux s v S).stk, ?_⟩
  have h := congrArg FoundationStoneTest16AU.CounterCfg.ctr
    (FoundationStoneTest16BO.erase_liftClosed c
      (FoundationStoneTest16AU.cstepAux s v (FoundationStoneTest16AT.encodeStacks S))
      (FoundationStoneTest16BO.cstepAux_closed c s hs v _))
  change (evalStmt c s hs v S).ctr = _ at h
  rw [FoundationStoneTest16AU.cstepAux_encode] at h
  exact h

def Encodes (s : Cfg c) (t : State 5 (Linked (P c))) : Prop :=
  Valid c s ∧ t = atCfg c s

/-- The semantic seam: the actual assembled primitive program respects
16BO's actual finiteStep on encoded stacks, including both halting cases. -/
theorem finite_respects_primitive :
    StateTransition.Respects (FoundationStoneTest16BO.finiteStep c)
      (nextStep c) (Encodes c) := by
  intro s t hst
  rcases hst with ⟨⟨S, hS⟩, rfl⟩
  rcases s with ⟨⟨q, v⟩, C⟩
  change C = _ at hS
  subst C
  cases q with
  | none =>
      change nextStep c (atCfg c ⟨(none, v), _⟩) = none
      simp [nextStep, atCfg, entryState, State.map, entry,
        linkedProgram, operationBlocks, entryCode, P, macroProgram,
        entryOwner, step, linkInstr, Instr.map]
  | some q =>
      change ∃ t, Encodes c (evalStmt c _
        (FoundationStoneTest16AN.supported_statement_closed c q) v S) t ∧ _
      refine ⟨_, ⟨evalStmt_valid c _ _ v S, rfl⟩, ?_⟩
      exact statement_reaches c _ _
        (fun v' p => placeOwner (q := q) (v := v') p)
        (installed_program c q) v (entryOwner (some q, v)) rfl S

def PrimitiveTerminates (s : Cfg c) : Prop :=
  (StateTransition.eval (nextStep c) (atCfg c s)).Dom

theorem halting_iff (s : Cfg c) (hs : Valid c s) :
    FoundationStoneTest16BO.FiniteTerminates c s ↔ PrimitiveTerminates c s := by
  exact (StateTransition.tr_eval_dom (finite_respects_primitive c) ⟨hs, rfl⟩).symm

theorem related_scratch_zero {s : Cfg c} {t : State 5 (Linked (P c))}
    (h : Encodes c s t) : t.counters FoundationStoneTest16BB.tempReg = 0 := by
  rcases h with ⟨_, rfl⟩
  rfl

#print axioms finite_respects_primitive
#print axioms halting_iff

end Simulation

/-! ## Explicit executable support enumeration

Finset.toList/equivFin would reintroduce choice. Instead the following lists
follow Mathlib's support construction and are proved to have exactly its
membership. Their order is irrelevant to semantics but explicit for indexing.
-/
open Turing.ToPartrec

def storeList : List (Option Γ') :=
  [none, some .consₗ, some .cons, some .bit0, some .bit1]

theorem mem_storeList (v : Option Γ') : v ∈ storeList := by
  cases v with
  | none => simp [storeList]
  | some g => cases g <;> simp [storeList]

def labelList : Λ' → List Λ'
  | Q@(.move _ _ _ q) => Q :: labelList q
  | Q@(.push _ _ q) => Q :: labelList q
  | Q@(.read q) => Q :: storeList.flatMap (fun v => labelList (q v))
  | Q@(.clear _ _ q) => Q :: labelList q
  | Q@(.copy q) => Q :: labelList q
  | Q@(.succ q) => Q :: unrev q :: labelList q
  | Q@(.pred q₁ q₂) => Q :: (labelList q₁ ++ unrev q₂ :: labelList q₂)
  | Q@(.ret _) => [Q]

theorem mem_labelList (q x : Λ') : x ∈ labelList q ↔ x ∈ trStmts₁ q := by
  induction q with
  | read f ih =>
      simp only [labelList, trStmts₁, List.mem_cons, List.mem_flatMap,
        Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
      simp only [mem_storeList, true_and, ih]
  | _ => simp_all [labelList, trStmts₁, or_left_comm]

def codeList : Code → Cont' → List Λ'
  | c@.zero', k => labelList (trNormal c k)
  | c@.succ, k => labelList (trNormal c k)
  | c@.tail, k => labelList (trNormal c k)
  | c@(.cons f fs), k =>
      labelList (trNormal c k) ++
      (codeList f (.cons₁ fs k) ++
      (labelList (move₂ (fun _ => false) .main .aux <|
        move₂ (fun s => s = Γ'.consₗ) .stack .main <|
        move₂ (fun _ => false) .aux .stack <| trNormal fs (.cons₂ k)) ++
      (codeList fs (.cons₂ k) ++ labelList (head .stack (.ret k)))))
  | c@(.comp f g), k =>
      labelList (trNormal c k) ++
      (codeList g (.comp f k) ++ (labelList (trNormal f k) ++ codeList f k))
  | c@(.case f g), k =>
      labelList (trNormal c k) ++ (codeList f k ++ codeList g k)
  | c@(.fix f), k =>
      labelList (trNormal c k) ++
      (codeList f (.fix f k) ++
      (labelList (.clear natEnd .main (trNormal f (.fix f k))) ++ [.ret k]))

theorem mem_codeList (c : Code) (k : Cont') (x : Λ') :
    x ∈ codeList c k ↔ x ∈ codeSupp' c k := by
  induction c generalizing k <;>
    simp_all only [codeList, codeSupp', List.mem_append, mem_labelList,
      Finset.mem_union, List.mem_singleton, Finset.mem_singleton]

def supportList (c : Code) : List Λ' := (codeList c .halt).dedup

theorem mem_supportList (c : Code) (q : Λ') :
    q ∈ supportList c ↔ q ∈ FoundationStoneTest16AN.support c := by
  simp [supportList, mem_codeList, FoundationStoneTest16AN.support, codeSupp, contSupp]

def supportedEquivList (c : Code) :
    FoundationStoneTest16AN.SupportedLabel c ≃ {q : Λ' // q ∈ supportList c} where
  toFun q := ⟨q.val, (mem_supportList c q.val).mpr q.property⟩
  invFun q := ⟨q.val, (mem_supportList c q.val).mp q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def supportedEquivFin (c : Code) :
    FoundationStoneTest16AN.SupportedLabel c ≃ Fin (supportList c).length :=
  (supportedEquivList c).trans
    (List.Nodup.getEquiv (supportList c) (List.nodup_dedup _)).symm

def symbolEquivFin : Γ' ≃ Fin 4 where
  toFun := FoundationStoneTest16AT.digit
  invFun := FoundationStoneTest16AT.symbol
  left_inv := FoundationStoneTest16AT.symbol_digit
  right_inv := FoundationStoneTest16AT.digit_symbol

def sourceEquivFin (c : Code) :
    SourceControl c ≃ Fin (((supportList c).length + 1) * 5) :=
  prodFinEquiv
    ((Equiv.optionCongr (supportedEquivFin c)).trans (finSuccEquiv _).symm)
    ((Equiv.optionCongr symbolEquivFin).trans (finSuccEquiv _).symm)

/-- An explicit alternative to 16AN's choice-based Fintype. -/
@[instance_reducible] def sourceFintype (c : Code) : Fintype (SourceControl c) :=
  Fintype.ofEquiv (Fin (((supportList c).length + 1) * 5)) (sourceEquivFin c).symm

@[instance_reducible] def sourceFiniteIndex (c : Code) : @FiniteIndex (SourceControl c) (sourceFintype c) := by
  letI := sourceFintype c
  exact ⟨(sourceEquivFin c).trans (finCongr (by
    simpa using (Fintype.card_congr (sourceEquivFin c)).symm))⟩

@[simp] theorem source_index_roundtrip (c : Code) (x : SourceControl c) :
    (sourceEquivFin c).symm (sourceEquivFin c x) = x :=
  (sourceEquivFin c).symm_apply_apply x

@[simp] theorem source_decode_roundtrip (c : Code)
    (i : Fin (((supportList c).length + 1) * 5)) :
    sourceEquivFin c ((sourceEquivFin c).symm i) = i :=
  (sourceEquivFin c).apply_symm_apply i

/-! ## The executable compiler: no remaining supplied indexing parameter -/
section Executable
attribute [local instance] sourceFintype sourceFiniteIndex

def executableBlocks (c : Code) : BlockFamily 5 (AsmLabel c) :=
  operationBlocks (macroProgram c)

abbrev ExecutableLabel (c : Code) := LinkedLabel (executableBlocks c)

def executableProgram (c : Code) : ExecutableLabel c → Instr 5 (ExecutableLabel c) :=
  linkedProgram (executableBlocks c)

def executableState (c : Code) (s : Cfg c) : State 5 (ExecutableLabel c) := atCfg c s

def ExecutableEncodes (c : Code) (s : Cfg c) (t : State 5 (ExecutableLabel c)) : Prop :=
  Valid c s ∧ t = executableState c s

theorem executable_respects (c : Code) :
    StateTransition.Respects (FoundationStoneTest16BO.finiteStep c)
      (step (executableProgram c)) (ExecutableEncodes c) :=
  finite_respects_primitive c

theorem executable_halting_iff (c : Code) (s : Cfg c) (hs : Valid c s) :
    FoundationStoneTest16BO.FiniteTerminates c s ↔
      (StateTransition.eval (step (executableProgram c)) (executableState c s)).Dom :=
  halting_iff c s hs

theorem executable_is_finite (c : Code) : Finite (ExecutableLabel c) := inferInstance

theorem executable_card (c : Code) :
    Fintype.card (ExecutableLabel c) =
      (ownerTotal c + 1) * (329 + (ownerTotal c + 1)) := by
  change Fintype.card (Linked (macroProgram c)) = _
  rw [assembled_control_card]
  congr 1
  omega

/-- The varying stack data is executable and does not refer to the chosen
universal list interpreter. The fixed control label is kept separate. -/
def initialStacks (d : Nat.Partrec.Code) : Stacks :=
  K'.elim (trList (FoundationStoneTest16AH.sourceTape d)) [] [] []

def initialCounters (d : Nat.Partrec.Code) : FoundationStoneTest16AT.FiveCounters :=
  FoundationStoneTest16AT.encodeStacks (initialStacks d)

theorem finiteSourceInit_counters (d : Nat.Partrec.Code) :
    (FoundationStoneTest16BO.finiteSourceInit d).ctr = initialCounters d := by
  have h := congrArg FoundationStoneTest16AU.CounterCfg.ctr
    (FoundationStoneTest16BO.erase_finiteSourceInit d)
  exact h

theorem finiteSourceInit_valid (d : Nat.Partrec.Code) :
    Valid FoundationStoneTest16AH.universalListCode
      (FoundationStoneTest16BO.finiteSourceInit d) :=
  ⟨initialStacks d, finiteSourceInit_counters d⟩

/-- Composes 16AH → 16AU → 16BO → the actual 16BQ primitive program.
This is a semantic statement about the fixed chosen universal interpreter;
it does not claim that Classical.choose in 16AH yields an evaluable literal. -/
theorem source_halts_iff_primitive (d : Nat.Partrec.Code) :
    FoundationStoneTest16AH.SourceHalts d ↔
      (StateTransition.eval
        (step (executableProgram FoundationStoneTest16AH.universalListCode))
        (executableState FoundationStoneTest16AH.universalListCode
          (FoundationStoneTest16BO.finiteSourceInit d))).Dom :=
  (FoundationStoneTest16BO.source_halts_iff_finite d).trans
    (executable_halting_iff _ _ (finiteSourceInit_valid d))

theorem turing_chamber_16BR_entry_certificate (d : Nat.Partrec.Code) :
    Valid FoundationStoneTest16AH.universalListCode
      (FoundationStoneTest16BO.finiteSourceInit d) ∧
    (FoundationStoneTest16BO.finiteSourceInit d).ctr = initialCounters d ∧
    (FoundationStoneTest16AH.SourceHalts d ↔
      (StateTransition.eval
        (step (executableProgram FoundationStoneTest16AH.universalListCode))
        (executableState FoundationStoneTest16AH.universalListCode
          (FoundationStoneTest16BO.finiteSourceInit d))).Dom) :=
  ⟨finiteSourceInit_valid d, finiteSourceInit_counters d,
    source_halts_iff_primitive d⟩

theorem turing_chamber_16BR_certificate (c : Code) :
    StateTransition.Respects (FoundationStoneTest16BO.finiteStep c)
      (step (executableProgram c)) (ExecutableEncodes c) ∧
    (∀ s, Valid c s → (FoundationStoneTest16BO.FiniteTerminates c s ↔
      (StateTransition.eval (step (executableProgram c)) (executableState c s)).Dom)) ∧
    BadTargetsLoop (macroProgram c) ∧ Finite (ExecutableLabel c) ∧
    (∀ q, q ∈ supportList c ↔ q ∈ FoundationStoneTest16AN.support c) :=
  ⟨executable_respects c, executable_halting_iff c,
    macroProgram_bad_targets_loop c, executable_is_finite c, mem_supportList c⟩

def smokeInstruction : Instr 5 (ExecutableLabel Code.zero') :=
  executableProgram Code.zero'
    (entry (executableBlocks Code.zero') (entryOwner (none, none)))

def smokeHalts (c : Code) (fuel : Nat) : Bool :=
  (run (executableProgram c) fuel
    (executableState c
      ⟨(some (FoundationStoneTest16AN.initialSupportedLabel c), none),
        FoundationStoneTest16AT.encodeStacks (fun _ => [])⟩)).isNone

-- Executable diagnostics, not replacements for the all-input theorems:
#eval ("zero support size", (supportList Code.zero').length)
#eval ("succ support size", (supportList Code.succ).length)
#eval ("halted owner emits halt", match smokeInstruction with | .halt => true | _ => false)
-- False means only that the bounded budget is exhausted, not divergence.
#eval ("zero program halts within 16 steps", smokeHalts Code.zero' 16)

end Executable

#check @StateTransition.Respects
#check @StateTransition.tr_eval_dom
#check @executable_respects
#check @source_halts_iff_primitive
#print axioms focus_append
#print axioms append_assoc
#print axioms compiler_shift
#print axioms statement_reaches
#print axioms mem_supportList
#print axioms source_index_roundtrip
#print axioms executable_respects
#print axioms executable_halting_iff
#print axioms source_halts_iff_primitive
#print axioms turing_chamber_16BR_certificate
#print axioms turing_chamber_16BR_entry_certificate

end FoundationStoneTest16BR
