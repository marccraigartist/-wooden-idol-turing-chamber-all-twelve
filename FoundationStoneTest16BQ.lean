import FoundationStoneTest16BO
import FoundationStoneTest16BP

/-!
# THE TURING CHAMBER — TEST 16BQ: SUPPORTED STATEMENT-TREE ASSEMBLER

Lean 4.35.0-rc2 / pinned Mathlib.

This file assembles 16BP's certified primitive stack operations behind the
seven constructors of each supported Mathlib `TM2.Stmt` tree.  `load` and
`branch` are folded while compiling because the local store is already part
of finite control.  `goto` uses 16BP's counter-preserving route constructor.
Only `push`, `pop` and `peek` enter arithmetic blocks.

Every statement occurrence has an explicit constructive finite index.  The
only remaining indexing parameter is the already-finite 16BO source control;
the caller supplies a `FiniteIndex` for it, which is exactly the data needed
by the following serialization pass.
-/

namespace FoundationStoneTest16BQ

open Turing
open Turing.PartrecToTM2
open FoundationStoneTest16AY
open FoundationStoneTest16BP

abbrev ExactStmt := FoundationStoneTest16AU.ExactStmt
abbrev FiveCounters := FoundationStoneTest16AT.FiveCounters
abbrev SourceControl (c : Turing.ToPartrec.Code) :=
  FoundationStoneTest16BO.FiniteControl c

/-! ## Finite positions in one statement tree -/

inductive StmtPos : ExactStmt → Type
  | root (s : ExactStmt) : StmtPos s
  | pushNext {k f q} : StmtPos q → StmtPos (.push k f q)
  | peekNext {k f q} : StmtPos q → StmtPos (.peek k f q)
  | popNext {k f q} : StmtPos q → StmtPos (.pop k f q)
  | loadNext {f q} : StmtPos q → StmtPos (.load f q)
  | branchLeft {p q₁ q₂} : StmtPos q₁ → StmtPos (.branch p q₁ q₂)
  | branchRight {p q₁ q₂} : StmtPos q₂ → StmtPos (.branch p q₁ q₂)

def posSize : ExactStmt → Nat
  | .push _ _ q => 1 + posSize q
  | .peek _ _ q => 1 + posSize q
  | .pop _ _ q => 1 + posSize q
  | .load _ q => 1 + posSize q
  | .branch _ q₁ q₂ => 1 + (posSize q₁ + posSize q₂)
  | .goto _ => 1
  | .halt => 1

theorem posSize_positive (s : ExactStmt) : 0 < posSize s := by
  cases s <;> simp [posSize]

def pushPosEquiv {k f q} :
    StmtPos (.push k f q) ≃ Unit ⊕ StmtPos q where
  toFun | .root _ => .inl () | .pushNext r => .inr r
  invFun | .inl _ => .root _ | .inr r => .pushNext r
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; rcases x with x | x <;> cases x <;> rfl

def peekPosEquiv {k f q} :
    StmtPos (.peek k f q) ≃ Unit ⊕ StmtPos q where
  toFun | .root _ => .inl () | .peekNext r => .inr r
  invFun | .inl _ => .root _ | .inr r => .peekNext r
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; rcases x with x | x <;> cases x <;> rfl

def popPosEquiv {k f q} :
    StmtPos (.pop k f q) ≃ Unit ⊕ StmtPos q where
  toFun | .root _ => .inl () | .popNext r => .inr r
  invFun | .inl _ => .root _ | .inr r => .popNext r
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; rcases x with x | x <;> cases x <;> rfl

def loadPosEquiv {f q} :
    StmtPos (.load f q) ≃ Unit ⊕ StmtPos q where
  toFun | .root _ => .inl () | .loadNext r => .inr r
  invFun | .inl _ => .root _ | .inr r => .loadNext r
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; rcases x with x | x <;> cases x <;> rfl

def branchPosEquiv {p q₁ q₂} :
    StmtPos (.branch p q₁ q₂) ≃ Unit ⊕ (StmtPos q₁ ⊕ StmtPos q₂) where
  toFun
    | .root _ => .inl ()
    | .branchLeft r => .inr (.inl r)
    | .branchRight r => .inr (.inr r)
  invFun
    | .inl _ => .root _
    | .inr (.inl r) => .branchLeft r
    | .inr (.inr r) => .branchRight r
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with x | x
    · cases x; rfl
    · rcases x with x | x <;> rfl

def gotoPosEquiv {f} : StmtPos (.goto f) ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => .root _
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; fin_cases x; rfl

def haltPosEquiv : StmtPos (.halt : ExactStmt) ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => .root _
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; fin_cases x; rfl

def posEquivFin : (s : ExactStmt) → StmtPos s ≃ Fin (posSize s)
  | .push _ _ q => pushPosEquiv.trans
      (sumFinEquiv unitEquivFinOne (posEquivFin q))
  | .peek _ _ q => peekPosEquiv.trans
      (sumFinEquiv unitEquivFinOne (posEquivFin q))
  | .pop _ _ q => popPosEquiv.trans
      (sumFinEquiv unitEquivFinOne (posEquivFin q))
  | .load _ q => loadPosEquiv.trans
      (sumFinEquiv unitEquivFinOne (posEquivFin q))
  | .branch p q₁ q₂ => branchPosEquiv.trans
      (sumFinEquiv unitEquivFinOne
        (sumFinEquiv (posEquivFin q₁) (posEquivFin q₂)))
  | .goto _ => gotoPosEquiv
  | .halt => haltPosEquiv

instance stmtPosFintype (s : ExactStmt) : Fintype (StmtPos s) :=
  Fintype.ofEquiv (Fin (posSize s)) (posEquivFin s).symm

instance stmtPosDecidableEq (s : ExactStmt) : DecidableEq (StmtPos s) :=
  (posEquivFin s).decidableEq

def focus : {s : ExactStmt} → StmtPos s → ExactStmt
  | s, .root _ => s
  | _, .pushNext p => focus p
  | _, .peekNext p => focus p
  | _, .popNext p => focus p
  | _, .loadNext p => focus p
  | _, .branchLeft p => focus p
  | _, .branchRight p => focus p

def append : {s : ExactStmt} → (p : StmtPos s) → StmtPos (focus p) → StmtPos s
  | _, .root _, r => r
  | _, .pushNext p, r => .pushNext (append p r)
  | _, .peekNext p, r => .peekNext (append p r)
  | _, .popNext p, r => .popNext (append p r)
  | _, .loadNext p, r => .loadNext (append p r)
  | _, .branchLeft p, r => .branchLeft (append p r)
  | _, .branchRight p, r => .branchRight (append p r)

@[simp] theorem append_root {s : ExactStmt} (p : StmtPos s) :
    append p (.root (focus p)) = p := by
  induction p with
  | root => rfl
  | pushNext p ih => change StmtPos.pushNext (append p (.root (focus p))) = _; rw [ih]
  | peekNext p ih => change StmtPos.peekNext (append p (.root (focus p))) = _; rw [ih]
  | popNext p ih => change StmtPos.popNext (append p (.root (focus p))) = _; rw [ih]
  | loadNext p ih => change StmtPos.loadNext (append p (.root (focus p))) = _; rw [ih]
  | branchLeft p ih => change StmtPos.branchLeft (append p (.root (focus p))) = _; rw [ih]
  | branchRight p ih => change StmtPos.branchRight (append p (.root (focus p))) = _; rw [ih]

/-! ## Closure and the recursive macro compiler -/

def positionSupports {S : Finset Λ'} {s : ExactStmt}
    (hs : Turing.TM2.SupportsStmt S s) :
    (p : StmtPos s) → Turing.TM2.SupportsStmt S (focus p)
  | .root _ => hs
  | @StmtPos.pushNext _ _ q p => positionSupports (s := q) hs p
  | @StmtPos.peekNext _ _ q p => positionSupports (s := q) hs p
  | @StmtPos.popNext _ _ q p => positionSupports (s := q) hs p
  | @StmtPos.loadNext _ q p => positionSupports (s := q) hs p
  | @StmtPos.branchLeft _ q₁ _ p => positionSupports (s := q₁) hs.1 p
  | @StmtPos.branchRight _ _ q₂ p => positionSupports (s := q₂) hs.2 p

def stackIndex : K' → StackReg
  | .main => 0
  | .rev => 1
  | .aux => 2
  | .stack => 3

/-- Compile one statement subtree.  The `place` map embeds its positions in
the global owner type; `finish` embeds supported `goto` destinations. -/
def compileStmt {K : Type} {S : Finset Λ'} :
    (s : ExactStmt) → (v : Option Γ') → Turing.TM2.SupportsStmt S s →
    (place : (v' : Option Γ') → StmtPos s → K) →
    (finish : {q : Λ' // q ∈ S} → Option Γ' → K) →
    (stop : Option Γ' → K) →
    (bad : K) → MacroInstr K
  | .push k f q, v, hs, place, finish, stop, bad =>
      .push (stackIndex k) (FoundationStoneTest16AT.digit (f v))
        (compileOwner place v (.pushNext (.root q))) bad
  | .peek k f q, v, hs, place, finish, stop, bad =>
      .peek (stackIndex k)
        (compileOwner place (f v none) (.peekNext (.root q)))
        (fun d => compileOwner place
          (f v (some (FoundationStoneTest16AT.symbol d)))
          (.peekNext (.root q))) bad
  | .pop k f q, v, hs, place, finish, stop, bad =>
      .pop (stackIndex k)
        (compileOwner place (f v none) (.popNext (.root q)))
        (fun d => compileOwner place
          (f v (some (FoundationStoneTest16AT.symbol d)))
          (.popNext (.root q))) bad
  | .load f q, v, hs, place, finish, stop, bad =>
      compileStmt q (f v) hs
        (fun v' p => place v' (.loadNext p)) finish stop bad
  | .branch test q₁ q₂, v, hs, place, finish, stop, bad =>
      if test v then
        compileStmt q₁ v hs.1
          (fun v' p => place v' (.branchLeft p)) finish stop bad
      else
        compileStmt q₂ v hs.2
          (fun v' p => place v' (.branchRight p)) finish stop bad
  | .goto f, v, hs, _, finish, _, _ => .loop (finish ⟨f v, hs v⟩ v)
  | .halt, v, _, _, _, stop, _ => .loop (stop v)
where
  compileOwner {s : ExactStmt}
      (place : (v' : Option Γ') → StmtPos s → K)
      (v' : Option Γ') (p : StmtPos s) : K := place v' p

@[simp] theorem compileStmt_push {K : Type} {S : Finset Λ'}
    (k f q v) (hs : Turing.TM2.SupportsStmt S (.push k f q))
    (place : (v' : Option Γ') → StmtPos (.push k f q) → K)
    (finish : {q : Λ' // q ∈ S} → Option Γ' → K)
    (stop : Option Γ' → K) (bad : K) :
    compileStmt (.push k f q) v hs place finish stop bad =
      .push (stackIndex k) (FoundationStoneTest16AT.digit (f v))
        (place v (.pushNext (.root q))) bad := rfl

@[simp] theorem compileStmt_pop {K : Type} {S : Finset Λ'}
    (k f q v) (hs : Turing.TM2.SupportsStmt S (.pop k f q))
    (place : (v' : Option Γ') → StmtPos (.pop k f q) → K)
    (finish : {q : Λ' // q ∈ S} → Option Γ' → K)
    (stop : Option Γ' → K) (bad : K) :
    compileStmt (.pop k f q) v hs place finish stop bad =
      .pop (stackIndex k)
        (place (f v none) (.popNext (.root q)))
        (fun d => place (f v (some (FoundationStoneTest16AT.symbol d)))
          (.popNext (.root q))) bad := rfl

@[simp] theorem compileStmt_peek {K : Type} {S : Finset Λ'}
    (k f q v) (hs : Turing.TM2.SupportsStmt S (.peek k f q))
    (place : (v' : Option Γ') → StmtPos (.peek k f q) → K)
    (finish : {q : Λ' // q ∈ S} → Option Γ' → K)
    (stop : Option Γ' → K) (bad : K) :
    compileStmt (.peek k f q) v hs place finish stop bad =
      .peek (stackIndex k)
        (place (f v none) (.peekNext (.root q)))
        (fun d => place (f v (some (FoundationStoneTest16AT.symbol d)))
          (.peekNext (.root q))) bad := rfl

@[simp] theorem compileStmt_load {K : Type} {S : Finset Λ'}
    (f q v) (hs : Turing.TM2.SupportsStmt S (.load f q))
    (place : (v' : Option Γ') → StmtPos (.load f q) → K)
    (finish : {q : Λ' // q ∈ S} → Option Γ' → K)
    (stop : Option Γ' → K) (bad : K) :
    compileStmt (.load f q) v hs place finish stop bad =
      compileStmt q (f v) hs
        (fun v' p => place v' (.loadNext p)) finish stop bad := rfl

@[simp] theorem compileStmt_branch {K : Type} {S : Finset Λ'}
    (test q₁ q₂ v) (hs : Turing.TM2.SupportsStmt S (.branch test q₁ q₂))
    (place : (v' : Option Γ') → StmtPos (.branch test q₁ q₂) → K)
    (finish : {q : Λ' // q ∈ S} → Option Γ' → K)
    (stop : Option Γ' → K) (bad : K) :
    compileStmt (.branch test q₁ q₂) v hs place finish stop bad =
      if test v then
        compileStmt q₁ v hs.1
          (fun v' p => place v' (.branchLeft p)) finish stop bad
      else
        compileStmt q₂ v hs.2
          (fun v' p => place v' (.branchRight p)) finish stop bad := rfl

@[simp] theorem compileStmt_goto {K : Type} {S : Finset Λ'}
    (f v) (hs : Turing.TM2.SupportsStmt S (.goto f))
    (place : (v' : Option Γ') → StmtPos (.goto f) → K)
    (finish : {q : Λ' // q ∈ S} → Option Γ' → K)
    (stop : Option Γ' → K) (bad : K) :
    compileStmt (.goto f) v hs place finish stop bad =
      .loop (finish ⟨f v, hs v⟩ v) := rfl

@[simp] theorem compileStmt_halt {K : Type} {S : Finset Λ'}
    (v) (hs : Turing.TM2.SupportsStmt S (.halt : ExactStmt))
    (place : (v' : Option Γ') → StmtPos (.halt : ExactStmt) → K)
    (finish : {q : Λ' // q ∈ S} → Option Γ' → K)
    (stop : Option Γ' → K) (bad : K) :
    compileStmt (.halt : ExactStmt) v hs place finish stop bad =
      .loop (stop v) := rfl

theorem compileStmt_bad_eq {K : Type} {S : Finset Λ'} :
    ∀ (s : ExactStmt) (v : Option Γ')
      (hs : Turing.TM2.SupportsStmt S s)
      (place : (v' : Option Γ') → StmtPos s → K)
      (finish : {q : Λ' // q ∈ S} → Option Γ' → K)
      (stop : Option Γ' → K)
      (bad found : K),
      badTarget (compileStmt s v hs place finish stop bad) = some found →
      found = bad := by
  intro s
  induction s with
  | push => intro; simp [compileStmt, badTarget]
  | peek => intro; simp [compileStmt, badTarget]
  | pop => intro; simp [compileStmt, badTarget]
  | load f q ih =>
      intro v hs place finish stop bad found h
      exact ih (f v) hs (fun v' p => place v' (.loadNext p))
        finish stop bad found h
  | branch test q₁ q₂ ih₁ ih₂ =>
      intro v hs place finish stop bad found h
      cases ht : test v
      · exact ih₂ v hs.2 (fun v' p => place v' (.branchRight p))
          finish stop bad found (by simpa [compileStmt, ht] using h)
      · exact ih₁ v hs.1 (fun v' p => place v' (.branchLeft p))
          finish stop bad found (by simpa [compileStmt, ht] using h)
  | goto => intro; simp [compileStmt, badTarget]
  | halt => intro; simp [compileStmt, badTarget]

theorem compileStmt_of_eq_halt {K : Type} {S : Finset Λ'}
    {s : ExactStmt} (h : s = .halt) (v : Option Γ')
    (hs : Turing.TM2.SupportsStmt S s)
    (place : (v' : Option Γ') → StmtPos s → K)
    (finish : {q : Λ' // q ∈ S} → Option Γ' → K)
    (stop : Option Γ' → K) (bad : K) :
    compileStmt s v hs place finish stop bad = .loop (stop v) := by
  subst s
  rfl

/-! ## The assembled finite owner space -/

def OwnerPos (c : Turing.ToPartrec.Code) : SourceControl c → Type
  | (none, _) => Unit
  | (some q, _) => StmtPos (FoundationStoneTest16BO.evaluatorProgram q.val)

def ownerSize (c : Turing.ToPartrec.Code) : SourceControl c → Nat
  | (none, _) => 1
  | (some q, _) => posSize (FoundationStoneTest16BO.evaluatorProgram q.val)

def ownerPosEquiv (c : Turing.ToPartrec.Code) (x : SourceControl c) :
    OwnerPos c x ≃ Fin (ownerSize c x) := by
  rcases x with ⟨q, v⟩
  cases q with
  | none => exact unitEquivFinOne
  | some q => exact posEquivFin (FoundationStoneTest16BO.evaluatorProgram q.val)

abbrev OwnerNode (c : Turing.ToPartrec.Code) := Σ x : SourceControl c, OwnerPos c x
abbrev AsmLabel (c : Turing.ToPartrec.Code) := Option (OwnerNode c)

def ownerTotal (c : Turing.ToPartrec.Code) [Fintype (SourceControl c)]
    [FiniteIndex (SourceControl c)] : Nat :=
  Fin.sum (fun i => ownerSize c (FiniteIndex.equivFin.symm i))

def sigmaFinEquiv {n : Nat} (f : Fin n → Nat) :
    ((i : Fin n) × Fin (f i)) ≃ Fin (Fin.sum f) where
  toFun := Fin.encodeSigma f
  invFun := Fin.decodeSigma f
  left_inv := Fin.decodeSigma_encodeSigma f
  right_inv := Fin.encodeSigma_decodeSigma f

def ownerNodeEquivFin (c : Turing.ToPartrec.Code)
    [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] :
    OwnerNode c ≃ Fin (ownerTotal c) :=
  (Equiv.sigmaCongr (FiniteIndex.equivFin (K := SourceControl c))
    (fun x => (ownerPosEquiv c x).trans <| finCongr <|
      congrArg (ownerSize c)
        (FiniteIndex.equivFin.symm_apply_apply x).symm)).trans
    (sigmaFinEquiv (fun i => ownerSize c (FiniteIndex.equivFin.symm i)))

def asmEquivFin (c : Turing.ToPartrec.Code)
    [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] :
    AsmLabel c ≃ Fin (ownerTotal c + 1) :=
  (Equiv.optionCongr (ownerNodeEquivFin c)).trans (finSuccEquiv _).symm

instance asmFintype (c : Turing.ToPartrec.Code)
    [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] :
    Fintype (AsmLabel c) :=
  Fintype.ofEquiv (Fin (ownerTotal c + 1)) (asmEquivFin c).symm

theorem asm_card (c : Turing.ToPartrec.Code)
    [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] :
    Fintype.card (AsmLabel c) = ownerTotal c + 1 := by
  simpa using Fintype.card_congr (asmEquivFin c)

instance asmFiniteIndex (c : Turing.ToPartrec.Code)
    [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] :
    FiniteIndex (AsmLabel c) where
  equivFin := (asmEquivFin c).trans (finCongr (asm_card c).symm)

def trap {c : Turing.ToPartrec.Code} : AsmLabel c := none

def entryOwner {c : Turing.ToPartrec.Code} : SourceControl c → AsmLabel c
  | (none, v) => some ⟨(none, v), ()⟩
  | (some q, v) => some ⟨(some q, v),
      .root (FoundationStoneTest16BO.evaluatorProgram q.val)⟩

def placeOwner {c : Turing.ToPartrec.Code} {q : FoundationStoneTest16AN.SupportedLabel c}
    {v : Option Γ'} (p : StmtPos (FoundationStoneTest16BO.evaluatorProgram q.val)) : AsmLabel c :=
  some ⟨(some q, v), p⟩

/-- The complete macro program.  `none` is the unique bad-route trap. -/
def macroProgram (c : Turing.ToPartrec.Code) : AsmLabel c → MacroInstr (AsmLabel c)
  | none => .loop none
  | some ⟨(none, _), _⟩ => .halt none
  | some ⟨(some q, v), p⟩ =>
      compileStmt (focus p) v
        (positionSupports
          (FoundationStoneTest16AN.supported_statement_closed c q) p)
        (fun v' r => placeOwner (q := q) (v := v') (append p r))
        (fun q' v' => entryOwner (some q', v'))
        (fun v' => entryOwner (none, v')) none

@[simp] theorem macroProgram_trap (c : Turing.ToPartrec.Code) :
    macroProgram c (trap : AsmLabel c) = .loop trap := rfl

theorem macroProgram_bad_targets_loop (c : Turing.ToPartrec.Code) :
    BadTargetsLoop (macroProgram c) := by
  intro owner bad hbad
  rcases owner with _ | ⟨⟨q, v⟩, p⟩
  · simp [macroProgram, badTarget] at hbad
  · cases q with
    | none => simp [macroProgram, badTarget] at hbad
    | some q =>
        have heq : bad = (none : AsmLabel c) := by
          apply compileStmt_bad_eq at hbad
          exact hbad
        subst bad
        exact macroProgram_trap c

@[simp] theorem macroProgram_halted (c : Turing.ToPartrec.Code) (v : Option Γ') :
    macroProgram c (entryOwner (none, v)) = .halt trap := rfl

theorem assembled_control_finite (c : Turing.ToPartrec.Code)
    [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] :
    Finite (Linked (macroProgram c)) := operation_control_is_finite (macroProgram c)

theorem assembled_control_card (c : Turing.ToPartrec.Code)
    [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] :
    Fintype.card (Linked (macroProgram c)) =
      (ownerTotal c + 1) * ((164 + (164 + (ownerTotal c + 1))) + 1) := by
  rw [operation_control_card, asm_card]

/-! ## Counter installation and counter-preserving routes -/

def packCounters (C : FiveCounters) : Reg5 → Nat
  | ⟨0, _⟩ => C.main
  | ⟨1, _⟩ => C.rev
  | ⟨2, _⟩ => C.aux
  | ⟨3, _⟩ => C.stack
  | ⟨4, _⟩ => 0

@[simp] theorem packCounters_temp (C : FiveCounters) :
    packCounters C FoundationStoneTest16BB.tempReg = 0 := rfl

theorem install_pack_set (C : FiveCounters) (k : K') (n : Nat) :
    FoundationStoneTest16BB.install (stackIndex k) (packCounters C) n 0 =
      packCounters (FoundationStoneTest16AT.set C k n) := by
  funext i
  fin_cases i <;> cases k <;>
    simp [FoundationStoneTest16BB.install, FoundationStoneTest16BB.stackReg,
      FoundationStoneTest16BB.tempReg, stackIndex, packCounters,
      FoundationStoneTest16AT.set]

/-- Unlike the dedicated trap lemma in 16BP, this route may end at a
different owner.  It is the counter-preserving instruction used for both
compiled `goto` and the final route into an explicit halted owner. -/
theorem primitive_route_reaches {K : Type} [Fintype K] [FiniteIndex K]
    (P : K → MacroInstr K) (owner next : K)
    (hP : P owner = .loop next) (base : Reg5 → Nat) (a : Nat) :
    Relation.TransGen
      (fun u v => step (linkedProgram (operationBlocks P)) u = some v)
      (entryState P owner
        (FoundationStoneTest16BB.install 0 base a 0))
      (entryState P next
        (FoundationStoneTest16BB.install 0 base a 0)) := by
  refine operation_reaches_of_run P owner (.loop next) hP ?_
    base 2 (by omega) a a next ?_
  · intro sink
    simp
  · simpa [operationEntry, operationExit] using
      FoundationStoneTest16BH.terminal_bridge
        (operationExit (.loop next)) (.pop .empty) a 0
        FoundationStoneTest16BH.pop_empty_terminal

theorem compiled_halt_routes_to_explicit_halt
    (c : Turing.ToPartrec.Code)
    [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)]
    (q : FoundationStoneTest16AN.SupportedLabel c) (v : Option Γ')
    (p : StmtPos (FoundationStoneTest16BO.evaluatorProgram q.val))
    (hfocus : focus p = (.halt : ExactStmt))
    (base : Reg5 → Nat) (a : Nat) :
    Relation.TransGen
      (fun u w => step (linkedProgram (operationBlocks (macroProgram c))) u = some w)
      (entryState (macroProgram c) (placeOwner (q := q) (v := v) p)
        (FoundationStoneTest16BB.install 0 base a 0))
      (entryState (macroProgram c) (entryOwner (none, v))
        (FoundationStoneTest16BB.install 0 base a 0)) := by
  apply primitive_route_reaches
  simp only [placeOwner, macroProgram]
  exact compileStmt_of_eq_halt hfocus _ _ _ _ _ _

structure AssemblyFacts (c : Turing.ToPartrec.Code)
    [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] : Prop where
  finiteOwners : Finite (AsmLabel c)
  finitePrimitiveControl : Finite (Linked (macroProgram c))
  exactOwnerCard : Fintype.card (AsmLabel c) = ownerTotal c + 1
  safeBadRoutes : BadTargetsLoop (macroProgram c)
  haltedOwnersAreExplicit : ∀ v,
    macroProgram c (entryOwner (none, v)) = .halt trap
  stackInstallExact : ∀ C k n,
    FoundationStoneTest16BB.install (stackIndex k) (packCounters C) n 0 =
      packCounters (FoundationStoneTest16AT.set C k n)
  operationSemantics : PrimitiveContracts

theorem turing_chamber_16BQ_certificate (c : Turing.ToPartrec.Code)
    [Fintype (SourceControl c)] [FiniteIndex (SourceControl c)] :
    AssemblyFacts c where
  finiteOwners := inferInstance
  finitePrimitiveControl := assembled_control_finite c
  exactOwnerCard := asm_card c
  safeBadRoutes := macroProgram_bad_targets_loop c
  haltedOwnersAreExplicit := macroProgram_halted c
  stackInstallExact := install_pack_set
  operationSemantics := primitive_contracts

#print axioms macroProgram_bad_targets_loop
#print axioms primitive_route_reaches
#print axioms compiled_halt_routes_to_explicit_halt
#print axioms turing_chamber_16BQ_certificate

end FoundationStoneTest16BQ
