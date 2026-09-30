import FoundationStoneTest16BM

/-!
# THE TURING CHAMBER — TEST 16BN: FINITE CONTROL AT THE MM2 DOOR

Lean 4.35.0-rc2 / pinned Mathlib.

16BM proved the semantic compiler from a primitive five-counter machine to
two physical counters, but its convenient arithmetic labels contained `Nat`.
This file removes that infinity rather than calling it unreachable.

The five packed registers use only the primes 2, 3, 5, 7 and 11.  Therefore:

* multiplication needs at most the finite sites 0..11;
* division needs at most the finite scan/remainder sites 0..10;
* remainder restoration needs at most the finite sites 0..10.

`FiniteLabel L` records exactly those bounded phases.  If the source control
`L` is finite, the compiled two-counter control is a genuine `Fintype`.
The finite program is not a second arithmetic implementation: it is the 16BM
program transported through explicit embed/compress maps.  Lean proves that
every finite instruction expands back to the corresponding 16BM instruction,
then transports steps, bounded runs, the three exact compiled instruction
contracts, `StateTransition.Respects`, and halting equivalence.

This closes the infinite-control leak.  Turning the finite typed table into a
numerically addressed `List` for 16AF is deliberately left to the next purely
serialising pass; no arithmetic or simulation hypothesis remains here.
-/

namespace FoundationStoneTest16BN

open FoundationStoneTest16AW

abbrev Reg5 := FoundationStoneTest16BJ.Reg5

inductive FMLabel
  | loop
  | add (site : Fin 12)
  | exit
deriving DecidableEq, Repr, Fintype

inductive FTLabel
  | loop
  | credit
  | exit
deriving DecidableEq, Repr

instance : Fintype FTLabel :=
  Fintype.ofList [.loop, .credit, .exit] (by intro x; cases x <;> simp)

inductive FIncLabel
  | mul (phase : FMLabel)
  | mulBridge
  | transfer (phase : FTLabel)
  | transferBridge
  | done
deriving DecidableEq, Repr, Fintype

inductive FDivLabel
  | scan (site : Fin 11)
  | credit
  | exit (remainder : Fin 11)
  | bad
deriving DecidableEq, Repr, Fintype

inductive FRestoreLabel
  | transfer (phase : FTLabel)
  | bridge
  | multiply (phase : FIncLabel)
  | multiplyBridge
  | add (remaining : Fin 11)
  | done
deriving DecidableEq, Repr, Fintype

inductive FiniteLabel (L : Type)
  | halted (owner : L)
  | incWork (owner : L) (register : Reg5) (next : L) (phase : FIncLabel)
  | divWork (owner : L) (register : Reg5) (positive zero : L) (phase : FDivLabel)
  | divRoute (owner : L) (register : Reg5) (positive zero : L) (remainder : Fin 11)
  | posWork (owner : L) (register : Reg5) (positive : L) (phase : FTLabel)
  | restoreWork (owner : L) (register : Reg5) (zero : L) (remainder : Fin 11)
      (phase : FRestoreLabel)
  | jump (target : L)
deriving DecidableEq, Repr

abbrev FiniteLabelCode (L : Type) :=
  L ⊕
  (L × Reg5 × L × FIncLabel) ⊕
  (L × Reg5 × L × L × FDivLabel) ⊕
  (L × Reg5 × L × L × Fin 11) ⊕
  (L × Reg5 × L × FTLabel) ⊕
  (L × Reg5 × L × Fin 11 × FRestoreLabel) ⊕
  L

def decodeFiniteLabel {L : Type} : FiniteLabelCode L → FiniteLabel L
  | .inl owner => .halted owner
  | .inr (.inl (owner, i, next, phase)) => .incWork owner i next phase
  | .inr (.inr (.inl (owner, i, positive, zero, phase))) =>
      .divWork owner i positive zero phase
  | .inr (.inr (.inr (.inl (owner, i, positive, zero, r)))) =>
      .divRoute owner i positive zero r
  | .inr (.inr (.inr (.inr (.inl (owner, i, positive, phase))))) =>
      .posWork owner i positive phase
  | .inr (.inr (.inr (.inr (.inr (.inl (owner, i, zero, r, phase)))))) =>
      .restoreWork owner i zero r phase
  | .inr (.inr (.inr (.inr (.inr (.inr target))))) => .jump target

theorem decodeFiniteLabel_surjective {L : Type} :
    Function.Surjective (@decodeFiniteLabel L) := by
  intro l
  cases l with
  | halted owner => exact ⟨.inl owner, rfl⟩
  | incWork owner i next phase => exact ⟨.inr (.inl (owner, i, next, phase)), rfl⟩
  | divWork owner i positive zero phase =>
      exact ⟨.inr (.inr (.inl (owner, i, positive, zero, phase))), rfl⟩
  | divRoute owner i positive zero r =>
      exact ⟨.inr (.inr (.inr (.inl (owner, i, positive, zero, r)))), rfl⟩
  | posWork owner i positive phase =>
      exact ⟨.inr (.inr (.inr (.inr (.inl (owner, i, positive, phase))))), rfl⟩
  | restoreWork owner i zero r phase =>
      exact ⟨.inr (.inr (.inr (.inr (.inr (.inl (owner, i, zero, r, phase)))))), rfl⟩
  | jump target => exact ⟨.inr (.inr (.inr (.inr (.inr (.inr target))))), rfl⟩

instance {L : Type} [Finite L] : Finite (FiniteLabel L) :=
  Finite.of_surjective decodeFiniteLabel decodeFiniteLabel_surjective

noncomputable instance {L : Type} [Fintype L] : Fintype (FiniteLabel L) :=
  Fintype.ofFinite _

/-! ## Explicit embedding into 16BM's ambient labels -/

def embedM : FMLabel → MLabel
  | .loop => .loop
  | .add d => .add d.val
  | .exit => .exit

def embedT : FTLabel → TLabel
  | .loop => .loop
  | .credit => .credit
  | .exit => .exit

def embedInc : FIncLabel → FoundationStoneTest16BK.IncLabel
  | .mul l => .mul (embedM l)
  | .mulBridge => .mulBridge
  | .transfer l => .transfer (embedT l)
  | .transferBridge => .transferBridge
  | .done => .done

def embedDiv : FDivLabel → FoundationStoneTest16AV.Label
  | .scan i => .scan i.val
  | .credit => .credit
  | .exit r => .exit r.val
  | .bad => .bad

def embedRestore : FRestoreLabel → FoundationStoneTest16BL.RestoreLabel
  | .transfer l => .transfer (embedT l)
  | .bridge => .bridge
  | .multiply l => .multiply (embedInc l)
  | .multiplyBridge => .multiplyBridge
  | .add k => .add k.val
  | .done => .done

def embed {L : Type} : FiniteLabel L → FoundationStoneTest16BM.GlobalLabel L
  | .halted owner => .halted owner
  | .incWork owner i next phase => .incWork owner i next (embedInc phase)
  | .divWork owner i positive zero phase =>
      .divWork owner i positive zero (embedDiv phase)
  | .divRoute owner i positive zero r => .divRoute owner i positive zero r.val
  | .posWork owner i positive phase => .posWork owner i positive (embedT phase)
  | .restoreWork owner i zero r phase =>
      .restoreWork owner i zero r.val (embedRestore phase)
  | .jump target => .jump target

/-! Compression is total only so the finite instruction table is a total
function.  Modulo is never used on a reachable target outside the proved
bounds.  `instruction_expands` below is the kernel-checked guardrail. -/

def fin12 (n : Nat) : Fin 12 := ⟨n % 12, Nat.mod_lt _ (by decide)⟩
def fin11 (n : Nat) : Fin 11 := ⟨n % 11, Nat.mod_lt _ (by decide)⟩

def compressM : MLabel → FMLabel
  | .loop => .loop
  | .add d => .add (fin12 d)
  | .exit => .exit

def compressT : TLabel → FTLabel
  | .loop => .loop
  | .credit => .credit
  | .exit => .exit

def compressInc : FoundationStoneTest16BK.IncLabel → FIncLabel
  | .mul l => .mul (compressM l)
  | .mulBridge => .mulBridge
  | .transfer l => .transfer (compressT l)
  | .transferBridge => .transferBridge
  | .done => .done

def compressDiv : FoundationStoneTest16AV.Label → FDivLabel
  | .scan i => .scan (fin11 i)
  | .credit => .credit
  | .exit r => .exit (fin11 r)
  | .bad => .bad

def compressRestore : FoundationStoneTest16BL.RestoreLabel → FRestoreLabel
  | .transfer l => .transfer (compressT l)
  | .bridge => .bridge
  | .multiply l => .multiply (compressInc l)
  | .multiplyBridge => .multiplyBridge
  | .add k => .add (fin11 k)
  | .done => .done

def compress {L : Type} : FoundationStoneTest16BM.GlobalLabel L → FiniteLabel L
  | .halted owner => .halted owner
  | .incWork owner i next phase => .incWork owner i next (compressInc phase)
  | .divWork owner i positive zero phase =>
      .divWork owner i positive zero (compressDiv phase)
  | .divRoute owner i positive zero r => .divRoute owner i positive zero (fin11 r)
  | .posWork owner i positive phase => .posWork owner i positive (compressT phase)
  | .restoreWork owner i zero r phase =>
      .restoreWork owner i zero (fin11 r) (compressRestore phase)
  | .jump target => .jump target

theorem compress_embed_M : ∀ l, compressM (embedM l) = l := by
  intro l
  cases l with
  | loop => rfl
  | exit => rfl
  | add d =>
      apply congrArg FMLabel.add
      apply Fin.ext
      simp [compressM, embedM, fin12, Nat.mod_eq_of_lt d.isLt]

theorem compress_embed_T : ∀ l, compressT (embedT l) = l := by
  intro l; cases l <;> rfl

theorem compress_embed_inc : ∀ l, compressInc (embedInc l) = l := by
  intro l
  cases l <;> simp [compressInc, embedInc, compress_embed_M, compress_embed_T]

theorem compress_embed_div : ∀ l, compressDiv (embedDiv l) = l := by
  intro l
  cases l with
  | credit => rfl
  | bad => rfl
  | scan i =>
      apply congrArg FDivLabel.scan
      apply Fin.ext
      simp [compressDiv, embedDiv, fin11, Nat.mod_eq_of_lt i.isLt]
  | exit r =>
      apply congrArg FDivLabel.exit
      apply Fin.ext
      simp [compressDiv, embedDiv, fin11, Nat.mod_eq_of_lt r.isLt]

theorem compress_embed_restore : ∀ l, compressRestore (embedRestore l) = l := by
  intro l
  cases l with
  | transfer t => simp [compressRestore, embedRestore, compress_embed_T]
  | bridge => rfl
  | multiply i => simp [compressRestore, embedRestore, compress_embed_inc]
  | multiplyBridge => rfl
  | done => rfl
  | add k =>
      apply congrArg FRestoreLabel.add
      apply Fin.ext
      simp [compressRestore, embedRestore, fin11, Nat.mod_eq_of_lt k.isLt]

theorem compress_embed {L : Type} : ∀ l : FiniteLabel L, compress (embed l) = l := by
  intro l
  cases l <;> simp [compress, embed, compress_embed_inc, compress_embed_div,
    compress_embed_T, compress_embed_restore, fin11, Nat.mod_eq_of_lt]

/-! ## The finite program -/

def mapInstr {A B : Type} (f : A → B) : Instr A → Instr B
  | .inc body next => .inc body (f next)
  | .dec body positive zero => .dec body (f positive) (f zero)
  | .halt => .halt

def finiteProgram {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L) :
    FiniteLabel L → Instr (FiniteLabel L) := fun l =>
  mapInstr compress (FoundationStoneTest16BM.globalProgram P (embed l))

def mapState {A B : Type} (f : A → B) (s : State A) : State B :=
  ⟨f s.pc, s.a, s.b⟩

def finiteStart {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L) (l : L) :
    FiniteLabel L := compress (FoundationStoneTest16BM.startLabel P l)

def finiteEncode {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) : State (FiniteLabel L) :=
  ⟨finiteStart P s.pc,
    FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec s.counters), 0⟩

theorem finite_control_is_nonempty {L : Type} [Fintype L] (l : L) :
    0 < Fintype.card (FiniteLabel L) := by
  rw [Fintype.card_pos_iff]
  exact ⟨.halted l⟩

/-! A label is safe when embedding after compression gives it back. -/
def Safe {L : Type} (l : FoundationStoneTest16BM.GlobalLabel L) : Prop :=
  embed (compress l) = l

theorem safe_embed {L : Type} (l : FiniteLabel L) : Safe (embed l) := by
  unfold Safe
  rw [compress_embed]

theorem safe_start {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L) (l : L) :
    Safe (FoundationStoneTest16BM.startLabel P l) := by
  cases h : P l <;>
    simp [FoundationStoneTest16BM.startLabel, h, Safe, embed, compress,
      compressInc, embedInc, compressM, embedM, fin12,
      compressDiv, embedDiv, fin11]

def ClosedInstr {A : Type} (R : A → Prop) : Instr A → Prop
  | .inc _ next => R next
  | .dec _ positive zero => R positive ∧ R zero
  | .halt => True

def ClosedDivInstr (R : FoundationStoneTest16AV.Label → Prop) :
    FoundationStoneTest16AV.Instr → Prop
  | .inc _ next => R next
  | .dec _ positive zero => R positive ∧ R zero
  | .halt => True

def RoundM (l : MLabel) : Prop := embedM (compressM l) = l
def RoundT (l : TLabel) : Prop := embedT (compressT l) = l
def RoundInc (l : FoundationStoneTest16BK.IncLabel) : Prop :=
  embedInc (compressInc l) = l
def RoundDiv (l : FoundationStoneTest16AV.Label) : Prop :=
  embedDiv (compressDiv l) = l
def RoundRestore (l : FoundationStoneTest16BL.RestoreLabel) : Prop :=
  embedRestore (compressRestore l) = l

theorem multiplication_phases_close :
    ∀ (i : Reg5) (l : FIncLabel),
      ClosedInstr RoundInc
        (FoundationStoneTest16BK.incBlock (FoundationStoneTest16BJ.prime i) (embedInc l)) := by
  intro i l
  fin_cases i <;> cases l with
  | mul phase =>
      cases phase with
      | loop => simp [ClosedInstr, RoundInc, embedInc, compressInc, embedM, compressM,
          FoundationStoneTest16BK.incBlock, FoundationStoneTest16BK.mapMulInstr,
          FoundationStoneTest16AW.mulProgram, FoundationStoneTest16BJ.prime, fin12]
      | exit => simp [ClosedInstr, RoundInc, embedInc, compressInc, embedM,
          FoundationStoneTest16BK.incBlock]
      | add site => fin_cases site <;>
          simp [ClosedInstr, RoundInc, embedInc, compressInc, embedM, compressM,
            FoundationStoneTest16BK.incBlock, FoundationStoneTest16BK.mapMulInstr,
            FoundationStoneTest16AW.mulProgram, fin12]
  | mulBridge => simp [ClosedInstr, RoundInc, embedInc, compressInc,
      FoundationStoneTest16BK.incBlock, embedT, compressT]
  | transfer phase => cases phase <;>
      simp [ClosedInstr, RoundInc, embedInc, compressInc, embedT, compressT,
        FoundationStoneTest16BK.incBlock, FoundationStoneTest16BK.mapTransferInstr,
        transferProgram]
  | transferBridge => simp [ClosedInstr, RoundInc, embedInc, compressInc,
      FoundationStoneTest16BK.incBlock]
  | done => simp [ClosedInstr, FoundationStoneTest16BK.incBlock, embedInc]

theorem division_phases_close :
    ∀ (i : Reg5) (l : FDivLabel),
      ClosedDivInstr RoundDiv
        (FoundationStoneTest16AV.divProgram (FoundationStoneTest16BJ.prime i) (embedDiv l)) := by
  intro i l
  fin_cases i <;> cases l with
  | scan site => fin_cases site <;>
      simp [ClosedDivInstr, RoundDiv, embedDiv, compressDiv,
        FoundationStoneTest16AV.divProgram, FoundationStoneTest16BJ.prime, fin11]
  | credit => simp [ClosedDivInstr, RoundDiv, embedDiv, compressDiv,
      FoundationStoneTest16AV.divProgram, FoundationStoneTest16BJ.prime, fin11]
  | exit remainder => fin_cases remainder <;>
      simp [ClosedDivInstr, FoundationStoneTest16AV.divProgram, embedDiv]
  | bad => simp [ClosedDivInstr, FoundationStoneTest16AV.divProgram, embedDiv]

theorem transfer_phases_close :
    ∀ l : FTLabel, ClosedInstr RoundT (transferProgram (embedT l)) := by
  intro l
  cases l <;> simp [ClosedInstr, RoundT, embedT, compressT, transferProgram]

theorem restoration_phases_close :
    ∀ (i : Reg5) (r : Fin 11) (l : FRestoreLabel),
      ClosedInstr RoundRestore
        (FoundationStoneTest16BL.restoreProgram
          (FoundationStoneTest16BJ.prime i) r.val (embedRestore l)) := by
  intro i r l
  fin_cases i <;> fin_cases r <;> cases l with
  | transfer phase => cases phase <;>
      simp [ClosedInstr, RoundRestore, embedRestore, compressRestore,
        FoundationStoneTest16BL.restoreProgram,
        FoundationStoneTest16BL.mapTransferInstr, transferProgram,
        embedT, compressT]
  | bridge => simp [ClosedInstr, RoundRestore, embedRestore, compressRestore,
      FoundationStoneTest16BL.restoreProgram, embedInc, compressInc,
      embedM, compressM, fin12]
  | multiply phase =>
      cases phase with
      | mul m => cases m with
        | loop => simp [ClosedInstr, RoundRestore, embedRestore, compressRestore,
            FoundationStoneTest16BL.restoreProgram,
            FoundationStoneTest16BK.incBlock,
            FoundationStoneTest16BK.mapMulInstr,
            FoundationStoneTest16AW.mulProgram, FoundationStoneTest16BJ.prime,
            embedInc, compressInc, embedM, compressM, fin12]
        | exit => simp [ClosedInstr, RoundRestore, embedRestore, compressRestore,
            FoundationStoneTest16BL.restoreProgram,
            FoundationStoneTest16BK.incBlock, embedInc, compressInc, embedM]
        | add site => fin_cases site <;>
            simp [ClosedInstr, RoundRestore, embedRestore, compressRestore,
              FoundationStoneTest16BL.restoreProgram,
              FoundationStoneTest16BK.incBlock,
              FoundationStoneTest16BK.mapMulInstr,
              FoundationStoneTest16AW.mulProgram, embedInc, compressInc,
              embedM, compressM, fin12]
      | mulBridge => simp [ClosedInstr, RoundRestore, embedRestore, compressRestore,
          FoundationStoneTest16BL.restoreProgram, FoundationStoneTest16BK.incBlock,
          embedInc, compressInc, embedT, compressT]
      | transfer t => cases t <;>
          simp [ClosedInstr, RoundRestore, embedRestore, compressRestore,
            FoundationStoneTest16BL.restoreProgram,
            FoundationStoneTest16BK.incBlock,
            FoundationStoneTest16BK.mapTransferInstr, transferProgram,
            embedInc, compressInc, embedT, compressT]
      | transferBridge => simp [ClosedInstr, RoundRestore, embedRestore,
          compressRestore, FoundationStoneTest16BL.restoreProgram,
          FoundationStoneTest16BK.incBlock, embedInc, compressInc]
      | done => simp [ClosedInstr, RoundRestore, embedRestore, compressRestore,
          FoundationStoneTest16BL.restoreProgram, embedInc]
  | multiplyBridge => simp [ClosedInstr, RoundRestore, embedRestore, compressRestore,
      FoundationStoneTest16BL.restoreProgram, fin11]
  | add remaining => fin_cases remaining <;>
      simp [ClosedInstr, RoundRestore, embedRestore, compressRestore,
        FoundationStoneTest16BL.restoreProgram, fin11]
  | done => simp [ClosedInstr, FoundationStoneTest16BL.restoreProgram, embedRestore]

theorem mapBK_preserves_safe {L : Type} (owner : L) (i : Reg5) (next : L)
    (x : Instr FoundationStoneTest16BK.IncLabel) (h : ClosedInstr RoundInc x) :
    ClosedInstr Safe (FoundationStoneTest16BM.mapBK owner i next x) := by
  cases x <;> simp [ClosedInstr, RoundInc, Safe, compress, embed,
    FoundationStoneTest16BM.mapBK] at h ⊢ <;> exact h

theorem mapAV_preserves_safe {L : Type} (owner : L) (i : Reg5) (positive zero : L)
    (x : FoundationStoneTest16AV.Instr) (h : ClosedDivInstr RoundDiv x) :
    ClosedInstr Safe (FoundationStoneTest16BM.mapAV owner i positive zero x) := by
  cases x <;> simp [ClosedInstr, ClosedDivInstr, RoundDiv, Safe, compress, embed,
    FoundationStoneTest16BM.mapAV] at h ⊢ <;>
    exact h

theorem mapTransfer_preserves_safe {L : Type} (owner : L) (i : Reg5) (positive : L)
    (x : Instr TLabel) (h : ClosedInstr RoundT x) :
    ClosedInstr Safe (FoundationStoneTest16BM.mapTransfer owner i positive x) := by
  cases x <;> simp [ClosedInstr, RoundT, Safe, compress, embed,
    FoundationStoneTest16BM.mapTransfer] at h ⊢ <;> exact h

theorem mapRestore_preserves_safe {L : Type} (owner : L) (i : Reg5) (zero : L)
    (r : Fin 11) (x : Instr FoundationStoneTest16BL.RestoreLabel)
    (h : ClosedInstr RoundRestore x) :
    ClosedInstr Safe (FoundationStoneTest16BM.mapRestore owner i zero r.val x) := by
  cases x <;> simp [ClosedInstr, RoundRestore, Safe, compress, embed,
    FoundationStoneTest16BM.mapRestore, fin11, Nat.mod_eq_of_lt r.isLt] at h ⊢ <;> exact h

/-! Every successor emitted from a finite label remains inside the bounded
phase space.  This is the substantive closure theorem. -/
theorem successors_safe {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (l : FiniteLabel L) :
    match FoundationStoneTest16BM.globalProgram P (embed l) with
    | .inc _ next => Safe next
    | .dec _ positive zero => Safe positive ∧ Safe zero
    | .halt => True := by
  cases l with
  | halted owner => simp [FoundationStoneTest16BM.globalProgram, embed]
  | jump target =>
      simpa [FoundationStoneTest16BM.globalProgram, embed] using safe_start P target
  | posWork owner i positive phase =>
      cases phase with
      | exit => simp [FoundationStoneTest16BM.globalProgram, embed, embedT,
          Safe, compress, compress_embed]
      | loop =>
          have h := transfer_phases_close FTLabel.loop
          change ClosedInstr Safe
            (FoundationStoneTest16BM.mapTransfer owner i positive (transferProgram TLabel.loop))
          exact mapTransfer_preserves_safe owner i positive _ h
      | credit =>
          have h := transfer_phases_close FTLabel.credit
          change ClosedInstr Safe
            (FoundationStoneTest16BM.mapTransfer owner i positive (transferProgram TLabel.credit))
          exact mapTransfer_preserves_safe owner i positive _ h
  | divRoute owner i positive zero r =>
      fin_cases r <;> simp [FoundationStoneTest16BM.globalProgram, embed, Safe, compress,
        embedT, compressT, embedRestore, compressRestore, fin11, compress_embed]
  | divWork owner i positive zero phase =>
      cases phase with
      | exit r =>
          simp [FoundationStoneTest16BM.globalProgram, embed, embedDiv, Safe, compress,
            compressDiv, fin11, Nat.mod_eq_of_lt r.isLt]
      | scan site =>
          fin_cases i <;> fin_cases site <;>
            simp [FoundationStoneTest16BM.globalProgram, FoundationStoneTest16BM.mapAV,
              FoundationStoneTest16AV.divProgram, FoundationStoneTest16BJ.prime,
              embed, embedDiv, Safe, compress, compressDiv, fin11]
      | credit =>
          simp only [embed, embedDiv, FoundationStoneTest16BM.globalProgram]
          change ClosedInstr Safe (FoundationStoneTest16BM.mapAV owner i positive zero
            (FoundationStoneTest16AV.divProgram (FoundationStoneTest16BJ.prime i) .credit))
          exact mapAV_preserves_safe owner i positive zero _
            (division_phases_close i .credit)
      | bad =>
          simp only [embed, embedDiv, FoundationStoneTest16BM.globalProgram]
          change ClosedInstr Safe (FoundationStoneTest16BM.mapAV owner i positive zero
            (FoundationStoneTest16AV.divProgram (FoundationStoneTest16BJ.prime i) .bad))
          exact mapAV_preserves_safe owner i positive zero _
            (division_phases_close i .bad)
  | incWork owner i next phase =>
      cases phase with
      | done => simp [FoundationStoneTest16BM.globalProgram, embed, embedInc,
          Safe, compress, compress_embed]
      | mul m =>
          fin_cases i
          all_goals cases m with
          | loop => simp [FoundationStoneTest16BM.globalProgram, FoundationStoneTest16BM.mapBK,
              FoundationStoneTest16BK.incBlock, FoundationStoneTest16BK.mapMulInstr,
              FoundationStoneTest16AW.mulProgram, FoundationStoneTest16BJ.prime,
              embed, embedInc, embedM, Safe, compress, compressInc, compressM, fin12]
          | exit => simp [FoundationStoneTest16BM.globalProgram, FoundationStoneTest16BM.mapBK,
              FoundationStoneTest16BK.incBlock, embed, embedInc, embedM,
              Safe, compress, compressInc]
          | add site => fin_cases site <;>
              simp [FoundationStoneTest16BM.globalProgram, FoundationStoneTest16BM.mapBK,
                FoundationStoneTest16BK.incBlock, FoundationStoneTest16BK.mapMulInstr,
                FoundationStoneTest16AW.mulProgram, FoundationStoneTest16BJ.prime,
                embed, embedInc, embedM, Safe, compress, compressInc, compressM, fin12]
      | mulBridge =>
          simp only [embed, embedInc, FoundationStoneTest16BM.globalProgram]
          change ClosedInstr Safe (FoundationStoneTest16BM.mapBK owner i next
            (FoundationStoneTest16BK.incBlock (FoundationStoneTest16BJ.prime i) .mulBridge))
          exact mapBK_preserves_safe owner i next _ (multiplication_phases_close i .mulBridge)
      | transfer t =>
          cases t <;> simp [FoundationStoneTest16BM.globalProgram,
            FoundationStoneTest16BM.mapBK, FoundationStoneTest16BK.incBlock,
            FoundationStoneTest16BK.mapTransferInstr, transferProgram,
            embed, embedInc, embedT, Safe, compress, compressInc, compressT]
      | transferBridge =>
          simp only [embed, embedInc, FoundationStoneTest16BM.globalProgram]
          change ClosedInstr Safe (FoundationStoneTest16BM.mapBK owner i next
            (FoundationStoneTest16BK.incBlock (FoundationStoneTest16BJ.prime i) .transferBridge))
          exact mapBK_preserves_safe owner i next _ (multiplication_phases_close i .transferBridge)
  | restoreWork owner i zero r phase =>
      cases phase with
      | done => simp [FoundationStoneTest16BM.globalProgram, embed, embedRestore,
          Safe, compress, compress_embed]
      | transfer t =>
          cases t <;> simp [FoundationStoneTest16BM.globalProgram,
            FoundationStoneTest16BM.mapRestore, FoundationStoneTest16BL.restoreProgram,
            FoundationStoneTest16BL.mapTransferInstr, transferProgram,
            embed, embedRestore, embedT, Safe, compress, compressRestore, compressT,
            fin11, Nat.mod_eq_of_lt r.isLt]
      | bridge =>
          simp only [embed, embedRestore, FoundationStoneTest16BM.globalProgram]
          change ClosedInstr Safe (FoundationStoneTest16BM.mapRestore owner i zero r.val
            (FoundationStoneTest16BL.restoreProgram (FoundationStoneTest16BJ.prime i) r.val .bridge))
          exact mapRestore_preserves_safe owner i zero r _
            (restoration_phases_close i r .bridge)
      | multiply m =>
          fin_cases i
          all_goals cases m with
          | mul mphase => cases mphase with
            | loop => simp [FoundationStoneTest16BM.globalProgram,
                FoundationStoneTest16BM.mapRestore,
                FoundationStoneTest16BL.restoreProgram,
                FoundationStoneTest16BK.incBlock,
                FoundationStoneTest16BK.mapMulInstr,
                FoundationStoneTest16AW.mulProgram, FoundationStoneTest16BJ.prime,
                embed, embedRestore, embedInc, embedM, Safe, compress,
                compressRestore, compressInc, compressM, fin11, fin12,
                Nat.mod_eq_of_lt r.isLt]
            | exit => simp [FoundationStoneTest16BM.globalProgram,
                FoundationStoneTest16BM.mapRestore,
                FoundationStoneTest16BL.restoreProgram,
                FoundationStoneTest16BK.incBlock, embed, embedRestore, embedInc,
                embedM, Safe, compress, compressRestore, compressInc, fin11,
                Nat.mod_eq_of_lt r.isLt]
            | add site => fin_cases site <;>
                simp [FoundationStoneTest16BM.globalProgram,
                  FoundationStoneTest16BM.mapRestore,
                  FoundationStoneTest16BL.restoreProgram,
                  FoundationStoneTest16BK.incBlock,
                  FoundationStoneTest16BK.mapMulInstr,
                  FoundationStoneTest16AW.mulProgram, FoundationStoneTest16BJ.prime,
                  embed, embedRestore, embedInc, embedM, Safe, compress,
                  compressRestore, compressInc, compressM, fin11, fin12,
                  Nat.mod_eq_of_lt r.isLt]
          | mulBridge => simp [FoundationStoneTest16BM.globalProgram,
              FoundationStoneTest16BM.mapRestore, FoundationStoneTest16BL.restoreProgram,
              FoundationStoneTest16BK.incBlock, embed, embedRestore, embedInc,
              embedT, Safe, compress, compressRestore, compressInc, compressT,
              fin11, Nat.mod_eq_of_lt r.isLt]
          | transfer t => cases t <;>
              simp [FoundationStoneTest16BM.globalProgram,
                FoundationStoneTest16BM.mapRestore,
                FoundationStoneTest16BL.restoreProgram,
                FoundationStoneTest16BK.incBlock,
                FoundationStoneTest16BK.mapTransferInstr, transferProgram,
                embed, embedRestore, embedInc, embedT, Safe, compress,
                compressRestore, compressInc, compressT, fin11,
                Nat.mod_eq_of_lt r.isLt]
          | transferBridge => simp [FoundationStoneTest16BM.globalProgram,
              FoundationStoneTest16BM.mapRestore, FoundationStoneTest16BL.restoreProgram,
              FoundationStoneTest16BK.incBlock, embed, embedRestore, embedInc,
              Safe, compress, compressRestore, compressInc, fin11,
              Nat.mod_eq_of_lt r.isLt]
          | done => simp [FoundationStoneTest16BM.globalProgram,
              FoundationStoneTest16BM.mapRestore, FoundationStoneTest16BL.restoreProgram,
              embed, embedRestore, embedInc, Safe, compress, compressRestore,
              fin11, Nat.mod_eq_of_lt r.isLt]
      | multiplyBridge =>
          simp only [embed, embedRestore, FoundationStoneTest16BM.globalProgram]
          change ClosedInstr Safe (FoundationStoneTest16BM.mapRestore owner i zero r.val
            (FoundationStoneTest16BL.restoreProgram (FoundationStoneTest16BJ.prime i) r.val
              .multiplyBridge))
          exact mapRestore_preserves_safe owner i zero r _
            (restoration_phases_close i r .multiplyBridge)
      | add k =>
          fin_cases k <;> simp [FoundationStoneTest16BM.globalProgram,
            FoundationStoneTest16BM.mapRestore, FoundationStoneTest16BL.restoreProgram,
            embed, embedRestore, Safe, compress, compressRestore, fin11,
            Nat.mod_eq_of_lt r.isLt]

/-! Generic execution transport for a safe ambient state. -/

theorem instruction_expands {L : Type}
    (P : L → FoundationStoneTest16AY.Instr 5 L) (l : FiniteLabel L) :
    mapInstr embed (finiteProgram P l) =
      FoundationStoneTest16BM.globalProgram P (embed l) := by
  unfold finiteProgram
  have hs := successors_safe P l
  cases h : FoundationStoneTest16BM.globalProgram P (embed l) with
  | halt => simp [mapInstr, h]
  | inc body next =>
      simp only [h] at hs
      simp [mapInstr, h, Safe] at hs ⊢
      exact hs
  | dec body positive zero =>
      simp only [h] at hs
      simp [mapInstr, h, Safe] at hs ⊢
      exact hs

theorem step_expands {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : State (FiniteLabel L)) :
    (step (finiteProgram P) s).map (mapState embed) =
      step (FoundationStoneTest16BM.globalProgram P) (mapState embed s) := by
  simp only [mapState]
  unfold step
  rw [← instruction_expands P s.pc]
  cases hi : finiteProgram P s.pc with
  | halt => rfl
  | inc body next => cases body <;> rfl
  | dec body positive zero =>
      cases body with
      | false => by_cases hz : s.a = 0 <;>
          simp [hz, mapInstr, mapState, FoundationStoneTest16AW.get,
            FoundationStoneTest16AW.set]
      | true => by_cases hz : s.b = 0 <;>
          simp [hz, mapInstr, mapState, FoundationStoneTest16AW.get,
            FoundationStoneTest16AW.set]

theorem run_expands {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L) :
    ∀ n s, (run (finiteProgram P) n s).map (mapState embed) =
      run (FoundationStoneTest16BM.globalProgram P) n (mapState embed s) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      unfold run
      rw [← step_expands]
      cases hs : step (finiteProgram P) s with
      | none => rfl
      | some s' =>
          simp only [Option.map_some]
          exact ih s'

/-! Exact compiled operations transfer from 16BM. -/

def finiteIncEntry {L : Type} (owner : L) (i : Reg5) (next : L) : FiniteLabel L :=
  .incWork owner i next (.mul .loop)

def finiteDivEntry {L : Type} (owner : L) (i : Reg5) (positive zero : L) : FiniteLabel L :=
  .divWork owner i positive zero (.scan 0)

theorem finite_inc_exact {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner next : L) (i : Reg5) (a : Nat) :
    ∃ n, 0 < n ∧ run (finiteProgram P) n ⟨finiteIncEntry owner i next, a, 0⟩ =
      some ⟨finiteStart P next, FoundationStoneTest16BJ.prime i * a, 0⟩ := by
  obtain ⟨n, hn, hr⟩ := FoundationStoneTest16BM.inc_compiled_exact P owner next i a
  refine ⟨n, hn, ?_⟩
  have hx := run_expands P n ⟨finiteIncEntry owner i next, a, 0⟩
  change Option.map (mapState embed)
      (run (finiteProgram P) n ⟨finiteIncEntry owner i next, a, 0⟩) =
    run (FoundationStoneTest16BM.globalProgram P) n
      ⟨.incWork owner i next (.mul .loop), a, 0⟩ at hx
  rw [hr] at hx
  cases hrun : run (finiteProgram P) n ⟨finiteIncEntry owner i next, a, 0⟩ with
  | none =>
      rw [hrun] at hx
      contradiction
  | some t =>
      rw [hrun] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      apply congrArg (mapState compress) at hx
      apply congrArg some
      cases t
      simp_all [finiteIncEntry, finiteStart, mapState, compress_embed]

theorem finite_dec_positive_exact {L : Type}
    (P : L → FoundationStoneTest16AY.Instr 5 L) (owner : L) (i : Reg5)
    (positive zero : L) (a : Nat) (hd : FoundationStoneTest16BJ.prime i ∣ a) :
    ∃ n, 0 < n ∧ run (finiteProgram P) n ⟨finiteDivEntry owner i positive zero, a, 0⟩ =
      some ⟨finiteStart P positive, a / FoundationStoneTest16BJ.prime i, 0⟩ := by
  obtain ⟨n, hn, hr⟩ :=
    FoundationStoneTest16BM.dec_positive_compiled_exact P owner i positive zero a hd
  refine ⟨n, hn, ?_⟩
  have hx := run_expands P n ⟨finiteDivEntry owner i positive zero, a, 0⟩
  change Option.map (mapState embed)
      (run (finiteProgram P) n ⟨finiteDivEntry owner i positive zero, a, 0⟩) =
    run (FoundationStoneTest16BM.globalProgram P) n
      ⟨.divWork owner i positive zero (.scan 0), a, 0⟩ at hx
  rw [hr] at hx
  cases hrun : run (finiteProgram P) n ⟨finiteDivEntry owner i positive zero, a, 0⟩ with
  | none =>
      rw [hrun] at hx
      contradiction
  | some t =>
      rw [hrun] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      apply congrArg (mapState compress) at hx
      apply congrArg some
      cases t
      simp_all [finiteDivEntry, finiteStart, mapState, compress_embed]

theorem finite_dec_zero_exact {L : Type}
    (P : L → FoundationStoneTest16AY.Instr 5 L) (owner : L) (i : Reg5)
    (positive zero : L) (a : Nat) (hnd : ¬ FoundationStoneTest16BJ.prime i ∣ a) :
    ∃ n, 0 < n ∧ run (finiteProgram P) n ⟨finiteDivEntry owner i positive zero, a, 0⟩ =
      some ⟨finiteStart P zero, a, 0⟩ := by
  obtain ⟨n, hn, hr⟩ :=
    FoundationStoneTest16BM.dec_zero_compiled_exact P owner i positive zero a hnd
  refine ⟨n, hn, ?_⟩
  have hx := run_expands P n ⟨finiteDivEntry owner i positive zero, a, 0⟩
  change Option.map (mapState embed)
      (run (finiteProgram P) n ⟨finiteDivEntry owner i positive zero, a, 0⟩) =
    run (FoundationStoneTest16BM.globalProgram P) n
      ⟨.divWork owner i positive zero (.scan 0), a, 0⟩ at hx
  rw [hr] at hx
  cases hrun : run (finiteProgram P) n ⟨finiteDivEntry owner i positive zero, a, 0⟩ with
  | none =>
      rw [hrun] at hx
      contradiction
  | some t =>
      rw [hrun] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      apply congrArg (mapState compress) at hx
      apply congrArg some
      cases t
      simp_all [finiteDivEntry, finiteStart, mapState, compress_embed]

def Encodes {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) (t : State (FiniteLabel L)) : Prop :=
  finiteEncode P s = t

theorem finite_global_respects {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L) :
    StateTransition.Respects (FoundationStoneTest16AY.step P)
      (step (finiteProgram P)) (Encodes P) := by
  intro s t hst
  subst t
  cases hi : P s.pc with
  | halt =>
      have hs : FoundationStoneTest16AY.step P s = none := by
        simp [FoundationStoneTest16AY.step, hi]
      rw [hs]
      simp [finiteEncode, finiteStart, finiteProgram, FoundationStoneTest16BM.startLabel,
        hi, FoundationStoneTest16BM.globalProgram, embed, compress, mapInstr, step]
  | inc i next =>
      let s' := FoundationStoneTest16AY.setCounter s next i (s.counters i + 1)
      have hs : FoundationStoneTest16AY.step P s = some s' := by
        simp [FoundationStoneTest16AY.step, hi, s']
      rw [hs]
      refine ⟨finiteEncode P s', rfl, ?_⟩
      obtain ⟨n, hn, hr⟩ := finite_inc_exact P s.pc next i
        (FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec s.counters))
      apply FoundationStoneTest16BI.positive_run_gives_reaches (finiteProgram P) n hn
      simpa [finiteEncode, finiteStart, hi, s', FoundationStoneTest16AY.setCounter,
        FoundationStoneTest16BJ.pack_update_inc, finiteIncEntry, compress, compressInc,
        compressM, fin12,
        FoundationStoneTest16BM.startLabel] using hr
  | dec i positive zero =>
      by_cases hz : s.counters i = 0
      · let s' : FoundationStoneTest16AY.State 5 L := { s with pc := zero }
        have hs : FoundationStoneTest16AY.step P s = some s' := by
          simp [FoundationStoneTest16AY.step, hi, hz, s']
        rw [hs]
        refine ⟨finiteEncode P s', rfl, ?_⟩
        have hnd : ¬ FoundationStoneTest16BJ.prime i ∣
            FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec s.counters) := by
          rw [FoundationStoneTest16BJ.prime_dvd_pack_iff]
          omega
        obtain ⟨n, hn, hr⟩ := finite_dec_zero_exact P s.pc i positive zero _ hnd
        apply FoundationStoneTest16BI.positive_run_gives_reaches (finiteProgram P) n hn
        simpa [finiteEncode, finiteStart, hi, s', compress,
          finiteDivEntry, compressDiv, fin11,
          FoundationStoneTest16BM.startLabel] using hr
      · have hp : 0 < s.counters i := Nat.pos_of_ne_zero hz
        let s' := FoundationStoneTest16AY.setCounter s positive i (s.counters i - 1)
        have hs : FoundationStoneTest16AY.step P s = some s' := by
          simp [FoundationStoneTest16AY.step, hi, hz, s']
        rw [hs]
        refine ⟨finiteEncode P s', rfl, ?_⟩
        have hd : FoundationStoneTest16BJ.prime i ∣
            FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec s.counters) :=
          (FoundationStoneTest16BJ.prime_dvd_pack_iff s.counters i).2 hp
        obtain ⟨n, hn, hr⟩ := finite_dec_positive_exact P s.pc i positive zero _ hd
        apply FoundationStoneTest16BI.positive_run_gives_reaches (finiteProgram P) n hn
        simpa [finiteEncode, finiteStart, hi, s', FoundationStoneTest16AY.setCounter,
          FoundationStoneTest16BJ.pack_update_dec _ i hp, finiteDivEntry,
          compress, compressDiv, fin11,
          FoundationStoneTest16BM.startLabel] using hr

def FiveTerminates {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) : Prop :=
  (StateTransition.eval (FoundationStoneTest16AY.step P) s).Dom

def FiniteMM2Terminates {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : State (FiniteLabel L)) : Prop :=
  (StateTransition.eval (step (finiteProgram P)) s).Dom

theorem finite_halting_iff {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) :
    FiveTerminates P s ↔ FiniteMM2Terminates P (finiteEncode P s) := by
  unfold FiveTerminates FiniteMM2Terminates
  exact (StateTransition.tr_eval_dom (finite_global_respects P) rfl).symm

/-! Red control: swapping the finite division route sends a divisible input
to restoration instead of the positive continuation. -/

def brokenRoute {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L) :
    FiniteLabel L → Instr (FiniteLabel L)
  | .divRoute owner i positive zero r =>
      let target := if r.val = 0 then
        FiniteLabel.restoreWork owner i zero r (.transfer .loop)
      else FiniteLabel.posWork owner i positive .loop
      .dec false target target
  | l => finiteProgram P l

theorem swapped_zero_route_is_detected {L : Type}
    (P : L → FoundationStoneTest16AY.Instr 5 L) (owner positive zero : L)
    (i : Reg5) (q : Nat) :
    step (brokenRoute P)
        ⟨FiniteLabel.divRoute owner i positive zero 0, 0, q⟩ =
      some ⟨FiniteLabel.restoreWork owner i zero 0 (.transfer .loop), 0, q⟩ ∧
    step (finiteProgram P)
        ⟨FiniteLabel.divRoute owner i positive zero 0, 0, q⟩ =
      some ⟨FiniteLabel.posWork owner i positive .loop, 0, q⟩ := by
  simp [brokenRoute, finiteProgram, FoundationStoneTest16BM.globalProgram, embed,
    compress, mapInstr, step, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set, embedT, compressT, fin11]

theorem turing_chamber_16BN_certificate :
    (∀ {L : Type} [Fintype L] (l : L), 0 < Fintype.card (FiniteLabel L)) ∧
    (∀ {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L),
      StateTransition.Respects (FoundationStoneTest16AY.step P)
        (step (finiteProgram P)) (Encodes P)) ∧
    (∀ {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
      (s : FoundationStoneTest16AY.State 5 L),
      FiveTerminates P s ↔ FiniteMM2Terminates P (finiteEncode P s)) :=
  ⟨finite_control_is_nonempty, finite_global_respects, finite_halting_iff⟩

#print axioms successors_safe
#print axioms instruction_expands
#print axioms run_expands
#print axioms finite_global_respects
#print axioms finite_halting_iff
#print axioms swapped_zero_route_is_detected
#print axioms turing_chamber_16BN_certificate

end FoundationStoneTest16BN
