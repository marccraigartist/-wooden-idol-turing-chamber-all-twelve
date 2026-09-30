import FoundationStoneTest16BR
import FoundationStoneTest16BN

/-!
# 16BS — The effective entrance to one fixed finite MM2

This file closes the effectiveness obligation left by 16BR. It gives a
computable arithmetic presentation of Mathlib's binary source tape, proves
that presentation equal to the counters installed by 16BR, transports 16BR
through 16BN, and obtains a computable many-one reduction from Mathlib's
halting predicate to halting of one fixed finite two-counter program.

Claims boundary:
* `universalListCode` remains `Classical.choose`; consequently the earned
  statement is existential: there is a fixed finite program. This file does
  not print an executable table for that chosen witness.
* Serialization to 16AG is still a separate pass.
* 16AG starts its relay at pc = 1, whereas 16AF starts its counter/helix
  problem at pc = 0. Their predicates cannot be composed literally until an
  explicit start-convention bridge is supplied.

Verified with Lean 4.35.0-rc2 and pinned Mathlib.
-/
namespace FoundationStoneTest16BS
open Turing Turing.PartrecToTM2
attribute [local instance] FoundationStoneTest16BR.sourceFintype
  FoundationStoneTest16BR.sourceFiniteIndex

def binaryFold (seed n : Nat) : Nat :=
  Nat.binaryRec seed (fun b _ r => (bif b then 4 else 3) + 5 * r) n

def binaryFoldStep (seed : Nat) (xs : List Nat) : Option Nat :=
  if xs.length = 0 then some seed else
    some ((bif xs.length.bodd then 4 else 3) + 5 * xs.getI xs.length.div2)

theorem binaryFoldStep_computable : Computable₂ binaryFoldStep := by
  unfold binaryFoldStep
  apply Computable₂.mk
  have hc : Computable (fun p : Nat × List Nat => p.2.length == 0) :=
    (Primrec.beq.comp
      (Primrec.list_length.comp Primrec.snd) (Primrec.const 0)).to_comp
  have ht : Computable (fun p : Nat × List Nat => some p.1) :=
    (Primrec.option_some.comp Primrec.fst).to_comp
  have hip : Primrec (fun p : Nat × List Nat =>
      bif p.2.length.bodd then 4 else 3) :=
    (Primrec.cond
      (Primrec.nat_bodd.comp (Primrec.list_length.comp Primrec.snd))
      (Primrec.const 4) (Primrec.const 3))
  have hgp : Primrec (fun p : Nat × List Nat =>
      p.2.getI p.2.length.div2) :=
    (Primrec.list_getI.comp
      Primrec.snd
      (Primrec.nat_div2.comp (Primrec.list_length.comp Primrec.snd)))
  have he : Computable (fun p : Nat × List Nat =>
      some ((bif p.2.length.bodd then 4 else 3) +
        5 * p.2.getI p.2.length.div2)) :=
    (Primrec.option_some.comp
      (Primrec.nat_add.comp hip
        (Primrec.nat_mul.comp (Primrec.const 5) hgp))).to_comp
  exact (Computable.cond hc ht he).of_eq (by intro p; simp [Bool.cond_eq_ite])

theorem binaryFold_computable : Computable₂ binaryFold := by
  apply Computable.nat_strong_rec binaryFold binaryFoldStep_computable
  intro seed n
  simp only [binaryFoldStep, List.length_map, List.length_range]
  by_cases hn : n = 0
  · subst n; rfl
  · simp only [hn, ↓reduceIte, Option.some.injEq]
    unfold binaryFold
    rw [Nat.binaryRec_of_ne_zero _ _ hn]
    rw [List.getI_eq_getElem?_getD]
    have hlt : n.div2 < n := by rw [Nat.div2_val]; omega
    simp [hlt]

#print axioms binaryFold_computable

theorem trNat_bit (b : Bool) (n : Nat) (h : n = 0 → b = true) :
    trNat (Nat.bit b n) = (if b then Γ'.bit1 else Γ'.bit0) :: trNat n := by
  unfold trNat
  change trNum (Num.ofNat' (Nat.bit b n)) =
    (if b then Γ'.bit1 else Γ'.bit0) :: trNum (Num.ofNat' n)
  have hb : Num.ofNat' (Nat.bit b n) =
      (bif b then Num.bit1 (Num.ofNat' n) else Num.bit0 (Num.ofNat' n)) := by
    unfold Num.ofNat'
    rw [Nat.binaryRec_eq b n (Or.inr h)]
    cases b <;> rfl
  rw [hb]
  cases b with
  | false =>
      cases hn : Num.ofNat' n with
      | zero =>
          exfalso
          have hz := congrArg (fun z : Num => (z : Nat)) hn
          have hn0 : n = 0 := by simpa using hz
          exact Bool.noConfusion (h hn0)
      | pos p => simp [trNum, trPosNum, Num.bit0, Num.bit1]
  | true =>
      cases hn : Num.ofNat' n <;> simp [trNum, trPosNum, Num.bit0, Num.bit1]

theorem binaryFold_code (tail : List Γ') (n : Nat) :
    binaryFold (FoundationStoneTest16AT.code tail) n =
      FoundationStoneTest16AT.code (trNat n ++ tail) := by
  induction n using Nat.binaryRec' with
  | zero => simp [binaryFold]
  | bit b n h ih =>
      unfold binaryFold
      rw [Nat.binaryRec_eq b n (Or.inr h)]
      rw [trNat_bit b n h]
      change (bif b then 4 else 3) + 5 * binaryFold
        (FoundationStoneTest16AT.code tail) n = _
      rw [ih]
      cases b <;> rfl

def inputStack (d : Nat.Partrec.Code) : Nat :=
  binaryFold 12 (Encodable.encode d)

theorem inputStack_computable : Computable inputStack := by
  unfold inputStack
  exact binaryFold_computable.comp (Computable.const 12) Primrec.encode.to_comp

theorem inputStack_exact (d : Nat.Partrec.Code) :
    inputStack d = (FoundationStoneTest16BR.initialCounters d).main := by
  rw [FoundationStoneTest16BR.initialCounters]
  change inputStack d = FoundationStoneTest16AT.code (trList [Encodable.encode d, 0])
  rw [show trList [Encodable.encode d, 0] =
      trNat (Encodable.encode d) ++ [Γ'.cons, Γ'.cons] by simp [trList]]
  rw [← binaryFold_code [Γ'.cons, Γ'.cons] (Encodable.encode d)]
  rfl

theorem initialCounters_exact (d : Nat.Partrec.Code) :
    FoundationStoneTest16BR.initialCounters d =
      ⟨inputStack d, 0, 0, 0, 0⟩ := by
  have hm := inputStack_exact d
  unfold FoundationStoneTest16BR.initialCounters FoundationStoneTest16AT.encodeStacks
    FoundationStoneTest16BR.initialStacks at hm
  simp only [K'.elim] at hm
  unfold FoundationStoneTest16BR.initialCounters
  unfold FoundationStoneTest16AT.encodeStacks FoundationStoneTest16BR.initialStacks
  simp only [K'.elim]
  rw [← hm]
  rfl

abbrev Five := Nat × (Nat × (Nat × (Nat × Nat)))

def pack (s : Five) : Nat :=
  2 ^ s.1 * 3 ^ s.2.1 * 5 ^ s.2.2.1 * 7 ^ s.2.2.2.1 * 11 ^ s.2.2.2.2

theorem pack_computable : Computable pack := by
  apply Primrec.to_comp
  unfold pack
  have hp : Primrec₂ (fun x y : Nat => x ^ y) :=
    Primrec₂.unpaired'.mp Nat.Primrec.pow
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_mul.comp
          (hp.comp (Primrec.const 2) Primrec.fst)
          (hp.comp (Primrec.const 3) (Primrec.fst.comp Primrec.snd)))
        (hp.comp (Primrec.const 5) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (hp.comp (Primrec.const 7)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (hp.comp (Primrec.const 11)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

def sourceFive (d : Nat.Partrec.Code) : Five :=
  (inputStack d, (0, (0, (0, 0))))

theorem sourceFive_computable : Computable sourceFive := by
  exact inputStack_computable.pair
    ((Computable.const 0).pair ((Computable.const 0).pair
      ((Computable.const 0).pair (Computable.const 0))))

def packedInput (d : Nat.Partrec.Code) : Nat :=
  pack (sourceFive d)

theorem packedInput_computable : Computable packedInput :=
  pack_computable.comp sourceFive_computable

theorem packedInput_exact (d : Nat.Partrec.Code) :
    packedInput d = FoundationStoneTest16AM.pack
      (FoundationStoneTest16BJ.fromVec
        (FoundationStoneTest16BQ.packCounters
          (FoundationStoneTest16BR.initialCounters d))) := by
  rw [initialCounters_exact]
  simp [packedInput, sourceFive, pack, FoundationStoneTest16AM.pack,
    FoundationStoneTest16BJ.fromVec, FoundationStoneTest16BQ.packCounters,
    inputStack_exact]

noncomputable abbrev UProgram :=
  FoundationStoneTest16BR.executableProgram
    FoundationStoneTest16AH.universalListCode

noncomputable def primitiveInitial (d : Nat.Partrec.Code) :=
  FoundationStoneTest16BR.executableState
    FoundationStoneTest16AH.universalListCode
    (FoundationStoneTest16BO.finiteSourceInit d)

noncomputable def finiteInitial (d : Nat.Partrec.Code) :=
  FoundationStoneTest16BN.finiteEncode UProgram (primitiveInitial d)

theorem source_halts_iff_finite_mm2 (d : Nat.Partrec.Code) :
    FoundationStoneTest16AH.SourceHalts d ↔
      FoundationStoneTest16BN.FiniteMM2Terminates UProgram (finiteInitial d) := by
  rw [FoundationStoneTest16BR.source_halts_iff_primitive]
  exact FoundationStoneTest16BN.finite_halting_iff UProgram (primitiveInitial d)

theorem finiteInitial_counters (d : Nat.Partrec.Code) :
    (finiteInitial d).a = packedInput d ∧ (finiteInitial d).b = 0 := by
  constructor
  · unfold finiteInitial FoundationStoneTest16BN.finiteEncode primitiveInitial
    change FoundationStoneTest16AM.pack
      (FoundationStoneTest16BJ.fromVec
        (FoundationStoneTest16BQ.packCounters
          (FoundationStoneTest16BO.finiteSourceInit d).ctr)) = packedInput d
    rw [FoundationStoneTest16BR.finiteSourceInit_counters]
    exact (packedInput_exact d).symm
  · rfl

/-- The one remaining fixed-control fact required to turn the pointwise
equivalence above into a many-one reduction on natural inputs. -/
noncomputable def fixedStart := (finiteInitial Nat.Partrec.Code.zero).pc

theorem finiteInitial_pc_constant (d : Nat.Partrec.Code) :
    (finiteInitial d).pc = fixedStart := by
  unfold finiteInitial primitiveInitial fixedStart
  rfl

theorem finiteInitial_exact (d : Nat.Partrec.Code) :
    finiteInitial d = ⟨fixedStart, packedInput d, 0⟩ := by
  cases h : finiteInitial d with
  | mk pc a b =>
      have hp := finiteInitial_pc_constant d
      have hc := finiteInitial_counters d
      simp only [h] at hp hc
      simp only [FoundationStoneTest16AW.State.mk.injEq]
      exact ⟨hp, hc.1, hc.2⟩

def FixedFiniteHalts (n : Nat) : Prop :=
  FoundationStoneTest16BN.FiniteMM2Terminates UProgram
    ⟨fixedStart, n, 0⟩

theorem source_halts_iff_fixed_finite (d : Nat.Partrec.Code) :
    FoundationStoneTest16AH.SourceHalts d ↔ FixedFiniteHalts (packedInput d) := by
  rw [source_halts_iff_finite_mm2]
  rw [finiteInitial_exact]
  rfl

theorem source_to_fixed_finite_is_effective :
    FoundationStoneTest16AH.SourceHalts ≤₀ FixedFiniteHalts :=
  ⟨packedInput, packedInput_computable, source_halts_iff_fixed_finite⟩

theorem fixed_finite_halting_is_not_computable :
    ¬ ComputablePred FixedFiniteHalts := by
  intro h
  exact FoundationStoneTest16AH.source_halting_is_not_computable
    (ComputablePred.computable_of_manyOneReducible
      source_to_fixed_finite_is_effective h)

/-- This is definitionally Mathlib's code-halting predicate at input zero;
there is no Chamber-local variant hidden behind `SourceHalts`. -/
theorem sourceHalts_is_mathlib (d : Nat.Partrec.Code) :
    FoundationStoneTest16AH.SourceHalts d ↔
      (Nat.Partrec.Code.eval d 0).Dom := Iff.rfl

/-- Claims lock: the universal control is a fixed `Classical.choose` witness.
The earned wording is existential, not an executable program listing. -/
theorem fixed_finite_program_exists :
    ∃ (L : Type) (_ : Fintype L) (P : L → FoundationStoneTest16AW.Instr L)
        (start : L) (f : Nat.Partrec.Code → Nat),
      Computable f ∧ ¬ ComputablePred (fun n =>
        (StateTransition.eval (FoundationStoneTest16AW.step P)
          (FoundationStoneTest16AW.State.mk start n 0)).Dom) := by
  refine ⟨FoundationStoneTest16BN.FiniteLabel
      (FoundationStoneTest16BR.ExecutableLabel
        FoundationStoneTest16AH.universalListCode), inferInstance,
    FoundationStoneTest16BN.finiteProgram UProgram, fixedStart, packedInput,
    packedInput_computable, ?_⟩
  exact fixed_finite_halting_is_not_computable

#check @StateTransition.tr_eval_dom
#check @StateTransition.Respects
#check @Fin.sum
#check @Fin.encodeSigma
#check @Fin.decodeSigma
#check @Fin.decodeSigma_encodeSigma
#check FoundationStoneTest16BR.sourceFintype
#check FoundationStoneTest16BR.sourceFiniteIndex

#print axioms packedInput_computable
#print axioms source_to_fixed_finite_is_effective
#print axioms fixed_finite_halting_is_not_computable
#print axioms fixed_finite_program_exists

end FoundationStoneTest16BS
