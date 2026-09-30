import FoundationStoneTest16BS
import FoundationStoneTest16AG

/-!
# 16BT — Serialization into the relay's MM2 instruction list

This file serializes any finite labelled 16AW two-counter program into the
exact list instruction format consumed by 16AG.  Each labelled instruction
gets a three-slot block.  Temporary changes to the other counter implement
unconditional routing and are restored before the next source boundary.

The semantic theorem `serializer_respects` covers increment, successful
decrement, zero routing, and explicit halt.  The fixed program inherited from
16BS is then transferred to 16AG's pc-one halting predicate, preserving the
effective reduction from Mathlib's `Nat.Partrec.Code` halting problem.

Claims and policy boundary:
* the instruction set is the labelled CM2-style variant with a jump on
  successful decrement; it is not the decidable fall-through-only reading of
  Minsky Table 11.1-1;
* the fixed list exists but is not exhibited, because the universal source
  code inherited from 16AH is selected classically;
* repository verification therefore needs a narrowly documented
  classical-choice exception for the Chamber chain while retaining the bans
  on unfinished proofs and newly declared axioms;
* the entrance is externally and computably encoded; in fact it is
  `2 ^ inputStack d`.  No complexity claim is made;
* the pc-one list-to-relay theorem is 16AG.  The separate pc-zero helix bridge
  remains for 16BU.

Verified with Lean 4.35.0-rc2 and pinned Mathlib.
-/

namespace FoundationStoneTest16BT
open FoundationStoneTest16AW
open FoundationStoneTest16AG

noncomputable def zeroFin {L : Type} [Fintype L] (start : L) :
    Fin (Fintype.card L) :=
  ⟨0, Fintype.card_pos_iff.mpr ⟨start⟩⟩

noncomputable def labelEquiv {L : Type} [Fintype L] (start : L) :
    L ≃ Fin (Fintype.card L) :=
  (Fintype.equivFin L).trans
    (Equiv.swap (Fintype.equivFin L start) (zeroFin start))

noncomputable def labelIndex {L : Type} [Fintype L] (start l : L) : Nat :=
  (labelEquiv start l).val

@[simp] theorem labelIndex_start {L : Type} [Fintype L] (start : L) :
    labelIndex start start = 0 := by
  simp [labelIndex, labelEquiv, zeroFin]

noncomputable def address {L : Type} [Fintype L]
    (P : L → Instr L) (start l : L) : Nat :=
  match P l with
  | .halt => 0
  | _ => 1 + 3 * labelIndex start l

noncomputable def blockInstr {L : Type} [Fintype L]
    (P : L → Instr L) (start l : L) (phase : Nat) : MM2Instr :=
  match P l, phase with
  | .halt, _ => .inl false
  | .inc body next, 0 => .inl body
  | .inc body next, 1 => .inl (!body)
  | .inc body next, _ => .inr (!body, address P start next)
  | .dec body positive zero, 0 => .inr (body, address P start positive)
  | .dec body positive zero, 1 => .inl (!body)
  | .dec body positive zero, _ => .inr (!body, address P start zero)

noncomputable def instructionAt {L : Type} [Fintype L]
    (P : L → Instr L) (start : L)
    (k : Fin (3 * Fintype.card L)) : MM2Instr :=
  let i : Fin (Fintype.card L) := ⟨k.val / 3, by
    have hk := k.isLt
    omega⟩
  blockInstr P start ((labelEquiv start).symm i) (k.val % 3)

noncomputable def serialize {L : Type} [Fintype L]
    (P : L → Instr L) (start : L) : MM2Program :=
  List.ofFn (instructionAt P start)

theorem labelIndex_lt {L : Type} [Fintype L] (start l : L) :
    labelIndex start l < Fintype.card L :=
  (labelEquiv start l).isLt

theorem serialized_get {L : Type} [Fintype L]
    (P : L → Instr L) (start l : L) (phase : Nat) (hp : phase < 3) :
    (serialize P start)[3 * labelIndex start l + phase]? =
      some (blockInstr P start l phase) := by
  unfold serialize
  rw [List.getElem?_ofFn]
  have hb : 3 * labelIndex start l + phase < 3 * Fintype.card L := by
    have hi := labelIndex_lt start l
    omega
  simp only [hb]
  apply congrArg some
  unfold instructionAt
  have hdiv : (3 * labelIndex start l + phase) / 3 =
      labelIndex start l := by omega
  have hmod : (3 * labelIndex start l + phase) % 3 = phase := by omega
  simp only [hdiv, hmod]
  have hfin : (⟨labelIndex start l, by
      exact labelIndex_lt start l⟩ : Fin (Fintype.card L)) =
      labelEquiv start l := by
    apply Fin.ext
    rfl
  rw [hfin, Equiv.symm_apply_apply]

theorem mm2Fetch_serialized {L : Type} [Fintype L]
    (P : L → Instr L) (start l : L) (phase : Nat) (hp : phase < 3) :
    mm2Fetch (serialize P start) (1 + 3 * labelIndex start l + phase) =
      some (blockInstr P start l phase) := by
  unfold mm2Fetch
  simp only [show 1 + 3 * labelIndex start l + phase ≠ 0 by omega,
    ↓reduceIte]
  rw [show 1 + 3 * labelIndex start l + phase - 1 =
      3 * labelIndex start l + phase by omega]
  exact serialized_get P start l phase hp

noncomputable def encodeState {L : Type} [Fintype L]
    (P : L → Instr L) (start : L) (s : FoundationStoneTest16AW.State L) :
    FoundationStoneTest16AG.State :=
  ⟨address P start s.pc, s.a, s.b⟩

theorem inc_reaches {L : Type} [Fintype L] (P : L → Instr L) (start l next : L)
    (body : Bool) (a b : Nat) (hi : P l = .inc body next) :
    Relation.TransGen
      (fun u v => mm2Step (serialize P start) u = some v)
      (encodeState P start ⟨l, a, b⟩)
      (encodeState P start
        (FoundationStoneTest16AW.set ⟨l, a, b⟩ next body
          (FoundationStoneTest16AW.get ⟨l, a, b⟩ body + 1))) := by
  cases body
  · let x₁ : FoundationStoneTest16AG.State :=
      ⟨2 + 3 * labelIndex start l, a + 1, b⟩
    let x₂ : FoundationStoneTest16AG.State :=
      ⟨3 + 3 * labelIndex start l, a + 1, b + 1⟩
    apply Relation.TransGen.tail (b := x₂)
    · apply Relation.TransGen.tail (b := x₁)
      · apply Relation.TransGen.single
        rw [show encodeState P start ⟨l, a, b⟩ =
          (⟨1 + 3 * labelIndex start l, a, b⟩ : FoundationStoneTest16AG.State) by
            simp [encodeState, address, hi]]
        have hf : mm2Fetch (serialize P start) (1 + 3 * labelIndex start l) =
            some (blockInstr P start l 0) := by
          simpa using mm2Fetch_serialized P start l 0 (by omega)
        simp [FoundationStoneTest16AG.mm2Step, hf, x₁, blockInstr,
          hi,
          FoundationStoneTest16AG.mm2Execute,
          FoundationStoneTest16AG.get, FoundationStoneTest16AG.set]
        omega
      · have hf : mm2Fetch (serialize P start) (2 + 3 * labelIndex start l) =
            some (blockInstr P start l 1) := by
          rw [show 2 + 3 * labelIndex start l =
            1 + 3 * labelIndex start l + 1 by omega]
          exact mm2Fetch_serialized P start l 1 (by omega)
        simp [FoundationStoneTest16AG.mm2Step, x₁, x₂, hf,
          blockInstr, hi, FoundationStoneTest16AG.mm2Execute,
          FoundationStoneTest16AG.get, FoundationStoneTest16AG.set]
        omega
    · have hf : mm2Fetch (serialize P start) (3 + 3 * labelIndex start l) =
          some (blockInstr P start l 2) := by
        rw [show 3 + 3 * labelIndex start l =
          1 + 3 * labelIndex start l + 2 by omega]
        exact mm2Fetch_serialized P start l 2 (by omega)
      simp [x₂, encodeState, FoundationStoneTest16AW.get,
        FoundationStoneTest16AW.set, FoundationStoneTest16AG.mm2Step,
        hf, blockInstr, hi, FoundationStoneTest16AG.mm2Execute,
        FoundationStoneTest16AG.get, FoundationStoneTest16AG.set]
  · let x₁ : FoundationStoneTest16AG.State :=
      ⟨2 + 3 * labelIndex start l, a, b + 1⟩
    let x₂ : FoundationStoneTest16AG.State :=
      ⟨3 + 3 * labelIndex start l, a + 1, b + 1⟩
    apply Relation.TransGen.tail (b := x₂)
    · apply Relation.TransGen.tail (b := x₁)
      · apply Relation.TransGen.single
        rw [show encodeState P start ⟨l, a, b⟩ =
          (⟨1 + 3 * labelIndex start l, a, b⟩ : FoundationStoneTest16AG.State) by
            simp [encodeState, address, hi]]
        have hf : mm2Fetch (serialize P start) (1 + 3 * labelIndex start l) =
            some (blockInstr P start l 0) := by
          simpa using mm2Fetch_serialized P start l 0 (by omega)
        simp [FoundationStoneTest16AG.mm2Step, hf, x₁, blockInstr, hi,
          FoundationStoneTest16AG.mm2Execute, FoundationStoneTest16AG.get,
          FoundationStoneTest16AG.set]
        omega
      · have hf : mm2Fetch (serialize P start) (2 + 3 * labelIndex start l) =
            some (blockInstr P start l 1) := by
          rw [show 2 + 3 * labelIndex start l =
            1 + 3 * labelIndex start l + 1 by omega]
          exact mm2Fetch_serialized P start l 1 (by omega)
        simp [FoundationStoneTest16AG.mm2Step, x₁, x₂, hf, blockInstr, hi,
          FoundationStoneTest16AG.mm2Execute, FoundationStoneTest16AG.get,
          FoundationStoneTest16AG.set]
        omega
    · have hf : mm2Fetch (serialize P start) (3 + 3 * labelIndex start l) =
          some (blockInstr P start l 2) := by
        rw [show 3 + 3 * labelIndex start l =
          1 + 3 * labelIndex start l + 2 by omega]
        exact mm2Fetch_serialized P start l 2 (by omega)
      simp [x₂, encodeState, FoundationStoneTest16AW.get,
        FoundationStoneTest16AW.set, FoundationStoneTest16AG.mm2Step,
        hf, blockInstr, hi, FoundationStoneTest16AG.mm2Execute,
        FoundationStoneTest16AG.get, FoundationStoneTest16AG.set]

theorem dec_positive_reaches {L : Type} [Fintype L]
    (P : L → Instr L) (start l positive zero : L) (body : Bool) (a b : Nat)
    (hi : P l = .dec body positive zero)
    (hn : FoundationStoneTest16AW.get (⟨l, a, b⟩ : FoundationStoneTest16AW.State L)
      body ≠ 0) :
    Relation.TransGen
      (fun u v => mm2Step (serialize P start) u = some v)
      (encodeState P start ⟨l, a, b⟩)
      (encodeState P start
        (FoundationStoneTest16AW.set ⟨l, a, b⟩ positive body
          (FoundationStoneTest16AW.get ⟨l, a, b⟩ body - 1))) := by
  apply Relation.TransGen.single
  have hf : mm2Fetch (serialize P start) (1 + 3 * labelIndex start l) =
      some (blockInstr P start l 0) := by
    simpa using mm2Fetch_serialized P start l 0 (by omega)
  cases body <;>
    simp [encodeState, address, hi, FoundationStoneTest16AW.get,
      FoundationStoneTest16AW.set, FoundationStoneTest16AG.mm2Step,
      hf, blockInstr, FoundationStoneTest16AG.mm2Execute,
      FoundationStoneTest16AG.get, FoundationStoneTest16AG.set] at hn ⊢
  all_goals omega

theorem dec_zero_reaches {L : Type} [Fintype L]
    (P : L → Instr L) (start l positive zero : L) (body : Bool) (a b : Nat)
    (hi : P l = .dec body positive zero)
    (hz : FoundationStoneTest16AW.get (⟨l, a, b⟩ : FoundationStoneTest16AW.State L)
      body = 0) :
    Relation.TransGen
      (fun u v => mm2Step (serialize P start) u = some v)
      (encodeState P start ⟨l, a, b⟩)
      (encodeState P start (⟨zero, a, b⟩ : FoundationStoneTest16AW.State L)) := by
  cases body
  · simp [FoundationStoneTest16AW.get] at hz
    let x₁ : FoundationStoneTest16AG.State :=
      ⟨2 + 3 * labelIndex start l, a, b⟩
    let x₂ : FoundationStoneTest16AG.State :=
      ⟨3 + 3 * labelIndex start l, a, b + 1⟩
    apply Relation.TransGen.tail (b := x₂)
    · apply Relation.TransGen.tail (b := x₁)
      · apply Relation.TransGen.single
        have hf : mm2Fetch (serialize P start) (1 + 3 * labelIndex start l) =
            some (blockInstr P start l 0) := by
          simpa using mm2Fetch_serialized P start l 0 (by omega)
        simp [encodeState, address, hi, x₁, FoundationStoneTest16AG.mm2Step,
          hf, blockInstr, FoundationStoneTest16AG.mm2Execute,
          FoundationStoneTest16AG.get, FoundationStoneTest16AG.set, hz]
        omega
      · have hf : mm2Fetch (serialize P start) (2 + 3 * labelIndex start l) =
            some (blockInstr P start l 1) := by
          rw [show 2 + 3 * labelIndex start l =
            1 + 3 * labelIndex start l + 1 by omega]
          exact mm2Fetch_serialized P start l 1 (by omega)
        simp [x₁, x₂, FoundationStoneTest16AG.mm2Step, hf, blockInstr, hi,
          FoundationStoneTest16AG.mm2Execute, FoundationStoneTest16AG.get,
          FoundationStoneTest16AG.set]
        omega
    · have hf : mm2Fetch (serialize P start) (3 + 3 * labelIndex start l) =
          some (blockInstr P start l 2) := by
        rw [show 3 + 3 * labelIndex start l =
          1 + 3 * labelIndex start l + 2 by omega]
        exact mm2Fetch_serialized P start l 2 (by omega)
      simp [x₂, encodeState, FoundationStoneTest16AG.mm2Step, hf, blockInstr, hi,
        FoundationStoneTest16AG.mm2Execute, FoundationStoneTest16AG.get,
        FoundationStoneTest16AG.set]
  · simp [FoundationStoneTest16AW.get] at hz
    let x₁ : FoundationStoneTest16AG.State :=
      ⟨2 + 3 * labelIndex start l, a, b⟩
    let x₂ : FoundationStoneTest16AG.State :=
      ⟨3 + 3 * labelIndex start l, a + 1, b⟩
    apply Relation.TransGen.tail (b := x₂)
    · apply Relation.TransGen.tail (b := x₁)
      · apply Relation.TransGen.single
        have hf : mm2Fetch (serialize P start) (1 + 3 * labelIndex start l) =
            some (blockInstr P start l 0) := by
          simpa using mm2Fetch_serialized P start l 0 (by omega)
        simp [encodeState, address, hi, x₁, FoundationStoneTest16AG.mm2Step,
          hf, blockInstr, FoundationStoneTest16AG.mm2Execute,
          FoundationStoneTest16AG.get, FoundationStoneTest16AG.set, hz]
        omega
      · have hf : mm2Fetch (serialize P start) (2 + 3 * labelIndex start l) =
            some (blockInstr P start l 1) := by
          rw [show 2 + 3 * labelIndex start l =
            1 + 3 * labelIndex start l + 1 by omega]
          exact mm2Fetch_serialized P start l 1 (by omega)
        simp [x₁, x₂, FoundationStoneTest16AG.mm2Step, hf, blockInstr, hi,
          FoundationStoneTest16AG.mm2Execute, FoundationStoneTest16AG.get,
          FoundationStoneTest16AG.set]
        omega
    · have hf : mm2Fetch (serialize P start) (3 + 3 * labelIndex start l) =
          some (blockInstr P start l 2) := by
        rw [show 3 + 3 * labelIndex start l =
          1 + 3 * labelIndex start l + 2 by omega]
        exact mm2Fetch_serialized P start l 2 (by omega)
      simp [x₂, encodeState, FoundationStoneTest16AG.mm2Step, hf, blockInstr, hi,
        FoundationStoneTest16AG.mm2Execute, FoundationStoneTest16AG.get,
        FoundationStoneTest16AG.set]

def Encodes {L : Type} [Fintype L] (P : L → Instr L) (start : L)
    (s : FoundationStoneTest16AW.State L) (t : FoundationStoneTest16AG.State) : Prop :=
  encodeState P start s = t

theorem serializer_respects {L : Type} [Fintype L]
    (P : L → Instr L) (start : L) :
    StateTransition.Respects (FoundationStoneTest16AW.step P)
      (mm2Step (serialize P start)) (Encodes P start) := by
  intro s t ht
  unfold Encodes at ht
  subst t
  cases hi : P s.pc with
  | halt =>
      simp [FoundationStoneTest16AW.step, hi, encodeState, address,
        FoundationStoneTest16AG.mm2Step, FoundationStoneTest16AG.mm2Fetch]
  | inc body next =>
      simp only [FoundationStoneTest16AW.step, hi]
      exact ⟨_, rfl, inc_reaches P start s.pc next body s.a s.b hi⟩
  | dec body positive zero =>
      simp only [FoundationStoneTest16AW.step, hi]
      by_cases hz : FoundationStoneTest16AW.get s body = 0
      · simp only [hz, ↓reduceIte]
        refine ⟨encodeState P start { s with pc := zero }, rfl, ?_⟩
        cases s
        exact dec_zero_reaches P start _ positive zero body _ _ hi hz
      · simp only [hz, ↓reduceIte]
        refine ⟨encodeState P start
          (FoundationStoneTest16AW.set s positive body
            (FoundationStoneTest16AW.get s body - 1)), rfl, ?_⟩
        cases s
        exact dec_positive_reaches P start _ positive zero body _ _ hi hz

theorem serialized_eval_dom_iff {L : Type} [Fintype L]
    (P : L → Instr L) (start : L) (s : FoundationStoneTest16AW.State L) :
    (StateTransition.eval (mm2Step (serialize P start))
      (encodeState P start s)).Dom ↔
    (StateTransition.eval (FoundationStoneTest16AW.step P) s).Dom :=
  StateTransition.tr_eval_dom (serializer_respects P start) rfl

theorem mm2Run_none_iff_eval_dom (p : MM2Program) (s : FoundationStoneTest16AG.State) :
    (∃ n, FoundationStoneTest16AG.mm2Run p n s = none) ↔
      (StateTransition.eval (mm2Step p) s).Dom := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing s with
    | zero => simp [FoundationStoneTest16AG.mm2Run] at hn
    | succ n ih =>
        simp only [FoundationStoneTest16AG.mm2Run] at hn
        cases hs : mm2Step p s with
        | none =>
            exact ⟨s, StateTransition.mem_eval.mpr
              ⟨Relation.ReflTransGen.refl, hs⟩⟩
        | some s' =>
            simp only [hs] at hn
            obtain ⟨t, ht⟩ := ih s' hn
            refine ⟨t, StateTransition.mem_eval.mpr ?_⟩
            obtain ⟨hr, hstop⟩ := StateTransition.mem_eval.mp ht
            exact ⟨Relation.ReflTransGen.head hs hr, hstop⟩
  · rintro ⟨t, ht⟩
    obtain ⟨hr, hstop⟩ := StateTransition.mem_eval.mp ht
    have reach_run : ∀ {a t : FoundationStoneTest16AG.State},
        StateTransition.Reaches (mm2Step p) a t → mm2Step p t = none →
          ∃ n, FoundationStoneTest16AG.mm2Run p n a = none := by
      intro a t hat
      induction hat using Relation.ReflTransGen.head_induction_on with
      | refl =>
          intro h
          exact ⟨1, by simp [FoundationStoneTest16AG.mm2Run, h]⟩
      | head hs _ ih =>
          intro h
          obtain ⟨n, hn⟩ := ih h
          change mm2Step p _ = some _ at hs
          exact ⟨n + 1, by simp [FoundationStoneTest16AG.mm2Run, hs, hn]⟩
    exact reach_run hr hstop

attribute [local instance] FoundationStoneTest16BR.sourceFintype
  FoundationStoneTest16BR.sourceFiniteIndex

noncomputable abbrev FixedLabel :=
  FoundationStoneTest16BN.FiniteLabel
    (FoundationStoneTest16BR.ExecutableLabel
      FoundationStoneTest16AH.universalListCode)

noncomputable abbrev FixedProgram : FixedLabel → Instr FixedLabel :=
  FoundationStoneTest16BN.finiteProgram FoundationStoneTest16BS.UProgram

theorem fixedStart_not_halt :
    FixedProgram FoundationStoneTest16BS.fixedStart ≠ .halt := by
  intro hh
  have hall : ∀ n, FoundationStoneTest16BS.FixedFiniteHalts n := by
    intro n
    unfold FoundationStoneTest16BS.FixedFiniteHalts
      FoundationStoneTest16BN.FiniteMM2Terminates
    rw [Part.dom_iff_mem]
    refine ⟨⟨FoundationStoneTest16BS.fixedStart, n, 0⟩,
      StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, ?_⟩⟩
    simp [FoundationStoneTest16AW.step, hh]
  apply FoundationStoneTest16BS.fixed_finite_halting_is_not_computable
  rw [ComputablePred.computable_iff]
  refine ⟨fun _ => true, Computable.const true, ?_⟩
  funext n
  apply propext
  simp [hall n]

noncomputable def fixedSerializedProgram : MM2Program :=
  serialize FixedProgram FoundationStoneTest16BS.fixedStart

def FixedSerializedHalts (n : Nat) : Prop :=
  FoundationStoneTest16AG.MM2Halts (fixedSerializedProgram, (n, 0))

theorem fixed_start_encodes_at_pc_one (n : Nat) :
    encodeState FixedProgram FoundationStoneTest16BS.fixedStart
      (⟨FoundationStoneTest16BS.fixedStart, n, 0⟩ :
        FoundationStoneTest16AW.State FixedLabel) =
      (⟨1, n, 0⟩ : FoundationStoneTest16AG.State) := by
  simp [encodeState, address, fixedStart_not_halt, labelIndex_start]

theorem fixed_finite_iff_serialized (n : Nat) :
    FoundationStoneTest16BS.FixedFiniteHalts n ↔ FixedSerializedHalts n := by
  unfold FoundationStoneTest16BS.FixedFiniteHalts
    FoundationStoneTest16BN.FiniteMM2Terminates FixedSerializedHalts
    FoundationStoneTest16AG.MM2Halts fixedSerializedProgram
  rw [mm2Run_none_iff_eval_dom]
  rw [← fixed_start_encodes_at_pc_one]
  exact (serialized_eval_dom_iff FixedProgram
    FoundationStoneTest16BS.fixedStart
    ⟨FoundationStoneTest16BS.fixedStart, n, 0⟩).symm

theorem source_halts_iff_fixed_serialized (d : Nat.Partrec.Code) :
    FoundationStoneTest16AH.SourceHalts d ↔
      FixedSerializedHalts (FoundationStoneTest16BS.packedInput d) := by
  rw [FoundationStoneTest16BS.source_halts_iff_fixed_finite]
  exact fixed_finite_iff_serialized _

theorem source_to_fixed_serialized_is_effective :
    FoundationStoneTest16AH.SourceHalts ≤₀ FixedSerializedHalts :=
  ⟨FoundationStoneTest16BS.packedInput,
    FoundationStoneTest16BS.packedInput_computable,
    source_halts_iff_fixed_serialized⟩

theorem fixed_serialized_halting_is_not_computable :
    ¬ ComputablePred FixedSerializedHalts := by
  intro h
  exact FoundationStoneTest16AH.source_halting_is_not_computable
    (ComputablePred.computable_of_manyOneReducible
      source_to_fixed_serialized_is_effective h)

/-- Existential claims lock: there is one fixed finite 16AG-format instruction
list whose pc-one halting predicate is undecidable.  The list depends on the
same classical witness as 16AH/16BS, so this does not exhibit its table. -/
theorem fixed_serialized_program_exists :
    ∃ p : MM2Program,
      ¬ ComputablePred (fun n => FoundationStoneTest16AG.MM2Halts (p, (n, 0))) :=
  ⟨fixedSerializedProgram, fixed_serialized_halting_is_not_computable⟩

/-! Audit-facing precision repairs. -/

/-- The source is the labelled two-counter variant: increment names its next
label, and decrement names both its positive and zero successors.  In
particular this is not Minsky's decidable fall-through-only Table 11.1-1
variant; the successful-decrement jump is present explicitly. -/
theorem labelled_dec_has_two_successors {L : Type} (body : Bool) (positive zero : L) :
    (Instr.dec body positive zero : Instr L) = .dec body positive zero := rfl

theorem code_cons_cons_is_twelve :
    FoundationStoneTest16AT.code
      [Turing.PartrecToTM2.Γ'.cons, Turing.PartrecToTM2.Γ'.cons] = 12 := rfl

theorem code_bit_zero_is_three :
    FoundationStoneTest16AT.code [Turing.PartrecToTM2.Γ'.bit0] = 3 := rfl

theorem code_bit_one_is_four :
    FoundationStoneTest16AT.code [Turing.PartrecToTM2.Γ'.bit1] = 4 := rfl

theorem packedInput_is_power_of_two (d : Nat.Partrec.Code) :
    FoundationStoneTest16BS.packedInput d =
      2 ^ FoundationStoneTest16BS.inputStack d := by
  simp [FoundationStoneTest16BS.packedInput, FoundationStoneTest16BS.pack,
    FoundationStoneTest16BS.sourceFive]

/-- Named view of the five entrance counters; this avoids relying on nested
tuple projections in statements added after 16BS. -/
structure EntranceFive where
  main : Nat
  rev : Nat
  aux : Nat
  stack : Nat
  temp : Nat
deriving DecidableEq, Repr

def EntranceFive.toTuple (s : EntranceFive) : FoundationStoneTest16BS.Five :=
  (s.main, (s.rev, (s.aux, (s.stack, s.temp))))

def namedEntrance (d : Nat.Partrec.Code) : EntranceFive :=
  ⟨FoundationStoneTest16BS.inputStack d, 0, 0, 0, 0⟩

theorem namedEntrance_exact (d : Nat.Partrec.Code) :
    (namedEntrance d).toTuple = FoundationStoneTest16BS.sourceFive d := rfl

/-- The mid-run packing fact used earlier in the chain is injectivity, not an
entrance-only coincidence. -/
theorem five_counter_pack_is_injective :
    Function.Injective FoundationStoneTest16AM.pack :=
  FoundationStoneTest16AM.pack_injective

#print axioms FoundationStoneTest16BS.binaryFold_computable
#print axioms FoundationStoneTest16BS.packedInput_computable
#print axioms FoundationStoneTest16BS.source_to_fixed_finite_is_effective
#print axioms FoundationStoneTest16BS.fixed_finite_halting_is_not_computable
#print axioms FoundationStoneTest16BS.fixed_finite_program_exists

#print axioms serializer_respects
#print axioms fixed_serialized_halting_is_not_computable
#print axioms fixed_serialized_program_exists
end FoundationStoneTest16BT
