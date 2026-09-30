import FoundationStoneTest16BT
import FoundationStoneTest16AF

/-!
# 16BU — Closing the Turing Chamber at the helix

16AG's compiled relay enters at pc 1, while 16AF's relay and helix problems
enter at pc 0.  This file closes that last convention gap using only 16AF's
native instructions.

There is no primitive no-op or goto in 16AF.  The bridge therefore prepends a
two-instruction counter-neutral route: increment body B, then decrement it and
jump to the relocated old pc 1.  Every old address is shifted by two.  Lean
proves that both counters are restored, every later step and bounded run
commute with relocation, and halting is equivalent in both directions.

Composing 16BT, 16AG, this bridge, and 16AF yields:
* an effective many-one reduction from Mathlib's code-halting predicate to
  the Wooden Idol helix halting predicate;
* noncomputability of the global helix halting predicate;
* existence of one fixed finite helix program whose halting is undecidable as
  its first entrance height varies;
* an explicit statement that the helix's native decrement/height-zero branch
  supplies the zero test.

Claims boundary:
* the fixed program is existential rather than printed, because its universal
  source code is the classical witness inherited from 16AH;
* the entrance height is externally computable but exponentially encoded;
* this is a computability/undecidability theorem, not a complexity theorem and
  not a P-versus-NP claim;
* Rice-style future-behaviour corollaries and the one-counter decidability
  control remain separate follow-up results.

Verified with Lean 4.35.0-rc2 and pinned Mathlib.
-/

namespace FoundationStoneTest16BU

abbrev AInstr := FoundationStoneTest16AG.Instr
abbrev AProgram := FoundationStoneTest16AG.Program
abbrev FInstr := FoundationStoneTest16AF.Instr
abbrev FProgram := FoundationStoneTest16AF.Program

def relocateInstr : AInstr → FInstr
  | .inl () => FoundationStoneTest16AF.halt
  | .inr (.inl (body, next)) => FoundationStoneTest16AF.inc body (next + 2)
  | .inr (.inr (body, next, zeroTarget)) =>
      FoundationStoneTest16AF.dec body (next + 2) (zeroTarget + 2)

/-- A counter-neutral two-instruction entrance followed by the relocated
pc-one relay. -/
def zeroStartProgram (p : AProgram) : FProgram :=
  FoundationStoneTest16AF.inc true 1 ::
  FoundationStoneTest16AF.dec true 3 3 :: p.map relocateInstr

def relocateState (s : FoundationStoneTest16AG.State) :
    FoundationStoneTest16AF.CState :=
  ⟨s.pc + 2, s.a, s.b⟩

theorem fetch_relocated (p : AProgram) (pc : Nat) :
    FoundationStoneTest16AF.fetch (zeroStartProgram p) (pc + 2) =
      relocateInstr (FoundationStoneTest16AG.fetch p pc) := by
  simp only [FoundationStoneTest16AF.fetch, zeroStartProgram,
    List.getElem?_cons_succ, List.getElem?_map, FoundationStoneTest16AG.fetch]
  cases h : p[pc]? with
  | none => rfl
  | some i =>
      cases i with
      | inl u => cases u; rfl
      | inr x =>
          cases x with
          | inl y => cases y; rfl
          | inr y => cases y; rfl

theorem step_relocated (p : AProgram) (s : FoundationStoneTest16AG.State) :
    FoundationStoneTest16AF.cstep (zeroStartProgram p) (relocateState s) =
      (FoundationStoneTest16AG.step p s).map relocateState := by
  cases h : FoundationStoneTest16AG.fetch p s.pc with
  | inl u =>
      cases u
      simp [FoundationStoneTest16AG.step, h, FoundationStoneTest16AG.execute,
        FoundationStoneTest16AF.cstep, relocateState, fetch_relocated,
        relocateInstr, FoundationStoneTest16AF.halt]
  | inr x =>
      cases x with
      | inl y =>
          rcases y with ⟨body, next⟩
          cases body <;>
            simp [FoundationStoneTest16AG.step, h, FoundationStoneTest16AG.execute,
        FoundationStoneTest16AG.get, FoundationStoneTest16AG.set,
              FoundationStoneTest16AF.cstep, FoundationStoneTest16AF.cget,
              FoundationStoneTest16AF.cset, relocateState, fetch_relocated,
              relocateInstr, FoundationStoneTest16AF.inc]
      | inr y =>
          rcases y with ⟨body, next, zeroTarget⟩
          cases body <;>
            simp [FoundationStoneTest16AG.step, h, FoundationStoneTest16AG.execute,
              FoundationStoneTest16AG.get, FoundationStoneTest16AG.set,
              FoundationStoneTest16AF.cstep, FoundationStoneTest16AF.cget,
              FoundationStoneTest16AF.cset, relocateState, fetch_relocated,
              relocateInstr, FoundationStoneTest16AF.dec]
          all_goals split <;> rfl

theorem run_relocated (p : AProgram) : ∀ n s,
    FoundationStoneTest16AF.crun (zeroStartProgram p) n (relocateState s) =
      (FoundationStoneTest16AG.run p n s).map relocateState := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      simp only [FoundationStoneTest16AF.crun, FoundationStoneTest16AG.run]
      rw [step_relocated]
      cases hs : FoundationStoneTest16AG.step p s with
      | none => rfl
      | some s' =>
          simp only [Option.map_some]
          exact ih s'

theorem zeroStart_first_step (p : AProgram) (a b : Nat) :
    FoundationStoneTest16AF.cstep (zeroStartProgram p) ⟨0, a, b⟩ =
      some ⟨1, a, b + 1⟩ := by
  simp [FoundationStoneTest16AF.cstep, FoundationStoneTest16AF.fetch,
    zeroStartProgram, FoundationStoneTest16AF.cget, FoundationStoneTest16AF.cset,
    FoundationStoneTest16AF.inc]

theorem zeroStart_second_step (p : AProgram) (a b : Nat) :
    FoundationStoneTest16AF.cstep (zeroStartProgram p) ⟨1, a, b + 1⟩ =
      some ⟨3, a, b⟩ := by
  simp [FoundationStoneTest16AF.cstep, FoundationStoneTest16AF.fetch,
    zeroStartProgram, FoundationStoneTest16AF.cget, FoundationStoneTest16AF.cset,
    FoundationStoneTest16AF.dec]

theorem run_from_zero (p : AProgram) (n a b : Nat) :
    FoundationStoneTest16AF.crun (zeroStartProgram p) (n + 2) ⟨0, a, b⟩ =
      (FoundationStoneTest16AG.run p n ⟨1, a, b⟩).map relocateState := by
  rw [show n + 2 = (n + 1) + 1 by omega]
  simp only [FoundationStoneTest16AF.crun, zeroStart_first_step,
    zeroStart_second_step]
  exact run_relocated p n ⟨1, a, b⟩

abbrev AProblem := FoundationStoneTest16AG.RelayProblem
abbrev FProblem := FoundationStoneTest16AF.Problem

def zeroStartProblem (q : AProblem) : FProblem :=
  (zeroStartProgram q.1, q.2)

theorem relay_halts_from_zero (q : AProblem) :
    FoundationStoneTest16AG.RelayHalts q ↔
      FoundationStoneTest16AF.RelayHalts (zeroStartProblem q) := by
  rcases q with ⟨p, a, b⟩
  unfold FoundationStoneTest16AG.RelayHalts
    FoundationStoneTest16AF.RelayHalts zeroStartProblem
    FoundationStoneTest16AF.counterStart
  change (∃ n, FoundationStoneTest16AG.run p n ⟨1, a, b⟩ = none) ↔
    ∃ n, FoundationStoneTest16AF.crun (zeroStartProgram p) n ⟨0, a, b⟩ = none
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 2, ?_⟩
    rw [run_from_zero]
    rw [hn]
    rfl
  · rintro ⟨m, hm⟩
    cases m with
    | zero => simp [FoundationStoneTest16AF.crun] at hm
    | succ m =>
        cases m with
        | zero =>
            simp [FoundationStoneTest16AF.crun, zeroStart_first_step] at hm
        | succ n =>
            have hr := run_from_zero p n a b
            rw [show n + 1 + 1 = n + 2 by omega, hr] at hm
            cases hrun : FoundationStoneTest16AG.run p n ⟨1, a, b⟩ with
            | none => exact ⟨n, hrun⟩
            | some s => simp [hrun] at hm

noncomputable def fixedRelayProgram : AProgram :=
  FoundationStoneTest16AG.compile FoundationStoneTest16BT.fixedSerializedProgram

noncomputable def fixedZeroRelayProgram : FProgram :=
  zeroStartProgram fixedRelayProgram

def FixedRelayHalts (n : Nat) : Prop :=
  FoundationStoneTest16AF.RelayHalts (fixedZeroRelayProgram, (n, 0))

def FixedHelixHalts (n : Nat) : Prop :=
  FoundationStoneTest16AF.HelixHalts (fixedZeroRelayProgram, (n, 0))

theorem fixed_serialized_iff_relay (n : Nat) :
    FoundationStoneTest16BT.FixedSerializedHalts n ↔ FixedRelayHalts n := by
  change FoundationStoneTest16AG.MM2Halts
      (FoundationStoneTest16BT.fixedSerializedProgram, (n, 0)) ↔
    FoundationStoneTest16AF.RelayHalts (fixedZeroRelayProgram, (n, 0))
  rw [FoundationStoneTest16AG.halting_compiles]
  exact relay_halts_from_zero
    (FoundationStoneTest16AG.compileProblem
      (FoundationStoneTest16BT.fixedSerializedProgram, (n, 0)))

theorem fixed_relay_iff_helix (n : Nat) :
    FixedRelayHalts n ↔ FixedHelixHalts n :=
  FoundationStoneTest16AF.relay_halts_iff_helix_halts _

theorem fixed_serialized_iff_helix (n : Nat) :
    FoundationStoneTest16BT.FixedSerializedHalts n ↔ FixedHelixHalts n := by
  rw [fixed_serialized_iff_relay, fixed_relay_iff_helix]

theorem source_halts_iff_fixed_helix (d : Nat.Partrec.Code) :
    FoundationStoneTest16AH.SourceHalts d ↔
      FixedHelixHalts (FoundationStoneTest16BS.packedInput d) := by
  rw [FoundationStoneTest16BT.source_halts_iff_fixed_serialized]
  exact fixed_serialized_iff_helix _

theorem source_to_fixed_helix_is_effective :
    FoundationStoneTest16AH.SourceHalts ≤₀ FixedHelixHalts :=
  ⟨FoundationStoneTest16BS.packedInput,
    FoundationStoneTest16BS.packedInput_computable,
    source_halts_iff_fixed_helix⟩

theorem fixed_helix_halting_is_not_computable :
    ¬ ComputablePred FixedHelixHalts := by
  intro h
  exact FoundationStoneTest16AH.source_halting_is_not_computable
    (ComputablePred.computable_of_manyOneReducible
      source_to_fixed_helix_is_effective h)

theorem zero_start_is_counter_neutral (p : AProgram) (a b : Nat) :
    FoundationStoneTest16AF.crun (zeroStartProgram p) 2 ⟨0, a, b⟩ =
      some ⟨3, a, b⟩ := by
  simpa [relocateState, FoundationStoneTest16AG.run] using run_from_zero p 0 a b

/-- The zero test used by the reduction is 16AF's native helix decrement:
zero body-height selects the instruction's explicit zero successor. -/
theorem native_helix_zero_test (p : FProgram) (h : FoundationStoneTest16AF.HState)
    (body : Bool) (next zeroTarget : Nat)
    (hf : FoundationStoneTest16AF.fetch p h.pc =
      FoundationStoneTest16AF.dec body next zeroTarget)
    (hz : (FoundationStoneTest16AF.bget h body).height = 0) :
    FoundationStoneTest16AF.hstep p h = some { h with pc := zeroTarget } := by
  simp [FoundationStoneTest16AF.hstep, hf, FoundationStoneTest16AF.dec, hz]

noncomputable def fixedHelixProblem (n : Nat) : FProblem :=
  (fixedZeroRelayProgram, (n, 0))

theorem fixedHelixProblem_computable : Computable fixedHelixProblem := by
  unfold fixedHelixProblem
  exact (Computable.const fixedZeroRelayProgram).pair
    (Computable.id.pair (Computable.const 0))

theorem fixed_helix_to_global_is_effective :
    FixedHelixHalts ≤₀ FoundationStoneTest16AF.HelixHalts :=
  ⟨fixedHelixProblem, fixedHelixProblem_computable, fun _ => Iff.rfl⟩

theorem helix_halting_is_not_computable :
    ¬ ComputablePred FoundationStoneTest16AF.HelixHalts := by
  intro h
  exact fixed_helix_halting_is_not_computable
    (ComputablePred.computable_of_manyOneReducible
      fixed_helix_to_global_is_effective h)

noncomputable def sourceToHelixProblem (d : Nat.Partrec.Code) : FProblem :=
  fixedHelixProblem (FoundationStoneTest16BS.packedInput d)

theorem sourceToHelixProblem_computable : Computable sourceToHelixProblem :=
  fixedHelixProblem_computable.comp FoundationStoneTest16BS.packedInput_computable

theorem source_to_helix_is_effective :
    FoundationStoneTest16AH.SourceHalts ≤₀ FoundationStoneTest16AF.HelixHalts :=
  ⟨sourceToHelixProblem, sourceToHelixProblem_computable,
    source_halts_iff_fixed_helix⟩

/-- Final existential claims lock: a single fixed two-body helix program has
an undecidable halting predicate as its first entrance height varies. -/
theorem fixed_helix_program_exists :
    ∃ p : FProgram,
      ¬ ComputablePred (fun n =>
        FoundationStoneTest16AF.HelixHalts (p, (n, 0))) :=
  ⟨fixedZeroRelayProgram, fixed_helix_halting_is_not_computable⟩

theorem turing_chamber_16BU_certificate :
    (∀ p a b, FoundationStoneTest16AF.crun (zeroStartProgram p) 2 ⟨0, a, b⟩ =
      some ⟨3, a, b⟩) ∧
    (∀ d, FoundationStoneTest16AH.SourceHalts d ↔
      FixedHelixHalts (FoundationStoneTest16BS.packedInput d)) ∧
    FoundationStoneTest16AH.SourceHalts ≤₀ FoundationStoneTest16AF.HelixHalts ∧
    ¬ ComputablePred FixedHelixHalts ∧
    ¬ ComputablePred FoundationStoneTest16AF.HelixHalts :=
  ⟨zero_start_is_counter_neutral, source_halts_iff_fixed_helix,
    source_to_helix_is_effective, fixed_helix_halting_is_not_computable,
    helix_halting_is_not_computable⟩

#print axioms zero_start_is_counter_neutral
#print axioms native_helix_zero_test
#print axioms relay_halts_from_zero
#print axioms fixed_serialized_iff_helix
#print axioms source_to_helix_is_effective
#print axioms fixed_helix_halting_is_not_computable
#print axioms helix_halting_is_not_computable
#print axioms fixed_helix_program_exists
#print axioms turing_chamber_16BU_certificate

end FoundationStoneTest16BU
