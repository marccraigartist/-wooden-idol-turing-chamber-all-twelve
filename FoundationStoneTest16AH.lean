import Mathlib.Computability.Halting
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# THE TURING CHAMBER — TEST 16AH: THE MATHLIB TM2 SOURCE DOOR

Lean 4.35.0-rc2 / Mathlib.

Mathlib's authenticated undecidable predicate uses `Nat.Partrec.Code`, whereas
`Turing.PartrecToTM2.tr_eval` executes the list-based `Turing.ToPartrec.Code`.
This file closes that representational seam without postulating a syntax translator.

Mathlib proves that every partial-recursive function has a list-code.  Apply that
theorem once to the universal evaluator `Nat.Partrec.Code.eval`, obtaining one
fixed interpreter `universalListCode`.  A source program `c` is supplied to
that interpreter as data, on the exact tape `[encode c, 0]`.

Lean certifies:

1. the fixed list-code evaluates that tape exactly when source code `c`
   evaluates at zero;
2. `PartrecToTM2.tr_eval` turns this into an exact equality of partial TM2 runs;
3. the exact initial configuration is identified field-by-field;
4. the exact target configuration is `PartrecToTM2.halt [answer]`;
5. source halting is equivalent to termination of the fixed Mathlib TM2 machine;
6. construction of the varying source tape is primitive recursive;
7. red control: the empty tape is not the authenticated source tape.

The chosen interpreter is a fixed mathematical constant.  The varying translation
from source codes to its input is effective; no halting oracle is used.
-/

namespace FoundationStoneTest16AH

open Nat.Partrec
open Nat.Partrec.Code
open Turing

/-- The authenticated source predicate from 16AE. -/
def SourceHalts (c : Nat.Partrec.Code) : Prop := (Nat.Partrec.Code.eval c 0).Dom

theorem source_halting_is_not_computable : ¬ ComputablePred SourceHalts := by
  exact ComputablePred.halting_problem 0

/-! ## 1. A fixed list-program interpreting encoded source programs -/

/-- The universal evaluator, viewed as a two-argument vector function. -/
def universalVectorEval (v : List.Vector Nat 2) : Part Nat :=
  Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode v.head) v.tail.head

theorem universalVectorEval_partrec : Nat.Partrec' universalVectorEval := by
  change Nat.Partrec' (fun v =>
    Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode v.head) v.tail.head)
  apply Nat.Partrec'.of_eq
    (Nat.Partrec'.part_iff₂.mpr
      (Nat.Partrec.Code.eval_part.comp
        ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst)
        Computable.snd).to₂)
  intro v
  rw [← Nat.Partrec.Code.ofNatCode_eq]

/-- One fixed Mathlib list-code implementing the universal evaluator. -/
noncomputable def universalListCode : Turing.ToPartrec.Code :=
  Classical.choose (Turing.ToPartrec.Code.exists_code universalVectorEval_partrec)

theorem universalListCode_spec (v : List.Vector Nat 2) :
    universalListCode.eval v.1 = pure <$> universalVectorEval v :=
  Classical.choose_spec
    (Turing.ToPartrec.Code.exists_code universalVectorEval_partrec) v

/-- The varying source tape.  Only data changes; the TM2 program is fixed. -/
def sourceTape (c : Nat.Partrec.Code) : List Nat := [Encodable.encode c, 0]

theorem sourceTape_primrec : Primrec sourceTape := by
  exact Primrec.list_cons.comp Primrec.encode
    (Primrec.list_cons.comp (Primrec.const 0) (Primrec.const []))

theorem sourceTape_computable : Computable sourceTape := sourceTape_primrec.to_comp

theorem universal_on_source (c : Nat.Partrec.Code) :
    universalListCode.eval (sourceTape c) =
      (fun n => [n]) <$> Nat.Partrec.Code.eval c 0 := by
  let v : List.Vector Nat 2 := ⟨sourceTape c, by simp [sourceTape]⟩
  have h := universalListCode_spec v
  change universalListCode.eval (sourceTape c) =
    pure <$> universalVectorEval v at h
  rw [h]
  unfold universalVectorEval
  simp only [v, sourceTape, List.Vector.head, List.Vector.tail]
  rw [show Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c by
    exact Denumerable.ofNat_encode c]
  rfl

/-! ## 2–5. Exact TM2 configurations and the halting equivalence -/

abbrev TMConfig := Turing.PartrecToTM2.Cfg'

/-- The exact varying initial configuration of Mathlib's fixed evaluator. -/
noncomputable def sourceInit (c : Nat.Partrec.Code) : TMConfig :=
  Turing.PartrecToTM2.init universalListCode (sourceTape c)

/-- Termination of Mathlib's fixed TM2 transition function from a configuration. -/
def TM2Terminates (cfg : TMConfig) : Prop :=
  (StateTransition.eval
    (Turing.TM2.step Turing.PartrecToTM2.tr) cfg).Dom

/-- The initial configuration, exposed field-by-field. -/
theorem sourceInit_fields (c : Nat.Partrec.Code) :
    sourceInit c =
      ⟨some (Turing.PartrecToTM2.trNormal universalListCode
          Turing.PartrecToTM2.Cont'.halt),
       none,
       Turing.PartrecToTM2.K'.elim
         (Turing.PartrecToTM2.trList (sourceTape c)) [] [] []⟩ :=
  rfl

/-- Exact partial-run equation: any source answer becomes Mathlib's exact halt
configuration carrying the singleton result tape. -/
theorem source_tm2_run (c : Nat.Partrec.Code) :
    StateTransition.eval
        (Turing.TM2.step Turing.PartrecToTM2.tr) (sourceInit c) =
      (fun n => Turing.PartrecToTM2.halt [n]) <$>
        Nat.Partrec.Code.eval c 0 := by
  unfold sourceInit
  rw [Turing.PartrecToTM2.tr_eval, universal_on_source]
  rw [Part.map_eq_map, Part.map_eq_map, Part.map_map]
  rfl

theorem dom_map_iff {α β : Type} (f : α → β) (p : Part α) :
    (f <$> p).Dom ↔ p.Dom := by
  simp only [Part.dom_iff_mem, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨_, a, ha, _⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨f a, a, ha, rfl⟩

/-- The authenticated source problem terminates exactly when the fixed Mathlib
TM2 machine terminates from the displayed initial configuration. -/
theorem source_halts_iff_tm2 (c : Nat.Partrec.Code) :
    SourceHalts c ↔ TM2Terminates (sourceInit c) := by
  unfold SourceHalts TM2Terminates
  rw [source_tm2_run, dom_map_iff]

/-- If source evaluation returns `n`, the exact reached target is
`PartrecToTM2.halt [n]`. -/
theorem source_answer_is_exact_target (c : Nat.Partrec.Code) (n : Nat)
    (h : n ∈ Nat.Partrec.Code.eval c 0) :
    Turing.PartrecToTM2.halt [n] ∈
      StateTransition.eval
        (Turing.TM2.step Turing.PartrecToTM2.tr) (sourceInit c) := by
  rw [source_tm2_run, Part.map_eq_map]
  exact Part.mem_map _ h

/-! ## 7. Red control -/

theorem source_tape_is_not_empty (c : Nat.Partrec.Code) : sourceTape c ≠ [] := by
  simp [sourceTape]

theorem empty_tape_initialisation_is_different (c : Nat.Partrec.Code) :
    Turing.PartrecToTM2.init universalListCode [] ≠ sourceInit c := by
  intro h
  have hs := congrArg
    (fun cfg => cfg.stk Turing.PartrecToTM2.K'.main) h
  simp [sourceInit, Turing.PartrecToTM2.init, sourceTape,
    Turing.PartrecToTM2.K'.elim] at hs

theorem turing_chamber_16AH_certificate :
    (∀ c, SourceHalts c ↔ TM2Terminates (sourceInit c)) ∧
    Computable sourceTape ∧
    (∀ c, sourceTape c ≠ []) :=
  ⟨source_halts_iff_tm2, sourceTape_computable, source_tape_is_not_empty⟩

#print axioms universalVectorEval_partrec
#print axioms universalListCode_spec
#print axioms sourceTape_primrec
#print axioms source_tm2_run
#print axioms source_halts_iff_tm2
#print axioms source_answer_is_exact_target
#print axioms empty_tape_initialisation_is_different
#print axioms turing_chamber_16AH_certificate

end FoundationStoneTest16AH
