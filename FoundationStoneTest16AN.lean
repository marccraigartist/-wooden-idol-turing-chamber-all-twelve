import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# THE TURING CHAMBER — TEST 16AN: FINITE SUPPORTED CONTROL

Lean 4.35.0-rc2 / pinned Mathlib.

Mathlib's `PartrecToTM2.Λ'` is an infinite ambient label type, but for every
fixed list-code `c`, `PartrecToTM2.tr_supports` supplies the finite closed set
`codeSupp c Cont'.halt`.  We replace the ambient labels by membership in that
finite support and fold the finite local store `Option Γ'` into the control.

No labels are enumerated by hand.  `Fintype.equivFin` supplies a canonical
finite address space, and Lean proves that encoding and decoding are inverse.
-/

namespace FoundationStoneTest16AN

open Turing
open Turing.PartrecToTM2
open Turing.ToPartrec

/-- The exact support of the fixed evaluator code, at the halting continuation. -/
def support (c : Code) : Finset Λ' := codeSupp c Cont'.halt

/-- A label together with proof that it belongs to the closed support. -/
abbrev SupportedLabel (c : Code) := {q : Λ' // q ∈ support c}

noncomputable instance supportedLabelFintype (c : Code) :
    Fintype (SupportedLabel c) := Fintype.ofFinite _

/-- The TM2 local store is finite and can be folded into finite control. -/
abbrev SupportedControl (c : Code) := SupportedLabel c × Option Γ'

noncomputable instance supportedControlFintype (c : Code) :
    Fintype (SupportedControl c) := Fintype.ofFinite _

/-- No hand allocation: Mathlib enumerates the finite supported controls. -/
noncomputable def controlEquivFin (c : Code) :
    SupportedControl c ≃ Fin (Fintype.card (SupportedControl c)) :=
  Fintype.equivFin _

noncomputable def controlCode (c : Code) (x : SupportedControl c) : Nat :=
  (controlEquivFin c x).val

noncomputable def decodeControl (c : Code)
    (n : Fin (Fintype.card (SupportedControl c))) : SupportedControl c :=
  (controlEquivFin c).symm n

theorem decode_encode (c : Code) (x : SupportedControl c) :
    decodeControl c (controlEquivFin c x) = x := by
  simp [decodeControl]

theorem encode_decode (c : Code)
    (n : Fin (Fintype.card (SupportedControl c))) :
    controlEquivFin c (decodeControl c n) = n := by
  simp [decodeControl]

theorem controlCode_injective (c : Code) : Function.Injective (controlCode c) := by
  intro x y h
  apply (controlEquivFin c).injective
  exact Fin.ext h

/-- The initial evaluator label is in the support, obtained from Mathlib's
support theorem rather than inserted manually. -/
def initialSupportedLabel (c : Code) : SupportedLabel c :=
  ⟨trNormal c Cont'.halt,
    (tr_supports c Cont'.halt).1⟩

theorem initial_label_value (c : Code) :
    (initialSupportedLabel c).val = trNormal c Cont'.halt := rfl

/-- Every supported label's complete TM2 statement can jump only inside the
same finite support.  This is the closure certificate needed by restriction. -/
theorem supported_statement_closed (c : Code) (q : SupportedLabel c) :
    Turing.TM2.SupportsStmt (support c) (tr q.val) := by
  have h := (tr_supports c Cont'.halt).2
  exact h q.val q.property

/-- Folding the finite local store into the label loses no distinction. -/
def foldControl (c : Code) (q : SupportedLabel c) (s : Option Γ') :
    SupportedControl c := (q, s)

theorem foldControl_injective (c : Code) :
    Function.Injective (fun p : SupportedLabel c × Option Γ' =>
      foldControl c p.1 p.2) := by
  intro x y h
  exact h

theorem finite_control_nonempty (c : Code) : Nonempty (SupportedControl c) :=
  ⟨(initialSupportedLabel c, none)⟩

/-! ## Red control: forgetting the local store collapses controls. -/

def forgetStore {c : Code} (x : SupportedControl c) : SupportedLabel c := x.1

theorem forgetting_store_not_injective (c : Code) :
    ¬ Function.Injective (@forgetStore c) := by
  intro h
  let q := initialSupportedLabel c
  let g0 : Option Γ' := none
  let g1 : Option Γ' := some Γ'.cons
  have he : forgetStore (q, g0) = forgetStore (q, g1) := rfl
  have hp := h he
  have hs := congrArg Prod.snd hp
  simp [g0, g1] at hs

theorem turing_chamber_16AN_certificate (c : Code) :
    Turing.TM2.SupportsStmt (support c) (tr (initialSupportedLabel c).val) ∧
    Function.Injective (controlCode c) ∧
    Nonempty (SupportedControl c) ∧
    ¬ Function.Injective (@forgetStore c) :=
  ⟨supported_statement_closed c (initialSupportedLabel c),
   controlCode_injective c, finite_control_nonempty c,
   forgetting_store_not_injective c⟩

#print axioms supported_statement_closed
#print axioms controlCode_injective
#print axioms forgetting_store_not_injective
#print axioms turing_chamber_16AN_certificate

end FoundationStoneTest16AN
