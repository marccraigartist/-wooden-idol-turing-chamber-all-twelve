import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AK-GENERAL: THE BASE-k STACK CONTRACT

Lean 4.35.0-rc2 / Mathlib.

This file generalises the arithmetic contract beneath 16AK's literal base-five
MM2 program.  For an alphabet `Fin k`, a symbol is stored as the nonzero digit
`d+1` in base `k+1`; zero is reserved as the end marker.

It proves, uniformly in every positive finite alphabet:

* zero is exactly the empty stack;
* push, top and pop have the advertised arithmetic formulas;
* the encoding is injective;
* the unshifted alternative collides with the empty stack.

Scope: this is the generic DATA contract.  16AK remains the authenticated
literal MM2 lowering for the concrete `k=4`, base-five alphabet used by
`PartrecToTM2`.  This file does not pretend that a symbolic-size instruction
list has already been lowered for every runtime `k`.
-/

namespace FoundationStoneTest16AKGeneral

def base (k : Nat) : Nat := k + 1

def stackCode (k : Nat) : List (Fin k) → Nat
  | [] => 0
  | d :: rest => (d.val + 1) + base k * stackCode k rest

def pushCode (k : Nat) (d : Fin k) (n : Nat) : Nat :=
  d.val + 1 + base k * n

def topCode (k n : Nat) : Nat := (n - 1) % base k
def popCode (k n : Nat) : Nat := (n - 1) / base k

theorem base_pos (k : Nat) : 0 < base k := by simp [base]

theorem stackCode_cons_pos {k : Nat} (d : Fin k) (s : List (Fin k)) :
    0 < stackCode k (d :: s) := by
  simp only [stackCode]
  omega

theorem stackCode_eq_zero_iff {k : Nat} (s : List (Fin k)) :
    stackCode k s = 0 ↔ s = [] := by
  cases s with
  | nil => simp [stackCode]
  | cons d rest =>
      constructor
      · intro h
        have hp := stackCode_cons_pos d rest
        omega
      · intro h
        contradiction

theorem push_correct {k : Nat} (d : Fin k) (s : List (Fin k)) :
    pushCode k d (stackCode k s) = stackCode k (d :: s) := rfl

theorem predecessor_formula {k : Nat} (d : Fin k) (s : List (Fin k)) :
    stackCode k (d :: s) - 1 = d.val + base k * stackCode k s := by
  simp only [stackCode, base]
  omega

theorem top_correct {k : Nat} (d : Fin k) (s : List (Fin k)) :
    topCode k (stackCode k (d :: s)) = d.val := by
  rw [topCode, predecessor_formula]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by simpa [base] using d.isLt)

theorem pop_correct {k : Nat} (d : Fin k) (s : List (Fin k)) :
    popCode k (stackCode k (d :: s)) = stackCode k s := by
  rw [popCode, predecessor_formula]
  rw [Nat.add_mul_div_left _ _ (base_pos k)]
  rw [Nat.div_eq_of_lt (by simpa [base] using d.isLt), Nat.zero_add]

theorem stackCode_injective {k : Nat} : Function.Injective (stackCode k) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      exact ((stackCode_eq_zero_iff ys).mp (by simpa [stackCode] using h.symm)).symm
  | cons d ds ih =>
      intro ys h
      cases ys with
      | nil =>
          have hp := stackCode_cons_pos d ds
          simp [stackCode] at h
      | cons e es =>
          have hv : d.val = e.val := by
            have ht := congrArg (topCode k) h
            simpa [top_correct] using ht
          have hde : d = e := Fin.ext hv
          subst e
          have hp := congrArg (popCode k) h
          have hrs : stackCode k ds = stackCode k es := by
            simpa [pop_correct] using hp
          exact congrArg (List.cons d) (ih hrs)

/-! ## The concrete source alphabet -/

abbrev SourceDigit := Fin 4

theorem source_base_is_five : base 4 = 5 := rfl

theorem source_contract (d : SourceDigit) (s : List SourceDigit) :
    topCode 4 (stackCode 4 (d :: s)) = d.val ∧
    popCode 4 (stackCode 4 (d :: s)) = stackCode 4 s ∧
    pushCode 4 d (stackCode 4 s) = stackCode 4 (d :: s) :=
  ⟨top_correct d s, pop_correct d s, push_correct d s⟩

/-! ## Red control: without the shift, zero is both a symbol and the terminator. -/

def badCode (k : Nat) : List (Fin k) → Nat
  | [] => 0
  | d :: rest => d.val + base k * badCode k rest

def zero4 : Fin 4 := ⟨0, by decide⟩

theorem unshifted_collides : badCode 4 [] = badCode 4 [zero4] := by decide

theorem unshifted_not_injective : ¬ Function.Injective (badCode 4) := by
  intro h
  have he := h unshifted_collides
  simp at he

theorem turing_chamber_16AK_general_certificate :
    (∀ k, Function.Injective (stackCode k)) ∧
    (∀ k (d : Fin k) s, topCode k (stackCode k (d :: s)) = d.val) ∧
    (∀ k (d : Fin k) s, popCode k (stackCode k (d :: s)) = stackCode k s) ∧
    (∀ k (d : Fin k) s,
      pushCode k d (stackCode k s) = stackCode k (d :: s)) ∧
    ¬ Function.Injective (badCode 4) :=
  ⟨fun _ => stackCode_injective,
   fun _ d s => top_correct d s,
   fun _ d s => pop_correct d s,
   fun _ d s => push_correct d s,
   unshifted_not_injective⟩

#print axioms stackCode_injective
#print axioms source_contract
#print axioms unshifted_not_injective
#print axioms turing_chamber_16AK_general_certificate

end FoundationStoneTest16AKGeneral
