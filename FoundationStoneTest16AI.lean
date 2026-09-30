import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AI: A STACK INSIDE ONE NUMBER

Lean 4.35.0-rc2 / Mathlib.

The Mathlib TM2 interpreter used in 16AH has a four-symbol alphabet.  This file
encodes a finite stack of four-valued symbols as one natural number.

We use base five, reserving digit zero as the end marker:

    []        ↦ 0
    d :: rest ↦ (d + 1) + 5 · code(rest)

Thus the four actual symbols occupy digits 1,2,3,4.  Lean certifies:

1. zero encodes exactly the empty stack;
2. `pushCode` exactly encodes list cons;
3. subtract-one/mod-five reads the top digit;
4. subtract-one/div-five pops the stack;
5. the encoding is injective;
6. the arithmetic push, pop and empty tests are primitive recursive;
7. red control: allowing symbol zero as an unshifted digit collapses `[]`
   and `[0]`, demonstrating why the reserved end marker is necessary.
-/

namespace FoundationStoneTest16AI

abbrev Digit := Fin 4

/-- Base-five stack representation, with zero reserved for the end marker. -/
def stackCode : List Digit → Nat
  | [] => 0
  | d :: rest => (d.val + 1) + 5 * stackCode rest

/-- Arithmetic push on an already encoded stack. -/
def pushCode (d : Digit) (n : Nat) : Nat := (d.val + 1) + 5 * n

/-- Read the shifted top digit.  It is in `0..3` on valid nonempty codes. -/
def topCode (n : Nat) : Nat := (n - 1) % 5

/-- Remove the top digit. -/
def popCode (n : Nat) : Nat := (n - 1) / 5

/-- Arithmetic empty-stack test. -/
def emptyCode (n : Nat) : Bool := n == 0

theorem stackCode_cons (d : Digit) (rest : List Digit) :
    stackCode (d :: rest) = pushCode d (stackCode rest) := rfl

theorem stackCode_cons_pos (d : Digit) (rest : List Digit) :
    0 < stackCode (d :: rest) := by
  unfold stackCode
  omega

/-- 1. Zero is an unambiguous end marker. -/
theorem stackCode_eq_zero_iff (s : List Digit) :
    stackCode s = 0 ↔ s = [] := by
  cases s with
  | nil => simp [stackCode]
  | cons d rest =>
      constructor
      · intro h
        have := stackCode_cons_pos d rest
        omega
      · intro h
        contradiction

/-- 2. Pushing in arithmetic is exactly list cons. -/
theorem push_correct (d : Digit) (s : List Digit) :
    pushCode d (stackCode s) = stackCode (d :: s) := rfl

/-- 3. The top operation recovers the original symbol value. -/
theorem top_correct (d : Digit) (s : List Digit) :
    topCode (stackCode (d :: s)) = d.val := by
  unfold topCode stackCode
  have hd : d.val < 4 := d.isLt
  omega

/-- 4. The pop operation recovers the rest of the encoded stack. -/
theorem pop_correct (d : Digit) (s : List Digit) :
    popCode (stackCode (d :: s)) = stackCode s := by
  unfold popCode
  rw [stackCode_cons]
  unfold pushCode
  have hd : d.val < 4 := d.isLt
  have hsub : d.val + 1 + 5 * stackCode s - 1 =
      d.val + 5 * stackCode s := by omega
  rw [hsub, Nat.add_mul_div_left _ _ (by decide)]
  have : d.val / 5 = 0 := Nat.div_eq_of_lt (by omega)
  rw [this, Nat.zero_add]

theorem empty_correct (s : List Digit) :
    emptyCode (stackCode s) = true ↔ s = [] := by
  simp [emptyCode, stackCode_eq_zero_iff]

/-- 5. The reserved end marker makes the representation injective. -/
theorem stackCode_injective : Function.Injective stackCode := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      have hy : stackCode ys = 0 := by simpa [stackCode] using h.symm
      exact ((stackCode_eq_zero_iff ys).mp hy).symm
  | cons d ds ih =>
      intro ys h
      cases ys with
      | nil =>
          have hp := stackCode_cons_pos d ds
          simp [stackCode] at h
      | cons e es =>
          have ht : d.val = e.val := by
            have := congrArg topCode h
            simpa [top_correct] using this
          have hd : d = e := Fin.ext ht
          subst e
          have hp : stackCode ds = stackCode es := by
            have := congrArg popCode h
            simpa [pop_correct] using this
          exact congrArg (List.cons d) (ih hp)

/-! ## 6. Effectivity of the arithmetic interface -/

theorem pushCode_primrec : Primrec₂ pushCode := by
  unfold pushCode
  exact (Primrec.nat_add.comp
    (Primrec.succ.comp (Primrec.fin_val.comp Primrec.fst))
    (Primrec.nat_mul.comp (Primrec.const 5) Primrec.snd)).to₂

theorem topCode_primrec : Primrec topCode := by
  unfold topCode
  exact Primrec.nat_mod.comp
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
    (Primrec.const 5)

theorem popCode_primrec : Primrec popCode := by
  unfold popCode
  exact Primrec.nat_div.comp
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
    (Primrec.const 5)

theorem emptyCode_primrec : Primrec emptyCode := by
  unfold emptyCode
  exact Primrec.beq.comp Primrec.id (Primrec.const 0)

/-! ## 7. Red control -/

/-- The tempting unshifted code has a leading-zero collision. -/
def badCode : List Digit → Nat
  | [] => 0
  | d :: rest => d.val + 4 * badCode rest

theorem unshifted_code_collapses :
    badCode [] = badCode [⟨0, by decide⟩] := by decide

theorem unshifted_code_not_injective : ¬ Function.Injective badCode := by
  intro h
  have := h unshifted_code_collapses
  simp at this

theorem turing_chamber_16AI_certificate :
    Function.Injective stackCode ∧
    (∀ d s, topCode (stackCode (d :: s)) = d.val) ∧
    (∀ d s, popCode (stackCode (d :: s)) = stackCode s) ∧
    Primrec₂ pushCode ∧ Primrec popCode ∧ Primrec emptyCode ∧
    ¬ Function.Injective badCode :=
  ⟨stackCode_injective, top_correct, pop_correct, pushCode_primrec,
   popCode_primrec, emptyCode_primrec, unshifted_code_not_injective⟩

#print axioms stackCode_eq_zero_iff
#print axioms top_correct
#print axioms pop_correct
#print axioms stackCode_injective
#print axioms pushCode_primrec
#print axioms popCode_primrec
#print axioms emptyCode_primrec
#print axioms unshifted_code_not_injective
#print axioms turing_chamber_16AI_certificate

end FoundationStoneTest16AI
