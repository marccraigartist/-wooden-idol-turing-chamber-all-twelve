import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AT: THE AUTHENTIC FOUR-STACK ARITHMETIC

Lean 4.35.0-rc2 / pinned Mathlib.

This file connects the base-five stack representation to the exact alphabet
and four stack indices of Mathlib's `PartrecToTM2` evaluator.  It is not an
abstract copy: the symbols are `consₗ`, `cons`, `bit0`, `bit1`, and the stacks
are `main`, `rev`, `aux`, `stack`.

Lean certifies symbol round trips, injective stack and four-stack encodings,
and exact arithmetic contracts for push, peek and pop on every one of the four
stacks.  The temporary fifth counter is zero at every source boundary.
-/

namespace FoundationStoneTest16AT

open Turing
open Turing.PartrecToTM2

abbrev Digit := Fin 4

def digit : Γ' → Digit
  | .consₗ => 0
  | .cons => 1
  | .bit0 => 2
  | .bit1 => 3

def symbol : Digit → Γ'
  | ⟨0, _⟩ => .consₗ
  | ⟨1, _⟩ => .cons
  | ⟨2, _⟩ => .bit0
  | ⟨3, _⟩ => .bit1

theorem symbol_digit (g : Γ') : symbol (digit g) = g := by
  cases g <;> rfl

theorem digit_symbol (d : Digit) : digit (symbol d) = d := by
  fin_cases d <;> rfl

def code : List Γ' → Nat
  | [] => 0
  | g :: rest => (digit g).val + 1 + 5 * code rest

def pushCode (g : Γ') (n : Nat) : Nat := (digit g).val + 1 + 5 * n
def topCode (n : Nat) : Nat := (n - 1) % 5
def popCode (n : Nat) : Nat := (n - 1) / 5

/-- Decode the top of a valid encoded stack.  The fifth residue is rejected;
it never occurs for an encoded source stack. -/
def readTop (n : Nat) : Option Γ' :=
  if hz : n = 0 then none
  else
    let r := topCode n
    if hr : r < 4 then some (symbol ⟨r, hr⟩) else none

theorem code_cons (g : Γ') (s : List Γ') :
    code (g :: s) = pushCode g (code s) := rfl

theorem code_cons_pos (g : Γ') (s : List Γ') : 0 < code (g :: s) := by
  simp [code]

theorem code_zero_iff (s : List Γ') : code s = 0 ↔ s = [] := by
  cases s with
  | nil => simp [code]
  | cons g s =>
      constructor
      · intro h
        have := code_cons_pos g s
        omega
      · intro h
        contradiction

theorem top_exact (g : Γ') (s : List Γ') :
    topCode (code (g :: s)) = (digit g).val := by
  unfold topCode code
  have hd := (digit g).isLt
  omega

theorem pop_exact (g : Γ') (s : List Γ') :
    popCode (code (g :: s)) = code s := by
  unfold popCode
  change ((digit g).val + 1 + 5 * code s - 1) / 5 = code s
  have hd := (digit g).isLt
  have hs : (digit g).val + 1 + 5 * code s - 1 =
      (digit g).val + 5 * code s := by omega
  rw [hs, Nat.add_mul_div_left _ _ (by decide)]
  rw [Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem readTop_exact (s : List Γ') : readTop (code s) = s.head? := by
  cases s with
  | nil => simp [readTop, code]
  | cons g rest =>
      have hp := code_cons_pos g rest
      have ht := top_exact g rest
      unfold readTop
      simp only [hp.ne', ↓reduceDIte]
      rw [ht]
      simp only [dif_pos (digit g).isLt, List.head?_cons, Option.some.injEq]
      exact symbol_digit g

theorem code_injective : Function.Injective code := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      exact ((code_zero_iff ys).mp (by simpa [code] using h.symm)).symm
  | cons g gs ih =>
      intro ys h
      cases ys with
      | nil =>
          have hp := code_cons_pos g gs
          simp [code] at h
      | cons d ds =>
          have hv : (digit g).val = (digit d).val := by
            have ht := congrArg topCode h
            simpa [top_exact] using ht
          have hgd : g = d := by
            have hfin : digit g = digit d := Fin.ext hv
            have hs := congrArg symbol hfin
            simpa [symbol_digit] using hs
          subst d
          have hp := congrArg popCode h
          have hrs : code gs = code ds := by simpa [pop_exact] using hp
          exact congrArg (List.cons g) (ih hrs)

structure FiveCounters where
  main : Nat
  rev : Nat
  aux : Nat
  stack : Nat
  temp : Nat
deriving DecidableEq, Repr

def encodeStacks (S : ∀ _ : K', List Γ') : FiveCounters :=
  ⟨code (S .main), code (S .rev), code (S .aux), code (S .stack), 0⟩

theorem encodeStacks_injective : Function.Injective encodeStacks := by
  intro S T h
  have hm := congrArg FiveCounters.main h
  have hr := congrArg FiveCounters.rev h
  have ha := congrArg FiveCounters.aux h
  have hs := congrArg FiveCounters.stack h
  funext k
  cases k with
  | main => exact code_injective hm
  | rev => exact code_injective hr
  | aux => exact code_injective ha
  | stack => exact code_injective hs

def get (c : FiveCounters) : K' → Nat
  | .main => c.main
  | .rev => c.rev
  | .aux => c.aux
  | .stack => c.stack

def set (c : FiveCounters) : K' → Nat → FiveCounters
  | .main, n => { c with main := n }
  | .rev, n => { c with rev := n }
  | .aux, n => { c with aux := n }
  | .stack, n => { c with stack := n }

theorem get_encode (S : ∀ _ : K', List Γ') (k : K') :
    get (encodeStacks S) k = code (S k) := by
  cases k <;> rfl

theorem get_set_same (c : FiveCounters) (k : K') (n : Nat) :
    get (set c k n) k = n := by
  cases k <;> rfl

theorem get_set_other (c : FiveCounters) (k j : K') (n : Nat) (h : j ≠ k) :
    get (set c k n) j = get c j := by
  cases k <;> cases j <;> simp_all [get, set]

def pushAt (S : ∀ _ : K', List Γ') (k : K') (g : Γ') :
    ∀ j : K', List Γ' := Function.update S k (g :: S k)

def popAt (S : ∀ _ : K', List Γ') (k : K') :
    ∀ j : K', List Γ' := Function.update S k (S k).tail

theorem push_contract (S : ∀ _ : K', List Γ') (k : K') (g : Γ') :
    encodeStacks (pushAt S k g) =
      set (encodeStacks S) k (pushCode g (get (encodeStacks S) k)) := by
  cases k <;> simp [encodeStacks, pushAt, set, get, pushCode, code]

theorem pop_contract_nonempty (S : ∀ _ : K', List Γ')
    (k : K') (g : Γ') (rest : List Γ') (h : S k = g :: rest) :
    encodeStacks (popAt S k) =
      set (encodeStacks S) k (popCode (get (encodeStacks S) k)) := by
  cases k <;>
    simp_all [encodeStacks, popAt, set, get, pop_exact]

theorem pop_contract (S : ∀ _ : K', List Γ') (k : K') :
    encodeStacks (popAt S k) =
      set (encodeStacks S) k (popCode (get (encodeStacks S) k)) := by
  cases h : S k with
  | nil =>
      cases k <;> simp_all [encodeStacks, popAt, set, get, popCode, code]
  | cons g rest => exact pop_contract_nonempty S k g rest h

theorem empty_test_exact (S : ∀ _ : K', List Γ') (k : K') :
    get (encodeStacks S) k = 0 ↔ S k = [] := by
  rw [get_encode, code_zero_iff]

theorem peek_contract (S : ∀ _ : K', List Γ') (k : K') :
    match S k with
    | [] => get (encodeStacks S) k = 0
    | g :: rest => topCode (get (encodeStacks S) k) = (digit g).val := by
  rw [get_encode]
  cases h : S k with
  | nil => simp [h, code]
  | cons g rest => simpa [h] using top_exact g rest

/-! Red control: base four without shifted digits makes the empty stack and a
leading zero symbol collide. -/

def badCode : List Γ' → Nat
  | [] => 0
  | g :: rest => (digit g).val + 4 * badCode rest

theorem unshifted_encoding_collides :
    badCode [] = badCode [.consₗ] := by decide

theorem turing_chamber_16AT_certificate :
    Function.Injective code ∧ Function.Injective encodeStacks ∧
    (∀ S k, get (encodeStacks S) k = 0 ↔ S k = []) ∧
    (∀ S k g, encodeStacks (pushAt S k g) =
      set (encodeStacks S) k (pushCode g (get (encodeStacks S) k)) ) ∧
    badCode [] = badCode [.consₗ] :=
  ⟨code_injective, encodeStacks_injective, empty_test_exact,
   push_contract, unshifted_encoding_collides⟩

#print axioms code_injective
#print axioms encodeStacks_injective
#print axioms push_contract
#print axioms pop_contract_nonempty
#print axioms pop_contract
#print axioms readTop_exact
#print axioms peek_contract
#print axioms turing_chamber_16AT_certificate

end FoundationStoneTest16AT
