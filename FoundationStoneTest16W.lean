import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# THE STACK DOOR — FOUNDATION STONE TEST 16W

Test 16V reached Mathlib's verified four-stack Turing chamber but left the
four-stack-to-two-counter bridge uninhabited.  This test builds the first
executable slice of that bridge: the unbounded stack data themselves become
natural numbers, exactly and without collision.

Mathlib's Turing alphabet has four symbols.  A stack is written in base five,
using digits 1--4 so that zero is reserved for the empty stack:

    code([])       = 0
    code(s :: xs)  = digit(s) + 5 * code(xs).

Lean certifies:

1. arithmetic push and pop are exact inverses on every encoded stack;
2. the stack encoding is injective;
3. every finite sequence of pushes and pops is simulated exactly on its code;
4. all four Turing stacks can be packed into one natural number and recovered
   as four collision-free stack codes;
5. RED CONTROL: decoding the base-five representation as base four corrupts
   a concrete two-symbol stack.

This is a genuine part of the missing compiler, but not the whole compiler.
It closes the DATA representation problem.  The next obligation is operational:
implement the base-five quotient/remainder operations as finite INC/JZDEC
macros using only two counters, and then encode the finite control labels.
-/

namespace FoundationStoneTest16W

abbrev Sym := Turing.PartrecToTM2.Γ'

/-! ## 1. A concrete base-five stack code -/

/-- The four symbols occupy digits 1,2,3,4.  Digit zero is the end marker. -/
def digit : Sym → Nat
  | .consₗ => 1
  | .cons => 2
  | .bit0 => 3
  | .bit1 => 4

/-- Decode the four valid payload digits after subtracting one. -/
def symbolOf : Nat → Sym
  | 0 => .consₗ
  | 1 => .cons
  | 2 => .bit0
  | _ => .bit1

theorem digit_bounds (s : Sym) : 0 < digit s ∧ digit s < 5 := by
  cases s <;> decide

theorem symbolOf_digit (s : Sym) : symbolOf (digit s - 1) = s := by
  cases s <;> rfl

def encodeStack : List Sym → Nat
  | [] => 0
  | s :: rest => digit s + 5 * encodeStack rest

def pushCode (s : Sym) (n : Nat) : Nat := digit s + 5 * n

/-- Pop a base-five digit.  The quotient is the remaining stack. -/
def popCode (n : Nat) : Option (Sym × Nat) :=
  if n = 0 then none
  else some (symbolOf ((n - 1) % 5), (n - 1) / 5)

theorem encode_cons (s : Sym) (rest : List Sym) :
    encodeStack (s :: rest) = pushCode s (encodeStack rest) := rfl

theorem pushCode_ne_zero (s : Sym) (n : Nat) : pushCode s n ≠ 0 := by
  have h := (digit_bounds s).1
  unfold pushCode
  omega

/-- Arithmetic pop exactly undoes arithmetic push, for every payload. -/
theorem pop_push (s : Sym) (n : Nat) : popCode (pushCode s n) = some (s, n) := by
  cases s <;> simp [popCode, pushCode, digit, symbolOf, Nat.add_mod,
    Nat.add_div]

theorem pop_encode_cons (s : Sym) (rest : List Sym) :
    popCode (encodeStack (s :: rest)) = some (s, encodeStack rest) := by
  rw [encode_cons, pop_push]

theorem encode_nonempty_ne_zero (s : Sym) (rest : List Sym) :
    encodeStack (s :: rest) ≠ 0 := by
  rw [encode_cons]
  exact pushCode_ne_zero s (encodeStack rest)

/-- No two stacks collide in the arithmetic representation. -/
theorem encodeStack_injective : Function.Injective encodeStack := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons s rest =>
          exact False.elim (encode_nonempty_ne_zero s rest h.symm)
  | cons s rest ih =>
      intro ys h
      cases ys with
      | nil => exact False.elim (encode_nonempty_ne_zero s rest h)
      | cons t tail =>
          have hp := congrArg popCode h
          rw [pop_encode_cons, pop_encode_cons] at hp
          have hpair : (s, encodeStack rest) = (t, encodeStack tail) :=
            Option.some.inj hp
          have hs : s = t := congrArg Prod.fst hpair
          have hr : encodeStack rest = encodeStack tail := congrArg Prod.snd hpair
          subst t
          rw [ih hr]

/-! ## 2. A compiler for finite stack histories -/

inductive StackAction
  | push (s : Sym)
  | pop
deriving DecidableEq

def stackStep : StackAction → List Sym → Option (List Sym)
  | .push s, xs => some (s :: xs)
  | .pop, [] => none
  | .pop, _ :: xs => some xs

def codeStep : StackAction → Nat → Option Nat
  | .push s, n => some (pushCode s n)
  | .pop, n => (popCode n).map Prod.snd

/-- One source stack action and one arithmetic action agree exactly. -/
theorem one_action_compiles (op : StackAction) (xs : List Sym) :
    (stackStep op xs).map encodeStack = codeStep op (encodeStack xs) := by
  cases op with
  | push s => rfl
  | pop =>
      cases xs with
      | nil => rfl
      | cons s rest => simp [stackStep, codeStep, pop_encode_cons]

def stackRun : List StackAction → List Sym → Option (List Sym)
  | [], xs => some xs
  | op :: ops, xs =>
      match stackStep op xs with
      | none => none
      | some ys => stackRun ops ys

def codeRun : List StackAction → Nat → Option Nat
  | [], n => some n
  | op :: ops, n =>
      match codeStep op n with
      | none => none
      | some m => codeRun ops m

/-- Every finite push/pop history commutes with encoding. -/
theorem actions_compile : ∀ ops xs,
    (stackRun ops xs).map encodeStack = codeRun ops (encodeStack xs) := by
  intro ops
  induction ops with
  | nil => intro xs; rfl
  | cons op ops ih =>
      intro xs
      unfold stackRun codeRun
      have h := one_action_compiles op xs
      cases hs : stackStep op xs with
      | none =>
          rw [hs] at h
          simp only [Option.map_none] at h
          rw [← h]
          rfl
      | some ys =>
          rw [hs] at h
          simp only [Option.map_some] at h
          rw [← h]
          exact ih ys

/-! ## 3. Four stacks become one natural-number payload -/

structure FourStacks where
  main : List Sym
  rev : List Sym
  aux : List Sym
  stack : List Sym
deriving DecidableEq

def fourCodes (s : FourStacks) : Nat × Nat × Nat × Nat :=
  (encodeStack s.main, encodeStack s.rev, encodeStack s.aux, encodeStack s.stack)

def packFour (s : FourStacks) : Nat :=
  Nat.pair (encodeStack s.main)
    (Nat.pair (encodeStack s.rev)
      (Nat.pair (encodeStack s.aux) (encodeStack s.stack)))

def unpackFourCodes (n : Nat) : Nat × Nat × Nat × Nat :=
  let p0 := Nat.unpair n
  let p1 := Nat.unpair p0.2
  let p2 := Nat.unpair p1.2
  (p0.1, p1.1, p2.1, p2.2)

theorem unpack_pack_four_codes (s : FourStacks) :
    unpackFourCodes (packFour s) = fourCodes s := by
  simp [unpackFourCodes, packFour, fourCodes, Nat.unpair_pair]

/-- Packing all four stacks is collision-free. -/
theorem packFour_injective : Function.Injective packFour := by
  intro x y h
  have hc := congrArg unpackFourCodes h
  rw [unpack_pack_four_codes, unpack_pack_four_codes] at hc
  have hmain : encodeStack x.main = encodeStack y.main :=
    congrArg (fun q => q.1) hc
  have hrev : encodeStack x.rev = encodeStack y.rev :=
    congrArg (fun q => q.2.1) hc
  have haux : encodeStack x.aux = encodeStack y.aux :=
    congrArg (fun q => q.2.2.1) hc
  have hstack : encodeStack x.stack = encodeStack y.stack :=
    congrArg (fun q => q.2.2.2) hc
  cases x
  cases y
  simp only [FourStacks.mk.injEq] at *
  exact ⟨encodeStack_injective hmain, encodeStack_injective hrev,
    encodeStack_injective haux, encodeStack_injective hstack⟩

/-! ## 4. Controls -/

def sampleStack : List Sym := [.bit1, .cons, .bit0]
def sampleActions : List StackAction := [.push .consₗ, .pop, .pop]

theorem sample_stack_code : encodeStack sampleStack = 89 := by decide

theorem sample_history_agrees :
    (stackRun sampleActions sampleStack).map encodeStack =
      codeRun sampleActions (encodeStack sampleStack) :=
  actions_compile sampleActions sampleStack

/-- Wrong on purpose: interpret the base-five code using base four. -/
def badPopCode (n : Nat) : Option (Sym × Nat) :=
  if n = 0 then none
  else some (symbolOf ((n - 1) % 4), (n - 1) / 4)

/-- RED CONTROL: the wrong radix corrupts both the recovered symbol and tail. -/
theorem wrong_radix_fails :
    badPopCode (encodeStack [.bit1, .cons]) ≠
      some (.bit1, encodeStack [.cons]) := by decide

/-! ## Certificate -/

theorem stack_door_certificate :
    (∀ s n, popCode (pushCode s n) = some (s, n)) ∧
    Function.Injective encodeStack ∧
    (∀ ops xs, (stackRun ops xs).map encodeStack =
      codeRun ops (encodeStack xs)) ∧
    Function.Injective packFour ∧
    badPopCode (encodeStack [.bit1, .cons]) ≠
      some (.bit1, encodeStack [.cons]) :=
  ⟨pop_push, encodeStack_injective, actions_compile,
   packFour_injective, wrong_radix_fails⟩

#print axioms pop_push
#print axioms encodeStack_injective
#print axioms one_action_compiles
#print axioms actions_compile
#print axioms unpack_pack_four_codes
#print axioms packFour_injective
#print axioms wrong_radix_fails
#print axioms stack_door_certificate

end FoundationStoneTest16W
