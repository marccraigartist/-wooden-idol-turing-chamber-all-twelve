import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# THE FOUR-STACK REGISTER FILE — FOUNDATION STONE TEST 16Y

Test 16X made one unbounded base-five stack run as a finite two-counter relay.
The next question is whether the complete four-stack data plane can be given an
exact numerical frame before its global two-counter multiplexing macro is built.

This file uses Mathlib's actual four-stack alphabet and stack names.  Lean
certifies:

1. every stack has an injective base-five code with exact arithmetic push/pop;
2. a four-stack bank is packed collision-free into one natural number;
3. selecting and updating any one of `main`, `rev`, `aux`, `stack` preserves the
   other three exactly;
4. symbolic push/pop and their four-code arithmetic compilation commute;
5. a finite control label, local store and complete stack bank form one
   collision-free numerical configuration frame;
6. RED CONTROL: the naive attempt to leave an unbounded inactive bank in 16X's
   scratch counter is not injective -- distinct active/bank splits merge.

The red control matters.  16X is a genuine one-stack operational compiler, but
it cannot simply be repeated four times while the other stacks sit untouched in
the second counter.  Test 16Y therefore closes the full CONFIGURATION CODING and
selected-update semantics, while leaving one exact operational obligation:
implement this collision-free global bank code with finite INC/JZDEC
multiplexing macros.
-/

namespace FoundationStoneTest16Y

abbrev Sym := Turing.PartrecToTM2.Γ'
abbrev StackName := Turing.PartrecToTM2.K'

/-! ## 1. Exact base-five stack arithmetic -/

def digit : Sym → Nat
  | .consₗ => 1
  | .cons => 2
  | .bit0 => 3
  | .bit1 => 4

def symbolOf : Nat → Sym
  | 0 => .consₗ
  | 1 => .cons
  | 2 => .bit0
  | _ => .bit1

theorem digit_bounds (s : Sym) : 0 < digit s ∧ digit s < 5 := by
  cases s <;> decide

def encodeStack : List Sym → Nat
  | [] => 0
  | s :: rest => digit s + 5 * encodeStack rest

def pushCode (s : Sym) (n : Nat) : Nat := digit s + 5 * n

def popCode (n : Nat) : Option (Sym × Nat) :=
  if n = 0 then none
  else some (symbolOf ((n - 1) % 5), (n - 1) / 5)

theorem pushCode_ne_zero (s : Sym) (n : Nat) : pushCode s n ≠ 0 := by
  have h := (digit_bounds s).1
  unfold pushCode
  omega

theorem pop_push (s : Sym) (n : Nat) : popCode (pushCode s n) = some (s, n) := by
  cases s <;> simp [popCode, pushCode, digit, symbolOf, Nat.add_mod, Nat.add_div]

theorem pop_encode_cons (s : Sym) (xs : List Sym) :
    popCode (encodeStack (s :: xs)) = some (s, encodeStack xs) := by
  change popCode (pushCode s (encodeStack xs)) = _
  exact pop_push s (encodeStack xs)

theorem encode_nonempty_ne_zero (s : Sym) (xs : List Sym) :
    encodeStack (s :: xs) ≠ 0 := pushCode_ne_zero s (encodeStack xs)

theorem encodeStack_injective : Function.Injective encodeStack := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons s rest => exact False.elim (encode_nonempty_ne_zero s rest h.symm)
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

/-! ## 2. The actual four-stack bank -/

structure Bank where
  main : List Sym
  rev : List Sym
  aux : List Sym
  stack : List Sym
deriving DecidableEq

def read (b : Bank) : StackName → List Sym
  | .main => b.main
  | .rev => b.rev
  | .aux => b.aux
  | .stack => b.stack

def write (b : Bank) : StackName → List Sym → Bank
  | .main, xs => { b with main := xs }
  | .rev, xs => { b with rev := xs }
  | .aux, xs => { b with aux := xs }
  | .stack, xs => { b with stack := xs }

theorem read_write_same (b : Bank) (k : StackName) (xs : List Sym) :
    read (write b k xs) k = xs := by cases k <;> rfl

theorem read_write_other (b : Bank) (k j : StackName) (xs : List Sym)
    (h : j ≠ k) : read (write b k xs) j = read b j := by
  cases k <;> cases j <;> simp_all [read, write]

def bankCodes (b : Bank) : Nat × Nat × Nat × Nat :=
  (encodeStack b.main, encodeStack b.rev,
    encodeStack b.aux, encodeStack b.stack)

def packBank (b : Bank) : Nat :=
  Nat.pair (encodeStack b.main)
    (Nat.pair (encodeStack b.rev)
      (Nat.pair (encodeStack b.aux) (encodeStack b.stack)))

def unpackBankCodes (n : Nat) : Nat × Nat × Nat × Nat :=
  let p0 := Nat.unpair n
  let p1 := Nat.unpair p0.2
  let p2 := Nat.unpair p1.2
  (p0.1, p1.1, p2.1, p2.2)

theorem unpack_pack_bank (b : Bank) :
    unpackBankCodes (packBank b) = bankCodes b := by
  simp [unpackBankCodes, packBank, bankCodes, Nat.unpair_pair]

theorem packBank_injective : Function.Injective packBank := by
  intro x y h
  have hc := congrArg unpackBankCodes h
  rw [unpack_pack_bank, unpack_pack_bank] at hc
  have hmain := congrArg (fun q => q.1) hc
  have hrev := congrArg (fun q => q.2.1) hc
  have haux := congrArg (fun q => q.2.2.1) hc
  have hstack := congrArg (fun q => q.2.2.2) hc
  cases x
  cases y
  simp only [Bank.mk.injEq] at *
  exact ⟨encodeStack_injective hmain, encodeStack_injective hrev,
    encodeStack_injective haux, encodeStack_injective hstack⟩

/-! ## 3. Selected symbolic updates -/

def pushAt (b : Bank) (k : StackName) (s : Sym) : Bank :=
  write b k (s :: read b k)

def popAt (b : Bank) (k : StackName) : Option (Sym × Bank) :=
  match read b k with
  | [] => none
  | s :: rest => some (s, write b k rest)

theorem push_reads_back (b : Bank) (k : StackName) (s : Sym) :
    read (pushAt b k s) k = s :: read b k := by
  exact read_write_same b k _

theorem push_preserves_other_stacks (b : Bank) (k j : StackName) (s : Sym)
    (h : j ≠ k) : read (pushAt b k s) j = read b j := by
  exact read_write_other b k j _ h

theorem pop_after_push (b : Bank) (k : StackName) (s : Sym) :
    popAt (pushAt b k s) k = some (s, b) := by
  cases k <;> simp [popAt, pushAt, read, write]

/-! ## 4. Arithmetic register-file semantics -/

abbrev Codes := Nat × Nat × Nat × Nat

def codeRead (c : Codes) : StackName → Nat
  | .main => c.1
  | .rev => c.2.1
  | .aux => c.2.2.1
  | .stack => c.2.2.2

def codeWrite (c : Codes) : StackName → Nat → Codes
  | .main, n => (n, c.2)
  | .rev, n => (c.1, n, c.2.2)
  | .aux, n => (c.1, c.2.1, n, c.2.2.2)
  | .stack, n => (c.1, c.2.1, c.2.2.1, n)

def codePush (c : Codes) (k : StackName) (s : Sym) : Codes :=
  codeWrite c k (pushCode s (codeRead c k))

def codePop (c : Codes) (k : StackName) : Option (Sym × Codes) :=
  match popCode (codeRead c k) with
  | none => none
  | some (s, rest) => some (s, codeWrite c k rest)

theorem bankCodes_read (b : Bank) (k : StackName) :
    codeRead (bankCodes b) k = encodeStack (read b k) := by cases k <;> rfl

theorem bankCodes_write (b : Bank) (k : StackName) (xs : List Sym) :
    bankCodes (write b k xs) = codeWrite (bankCodes b) k (encodeStack xs) := by
  cases k <;> rfl

/-- Selected PUSH commutes with compilation of the whole register file. -/
theorem selected_push_compiles (b : Bank) (k : StackName) (s : Sym) :
    bankCodes (pushAt b k s) = codePush (bankCodes b) k s := by
  unfold pushAt codePush
  rw [bankCodes_write, bankCodes_read]
  rfl

/-- Selected POP commutes with compilation, including empty-stack failure. -/
theorem selected_pop_compiles (b : Bank) (k : StackName) :
    (popAt b k).map (fun r => (r.1, bankCodes r.2)) =
      codePop (bankCodes b) k := by
  unfold popAt codePop
  rw [bankCodes_read]
  cases h : read b k with
  | nil => rfl
  | cons s rest =>
      rw [pop_encode_cons]
      simp only [Option.map_some]
      rw [bankCodes_write]

/-! ## 5. Finite control and local store join the bank -/

def storeCode : Option Sym → Nat
  | none => 0
  | some s => digit s

theorem storeCode_injective : Function.Injective storeCode := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some s => cases s <;> contradiction
  | some s =>
      cases y with
      | none => cases s <;> contradiction
      | some t => cases s <;> cases t <;> simp_all [storeCode, digit]

structure Frame (K : Nat) where
  label : Fin K
  store : Option Sym
  bank : Bank
deriving DecidableEq

def encodeFrame {K : Nat} (f : Frame K) : Nat :=
  Nat.pair f.label.val (Nat.pair (storeCode f.store) (packBank f.bank))

def frameParts (n : Nat) : Nat × Nat × Nat :=
  let p := Nat.unpair n
  let q := Nat.unpair p.2
  (p.1, q.1, q.2)

theorem frameParts_encode {K : Nat} (f : Frame K) :
    frameParts (encodeFrame f) = (f.label.val, storeCode f.store, packBank f.bank) := by
  simp [frameParts, encodeFrame, Nat.unpair_pair]

/-- A finite control label, local store and all four stacks have no collisions. -/
theorem encodeFrame_injective {K : Nat} : Function.Injective (@encodeFrame K) := by
  intro x y h
  have hp := congrArg frameParts h
  rw [frameParts_encode, frameParts_encode] at hp
  have hl : x.label.val = y.label.val := congrArg (fun q => q.1) hp
  have hs : storeCode x.store = storeCode y.store := congrArg (fun q => q.2.1) hp
  have hb : packBank x.bank = packBank y.bank := congrArg (fun q => q.2.2) hp
  cases x
  cases y
  simp only [Frame.mk.injEq]
  exact ⟨Fin.ext hl, storeCode_injective hs, packBank_injective hb⟩

/-! ## 6. Red control: scratch is not an inactive bank -/

/-- What the 16X push loop would leave if the destination already contained
an unrelated bank payload. -/
def naiveMergedPush (s : Sym) (active inactive : Nat) : Nat :=
  inactive + pushCode s active

/-- Distinct active/bank splits collide under naive addition. -/
theorem naive_scratch_collision :
    (1, 0) ≠ (0, 5) ∧
    naiveMergedPush .consₗ 1 0 = naiveMergedPush .consₗ 0 5 := by decide

theorem naive_scratch_not_injective :
    ¬ Function.Injective (fun p : Nat × Nat => naiveMergedPush .consₗ p.1 p.2) := by
  intro h
  exact naive_scratch_collision.1 (h naive_scratch_collision.2)

/-! ## Certificate -/

theorem four_stack_register_certificate :
    Function.Injective packBank ∧
    (∀ b k s, popAt (pushAt b k s) k = some (s, b)) ∧
    (∀ b k j s, j ≠ k → read (pushAt b k s) j = read b j) ∧
    (∀ b k s, bankCodes (pushAt b k s) = codePush (bankCodes b) k s) ∧
    (∀ b k, (popAt b k).map (fun r => (r.1, bankCodes r.2)) =
      codePop (bankCodes b) k) ∧
    (∀ K, Function.Injective (@encodeFrame K)) ∧
    ¬ Function.Injective (fun p : Nat × Nat => naiveMergedPush .consₗ p.1 p.2) :=
  ⟨packBank_injective, pop_after_push, push_preserves_other_stacks,
   selected_push_compiles, selected_pop_compiles, fun _ => encodeFrame_injective,
   naive_scratch_not_injective⟩

#print axioms encodeStack_injective
#print axioms packBank_injective
#print axioms push_preserves_other_stacks
#print axioms selected_push_compiles
#print axioms selected_pop_compiles
#print axioms encodeFrame_injective
#print axioms naive_scratch_not_injective
#print axioms four_stack_register_certificate

end FoundationStoneTest16Y
