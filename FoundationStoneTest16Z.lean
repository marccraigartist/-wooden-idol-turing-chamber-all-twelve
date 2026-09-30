import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# THE GLOBAL MULTIPLEXER — FOUNDATION STONE TEST 16Z

Test 16X supplied exact two-counter PUSH/POP for one base-five stack.  Test 16Y
gave Mathlib's four stacks, local store and finite control a collision-free
configuration code, and proved that a naive scratch-bank merge collides.

This test constructs the correct arithmetic multiplexer.  The four stack codes
are nested with `Nat.pair`, whose `Nat.unpair` is an exact inverse.  A selected
stack is isolated, changed by the same base-five law used by 16X, and returned
to its original slot before the bank is repacked.

Lean certifies:

1. packing and unpacking the four-code bank are mutual inverses;
2. multiplexed PUSH changes exactly the selected stack;
3. multiplexed POP returns exactly its top symbol and residual stack;
4. POP after PUSH restores the entire packed four-stack bank;
5. a complete numerical frame preserves control and local store while its bank
   is updated, and the frame packer is bijective;
6. RED CONTROL: a corrupted selector updates the wrong stack and is detected;
7. RED CONTROL: erasing the control coordinate causes a concrete collision.

This is an executable arithmetic multiplexer, not yet an `INC/JZDEC` listing.
The remaining data-plane obligation is now sharply isolated: compile
`Nat.unpair`, `Nat.pair`, and the finite selector cases into two-counter macros,
then compose those macros with 16X's already-verified radix relay.
-/

namespace FoundationStoneTest16Z

abbrev Sym := Turing.PartrecToTM2.Γ'
abbrev Slot := Turing.PartrecToTM2.K'

/-! ## 1. The same radix law as 16W/16X -/

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

def pushCode (s : Sym) (n : Nat) : Nat := digit s + 5 * n

def popCode (n : Nat) : Option (Sym × Nat) :=
  if n = 0 then none
  else some (symbolOf ((n - 1) % 5), (n - 1) / 5)

theorem pop_push (s : Sym) (n : Nat) : popCode (pushCode s n) = some (s, n) := by
  cases s <;> simp [popCode, pushCode, digit, symbolOf, Nat.add_mod, Nat.add_div]

/-! ## 2. A bijective numerical bank -/

structure Codes where
  main : Nat
  rev : Nat
  aux : Nat
  stack : Nat
deriving DecidableEq, Repr

def bankRead (c : Codes) : Slot → Nat
  | .main => c.main
  | .rev => c.rev
  | .aux => c.aux
  | .stack => c.stack

def bankWrite (c : Codes) : Slot → Nat → Codes
  | .main, n => { c with main := n }
  | .rev, n => { c with rev := n }
  | .aux, n => { c with aux := n }
  | .stack, n => { c with stack := n }

theorem bankRead_write_same (c : Codes) (k : Slot) (n : Nat) :
    bankRead (bankWrite c k n) k = n := by cases k <;> rfl

theorem bankRead_write_other (c : Codes) (k j : Slot) (n : Nat) (h : j ≠ k) :
    bankRead (bankWrite c k n) j = bankRead c j := by
  cases k <;> cases j <;> simp_all [bankRead, bankWrite]

def packBank (c : Codes) : Nat :=
  Nat.pair c.main (Nat.pair c.rev (Nat.pair c.aux c.stack))

def unpackBank (n : Nat) : Codes :=
  let p0 := Nat.unpair n
  let p1 := Nat.unpair p0.2
  let p2 := Nat.unpair p1.2
  ⟨p0.1, p1.1, p2.1, p2.2⟩

theorem unpack_pack_bank (c : Codes) : unpackBank (packBank c) = c := by
  rcases c with ⟨a, b, d, e⟩
  simp [unpackBank, packBank, Nat.unpair_pair]

theorem pack_unpack_bank (n : Nat) : packBank (unpackBank n) = n := by
  unfold unpackBank packBank
  simp only
  rw [Nat.pair_unpair, Nat.pair_unpair, Nat.pair_unpair]

theorem packBank_bijective : Function.Bijective packBank := by
  constructor
  · intro x y h
    have := congrArg unpackBank h
    simpa [unpack_pack_bank] using this
  · intro n
    exact ⟨unpackBank n, pack_unpack_bank n⟩

/-! ## 3. Select, operate, return -/

def muxPush (packed : Nat) (k : Slot) (s : Sym) : Nat :=
  let bank := unpackBank packed
  packBank (bankWrite bank k (pushCode s (bankRead bank k)))

def muxPop (packed : Nat) (k : Slot) : Option (Sym × Nat) :=
  let bank := unpackBank packed
  match popCode (bankRead bank k) with
  | none => none
  | some (s, rest) => some (s, packBank (bankWrite bank k rest))

theorem unpack_muxPush (packed : Nat) (k : Slot) (s : Sym) :
    unpackBank (muxPush packed k s) =
      bankWrite (unpackBank packed) k
        (pushCode s (bankRead (unpackBank packed) k)) := by
  simp [muxPush, unpack_pack_bank]

/-- The selected stack receives exactly the 16X radix PUSH. -/
theorem muxPush_selected (packed : Nat) (k : Slot) (s : Sym) :
    bankRead (unpackBank (muxPush packed k s)) k =
      pushCode s (bankRead (unpackBank packed) k) := by
  rw [unpack_muxPush, bankRead_write_same]

/-- Every non-selected stack is unchanged. -/
theorem muxPush_preserves_other (packed : Nat) (k j : Slot) (s : Sym)
    (h : j ≠ k) :
    bankRead (unpackBank (muxPush packed k s)) j =
      bankRead (unpackBank packed) j := by
  rw [unpack_muxPush, bankRead_write_other _ _ _ _ h]

/-- A selected pop after a selected push recovers the symbol and the ENTIRE bank. -/
theorem muxPop_after_muxPush (packed : Nat) (k : Slot) (s : Sym) :
    muxPop (muxPush packed k s) k = some (s, packed) := by
  unfold muxPop muxPush
  simp only [unpack_pack_bank]
  rw [bankRead_write_same, pop_push]
  simp only
  rw [show bankWrite
      (bankWrite (unpackBank packed) k
        (pushCode s (bankRead (unpackBank packed) k)))
      k (bankRead (unpackBank packed) k) = unpackBank packed by
        cases k <;> rfl]
  rw [pack_unpack_bank]

/-- Empty selected stacks take the empty branch, regardless of the other three. -/
theorem muxPop_empty_selected (c : Codes) (k : Slot)
    (h : bankRead c k = 0) : muxPop (packBank c) k = none := by
  unfold muxPop
  simp only [unpack_pack_bank]
  rw [h]
  rfl

/-! ## 4. Control and local store remain outside the selected data update -/

structure NumericFrame where
  control : Nat
  store : Nat
  bank : Nat
deriving DecidableEq, Repr

def packFrame (f : NumericFrame) : Nat :=
  Nat.pair f.control (Nat.pair f.store f.bank)

def unpackFrame (n : Nat) : NumericFrame :=
  let p := Nat.unpair n
  let q := Nat.unpair p.2
  ⟨p.1, q.1, q.2⟩

theorem unpack_pack_frame (f : NumericFrame) : unpackFrame (packFrame f) = f := by
  rcases f with ⟨control, store, bank⟩
  simp [unpackFrame, packFrame, Nat.unpair_pair]

theorem pack_unpack_frame (n : Nat) : packFrame (unpackFrame n) = n := by
  unfold unpackFrame packFrame
  simp only
  rw [Nat.pair_unpair, Nat.pair_unpair]

theorem packFrame_bijective : Function.Bijective packFrame := by
  constructor
  · intro x y h
    have := congrArg unpackFrame h
    simpa [unpack_pack_frame] using this
  · intro n
    exact ⟨unpackFrame n, pack_unpack_frame n⟩

def frameMuxPush (encoded : Nat) (k : Slot) (s : Sym) : Nat :=
  let f := unpackFrame encoded
  packFrame { f with bank := muxPush f.bank k s }

theorem frameMuxPush_exact (f : NumericFrame) (k : Slot) (s : Sym) :
    unpackFrame (frameMuxPush (packFrame f) k s) =
      { f with bank := muxPush f.bank k s } := by
  simp [frameMuxPush, unpack_pack_frame]

theorem frameMuxPush_keeps_control (f : NumericFrame) (k : Slot) (s : Sym) :
    (unpackFrame (frameMuxPush (packFrame f) k s)).control = f.control := by
  rw [frameMuxPush_exact]

theorem frameMuxPush_keeps_store (f : NumericFrame) (k : Slot) (s : Sym) :
    (unpackFrame (frameMuxPush (packFrame f) k s)).store = f.store := by
  rw [frameMuxPush_exact]

/-! ## 5. Red controls -/

/-- Wrong on purpose: requests for `aux` are silently redirected to `rev`. -/
def badSelect : Slot → Slot
  | .aux => .rev
  | k => k

def badMuxPush (packed : Nat) (k : Slot) (s : Sym) : Nat :=
  muxPush packed (badSelect k) s

def emptyBank : Codes := ⟨0, 0, 0, 0⟩

/-- RED CONTROL: the corrupted selector changes the wrong coordinate. -/
theorem bad_selector_detected :
    badMuxPush (packBank emptyBank) .aux .bit1 ≠
      muxPush (packBank emptyBank) .aux .bit1 := by decide

/-- Erasing control keeps only store and bank. -/
def eraseControl (f : NumericFrame) : Nat := Nat.pair f.store f.bank

/-- RED CONTROL: the same data with different control locations collapses. -/
theorem erasing_control_collides :
    (⟨0, 3, 17⟩ : NumericFrame) ≠ ⟨1, 3, 17⟩ ∧
    eraseControl ⟨0, 3, 17⟩ = eraseControl ⟨1, 3, 17⟩ := by decide

/-! ## Certificate -/

theorem global_multiplexer_certificate :
    Function.Bijective packBank ∧
    (∀ packed k s,
      bankRead (unpackBank (muxPush packed k s)) k =
        pushCode s (bankRead (unpackBank packed) k)) ∧
    (∀ packed k j s, j ≠ k →
      bankRead (unpackBank (muxPush packed k s)) j =
        bankRead (unpackBank packed) j) ∧
    (∀ packed k s, muxPop (muxPush packed k s) k = some (s, packed)) ∧
    Function.Bijective packFrame ∧
    (∀ f k s,
      (unpackFrame (frameMuxPush (packFrame f) k s)).control = f.control ∧
      (unpackFrame (frameMuxPush (packFrame f) k s)).store = f.store) ∧
    badMuxPush (packBank emptyBank) .aux .bit1 ≠
      muxPush (packBank emptyBank) .aux .bit1 ∧
    eraseControl ⟨0, 3, 17⟩ = eraseControl ⟨1, 3, 17⟩ :=
  ⟨packBank_bijective, muxPush_selected, muxPush_preserves_other,
   muxPop_after_muxPush, packFrame_bijective,
   fun f k s => ⟨frameMuxPush_keeps_control f k s,
     frameMuxPush_keeps_store f k s⟩,
   bad_selector_detected, erasing_control_collides.2⟩

#print axioms packBank_bijective
#print axioms muxPush_selected
#print axioms muxPush_preserves_other
#print axioms muxPop_after_muxPush
#print axioms packFrame_bijective
#print axioms frameMuxPush_exact
#print axioms bad_selector_detected
#print axioms erasing_control_collides
#print axioms global_multiplexer_certificate

end FoundationStoneTest16Z
