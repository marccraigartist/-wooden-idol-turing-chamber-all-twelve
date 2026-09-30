import Mathlib

/-!
# THE COMPILED MULTIPLEXER — FOUNDATION STONE TEST 16AA

Tests 16X and 16Z left one precise data-plane question.  The radix PUSH/POP
was literal two-counter code for one stack, while the four-stack multiplexer
used Lean's arithmetic `Nat.pair`/`Nat.unpair`.  This test checks that the
packing layer is not an oracle.

We encode an instruction request as

    pair slot (pair digit packedBank)

where the bank is `pair a (pair b (pair c d))`.  The selector is normalised
modulo four.  The selected coordinate is replaced by `digit + 5 * old`, the
same base-five PUSH law certified operationally in Test 16X.

Lean certifies:

1. all projections and the four specialised updates are primitive recursive;
2. the finite four-way selector is primitive recursive;
3. consequently a concrete partial-recursive program code exists whose
   evaluator is exactly the global multiplexed PUSH;
4. unpacking after any selected update changes exactly that coordinate;
5. selectors differing by a multiple of four choose the same branch;
6. RED CONTROL: erasing the selector is detected on an explicit bank.

The important boundary is explicit.  This compiles the whole arithmetic
multiplexer into Mathlib's program calculus; it does NOT yet translate that
program calculus into the literal two-counter `INC/JZDEC` language of 16X.
Thus 16AA removes “perhaps pair/unpair is non-computable” and “perhaps the
selector needs unbounded memory”, but it does not counterfeit Minsky's missing
compiler theorem.
-/

namespace FoundationStoneTest16AA

/-! ## 1. The exact four-stack bank -/

structure Bank where
  s0 : Nat
  s1 : Nat
  s2 : Nat
  s3 : Nat
deriving DecidableEq, Repr

def pack (b : Bank) : Nat :=
  Nat.pair b.s0 (Nat.pair b.s1 (Nat.pair b.s2 b.s3))

def unpack (n : Nat) : Bank :=
  let p0 := Nat.unpair n
  let p1 := Nat.unpair p0.2
  let p2 := Nat.unpair p1.2
  ⟨p0.1, p1.1, p2.1, p2.2⟩

theorem unpack_pack (b : Bank) : unpack (pack b) = b := by
  rcases b with ⟨a, b, c, d⟩
  simp [unpack, pack, Nat.unpair_pair]

theorem pack_unpack (n : Nat) : pack (unpack n) = n := by
  unfold unpack pack
  simp only
  rw [Nat.pair_unpair, Nat.pair_unpair, Nat.pair_unpair]

def read (b : Bank) (slot : Nat) : Nat :=
  match slot % 4 with
  | 0 => b.s0
  | 1 => b.s1
  | 2 => b.s2
  | _ => b.s3

def write (b : Bank) (slot value : Nat) : Bank :=
  match slot % 4 with
  | 0 => { b with s0 := value }
  | 1 => { b with s1 := value }
  | 2 => { b with s2 := value }
  | _ => { b with s3 := value }

def radixPush (digit payload : Nat) : Nat := digit + 5 * payload

def muxPush (request : Nat) : Nat :=
  let slot := request.unpair.1
  let data := request.unpair.2
  let digit := data.unpair.1
  let packed := data.unpair.2
  let b := unpack packed
  pack (write b slot (radixPush digit (read b slot)))

def request (slot digit packed : Nat) : Nat :=
  Nat.pair slot (Nat.pair digit packed)

/-! ## 2. Exact semantics before compilation -/

theorem muxPush_request (b : Bank) (slot digit : Nat) :
    unpack (muxPush (request slot digit (pack b))) =
      write b slot (radixPush digit (read b slot)) := by
  simp [muxPush, request, unpack_pack]

theorem selected_coordinate_changes_exactly (b : Bank) (slot digit : Nat) :
    read (unpack (muxPush (request slot digit (pack b)))) slot =
      radixPush digit (read b slot) := by
  rw [muxPush_request]
  have hlt : slot % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : slot % 4 <;> simp [read, write, h]

theorem selector_is_finite_control (b : Bank) (slot digit k : Nat) :
    muxPush (request (slot + 4 * k) digit (pack b)) =
      muxPush (request slot digit (pack b)) := by
  simp only [muxPush, request, Nat.unpair_pair, unpack_pack]
  unfold read write
  rw [Nat.add_mul_mod_self_left]

/-! ## 3. Primitive-recursive compiler proof

The proof is deliberately structural.  It uses only pairing, unpairing,
addition, multiplication, remainder by a constant, and finite case splits.
-/

def leftN (n : Nat) : Nat := n.unpair.1
def rightN (n : Nat) : Nat := n.unpair.2

theorem leftN_prim : Primrec leftN := by
  exact Primrec.fst.comp Primrec.unpair

theorem rightN_prim : Primrec rightN := by
  exact Primrec.snd.comp Primrec.unpair

theorem mod4_prim : Primrec (fun n : Nat => n % 4) := by
  exact Primrec.nat_mod.comp Primrec.id (Primrec.const 4)

theorem radixPush_prim : Primrec₂ radixPush := by
  exact Primrec.nat_add.comp₂ Primrec₂.left
    (Primrec.nat_mul.comp₂ (Primrec₂.const 5) Primrec₂.right)

def b0 (n : Nat) : Nat := leftN n
def br1 (n : Nat) : Nat := rightN n
def b1 (n : Nat) : Nat := leftN (br1 n)
def br2 (n : Nat) : Nat := rightN (br1 n)
def b2 (n : Nat) : Nat := leftN (br2 n)
def b3 (n : Nat) : Nat := rightN (br2 n)

theorem b0_prim : Primrec b0 := leftN_prim
theorem br1_prim : Primrec br1 := rightN_prim
theorem b1_prim : Primrec b1 := leftN_prim.comp br1_prim
theorem br2_prim : Primrec br2 := rightN_prim.comp br1_prim
theorem b2_prim : Primrec b2 := leftN_prim.comp br2_prim
theorem b3_prim : Primrec b3 := rightN_prim.comp br2_prim

def rebuild0 (digit bank : Nat) : Nat :=
  Nat.pair (radixPush digit (b0 bank)) (br1 bank)

def rebuild1 (digit bank : Nat) : Nat :=
  Nat.pair (b0 bank)
    (Nat.pair (radixPush digit (b1 bank)) (br2 bank))

def rebuild2 (digit bank : Nat) : Nat :=
  Nat.pair (b0 bank)
    (Nat.pair (b1 bank)
      (Nat.pair (radixPush digit (b2 bank)) (b3 bank)))

def rebuild3 (digit bank : Nat) : Nat :=
  Nat.pair (b0 bank)
    (Nat.pair (b1 bank)
      (Nat.pair (b2 bank) (radixPush digit (b3 bank))))

theorem rebuild0_prim : Primrec₂ rebuild0 := by
  exact Primrec₂.natPair.comp₂
    (radixPush_prim.comp₂ Primrec₂.left (b0_prim.comp₂ Primrec₂.right))
    (br1_prim.comp₂ Primrec₂.right)

theorem rebuild1_prim : Primrec₂ rebuild1 := by
  exact Primrec₂.natPair.comp₂
    (b0_prim.comp₂ Primrec₂.right)
    (Primrec₂.natPair.comp₂
      (radixPush_prim.comp₂ Primrec₂.left (b1_prim.comp₂ Primrec₂.right))
      (br2_prim.comp₂ Primrec₂.right))

theorem rebuild2_prim : Primrec₂ rebuild2 := by
  exact Primrec₂.natPair.comp₂
    (b0_prim.comp₂ Primrec₂.right)
    (Primrec₂.natPair.comp₂
      (b1_prim.comp₂ Primrec₂.right)
      (Primrec₂.natPair.comp₂
        (radixPush_prim.comp₂ Primrec₂.left (b2_prim.comp₂ Primrec₂.right))
        (b3_prim.comp₂ Primrec₂.right)))

theorem rebuild3_prim : Primrec₂ rebuild3 := by
  exact Primrec₂.natPair.comp₂
    (b0_prim.comp₂ Primrec₂.right)
    (Primrec₂.natPair.comp₂
      (b1_prim.comp₂ Primrec₂.right)
      (Primrec₂.natPair.comp₂
        (b2_prim.comp₂ Primrec₂.right)
        (radixPush_prim.comp₂ Primrec₂.left (b3_prim.comp₂ Primrec₂.right))))

def selectRebuild (slot digit bank : Nat) : Nat :=
  match slot % 4 with
  | 0 => rebuild0 digit bank
  | 1 => rebuild1 digit bank
  | 2 => rebuild2 digit bank
  | _ => rebuild3 digit bank

def selectOnPair (p : Nat × Nat) : Nat :=
  let slot := p.1.unpair.1
  let digit := p.1.unpair.2
  selectRebuild slot digit p.2

/-! We expose the finite branch as nested equality tests.  This is extensionally
the same function and makes the primitive-recursive construction transparent. -/
def selectRebuildIf (slot digit bank : Nat) : Nat :=
  if slot % 4 = 0 then rebuild0 digit bank
  else if slot % 4 = 1 then rebuild1 digit bank
  else if slot % 4 = 2 then rebuild2 digit bank
  else rebuild3 digit bank

theorem selectRebuild_eq_if : selectRebuild = selectRebuildIf := by
  funext slot digit bank
  have hlt : slot % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : slot % 4 <;> simp [selectRebuild, selectRebuildIf, h]

theorem muxPush_eq_select (n : Nat) :
    muxPush n = selectRebuild n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2 := by
  have hlt : n.unpair.1 % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : n.unpair.1 % 4 <;>
    simp [muxPush, selectRebuild, unpack, pack, write, read, radixPush,
      rebuild0, rebuild1, rebuild2, rebuild3, b0, b1, b2, b3, br1, br2,
      leftN, rightN, h]

/-! The whole mux is primitive recursive.  The finite case proof is completed
below using the standard primitive-recursive equality/if constructors. -/
theorem muxPush_prim_root : Primrec muxPush := by
  -- `simp?`/closure automation is intentionally avoided: every operation is visible.
  have h := (Primrec.ite
    (Primrec.eq.comp
      (mod4_prim.comp leftN_prim)
      (Primrec.const 0))
    (rebuild0_prim.comp
      (leftN_prim.comp rightN_prim)
      (rightN_prim.comp rightN_prim))
    (Primrec.ite
      (Primrec.eq.comp
        (mod4_prim.comp leftN_prim)
        (Primrec.const 1))
      (rebuild1_prim.comp
        (leftN_prim.comp rightN_prim)
        (rightN_prim.comp rightN_prim))
      (Primrec.ite
        (Primrec.eq.comp
          (mod4_prim.comp leftN_prim)
          (Primrec.const 2))
        (rebuild2_prim.comp
          (leftN_prim.comp rightN_prim)
          (rightN_prim.comp rightN_prim))
        (rebuild3_prim.comp
          (leftN_prim.comp rightN_prim)
          (rightN_prim.comp rightN_prim)))))
  apply h.of_eq
  intro n
  change selectRebuildIf (leftN n) (leftN (rightN n)) (rightN (rightN n)) = muxPush n
  rw [← selectRebuild_eq_if]
  simpa [leftN, rightN] using (muxPush_eq_select n).symm

theorem muxPush_prim : Nat.Primrec muxPush :=
  Primrec.nat_iff.mp muxPush_prim_root

/-! ## 4. An actual program code, not merely a Lean evaluator -/

open Nat.Partrec
open Nat.Partrec.Code

theorem compiled_mux_exists :
    ∃ c : Nat.Partrec.Code, c.eval = (muxPush : Nat →. Nat) := by
  exact (Nat.Partrec.Code.exists_code.mp (Nat.Partrec.of_primrec muxPush_prim))

theorem compiled_mux_runs_exactly :
    ∃ c : Nat.Partrec.Code, ∀ n out,
      out ∈ c.eval n ↔ out = muxPush n := by
  obtain ⟨c, hc⟩ := compiled_mux_exists
  refine ⟨c, fun n out => ?_⟩
  rw [hc]
  simp

/-! ## 5. Red control -/

def eraseSelector (n : Nat) : Nat :=
  request 0 n.unpair.2.unpair.1 n.unpair.2.unpair.2

def witnessBank : Bank := ⟨1, 2, 3, 4⟩

theorem erased_selector_is_detected :
    muxPush (eraseSelector (request 2 4 (pack witnessBank))) ≠
      muxPush (request 2 4 (pack witnessBank)) := by
  norm_num [eraseSelector, request, muxPush, pack, unpack, write, read,
    radixPush, witnessBank]

/-! ## Certificate -/

theorem compiled_multiplexer_certificate :
    Nat.Primrec muxPush ∧
    (∀ b slot digit,
      read (unpack (muxPush (request slot digit (pack b)))) slot =
        radixPush digit (read b slot)) ∧
    (∀ b slot digit k,
      muxPush (request (slot + 4 * k) digit (pack b)) =
        muxPush (request slot digit (pack b))) ∧
    (∃ c : Nat.Partrec.Code, ∀ n out,
      out ∈ c.eval n ↔ out = muxPush n) ∧
    muxPush (eraseSelector (request 2 4 (pack witnessBank))) ≠
      muxPush (request 2 4 (pack witnessBank)) :=
  ⟨muxPush_prim, selected_coordinate_changes_exactly,
   selector_is_finite_control, compiled_mux_runs_exactly,
   erased_selector_is_detected⟩

#print axioms unpack_pack
#print axioms pack_unpack
#print axioms selected_coordinate_changes_exactly
#print axioms selector_is_finite_control
#print axioms muxPush_prim
#print axioms compiled_mux_exists
#print axioms compiled_mux_runs_exactly
#print axioms erased_selector_is_detected
#print axioms compiled_multiplexer_certificate

end FoundationStoneTest16AA
