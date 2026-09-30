import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AL: FOUR STACK COUNTERS AND REAL SCRATCH

Lean 4.35.0-rc2 / Mathlib.

Instead of expanding Mathlib's four-stack TM2 into the much larger alphabet of
`TM2to1`, this data layer keeps the source alphabet `Fin 4` and represents the
four stacks by four base-five counters plus one temporary counter.

Lean certifies that the representation is injective, that the temporary
counter is zero at every source-machine boundary, and that push/pop/top on any
individual stack have the exact arithmetic contract used by 16AK.

The red control is deliberately narrow.  16AK's literal division block returns
`oldB + quotient` in B.  Therefore, if A and B are used directly for the two
tape halves, a nonzero right half is contaminated.  This does NOT claim that
two-counter simulation is impossible; 16AM's prime packing is the escape.
-/

namespace FoundationStoneTest16AL

abbrev Digit := Fin 4

def code : List Digit → Nat
  | [] => 0
  | d :: s => d.val + 1 + 5 * code s

def top (n : Nat) : Nat := (n - 1) % 5
def pop (n : Nat) : Nat := (n - 1) / 5
def push (d : Digit) (n : Nat) : Nat := d.val + 1 + 5 * n

theorem code_cons_pos (d : Digit) (s : List Digit) : 0 < code (d :: s) := by
  simp [code]

theorem code_zero_iff (s : List Digit) : code s = 0 ↔ s = [] := by
  cases s with
  | nil => simp [code]
  | cons d s =>
      constructor
      · intro h; have := code_cons_pos d s; omega
      · intro h; contradiction

theorem top_exact (d : Digit) (s : List Digit) : top (code (d :: s)) = d.val := by
  unfold top code
  have hd := d.isLt
  omega

theorem pop_exact (d : Digit) (s : List Digit) : pop (code (d :: s)) = code s := by
  unfold pop
  change (d.val + 1 + 5 * code s - 1) / 5 = code s
  have hd := d.isLt
  have hs : d.val + 1 + 5 * code s - 1 = d.val + 5 * code s := by omega
  rw [hs, Nat.add_mul_div_left _ _ (by decide)]
  rw [Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem code_injective : Function.Injective code := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      exact ((code_zero_iff ys).mp (by simpa [code] using h.symm)).symm
  | cons d ds ih =>
      intro ys h
      cases ys with
      | nil => have := code_cons_pos d ds; simp [code] at h
      | cons e es =>
          have hv : d.val = e.val := by
            have := congrArg top h
            simpa [top_exact] using this
          have hde : d = e := Fin.ext hv
          subst e
          have hp := congrArg pop h
          have hrs : code ds = code es := by simpa [pop_exact] using hp
          exact congrArg (List.cons d) (ih hrs)

structure FourStacks where
  s0 : List Digit
  s1 : List Digit
  s2 : List Digit
  s3 : List Digit
deriving DecidableEq, Repr

structure FiveCounters where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  temp : Nat
deriving DecidableEq, Repr

def encode (s : FourStacks) : FiveCounters :=
  ⟨code s.s0, code s.s1, code s.s2, code s.s3, 0⟩

theorem encode_injective : Function.Injective encode := by
  intro s t h
  have h0 := congrArg FiveCounters.c0 h
  have h1 := congrArg FiveCounters.c1 h
  have h2 := congrArg FiveCounters.c2 h
  have h3 := congrArg FiveCounters.c3 h
  cases s; cases t
  simp only [encode] at h0 h1 h2 h3
  simp only [FourStacks.mk.injEq]
  exact ⟨code_injective h0, code_injective h1,
    code_injective h2, code_injective h3⟩

theorem boundary_scratch_zero (s : FourStacks) : (encode s).temp = 0 := rfl

def push0 (d : Digit) (s : FourStacks) : FourStacks := { s with s0 := d :: s.s0 }

theorem push0_contract (d : Digit) (s : FourStacks) :
    (encode (push0 d s)).c0 = push d (encode s).c0 ∧
    (encode (push0 d s)).c1 = (encode s).c1 ∧
    (encode (push0 d s)).c2 = (encode s).c2 ∧
    (encode (push0 d s)).c3 = (encode s).c3 ∧
    (encode (push0 d s)).temp = 0 := by
  simp [encode, push0, push, code]

def pop0 (s : FourStacks) : FourStacks := { s with s0 := s.s0.tail }

theorem pop0_contract (d : Digit) (rest : List Digit)
    (s1 s2 s3 : List Digit) :
    encode (pop0 ⟨d :: rest, s1, s2, s3⟩) =
      ⟨pop (code (d :: rest)), code s1, code s2, code s3, 0⟩ := by
  simp [encode, pop0, pop_exact]

/-! ## Representation-specific red control -/

/-- Arithmetic result of 16AK's division block: A is emptied and its quotient
is ADDED to the pre-existing B. -/
def div5Result (a b : Nat) : Nat × Nat := (0, b + a / 5)

theorem occupied_second_counter_is_contaminated :
    div5Result 5 7 = (0, 8) ∧ div5Result 5 0 = (0, 1) := by decide

theorem direct_halves_do_not_preserve_right :
    (div5Result 5 7).2 ≠ 7 := by decide

theorem turing_chamber_16AL_certificate :
    Function.Injective encode ∧
    (∀ s, (encode s).temp = 0) ∧
    (∀ d s, (encode (push0 d s)).c0 = push d (encode s).c0) ∧
    (div5Result 5 7).2 ≠ 7 :=
  ⟨encode_injective, boundary_scratch_zero, fun d s => (push0_contract d s).1,
   direct_halves_do_not_preserve_right⟩

#print axioms code_injective
#print axioms encode_injective
#print axioms push0_contract
#print axioms pop0_contract
#print axioms direct_halves_do_not_preserve_right
#print axioms turing_chamber_16AL_certificate

end FoundationStoneTest16AL
