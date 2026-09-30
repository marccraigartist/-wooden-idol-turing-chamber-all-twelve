import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AM: PRIME-EXPONENT PACKING

Lean 4.35.0-rc2 / Mathlib.

The authenticated Mathlib evaluator has four base-five stacks.  A fifth
logical counter is needed while one stack is divided into quotient and
remainder.  This file proves the arithmetic heart of the classical Minsky
packing:

    (C0,C1,C2,C3,T) |-> 2^C0 * 3^C1 * 5^C2 * 7^C3 * 11^T.

Every logical counter can be read back as the corresponding prime valuation.
Consequently the packing is injective; multiplication by a selected prime is
logical increment; divisibility is logical nonzero; and exact division is
logical decrement.  The physical MM2 lowering of those arithmetic operations
is a separate obligation and is deliberately not hidden here.
-/

namespace FoundationStoneTest16AM

structure FiveCounters where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  temp : Nat
deriving DecidableEq, Repr

def pack (s : FiveCounters) : Nat :=
  2 ^ s.c0 * 3 ^ s.c1 * 5 ^ s.c2 * 7 ^ s.c3 * 11 ^ s.temp

theorem pack_pos (s : FiveCounters) : 0 < pack s := by
  simp [pack]

private theorem f2 : Nat.Prime 2 := by norm_num
private theorem f3 : Nat.Prime 3 := by norm_num
private theorem f5 : Nat.Prime 5 := by norm_num
private theorem f7 : Nat.Prime 7 := by norm_num
private theorem f11 : Nat.Prime 11 := by norm_num

theorem factor_two (s : FiveCounters) : (pack s).factorization 2 = s.c0 := by
  rcases s with ⟨a,b,c,d,t⟩
  simp [pack, Nat.factorization_mul,
    Nat.Prime.factorization f2, Nat.Prime.factorization f3,
    Nat.Prime.factorization f5, Nat.Prime.factorization f7,
    Nat.Prime.factorization f11]

theorem factor_three (s : FiveCounters) : (pack s).factorization 3 = s.c1 := by
  rcases s with ⟨a,b,c,d,t⟩
  simp [pack, Nat.factorization_mul,
    Nat.Prime.factorization f2, Nat.Prime.factorization f3,
    Nat.Prime.factorization f5, Nat.Prime.factorization f7,
    Nat.Prime.factorization f11]

theorem factor_five (s : FiveCounters) : (pack s).factorization 5 = s.c2 := by
  rcases s with ⟨a,b,c,d,t⟩
  simp [pack, Nat.factorization_mul,
    Nat.Prime.factorization f2, Nat.Prime.factorization f3,
    Nat.Prime.factorization f5, Nat.Prime.factorization f7,
    Nat.Prime.factorization f11]

theorem factor_seven (s : FiveCounters) : (pack s).factorization 7 = s.c3 := by
  rcases s with ⟨a,b,c,d,t⟩
  simp [pack, Nat.factorization_mul,
    Nat.Prime.factorization f2, Nat.Prime.factorization f3,
    Nat.Prime.factorization f5, Nat.Prime.factorization f7,
    Nat.Prime.factorization f11]

theorem factor_eleven (s : FiveCounters) : (pack s).factorization 11 = s.temp := by
  rcases s with ⟨a,b,c,d,t⟩
  simp [pack, Nat.factorization_mul,
    Nat.Prime.factorization f2, Nat.Prime.factorization f3,
    Nat.Prime.factorization f5, Nat.Prime.factorization f7,
    Nat.Prime.factorization f11]

theorem pack_injective : Function.Injective pack := by
  intro s t h
  have h2 := congrArg (fun n : Nat => n.factorization 2) h
  have h3 := congrArg (fun n : Nat => n.factorization 3) h
  have h5 := congrArg (fun n : Nat => n.factorization 5) h
  have h7 := congrArg (fun n : Nat => n.factorization 7) h
  have h11 := congrArg (fun n : Nat => n.factorization 11) h
  rw [factor_two, factor_two] at h2
  rw [factor_three, factor_three] at h3
  rw [factor_five, factor_five] at h5
  rw [factor_seven, factor_seven] at h7
  rw [factor_eleven, factor_eleven] at h11
  cases s; cases t
  simp_all

def inc0 (s : FiveCounters) : FiveCounters := { s with c0 := s.c0 + 1 }
def inc1 (s : FiveCounters) : FiveCounters := { s with c1 := s.c1 + 1 }
def inc2 (s : FiveCounters) : FiveCounters := { s with c2 := s.c2 + 1 }
def inc3 (s : FiveCounters) : FiveCounters := { s with c3 := s.c3 + 1 }
def incT (s : FiveCounters) : FiveCounters := { s with temp := s.temp + 1 }

theorem increment_laws (s : FiveCounters) :
    pack (inc0 s) = 2 * pack s ∧
    pack (inc1 s) = 3 * pack s ∧
    pack (inc2 s) = 5 * pack s ∧
    pack (inc3 s) = 7 * pack s ∧
    pack (incT s) = 11 * pack s := by
  rcases s with ⟨a,b,c,d,t⟩
  constructor
  · simp [pack, inc0, pow_succ]; ring
  constructor
  · simp [pack, inc1, pow_succ]; ring
  constructor
  · simp [pack, inc2, pow_succ]; ring
  constructor
  · simp [pack, inc3, pow_succ]; ring
  · simp [pack, incT, pow_succ]; ring

theorem two_dvd_iff (s : FiveCounters) : 2 ∣ pack s ↔ 0 < s.c0 := by
  rw [f2.dvd_iff_one_le_factorization (pack_pos s).ne']
  rw [factor_two]
  omega

theorem three_dvd_iff (s : FiveCounters) : 3 ∣ pack s ↔ 0 < s.c1 := by
  rw [f3.dvd_iff_one_le_factorization (pack_pos s).ne']
  rw [factor_three]
  omega

theorem five_dvd_iff (s : FiveCounters) : 5 ∣ pack s ↔ 0 < s.c2 := by
  rw [f5.dvd_iff_one_le_factorization (pack_pos s).ne']
  rw [factor_five]
  omega

theorem seven_dvd_iff (s : FiveCounters) : 7 ∣ pack s ↔ 0 < s.c3 := by
  rw [f7.dvd_iff_one_le_factorization (pack_pos s).ne']
  rw [factor_seven]
  omega

theorem eleven_dvd_iff (s : FiveCounters) : 11 ∣ pack s ↔ 0 < s.temp := by
  rw [f11.dvd_iff_one_le_factorization (pack_pos s).ne']
  rw [factor_eleven]
  omega

def dec0 (s : FiveCounters) : FiveCounters := { s with c0 := s.c0 - 1 }
def dec1 (s : FiveCounters) : FiveCounters := { s with c1 := s.c1 - 1 }
def dec2 (s : FiveCounters) : FiveCounters := { s with c2 := s.c2 - 1 }
def dec3 (s : FiveCounters) : FiveCounters := { s with c3 := s.c3 - 1 }
def decT (s : FiveCounters) : FiveCounters := { s with temp := s.temp - 1 }

theorem decrement_laws (s : FiveCounters) :
    0 < s.c0 → pack (dec0 s) = pack s / 2 := by
  intro h
  rcases s with ⟨a,b,c,d,t⟩
  simp only at h
  obtain ⟨a, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  simp [pack, dec0, pow_succ, Nat.mul_div_left]
  rw [show 2 ^ a * 2 * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ t =
      (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ t) * 2 by ring]
  rw [Nat.mul_div_left _ (by norm_num : 0 < 2)]

theorem decrement_laws_1 (s : FiveCounters) :
    0 < s.c1 → pack (dec1 s) = pack s / 3 := by
  intro h
  rcases s with ⟨a,b,c,d,t⟩
  simp only at h
  obtain ⟨b, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  simp [pack, dec1, pow_succ, Nat.mul_div_left]
  rw [show 2 ^ a * (3 ^ b * 3) * 5 ^ c * 7 ^ d * 11 ^ t =
      (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ t) * 3 by ring]
  rw [Nat.mul_div_left _ (by norm_num : 0 < 3)]

theorem decrement_laws_2 (s : FiveCounters) :
    0 < s.c2 → pack (dec2 s) = pack s / 5 := by
  intro h
  rcases s with ⟨a,b,c,d,t⟩
  simp only at h
  obtain ⟨c, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
  simp [pack, dec2, pow_succ, Nat.mul_div_left]
  rw [show 2 ^ a * 3 ^ b * (5 ^ c * 5) * 7 ^ d * 11 ^ t =
      (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ t) * 5 by ring]
  rw [Nat.mul_div_left _ (by norm_num : 0 < 5)]

theorem decrement_laws_3 (s : FiveCounters) :
    0 < s.c3 → pack (dec3 s) = pack s / 7 := by
  intro h
  rcases s with ⟨a,b,c,d,t⟩
  simp only at h
  obtain ⟨d, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  simp [pack, dec3, pow_succ, Nat.mul_div_left]
  rw [show 2 ^ a * 3 ^ b * 5 ^ c * (7 ^ d * 7) * 11 ^ t =
      (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ t) * 7 by ring]
  rw [Nat.mul_div_left _ (by norm_num : 0 < 7)]

theorem decrement_laws_T (s : FiveCounters) :
    0 < s.temp → pack (decT s) = pack s / 11 := by
  intro h
  rcases s with ⟨a,b,c,d,t⟩
  simp only at h
  obtain ⟨t, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  simp [pack, decT, pow_succ, Nat.mul_div_left]
  rw [show 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * (11 ^ t * 11) =
      (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ t) * 11 by ring]
  rw [Nat.mul_div_left _ (by norm_num : 0 < 11)]

/-! ## Red control: non-coprime bases collapse independent counters. -/

def badPack (x y : Nat) : Nat := 2 ^ x * 4 ^ y

theorem noncoprime_collision : badPack 2 0 = badPack 0 1 := by decide

theorem noncoprime_not_injective :
    ¬ Function.Injective (fun p : Nat × Nat => badPack p.1 p.2) := by
  intro h
  have he := h (a₁ := (2,0)) (a₂ := (0,1))
    (show badPack 2 0 = badPack 0 1 by decide)
  norm_num at he

theorem turing_chamber_16AM_certificate :
    Function.Injective pack ∧
    (∀ s, 2 ∣ pack s ↔ 0 < s.c0) ∧
    (∀ s, 3 ∣ pack s ↔ 0 < s.c1) ∧
    (∀ s, 5 ∣ pack s ↔ 0 < s.c2) ∧
    (∀ s, 7 ∣ pack s ↔ 0 < s.c3) ∧
    (∀ s, 11 ∣ pack s ↔ 0 < s.temp) ∧
    ¬ Function.Injective (fun p : Nat × Nat => badPack p.1 p.2) :=
  ⟨pack_injective, two_dvd_iff, three_dvd_iff, five_dvd_iff,
   seven_dvd_iff, eleven_dvd_iff, noncoprime_not_injective⟩

#print axioms pack_injective
#print axioms increment_laws
#print axioms decrement_laws
#print axioms turing_chamber_16AM_certificate

end FoundationStoneTest16AM
