import Mathlib

/-!
# THE N-SPECTRUM — TEST 10: PRIMES, MIRRORS AND LIFTED RETURN

This file asks which parts of the twelve-seat Wooden Idol belong specifically to N12
and which belong to an arbitrary finite clock.

There are three independent mechanisms.

1. ORBIT ARITHMETIC.  On an N-clock, a step `k` is addition by `k` modulo N.  A unit
   step has the same return equation as step 1.  At prime N every nonzero step is a
   unit, so every nonzero turn is arithmetically indivisible.
2. MIRROR PARITY.  The gap mirror `k ↦ N - 1 - k` has no fixed seat when N is even,
   but it has a central fixed seat when N is odd.  This is parity, not primality.
3. HELIX MEMORY.  Lifting any move by a height counter prevents full-state return
   after every positive number of steps, even when the circular shadow closes.

N12 is therefore special in a precise mixed sense: it is even, so its gap mirror is
fixed-point-free, and highly composite, so it supports proper subcycles of lengths
2, 3, 4 and 6 as well as the full 12-cycle.

Honest scope: this classifies the finite clock mechanism used here.  It does not yet
classify the three-dimensional two-axis Dead Globe rotations for every angle 2π/N.
-/

namespace FoundationStoneTestTen

/-! ## Part 1 — arbitrary cyclic clocks -/

abbrev Clock (N : Nat) := ZMod N

def turn {N : Nat} (k : Clock N) (x : Clock N) : Clock N := x + k

def iterF {X : Type} (f : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => f (iterF f n x)

/-- After `t` turns by `k`, the clock has added `t*k`. -/
theorem iter_turn {N : Nat} (k x : Clock N) :
    ∀ t, iterF (turn k) t x = x + (t : Clock N) * k := by
  intro t
  induction t with
  | zero => simp [iterF]
  | succ t ih =>
      simp only [iterF, turn, ih, Nat.cast_add, Nat.cast_one]
      ring

/-- A unit step has exactly the same return equation as the one-seat step. -/
theorem unit_turn_returns_iff {N : Nat} (k x : Clock N) (hk : IsUnit k) (t : Nat) :
    iterF (turn k) t x = x ↔ (t : Clock N) = 0 := by
  rw [iter_turn]
  constructor
  · intro h
    have hmul : (t : Clock N) * k = 0 := by
      apply add_left_cancel (a := x)
      simpa using h
    obtain ⟨u, rfl⟩ := hk
    calc
      (t : Clock N) = (t : Clock N) * (u : Clock N) * (↑u⁻¹ : Clock N) := by simp
      _ = 0 * (↑u⁻¹ : Clock N) := by rw [hmul]
      _ = 0 := by simp
  · intro ht
    rw [ht]
    simp

/-- At a prime modulus, every nonzero step is a unit. -/
theorem prime_nonzero_step_is_unit (p : Nat) [hp : Fact p.Prime] (k : Clock p)
    (hk : k ≠ 0) : IsUnit k := by
  exact isUnit_iff_ne_zero.mpr hk

/-- Hence at prime N every nonzero step has the full-clock return equation. -/
theorem prime_turn_returns_iff (p : Nat) [Fact p.Prime] (k x : Clock p)
    (hk : k ≠ 0) (t : Nat) :
    iterF (turn k) t x = x ↔ (t : Clock p) = 0 :=
  unit_turn_returns_iff k x (prime_nonzero_step_is_unit p k hk) t

/-! ## Part 2 — the gap mirror is governed by parity -/

/-- The mirror through the two gaps neighbouring seats 0 and N-1. -/
def gapMirror {N : Nat} (_hN : 0 < N) (x : Fin N) : Fin N :=
  ⟨N - 1 - x.val, by omega⟩

/-- On every positive even clock the gap mirror fixes no seat. -/
theorem even_gapMirror_fixedPointFree (N : Nat) (hN : 0 < N) (hEven : Even N) :
    ∀ x : Fin N, gapMirror hN x ≠ x := by
  intro x hx
  have hv := congrArg Fin.val hx
  simp only [gapMirror] at hv
  obtain ⟨m, hm⟩ := hEven
  omega

/-- On every odd clock the same mirror fixes its central seat. -/
theorem odd_gapMirror_hasFixedPoint (N : Nat) (hN : 0 < N) (hOdd : Odd N) :
    ∃ x : Fin N, gapMirror hN x = x := by
  obtain ⟨m, hm⟩ := hOdd
  subst N
  refine ⟨⟨m, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [gapMirror]
  omega

/-! ## Part 3 — concrete controls: prime 5 versus composite 12 -/

def finTurn {N : Nat} (k : Fin N) (x : Fin N) : Fin N := x + k

/-- Prime control: every nonzero step on the 5-clock returns first after five turns. -/
theorem five_prime_full_cycles :
    ∀ k : Fin 5, k ≠ 0 →
      (∀ x, iterF (finTurn k) 5 x = x) ∧
      (∀ t : Fin 5, t ≠ 0 → ∀ x, iterF (finTurn k) t.val x ≠ x) := by
  decide

/-- N12 admits proper cycles: half-turn, third-turn and quarter-turn. -/
theorem twelve_composite_subcycles :
    (∀ x : Fin 12, iterF (finTurn 6) 2 x = x) ∧
    (∀ x : Fin 12, iterF (finTurn 4) 3 x = x) ∧
    (∀ x : Fin 12, iterF (finTurn 3) 4 x = x) ∧
    (∀ x : Fin 12, iterF (finTurn 2) 6 x = x) ∧
    (∀ x : Fin 12, iterF (finTurn 1) 12 x = x) := by
  decide

/-- N12's gap mirror is fixed-point-free. -/
theorem twelve_gap_mirror_has_no_fixed_seat :
    ∀ x : Fin 12, gapMirror (by decide : 0 < 12) x ≠ x :=
  even_gapMirror_fixedPointFree 12 (by decide) (by decide)

/-- Odd-prime control: the 5-clock gap mirror fixes seat 2. -/
theorem five_gap_mirror_fixes_two :
    gapMirror (by decide : 0 < 5) (2 : Fin 5) = 2 := by decide

/-! ## Part 4 — every clock can be lifted to a non-closing helix -/

structure LiftedState (X : Type) where
  shadow : X
  height : Nat
deriving DecidableEq

def liftOnce {X : Type} (move : X → X) (s : LiftedState X) : LiftedState X :=
  ⟨move s.shadow, s.height + 1⟩

def runLift {X : Type} (move : X → X) : Nat → LiftedState X → LiftedState X
  | 0, s => s
  | n + 1, s => liftOnce move (runLift move n s)

theorem lifted_height {X : Type} (move : X → X) :
    ∀ n s, (runLift move n s).height = s.height + n := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      simp only [runLift, liftOnce]
      rw [ih]
      omega

/-- Independent of N: a positive lifted run never returns to the same full state. -/
theorem positive_lift_never_returns {X : Type} (move : X → X) (n : Nat) (hn : 0 < n) :
    ∀ s, runLift move n s ≠ s := by
  intro s hreturn
  have hh := congrArg LiftedState.height hreturn
  rw [lifted_height] at hh
  omega

/-- The N12 shadow closes after twelve one-seat turns, but its helix does not. -/
theorem twelve_shadow_closes_helix_does_not (s : LiftedState (Fin 12)) :
    (runLift (finTurn 1) 12 s).shadow = s.shadow ∧
    runLift (finTurn 1) 12 s ≠ s := by
  constructor
  · change iterF (finTurn 1) 12 s.shadow = s.shadow
    exact twelve_composite_subcycles.2.2.2.2 s.shadow
  · exact positive_lift_never_returns (finTurn 1) 12 (by decide) s

/-- Prime clocks behave the same after projection: closure does not imply lifted return. -/
theorem five_shadow_closes_helix_does_not (s : LiftedState (Fin 5)) :
    (runLift (finTurn 1) 5 s).shadow = s.shadow ∧
    runLift (finTurn 1) 5 s ≠ s := by
  constructor
  · change iterF (finTurn 1) 5 s.shadow = s.shadow
    exact (five_prime_full_cycles 1 (by decide)).1 s.shadow
  · exact positive_lift_never_returns (finTurn 1) 5 (by decide) s

/-! ## Certificate -/

theorem n_spectrum_certificate :
    (∀ (N : Nat) (hN : 0 < N), Even N → ∀ x : Fin N, gapMirror hN x ≠ x) ∧
    (∀ (N : Nat) (hN : 0 < N), Odd N → ∃ x : Fin N, gapMirror hN x = x) ∧
    (∀ k : Fin 5, k ≠ 0 →
      (∀ x, iterF (finTurn k) 5 x = x) ∧
      (∀ t : Fin 5, t ≠ 0 → ∀ x, iterF (finTurn k) t.val x ≠ x)) ∧
    (∀ x : Fin 12, gapMirror (by decide : 0 < 12) x ≠ x) ∧
    (∀ (X : Type) (move : X → X) n, 0 < n → ∀ s, runLift move n s ≠ s) :=
  ⟨even_gapMirror_fixedPointFree,
   odd_gapMirror_hasFixedPoint,
   five_prime_full_cycles,
   twelve_gap_mirror_has_no_fixed_seat,
   fun X move n hn => positive_lift_never_returns (X := X) move n hn⟩

#print axioms iter_turn
#print axioms unit_turn_returns_iff
#print axioms prime_nonzero_step_is_unit
#print axioms prime_turn_returns_iff
#print axioms even_gapMirror_fixedPointFree
#print axioms odd_gapMirror_hasFixedPoint
#print axioms five_prime_full_cycles
#print axioms twelve_composite_subcycles
#print axioms twelve_gap_mirror_has_no_fixed_seat
#print axioms five_gap_mirror_fixes_two
#print axioms lifted_height
#print axioms positive_lift_never_returns
#print axioms twelve_shadow_closes_helix_does_not
#print axioms five_shadow_closes_helix_does_not
#print axioms n_spectrum_certificate

end FoundationStoneTestTen
