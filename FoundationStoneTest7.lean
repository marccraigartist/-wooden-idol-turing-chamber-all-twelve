import Mathlib

/-!
# THE FOUNDATION STONE — TEST 7: EARNING THE ROTATION

Test 6 assumed that the transport between bodies A and B was a rotation, then proved
that reciprocity and separation force its offset to be six.  Test 7 removes that family
assumption.  The transport begins as an arbitrary function on the twelve seats.

Lean checks:
1. If an arbitrary transport commutes with the one-seat forward move, then it is
   necessarily translation by its value at B12.  The rotation is earned from behaviour.
2. If the same transport is reciprocal and has no fixed seat, its earned offset is six.
3. Consequently the transport is the antipode everywhere, and B's own B1 is A's B7.
4. Red control: reciprocity plus separation do not suffice.  Magenta has both properties
   but reverses the forward move rather than commuting with it.
5. A second red control makes the assumption boundary explicit: magenta obeys
   reverse-oriented shared movement rather than the antipode's shared direction.

Scope: this proves a rigidity theorem for a directed twelve-seat cycle.  It does not show
that the Wooden Idol generates the shared direction.  That becomes Test 8.
-/

namespace FoundationStoneTestSeven

abbrev Seat := Fin 12

def clockForward (seat : Seat) : Seat := seat + 1
def clockBack (seat : Seat) : Seat := seat + 11
def rotation (offset seat : Seat) : Seat := seat + offset
def antipode (seat : Seat) : Seat := seat + 6
def magenta (seat : Seat) : Seat := 11 - seat

/-- A transport respects the common directed successor operation. -/
def SharesForward (f : Seat → Seat) : Prop :=
  ∀ seat, f (clockForward seat) = clockForward (f seat)

/-- Both bodies use the same map in opposite directions. -/
def Reciprocal (f : Seat → Seat) : Prop :=
  ∀ seat, f (f seat) = seat

/-- The two frames never identify a seat with itself. -/
def Separate (f : Seat → Seat) : Prop :=
  ∀ seat, f seat ≠ seat

def iterF (f : Seat → Seat) : Nat → Seat → Seat
  | 0, seat => seat
  | n + 1, seat => f (iterF f n seat)

/-- Equivariance for one forward step propagates through every finite number of steps. -/
theorem shares_forward_iter (f : Seat → Seat) (h : SharesForward f) :
    ∀ n seat, f (iterF clockForward n seat) = iterF clockForward n (f seat) := by
  intro n
  induction n with
  | zero => intro seat; rfl
  | succ n ih =>
      intro seat
      simp only [iterF]
      rw [h, ih]

/-- Starting at B12, `seat.val` forward steps reach the seat itself. -/
theorem seat_generated_from_zero : ∀ seat : Seat,
    iterF clockForward seat.val (0 : Seat) = seat := by
  intro seat
  fin_cases seat <;> decide

/-- Starting anywhere, the same number of forward steps is addition by that seat. -/
theorem iter_forward_from_seat : ∀ target start : Seat,
    iterF clockForward target.val start = rotation start target := by
  intro target start
  fin_cases target <;> simp [iterF, clockForward, rotation, add_comm, add_left_comm]

/-- The key rigidity theorem: shared forward movement forces an arbitrary map to be a
rotation.  No rotational form occurs in the hypotheses. -/
theorem shared_forward_forces_rotation (f : Seat → Seat) (h : SharesForward f) :
    ∀ seat, f seat = rotation (f 0) seat := by
  intro seat
  have heq := shares_forward_iter f h seat.val (0 : Seat)
  rw [seat_generated_from_zero seat] at heq
  rw [iter_forward_from_seat seat (f 0)] at heq
  exact heq

/-- Every rotation respects the chosen direction. -/
theorem rotation_shares_forward (offset : Seat) : SharesForward (rotation offset) := by
  intro seat
  unfold clockForward rotation
  abel

/-- Thus shared-forward transports are exactly the rotations, with a uniquely exposed
offset `f 0`. -/
theorem shares_forward_iff_rotation (f : Seat → Seat) :
    SharesForward f ↔ ∃ offset, ∀ seat, f seat = rotation offset seat := by
  constructor
  · intro h
    exact ⟨f 0, shared_forward_forces_rotation f h⟩
  · rintro ⟨offset, h⟩ seat
    rw [h, h]
    exact rotation_shares_forward offset seat

/-- A rotation is reciprocal exactly when twice its offset is zero on the clock. -/
theorem reciprocal_rotation_iff_double_zero (offset : Seat) :
    Reciprocal (rotation offset) ↔ offset + offset = 0 := by
  constructor
  · intro h
    simpa [Reciprocal, rotation] using h (0 : Seat)
  · intro h seat
    unfold rotation
    rw [add_assoc, h, add_zero]

/-- A rotation used reciprocally has offset zero or six. -/
theorem reciprocal_rotation_offset (offset : Seat)
    (h : Reciprocal (rotation offset)) : offset = 0 ∨ offset = 6 := by
  have hdbl := (reciprocal_rotation_iff_double_zero offset).mp h
  fin_cases offset <;> simp_all

/-- A separated rotation cannot have offset zero. -/
theorem separate_rotation_nonzero (offset : Seat)
    (h : Separate (rotation offset)) : offset ≠ 0 := by
  intro hoffset
  subst hoffset
  exact h 0 (by decide)

/-- Main result: behavioural direction + reciprocity + separation force the antipode. -/
theorem directed_reciprocal_separation_forces_six (f : Seat → Seat)
    (hforward : SharesForward f) (hreciprocal : Reciprocal f)
    (hseparate : Separate f) : f 0 = 6 := by
  have hform := shared_forward_forces_rotation f hforward
  have hrecrot : Reciprocal (rotation (f 0)) := by
    intro seat
    rw [← hform seat, ← hform (f seat)]
    exact hreciprocal seat
  have hseprot : Separate (rotation (f 0)) := by
    intro seat
    rw [← hform seat]
    exact hseparate seat
  rcases reciprocal_rotation_offset (f 0) hrecrot with hzero | hsix
  · exact False.elim (separate_rotation_nonzero (f 0) hseprot hzero)
  · exact hsix

/-- The whole arbitrary transport, not merely its offset, is the antipode. -/
theorem directed_reciprocal_separation_forces_antipode (f : Seat → Seat)
    (hforward : SharesForward f) (hreciprocal : Reciprocal f)
    (hseparate : Separate f) : ∀ seat, f seat = antipode seat := by
  intro seat
  rw [shared_forward_forces_rotation f hforward seat,
    directed_reciprocal_separation_forces_six f hforward hreciprocal hseparate]
  rfl

/-- B's own B1 is A's B7, now without assuming the transport was a rotation. -/
theorem earned_B_own_B1_is_A_B7 (f : Seat → Seat)
    (hforward : SharesForward f) (hreciprocal : Reciprocal f)
    (hseparate : Separate f) : f 1 = 7 := by
  rw [directed_reciprocal_separation_forces_antipode f hforward hreciprocal hseparate]
  decide

/-! ## Red controls -/

theorem antipode_reciprocal : Reciprocal antipode := by
  intro seat
  fin_cases seat <;> decide
theorem antipode_separate : Separate antipode := by
  intro seat
  fin_cases seat <;> decide
theorem antipode_shares_forward : SharesForward antipode := by
  intro seat
  unfold antipode clockForward
  abel

theorem magenta_reciprocal : Reciprocal magenta := by
  intro seat
  fin_cases seat <;> decide
theorem magenta_separate : Separate magenta := by
  intro seat
  fin_cases seat <;> decide

/-- Magenta shares the undirected clock but reverses its selected direction. -/
theorem magenta_reverses_forward : ∀ seat,
    magenta (clockForward seat) = clockBack (magenta seat) := by decide

theorem magenta_not_shares_forward : ¬ SharesForward magenta := by
  intro h
  exact (by decide :
    magenta (clockForward (0 : Seat)) ≠ clockForward (magenta (0 : Seat))) (h 0)

/-- Reciprocity and separation alone still admit two distinct maps. -/
theorem undirected_red_control :
    ∃ f g : Seat → Seat,
      Reciprocal f ∧ Separate f ∧ Reciprocal g ∧ Separate g ∧ f ≠ g := by
  refine ⟨antipode, magenta, antipode_reciprocal, antipode_separate,
    magenta_reciprocal, magenta_separate, ?_⟩
  intro h
  have h0 := congrFun h (0 : Seat)
  exact (by decide : antipode (0 : Seat) ≠ magenta (0 : Seat)) h0

/-- The test's complete certificate. -/
theorem foundation_stone_test_seven :
    (∀ f : Seat → Seat, SharesForward f →
      ∀ seat, f seat = rotation (f 0) seat) ∧
    (∀ f : Seat → Seat,
      SharesForward f → Reciprocal f → Separate f → f 0 = 6) ∧
    (∀ f : Seat → Seat,
      SharesForward f → Reciprocal f → Separate f →
        ∀ seat, f seat = antipode seat) ∧
    (∀ f : Seat → Seat,
      SharesForward f → Reciprocal f → Separate f → f 1 = 7) ∧
    (Reciprocal antipode ∧ Separate antipode ∧ SharesForward antipode) ∧
    (Reciprocal magenta ∧ Separate magenta ∧ ¬ SharesForward magenta) ∧
    (∀ seat, magenta (clockForward seat) = clockBack (magenta seat)) ∧
    (∃ f g : Seat → Seat,
      Reciprocal f ∧ Separate f ∧ Reciprocal g ∧ Separate g ∧ f ≠ g) :=
  ⟨shared_forward_forces_rotation,
   directed_reciprocal_separation_forces_six,
   directed_reciprocal_separation_forces_antipode,
   earned_B_own_B1_is_A_B7,
   ⟨antipode_reciprocal, antipode_separate, antipode_shares_forward⟩,
   ⟨magenta_reciprocal, magenta_separate, magenta_not_shares_forward⟩,
   magenta_reverses_forward,
   undirected_red_control⟩

#print axioms shared_forward_forces_rotation
#print axioms shares_forward_iff_rotation
#print axioms reciprocal_rotation_iff_double_zero
#print axioms directed_reciprocal_separation_forces_six
#print axioms directed_reciprocal_separation_forces_antipode
#print axioms earned_B_own_B1_is_A_B7
#print axioms antipode_shares_forward
#print axioms magenta_reverses_forward
#print axioms magenta_not_shares_forward
#print axioms undirected_red_control
#print axioms foundation_stone_test_seven

end FoundationStoneTestSeven
