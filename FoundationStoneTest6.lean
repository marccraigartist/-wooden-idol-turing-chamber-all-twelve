import Mathlib

/-!
# THE FOUNDATION STONE — TEST 6: EARNING THE +6 ALIGNMENT

Test 5 used the antipodal coordinate change `k ↦ k + 6`.  Test 6 asks whether
that alignment is forced or merely selected.

There are two different questions:

* among transports that preserve the orientation of the shared twelve-seat clock
  (therefore rotations `k ↦ k + offset`), which transports are reciprocal?
* if we forget the oriented-clock requirement and allow arbitrary seat maps, do
  reciprocity and separation still determine the transport?

Lean checks:
1. Every rotation preserves the one-seat forward movement.
2. A rotational transport is reciprocal exactly at offsets 0 and 6.
3. Requiring the two frames to be different removes 0, uniquely forcing +6.
4. Therefore B's local B1 is A's B7; this is now earned from the stated alignment
   principles rather than inserted as the offset.
5. Red control: magenta and the antipode are distinct, fixed-point-free reciprocal
   maps.  Thus two bodies + reciprocity + separation alone do NOT force +6.
6. Magenta reverses the forward direction, so the red control is excluded precisely
   by the shared oriented-clock condition.

The result is conditional and exact: +6 is the unique nontrivial reciprocal
ROTATION of a twelve-seat clock.  It is not the unique fixed-point-free involution
of twelve seats, and it is not forced by the phrase "two bodies" alone.
-/

namespace FoundationStoneTestSix

abbrev Seat := Fin 12

inductive Body
  | A
  | B
deriving DecidableEq

/-- The magenta half-seat reflection from the earlier tests. -/
def magenta (seat : Seat) : Seat := 11 - seat

theorem magenta_twice : ∀ seat, magenta (magenta seat) = seat := by decide
theorem magenta_ne : ∀ seat, magenta seat ≠ seat := by decide

/-- The antipodal frame-change used by Test 5. -/
def antipode (seat : Seat) : Seat := seat + 6

theorem antipode_twice : ∀ seat, antipode (antipode seat) = seat := by decide
theorem antipode_ne : ∀ seat, antipode seat ≠ seat := by decide

theorem antipode_is_not_magenta : antipode ≠ magenta := by
  intro h
  have bad := congrFun h (0 : Seat)
  exact (by decide : antipode (0 : Seat) ≠ magenta (0 : Seat)) bad

/-! ## The family of orientation-preserving clock transports -/

/-- Translation by an offset on the shared twelve-seat cyclic clock. -/
def rotation (offset seat : Seat) : Seat := seat + offset

def clockForward (seat : Seat) : Seat := seat + 1
def clockBack (seat : Seat) : Seat := seat + 11

/-- Every rotation respects the chosen forward orientation. -/
theorem rotation_preserves_forward : ∀ offset seat : Seat,
    rotation offset (clockForward seat) = clockForward (rotation offset seat) := by
  decide

/-- Transporting A to B and then B to A by the same rotation returns every seat. -/
def ReciprocalRotation (offset : Seat) : Prop :=
  ∀ seat, rotation offset (rotation offset seat) = seat

/-- The two coordinate frames do not identify any seat with itself. -/
def SeparateRotation (offset : Seat) : Prop :=
  ∀ seat, rotation offset seat ≠ seat

/-- Exact census: only the zero turn and the half-turn are reciprocal rotations. -/
theorem reciprocal_rotation_iff_double_zero (offset : Seat) :
    ReciprocalRotation offset ↔ offset + offset = 0 := by
  constructor
  · intro h
    simpa [ReciprocalRotation, rotation] using h (0 : Seat)
  · intro h seat
    unfold rotation
    rw [add_assoc, h, add_zero]

theorem reciprocal_rotation_classification : ∀ offset : Seat,
    ReciprocalRotation offset ↔ offset = 0 ∨ offset = 6 := by
  intro offset
  rw [reciprocal_rotation_iff_double_zero]
  fin_cases offset <;> decide

/-- Exact census: every nonzero clock rotation separates the two frames. -/
theorem separate_rotation_classification : ∀ offset : Seat,
    SeparateRotation offset ↔ offset ≠ 0 := by
  intro offset
  constructor
  · intro h hoffset
    subst hoffset
    exact h 0 (by decide)
  · intro hoffset seat hfixed
    apply hoffset
    have hsame : seat + offset = seat + 0 := by
      simpa [rotation] using hfixed
    exact add_left_cancel hsame

/-- The foundation-stone result: reciprocal, separated, oriented transport forces +6. -/
theorem unique_nontrivial_reciprocal_rotation (offset : Seat)
    (hreciprocal : ReciprocalRotation offset)
    (hseparate : SeparateRotation offset) : offset = 6 := by
  have hcases := (reciprocal_rotation_classification offset).mp hreciprocal
  have hnonzero := (separate_rotation_classification offset).mp hseparate
  rcases hcases with hzero | hsix
  · exact False.elim (hnonzero hzero)
  · exact hsix

/-- A candidate second-body alignment expressed inside the oriented rotation family. -/
structure OrientedAlignment where
  offset : Seat
  reciprocal : ReciprocalRotation offset
  separate : SeparateRotation offset

theorem OrientedAlignment.offset_is_six (alignment : OrientedAlignment) :
    alignment.offset = 6 :=
  unique_nontrivial_reciprocal_rotation alignment.offset
    alignment.reciprocal alignment.separate

/-- A local seat expressed in A's coordinates using a candidate alignment. -/
def inAFrameAt (alignment : OrientedAlignment) : Body → Seat → Seat
  | .A, seat => seat
  | .B, seat => rotation alignment.offset seat

/-- B's B1 = A's B7 is now a consequence of the alignment principles. -/
theorem earned_B_own_B1_is_A_B7 (alignment : OrientedAlignment) :
    inAFrameAt alignment .B (1 : Seat) = (7 : Seat) := by
  unfold inAFrameAt
  rw [alignment.offset_is_six]
  decide

/-- The actual antipodal alignment inhabits the specification. -/
def antipodalAlignment : OrientedAlignment where
  offset := 6
  reciprocal := by
    simpa [ReciprocalRotation, rotation, antipode] using antipode_twice
  separate := by
    simpa [SeparateRotation, rotation, antipode] using antipode_ne

theorem earned_alignment_agrees_with_antipode :
    ∀ seat, inAFrameAt antipodalAlignment .B seat = antipode seat := by
  intro seat
  rfl

/-! ## Red control: two bodies alone do not determine +6 -/

/-- The weaker requirements do not mention the shared cyclic orientation. -/
def WeakReciprocalSeparation (f : Seat → Seat) : Prop :=
  (∀ seat, f (f seat) = seat) ∧ (∀ seat, f seat ≠ seat)

theorem antipode_is_a_weak_alignment : WeakReciprocalSeparation antipode :=
  ⟨antipode_twice, antipode_ne⟩

theorem magenta_is_a_weak_alignment : WeakReciprocalSeparation magenta :=
  ⟨magenta_twice, magenta_ne⟩

/-- Red control: the weak principles admit at least two different transports. -/
theorem weak_alignment_is_not_unique :
    ∃ f g : Seat → Seat,
      WeakReciprocalSeparation f ∧ WeakReciprocalSeparation g ∧ f ≠ g := by
  exact ⟨antipode, magenta, antipode_is_a_weak_alignment,
    magenta_is_a_weak_alignment, antipode_is_not_magenta⟩

/-- Magenta reverses, rather than preserves, the chosen one-seat direction. -/
theorem magenta_reverses_forward : ∀ seat,
    magenta (clockForward seat) = clockBack (magenta seat) := by
  decide

/-- A concrete witness that magenta fails oriented forward equivariance. -/
theorem magenta_does_not_preserve_forward :
    ¬ ∀ seat, magenta (clockForward seat) = clockForward (magenta seat) := by
  intro h
  exact (by decide :
    magenta (clockForward (0 : Seat)) ≠ clockForward (magenta (0 : Seat))) (h 0)

/-! ## Certificate -/

theorem foundation_stone_test_six :
    (∀ offset seat : Seat,
      rotation offset (clockForward seat) = clockForward (rotation offset seat)) ∧
    (∀ offset : Seat,
      ReciprocalRotation offset ↔ offset = 0 ∨ offset = 6) ∧
    (∀ offset : Seat,
      SeparateRotation offset ↔ offset ≠ 0) ∧
    (∀ offset : Seat,
      ReciprocalRotation offset → SeparateRotation offset → offset = 6) ∧
    (∀ alignment : OrientedAlignment,
      inAFrameAt alignment .B (1 : Seat) = (7 : Seat)) ∧
    (∃ f g : Seat → Seat,
      WeakReciprocalSeparation f ∧ WeakReciprocalSeparation g ∧ f ≠ g) ∧
    (∀ seat, magenta (clockForward seat) = clockBack (magenta seat)) ∧
    (¬ ∀ seat, magenta (clockForward seat) = clockForward (magenta seat)) :=
  ⟨rotation_preserves_forward,
   reciprocal_rotation_classification,
   separate_rotation_classification,
   unique_nontrivial_reciprocal_rotation,
   earned_B_own_B1_is_A_B7,
   weak_alignment_is_not_unique,
   magenta_reverses_forward,
   magenta_does_not_preserve_forward⟩

#print axioms rotation_preserves_forward
#print axioms reciprocal_rotation_classification
#print axioms separate_rotation_classification
#print axioms unique_nontrivial_reciprocal_rotation
#print axioms OrientedAlignment.offset_is_six
#print axioms earned_B_own_B1_is_A_B7
#print axioms earned_alignment_agrees_with_antipode
#print axioms antipode_is_a_weak_alignment
#print axioms magenta_is_a_weak_alignment
#print axioms weak_alignment_is_not_unique
#print axioms magenta_reverses_forward
#print axioms magenta_does_not_preserve_forward
#print axioms foundation_stone_test_six

end FoundationStoneTestSix
