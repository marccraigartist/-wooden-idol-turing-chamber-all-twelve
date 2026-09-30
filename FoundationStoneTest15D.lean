import Mathlib

/-!
# THE ASYMMETRY SEAM — TEST 15D

Test 15C found one equal-length point and one order-sensitive point.  Test 15D
maps the whole space.

Let `A = 4 Ry(30°)Rz(30°)` and `B = 4 Rz(30°)Ry(30°)`.  The factor 4 keeps all
matrix entries in `ℚ(√3)` and multiplies both squared chord lengths equally.

Lean proves the exact global formula

  chord²(B,v) - chord²(A,v) = 16 (2 - √3) x (y + z).

Because `2 - √3` is positive, the geometry divides into three regions:

* the seam `x = 0` or `y + z = 0`, where the two chord lengths agree;
* `x(y+z) > 0`, where order B travels farther from the start;
* `x(y+z) < 0`, where order A travels farther from the start.

The seam is the union of two planes through the origin (hence two great circles
on any centred sphere).  The x-axis point lies on the seam but its two endpoints
are still different: equal length is not equal motion.  The +15° half-seat
direction lies on the B-longer side; its reflected direction lies on the
A-longer side.  Antipodal points remain on the same side, so this scalar
asymmetry does not by itself create handedness.

This is a classification of one-step chord asymmetry for the stated frame.  It
does not yet identify total two-leg arc length, and the mapping from the abstract
15° direction to a particular Dead Globe renderer remains a separate frame
check.
-/

namespace FoundationStoneTestFifteenD

noncomputable section

structure R3 where
  x : ℝ
  y : ℝ
  z : ℝ

@[ext] theorem R3.ext (u v : R3)
    (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  cases u
  cases v
  simp_all

def sqrt3 : ℝ := Real.sqrt 3

/-- `4 Ry(30°)Rz(30°)`. -/
def A (v : R3) : R3 :=
  ⟨3 * v.x - sqrt3 * v.y + 2 * v.z,
   2 * v.x + 2 * sqrt3 * v.y,
   -sqrt3 * v.x + v.y + 2 * sqrt3 * v.z⟩

/-- `4 Rz(30°)Ry(30°)`. -/
def B (v : R3) : R3 :=
  ⟨3 * v.x - 2 * v.y + sqrt3 * v.z,
   sqrt3 * v.x + 2 * sqrt3 * v.y + v.z,
   -2 * v.x + 2 * sqrt3 * v.z⟩

def scale (k : ℝ) (v : R3) : R3 := ⟨k * v.x, k * v.y, k * v.z⟩
def sub (u v : R3) : R3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
def neg (v : R3) : R3 := ⟨-v.x, -v.y, -v.z⟩

def normSq (v : R3) : ℝ := v.x^2 + v.y^2 + v.z^2

/-- Sixteen times the actual squared chord length. -/
def chordSqScaled (F : R3 → R3) (v : R3) : ℝ :=
  normSq (sub (F v) (scale 4 v))

theorem sqrt3_sq : sqrt3 ^ 2 = 3 := by
  unfold sqrt3
  exact Real.sq_sqrt (by norm_num)

theorem sqrt3_lt_two : sqrt3 < 2 := by
  have hs := sqrt3_sq
  have hn : 0 ≤ sqrt3 := Real.sqrt_nonneg 3
  nlinarith

theorem two_minus_sqrt3_pos : 0 < 2 - sqrt3 := by
  linarith [sqrt3_lt_two]

/-! ## The maps really are equally scaled rotations -/

theorem A_preserves_norm_scaled (v : R3) : normSq (A v) = 16 * normSq v := by
  unfold normSq A
  dsimp only
  linear_combination
    (v.x^2 + 5 * v.y^2 + 4 * v.z^2 - 4 * v.x * v.z) * sqrt3_sq

theorem B_preserves_norm_scaled (v : R3) : normSq (B v) = 16 * normSq v := by
  unfold normSq B
  dsimp only
  linear_combination
    (v.x^2 + 4 * v.y^2 + 5 * v.z^2 + 4 * v.x * v.y) * sqrt3_sq

/-! ## The global seam equation -/

def seamValue (v : R3) : ℝ := v.x * (v.y + v.z)

theorem chord_difference_formula (v : R3) :
    chordSqScaled B v - chordSqScaled A v =
      16 * (2 - sqrt3) * seamValue v := by
  unfold chordSqScaled normSq sub scale A B seamValue
  dsimp only
  linear_combination
    (-v.y^2 + v.z^2 + 4 * v.x * v.y + 4 * v.x * v.z) * sqrt3_sq

/-- Exactly the two planes `x=0` and `y+z=0`. -/
theorem equal_chords_iff_on_seam (v : R3) :
    chordSqScaled A v = chordSqScaled B v ↔
      v.x = 0 ∨ v.y + v.z = 0 := by
  rw [eq_comm]
  have hd := chord_difference_formula v
  have hp := two_minus_sqrt3_pos
  constructor
  · intro heq
    have hprod : 16 * (2 - sqrt3) * seamValue v = 0 := by
      nlinarith
    have hc : 16 * (2 - sqrt3) ≠ 0 :=
      mul_ne_zero (by norm_num) (ne_of_gt hp)
    have hz : seamValue v = 0 := (mul_eq_zero.mp hprod).resolve_left hc
    exact mul_eq_zero.mp hz
  · intro h
    have hz : seamValue v = 0 := by
      unfold seamValue
      rcases h with hx | hy
      · simp [hx]
      · simp [hy]
    nlinarith

theorem B_longer_iff_positive_side (v : R3) :
    chordSqScaled A v < chordSqScaled B v ↔ 0 < seamValue v := by
  have hd := chord_difference_formula v
  have hp := two_minus_sqrt3_pos
  have hc : 0 < 16 * (2 - sqrt3) := mul_pos (by norm_num) hp
  constructor
  · intro h
    have hprod : 0 < 16 * (2 - sqrt3) * seamValue v := by nlinarith
    rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · exact hpos.2
    · exfalso
      linarith [hc, hneg.1]
  · intro h
    have hprod : 0 < 16 * (2 - sqrt3) * seamValue v := mul_pos hc h
    nlinarith

theorem A_longer_iff_negative_side (v : R3) :
    chordSqScaled B v < chordSqScaled A v ↔ seamValue v < 0 := by
  have hd := chord_difference_formula v
  have hp := two_minus_sqrt3_pos
  have hc : 0 < 16 * (2 - sqrt3) := mul_pos (by norm_num) hp
  constructor
  · intro h
    have hprod : 16 * (2 - sqrt3) * seamValue v < 0 := by nlinarith
    rcases (mul_neg_iff.mp hprod) with hsign | hsign
    · exact hsign.2
    · exfalso
      linarith [hc, hsign.1]
  · intro h
    have hprod : 16 * (2 - sqrt3) * seamValue v < 0 := mul_neg_of_pos_of_neg hc h
    nlinarith

/-! ## Controls and named points -/

def xPoint : R3 := ⟨1, 0, 0⟩
def yPoint : R3 := ⟨0, 1, 0⟩
def zPoint : R3 := ⟨0, 0, 1⟩
def fifteenPoint : R3 := ⟨1, 0, 2 - sqrt3⟩
def reflectedFifteenPoint : R3 := ⟨1, 0, sqrt3 - 2⟩

theorem all_coordinate_axes_lie_on_seam :
    (chordSqScaled A xPoint = chordSqScaled B xPoint) ∧
    (chordSqScaled A yPoint = chordSqScaled B yPoint) ∧
    (chordSqScaled A zPoint = chordSqScaled B zPoint) := by
  constructor
  · exact (equal_chords_iff_on_seam xPoint).2 (Or.inr (by norm_num [xPoint]))
  constructor
  · exact (equal_chords_iff_on_seam yPoint).2 (Or.inl (by norm_num [yPoint]))
  · exact (equal_chords_iff_on_seam zPoint).2 (Or.inl (by norm_num [zPoint]))

/-- RED CONTROL: the x point has equal lengths but unequal destinations. -/
theorem seam_does_not_mean_same_motion :
    chordSqScaled A xPoint = chordSqScaled B xPoint ∧ A xPoint ≠ B xPoint := by
  constructor
  · exact all_coordinate_axes_lie_on_seam.1
  · intro h
    have hy := congrArg R3.y h
    unfold A B xPoint at hy
    dsimp only at hy
    have hn : 0 ≤ sqrt3 := Real.sqrt_nonneg 3
    have hs := sqrt3_sq
    nlinarith

theorem fifteen_is_on_B_longer_side :
    chordSqScaled A fifteenPoint < chordSqScaled B fifteenPoint := by
  rw [B_longer_iff_positive_side]
  unfold seamValue fifteenPoint
  dsimp only
  simpa using two_minus_sqrt3_pos

theorem reflected_fifteen_is_on_A_longer_side :
    chordSqScaled B reflectedFifteenPoint <
      chordSqScaled A reflectedFifteenPoint := by
  rw [A_longer_iff_negative_side]
  unfold seamValue reflectedFifteenPoint
  dsimp only
  linarith [two_minus_sqrt3_pos]

/-! ## Symmetry of the classification -/

theorem antipode_keeps_side (v : R3) : seamValue (neg v) = seamValue v := by
  unfold seamValue neg
  dsimp only
  ring

theorem scale_changes_seam_quadratically (k : ℝ) (v : R3) :
    seamValue (scale k v) = k^2 * seamValue v := by
  unfold seamValue scale
  dsimp only
  ring

theorem swap_yz_keeps_side (v : R3) :
    seamValue ⟨v.x, v.z, v.y⟩ = seamValue v := by
  unfold seamValue
  dsimp only
  ring

/-! ## Certificate -/

theorem asymmetry_seam_test_15D_certificate :
    (∀ v, chordSqScaled B v - chordSqScaled A v =
      16 * (2 - sqrt3) * seamValue v) ∧
    (∀ v, chordSqScaled A v = chordSqScaled B v ↔
      v.x = 0 ∨ v.y + v.z = 0) ∧
    (∀ v, chordSqScaled A v < chordSqScaled B v ↔ 0 < seamValue v) ∧
    (∀ v, chordSqScaled B v < chordSqScaled A v ↔ seamValue v < 0) ∧
    (chordSqScaled A xPoint = chordSqScaled B xPoint ∧ A xPoint ≠ B xPoint) ∧
    chordSqScaled A fifteenPoint < chordSqScaled B fifteenPoint ∧
    chordSqScaled B reflectedFifteenPoint <
      chordSqScaled A reflectedFifteenPoint ∧
    (∀ v, seamValue (neg v) = seamValue v) :=
  ⟨chord_difference_formula,
   equal_chords_iff_on_seam,
   B_longer_iff_positive_side,
   A_longer_iff_negative_side,
   seam_does_not_mean_same_motion,
   fifteen_is_on_B_longer_side,
   reflected_fifteen_is_on_A_longer_side,
   antipode_keeps_side⟩

#print axioms A_preserves_norm_scaled
#print axioms B_preserves_norm_scaled
#print axioms chord_difference_formula
#print axioms equal_chords_iff_on_seam
#print axioms B_longer_iff_positive_side
#print axioms A_longer_iff_negative_side
#print axioms all_coordinate_axes_lie_on_seam
#print axioms seam_does_not_mean_same_motion
#print axioms fifteen_is_on_B_longer_side
#print axioms reflected_fifteen_is_on_A_longer_side
#print axioms antipode_keeps_side
#print axioms scale_changes_seam_quadratically
#print axioms swap_yz_keeps_side
#print axioms asymmetry_seam_test_15D_certificate

end

end FoundationStoneTestFifteenD
