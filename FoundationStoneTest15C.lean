import Mathlib

/-!
# PATH AND HOLONOMY — TEST 15C

Test 15B established an intrinsic coordinate obstruction for the ordered pair
of 30° rotations.  Test 15C asks three stricter questions.

1. Do different endpoints necessarily mean different travelled distances?
2. Does the 15° half-seat direction distinguish the two orders metrically?
3. Does a closed word in the rotations and their inverses leave an orientation
   residue — a genuine non-trivial holonomy?

Everything is exact.  `Z3` represents `a + b√3`; no floating-point angle or
length enters the proof.  Each primitive map is twice a 30° rotation, so a
two-rotation word is scaled by 4 and the four-word commutator by 256.

Lean is asked to establish:

* RED CONTROL: at the x-axis point, the two orders have different endpoints but
  exactly equal one-step chord length.  Endpoint asymmetry alone is therefore
  not length asymmetry.
* At the direction `(1,0,2-√3)`, corresponding to 15° above the x-axis in the
  xz-plane, the two orders have unequal exact chord lengths; `Rz·Ry` is longer.
* The scaled inverse words really undo the forward words.
* The commutator `A B A⁻¹ B⁻¹` does not return the x-axis point, even after the
  forced scale factor is accounted for.  This is an exact holonomy residue.
* A commuting abstract pair has trivial commutator.  Non-commutation, not the
  notation “loop”, is doing the work.

The path comparison is chord length between start and finish, not total arc
length along the two primitive legs.  The half-seat point also retains the
outstanding renderer-frame caveat from the Dead Globe work.
-/

namespace FoundationStoneTestFifteenC

structure Z3 where
  a : Int
  b : Int
deriving DecidableEq

@[ext] theorem Z3.ext (u v : Z3) (ha : u.a = v.a) (hb : u.b = v.b) : u = v := by
  cases u
  cases v
  simp_all

def zadd (u v : Z3) : Z3 := ⟨u.a + v.a, u.b + v.b⟩
def zneg (u : Z3) : Z3 := ⟨-u.a, -u.b⟩
def zsub (u v : Z3) : Z3 := zadd u (zneg v)
def zscale (k : Int) (u : Z3) : Z3 := ⟨k * u.a, k * u.b⟩
def zroot (u : Z3) : Z3 := ⟨3 * u.b, u.a⟩
def zmul (u v : Z3) : Z3 :=
  ⟨u.a * v.a + 3 * u.b * v.b, u.a * v.b + u.b * v.a⟩

structure V3 where
  x : Z3
  y : Z3
  z : Z3
deriving DecidableEq

@[ext] theorem V3.ext (u v : V3)
    (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  cases u
  cases v
  simp_all

def vsub (u v : V3) : V3 :=
  ⟨zsub u.x v.x, zsub u.y v.y, zsub u.z v.z⟩

def vscale (k : Int) (v : V3) : V3 :=
  ⟨zscale k v.x, zscale k v.y, zscale k v.z⟩

def zdot (u v : V3) : Z3 :=
  zadd (zadd (zmul u.x v.x) (zmul u.y v.y)) (zmul u.z v.z)

def normSq (v : V3) : Z3 := zdot v v

/-! ## Positive and negative primitive rotations -/

/-- `2 Rz(+30°)`. -/
def rzP (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.y,
   zadd v.x (zroot v.y),
   zscale 2 v.z⟩

/-- `2 Ry(+30°)`. -/
def ryP (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.z,
   zscale 2 v.y,
   zadd (zneg v.x) (zroot v.z)⟩

/-- `2 Rz(-30°)`. -/
def rzN (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.y,
   zadd (zneg v.x) (zroot v.y),
   zscale 2 v.z⟩

/-- `2 Ry(-30°)`. -/
def ryN (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.z,
   zscale 2 v.y,
   zadd v.x (zroot v.z)⟩

/-- `A = 4 Ry Rz`. -/
def A (v : V3) : V3 := ryP (rzP v)

/-- `B = 4 Rz Ry`. -/
def B (v : V3) : V3 := rzP (ryP v)

/-- `4 A⁻¹ = 4 Rz⁻¹ Ry⁻¹`. -/
def Ainv (v : V3) : V3 := rzN (ryN v)

/-- `4 B⁻¹ = 4 Ry⁻¹ Rz⁻¹`. -/
def Binv (v : V3) : V3 := ryN (rzN v)

/-- The inverse words undo their partners, with the unavoidable scale `16`. -/
theorem A_inverse_exact (v : V3) : A (Ainv v) = vscale 16 v := by
  apply V3.ext <;> apply Z3.ext <;>
    simp [A, Ainv, ryP, rzP, ryN, rzN, vscale,
      zadd, zsub, zneg, zscale, zroot] <;> ring

theorem B_inverse_exact (v : V3) : B (Binv v) = vscale 16 v := by
  apply V3.ext <;> apply Z3.ext <;>
    simp [B, Binv, ryP, rzP, ryN, rzN, vscale,
      zadd, zsub, zneg, zscale, zroot] <;> ring

/-! ## Chord-length comparison -/

/-- Sixteen times the actual squared chord length, because `F v` is scaled by 4. -/
def chordSqScaled (F : V3 → V3) (v : V3) : Z3 :=
  normSq (vsub (F v) (vscale 4 v))

def xPoint : V3 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

/-- Direction 15° above x in the xz-plane: `tan 15° = 2 - √3`. -/
def fifteenPoint : V3 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨2, -1⟩⟩

theorem x_endpoints_differ : A xPoint ≠ B xPoint := by decide

/-- RED CONTROL: different destinations, equal chord length. -/
theorem x_chords_are_equal :
    chordSqScaled A xPoint = ⟨8, 0⟩ ∧
    chordSqScaled B xPoint = ⟨8, 0⟩ := by
  decide

/-- At the half-seat direction, the squared chords are exact but unequal. -/
theorem fifteen_chords_exact :
    chordSqScaled A fifteenPoint = ⟨368, -208⟩ ∧
    chordSqScaled B fifteenPoint = ⟨480, -272⟩ := by
  decide

theorem fifteen_chords_are_unequal :
    chordSqScaled A fifteenPoint ≠ chordSqScaled B fifteenPoint := by
  rw [fifteen_chords_exact.1, fifteen_chords_exact.2]
  decide

/-! Interpret `a+b√3` as a real number only for the direction of the inequality. -/

noncomputable def zreal (u : Z3) : ℝ := u.a + u.b * Real.sqrt 3

theorem sqrt_three_lt_seven_fourths : Real.sqrt 3 < (7 : ℝ) / 4 := by
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith

/-- `B` has the longer one-step chord at the 15° direction. -/
theorem fifteen_B_chord_is_longer :
    zreal (chordSqScaled A fifteenPoint) <
      zreal (chordSqScaled B fifteenPoint) := by
  rw [fifteen_chords_exact.1, fifteen_chords_exact.2]
  unfold zreal
  dsimp only
  have h := sqrt_three_lt_seven_fourths
  norm_num at h ⊢
  linarith

/-! ## Exact holonomy -/

/-- Scaled commutator `A B A⁻¹ B⁻¹`; four words contribute scale `4⁴=256`. -/
def holonomy (v : V3) : V3 := A (B (Ainv (Binv v)))

theorem holonomy_x_exact :
    holonomy xPoint =
      ⟨⟨4, 144⟩, ⟨24, 0⟩, ⟨48, -12⟩⟩ := by
  decide

theorem holonomy_x_is_nontrivial :
    holonomy xPoint ≠ vscale 256 xPoint := by
  rw [holonomy_x_exact]
  decide

theorem holonomy_displacement_is_nonzero :
    normSq (vsub (holonomy xPoint) (vscale 256 xPoint)) =
      ⟨129024, -73728⟩ := by
  decide

/-! ## RED CONTROL: commuting elements have no commutator residue -/

theorem commuting_commutator_is_trivial {G : Type} [Group G]
    (a b : G) (h : a * b = b * a) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  calc
    a * b * a⁻¹ * b⁻¹ = b * a * a⁻¹ * b⁻¹ := by rw [h]
    _ = 1 := by simp

/-! ## Certificate -/

theorem path_and_holonomy_test_15C_certificate :
    (∀ v, A (Ainv v) = vscale 16 v) ∧
    (∀ v, B (Binv v) = vscale 16 v) ∧
    A xPoint ≠ B xPoint ∧
    chordSqScaled A xPoint = chordSqScaled B xPoint ∧
    chordSqScaled A fifteenPoint ≠ chordSqScaled B fifteenPoint ∧
    zreal (chordSqScaled A fifteenPoint) <
      zreal (chordSqScaled B fifteenPoint) ∧
    holonomy xPoint ≠ vscale 256 xPoint :=
  ⟨A_inverse_exact,
   B_inverse_exact,
   x_endpoints_differ,
   x_chords_are_equal.1.trans x_chords_are_equal.2.symm,
   fifteen_chords_are_unequal,
   fifteen_B_chord_is_longer,
   holonomy_x_is_nontrivial⟩

#print axioms A_inverse_exact
#print axioms B_inverse_exact
#print axioms x_endpoints_differ
#print axioms x_chords_are_equal
#print axioms fifteen_chords_exact
#print axioms fifteen_chords_are_unequal
#print axioms sqrt_three_lt_seven_fourths
#print axioms fifteen_B_chord_is_longer
#print axioms holonomy_x_exact
#print axioms holonomy_x_is_nontrivial
#print axioms holonomy_displacement_is_nonzero
#print axioms commuting_commutator_is_trivial
#print axioms path_and_holonomy_test_15C_certificate

end FoundationStoneTestFifteenC
