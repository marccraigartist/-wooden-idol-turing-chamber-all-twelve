import Mathlib

/-!
# THE NATIVE RETURN OBSTRUCTION — TEST 15B

Test 15A proved an abstract pattern: a visible cycle may close while hidden
information accumulates.  Its red control showed that an arbitrary counter can
manufacture that pattern.  Test 15B therefore removes the counter completely.

The state here is only an exact three-dimensional point.  Its coordinates lie
in `ℤ[√3]`, represented by pairs `(a,b)` for `a + b√3`.  The two primitive maps
are the exact scaled 30° rotations `2 Rz(30°)` and `2 Ry(30°)`.  Their
composition is therefore `4 Ry(30°)Rz(30°)`; the factor `4` is forced by the two
half-angle denominators, not stored as an extra state field.

Lean tests the following.

1. The combined matrix is derived by composing the two primitive rotations.
2. Order genuinely matters: `Ry·Rz` and `Rz·Ry` send the x-axis point to
   different exact points, although both have squared norm `16` and x-dot
   numerator `3` (the same one-step angular displacement, cosine `3/4`).
3. A parity residue computed directly from the geometric coordinates is
   preserved and forces the first coordinate after every positive step to be
   odd.  A returned point would instead be multiplied by `4^n`, hence even.
4. Consequently the x-axis orbit never returns and never revisits a previous
   point.  No history counter or auxiliary height occurs in the state.
5. RED CONTROL: the corresponding 90° coordinate rotation really closes after
   three moves.  The obstruction does not declare every rotation non-closing.
6. INFORMATION WARNING: the parity residue is only a certificate of
   non-return.  Its Boolean shadow is constant along the orbit, so it is not a
   complete description of the motion and must not be called the helix itself.

This pays Test 15A's padding debt for this particular ordered 30° orbit.  It
does not yet prove that physical arc-length is the invariant, nor does it settle
the outstanding frame check against a specific Dead Globe renderer.
-/

namespace FoundationStoneTestFifteenB

/-! ## Exact arithmetic in ℤ[√3] -/

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

def vscale (k : Int) (v : V3) : V3 :=
  ⟨zscale k v.x, zscale k v.y, zscale k v.z⟩

/-! ## The two primitive 30° rotations and their two orders -/

/-- `2 Rz(30°)`: `(x,y,z) ↦ (√3x-y, x+√3y, 2z)`. -/
def rz2 (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.y,
   zadd v.x (zroot v.y),
   zscale 2 v.z⟩

/-- `2 Ry(30°)`: `(x,y,z) ↦ (√3x+z, 2y, -x+√3z)`. -/
def ry2 (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.z,
   zscale 2 v.y,
   zadd (zneg v.x) (zroot v.z)⟩

/-- First z, then y: exactly `4 Ry(30°)Rz(30°)`. -/
def stepYZ (v : V3) : V3 := ry2 (rz2 v)

/-- First y, then z: exactly `4 Rz(30°)Ry(30°)`. -/
def stepZY (v : V3) : V3 := rz2 (ry2 v)

/-- The matrix printed in the Dead Globe bucket is not assumed separately: it
unfolds from the two primitive rotations. -/
theorem stepYZ_matrix (v : V3) :
    stepYZ v =
      ⟨⟨3 * v.x.a - 3 * v.y.b + 2 * v.z.a,
         3 * v.x.b - v.y.a + 2 * v.z.b⟩,
       ⟨2 * v.x.a + 6 * v.y.b,
         2 * v.x.b + 2 * v.y.a⟩,
       ⟨-3 * v.x.b + v.y.a + 6 * v.z.b,
         -v.x.a + v.y.b + 2 * v.z.a⟩⟩ := by
  apply V3.ext <;> apply Z3.ext <;>
    simp [stepYZ, ry2, rz2, zadd, zsub, zneg, zscale, zroot] <;> ring

def xPoint : V3 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

theorem two_orders_are_distinct : stepYZ xPoint ≠ stepZY xPoint := by
  decide

theorem stepYZ_xPoint_exact :
    stepYZ xPoint = ⟨⟨3, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩⟩ := by
  decide

theorem stepZY_xPoint_exact :
    stepZY xPoint = ⟨⟨3, 0⟩, ⟨0, 1⟩, ⟨-2, 0⟩⟩ := by
  decide

/-! ## Exact one-step metric checks -/

def zdot (u v : V3) : Z3 :=
  zadd (zadd (zmul u.x v.x) (zmul u.y v.y)) (zmul u.z v.z)

def normSq (v : V3) : Z3 := zdot v v

/-- Both orders move the x-axis point through the same angle: in the scaled
coordinates the new norm is `4` and the dot product is `3`, hence cosine `3/4`.
The endpoints nevertheless differ. -/
theorem same_metric_different_endpoint :
    normSq (stepYZ xPoint) = ⟨16, 0⟩ ∧
    normSq (stepZY xPoint) = ⟨16, 0⟩ ∧
    zdot xPoint (stepYZ xPoint) = ⟨3, 0⟩ ∧
    zdot xPoint (stepZY xPoint) = ⟨3, 0⟩ ∧
    stepYZ xPoint ≠ stepZY xPoint := by
  decide

/-! ## Iteration and the coordinate-derived obstruction -/

def iter (F : V3 → V3) : Nat → V3 → V3
  | 0, v => v
  | n + 1, v => F (iter F n v)

def pow4 : Nat → Int
  | 0 => 1
  | n + 1 => 4 * pow4 n

def ReturnsAfter (n : Nat) (v : V3) : Prop :=
  iter stepYZ n v = vscale (pow4 n) v

def SamePlace (m n : Nat) (v : V3) : Prop :=
  vscale (pow4 n) (iter stepYZ m v) =
    vscale (pow4 m) (iter stepYZ n v)

/-- This residue is read from the geometric coordinates themselves.  There is
no counter field. -/
def GeometricOdd (v : V3) : Prop :=
  (v.x.a + v.x.b + v.y.a + v.y.b) % 2 = 1

theorem step_keeps_geometric_odd (v : V3) (h : GeometricOdd v) :
    GeometricOdd (stepYZ v) := by
  rw [stepYZ_matrix]
  unfold GeometricOdd at *
  simp only
  omega

theorem step_makes_first_coordinate_odd (v : V3) (h : GeometricOdd v) :
    ((stepYZ v).x.a + (stepYZ v).x.b) % 2 = 1 := by
  rw [stepYZ_matrix]
  unfold GeometricOdd at h
  simp only
  omega

theorem iter_keeps_geometric_odd (v : V3) (h : GeometricOdd v) :
    ∀ n, GeometricOdd (iter stepYZ n v) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact step_keeps_geometric_odd _ ih

theorem first_coordinate_odd_after_positive_step
    (v : V3) (h : GeometricOdd v) (n : Nat) :
    ((iter stepYZ (n + 1) v).x.a +
      (iter stepYZ (n + 1) v).x.b) % 2 = 1 :=
  step_makes_first_coordinate_odd _ (iter_keeps_geometric_odd v h n)

theorem pow4_even (n : Nat) : pow4 (n + 1) % 2 = 0 := by
  show (4 * pow4 n) % 2 = 0
  omega

theorem pow4_pos : ∀ n, 0 < pow4 n
  | 0 => by decide
  | n + 1 => by
      show 0 < 4 * pow4 n
      have := pow4_pos n
      omega

theorem pow4_add (m j : Nat) : pow4 (m + j) = pow4 m * pow4 j := by
  induction m with
  | zero => simp [pow4]
  | succ m ih =>
      rw [Nat.succ_add]
      show 4 * pow4 (m + j) = 4 * pow4 m * pow4 j
      rw [ih, Int.mul_assoc]

/-- Native non-return: odd geometry cannot equal its positive `4^n` scaling. -/
theorem geometric_odd_never_returns
    (v : V3) (h : GeometricOdd v) (n : Nat) (hn : 0 < n) :
    ¬ ReturnsAfter n v := by
  intro hr
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hodd := first_coordinate_odd_after_positive_step v h k
  have hxa := congrArg (fun w => w.x.a) hr
  have hxb := congrArg (fun w => w.x.b) hr
  simp only [vscale, zscale] at hxa hxb
  rw [hxa, hxb] at hodd
  have he := pow4_even k
  rw [← Int.mul_add, Int.mul_emod, he] at hodd
  simp at hodd

/-- Native non-revisit: cancellation uses the positive forced scale `4^m`. -/
theorem geometric_odd_never_revisits
    (v : V3) (h : GeometricOdd v) (m n : Nat) (hmn : m < n) :
    ¬ SamePlace m n v := by
  intro hs
  obtain ⟨j, rfl⟩ : ∃ j, n = m + (j + 1) := ⟨n - m - 1, by omega⟩
  have hxa := congrArg (fun w => w.x.a) hs
  have hxb := congrArg (fun w => w.x.b) hs
  simp only [vscale, zscale] at hxa hxb
  rw [pow4_add, Int.mul_assoc] at hxa hxb
  have hp : pow4 m ≠ 0 := Int.ne_of_gt (pow4_pos m)
  have ha := Int.eq_of_mul_eq_mul_left hp hxa
  have hb := Int.eq_of_mul_eq_mul_left hp hxb
  have hodd := first_coordinate_odd_after_positive_step v h (m + j)
  rw [show m + j + 1 = m + (j + 1) from by omega] at hodd
  rw [← ha, ← hb, ← Int.mul_add] at hodd
  have he := pow4_even j
  rw [Int.mul_emod, he] at hodd
  simp at hodd

theorem xPoint_is_geometric_odd : GeometricOdd xPoint := by
  unfold GeometricOdd xPoint
  decide

theorem xPoint_never_returns (n : Nat) (hn : 0 < n) :
    ¬ ReturnsAfter n xPoint :=
  geometric_odd_never_returns xPoint xPoint_is_geometric_odd n hn

theorem xPoint_never_revisits (m n : Nat) (hmn : m < n) :
    ¬ SamePlace m n xPoint :=
  geometric_odd_never_revisits xPoint xPoint_is_geometric_odd m n hmn

/-! ## Information warning: the certificate is not the motion -/

def parityShadow (v : V3) : Bool :=
  (v.x.a + v.x.b + v.y.a + v.y.b) % 2 == 1

theorem parity_shadow_stays_true (n : Nat) :
    parityShadow (iter stepYZ n xPoint) = true := by
  have h := iter_keeps_geometric_odd xPoint xPoint_is_geometric_odd n
  unfold GeometricOdd at h
  simpa [parityShadow] using h

theorem parity_shadow_forgets_distinct_geometry :
    parityShadow xPoint = parityShadow (stepYZ xPoint) ∧
    xPoint ≠ stepYZ xPoint := by
  constructor <;> decide

/-! ## RED CONTROL: a closing rotation -/

def step90 (v : V3) : V3 := ⟨v.z, v.x, v.y⟩

theorem ninety_degree_control_closes :
    ∀ v : V3, step90 (step90 (step90 v)) = v :=
  fun _ => rfl

/-! ## Certificate -/

theorem native_return_obstruction_test_15B_certificate :
    (∀ v, stepYZ v = ry2 (rz2 v)) ∧
    stepYZ xPoint ≠ stepZY xPoint ∧
    normSq (stepYZ xPoint) = ⟨16, 0⟩ ∧
    normSq (stepZY xPoint) = ⟨16, 0⟩ ∧
    (∀ n, 0 < n → ¬ ReturnsAfter n xPoint) ∧
    (∀ m n, m < n → ¬ SamePlace m n xPoint) ∧
    (∀ n, parityShadow (iter stepYZ n xPoint) = true) ∧
    (∀ v, step90 (step90 (step90 v)) = v) :=
  ⟨fun _ => rfl,
   two_orders_are_distinct,
   same_metric_different_endpoint.1,
   same_metric_different_endpoint.2.1,
   xPoint_never_returns,
   xPoint_never_revisits,
   parity_shadow_stays_true,
   ninety_degree_control_closes⟩

#print axioms stepYZ_matrix
#print axioms two_orders_are_distinct
#print axioms same_metric_different_endpoint
#print axioms step_keeps_geometric_odd
#print axioms step_makes_first_coordinate_odd
#print axioms geometric_odd_never_returns
#print axioms geometric_odd_never_revisits
#print axioms xPoint_never_returns
#print axioms xPoint_never_revisits
#print axioms parity_shadow_stays_true
#print axioms parity_shadow_forgets_distinct_geometry
#print axioms ninety_degree_control_closes
#print axioms native_return_obstruction_test_15B_certificate

end FoundationStoneTestFifteenB
