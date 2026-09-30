/-!
# THE FOUNDATION STONE — TEST 15G: THE SIGNED BEND FIELD

Core Lean only; no imports.

Test 15Z found the first signed measurement: the oriented triple product
`det[start, midpoint, end]`.  It proved that this bend reverses on the old
unsigned turn seam and distinguished the two orders at the x-axis point.

This file maps that measurement globally.  It does not attach a counter or a
history label: the sign is computed from the actual three-point journey.

Results:
1. The two bend fields are explicit homogeneous cubics over ℤ[√3].
2. Their signed difference is an explicit cubic.  It is nonzero on both planes
   that were seams for the unsigned chord field: y+z=0 and x=0.  The old hinge
   planes therefore do not survive as signed seams.
3. On y+z=0 the bends are exact opposites, not equals.  Squaring the bend makes
   that distinction disappear again: unsigned measurement forgets handedness.
4. The Y–Z bisector remains a genuine seam.  Along (0,t,t), both bends equal
   (8−4√3)t³.
5. At 15Y's endpoint-blind line the two routes have the same finish but opposite,
   nonzero bends.  The journey remains distinguishable after its endpoint agrees.

Scope: exact points in ℤ[√3]³.  The displayed identities are polynomial, but the
transfer to arbitrary real coordinates is not claimed by this file.
-/
namespace FoundationStoneFifteenG

structure Z3 where
  a : Int
  b : Int
deriving DecidableEq

structure V3 where
  x : Z3
  y : Z3
  z : Z3
deriving DecidableEq

def zzero : Z3 := ⟨0, 0⟩
def zone : Z3 := ⟨1, 0⟩
def zadd (u v : Z3) : Z3 := ⟨u.a + v.a, u.b + v.b⟩
def zneg (u : Z3) : Z3 := ⟨-u.a, -u.b⟩
def zsub (u v : Z3) : Z3 := zadd u (zneg v)
def zscale (k : Int) (u : Z3) : Z3 := ⟨k * u.a, k * u.b⟩
def zroot (u : Z3) : Z3 := ⟨3 * u.b, u.a⟩
def zmul (u v : Z3) : Z3 :=
  ⟨u.a * v.a + 3 * u.b * v.b, u.a * v.b + u.b * v.a⟩

def vneg (v : V3) : V3 := ⟨zneg v.x, zneg v.y, zneg v.z⟩

/-- Twice the positive 30° turns. -/
def rzP (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.y, zadd v.x (zroot v.y), zscale 2 v.z⟩
def ryP (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩

/-- A is Z-first; B is Y-first. -/
def A (v : V3) : V3 := ryP (rzP v)
def B (v : V3) : V3 := rzP (ryP v)

/-- Half-turn about the Y–Z bisector. -/
def exchange (v : V3) : V3 := ⟨zneg v.x, v.z, v.y⟩

/-- Triple product `u · (v × w)`. -/
def det3 (u v w : V3) : Z3 :=
  zadd (zadd (zmul u.x (zsub (zmul v.y w.z) (zmul v.z w.y)))
             (zmul u.y (zsub (zmul v.z w.x) (zmul v.x w.z))))
       (zmul u.z (zsub (zmul v.x w.y) (zmul v.y w.x)))

/-- Signed bend of each two-leg journey; scale 8. -/
def bendA (v : V3) : Z3 := det3 v (rzP v) (A v)
def bendB (v : V3) : Z3 := det3 v (ryP v) (B v)

/-- A compact cubic monomial `c·u·v·w`. -/
def c3 (c u v w : Z3) : Z3 := zmul c (zmul u (zmul v w))

/-- The complete Z-first cubic bend field. -/
def cubicA (v : V3) : Z3 :=
  zadd (c3 ⟨0, -1⟩ v.x v.x v.x)
  (zadd (c3 ⟨1, 0⟩ v.x v.x v.y)
  (zadd (c3 ⟨-7, 4⟩ v.x v.x v.z)
  (zadd (c3 ⟨0, -1⟩ v.x v.y v.y)
  (zadd (c3 ⟨10, -6⟩ v.x v.y v.z)
  (zadd (c3 ⟨-2, 0⟩ v.x v.z v.z)
  (zadd (c3 ⟨1, 0⟩ v.y v.y v.y)
  (zadd (c3 ⟨3, -2⟩ v.y v.y v.z)
        (c3 ⟨4, -2⟩ v.y v.z v.z))))))))

/-- The complete Y-first cubic bend field. -/
def cubicB (v : V3) : Z3 :=
  zadd (c3 ⟨0, 1⟩ v.x v.x v.x)
  (zadd (c3 ⟨-7, 4⟩ v.x v.x v.y)
  (zadd (c3 ⟨1, 0⟩ v.x v.x v.z)
  (zadd (c3 ⟨2, 0⟩ v.x v.y v.y)
  (zadd (c3 ⟨-10, 6⟩ v.x v.y v.z)
  (zadd (c3 ⟨0, 1⟩ v.x v.z v.z)
  (zadd (c3 ⟨4, -2⟩ v.y v.y v.z)
  (zadd (c3 ⟨3, -2⟩ v.y v.z v.z)
        (c3 ⟨1, 0⟩ v.z v.z v.z))))))))

/-- The explicit signed order field `bendA − bendB`. -/
def signedOrderField (v : V3) : Z3 :=
  zadd (c3 ⟨0, -2⟩ v.x v.x v.x)
  (zadd (c3 ⟨8, -4⟩ v.x v.x v.y)
  (zadd (c3 ⟨-8, 4⟩ v.x v.x v.z)
  (zadd (c3 ⟨-2, -1⟩ v.x v.y v.y)
  (zadd (c3 ⟨20, -12⟩ v.x v.y v.z)
  (zadd (c3 ⟨-2, -1⟩ v.x v.z v.z)
  (zadd (c3 ⟨1, 0⟩ v.y v.y v.y)
  (zadd (c3 ⟨-1, 0⟩ v.y v.y v.z)
  (zadd (c3 ⟨1, 0⟩ v.y v.z v.z)
        (c3 ⟨-1, 0⟩ v.z v.z v.z)))))))))

/-- 1a. Exact global formula for the Z-first bend. -/
theorem bendA_is_cubicA (v : V3) : bendA v = cubicA v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [bendA, det3, A, rzP, ryP, cubicA, c3,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

/-- 1b. Exact global formula for the Y-first bend. -/
theorem bendB_is_cubicB (v : V3) : bendB v = cubicB v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [bendB, det3, B, rzP, ryP, cubicB, c3,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

/-- 2. The signed difference is the displayed cubic field. -/
theorem bend_difference_is_the_signed_order_field (v : V3) :
    zsub (bendA v) (bendB v) = signedOrderField v := by
  rw [bendA_is_cubicA, bendB_is_cubicB]
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [cubicA, cubicB, signedOrderField, c3,
    zadd, zneg, zsub, zmul, Z3.mk.injEq]
  constructor <;> grind

/-! ## Transport and the signed turn seam -/

theorem bend_is_carried (v : V3) : bendB (exchange v) = bendA v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [bendA, bendB, det3, exchange, A, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem bendB_odd (v : V3) : bendB (vneg v) = zneg (bendB v) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [bendB, det3, vneg, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem exchange_is_antipode_on_turn_plane (v : V3) (h : zadd v.y v.z = zzero) :
    exchange v = vneg v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [exchange, vneg, zneg, zadd, zzero, V3.mk.injEq, Z3.mk.injEq,
    true_and] at h ⊢
  omega

/-- 3a. The old turn seam becomes an exact sign reversal. -/
theorem bends_are_opposite_on_the_turn_plane (v : V3)
    (h : zadd v.y v.z = zzero) : bendA v = zneg (bendB v) := by
  rw [← bend_is_carried v, exchange_is_antipode_on_turn_plane v h, bendB_odd]

/-- Squaring removes orientation. -/
def bendSqA (v : V3) : Z3 := zmul (bendA v) (bendA v)
def bendSqB (v : V3) : Z3 := zmul (bendB v) (bendB v)

/-- 3b. Once sign is forgotten, the whole old turn seam returns. -/
theorem unsigned_bend_forgets_the_turn_plane (v : V3)
    (h : zadd v.y v.z = zzero) : bendSqA v = bendSqB v := by
  unfold bendSqA bendSqB
  rw [bends_are_opposite_on_the_turn_plane v h]
  generalize bendB v = q
  obtain ⟨qa, qb⟩ := q
  simp only [zneg, zmul, Z3.mk.injEq]
  constructor <;> grind

/-! ## Witnesses: the old planes are not signed seams -/

def xPoint : V3 := ⟨zone, zzero, zzero⟩
def yPoint : V3 := ⟨zzero, zone, zzero⟩

/-- y+z=0, yet the bends are unequal nonzero opposites. -/
theorem old_turn_plane_is_not_a_signed_seam :
    zadd xPoint.y xPoint.z = zzero ∧
    bendA xPoint = ⟨0, -1⟩ ∧ bendB xPoint = ⟨0, 1⟩ := by decide

/-- x=0, yet the bends differ. -/
theorem old_chord_plane_is_not_a_signed_seam :
    yPoint.x = zzero ∧ bendA yPoint = ⟨1, 0⟩ ∧ bendB yPoint = zzero := by decide

/-- Red control: their squared bends agree at x although their signed bends do not. -/
theorem sign_is_the_only_distinction_at_x :
    bendSqA xPoint = bendSqB xPoint ∧ bendA xPoint ≠ bendB xPoint := by decide

/-! ## The surviving hinge line -/

def bisectorPoint (t : Z3) : V3 := ⟨zzero, t, t⟩

/-- 4. Along the Y–Z bisector both cubics agree, generally nontrivially. -/
theorem bend_on_the_bisector (t : Z3) :
    bendA (bisectorPoint t) = c3 ⟨8, -4⟩ t t t ∧
    bendB (bisectorPoint t) = c3 ⟨8, -4⟩ t t t := by
  obtain ⟨ta, tb⟩ := t
  simp only [bendA, bendB, bisectorPoint, det3, A, B, rzP, ryP, c3,
    zzero, zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> constructor <;> grind

/-! ## Same endpoint, opposite journey -/

/-- 15Y's blind point `(1, √3−2, 2−√3)`. -/
def blindPoint : V3 := ⟨⟨1, 0⟩, ⟨-2, 1⟩, ⟨2, -1⟩⟩

/-- 5. Endpoint equality does not erase the signed route. -/
theorem blind_finish_retains_opposite_bend :
    A blindPoint = B blindPoint ∧
    bendA blindPoint = ⟨-224, 128⟩ ∧
    bendB blindPoint = ⟨224, -128⟩ := by decide

/-! ## Certificate -/

theorem signed_bend_field_certificate :
    (∀ v, bendA v = cubicA v) ∧
    (∀ v, bendB v = cubicB v) ∧
    (∀ v, zsub (bendA v) (bendB v) = signedOrderField v) ∧
    (∀ v, zadd v.y v.z = zzero → bendA v = zneg (bendB v)) ∧
    (∀ v, zadd v.y v.z = zzero → bendSqA v = bendSqB v) ∧
    bendA xPoint ≠ bendB xPoint ∧
    bendA yPoint ≠ bendB yPoint ∧
    (∀ t, bendA (bisectorPoint t) = c3 ⟨8, -4⟩ t t t ∧
      bendB (bisectorPoint t) = c3 ⟨8, -4⟩ t t t) ∧
    (A blindPoint = B blindPoint ∧ bendA blindPoint = zneg (bendB blindPoint)) :=
  ⟨bendA_is_cubicA, bendB_is_cubicB, bend_difference_is_the_signed_order_field,
   bends_are_opposite_on_the_turn_plane, unsigned_bend_forgets_the_turn_plane,
   by decide, by decide, bend_on_the_bisector,
   ⟨by decide, by decide⟩⟩

#print axioms bendA_is_cubicA
#print axioms bendB_is_cubicB
#print axioms bend_difference_is_the_signed_order_field
#print axioms bends_are_opposite_on_the_turn_plane
#print axioms unsigned_bend_forgets_the_turn_plane
#print axioms old_turn_plane_is_not_a_signed_seam
#print axioms old_chord_plane_is_not_a_signed_seam
#print axioms sign_is_the_only_distinction_at_x
#print axioms bend_on_the_bisector
#print axioms blind_finish_retains_opposite_bend
#print axioms signed_bend_field_certificate

end FoundationStoneFifteenG
