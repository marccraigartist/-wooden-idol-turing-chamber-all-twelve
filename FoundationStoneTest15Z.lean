/-!
# THE HINGE — FOUNDATION STONE 15Z (Claude)

Why 15D and 15E share one seam and differ in the other.  Core Lean, no Mathlib.
Same encoding as 15C/15Y: `Z3` is `a + b√3`; `rzP`, `ryP` are `2·Rz(30°)`,
`2·Ry(30°)`; `A = ryP ∘ rzP` (Z first), `B = rzP ∘ ryP` (Y first).

The exchange `σ(x,y,z) = (−x,z,y)` is the half-turn about the Y–Z bisector
`(0,1,1)`.  It carries each leg onto the other clock's leg.

Lean certifies:

1. TRANSPORT.  `σ·Rz = Ry·σ` and `σ·Ry = Rz·σ`, so σ carries the whole Z-first
   journey onto the Y-first journey, leg by leg.  The 15D chord and the 15E
   two-leg energy are both carried across.
2. TURN SEAM.  ANY pair of measurements carried across by σ, and unchanged by
   v ↦ −v, agrees on the whole plane y + z = 0.  No formula needed.  This covers
   the chord, the energy, and 15F's travelled arc (its `shared_plane_length` is
   an instance: the arc is carried across and unchanged by v ↦ −v).
3. HINGE POINTS.  ANY carried-across pair agrees on the bisector itself.
4. HINGE CLASSIFICATION.  Every quadratic form reversed by σ is
   `(y+z)·(d·x + b·(y−z))`.  So a quadratic measurement always has the turn seam
   and one second plane, and that plane always contains the bisector: the
   measurement only chooses the hinge angle.
5. INSTANCES.  Chord: `(d, b) = (16(2−√3), 0)`, plane x = 0.  Energy:
   `(d, b) = (16√3−24, 4√3−8)`, plane 2√3x + z − y = 0 (Charlie's 15E, derived
   again here in core Lean).  Both planes contain (0,1,1).
6. RED CONTROL.  A frame-bound reading (the endpoint's z-coordinate, as a
   renderer with a fixed "up" would show) is not carried across by σ, and it DOES
   tell the orders apart at the x-point, where every carried-across measurement is
   blind.
7. LADDER.  At 15Y's blind point the endpoints agree but the midpoints differ:
   same finish, different journey.
8. SIGNED READINGS.  If a carried-across measurement is odd (it flips sign when
   v ↦ −v), then on the turn seam the two orders give EXACTLY OPPOSITE values.
   The bend of the journey, `det[start, midpoint, end]`, is such a reading, and
   at the x-point it is nonzero: the order that every unsigned measurement
   misses there shows up as a reversal of bend.
-/

namespace FoundationStoneFifteenZ

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

def vsub (u v : V3) : V3 := ⟨zsub u.x v.x, zsub u.y v.y, zsub u.z v.z⟩
def vscale (k : Int) (v : V3) : V3 := ⟨zscale k v.x, zscale k v.y, zscale k v.z⟩
def vneg (v : V3) : V3 := ⟨zneg v.x, zneg v.y, zneg v.z⟩
def zdot (u v : V3) : Z3 := zadd (zadd (zmul u.x v.x) (zmul u.y v.y)) (zmul u.z v.z)
def normSq (v : V3) : Z3 := zdot v v

def rzP (v : V3) : V3 := ⟨zsub (zroot v.x) v.y, zadd v.x (zroot v.y), zscale 2 v.z⟩
def ryP (v : V3) : V3 := ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩

def A (v : V3) : V3 := ryP (rzP v)
def B (v : V3) : V3 := rzP (ryP v)

/-- Half-turn about the Y–Z bisector. -/
def exchange (v : V3) : V3 := ⟨zneg v.x, v.z, v.y⟩

/-! ## The two measurements, scaled by 16 -/

/-- 15D: squared start-to-finish chord. -/
def chordA (v : V3) : Z3 := normSq (vsub (A v) (vscale 4 v))
def chordB (v : V3) : Z3 := normSq (vsub (B v) (vscale 4 v))

/-- 15E: sum of the two squared leg chords. -/
def energyA (v : V3) : Z3 :=
  zadd (normSq (vsub (vscale 2 (rzP v)) (vscale 4 v)))
       (normSq (vsub (A v) (vscale 2 (rzP v))))
def energyB (v : V3) : Z3 :=
  zadd (normSq (vsub (vscale 2 (ryP v)) (vscale 4 v)))
       (normSq (vsub (B v) (vscale 2 (ryP v))))

/-! ## 1. Transport: the exchange carries one journey onto the other -/

theorem exchange_carries_z_leg (v : V3) : exchange (rzP v) = ryP (exchange v) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [exchange, rzP, ryP, zadd, zneg, zsub, zscale, zroot, V3.mk.injEq, Z3.mk.injEq,
    true_and]
  omega

theorem exchange_carries_y_leg (v : V3) : exchange (ryP v) = rzP (exchange v) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [exchange, rzP, ryP, zadd, zneg, zsub, zscale, zroot, V3.mk.injEq, Z3.mk.injEq,
    and_true]
  omega

theorem exchange_carries_journey (v : V3) : exchange (A v) = B (exchange v) := by
  unfold A B
  rw [exchange_carries_y_leg, exchange_carries_z_leg]

theorem chord_is_carried (v : V3) : chordB (exchange v) = chordA v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordA, chordB, normSq, zdot, vsub, vscale, exchange, A, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem energy_is_carried (v : V3) : energyB (exchange v) = energyA v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [energyA, energyB, normSq, zdot, vsub, vscale, exchange, A, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem chordA_even (v : V3) : chordA (vneg v) = chordA v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordA, normSq, zdot, vsub, vscale, vneg, A, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem chordB_even (v : V3) : chordB (vneg v) = chordB v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordB, normSq, zdot, vsub, vscale, vneg, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem energyB_even (v : V3) : energyB (vneg v) = energyB v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [energyB, normSq, zdot, vsub, vscale, vneg, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

/-! ## 2–3. The turn seam and the hinge points, for ANY carried-across pair -/

theorem exchange_is_antipode_on_turn_plane (v : V3) (h : zadd v.y v.z = zzero) :
    exchange v = vneg v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [exchange, vneg, zneg, zadd, zzero, V3.mk.injEq, Z3.mk.injEq,
    true_and] at h ⊢
  omega

/-- No formula: symmetry alone forces the turn seam. -/
theorem turn_seam_for_any_measurement (fA fB : V3 → Z3)
    (carried : ∀ v, fB (exchange v) = fA v) (evenB : ∀ v, fB (vneg v) = fB v)
    (v : V3) (h : zadd v.y v.z = zzero) : fA v = fB v := by
  rw [← carried v, exchange_is_antipode_on_turn_plane v h, evenB]

def bisector : V3 := ⟨zzero, zone, zone⟩

theorem exchange_fixes_bisector : exchange bisector = bisector := by decide

theorem hinge_point_for_any_measurement (fA fB : V3 → Z3)
    (carried : ∀ v, fB (exchange v) = fA v) : fA bisector = fB bisector := by
  rw [← carried bisector, exchange_fixes_bisector]

theorem chord_turn_seam (v : V3) (h : zadd v.y v.z = zzero) : chordA v = chordB v :=
  turn_seam_for_any_measurement chordA chordB chord_is_carried chordB_even v h

theorem energy_turn_seam (v : V3) (h : zadd v.y v.z = zzero) : energyA v = energyB v :=
  turn_seam_for_any_measurement energyA energyB energy_is_carried energyB_even v h

/-! ## 4. The hinge classification -/

/-- `a x² + b y² + c z² + d xy + e xz + f yz`, coefficients in ℤ[√3]. -/
structure Quad where
  a : Z3
  b : Z3
  c : Z3
  d : Z3
  e : Z3
  f : Z3

def Quad.eval (q : Quad) (v : V3) : Z3 :=
  zadd (zadd (zadd (zmul q.a (zmul v.x v.x)) (zmul q.b (zmul v.y v.y)))
             (zadd (zmul q.c (zmul v.z v.z)) (zmul q.d (zmul v.x v.y))))
       (zadd (zmul q.e (zmul v.x v.z)) (zmul q.f (zmul v.y v.z)))

/-- `(y+z)·(d·x + b·(y−z))`. -/
def hingeForm (d b : Z3) (v : V3) : Z3 :=
  zmul (zadd v.y v.z) (zadd (zmul d v.x) (zmul b (zsub v.y v.z)))

theorem hinge_classification (q : Quad)
    (odd : ∀ v, q.eval (exchange v) = zneg (q.eval v)) :
    ∀ v, q.eval v = hingeForm q.d q.b v := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, ⟨e1, e2⟩, ⟨f1, f2⟩⟩ := q
  have h1 := odd ⟨zone, zzero, zzero⟩
  have h2 := odd ⟨zzero, zone, zzero⟩
  have h3 := odd ⟨zzero, zone, zone⟩
  have h4 := odd ⟨zone, zone, zzero⟩
  simp only [Quad.eval, exchange, zmul, zadd, zneg, zone, zzero, Z3.mk.injEq] at h1 h2 h3 h4
  have ha1 : a1 = 0 := by omega
  have ha2 : a2 = 0 := by omega
  have hc1 : c1 = -b1 := by omega
  have hc2 : c2 = -b2 := by omega
  have hf1 : f1 = 0 := by omega
  have hf2 : f2 = 0 := by omega
  have he1 : e1 = d1 := by omega
  have he2 : e2 = d2 := by omega
  subst ha1 ha2 hc1 hc2 hf1 hf2 he1 he2
  intro v
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [Quad.eval, hingeForm, zmul, zadd, zneg, zsub, Z3.mk.injEq]
  constructor <;> grind

/-- Every hinge plane contains the bisector: the measurement only picks the angle. -/
theorem every_hinge_plane_contains_bisector (d b : Z3) :
    zadd (zmul d bisector.x) (zmul b (zsub bisector.y bisector.z)) = zzero := by
  obtain ⟨d1, d2⟩ := d
  obtain ⟨b1, b2⟩ := b
  simp only [bisector, zmul, zadd, zsub, zneg, zone, zzero, Z3.mk.injEq]
  omega

/-! ## 5. The two instances -/

/-- 15D's chord field: hinge `(16(2−√3), 0)`, second plane x = 0. -/
theorem chord_hinge (v : V3) :
    zsub (chordB v) (chordA v) = hingeForm ⟨32, -16⟩ zzero v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordA, chordB, hingeForm, normSq, zdot, vsub, vscale, A, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, zzero, Z3.mk.injEq]
  constructor <;> grind

/-- 15E's energy field: hinge `(16√3−24, 4√3−8)`, second plane 2√3x + z − y = 0.
Same as Charlie's `4(2−√3)(y+z)(2√3x+z−y)`. -/
theorem energy_hinge (v : V3) :
    zsub (energyB v) (energyA v) = hingeForm ⟨-24, 16⟩ ⟨-8, 4⟩ v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [energyA, energyB, hingeForm, normSq, zdot, vsub, vscale, A, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

/-! ## 6. RED CONTROL: a frame-bound reading -/

def xPoint : V3 := ⟨zone, zzero, zzero⟩

/-- What a renderer with a fixed "up" shows: the endpoint's z-coordinate. -/
def upA (v : V3) : Z3 := (A v).z
def upB (v : V3) : Z3 := (B v).z

theorem x_point_is_on_turn_plane : zadd xPoint.y xPoint.z = zzero := by decide

theorem carried_measurements_are_blind_at_x :
    chordA xPoint = chordB xPoint ∧ energyA xPoint = energyB xPoint :=
  ⟨chord_turn_seam xPoint x_point_is_on_turn_plane,
   energy_turn_seam xPoint x_point_is_on_turn_plane⟩

theorem up_reading_is_not_carried : upB (exchange xPoint) ≠ upA xPoint := by decide

theorem up_reading_sees_the_order_at_x : upA xPoint ≠ upB xPoint := by decide

/-! ## 7. The ladder: same finish, different journey -/

/-- 15Y's blind point `(1, √3−2, 2−√3)`. -/
def blindPoint : V3 := ⟨⟨1, 0⟩, ⟨-2, 1⟩, ⟨2, -1⟩⟩

theorem same_finish : A blindPoint = B blindPoint := by decide
theorem different_midpoints : rzP blindPoint ≠ ryP blindPoint := by decide

/-! ## 8. Signed readings: the turn seam reverses them -/

theorem turn_seam_reverses_any_odd_measurement (fA fB : V3 → Z3)
    (carried : ∀ v, fB (exchange v) = fA v) (oddB : ∀ v, fB (vneg v) = zneg (fB v))
    (v : V3) (h : zadd v.y v.z = zzero) : fA v = zneg (fB v) := by
  rw [← carried v, exchange_is_antipode_on_turn_plane v h, oddB]

/-- Triple product `u · (v × w)`. -/
def det3 (u v w : V3) : Z3 :=
  zadd (zadd (zmul u.x (zsub (zmul v.y w.z) (zmul v.z w.y)))
             (zmul u.y (zsub (zmul v.z w.x) (zmul v.x w.z))))
       (zmul u.z (zsub (zmul v.x w.y) (zmul v.y w.x)))

/-- Which way the journey bends: `det[start, midpoint, end]` (scale 8). -/
def bendA (v : V3) : Z3 := det3 v (rzP v) (A v)
def bendB (v : V3) : Z3 := det3 v (ryP v) (B v)

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

theorem bend_reverses_on_turn_seam (v : V3) (h : zadd v.y v.z = zzero) :
    bendA v = zneg (bendB v) :=
  turn_seam_reverses_any_odd_measurement bendA bendB bend_is_carried bendB_odd v h

/-- At the x-point every unsigned carried measurement ties, but the bend does not. -/
theorem bend_sees_the_order_at_x :
    bendA xPoint = ⟨0, -1⟩ ∧ bendB xPoint = ⟨0, 1⟩ := by decide

/-! ## Certificate -/

theorem the_hinge :
    (∀ v, exchange (A v) = B (exchange v)) ∧
    (∀ fA fB : V3 → Z3, (∀ v, fB (exchange v) = fA v) → (∀ v, fB (vneg v) = fB v) →
      ∀ v, zadd v.y v.z = zzero → fA v = fB v) ∧
    (∀ q : Quad, (∀ v, q.eval (exchange v) = zneg (q.eval v)) →
      ∀ v, q.eval v = hingeForm q.d q.b v) ∧
    (∀ v, zsub (chordB v) (chordA v) = hingeForm ⟨32, -16⟩ zzero v) ∧
    (∀ v, zsub (energyB v) (energyA v) = hingeForm ⟨-24, 16⟩ ⟨-8, 4⟩ v) ∧
    upA xPoint ≠ upB xPoint ∧
    (A blindPoint = B blindPoint ∧ rzP blindPoint ≠ ryP blindPoint) ∧
    (∀ v, zadd v.y v.z = zzero → bendA v = zneg (bendB v)) ∧
    (bendA xPoint = ⟨0, -1⟩ ∧ bendB xPoint = ⟨0, 1⟩) :=
  ⟨exchange_carries_journey, turn_seam_for_any_measurement, hinge_classification,
   chord_hinge, energy_hinge, up_reading_sees_the_order_at_x,
   ⟨same_finish, different_midpoints⟩, bend_reverses_on_turn_seam,
   bend_sees_the_order_at_x⟩

#print axioms exchange_carries_journey
#print axioms turn_seam_for_any_measurement
#print axioms hinge_point_for_any_measurement
#print axioms hinge_classification
#print axioms chord_hinge
#print axioms energy_hinge
#print axioms up_reading_sees_the_order_at_x
#print axioms different_midpoints
#print axioms bend_reverses_on_turn_seam
#print axioms bend_sees_the_order_at_x
#print axioms the_hinge

end FoundationStoneFifteenZ
