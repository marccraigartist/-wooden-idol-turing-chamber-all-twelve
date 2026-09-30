/-!
# WHERE THE GLOBE FEELS THE ORDER — FOUNDATION STONE 15Y (Claude)

An answer to Charlie's proposed Test 15D.  Core Lean only, no Mathlib.

Same encoding as Test 15C: `Z3` is `a + b√3`; `rzP`, `ryP` are `2·Rz(30°)` and
`2·Ry(30°)`; `A = 4·Ry·Rz` (Rz acts first), `B = 4·Rz·Ry` (Ry acts first);
`chordSqScaled F v = |F v − 4v|²`, which is sixteen times the true squared chord.

Lean certifies:

1. CHORD LAW.  Each order is one turn about its own axle, and a point's chord is
   the full-turn chord times its squared distance from that axle.  The two axles
   are mirror images: `(1, 2+√3, 2+√3)` and `(−1, 2+√3, 2+√3)`.
2. EQUATOR.  Charlie's 15° point is exactly square to B's axle, so B carries it
   the full turn.
3. ORDER FIELD.  For every point, chord²(B) − chord²(A) = 16(2−√3)·x·(y+z).
4. SEAMS.  The chords are equal exactly when x = 0 or y + z = 0: two
   perpendicular great circles.
5. BLIND LINE.  `A v = B v` exactly on one line, `(1, √3−2, 2−√3)`.  That line
   is the axle of the loop B⁻¹A, whose trace ⟨33, 8⟩ is the 15X holonomy trace:
   the same 15.36° turn.
6. EXCHANGE.  The half-turn about the Y–Z bisector, (x,y,z) ↦ (−x,z,y), swaps
   the two orders and reverses the field.
7. RED CONTROL.  Half-turns about Y and Z commute, so their order field is zero
   everywhere.  Perpendicular axles alone do not make the field.

Scope: points have coordinates in ℤ[√3].  The identities are polynomial, so the
same algebra holds for every real point, but that transfer is not certified here.
The Dead Globe renderer-frame caveat still applies.
-/

namespace FoundationStoneFifteenY

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
def zadd (u v : Z3) : Z3 := ⟨u.a + v.a, u.b + v.b⟩
def zneg (u : Z3) : Z3 := ⟨-u.a, -u.b⟩
def zsub (u v : Z3) : Z3 := zadd u (zneg v)
def zscale (k : Int) (u : Z3) : Z3 := ⟨k * u.a, k * u.b⟩
def zroot (u : Z3) : Z3 := ⟨3 * u.b, u.a⟩
def zmul (u v : Z3) : Z3 :=
  ⟨u.a * v.a + 3 * u.b * v.b, u.a * v.b + u.b * v.a⟩

def vsub (u v : V3) : V3 := ⟨zsub u.x v.x, zsub u.y v.y, zsub u.z v.z⟩
def vscale (k : Int) (v : V3) : V3 := ⟨zscale k v.x, zscale k v.y, zscale k v.z⟩
def zdot (u v : V3) : Z3 := zadd (zadd (zmul u.x v.x) (zmul u.y v.y)) (zmul u.z v.z)
def normSq (v : V3) : Z3 := zdot v v

/-! ## Charlie's maps, unchanged -/

def rzP (v : V3) : V3 := ⟨zsub (zroot v.x) v.y, zadd v.x (zroot v.y), zscale 2 v.z⟩
def ryP (v : V3) : V3 := ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩
def rzN (v : V3) : V3 := ⟨zadd (zroot v.x) v.y, zadd (zneg v.x) (zroot v.y), zscale 2 v.z⟩
def ryN (v : V3) : V3 := ⟨zsub (zroot v.x) v.z, zscale 2 v.y, zadd v.x (zroot v.z)⟩

def A (v : V3) : V3 := ryP (rzP v)
def B (v : V3) : V3 := rzP (ryP v)
def Binv (v : V3) : V3 := ryN (rzN v)

def chordSqScaled (F : V3 → V3) (v : V3) : Z3 := normSq (vsub (F v) (vscale 4 v))

def xPoint : V3 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
def fifteenPoint : V3 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨2, -1⟩⟩

/-! ## 1. Two axles, one angle -/

/-- `(1, 2+√3, 2+√3)`. -/
def axleA : V3 := ⟨⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩⟩
/-- `(−1, 2+√3, 2+√3)`: the mirror image of `axleA` in the x-coordinate. -/
def axleB : V3 := ⟨⟨-1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩⟩

theorem axleA_stays : A axleA = vscale 4 axleA := by decide
theorem axleB_stays : B axleB = vscale 4 axleB := by decide
theorem axles_are_the_same_length : normSq axleA = normSq axleB := by decide

/-- Sixteen times the full-turn squared chord, `16·(9/4 − √3)`.  Both orders
turn by the same angle (cos = √3/2 − 1/8, about 42.18°). -/
def fullTurn : Z3 := ⟨36, -16⟩

/-- A point's chord is the full-turn chord times its squared distance from the
axle, measured in units of the axle's length. -/
theorem chord_law_A (v : V3) :
    zmul (chordSqScaled A v) (normSq axleA) =
      zmul fullTurn (zsub (zmul (normSq v) (normSq axleA))
        (zmul (zdot v axleA) (zdot v axleA))) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordSqScaled, normSq, zdot, vsub, vscale, A, ryP, rzP, axleA, fullTurn,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem chord_law_B (v : V3) :
    zmul (chordSqScaled B v) (normSq axleB) =
      zmul fullTurn (zsub (zmul (normSq v) (normSq axleB))
        (zmul (zdot v axleB) (zdot v axleB))) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordSqScaled, normSq, zdot, vsub, vscale, B, ryP, rzP, axleB, fullTurn,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

/-! ## 2. The 15° point sits on B's equator -/

theorem fifteen_is_square_to_B_axle : zdot fifteenPoint axleB = zzero := by decide
theorem fifteen_is_not_square_to_A_axle : zdot fifteenPoint axleA = ⟨2, 0⟩ := by decide

/-- So B carries the 15° point the full turn: Charlie's `⟨480, −272⟩` is exactly
`fullTurn · |p|²`. -/
theorem fifteen_gets_the_full_turn_under_B :
    chordSqScaled B fifteenPoint = zmul fullTurn (normSq fifteenPoint) := by decide

/-! ## 3. The order field -/

/-- `16(2−√3)·x·(y+z)`. -/
def orderField (v : V3) : Z3 := zmul ⟨32, -16⟩ (zmul v.x (zadd v.y v.z))

theorem order_field (v : V3) :
    chordSqScaled B v = zadd (chordSqScaled A v) (orderField v) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordSqScaled, orderField, normSq, zdot, vsub, vscale, A, B, ryP, rzP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem field_at_x : orderField xPoint = zzero := by decide
/-- Matches 15C: `⟨480, −272⟩ − ⟨368, −208⟩ = ⟨112, −64⟩`. -/
theorem field_at_fifteen : orderField fifteenPoint = ⟨112, -64⟩ := by decide

/-! ## 4. The seams: exactly two great circles

ℤ[√3] has no zero divisors, because √3 is irrational. -/

theorem three_divides_root (m k : Nat) (h : m * m = 3 * k) : m % 3 = 0 := by
  have h3 : (m * m) % 3 = 0 := by rw [h]; exact Nat.mul_mod_right 3 k
  rw [Nat.mul_mod] at h3
  have : m % 3 < 3 := Nat.mod_lt _ (by decide)
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with r | r | r
  · exact r
  · rw [r] at h3; contradiction
  · rw [r] at h3; contradiction

theorem root_three_is_irrational_nat :
    ∀ n m : Nat, m * m = 3 * n * n → n = 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro m h
    obtain ⟨q, rfl⟩ : ∃ q, m = 3 * q :=
      ⟨m / 3, by have := three_divides_root m (n * n) (by rw [h, Nat.mul_assoc]); omega⟩
    have hn : n * n = 3 * (q * q) := by grind
    obtain ⟨t, rfl⟩ : ∃ t, n = 3 * t :=
      ⟨n / 3, by have := three_divides_root n (q * q) hn; omega⟩
    have hq : q * q = 3 * t * t := by grind
    by_cases ht : t = 0
    · rw [ht]
    · exact absurd (ih t (by omega) q hq) ht

theorem root_three_is_irrational (a b : Int) (h : a * a = 3 * b * b) :
    a = 0 ∧ b = 0 := by
  have hn : a.natAbs * a.natAbs = 3 * b.natAbs * b.natAbs := by
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_mul, Nat.mul_assoc] using this
  have hb : b = 0 := Int.natAbs_eq_zero.mp (root_three_is_irrational_nat _ _ hn)
  subst hb
  have : a * a = 0 := by simpa using h
  exact ⟨(Int.mul_eq_zero.mp this).elim id id, rfl⟩

theorem zmul_eq_zero {u w : Z3} (h : zmul u w = zzero) : u = zzero ∨ w = zzero := by
  obtain ⟨ua, ub⟩ := u
  obtain ⟨wa, wb⟩ := w
  simp only [zmul, zzero, Z3.mk.injEq] at h ⊢
  obtain ⟨h1, h2⟩ := h
  have ea : (ua * ua - 3 * ub * ub) * wa = 0 := by grind
  have eb : (ua * ua - 3 * ub * ub) * wb = 0 := by grind
  by_cases hN : ua * ua - 3 * ub * ub = 0
  · left
    exact root_three_is_irrational ua ub (by omega)
  · right
    exact ⟨(Int.mul_eq_zero.mp ea).resolve_left hN,
           (Int.mul_eq_zero.mp eb).resolve_left hN⟩

theorem zadd_zzero (u : Z3) : zadd u zzero = u := by
  cases u; simp [zadd, zzero]

theorem equal_chords_iff_on_a_seam (v : V3) :
    chordSqScaled A v = chordSqScaled B v ↔
      v.x = zzero ∨ zadd v.y v.z = zzero := by
  rw [order_field]
  constructor
  · intro h
    have hf : orderField v = zzero := by
      revert h
      generalize chordSqScaled A v = c
      generalize orderField v = f
      intro h
      cases c; cases f
      simp only [zadd, zzero, Z3.mk.injEq] at h ⊢
      omega
    rcases zmul_eq_zero hf with h0 | h0
    · simp [zzero] at h0
    · exact zmul_eq_zero h0
  · intro h
    have hp : zmul v.x (zadd v.y v.z) = zzero := by
      rcases h with h | h <;> rw [h] <;> simp [zmul, zzero]
    have hf : orderField v = zzero := by
      unfold orderField; rw [hp]; decide
    rw [hf, zadd_zzero]

/-! ## 5. The blind line: where the two orders land together -/

/-- `(1, √3−2, 2−√3)`. -/
def blindPoint : V3 := ⟨⟨1, 0⟩, ⟨-2, 1⟩, ⟨2, -1⟩⟩

theorem blind_point_lands_together : A blindPoint = B blindPoint := by decide
theorem blind_point_is_on_a_seam : zadd blindPoint.y blindPoint.z = zzero := by decide

theorem only_the_blind_line_lands_together (v : V3) :
    A v = B v ↔ (v.y = zmul ⟨-2, 1⟩ v.x ∧ v.z = zmul ⟨2, -1⟩ v.x) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [A, B, ryP, rzP, zadd, zneg, zsub, zscale, zroot, zmul,
    V3.mk.injEq, Z3.mk.injEq]
  omega

/-- The loop B⁻¹A: go by A, come back by B's inverse.  Scale 16. -/
def loopBA (v : V3) : V3 := Binv (A v)

def e1 : V3 := ⟨⟨1, 0⟩, zzero, zzero⟩
def e2 : V3 := ⟨zzero, ⟨1, 0⟩, zzero⟩
def e3 : V3 := ⟨zzero, zzero, ⟨1, 0⟩⟩
def trace16 (F : V3 → V3) : Z3 := zadd (zadd (F e1).x (F e2).y) (F e3).z

theorem blind_line_is_the_loop_axle : loopBA blindPoint = vscale 16 blindPoint := by decide
/-- Same trace as 15X's `Rz Ry Rz⁻¹ Ry⁻¹`: the same 15.36° turn. -/
theorem loop_trace : trace16 loopBA = ⟨33, 8⟩ := by decide
theorem loop_is_not_nothing : loopBA e1 ≠ vscale 16 e1 := by decide

/-! ## 6. The exchange half-turn -/

/-- Half-turn about the bisector of the Y and Z axles. -/
def exchange (v : V3) : V3 := ⟨zneg v.x, v.z, v.y⟩

theorem exchange_fixes_bisector :
    exchange ⟨zzero, ⟨1, 0⟩, ⟨1, 0⟩⟩ = ⟨zzero, ⟨1, 0⟩, ⟨1, 0⟩⟩ := by decide

theorem exchange_twice (v : V3) : exchange (exchange v) = v := by
  obtain ⟨⟨xa, xb⟩, y, z⟩ := v
  simp [exchange, zneg]

theorem exchange_swaps_the_orders (v : V3) : exchange (A v) = B (exchange v) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [exchange, A, B, ryP, rzP, zadd, zneg, zsub, zscale, zroot,
    V3.mk.injEq, Z3.mk.injEq]
  omega

theorem exchange_reverses_the_field (v : V3) :
    orderField (exchange v) = zneg (orderField v) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [exchange, orderField, zadd, zneg, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem exchange_reverses_the_blind_line :
    exchange blindPoint = vscale (-1) blindPoint := by decide

/-! ## 7. RED CONTROL: commuting half-turns have no order field -/

def halfY (v : V3) : V3 := ⟨zneg v.x, v.y, zneg v.z⟩
def halfZ (v : V3) : V3 := ⟨zneg v.x, zneg v.y, v.z⟩

theorem half_turns_commute (v : V3) : halfY (halfZ v) = halfZ (halfY v) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp [halfY, halfZ, zneg]

theorem half_turn_field_is_zero (v : V3) :
    normSq (vsub (halfY (halfZ v)) v) = normSq (vsub (halfZ (halfY v)) v) := by
  rw [half_turns_commute]

/-! ## Certificate -/

theorem where_the_globe_feels_the_order :
    A axleA = vscale 4 axleA ∧
    B axleB = vscale 4 axleB ∧
    zdot fifteenPoint axleB = zzero ∧
    (∀ v, chordSqScaled B v = zadd (chordSqScaled A v) (orderField v)) ∧
    (∀ v, chordSqScaled A v = chordSqScaled B v ↔
      v.x = zzero ∨ zadd v.y v.z = zzero) ∧
    (∀ v, A v = B v ↔ (v.y = zmul ⟨-2, 1⟩ v.x ∧ v.z = zmul ⟨2, -1⟩ v.x)) ∧
    loopBA blindPoint = vscale 16 blindPoint ∧
    trace16 loopBA = ⟨33, 8⟩ ∧
    (∀ v, exchange (A v) = B (exchange v)) ∧
    (∀ v, halfY (halfZ v) = halfZ (halfY v)) :=
  ⟨axleA_stays, axleB_stays, fifteen_is_square_to_B_axle, order_field,
   equal_chords_iff_on_a_seam, only_the_blind_line_lands_together,
   blind_line_is_the_loop_axle, loop_trace, exchange_swaps_the_orders,
   half_turns_commute⟩

#print axioms chord_law_A
#print axioms chord_law_B
#print axioms fifteen_gets_the_full_turn_under_B
#print axioms order_field
#print axioms equal_chords_iff_on_a_seam
#print axioms only_the_blind_line_lands_together
#print axioms loop_trace
#print axioms exchange_swaps_the_orders
#print axioms exchange_reverses_the_field
#print axioms where_the_globe_feels_the_order

end FoundationStoneFifteenY
