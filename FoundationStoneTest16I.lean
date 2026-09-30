/-!
# THE NATIVE FRAME CHANGE — FOUNDATION STONE TEST 16I

Runs in the Lean live editor with no imports (core Lean only).

Test 16H earned a least successor frame from deliberately constructed binary
histories.  Test 16I removes that planted example.  Its two histories are the
Dead Globe's native noncommuting 30-degree journeys:

    A = Ry(30°) after Rz(30°)       B = Rz(30°) after Ry(30°).

The exact arithmetic is over Z[sqrt 3], scaled by 2 per primitive turn.  The
exchange half-turn sigma(x,y,z)=(-x,z,y) carries A's journey onto B's journey.
At the x-axis seat point sigma is the antipode.

Lean certifies:
1. EVERY exchange-carried evaluator that ignores sign is blind there.
2. The native unsigned chord and two-leg energy belong to that class and tie.
3. Any exchange-carried evaluator that separates the routes there CANNOT ignore
   sign.  Sign sensitivity is forced by the failure of the unsigned frame.
4. The journey's native signed bend, det[start, midpoint, endpoint], is carried
   by the exchange, reverses under sign, and separates the routes exactly.
5. Adding bend to the unsigned frame is a strict behavioural refinement.
6. RED CONTROL.  A renderer's fixed "up" coordinate also separates the routes,
   but it is not exchange-carried.  Separation alone is therefore not enough:
   the signed bend succeeds without secretly privileging an external direction.

Scope lock: bend is a canonical native witness, not the unique possible signed
evaluator.  This is an earned B6-shaped frame change inside the two-route model;
it is not yet the full Stage 3 twelve-station certificate.
-/
namespace NativeFrameChange

/-! ## Exact geometry -/

/-- a + b*sqrt(3) -/
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

/-- Twice the primitive positive 30-degree turns. -/
def rzP (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.y, zadd v.x (zroot v.y), zscale 2 v.z⟩
def ryP (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩

/-- Z first, then Y; and Y first, then Z.  Each is scaled by 4. -/
def A (v : V3) : V3 := ryP (rzP v)
def B (v : V3) : V3 := rzP (ryP v)

/-- Half-turn about the Y-Z bisector. -/
def exchange (v : V3) : V3 := ⟨zneg v.x, v.z, v.y⟩

def xPoint : V3 := ⟨zone, zzero, zzero⟩

/-- The exchange carries each primitive leg to the other clock's leg. -/
theorem exchange_carries_z_leg (v : V3) : exchange (rzP v) = ryP (exchange v) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [exchange, rzP, ryP, zadd, zneg, zsub, zscale, zroot,
    V3.mk.injEq, Z3.mk.injEq, true_and]
  omega

theorem exchange_carries_y_leg (v : V3) : exchange (ryP v) = rzP (exchange v) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [exchange, rzP, ryP, zadd, zneg, zsub, zscale, zroot,
    V3.mk.injEq, Z3.mk.injEq, and_true]
  omega

theorem exchange_carries_journey (v : V3) : exchange (A v) = B (exchange v) := by
  unfold A B
  rw [exchange_carries_y_leg, exchange_carries_z_leg]

/-- At the x seat, exchange is exactly the antipode. -/
theorem exchange_is_antipode_at_x : exchange xPoint = vneg xPoint := by decide

/-! ## The evaluator-class obstruction -/

def CarriedAcross (fA fB : V3 → Z3) : Prop := ∀ v, fB (exchange v) = fA v
def IgnoresSign (f : V3 → Z3) : Prop := ∀ v, f (vneg v) = f v
def ReversesSign (f : V3 → Z3) : Prop := ∀ v, f (vneg v) = zneg (f v)

/-- 1. The whole carried, sign-blind evaluator class ties at the x seat. -/
theorem every_carried_unsigned_evaluator_is_blind
    (fA fB : V3 → Z3) (hc : CarriedAcross fA fB) (he : IgnoresSign fB) :
    fA xPoint = fB xPoint := by
  rw [← hc xPoint, exchange_is_antipode_at_x, he]

/-- 3. Contrapositive: a carried separator at x must be sign-sensitive. -/
theorem separating_carried_evaluator_cannot_ignore_sign
    (fA fB : V3 → Z3) (hc : CarriedAcross fA fB)
    (hsep : fA xPoint ≠ fB xPoint) : ¬ IgnoresSign fB := by
  intro he
  exact hsep (every_carried_unsigned_evaluator_is_blind fA fB hc he)

/-- A carried sign-reversing evaluator gives opposite readings on the seam. -/
theorem every_carried_signed_evaluator_reverses
    (fA fB : V3 → Z3) (hc : CarriedAcross fA fB) (ho : ReversesSign fB) :
    fA xPoint = zneg (fB xPoint) := by
  rw [← hc xPoint, exchange_is_antipode_at_x, ho]

/-! ## Native unsigned frame: chord and two-leg energy -/

def chordA (v : V3) : Z3 := normSq (vsub (A v) (vscale 4 v))
def chordB (v : V3) : Z3 := normSq (vsub (B v) (vscale 4 v))

def energyA (v : V3) : Z3 :=
  zadd (normSq (vsub (vscale 2 (rzP v)) (vscale 4 v)))
       (normSq (vsub (A v) (vscale 2 (rzP v))))
def energyB (v : V3) : Z3 :=
  zadd (normSq (vsub (vscale 2 (ryP v)) (vscale 4 v)))
       (normSq (vsub (B v) (vscale 2 (ryP v))))

theorem chord_is_carried : CarriedAcross chordA chordB := by
  intro v
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordA, chordB, normSq, zdot, vsub, vscale, exchange,
    A, B, rzP, ryP, zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem energy_is_carried : CarriedAcross energyA energyB := by
  intro v
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [energyA, energyB, normSq, zdot, vsub, vscale, exchange,
    A, B, rzP, ryP, zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem chordB_ignores_sign : IgnoresSign chordB := by
  intro v
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordB, normSq, zdot, vsub, vscale, vneg, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem energyB_ignores_sign : IgnoresSign energyB := by
  intro v
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [energyB, normSq, zdot, vsub, vscale, vneg, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

/-- 2. Both native unsigned measurements are forced to tie. -/
theorem native_unsigned_frame_is_blind :
    chordA xPoint = chordB xPoint ∧ energyA xPoint = energyB xPoint :=
  ⟨every_carried_unsigned_evaluator_is_blind chordA chordB
      chord_is_carried chordB_ignores_sign,
   every_carried_unsigned_evaluator_is_blind energyA energyB
      energy_is_carried energyB_ignores_sign⟩

/-! ## Native signed frame: the bend of the journey -/

/-- Triple product u dot (v cross w). -/
def det3 (u v w : V3) : Z3 :=
  zadd (zadd (zmul u.x (zsub (zmul v.y w.z) (zmul v.z w.y)))
             (zmul u.y (zsub (zmul v.z w.x) (zmul v.x w.z))))
       (zmul u.z (zsub (zmul v.x w.y) (zmul v.y w.x)))

/-- Signed route bend: start, native midpoint, native endpoint. -/
def bendA (v : V3) : Z3 := det3 v (rzP v) (A v)
def bendB (v : V3) : Z3 := det3 v (ryP v) (B v)

theorem bend_is_carried : CarriedAcross bendA bendB := by
  intro v
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [bendA, bendB, det3, exchange, A, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem bendB_reverses_sign : ReversesSign bendB := by
  intro v
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [bendB, det3, vneg, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

/-- 4a. Abstractly, the two native bends are opposites at x. -/
theorem native_bend_reverses : bendA xPoint = zneg (bendB xPoint) :=
  every_carried_signed_evaluator_reverses bendA bendB bend_is_carried bendB_reverses_sign

/-- 4b. Concretely they are nonzero opposite orientations. -/
theorem native_bend_separates :
    bendA xPoint = ⟨0, -1⟩ ∧ bendB xPoint = ⟨0, 1⟩ := by decide

theorem native_bend_is_a_separator : bendA xPoint ≠ bendB xPoint := by
  rw [native_bend_separates.1, native_bend_separates.2]
  intro h
  have hb := congrArg Z3.b h
  change (-1 : Int) = 1 at hb
  omega

/-- The obstruction applies to the actual native bend: it cannot ignore sign. -/
theorem bend_cannot_ignore_sign : ¬ IgnoresSign bendB :=
  separating_carried_evaluator_cannot_ignore_sign bendA bendB
    bend_is_carried native_bend_is_a_separator

/-! ## Behavioural frame refinement on the two native routes -/

inductive Route
  | zThenY
  | yThenZ
deriving DecidableEq

def unsignedReading : Route → Z3 × Z3
  | .zThenY => (chordA xPoint, energyA xPoint)
  | .yThenZ => (chordB xPoint, energyB xPoint)

def signedReading : Route → (Z3 × Z3) × Z3
  | .zThenY => (unsignedReading .zThenY, bendA xPoint)
  | .yThenZ => (unsignedReading .yThenZ, bendB xPoint)

def Refines {New Old : Type} (new : Route → New) (old : Route → Old) : Prop :=
  ∀ r s, new r = new s → old r = old s

def StrictlyRefines {New Old : Type} (new : Route → New) (old : Route → Old) : Prop :=
  Refines new old ∧ ¬ Refines old new

theorem signed_refines_unsigned : Refines signedReading unsignedReading := by
  intro r s h
  cases r <;> cases s <;> simp_all [signedReading]

theorem unsigned_routes_tie :
    unsignedReading .zThenY = unsignedReading .yThenZ := by
  apply Prod.ext
  · exact native_unsigned_frame_is_blind.1
  · exact native_unsigned_frame_is_blind.2

theorem signed_routes_differ : signedReading .zThenY ≠ signedReading .yThenZ := by
  intro h
  have hb := congrArg Prod.snd h
  exact native_bend_is_a_separator hb

theorem unsigned_does_not_refine_signed : ¬ Refines unsignedReading signedReading := by
  intro h
  exact signed_routes_differ (h .zThenY .yThenZ unsigned_routes_tie)

/-- 5. The bend-bearing frame is strictly finer on the native routes. -/
theorem native_signed_frame_is_strictly_finer :
    StrictlyRefines signedReading unsignedReading :=
  ⟨signed_refines_unsigned, unsigned_does_not_refine_signed⟩

inductive NativeFrame
  | unsigned
  | signed
deriving DecidableEq

/-- B6-shaped, but earned by native route behaviour rather than mere inequality. -/
def NativeEarnedB6 : Prop :=
  ∃ φ' : NativeFrame, φ' ≠ .unsigned ∧ φ' = .signed ∧
    StrictlyRefines signedReading unsignedReading

theorem native_earned_B6 : NativeEarnedB6 := by
  exact ⟨.signed, by decide, rfl, native_signed_frame_is_strictly_finer⟩

/-! ## Red control: a frame-bound separator -/

/-- A renderer with an externally fixed up direction reads endpoint z. -/
def upA (v : V3) : Z3 := (A v).z
def upB (v : V3) : Z3 := (B v).z

/-- 6a. It distinguishes the two orders at x... -/
theorem up_sees_the_order : upA xPoint ≠ upB xPoint := by decide

/-- 6b. ...but it fails the exchange transport law even at that point. -/
theorem up_is_not_carried : upB (exchange xPoint) ≠ upA xPoint := by decide

/-- So its success is frame privilege, unlike the transported bend. -/
theorem separation_alone_is_not_enough :
    upA xPoint ≠ upB xPoint ∧ ¬ CarriedAcross upA upB := by
  refine ⟨up_sees_the_order, ?_⟩
  intro h
  exact up_is_not_carried (h xPoint)

/-! ## Certificate -/

theorem native_frame_change_certificate :
    (∀ fA fB : V3 → Z3, CarriedAcross fA fB → IgnoresSign fB →
      fA xPoint = fB xPoint) ∧
    (chordA xPoint = chordB xPoint ∧ energyA xPoint = energyB xPoint) ∧
    (∀ fA fB : V3 → Z3, CarriedAcross fA fB → fA xPoint ≠ fB xPoint →
      ¬ IgnoresSign fB) ∧
    (bendA xPoint = ⟨0, -1⟩ ∧ bendB xPoint = ⟨0, 1⟩) ∧
    StrictlyRefines signedReading unsignedReading ∧
    NativeEarnedB6 ∧
    (upA xPoint ≠ upB xPoint ∧ ¬ CarriedAcross upA upB) :=
  ⟨every_carried_unsigned_evaluator_is_blind,
   native_unsigned_frame_is_blind,
   separating_carried_evaluator_cannot_ignore_sign,
   native_bend_separates,
   native_signed_frame_is_strictly_finer,
   native_earned_B6,
   separation_alone_is_not_enough⟩

#print axioms exchange_carries_journey
#print axioms every_carried_unsigned_evaluator_is_blind
#print axioms separating_carried_evaluator_cannot_ignore_sign
#print axioms chord_is_carried
#print axioms energy_is_carried
#print axioms native_unsigned_frame_is_blind
#print axioms bend_is_carried
#print axioms bendB_reverses_sign
#print axioms native_bend_separates
#print axioms bend_cannot_ignore_sign
#print axioms native_signed_frame_is_strictly_finer
#print axioms native_earned_B6
#print axioms separation_alone_is_not_enough
#print axioms native_frame_change_certificate

end NativeFrameChange
