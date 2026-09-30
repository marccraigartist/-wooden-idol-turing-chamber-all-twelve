/-!
# THE MISSING BIT — FOUNDATION STONE TEST 16B: THE BLIND EVALUATOR CLASS

Runs in the Lean live editor with no imports (core Lean only).

Test 16A proved that endpoint-only replay cannot recover two different native journeys
that finish together.  Test 16B widens the question: can asking more questions help if
every question belongs to the same symmetry-bound class?

An admissible evaluator pair has two properties:

* TRANSPORT: the exchange half-turn carries A's measurement to B's measurement;
* UNSIGNED: B's measurement ignores the antipodal sign of its input.

On the turn plane `y + z = 0`, the exchange IS the antipode.  Therefore every admissible
pair ties there.  Lean certifies not only simultaneous lists of such questions but an
ADAPTIVE interrogation: after seeing all previous answers, a strategy may choose any next
admissible evaluator.  The two transcripts are still equal after every finite number of
rounds.

Native instances:

* start-to-finish chord and two-leg energy belong to the blind class;
* signed bend is transported by the exchange but is ODD rather than unsigned;
* at the x-axis point, chord and energy tie while the bends are `(0,-1)` and `(0,1)`.

So asking more questions from the same class cannot reveal the missing bit.  The signed
bend escapes because it changes the observation class, not because it samples the old
class more thoroughly.

Scope: this class is explicitly the exchange-carried, sign-insensitive class.  The theorem
does not say all evaluators are blind.  The signed red control proves that they are not.
-/
namespace FoundationStoneSixteenB

/-! ## Exact geometry over Z[sqrt 3] -/

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

def rzP (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.y, zadd v.x (zroot v.y), zscale 2 v.z⟩

def ryP (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩

/-- Z first, then Y. -/
def A (v : V3) : V3 := ryP (rzP v)

/-- Y first, then Z. -/
def B (v : V3) : V3 := rzP (ryP v)

/-- Half-turn about the Y-Z bisector. -/
def exchange (v : V3) : V3 := ⟨zneg v.x, v.z, v.y⟩

/-! ## The evaluator class -/

/-- A paired reading transported from the A journey to the B journey and unsigned on B. -/
structure EvaluatorPair (R : Type) where
  left : V3 → R
  right : V3 → R
  carried : ∀ v, right (exchange v) = left v
  unsignedRight : ∀ v, right (vneg v) = right v

/-- On the turn plane, exchange is exactly the antipode. -/
theorem exchange_is_antipode_on_turn_plane (v : V3) (h : zadd v.y v.z = zzero) :
    exchange v = vneg v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [exchange, vneg, zneg, zadd, zzero, V3.mk.injEq, Z3.mk.injEq,
    true_and] at h ⊢
  omega

/-- 1. Every evaluator in the whole admissible class ties on the turn plane. -/
theorem every_admissible_evaluator_is_blind {R : Type} (e : EvaluatorPair R)
    (v : V3) (h : zadd v.y v.z = zzero) : e.left v = e.right v := by
  rw [← e.carried v, exchange_is_antipode_on_turn_plane v h, e.unsignedRight]

/-! ## Any fixed bank, and then any adaptive interrogation -/

def answersLeft {R : Type} (bank : List (EvaluatorPair R)) (v : V3) : List R :=
  bank.map (fun e => e.left v)

def answersRight {R : Type} (bank : List (EvaluatorPair R)) (v : V3) : List R :=
  bank.map (fun e => e.right v)

/-- 2a. Any finite bank of admissible evaluators remains blind. -/
theorem every_finite_bank_is_blind {R : Type} (bank : List (EvaluatorPair R))
    (v : V3) (h : zadd v.y v.z = zzero) :
    answersLeft bank v = answersRight bank v := by
  induction bank with
  | nil => rfl
  | cons e rest ih =>
    simp only [answersLeft, answersRight, List.map_cons, List.cons.injEq]
    exact ⟨every_admissible_evaluator_is_blind e v h, ih⟩

/-- An adaptive strategy chooses its next admissible evaluator from the transcript so far. -/
def transcriptLeft {R : Type} (choose : List R → EvaluatorPair R) : Nat → V3 → List R
  | 0, _ => []
  | n + 1, v =>
      let old := transcriptLeft choose n v
      old ++ [(choose old).left v]

def transcriptRight {R : Type} (choose : List R → EvaluatorPair R) : Nat → V3 → List R
  | 0, _ => []
  | n + 1, v =>
      let old := transcriptRight choose n v
      old ++ [(choose old).right v]

/-- 2b. Even adaptive choice cannot escape a blind evaluator class. -/
theorem every_adaptive_interrogation_is_blind {R : Type}
    (choose : List R → EvaluatorPair R) (v : V3) (h : zadd v.y v.z = zzero) :
    ∀ n, transcriptLeft choose n v = transcriptRight choose n v := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [transcriptLeft, transcriptRight]
    rw [ih]
    exact congrArg (fun answer => transcriptRight choose n v ++ [answer])
      (every_admissible_evaluator_is_blind (choose (transcriptRight choose n v)) v h)

/-! ## Native unsigned instances -/

def chordA (v : V3) : Z3 := normSq (vsub (A v) (vscale 4 v))
def chordB (v : V3) : Z3 := normSq (vsub (B v) (vscale 4 v))

def energyA (v : V3) : Z3 :=
  zadd (normSq (vsub (vscale 2 (rzP v)) (vscale 4 v)))
       (normSq (vsub (A v) (vscale 2 (rzP v))))

def energyB (v : V3) : Z3 :=
  zadd (normSq (vsub (vscale 2 (ryP v)) (vscale 4 v)))
       (normSq (vsub (B v) (vscale 2 (ryP v))))

theorem chord_is_carried (v : V3) : chordB (exchange v) = chordA v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordA, chordB, normSq, zdot, vsub, vscale, exchange, A, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem chordB_is_unsigned (v : V3) : chordB (vneg v) = chordB v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [chordB, normSq, zdot, vsub, vscale, vneg, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem energy_is_carried (v : V3) : energyB (exchange v) = energyA v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [energyA, energyB, normSq, zdot, vsub, vscale, exchange, A, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem energyB_is_unsigned (v : V3) : energyB (vneg v) = energyB v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [energyB, normSq, zdot, vsub, vscale, vneg, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

def chordPair : EvaluatorPair Z3 :=
  ⟨chordA, chordB, chord_is_carried, chordB_is_unsigned⟩

def energyPair : EvaluatorPair Z3 :=
  ⟨energyA, energyB, energy_is_carried, energyB_is_unsigned⟩

def xPoint : V3 := ⟨zone, zzero, zzero⟩

theorem x_point_is_on_turn_plane : zadd xPoint.y xPoint.z = zzero := by decide

/-- 3. The two previously studied unsigned measurements are instances of the class. -/
theorem native_unsigned_bank_is_blind :
    answersLeft [chordPair, energyPair] xPoint =
      answersRight [chordPair, energyPair] xPoint :=
  every_finite_bank_is_blind _ xPoint x_point_is_on_turn_plane

/-! ## Signed bend: the red control outside the class -/

def det3 (u v w : V3) : Z3 :=
  zadd (zadd (zmul u.x (zsub (zmul v.y w.z) (zmul v.z w.y)))
             (zmul u.y (zsub (zmul v.z w.x) (zmul v.x w.z))))
       (zmul u.z (zsub (zmul v.x w.y) (zmul v.y w.x)))

def bendA (v : V3) : Z3 := det3 v (rzP v) (A v)
def bendB (v : V3) : Z3 := det3 v (ryP v) (B v)

theorem bend_is_carried (v : V3) : bendB (exchange v) = bendA v := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [bendA, bendB, det3, exchange, A, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem bendB_is_odd (v : V3) : bendB (vneg v) = zneg (bendB v) := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [bendB, det3, vneg, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

/-- 4a. The signed bend genuinely lies outside the unsigned class. -/
theorem bendB_is_not_unsigned : ¬ ∀ v, bendB (vneg v) = bendB v := by
  intro h
  have hx := h xPoint
  have hneg : bendB (vneg xPoint) = ⟨0, -1⟩ := by decide
  have hpos : bendB xPoint = ⟨0, 1⟩ := by decide
  rw [hneg, hpos] at hx
  contradiction

/-- 4b. At the same turn-plane point, signed bend sees the order exactly. -/
theorem signed_bend_escapes_at_x :
    bendA xPoint = ⟨0, -1⟩ ∧ bendB xPoint = ⟨0, 1⟩ ∧
      bendA xPoint ≠ bendB xPoint := by
  decide

/-- 4c. The signed pair is still transported correctly: it escapes only by retaining sign. -/
theorem signed_escape_is_not_frame_cheating :
    (∀ v, bendB (exchange v) = bendA v) ∧
      ¬ (∀ v, bendB (vneg v) = bendB v) :=
  ⟨bend_is_carried, bendB_is_not_unsigned⟩

/-! ## Certificate -/

theorem blind_evaluator_class_certificate :
    (∀ (R : Type) (e : EvaluatorPair R) (v : V3),
      zadd v.y v.z = zzero → e.left v = e.right v) ∧
    (∀ (R : Type) (bank : List (EvaluatorPair R)) (v : V3),
      zadd v.y v.z = zzero → answersLeft bank v = answersRight bank v) ∧
    (∀ (R : Type) (choose : List R → EvaluatorPair R) (v : V3),
      zadd v.y v.z = zzero → ∀ n,
        transcriptLeft choose n v = transcriptRight choose n v) ∧
    answersLeft [chordPair, energyPair] xPoint =
      answersRight [chordPair, energyPair] xPoint ∧
    (∀ v, bendB (exchange v) = bendA v) ∧
    ¬ (∀ v, bendB (vneg v) = bendB v) ∧
    bendA xPoint ≠ bendB xPoint :=
  ⟨fun _ e v => every_admissible_evaluator_is_blind e v,
   fun _ bank v => every_finite_bank_is_blind bank v,
   fun _ choose v => every_adaptive_interrogation_is_blind choose v,
   native_unsigned_bank_is_blind, bend_is_carried, bendB_is_not_unsigned,
   signed_bend_escapes_at_x.2.2⟩

#print axioms exchange_is_antipode_on_turn_plane
#print axioms every_admissible_evaluator_is_blind
#print axioms every_finite_bank_is_blind
#print axioms every_adaptive_interrogation_is_blind
#print axioms chord_is_carried
#print axioms chordB_is_unsigned
#print axioms energy_is_carried
#print axioms energyB_is_unsigned
#print axioms native_unsigned_bank_is_blind
#print axioms bend_is_carried
#print axioms bendB_is_odd
#print axioms bendB_is_not_unsigned
#print axioms signed_bend_escapes_at_x
#print axioms signed_escape_is_not_frame_cheating
#print axioms blind_evaluator_class_certificate

end FoundationStoneSixteenB
