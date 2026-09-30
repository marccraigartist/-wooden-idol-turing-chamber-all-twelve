/-!
# THE ONE-BIT LIFT — FOUNDATION STONE TEST 16C

Runs in the Lean live editor with no imports (core Lean only).

Test 16B proved that every exchange-carried, sign-insensitive evaluator is blind on the
turn plane, even when the questions are chosen adaptively.  This test asks what is
minimally needed to escape that blindness at the x-axis point.

There are two native journeys:

* A: turn about z, then y;
* B: turn about y, then z.

Order of results:

1. The old unsigned observation — endpoint chord plus two-leg energy — is identical for
   A and B.  Therefore no decoder can recover the route from that observation.
2. The signed bend is computed from the journey itself.  It is -sqrt(3) for A and
   +sqrt(3) for B (in the exact Z[sqrt(3)] encoding).
3. One Boolean orientation bit extracted from that bend separates the two routes, and
   the enriched observation has an explicit decoder.
4. The lift is minimal in the two-route sense: adding Unit still cannot recover the
   route, while Bool can.
5. RED CONTROL / PROVENANCE BOUNDARY.  A hand-written route label produces exactly the
   same Boolean function as the native bend bit.  Once origin is erased, output alone
   cannot tell an earned bit from a glued-on bit.  Merely tagging the origin separates
   the packets, but a future test must certify that tag from the production route.

This is deliberately local: "one bit" means one bit is necessary and sufficient to
distinguish these two routes at this point.  It is not a global reconstruction theorem
for every point or every possible history.
-/
namespace FoundationStoneSixteenC

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
def zdot (u v : V3) : Z3 := zadd (zadd (zmul u.x v.x) (zmul u.y v.y)) (zmul u.z v.z)
def normSq (v : V3) : Z3 := zdot v v

/-- Twice a 30-degree turn about z. -/
def rzP (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.y, zadd v.x (zroot v.y), zscale 2 v.z⟩

/-- Twice a 30-degree turn about y. -/
def ryP (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩

/-- Z first, then Y; scaled by four. -/
def stepA (v : V3) : V3 := ryP (rzP v)

/-- Y first, then Z; scaled by four. -/
def stepB (v : V3) : V3 := rzP (ryP v)

def xPoint : V3 := ⟨zone, zzero, zzero⟩

/-! ## The old unsigned observation -/

def chordA (v : V3) : Z3 := normSq (vsub (stepA v) (vscale 4 v))
def chordB (v : V3) : Z3 := normSq (vsub (stepB v) (vscale 4 v))

def energyA (v : V3) : Z3 :=
  zadd (normSq (vsub (vscale 2 (rzP v)) (vscale 4 v)))
       (normSq (vsub (stepA v) (vscale 2 (rzP v))))

def energyB (v : V3) : Z3 :=
  zadd (normSq (vsub (vscale 2 (ryP v)) (vscale 4 v)))
       (normSq (vsub (stepB v) (vscale 2 (ryP v))))

inductive Route
  | A
  | B
deriving DecidableEq

def oldObservation : Route → Z3 × Z3
  | .A => (chordA xPoint, energyA xPoint)
  | .B => (chordB xPoint, energyB xPoint)

/-- 1a. Chord and energy together still see no difference. -/
theorem old_observation_collapses : oldObservation .A = oldObservation .B := by
  decide

/-- 1b. Consequently no decoder from the old observation can recover both routes. -/
theorem no_decoder_from_old_observation :
    ¬ ∃ decode : (Z3 × Z3) → Route, ∀ r, decode (oldObservation r) = r := by
  intro h
  obtain ⟨decode, hd⟩ := h
  have hab : Route.A = Route.B := calc
    Route.A = decode (oldObservation .A) := (hd .A).symm
    _ = decode (oldObservation .B) := congrArg decode old_observation_collapses
    _ = Route.B := hd .B
  exact Route.noConfusion hab

/-! ## Native signed bend -/

/-- Triple product u dot (v cross w). -/
def det3 (u v w : V3) : Z3 :=
  zadd (zadd (zmul u.x (zsub (zmul v.y w.z) (zmul v.z w.y)))
             (zmul u.y (zsub (zmul v.z w.x) (zmul v.x w.z))))
       (zmul u.z (zsub (zmul v.x w.y) (zmul v.y w.x)))

def bendA (v : V3) : Z3 := det3 v (rzP v) (stepA v)
def bendB (v : V3) : Z3 := det3 v (ryP v) (stepB v)

def nativeBend : Route → Z3
  | .A => bendA xPoint
  | .B => bendB xPoint

/-- 2. The missing orientation is already present in the native journeys. -/
theorem native_bends_are_opposite :
    nativeBend .A = ⟨0, -1⟩ ∧ nativeBend .B = ⟨0, 1⟩ := by
  decide

/-- Read one bit from the sign-bearing native bend. -/
def nativeOrientation (r : Route) : Bool := nativeBend r == ⟨0, 1⟩

theorem native_orientation_values :
    nativeOrientation .A = false ∧ nativeOrientation .B = true := by
  decide

theorem native_orientation_is_injective : Function.Injective nativeOrientation := by
  intro r s h
  cases r <;> cases s
  · rfl
  · have hf := native_orientation_values.1
    have ht := native_orientation_values.2
    rw [hf, ht] at h
    contradiction
  · have hf := native_orientation_values.1
    have ht := native_orientation_values.2
    rw [ht, hf] at h
    contradiction
  · rfl

/-! ## The one-bit lift -/

def enrichedObservation (r : Route) : (Z3 × Z3) × Bool :=
  (oldObservation r, nativeOrientation r)

theorem enriched_observation_is_injective : Function.Injective enrichedObservation := by
  intro r s h
  exact native_orientation_is_injective (congrArg Prod.snd h)

def decodeEnriched (o : (Z3 × Z3) × Bool) : Route :=
  if o.2 then .B else .A

/-- 3. The enriched observation has an explicit decoder. -/
theorem one_native_bit_suffices : ∀ r, decodeEnriched (enrichedObservation r) = r := by
  intro r
  cases r <;> decide

/-- Forgetting the orientation bit restores the old collapse. -/
theorem forgetting_the_bit_restores_blindness :
    (enrichedObservation .A).1 = (enrichedObservation .B).1 :=
  old_observation_collapses

/-! ## Minimality for two routes -/

def unitLift (r : Route) : (Z3 × Z3) × Unit := (oldObservation r, ())

theorem unit_lift_collapses : unitLift .A = unitLift .B := by
  rw [unitLift, unitLift, old_observation_collapses]

/-- 4a. An augmentation carrying no distinction cannot repair the decoder. -/
theorem no_decoder_from_unit_lift :
    ¬ ∃ decode : ((Z3 × Z3) × Unit) → Route, ∀ r, decode (unitLift r) = r := by
  intro h
  obtain ⟨decode, hd⟩ := h
  have hab : Route.A = Route.B := calc
    Route.A = decode (unitLift .A) := (hd .A).symm
    _ = decode (unitLift .B) := congrArg decode unit_lift_collapses
    _ = Route.B := hd .B
  exact Route.noConfusion hab

/-- 4b. Bool is enough, while Unit is not: one bit is minimal for this two-route task. -/
theorem one_bit_is_minimal_for_the_two_routes :
    (∃ encode : Route → Bool, Function.Injective encode) ∧
    ¬ (∃ encode : Route → Unit, Function.Injective encode) := by
  constructor
  · exact ⟨nativeOrientation, native_orientation_is_injective⟩
  · intro h
    obtain ⟨encode, hi⟩ := h
    have : Route.A = Route.B := hi (Subsingleton.elim _ _)
    exact Route.noConfusion this

/-! ## Red control: the bit's value does not certify its origin -/

/-- A glued-on answer that simply names which route was selected. -/
def declaredOrientation : Route → Bool
  | .A => false
  | .B => true

/-- 5a. Extentionally, the earned bit and the declared label are identical. -/
theorem native_bit_equals_declared_label : nativeOrientation = declaredOrientation := by
  funext r
  cases r <;> decide

inductive Origin
  | native
  | declared
deriving DecidableEq

structure BitPacket where
  bit : Bool
  origin : Origin
deriving DecidableEq

def nativePacket (r : Route) : BitPacket := ⟨nativeOrientation r, .native⟩
def declaredPacket (r : Route) : BitPacket := ⟨declaredOrientation r, .declared⟩
def eraseOrigin (p : BitPacket) : Bool := p.bit

/-- 5b. Erasing provenance makes the native and declared packets identical. -/
theorem erasing_origin_erases_the_difference :
    ∀ r, eraseOrigin (nativePacket r) = eraseOrigin (declaredPacket r) := by
  intro r
  change nativeOrientation r = declaredOrientation r
  exact congrFun native_bit_equals_declared_label r

/-- 5c. Retaining an origin field distinguishes the packets — but this field is only a
label here, not yet a certificate that the native computation was actually performed. -/
theorem retained_origin_distinguishes_packets :
    ∀ r, nativePacket r ≠ declaredPacket r := by
  intro r h
  have := congrArg BitPacket.origin h
  cases this

/-! ## Certificate -/

theorem one_bit_lift_certificate :
    oldObservation .A = oldObservation .B ∧
    (¬ ∃ decode : (Z3 × Z3) → Route, ∀ r, decode (oldObservation r) = r) ∧
    nativeBend .A = ⟨0, -1⟩ ∧ nativeBend .B = ⟨0, 1⟩ ∧
    Function.Injective enrichedObservation ∧
    (∀ r, decodeEnriched (enrichedObservation r) = r) ∧
    (¬ ∃ decode : ((Z3 × Z3) × Unit) → Route,
      ∀ r, decode (unitLift r) = r) ∧
    nativeOrientation = declaredOrientation ∧
    (∀ r, eraseOrigin (nativePacket r) = eraseOrigin (declaredPacket r)) ∧
    (∀ r, nativePacket r ≠ declaredPacket r) :=
  ⟨old_observation_collapses, no_decoder_from_old_observation,
   native_bends_are_opposite.1, native_bends_are_opposite.2,
   enriched_observation_is_injective, one_native_bit_suffices,
   no_decoder_from_unit_lift, native_bit_equals_declared_label,
   erasing_origin_erases_the_difference, retained_origin_distinguishes_packets⟩

#print axioms old_observation_collapses
#print axioms no_decoder_from_old_observation
#print axioms native_bends_are_opposite
#print axioms native_orientation_is_injective
#print axioms enriched_observation_is_injective
#print axioms one_native_bit_suffices
#print axioms forgetting_the_bit_restores_blindness
#print axioms no_decoder_from_unit_lift
#print axioms one_bit_is_minimal_for_the_two_routes
#print axioms native_bit_equals_declared_label
#print axioms erasing_origin_erases_the_difference
#print axioms retained_origin_distinguishes_packets
#print axioms one_bit_lift_certificate

end FoundationStoneSixteenC
