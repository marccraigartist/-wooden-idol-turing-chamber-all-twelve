/-!
# THE NEW EYE ENTERS THE IDOL — FOUNDATION STONE TEST 16J

Runs in the Lean live editor with no imports (core Lean only).

This is an audited integration probe, not a claim that Stage 3 has already been
rewritten.  It copies the certified twelve-predicate interface used by Test 1
and installs Test 16I's native unsigned/signed geometric frame.

Lean certifies two sharply different facts.

LEGACY INTEGRATION
1. Replacing the frame type Phi by Phi x NativeFrame preserves B1-B5 and
   B7-B12.  This is exact, for all systems.
2. Legacy B6 then holds.  But it holds without using any geometry: even an
   arbitrary Bool tag would do.  Therefore an All12 green obtained only this
   way is a projection green, not evidence that the new eye interacts with the
   Idol.

EARNED GEOMETRIC INTEGRATION
3. The old frame reads the two native 30-degree routes by unsigned chord and
   two-leg energy.  Those readings tie at the x-axis seat.
4. The successor frame adds the route's signed bend.  The bends are nonzero
   opposites, so the successor strictly refines the old frame.
5. Bend obeys the exchange transport law: it is native to the two-body change
   of frame.  A renderer's fixed up-coordinate also separates the routes, but
   fails that law and is rejected.
6. Hence the earned frame can coexist with any witness of the other eleven
   predicates.  What is not yet proved is mutual coupling: the old predicates
   cannot react to the frame because none of them mentions Phi.

Result: Test 16J closes the compatibility question and exposes the interface
debt.  A genuine Stage 3 integration must strengthen the signature so frame,
denotation, provenance or checking are linked.
-/
namespace FoundationStoneTest16J

/-! ## Part I — the certified twelve-predicate interface -/

def iter {X : Type} (T : X -> X) : Nat -> X -> X
  | 0, x => x
  | n + 1, x => T (iter T n x)

structure System where
  X : Type
  T : X -> X
  Phi : Type
  phi : Phi
  L : Type
  falsum : L
  con : L
  den : L -> X -> Prop
  Prf : L -> Prop
  R : X -> X -> Prop
  C : X -> X -> X
  interp : Nat -> X -> X -> Bool
  finuniversal : forall Q : X -> X -> Prop, (forall x y, Decidable (Q x y)) ->
    forall K : List X, exists e, forall x, x ∈ K -> forall y, y ∈ K ->
      interp e x y = true <-> Q x y

def Invariant {X : Type} (T : X -> X) (I : X -> Prop) : Prop :=
  forall x, I x -> I (T x)

def Reachable {X : Type} (T : X -> X) (x y : X) : Prop :=
  exists n, iter T n x = y

def CoOrbit {X : Type} (T : X -> X) (x y : X) : Prop :=
  exists n m, iter T n x = iter T m y

def Consistent (S : System) : Prop := ¬ S.Prf S.falsum

namespace System
def B1 (S : System) : Prop :=
  ¬ (exists e : Nat, forall x y, S.interp e x y = true <-> Reachable S.T x y)
def B2 (S : System) : Prop :=
  exists x : S.X, S.T x ≠ x /\
    forall ell : S.L, S.den ell x -> forall n, exists m, n < m /\ S.den ell (iter S.T m x)
def B3 (S : System) : Prop :=
  exists I : S.X -> Prop, Invariant S.T I /\
    (forall x, I x -> exists y, I y /\ S.T y = x) /\
    ¬ (exists ell : S.L, forall x, S.den ell x <-> I x)
def B4 (S : System) : Prop := forall x y, S.R x y <-> CoOrbit S.T x y
def B5 (S : System) : Prop := Consistent S /\ ¬ S.Prf S.con
def B6 (S : System) : Prop := exists phi' : S.Phi, phi' ≠ S.phi
def B7 (S : System) : Prop := exists F : S.X -> S.X, forall x, F x ≠ x
def B8 (S : System) : Prop :=
  exists K : S.X -> Prop, (exists a, K a) /\ (exists b, ¬ K b) /\
    (forall x y, K x -> K (S.C x y)) /\
    (forall x y, K (S.C x y) -> K x \/ K y)
def B9 (S : System) : Prop := forall x, S.T x ≠ x
def B10 (S : System) : Prop :=
  Function.Injective S.T /\ exists ell : S.L, exists x, S.den ell x /\
    ¬ (forall y, S.den ell y)
def B11 (S : System) : Prop :=
  exists I : S.X -> Prop, Invariant S.T I /\
    I ≠ (fun _ => False) /\ I ≠ (fun _ => True) /\
    ¬ (exists ell : S.L, forall x, S.den ell x <-> I x)
def B12 (S : System) : Prop :=
  forall x, exists n y, 0 < n /\ iter S.T n x = y /\ S.T y ≠ y
end System

structure All12 (S : System) : Prop where
  b1 : S.B1
  b2 : S.B2
  b3 : S.B3
  b4 : S.B4
  b5 : S.B5
  b6 : S.B6
  b7 : S.B7
  b8 : S.B8
  b9 : S.B9
  b10 : S.B10
  b11 : S.B11
  b12 : S.B12

structure AllBut6 (S : System) : Prop where
  b1 : S.B1
  b2 : S.B2
  b3 : S.B3
  b4 : S.B4
  b5 : S.B5
  b7 : S.B7
  b8 : S.B8
  b9 : S.B9
  b10 : S.B10
  b11 : S.B11
  b12 : S.B12

/-! ## Part II — the native geometry, compressed from Test 16I -/

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

def rzP (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.y, zadd v.x (zroot v.y), zscale 2 v.z⟩
def ryP (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩

def A (v : V3) : V3 := ryP (rzP v)
def B (v : V3) : V3 := rzP (ryP v)
def exchange (v : V3) : V3 := ⟨zneg v.x, v.z, v.y⟩
def xPoint : V3 := ⟨zone, zzero, zzero⟩

def chordA (v : V3) : Z3 := normSq (vsub (A v) (vscale 4 v))
def chordB (v : V3) : Z3 := normSq (vsub (B v) (vscale 4 v))

def energyA (v : V3) : Z3 :=
  zadd (normSq (vsub (vscale 2 (rzP v)) (vscale 4 v)))
       (normSq (vsub (A v) (vscale 2 (rzP v))))
def energyB (v : V3) : Z3 :=
  zadd (normSq (vsub (vscale 2 (ryP v)) (vscale 4 v)))
       (normSq (vsub (B v) (vscale 2 (ryP v))))

def det3 (u v w : V3) : Z3 :=
  zadd (zadd (zmul u.x (zsub (zmul v.y w.z) (zmul v.z w.y)))
             (zmul u.y (zsub (zmul v.z w.x) (zmul v.x w.z))))
       (zmul u.z (zsub (zmul v.x w.y) (zmul v.y w.x)))

def bendA (v : V3) : Z3 := det3 v (rzP v) (A v)
def bendB (v : V3) : Z3 := det3 v (ryP v) (B v)
def upA (v : V3) : Z3 := (A v).z
def upB (v : V3) : Z3 := (B v).z

def CarriedAcross (fA fB : V3 -> Z3) : Prop :=
  forall v, fB (exchange v) = fA v

theorem bend_is_carried : CarriedAcross bendA bendB := by
  intro v
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, ⟨za, zb⟩⟩ := v
  simp only [bendA, bendB, det3, exchange, A, B, rzP, ryP,
    zadd, zneg, zsub, zscale, zroot, zmul, Z3.mk.injEq]
  constructor <;> grind

theorem native_unsigned_tie :
    chordA xPoint = chordB xPoint /\ energyA xPoint = energyB xPoint := by
  decide

theorem native_bend_separates :
    bendA xPoint = ⟨0, -1⟩ /\ bendB xPoint = ⟨0, 1⟩ := by
  decide

theorem native_bend_differs : bendA xPoint ≠ bendB xPoint := by
  rw [native_bend_separates.1, native_bend_separates.2]
  decide

theorem up_separates_but_is_not_carried :
    upA xPoint ≠ upB xPoint /\ ¬ CarriedAcross upA upB := by
  constructor
  · decide
  · intro h
    have hx := h xPoint
    exact (by decide : upB (exchange xPoint) ≠ upA xPoint) hx

/-! ## Part III — earned refinement -/

inductive Route
  | zThenY
  | yThenZ
deriving DecidableEq

def unsignedReading : Route -> Z3 × Z3
  | .zThenY => (chordA xPoint, energyA xPoint)
  | .yThenZ => (chordB xPoint, energyB xPoint)

def signedReading : Route -> (Z3 × Z3) × Z3
  | .zThenY => (unsignedReading .zThenY, bendA xPoint)
  | .yThenZ => (unsignedReading .yThenZ, bendB xPoint)

def Refines {New Old : Type} (new : Route -> New) (old : Route -> Old) : Prop :=
  forall r s, new r = new s -> old r = old s

def StrictlyRefines {New Old : Type} (new : Route -> New) (old : Route -> Old) : Prop :=
  Refines new old /\ ¬ Refines old new

theorem native_signed_strictly_refines_unsigned :
    StrictlyRefines signedReading unsignedReading := by
  constructor
  · intro r s h
    cases r <;> cases s <;> simp_all [signedReading]
  · intro h
    have hu : unsignedReading .zThenY = unsignedReading .yThenZ := by
      apply Prod.ext
      · exact native_unsigned_tie.1
      · exact native_unsigned_tie.2
    have hs := h .zThenY .yThenZ hu
    exact native_bend_differs (congrArg Prod.snd hs)

inductive NativeFrame
  | unsigned
  | signed
deriving DecidableEq

def NativeEarnedB6 : Prop :=
  StrictlyRefines signedReading unsignedReading /\
  CarriedAcross bendA bendB /\
  bendA xPoint ≠ bendB xPoint

theorem native_earned_B6 : NativeEarnedB6 :=
  ⟨native_signed_strictly_refines_unsigned, bend_is_carried, native_bend_differs⟩

/-! ## Part IV — install the frame and audit all twelve -/

def reframe (S : System) : System where
  X := S.X
  T := S.T
  Phi := S.Phi × NativeFrame
  phi := (S.phi, .unsigned)
  L := S.L
  falsum := S.falsum
  con := S.con
  den := S.den
  Prf := S.Prf
  R := S.R
  C := S.C
  interp := S.interp
  finuniversal := S.finuniversal

/-- The old B6 goes green without consulting the geometry.  This is the
projection-green warning, formalised. -/
theorem legacy_B6_is_cheap (S : System) : (reframe S).B6 := by
  refine ⟨(S.phi, .signed), ?_⟩
  intro h
  have hf := congrArg Prod.snd h
  contradiction

/-- Stronger red control: an entirely content-free Bool tag also satisfies the
old B6. -/
def boolTag (S : System) : System where
  X := S.X
  T := S.T
  Phi := S.Phi × Bool
  phi := (S.phi, false)
  L := S.L
  falsum := S.falsum
  con := S.con
  den := S.den
  Prf := S.Prf
  R := S.R
  C := S.C
  interp := S.interp
  finuniversal := S.finuniversal

theorem arbitrary_tag_satisfies_legacy_B6 (S : System) : (boolTag S).B6 := by
  refine ⟨(S.phi, true), ?_⟩
  intro h
  have hf := congrArg Prod.snd h
  contradiction

/-- All eleven other predicates survive exactly because their definitions do
not inspect Phi or phi. -/
theorem reframe_keeps_other_eleven (S : System) (h : AllBut6 S) :
    AllBut6 (reframe S) := by
  exact ⟨h.b1, h.b2, h.b3, h.b4, h.b5, h.b7, h.b8, h.b9, h.b10, h.b11, h.b12⟩

theorem legacy_all12_after_reframe (S : System) (h : AllBut6 S) :
    All12 (reframe S) := by
  have k := reframe_keeps_other_eleven S h
  exact ⟨k.b1, k.b2, k.b3, k.b4, k.b5, legacy_B6_is_cheap S,
    k.b7, k.b8, k.b9, k.b10, k.b11, k.b12⟩

/-- The honest certificate records both facts: legacy compatibility and the
independent native evidence that makes this particular frame earned. -/
def EarnedIntegration (S : System) : Prop :=
  All12 (reframe S) /\ NativeEarnedB6 /\
    (upA xPoint ≠ upB xPoint /\ ¬ CarriedAcross upA upB)

theorem earned_B6_coexists_with_the_other_eleven (S : System) (h : AllBut6 S) :
    EarnedIntegration S :=
  ⟨legacy_all12_after_reframe S h, native_earned_B6,
   up_separates_but_is_not_carried⟩

/-! ## Certificate -/

theorem test_16J_certificate :
    NativeEarnedB6 /\
    (forall S : System, S.B6 -> (reframe S).B6) /\
    (forall S : System, AllBut6 S -> AllBut6 (reframe S)) /\
    (forall S : System, AllBut6 S -> EarnedIntegration S) /\
    (forall S : System, (boolTag S).B6) /\
    (upA xPoint ≠ upB xPoint /\ ¬ CarriedAcross upA upB) :=
  ⟨native_earned_B6,
   fun S _ => legacy_B6_is_cheap S,
   reframe_keeps_other_eleven,
   earned_B6_coexists_with_the_other_eleven,
   arbitrary_tag_satisfies_legacy_B6,
   up_separates_but_is_not_carried⟩

#print axioms bend_is_carried
#print axioms native_unsigned_tie
#print axioms native_bend_separates
#print axioms native_signed_strictly_refines_unsigned
#print axioms native_earned_B6
#print axioms legacy_B6_is_cheap
#print axioms arbitrary_tag_satisfies_legacy_B6
#print axioms reframe_keeps_other_eleven
#print axioms legacy_all12_after_reframe
#print axioms earned_B6_coexists_with_the_other_eleven
#print axioms up_separates_but_is_not_carried
#print axioms test_16J_certificate

end FoundationStoneTest16J
