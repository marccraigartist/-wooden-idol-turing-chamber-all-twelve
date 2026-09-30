import FoundationStoneTest2B

/-!
# THE FOUNDATION STONE — TEST 3: THE TWO-LEVEL WALL

Test 2B found a real boundary: the magenta move reverses the truth/discovery chart, but
it leaves the infinite address untouched. Universal reversal therefore breaks as soon
as the language can speak about the address.

Test 3 asks whether that break is a defect or the beginning of the correct structure.
The answer is the latter, provided the language remembers which kind of reading it is:

* `polar` readings reverse under the move;
* `stable` readings survive the move.

Lean checks four things:
1. the exact magenta construction obeys this typed law;
2. both modes are genuinely occupied;
3. collapsing everything to reversal fails;
4. collapsing everything to invariance fails.

The richer two-level wall still satisfies all twelve Stage 2 predicates.  Its B3/B11
witness is now `address = 0`, which is deliberately absent from the three-name language.
This is an existence and separation result, not Gödel, Tarski, Turing, or P versus NP.
-/

namespace FoundationStoneTestThree

open FoundationStoneTestTwo

inductive ReadingMode
  | polar
  | stable
deriving DecidableEq

inductive LayeredName
  | chart (name : ChartName)
  | addressEven
deriving DecidableEq

def readingMode : LayeredName → ReadingMode
  | .chart _ => .polar
  | .addressEven => .stable

def layeredDen : LayeredName → NativePoint → Prop
  | .chart name, p => nativeDen name p
  | .addressEven, p => nativeEvenAddress p

/-- The law is selected by the kind of reading rather than falsely imposed on all names. -/
def ObeysReadingMode (T : NativePoint → NativePoint)
    (den : LayeredName → NativePoint → Prop) : Prop :=
  ∀ name p,
    match readingMode name with
    | .polar => den name (T p) ↔ ¬ den name p
    | .stable => den name (T p) ↔ den name p

/-- GREEN: magenta reverses chart readings and preserves the address reading. -/
theorem native_obeys_two_level_law : ObeysReadingMode nativeTurn layeredDen := by
  intro name p
  cases name with
  | chart name => exact native_lift_reverses name p
  | addressEven => rfl

theorem both_reading_modes_are_real :
    (∃ name, readingMode name = .polar) ∧ (∃ name, readingMode name = .stable) :=
  ⟨⟨.chart .truth, rfl⟩, ⟨.addressEven, rfl⟩⟩

def PreservesEveryReading (T : NativePoint → NativePoint)
    (den : LayeredName → NativePoint → Prop) : Prop :=
  ∀ name p, den name (T p) ↔ den name p

/-- RED 1: the stable address reading prevents the whole language being reversing. -/
theorem not_every_reading_reverses :
    ¬ ReversesReadings nativeTurn layeredDen := by
  intro h
  have bad := h .addressEven ((0, (0 : Seat)) : NativePoint)
  simp [layeredDen, nativeEvenAddress, nativeTurn] at bad

/-- RED 2: the truth reading prevents the whole language being invariant. -/
theorem not_every_reading_is_stable :
    ¬ PreservesEveryReading nativeTurn layeredDen := by
  intro h
  have bad := h (.chart .truth) ((0, (1 : Seat)) : NativePoint)
  simp [layeredDen, nativeDen, nativeTurn, chartDen, magenta, truthChart] at bad

def LayeredWall : System where
  X := NativePoint
  T := nativeTurn
  Φ := Bool
  φ := true
  L := LayeredName
  falsum := .chart .truth
  con := .chart .discovery
  den := layeredDen
  Prf := fun _ => False
  R := CoOrbit nativeTurn
  C := fun x _ => x
  interp := nativeInterp
  finuniversal := native_finite_universal

def addressZero (p : NativePoint) : Prop := p.1 = 0

theorem address_zero_invariant : Invariant nativeTurn addressZero := by
  intro p hp
  exact hp

theorem address_zero_backward (p : NativePoint) (hp : addressZero p) :
    ∃ q, addressZero q ∧ nativeTurn q = p :=
  ⟨nativeTurn p, hp, native_turn_twice p⟩

/-- No name in the deliberately small layered language says exactly `address = 0`. -/
theorem address_zero_is_not_named :
    ¬ ∃ name : LayeredName, ∀ p, layeredDen name p ↔ addressZero p := by
  rintro ⟨name, h⟩
  cases name with
  | chart name =>
      cases name with
      | truth =>
          have ht : layeredDen (.chart .truth) ((1, (1 : Seat)) : NativePoint) := by
            simp [layeredDen, nativeDen, chartDen, truthChart]
          have hz : ¬ addressZero ((1, (1 : Seat)) : NativePoint) := by
            simp [addressZero]
          exact hz ((h _).mp ht)
      | discovery =>
          have hd : layeredDen (.chart .discovery) ((1, (0 : Seat)) : NativePoint) := by
            simp [layeredDen, nativeDen, chartDen, truthChart]
          have hz : ¬ addressZero ((1, (0 : Seat)) : NativePoint) := by
            simp [addressZero]
          exact hz ((h _).mp hd)
  | addressEven =>
      have he : layeredDen .addressEven ((2, (0 : Seat)) : NativePoint) := by
        simp [layeredDen, nativeEvenAddress]
      have hz : ¬ addressZero ((2, (0 : Seat)) : NativePoint) := by
        simp [addressZero]
      exact hz ((h _).mp he)

theorem layered_B1 : LayeredWall.B1 := by
  rintro ⟨e, he⟩
  let ps := decodeNativePairs e
  have hsub : Set.range (fun k : Nat =>
      (((k, (0 : Seat)) : NativePoint), ((k, magenta 0) : NativePoint))) ⊆
      {z | z ∈ ps} := by
    rintro z ⟨k, rfl⟩
    have hr : Reachable nativeTurn (k, (0 : Seat)) (k, magenta 0) := ⟨1, rfl⟩
    have hb := (he (k, (0 : Seat)) (k, magenta 0)).mpr hr
    exact decide_eq_true_iff.mp hb
  have hfin : Set.Finite {z | z ∈ ps} := by
    simpa only [List.mem_toFinset] using (Set.finite_mem_finset ps.toFinset)
  have hrange : Set.Infinite (Set.range (fun k : Nat =>
      (((k, (0 : Seat)) : NativePoint), ((k, magenta 0) : NativePoint)))) := by
    apply Set.infinite_range_of_injective
    intro a b h
    exact congrArg (fun z : NativePoint × NativePoint => z.1.1) h
  exact hrange (hfin.subset hsub)

theorem layered_B2 : LayeredWall.B2 := by
  refine ⟨(0, (1 : Seat)), native_turn_ne _, ?_⟩
  intro name hname n
  refine ⟨2 * (n + 1), by omega, ?_⟩
  change layeredDen name (iter nativeTurn (2 * (n + 1)) (0, (1 : Seat)))
  rw [native_turn_even]
  exact hname

theorem layered_B3 : LayeredWall.B3 :=
  ⟨addressZero, address_zero_invariant, address_zero_backward, address_zero_is_not_named⟩

theorem layered_B4 : LayeredWall.B4 := fun _ _ => Iff.rfl

theorem layered_B5 : LayeredWall.B5 :=
  ⟨by simp [Consistent, LayeredWall], by simp [LayeredWall]⟩

theorem layered_B6 : LayeredWall.B6 := by
  refine ⟨false, ?_⟩
  change false ≠ true
  decide

theorem layered_B7 : LayeredWall.B7 := ⟨nativeTurn, native_turn_ne⟩

theorem layered_B8 : LayeredWall.B8 := by
  refine ⟨fun p => truthChart p.2 = true,
    ⟨(0, (1 : Seat)), by decide⟩, ⟨(0, (0 : Seat)), by decide⟩, ?_, ?_⟩
  · intro x y hx
    exact hx
  · intro x y hx
    exact Or.inl hx

theorem layered_B9 : LayeredWall.B9 := native_turn_ne

theorem layered_B10 : LayeredWall.B10 := by
  refine ⟨native_turn_injective, ?_⟩
  refine ⟨.chart .truth, (0, (1 : Seat)), ?_, ?_⟩
  · simp [LayeredWall, layeredDen, nativeDen, chartDen, truthChart]
  · intro hall
    have hfalse : ¬ layeredDen (.chart .truth) ((0, (0 : Seat)) : NativePoint) := by
      simp [layeredDen, nativeDen, chartDen, truthChart]
    exact hfalse (hall (0, 0))

theorem layered_B11 : LayeredWall.B11 := by
  refine ⟨addressZero, address_zero_invariant, ?_, ?_, address_zero_is_not_named⟩
  · intro h
    have hz : addressZero ((0, (0 : Seat)) : NativePoint) := by simp [addressZero]
    exact (Iff.of_eq (congrFun h (0, (0 : Seat)))).mp hz
  · intro h
    have hn : ¬ addressZero ((1, (0 : Seat)) : NativePoint) := by simp [addressZero]
    exact hn ((Iff.of_eq (congrFun h (1, (0 : Seat)))).mpr trivial)

theorem layered_B12 : LayeredWall.B12 := by
  intro p
  exact ⟨1, nativeTurn p, by decide, rfl, native_turn_ne (nativeTurn p)⟩

theorem layered_all12 : All12 LayeredWall :=
  ⟨layered_B1, layered_B2, layered_B3, layered_B4, layered_B5, layered_B6,
   layered_B7, layered_B8, layered_B9, layered_B10, layered_B11, layered_B12⟩

/-- Test 3 certificate: the typed split works, and both untyped collapses are rejected. -/
theorem foundation_stone_test_three :
    All12 LayeredWall ∧
    ObeysReadingMode nativeTurn layeredDen ∧
    (∃ name, readingMode name = .polar) ∧
    (∃ name, readingMode name = .stable) ∧
    ¬ ReversesReadings nativeTurn layeredDen ∧
    ¬ PreservesEveryReading nativeTurn layeredDen :=
  ⟨layered_all12, native_obeys_two_level_law,
   both_reading_modes_are_real.1, both_reading_modes_are_real.2,
   not_every_reading_reverses, not_every_reading_is_stable⟩

#print axioms native_obeys_two_level_law
#print axioms both_reading_modes_are_real
#print axioms not_every_reading_reverses
#print axioms not_every_reading_is_stable
#print axioms address_zero_is_not_named
#print axioms layered_B1
#print axioms layered_B3
#print axioms layered_B11
#print axioms layered_all12
#print axioms foundation_stone_test_three

end FoundationStoneTestThree
