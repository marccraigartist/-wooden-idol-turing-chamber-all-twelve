import FoundationStoneTest3

/-!
# THE FOUNDATION STONE — TEST 4: THE LANGUAGE TURNS WITH THE WALL

Test 3 assigned each primitive reading a mode: chart readings reverse and address
readings remain stable.  Test 4 removes that external classification.  It builds a
Boolean language and lets the magenta move act on the language itself.

Truth is transported to Discovery; Discovery to Truth; address provenance is fixed;
and transport commutes with NOT, AND and OR.  The main equivariance theorem says:

    evaluate (transport sentence) at point
      ↔ evaluate sentence at (magenta moves point).

A mixed sentence, `Truth AND address-even`, is neither globally reversing nor globally
stable.  Nevertheless it has the exact lawful destination `Discovery AND address-even`.
Thus the typed split from Test 3 was not the final structure: the stronger structure is
an involutive action on descriptions.

The expanded formula wall is freshly checked against all twelve Stage 2 predicates.
Its B3/B11 witness remains `address = 0`.  The Boolean language cannot name that set
because it sees only address parity: addresses 0 and 2 are observationally identical.

This is an equivariance and expressiveness result.  It is not Gödel, Tarski, Turing,
undecidability, or a P-versus-NP result.
-/

namespace FoundationStoneTestFour

open FoundationStoneTestTwo
open FoundationStoneTestThree

inductive Formula
  | truth
  | discovery
  | addressEven
  | top
  | bot
  | neg (body : Formula)
  | and (left right : Formula)
  | or (left right : Formula)
deriving DecidableEq

def evalFormula : Formula → NativePoint → Prop
  | .truth, p => nativeDen .truth p
  | .discovery, p => nativeDen .discovery p
  | .addressEven, p => nativeEvenAddress p
  | .top, _ => True
  | .bot, _ => False
  | .neg body, p => ¬ evalFormula body p
  | .and left right, p => evalFormula left p ∧ evalFormula right p
  | .or left right, p => evalFormula left p ∨ evalFormula right p

/-- The language's own magenta action. -/
def transport : Formula → Formula
  | .truth => .discovery
  | .discovery => .truth
  | .addressEven => .addressEven
  | .top => .top
  | .bot => .bot
  | .neg body => .neg (transport body)
  | .and left right => .and (transport left) (transport right)
  | .or left right => .or (transport left) (transport right)

/-- The central GREEN result: moving descriptions is exactly moving their points. -/
theorem transport_semantics (sentence : Formula) (p : NativePoint) :
    evalFormula (transport sentence) p ↔ evalFormula sentence (nativeTurn p) := by
  induction sentence with
  | truth =>
      rcases p with ⟨n, k⟩
      fin_cases k <;> simp [transport, evalFormula, nativeDen, chartDen,
        nativeTurn, magenta, truthChart]
  | discovery =>
      rcases p with ⟨n, k⟩
      fin_cases k <;> simp [transport, evalFormula, nativeDen, chartDen,
        nativeTurn, magenta, truthChart]
  | addressEven => rfl
  | top => simp [transport, evalFormula]
  | bot => simp [transport, evalFormula]
  | neg body ih => simp [transport, evalFormula, ih]
  | and left right ihLeft ihRight => simp [transport, evalFormula, ihLeft, ihRight]
  | or left right ihLeft ihRight => simp [transport, evalFormula, ihLeft, ihRight]

/-- Two language turns return the exact syntax, not merely an equivalent meaning. -/
theorem transport_twice : ∀ sentence : Formula,
    transport (transport sentence) = sentence := by
  intro sentence
  induction sentence <;> simp_all [transport]

theorem transport_bijective : Function.Bijective transport := by
  constructor
  · intro a b h
    have := congrArg transport h
    simpa [transport_twice] using this
  · intro sentence
    exact ⟨transport sentence, transport_twice sentence⟩

theorem transport_neg (sentence : Formula) :
    transport (.neg sentence) = .neg (transport sentence) := rfl

theorem transport_and (left right : Formula) :
    transport (.and left right) = .and (transport left) (transport right) := rfl

theorem transport_or (left right : Formula) :
    transport (.or left right) = .or (transport left) (transport right) := rfl

def FormulaReverses (sentence : Formula) : Prop :=
  ∀ p, evalFormula sentence (nativeTurn p) ↔ ¬ evalFormula sentence p

def FormulaStable (sentence : Formula) : Prop :=
  ∀ p, evalFormula sentence (nativeTurn p) ↔ evalFormula sentence p

/-- The first genuinely mixed reading. -/
def mixed : Formula := .and .truth .addressEven

theorem mixed_transport : transport mixed = .and .discovery .addressEven := rfl

/-- RED 1: the mixed sentence is not globally stable. -/
theorem mixed_is_not_stable : ¬ FormulaStable mixed := by
  intro h
  have bad := h ((0, (1 : Seat)) : NativePoint)
  simp [mixed, evalFormula, nativeDen, chartDen, nativeEvenAddress,
    nativeTurn, magenta, truthChart] at bad

/-- RED 2: the mixed sentence is not globally reversing either. -/
theorem mixed_is_not_reversing : ¬ FormulaReverses mixed := by
  intro h
  have bad := h ((1, (0 : Seat)) : NativePoint)
  simp [mixed, evalFormula, nativeDen, chartDen, nativeEvenAddress,
    nativeTurn, magenta, truthChart] at bad

/-- Yet the mixed sentence has a completely determined semantic destination. -/
theorem mixed_has_lawful_destination (p : NativePoint) :
    evalFormula (.and .discovery .addressEven) p ↔
      evalFormula mixed (nativeTurn p) := by
  simpa [mixed_transport] using transport_semantics mixed p

/-- Formulae see address parity, not the exact address: 0 and 2 look identical. -/
theorem zero_and_two_are_indistinguishable (sentence : Formula) (seat : Seat) :
    evalFormula sentence ((0, seat) : NativePoint) ↔
      evalFormula sentence ((2, seat) : NativePoint) := by
  induction sentence with
  | truth => rfl
  | discovery => rfl
  | addressEven => simp [evalFormula, nativeEvenAddress]
  | top => simp [evalFormula]
  | bot => simp [evalFormula]
  | neg body ih => simp [evalFormula, ih]
  | and left right ihLeft ihRight => simp [evalFormula, ihLeft, ihRight]
  | or left right ihLeft ihRight => simp [evalFormula, ihLeft, ihRight]

theorem address_zero_is_not_formula_named :
    ¬ ∃ sentence : Formula, ∀ p, evalFormula sentence p ↔ addressZero p := by
  rintro ⟨sentence, h⟩
  have hzero : evalFormula sentence ((0, (0 : Seat)) : NativePoint) :=
    (h _).mpr (by simp [addressZero])
  have htwo : evalFormula sentence ((2, (0 : Seat)) : NativePoint) :=
    (zero_and_two_are_indistinguishable sentence 0).mp hzero
  exact (by simpa [addressZero] using (h _).mp htwo)

def FormulaWall : System where
  X := NativePoint
  T := nativeTurn
  Φ := Bool
  φ := true
  L := Formula
  falsum := .bot
  con := .top
  den := evalFormula
  Prf := fun _ => False
  R := CoOrbit nativeTurn
  C := fun x _ => x
  interp := nativeInterp
  finuniversal := native_finite_universal

/-- Fresh B1 proof: no inheritance from the earlier walls. -/
theorem formula_B1 : FormulaWall.B1 := by
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

theorem formula_B2 : FormulaWall.B2 := by
  refine ⟨(0, (1 : Seat)), native_turn_ne _, ?_⟩
  intro sentence hs n
  refine ⟨2 * (n + 1), by omega, ?_⟩
  change evalFormula sentence (iter nativeTurn (2 * (n + 1)) (0, (1 : Seat)))
  rw [native_turn_even]
  exact hs

theorem formula_B3 : FormulaWall.B3 :=
  ⟨addressZero, address_zero_invariant, address_zero_backward,
   address_zero_is_not_formula_named⟩

theorem formula_B4 : FormulaWall.B4 := fun _ _ => Iff.rfl

theorem formula_B5 : FormulaWall.B5 :=
  ⟨by simp [Consistent, FormulaWall], by simp [FormulaWall]⟩

theorem formula_B6 : FormulaWall.B6 := by
  refine ⟨false, ?_⟩
  change false ≠ true
  decide

theorem formula_B7 : FormulaWall.B7 := ⟨nativeTurn, native_turn_ne⟩

theorem formula_B8 : FormulaWall.B8 := by
  refine ⟨fun p => truthChart p.2 = true,
    ⟨(0, (1 : Seat)), by decide⟩, ⟨(0, (0 : Seat)), by decide⟩, ?_, ?_⟩
  · intro x y hx
    exact hx
  · intro x y hx
    exact Or.inl hx

theorem formula_B9 : FormulaWall.B9 := native_turn_ne

theorem formula_B10 : FormulaWall.B10 := by
  refine ⟨native_turn_injective, .truth, (0, (1 : Seat)), ?_, ?_⟩
  · simp [FormulaWall, evalFormula, nativeDen, chartDen, truthChart]
  · intro hall
    have hfalse : ¬ evalFormula .truth ((0, (0 : Seat)) : NativePoint) := by
      simp [evalFormula, nativeDen, chartDen, truthChart]
    exact hfalse (hall (0, 0))

theorem formula_B11 : FormulaWall.B11 := by
  refine ⟨addressZero, address_zero_invariant, ?_, ?_, address_zero_is_not_formula_named⟩
  · intro h
    have hz : addressZero ((0, (0 : Seat)) : NativePoint) := by simp [addressZero]
    exact (Iff.of_eq (congrFun h (0, (0 : Seat)))).mp hz
  · intro h
    have hn : ¬ addressZero ((1, (0 : Seat)) : NativePoint) := by simp [addressZero]
    exact hn ((Iff.of_eq (congrFun h (1, (0 : Seat)))).mpr trivial)

theorem formula_B12 : FormulaWall.B12 := by
  intro p
  exact ⟨1, nativeTurn p, by decide, rfl, native_turn_ne (nativeTurn p)⟩

theorem formula_all12 : All12 FormulaWall :=
  ⟨formula_B1, formula_B2, formula_B3, formula_B4, formula_B5, formula_B6,
   formula_B7, formula_B8, formula_B9, formula_B10, formula_B11, formula_B12⟩

/-- Test 4 certificate: compositional language action, fresh All12, and both red controls. -/
theorem foundation_stone_test_four :
    All12 FormulaWall ∧
    (∀ sentence p, evalFormula (transport sentence) p ↔
      evalFormula sentence (nativeTurn p)) ∧
    (∀ sentence, transport (transport sentence) = sentence) ∧
    Function.Bijective transport ∧
    transport mixed = .and .discovery .addressEven ∧
    ¬ FormulaStable mixed ∧
    ¬ FormulaReverses mixed :=
  ⟨formula_all12, transport_semantics, transport_twice, transport_bijective,
   mixed_transport, mixed_is_not_stable, mixed_is_not_reversing⟩

#print axioms transport_semantics
#print axioms transport_twice
#print axioms transport_bijective
#print axioms mixed_is_not_stable
#print axioms mixed_is_not_reversing
#print axioms mixed_has_lawful_destination
#print axioms zero_and_two_are_indistinguishable
#print axioms address_zero_is_not_formula_named
#print axioms formula_B1
#print axioms formula_B3
#print axioms formula_B11
#print axioms formula_all12
#print axioms foundation_stone_test_four

end FoundationStoneTestFour
