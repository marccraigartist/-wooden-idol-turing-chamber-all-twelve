import Mathlib

/-!
# THE FOUNDATION STONE — TEST 2: CAN REVERSAL LIVE INSIDE ALL TWELVE?

This is the hard compatibility test suggested by Test 1.

It constructs one explicit infinite system `PolarWall` satisfying all twelve Stage 2
stations and the candidate principle

    den ℓ (T x) ↔ ¬ den ℓ x.

The language is not empty: it has one reading for every natural-number address, and each
reading distinguishes the two opposed sides at that address.  But the control results show
the price: no reading can be constant or name a `T`-invariant property.  Thus compatibility
is green, while Gödel/Tarski strength remains unearned.

`pairInterp` is a genuine finite-table codebook.  Every decidable relation can be matched
on every finite window, but no one finite table decides the infinite reachability relation.
-/

namespace FoundationStoneTestTwo

def iter {X : Type} (T : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => T (iter T n x)

structure System where
  X : Type
  T : X → X
  Φ : Type
  φ : Φ
  L : Type
  falsum : L
  con : L
  den : L → X → Prop
  Prf : L → Prop
  R : X → X → Prop
  C : X → X → X
  interp : Nat → X → X → Bool
  finuniversal : ∀ Q : X → X → Prop, (∀ x y, Decidable (Q x y)) →
    ∀ K : List X, ∃ e, ∀ x ∈ K, ∀ y ∈ K, interp e x y = true ↔ Q x y

def Invariant {X : Type} (T : X → X) (I : X → Prop) : Prop := ∀ x, I x → I (T x)
def Reachable {X : Type} (T : X → X) (x y : X) : Prop := ∃ n, iter T n x = y
def CoOrbit {X : Type} (T : X → X) (x y : X) : Prop := ∃ n m, iter T n x = iter T m y
def Consistent (S : System) : Prop := ¬ S.Prf S.falsum

namespace System
def B1 (S : System) : Prop := ¬ ∃ e : Nat, ∀ x y, S.interp e x y = true ↔ Reachable S.T x y
def B2 (S : System) : Prop :=
  ∃ x : S.X, S.T x ≠ x ∧
    ∀ ℓ : S.L, S.den ℓ x → ∀ n, ∃ m, n < m ∧ S.den ℓ (iter S.T m x)
def B3 (S : System) : Prop :=
  ∃ I : S.X → Prop, Invariant S.T I ∧
    (∀ x, I x → ∃ y, I y ∧ S.T y = x) ∧ ¬ ∃ ℓ : S.L, ∀ x, S.den ℓ x ↔ I x
def B4 (S : System) : Prop := ∀ x y, S.R x y ↔ CoOrbit S.T x y
def B5 (S : System) : Prop := Consistent S ∧ ¬ S.Prf S.con
def B6 (S : System) : Prop := ∃ φ' : S.Φ, φ' ≠ S.φ
def B7 (S : System) : Prop := ∃ F : S.X → S.X, ∀ x, F x ≠ x
def B8 (S : System) : Prop :=
  ∃ K : S.X → Prop, (∃ a, K a) ∧ (∃ b, ¬ K b) ∧
    (∀ x y, K x → K (S.C x y)) ∧ (∀ x y, K (S.C x y) → K x ∨ K y)
def B9 (S : System) : Prop := ∀ x, S.T x ≠ x
def B10 (S : System) : Prop :=
  Function.Injective S.T ∧ ∃ ℓ : S.L, ∃ x, S.den ℓ x ∧ ¬ ∀ y, S.den ℓ y
def B11 (S : System) : Prop :=
  ∃ I : S.X → Prop, Invariant S.T I ∧
    I ≠ (fun _ => False) ∧ I ≠ (fun _ => True) ∧ ¬ ∃ ℓ : S.L, ∀ x, S.den ℓ x ↔ I x
def B12 (S : System) : Prop := ∀ x, ∃ n y, 0 < n ∧ iter S.T n x = y ∧ S.T y ≠ y
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

def ReversesReadings {X L : Type} (T : X → X) (den : L → X → Prop) : Prop :=
  ∀ ℓ x, den ℓ (T x) ↔ ¬ den ℓ x

abbrev Point := Nat × Bool

def turn (p : Point) : Point := (p.1, !p.2)

theorem turn_ne (p : Point) : turn p ≠ p := by
  rcases p with ⟨n, b⟩
  intro h
  have hb : (!b) = b := congrArg Prod.snd h
  cases b <;> contradiction

theorem turn_injective : Function.Injective turn := by
  rintro ⟨n, a⟩ ⟨m, b⟩ h
  have hn : n = m := congrArg Prod.fst h
  have hb : (!a) = (!b) := congrArg Prod.snd h
  cases a <;> cases b <;> simp_all

theorem turn_twice (p : Point) : turn (turn p) = p := by
  rcases p with ⟨n, b⟩
  cases b <;> rfl

theorem turn_even (p : Point) : ∀ k, iter turn (2 * k) p = p
  | 0 => rfl
  | k + 1 => by
      show turn (turn (iter turn (2 * k) p)) = p
      rw [turn_twice, turn_even p k]

/-! ## A finite-table interpreter, enumerated by natural numbers -/

abbrev PairList := List (Point × Point)

def decodePairs (e : Nat) : PairList :=
  (Encodable.decode e : Option PairList).getD []

def pairInterp (e : Nat) (x y : Point) : Bool :=
  decide ((x, y) ∈ decodePairs e)

theorem decode_encode_pairs (ps : PairList) : decodePairs (Encodable.encode ps) = ps := by
  simp [decodePairs]

theorem pair_finite_universal :
    ∀ Q : Point → Point → Prop, (∀ x y, Decidable (Q x y)) →
      ∀ K : List Point, ∃ e, ∀ x ∈ K, ∀ y ∈ K, pairInterp e x y = true ↔ Q x y := by
  intro Q hQ K
  classical
  let ps : PairList := (K ×ˢ K).filter (fun z => Q z.1 z.2)
  refine ⟨Encodable.encode ps, ?_⟩
  intro x hx y hy
  rw [pairInterp, decode_encode_pairs, decide_eq_true_iff]
  simp [ps, hx, hy]

/-! ## The polar language: every address has a reading, and every reading flips -/

def polarDen (ℓ : Nat) (p : Point) : Prop :=
  p.2 = decide (p.1 = ℓ)

theorem polar_reverses : ReversesReadings turn polarDen := by
  intro ℓ p
  rcases p with ⟨n, b⟩
  unfold turn polarDen
  by_cases h : n = ℓ
  · simp [h]
  · simp [h]

theorem every_address_has_a_reading (n : Nat) :
    polarDen n (n, true) ∧ ¬ polarDen n (n, false) := by
  simp [polarDen]

theorem no_constant_true_reading : ¬ ∃ ℓ, ∀ p : Point, polarDen ℓ p := by
  rintro ⟨ℓ, h⟩
  exact (every_address_has_a_reading ℓ).2 (h (ℓ, false))

theorem no_constant_false_reading : ¬ ∃ ℓ, ∀ p : Point, ¬ polarDen ℓ p := by
  rintro ⟨ℓ, h⟩
  exact h (ℓ, true) (every_address_has_a_reading ℓ).1

def PolarWall : System where
  X := Point
  T := turn
  Φ := Bool
  φ := true
  L := Nat
  falsum := 0
  con := 1
  den := polarDen
  Prf := fun _ => False
  R := CoOrbit turn
  C := fun x _ => x
  interp := pairInterp
  finuniversal := pair_finite_universal

/-! ## Reversal controls -/

theorem reversal_hides_invariant
    (I : Point → Prop) (hI : Invariant turn I) (x : Point) :
    ¬ ∃ ℓ, ∀ y, polarDen ℓ y ↔ I y := by
  intro ⟨ℓ, hℓ⟩
  have hnx : ¬ I x := fun hx =>
    (polar_reverses ℓ x).mp ((hℓ (turn x)).mpr (hI x hx)) ((hℓ x).mpr hx)
  have hTx : I (turn x) :=
    (hℓ (turn x)).mp ((polar_reverses ℓ x).mpr fun hd => hnx ((hℓ x).mp hd))
  exact (polar_reverses ℓ (turn x)).mp
    ((hℓ (turn (turn x))).mpr (hI _ hTx)) ((hℓ (turn x)).mpr hTx)

def evenAddress (p : Point) : Prop := p.1 % 2 = 0

theorem even_invariant : Invariant turn evenAddress := by
  intro p hp
  exact hp

theorem even_backward (p : Point) (hp : evenAddress p) :
    ∃ q, evenAddress q ∧ turn q = p := by
  exact ⟨turn p, hp, turn_twice p⟩

theorem even_nonempty : evenAddress (0, false) := by simp [evenAddress]
theorem even_not_universal : ¬ evenAddress (1, false) := by simp [evenAddress]

/-! ## The twelve stations -/

theorem polar_B1 : PolarWall.B1 := by
  rintro ⟨e, he⟩
  let ps := decodePairs e
  have hsub : Set.range (fun k : Nat => ((k, false), (k, true))) ⊆
      {z | z ∈ ps} := by
    rintro z ⟨k, rfl⟩
    have hr : Reachable turn (k, false) (k, true) := ⟨1, rfl⟩
    have hb := (he (k, false) (k, true)).mpr hr
    exact decide_eq_true_iff.mp hb
  have hfin : Set.Finite {z | z ∈ ps} := by
    simpa only [List.mem_toFinset] using (Set.finite_mem_finset ps.toFinset)
  have hrange : Set.Infinite (Set.range (fun k : Nat => ((k, false), (k, true)))) := by
    apply Set.infinite_range_of_injective
    intro a b h
    exact congrArg (fun z : Point × Point => z.1.1) h
  exact hrange (hfin.subset hsub)

theorem polar_B2 : PolarWall.B2 := by
  refine ⟨(0, true), turn_ne _, ?_⟩
  intro ℓ hℓ n
  refine ⟨2 * (n + 1), by omega, ?_⟩
  change polarDen ℓ (iter turn (2 * (n + 1)) (0, true))
  rw [turn_even]
  exact hℓ

theorem polar_B3 : PolarWall.B3 := by
  refine ⟨evenAddress, even_invariant, even_backward, ?_⟩
  exact reversal_hides_invariant evenAddress even_invariant (0, false)

theorem polar_B4 : PolarWall.B4 := fun _ _ => Iff.rfl

theorem polar_B5 : PolarWall.B5 := ⟨by simp [Consistent, PolarWall], by simp [PolarWall]⟩

theorem polar_B6 : PolarWall.B6 := by
  refine ⟨false, ?_⟩
  change false ≠ true
  decide

theorem polar_B7 : PolarWall.B7 := ⟨turn, turn_ne⟩

theorem polar_B8 : PolarWall.B8 := by
  refine ⟨fun p => p.2 = true, ⟨(0, true), rfl⟩, ⟨(0, false), by decide⟩, ?_, ?_⟩
  · intro x y hx
    exact hx
  · intro x y hx
    exact Or.inl hx

theorem polar_B9 : PolarWall.B9 := turn_ne

theorem polar_B10 : PolarWall.B10 := by
  refine ⟨turn_injective, ?_⟩
  show ∃ ℓ : Nat, ∃ x : Point, polarDen ℓ x ∧ ¬ ∀ y, polarDen ℓ y
  refine ⟨0, (0, true), (every_address_has_a_reading 0).1, ?_⟩
  intro hall
  exact (every_address_has_a_reading 0).2 (hall (0, false))

theorem polar_B11 : PolarWall.B11 := by
  refine ⟨evenAddress, even_invariant, ?_, ?_, ?_⟩
  · intro h
    exact (Iff.of_eq (congrFun h (0, false))).mp even_nonempty
  · intro h
    exact even_not_universal ((Iff.of_eq (congrFun h (1, false))).mpr trivial)
  · exact reversal_hides_invariant evenAddress even_invariant (0, false)

theorem polar_B12 : PolarWall.B12 := by
  intro p
  exact ⟨1, turn p, by decide, rfl, turn_ne (turn p)⟩

theorem polar_all12 : All12 PolarWall :=
  ⟨polar_B1, polar_B2, polar_B3, polar_B4, polar_B5, polar_B6,
   polar_B7, polar_B8, polar_B9, polar_B10, polar_B11, polar_B12⟩

/-! ## TEST 2 result and its red control -/

/-- GREEN: reversal is consistent with all twelve in one explicit infinite model. -/
theorem reversal_can_live_inside_all_twelve :
    ∃ S : System, All12 S ∧ ReversesReadings S.T S.den :=
  ⟨PolarWall, polar_all12, polar_reverses⟩

/-- RED: the same principle prevents the language from naming even the constant truths. -/
theorem reversal_price :
    (¬ ∃ ℓ, ∀ p : Point, PolarWall.den ℓ p) ∧
    (¬ ∃ ℓ, ∀ p : Point, ¬ PolarWall.den ℓ p) ∧
    (¬ ∃ ℓ, ∀ p : Point, PolarWall.den ℓ p ↔ evenAddress p) :=
  ⟨no_constant_true_reading, no_constant_false_reading,
   reversal_hides_invariant evenAddress even_invariant (0, false)⟩

/-- The honest certificate: compatibility, nonempty address-indexed language, and price. -/
theorem foundation_stone_test_two :
    (∃ S : System, All12 S ∧ ReversesReadings S.T S.den) ∧
    (∀ n, polarDen n (n, true) ∧ ¬ polarDen n (n, false)) ∧
    (¬ ∃ ℓ, ∀ p : Point, PolarWall.den ℓ p) ∧
    (¬ ∃ ℓ, ∀ p : Point, ¬ PolarWall.den ℓ p) :=
  ⟨reversal_can_live_inside_all_twelve, every_address_has_a_reading,
   no_constant_true_reading, no_constant_false_reading⟩

#print axioms pair_finite_universal
#print axioms polar_B1
#print axioms polar_reverses
#print axioms polar_all12
#print axioms reversal_can_live_inside_all_twelve
#print axioms reversal_price
#print axioms foundation_stone_test_two

end FoundationStoneTestTwo
