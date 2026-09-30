/-!
# THE FOUNDATION STONE — TEST 2X: THE PRICE OF POLARITY

Runs in the Lean live editor with no imports (core Lean only). Written as input to
Charlie's Test 2B (native or installed?). It asks the expressiveness question directly.

Order of results:
1. GENERAL. A reversed language can name neither "always" nor "never".
2. GENERAL. Reversal is impossible in any language with negation and conjunction: the
   moment a language can say "A and not A", some reading fails to reverse. A polar
   language can never be a Boolean logic — and Tarski's languages are Boolean.
3. GENERAL. When two readings both reverse, "they agree" is left unchanged by the flip.
   So any connective that compares two polar readings names an invariant.
4. THE CLOCK (Marc's pre-existing structure, recorded in July):
   a. the magenta line is the ONLY symmetry of the twelve-gon that reverses the truth
      chart — no other mirror, no rotation;
   b. every gap mirror reverses parity (odd / even seats);
   c. chart and parity disagree at exactly B4 and B7 — the known (4 7) swap;
   d. so "chart agrees with parity" is magenta-invariant and not constant: a language
      holding the two native readings and one connective names a magenta invariant,
      and reversal fails for it.
   Point (d) is FREE given (3): it is forced, not a new pattern in the Idol.

Seat `0` is B12; seats `1`–`11` are B1–B11. Magenta is `k ↦ 11 − k`.
-/
namespace PriceOfPolarity

/-- The flip reverses every reading. -/
def ReversesReadings {X L : Type} (T : X → X) (den : L → X → Prop) : Prop :=
  ∀ ℓ x, den ℓ (T x) ↔ ¬ den ℓ x

/-- 1a. A reversed language cannot say "always". -/
theorem reversal_cannot_say_always {X L : Type} (T : X → X) (den : L → X → Prop)
    (hR : ReversesReadings T den) (x : X) : ¬ ∃ ℓ : L, ∀ y, den ℓ y := by
  intro ⟨ℓ, h⟩
  exact (hR ℓ x).mp (h (T x)) (h x)

/-- 1b. A reversed language cannot say "never". -/
theorem reversal_cannot_say_never {X L : Type} (T : X → X) (den : L → X → Prop)
    (hR : ReversesReadings T den) (x : X) : ¬ ∃ ℓ : L, ∀ y, ¬ den ℓ y := by
  intro ⟨ℓ, h⟩
  exact h (T x) ((hR ℓ x).mpr (h x))

/-- A language with negation and conjunction. -/
def HasNotAnd {X L : Type} (den : L → X → Prop) : Prop :=
  (∀ ℓ, ∃ ℓ' : L, ∀ y, den ℓ' y ↔ ¬ den ℓ y) ∧
  (∀ ℓ₁ ℓ₂, ∃ ℓ' : L, ∀ y, den ℓ' y ↔ den ℓ₁ y ∧ den ℓ₂ y)

/-- 2. Reversal is impossible in any language with negation and conjunction (given one
name and one point). -/
theorem reversal_forbids_boolean_language {X L : Type} (T : X → X) (den : L → X → Prop)
    (hR : ReversesReadings T den) (hB : HasNotAnd den) (ℓ : L) (x : X) : False := by
  obtain ⟨ℓn, hn⟩ := hB.1 ℓ
  obtain ⟨ℓa, ha⟩ := hB.2 ℓ ℓn
  have never : ∀ y, ¬ den ℓa y := fun y h =>
    let ⟨h1, h2⟩ := (ha y).mp h
    (hn y).mp h2 h1
  exact reversal_cannot_say_never T den hR x ⟨ℓa, never⟩

/-- 3. Two reversed readings: their agreement is left unchanged by the flip. -/
theorem polar_agreement_is_invariant {X : Type} (T : X → X) (A B : X → Prop)
    (hA : ∀ x, A (T x) ↔ ¬ A x) (hB : ∀ x, B (T x) ↔ ¬ B x) (x : X)
    (h : A x ↔ B x) : A (T x) ↔ B (T x) := by
  constructor
  · intro hTA
    exact (hB x).mpr fun hBx => (hA x).mp hTA (h.mpr hBx)
  · intro hTB
    exact (hA x).mpr fun hAx => (hB x).mp hTB (h.mp hAx)

/-! ## The clock -/

abbrev Seat := Fin 12

def magenta (k : Seat) : Seat := 11 - k

/-- The truth chart {B1, B3, B4, B5, B9, B11}. -/
def truthChart (k : Seat) : Bool :=
  match k.val with
  | 1 | 3 | 4 | 5 | 9 | 11 => true
  | _ => false

/-- Parity: the odd seats {B1, B3, B5, B7, B9, B11}. -/
def odd (k : Seat) : Bool := k.val % 2 == 1

/-- 4a. The magenta line is the only mirror that reverses the truth chart... -/
theorem only_magenta_mirror_reverses_the_chart :
    ∀ c : Seat, (∀ k : Seat, truthChart (c - k) = !truthChart k) ↔ c = 11 := by
  decide

/-- 4a'. ... and no rotation reverses it. -/
theorem no_rotation_reverses_the_chart :
    ∀ t : Seat, ¬ ∀ k : Seat, truthChart (k + t) = !truthChart k := by
  decide

/-- 4b. Every gap mirror (odd constant) reverses parity: magenta is one of six. -/
theorem every_gap_mirror_reverses_parity :
    ∀ c : Seat, c.val % 2 = 1 → ∀ k : Seat, odd (c - k) = !odd k := by
  decide

/-- 4c. Chart and parity disagree at exactly B4 and B7: the (4 7) swap. -/
theorem chart_and_parity_disagree_at_B4_B7 :
    ∀ k : Seat, truthChart k ≠ odd k ↔ (k = 4 ∨ k = 7) := by
  decide

/-- 4d. So "chart agrees with parity" is magenta-invariant and not constant. -/
theorem agreement_is_a_magenta_invariant :
    (∀ k : Seat, (truthChart (magenta k) == odd (magenta k)) = (truthChart k == odd k)) ∧
    (truthChart 0 == odd 0) = true ∧ (truthChart 4 == odd 4) = false := by
  decide

/-- Three native names: the chart, parity, and "the chart agrees with parity". -/
def threeReadings (ℓ : Fin 3) (k : Seat) : Prop :=
  match ℓ.val with
  | 0 => truthChart k = true
  | 1 => odd k = true
  | _ => (truthChart k == odd k) = true

/-- 4e. The first two names reverse under magenta... -/
theorem chart_and_parity_both_reverse :
    ∀ k : Seat, (truthChart (magenta k) = !truthChart k) ∧ (odd (magenta k) = !odd k) := by
  decide

/-- 4f. ...but once the language can compare them, reversal fails. -/
theorem comparison_breaks_reversal : ¬ ReversesReadings magenta threeReadings := by
  intro h
  have h0 := h 2 0
  have e1 : threeReadings 2 (magenta 0) := show (truthChart 11 == odd 11) = true by decide
  have e2 : threeReadings 2 0 := show (truthChart 0 == odd 0) = true by decide
  exact h0.mp e1 e2

theorem price_of_polarity_certificate :
    (∀ c : Seat, (∀ k : Seat, truthChart (c - k) = !truthChart k) ↔ c = 11) ∧
    (∀ c : Seat, c.val % 2 = 1 → ∀ k : Seat, odd (c - k) = !odd k) ∧
    (∀ k : Seat, truthChart k ≠ odd k ↔ (k = 4 ∨ k = 7)) ∧
    ¬ ReversesReadings magenta threeReadings :=
  ⟨only_magenta_mirror_reverses_the_chart, every_gap_mirror_reverses_parity,
   chart_and_parity_disagree_at_B4_B7, comparison_breaks_reversal⟩

#print axioms reversal_cannot_say_always
#print axioms reversal_cannot_say_never
#print axioms reversal_forbids_boolean_language
#print axioms polar_agreement_is_invariant
#print axioms only_magenta_mirror_reverses_the_chart
#print axioms no_rotation_reverses_the_chart
#print axioms every_gap_mirror_reverses_parity
#print axioms chart_and_parity_disagree_at_B4_B7
#print axioms agreement_is_a_magenta_invariant
#print axioms comparison_breaks_reversal
#print axioms price_of_polarity_certificate

end PriceOfPolarity
