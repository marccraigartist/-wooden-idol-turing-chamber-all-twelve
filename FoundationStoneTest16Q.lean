/-!
# THE ALIGNMENT SPECTRUM — FOUNDATION STONE TEST 16Q

Core Lean only; no imports.

Test 16P found that the two counter-rotating twelve-seat helices physically
align after exactly three and nine completed transfers.  This test replaces
12 by an arbitrary clock size and asks which part of that result belongs to
twelve.

At a boundary after `n` units have moved out of a total of `N`:

* A's descending clock reads `(N - n) mod N`;
* B's ascending local clock reads `n mod N`;
* when an antipodal frame exists, B translated into A's frame reads
  `(n + N/2) mod N`.

Lean certifies:

1. an exact antipodal frame exists for every even clock and for no odd clock;
2. for `N = 4k`, the translated readings align exactly at `n = k` and
   `n = 3k`: the quarter and three-quarter boundaries;
3. for `N = 4k + 2`, they never align—not even though the antipodal frame
   itself exists;
4. `N = 12` therefore recovers Test 16P's `3, 9`, while `N = 10` has none;
5. red control: without the antipodal translation, the twelve-clock alignment
   set changes to `0, 6, 12`, so the quarter points are not an artefact of two
   clocks merely counter-rotating;
6. prime-sized clocks supply no alignment in this scheme: every odd size has
   no antipodal frame, and the only even prime size, `N = 2`, is in the
   `4k+2` no-alignment class.  This is a parity consequence, not a special
   prime-number mechanism.

The result is the exact congruence `2n = N/2 (mod N)`.  It is solvable exactly
when `N/2` is even, equivalently when four divides `N`.  Twelve is therefore
the first nontrivial clock that also carries Marc's threefold/weld structure,
but the two physical alignments belong to the whole `4k` spectrum.
-/

namespace FoundationStoneTest16Q

/-! ## 1. The general clock readings -/

/-- A's reading after `n` units have left an initial height `N`. -/
def aReading (N n : Nat) : Nat := (N - n) % N

/-- B's local ascending reading. -/
def bLocalReading (N n : Nat) : Nat := n % N

/-- B's local reading translated by a proposed half-turn into A's frame. -/
def bInAFrame (N half n : Nat) : Nat := (n + half) % N

/-- The two physical directions agree after translating B into A's frame. -/
def Aligned (N half n : Nat) : Prop :=
  aReading N n = bInAFrame N half n

/-- A clock admits an exact antipodal frame when some offset doubled is `N`. -/
def HasAntipodalFrame (N : Nat) : Prop := ∃ half, 2 * half = N

theorem every_even_clock_has_an_antipodal_frame (m : Nat) :
    HasAntipodalFrame (2 * m) := by
  exact ⟨m, by omega⟩

theorem no_odd_clock_has_an_antipodal_frame (k : Nat) :
    ¬ HasAntipodalFrame (2 * k + 1) := by
  intro h
  obtain ⟨half, hh⟩ := h
  omega

/-! ## 2. Exact modular normal forms -/

/-- Below the half-turn, adding the half-turn does not wrap. -/
theorem add_half_lower (m n : Nat) (_hm : 0 < m) (hn : n < m) :
    (n + m) % (2 * m) = n + m := by
  apply Nat.mod_eq_of_lt
  omega

/-- Above the half-turn but below one revolution, adding it wraps once. -/
theorem add_half_upper (m n : Nat) (_hm : 0 < m) (hlo : m ≤ n)
    (hhi : n < 2 * m) :
    (n + m) % (2 * m) = n - m := by
  have he : n + m = (n - m) + 2 * m := by omega
  rw [he, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- Inside a revolution, the descending reading has not wrapped. -/
theorem backward_inside (m n : Nat) (_hm : 0 < m) (hn0 : 0 < n)
    (hn : n < 2 * m) :
    (2 * m - n) % (2 * m) = 2 * m - n := by
  apply Nat.mod_eq_of_lt
  omega

/-! ## 3. The alignment spectrum -/

/-- If four divides the clock size, there are exactly two physical alignments:
the quarter and three-quarter boundaries. -/
theorem four_multiple_alignment_spectrum (k n : Nat) (hk : 0 < k)
    (hn : n ≤ 4 * k) :
    Aligned (4 * k) (2 * k) n ↔ n = k ∨ n = 3 * k := by
  unfold Aligned aReading bInAFrame
  constructor
  · intro h
    by_cases hn0 : n = 0
    · subst n
      have h2 : (2 * k) % (4 * k) = 2 * k := Nat.mod_eq_of_lt (by omega)
      simp only [Nat.sub_zero, Nat.mod_self, Nat.zero_add, h2] at h
      omega
    by_cases hn4 : n = 4 * k
    · subst n
      have h1 : (4 * k - 4 * k) % (4 * k) = 0 := by simp
      have h2 : (4 * k + 2 * k) % (4 * k) = 2 * k := by
        have he : 4 * k + 2 * k = 2 * k + 4 * k := by omega
        rw [he, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1, h2] at h
      omega
    have hnlt : n < 4 * k := by omega
    have hl := backward_inside (2 * k) n (by omega) (by omega) (by omega)
    rw [show 2 * (2 * k) = 4 * k by omega] at hl
    rw [hl] at h
    by_cases hhalf : n < 2 * k
    · have hr := add_half_lower (2 * k) n (by omega) hhalf
      rw [show 2 * (2 * k) = 4 * k by omega] at hr
      rw [hr] at h
      left
      omega
    · have hr := add_half_upper (2 * k) n (by omega) (by omega) (by omega)
      rw [show 2 * (2 * k) = 4 * k by omega] at hr
      rw [hr] at h
      right
      omega
  · intro h
    rcases h with he | he
    · subst n
      have h1 : (4 * k - k) % (4 * k) = 3 * k := by
        have heq : 4 * k - k = 3 * k := by omega
        rw [heq]
        exact Nat.mod_eq_of_lt (by omega)
      have h2 : (k + 2 * k) % (4 * k) = 3 * k := by
        have heq : k + 2 * k = 3 * k := by omega
        rw [heq]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1, h2]
    · subst n
      have h1 : (4 * k - 3 * k) % (4 * k) = k := by
        have heq : 4 * k - 3 * k = k := by omega
        rw [heq]
        exact Nat.mod_eq_of_lt (by omega)
      have h2 := add_half_upper (2 * k) (3 * k) (by omega) (by omega) (by omega)
      rw [show 2 * (2 * k) = 4 * k by omega] at h2
      rw [h1, h2]
      omega

/-- If the clock is even but not divisible by four, its antipodal frame exists
but the two counter-rotating readings never physically align. -/
theorem two_mod_four_has_no_alignment (k n : Nat) (hn : n ≤ 4 * k + 2) :
    ¬ Aligned (4 * k + 2) (2 * k + 1) n := by
  unfold Aligned aReading bInAFrame
  intro h
  let m := 2 * k + 1
  have hm : 0 < m := by omega
  have hN : 2 * m = 4 * k + 2 := by omega
  by_cases hn0 : n = 0
  · subst n
    have h2 : (2 * k + 1) % (4 * k + 2) = 2 * k + 1 :=
      Nat.mod_eq_of_lt (by omega)
    simp only [Nat.sub_zero, Nat.mod_self, Nat.zero_add, h2] at h
    omega
  by_cases hnN : n = 4 * k + 2
  · subst n
    have h1 : (4 * k + 2 - (4 * k + 2)) % (4 * k + 2) = 0 := by simp
    have h2 : ((4 * k + 2) + (2 * k + 1)) % (4 * k + 2) = 2 * k + 1 := by
      have he : (4 * k + 2) + (2 * k + 1) = (2 * k + 1) + (4 * k + 2) := by omega
      rw [he, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h2] at h
    omega
  have hnlt : n < 2 * m := by omega
  have hl := backward_inside m n hm (by omega) hnlt
  rw [hN] at hl
  rw [hl] at h
  by_cases hhalf : n < m
  · have hr := add_half_lower m n hm hhalf
    rw [hN] at hr
    rw [hr] at h
    dsimp [m] at h
    omega
  · have hr := add_half_upper m n hm (by omega) hnlt
    rw [hN] at hr
    rw [hr] at h
    dsimp [m] at h
    omega

/-! ## 4. Twelve recovered, neighbouring controls -/

theorem twelve_alignment_recovered (n : Nat) (hn : n ≤ 12) :
    Aligned 12 6 n ↔ n = 3 ∨ n = 9 := by
  simpa using four_multiple_alignment_spectrum 3 n (by decide) hn

theorem eight_alignment_is_two_and_six (n : Nat) (hn : n ≤ 8) :
    Aligned 8 4 n ↔ n = 2 ∨ n = 6 := by
  simpa using four_multiple_alignment_spectrum 2 n (by decide) hn

/-- Red neighbour: ten has an antipodal frame but no alignment. -/
theorem ten_has_frame_but_no_alignment :
    HasAntipodalFrame 10 ∧ ∀ n, n ≤ 10 → ¬ Aligned 10 5 n := by
  refine ⟨⟨5, by decide⟩, ?_⟩
  intro n hn
  simpa using two_mod_four_has_no_alignment 2 n hn

/-- The sole even prime size is already a no-alignment control. -/
theorem two_has_frame_but_no_alignment :
    HasAntipodalFrame 2 ∧ ∀ n, n ≤ 2 → ¬ Aligned 2 1 n := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  intro n hn
  simpa using two_mod_four_has_no_alignment 0 n hn

/-! ## 5. Red control: remove the antipodal frame translation -/

def UnshiftedAligned (N n : Nat) : Prop :=
  aReading N n = bLocalReading N n

/-- Without B's `+6` frame translation, the twelve-clock meetings move to the
start, halfway point and finish. -/
theorem twelve_unshifted_alignment_is_zero_six_twelve :
    ∀ n : Fin 13, UnshiftedAligned 12 n.val ↔
      (n.val = 0 ∨ n.val = 6 ∨ n.val = 12) := by
  unfold UnshiftedAligned aReading bLocalReading
  decide

/-- With the frame translation, the same finite window has only 3 and 9. -/
theorem twelve_shifted_alignment_is_three_nine :
    ∀ n : Fin 13, Aligned 12 6 n.val ↔ (n.val = 3 ∨ n.val = 9) := by
  intro n
  exact twelve_alignment_recovered n.val (by omega)

/-! ## Certificate -/

theorem alignment_spectrum_certificate :
    (∀ k n, 0 < k → n ≤ 4 * k →
      (Aligned (4 * k) (2 * k) n ↔ n = k ∨ n = 3 * k)) ∧
    (∀ k n, n ≤ 4 * k + 2 → ¬ Aligned (4 * k + 2) (2 * k + 1) n) ∧
    (∀ k, ¬ HasAntipodalFrame (2 * k + 1)) ∧
    (∀ n, n ≤ 12 → (Aligned 12 6 n ↔ n = 3 ∨ n = 9)) ∧
    (HasAntipodalFrame 10 ∧ ∀ n, n ≤ 10 → ¬ Aligned 10 5 n) ∧
    (∀ n : Fin 13, UnshiftedAligned 12 n.val ↔
      (n.val = 0 ∨ n.val = 6 ∨ n.val = 12)) :=
  ⟨four_multiple_alignment_spectrum, two_mod_four_has_no_alignment,
   no_odd_clock_has_an_antipodal_frame, twelve_alignment_recovered,
   ten_has_frame_but_no_alignment, twelve_unshifted_alignment_is_zero_six_twelve⟩

#print axioms every_even_clock_has_an_antipodal_frame
#print axioms no_odd_clock_has_an_antipodal_frame
#print axioms four_multiple_alignment_spectrum
#print axioms two_mod_four_has_no_alignment
#print axioms twelve_alignment_recovered
#print axioms ten_has_frame_but_no_alignment
#print axioms two_has_frame_but_no_alignment
#print axioms twelve_unshifted_alignment_is_zero_six_twelve
#print axioms alignment_spectrum_certificate

end FoundationStoneTest16Q
