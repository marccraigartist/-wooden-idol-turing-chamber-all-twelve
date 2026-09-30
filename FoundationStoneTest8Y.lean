/-!
# THE FOUNDATION STONE — TEST 8Y: THE ALIGNMENT IS NOT A DIRECTION

Runs in the Lean live editor with no imports (core Lean only). An audit of Test 8.

Test 8 proves (correctly) that a reflection-symmetric input cannot choose clockwise over
anticlockwise. But the two-body alignment is not a choice of direction:

1. Keeping the clockwise step and keeping the anticlockwise step are the SAME condition
   on a frame change. So the pebble's direction never enters: a clockwise pebble and an
   anticlockwise pebble force the same result.
2. The antipode is its own mirror image: reflecting the whole picture in magenta leaves
   it unchanged. So Test 8's symmetry obstruction does not apply to it.
3. The antipode commutes with every one of the clock's 24 moves, turns and mirrors alike.
   Test 8X shows it is the only separate map that keeps the relay line and the
   done/doing axis. So a perfectly symmetric specification picks it out, with no pebble.

Seat `0` is B12; seats `1`–`11` are B1–B11.
-/
namespace NotADirection

abbrev Seat := Fin 12

def iter (g : Seat → Seat) : Nat → Seat → Seat
  | 0, k => k
  | n + 1, k => g (iter g n k)

theorem commutes_iter (f g : Seat → Seat) (h : ∀ k, f (g k) = g (f k)) :
    ∀ n k, f (iter g n k) = iter g n (f k) := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n ih => intro k; show f (g (iter g n k)) = g (iter g n (f k)); rw [h, ih]

theorem eleven_forward_is_back : ∀ k : Seat, iter (· + 1) 11 k = k + 11 := by decide
theorem eleven_back_is_forward : ∀ k : Seat, iter (· + 11) 11 k = k + 1 := by decide

/-- 1. Keeping the clockwise step is the same condition as keeping the anticlockwise
step. The direction of the pebble makes no difference. -/
theorem clockwise_iff_anticlockwise (f : Seat → Seat) :
    (∀ k, f (k + 1) = f k + 1) ↔ (∀ k, f (k + 11) = f k + 11) := by
  constructor
  · intro h k
    have hi := commutes_iter f (· + 1) h 11 k
    rw [eleven_forward_is_back, eleven_forward_is_back] at hi
    exact hi
  · intro h k
    have hi := commutes_iter f (· + 11) h 11 k
    rw [eleven_back_is_forward, eleven_back_is_forward] at hi
    exact hi

/-- 2. The antipode is its own mirror image under magenta. -/
theorem antipode_is_its_own_reflection :
    ∀ k : Seat, (11 : Seat) - ((11 - k) + 6) = k + 6 := by decide

/-- 3. The antipode commutes with all 24 clock moves: every turn and every mirror. -/
theorem antipode_commutes_with_every_move :
    (∀ t k : Seat, (k + t) + 6 = (k + 6) + t) ∧
    (∀ c k : Seat, (c - k) + 6 = c - (k + 6)) := by
  decide

/-- 3'. No other turn commutes with every mirror except standing still. -/
theorem only_the_half_turn_commutes_with_every_mirror :
    ∀ t : Seat, (∀ c k : Seat, (c - k) + t = c - (k + t)) ↔ (t = 0 ∨ t = 6) := by
  decide

#print axioms clockwise_iff_anticlockwise
#print axioms antipode_is_its_own_reflection
#print axioms antipode_commutes_with_every_move
#print axioms only_the_half_turn_commutes_with_every_mirror

end NotADirection
