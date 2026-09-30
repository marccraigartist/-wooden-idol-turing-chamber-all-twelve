import Mathlib

/-!
# THE TWO MEASUREMENTS — TEST 15E

Test 15D classified the straight chord from the start to the final point after
two ordered 30-degree rotations.  Test 15E retains the intermediate point and
asks a different question: how much squared chord is accumulated across the
two legs?

`Ry2` and `Rz2` are twice the 30-degree rotations.  This avoids denominators.
`A = Ry2 ∘ Rz2` and `B = Rz2 ∘ Ry2` are therefore four times the two final
rotations.  Each leg in `pathEnergyA/B` is scaled uniformly by four, so each
path energy is sixteen times the sum of the two actual squared leg chords.

Lean proves two different exact seams:

  endpoint difference = 16 (2 - √3) x (y + z)

  path-energy difference = 4 (2 - √3) (y + z) (2√3 x + z - y).

Consequently the two measurements share the plane `y + z = 0`, but their
other planes differ.  Each measurement can therefore forget an order
difference detected by the other.  Most strongly, on the x-axis both scalar
measurements agree while the ordered rotations still reach different points.

This is additive squared-chord energy, not the sum of spherical arc lengths.
That distinction is deliberately retained for Test 15F.
-/

namespace FoundationStoneTestFifteenE

noncomputable section

structure R3 where
  x : ℝ
  y : ℝ
  z : ℝ

@[ext] theorem R3.ext (u v : R3)
    (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  cases u
  cases v
  simp_all

def sqrt3 : ℝ := Real.sqrt 3

def scale (k : ℝ) (v : R3) : R3 := ⟨k * v.x, k * v.y, k * v.z⟩
def sub (u v : R3) : R3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
def normSq (v : R3) : ℝ := v.x^2 + v.y^2 + v.z^2

/-- Twice a 30-degree rotation about z. -/
def Rz2 (v : R3) : R3 :=
  ⟨sqrt3 * v.x - v.y, v.x + sqrt3 * v.y, 2 * v.z⟩

/-- Twice a 30-degree rotation about y. -/
def Ry2 (v : R3) : R3 :=
  ⟨sqrt3 * v.x + v.z, 2 * v.y, -v.x + sqrt3 * v.z⟩

/-- Four times `Ry(30) ∘ Rz(30)`, in reduced `ℚ(√3)` coordinates. -/
def A (v : R3) : R3 :=
  ⟨3 * v.x - sqrt3 * v.y + 2 * v.z,
   2 * v.x + 2 * sqrt3 * v.y,
   -sqrt3 * v.x + v.y + 2 * sqrt3 * v.z⟩

/-- Four times `Rz(30) ∘ Ry(30)`, in reduced `ℚ(√3)` coordinates. -/
def B (v : R3) : R3 :=
  ⟨3 * v.x - 2 * v.y + sqrt3 * v.z,
   sqrt3 * v.x + 2 * sqrt3 * v.y + v.z,
   -2 * v.x + 2 * sqrt3 * v.z⟩

/-- Sixteen times the actual squared start-to-finish chord. -/
def endpointEnergy (F : R3 → R3) (v : R3) : ℝ :=
  normSq (sub (F v) (scale 4 v))

/-- Sixteen times the sum of the two actual squared leg chords for z then y. -/
def pathEnergyA (v : R3) : ℝ :=
  normSq (sub (scale 2 (Rz2 v)) (scale 4 v)) +
  normSq (sub (A v) (scale 2 (Rz2 v)))

/-- Sixteen times the sum of the two actual squared leg chords for y then z. -/
def pathEnergyB (v : R3) : ℝ :=
  normSq (sub (scale 2 (Ry2 v)) (scale 4 v)) +
  normSq (sub (B v) (scale 2 (Ry2 v)))

theorem sqrt3_sq : sqrt3 ^ 2 = 3 := by
  unfold sqrt3
  exact Real.sq_sqrt (by norm_num)

theorem sqrt3_pos : 0 < sqrt3 := by
  unfold sqrt3
  positivity

theorem two_minus_sqrt3_pos : 0 < 2 - sqrt3 := by
  have hs := sqrt3_sq
  have hn : 0 ≤ sqrt3 := le_of_lt sqrt3_pos
  nlinarith

theorem A_is_Ry_after_Rz (v : R3) : A v = Ry2 (Rz2 v) := by
  apply R3.ext
  · unfold A Ry2 Rz2
    dsimp only
    linear_combination -v.x * sqrt3_sq
  · unfold A Ry2 Rz2
    dsimp only
    ring
  · unfold A Ry2 Rz2
    dsimp only
    ring

theorem B_is_Rz_after_Ry (v : R3) : B v = Rz2 (Ry2 v) := by
  apply R3.ext
  · unfold B Ry2 Rz2
    dsimp only
    linear_combination -v.x * sqrt3_sq
  · unfold B Ry2 Rz2
    dsimp only
    ring
  · unfold B Ry2 Rz2
    dsimp only
    ring

/-! ## Exact endpoint and path equations -/

def endpointSeam (v : R3) : ℝ := v.x * (v.y + v.z)

def pathSeam (v : R3) : ℝ :=
  (v.y + v.z) * (2 * sqrt3 * v.x + v.z - v.y)

theorem endpoint_difference_formula (v : R3) :
    endpointEnergy B v - endpointEnergy A v =
      16 * (2 - sqrt3) * endpointSeam v := by
  unfold endpointEnergy normSq sub scale A B endpointSeam
  dsimp only
  linear_combination
    (-v.y^2 + v.z^2 + 4 * v.x * v.y + 4 * v.x * v.z) * sqrt3_sq

theorem path_difference_formula (v : R3) :
    pathEnergyB v - pathEnergyA v =
      4 * (2 - sqrt3) * pathSeam v := by
  unfold pathEnergyA pathEnergyB normSq sub scale A B Ry2 Rz2 pathSeam
  dsimp only
  linear_combination
    (v.z^2 - v.y^2 + 8 * v.x * (v.y + v.z)) * sqrt3_sq

/-! ## The two different seams -/

theorem endpoint_equal_iff (v : R3) :
    endpointEnergy A v = endpointEnergy B v ↔
      v.x = 0 ∨ v.y + v.z = 0 := by
  rw [eq_comm]
  have hd := endpoint_difference_formula v
  have hp := two_minus_sqrt3_pos
  constructor
  · intro heq
    have hprod : 16 * (2 - sqrt3) * endpointSeam v = 0 := by
      nlinarith
    have hc : 16 * (2 - sqrt3) ≠ 0 :=
      mul_ne_zero (by norm_num) (ne_of_gt hp)
    have hz : endpointSeam v = 0 := (mul_eq_zero.mp hprod).resolve_left hc
    exact mul_eq_zero.mp hz
  · intro h
    have hz : endpointSeam v = 0 := by
      unfold endpointSeam
      rcases h with hx | hy
      · simp [hx]
      · simp [hy]
    nlinarith

theorem path_equal_iff (v : R3) :
    pathEnergyA v = pathEnergyB v ↔
      v.y + v.z = 0 ∨ 2 * sqrt3 * v.x + v.z - v.y = 0 := by
  rw [eq_comm]
  have hd := path_difference_formula v
  have hp := two_minus_sqrt3_pos
  constructor
  · intro heq
    have hprod : 4 * (2 - sqrt3) * pathSeam v = 0 := by
      nlinarith
    have hc : 4 * (2 - sqrt3) ≠ 0 :=
      mul_ne_zero (by norm_num) (ne_of_gt hp)
    have hz : pathSeam v = 0 := (mul_eq_zero.mp hprod).resolve_left hc
    exact mul_eq_zero.mp hz
  · intro h
    have hz : pathSeam v = 0 := by
      unfold pathSeam
      rcases h with h₁ | h₂
      · simp [h₁]
      · simp [h₂]
    nlinarith

/-- The plane `y + z = 0` is forgotten by both scalar measurements. -/
theorem shared_plane_forgets_both (v : R3) (h : v.y + v.z = 0) :
    endpointEnergy A v = endpointEnergy B v ∧
      pathEnergyA v = pathEnergyB v :=
  ⟨(endpoint_equal_iff v).2 (Or.inr h), (path_equal_iff v).2 (Or.inl h)⟩

/-! ## Independence controls -/

def xPoint : R3 := ⟨1, 0, 0⟩
def yPoint : R3 := ⟨0, 1, 0⟩
def crossPoint : R3 := ⟨1, 2 * sqrt3, 0⟩
def fifteenPoint : R3 := ⟨1, 0, 2 - sqrt3⟩

/-- Endpoint chords agree at y, while path A has greater accumulated energy. -/
theorem endpoint_can_forget_what_path_detects :
    endpointEnergy A yPoint = endpointEnergy B yPoint ∧
      pathEnergyB yPoint < pathEnergyA yPoint := by
  constructor
  · exact (endpoint_equal_iff yPoint).2 (Or.inl (by norm_num [yPoint]))
  · have hd := path_difference_formula yPoint
    have hc : 0 < 4 * (2 - sqrt3) :=
      mul_pos (by norm_num) two_minus_sqrt3_pos
    have hs : pathSeam yPoint = -1 := by norm_num [pathSeam, yPoint]
    have hprod : 4 * (2 - sqrt3) * pathSeam yPoint < 0 := by
      rw [hs]
      nlinarith
    nlinarith [hd, hprod]

/-- Path energies agree at this point, while endpoint B lies farther from the start. -/
theorem path_can_forget_what_endpoint_detects :
    pathEnergyA crossPoint = pathEnergyB crossPoint ∧
      endpointEnergy A crossPoint < endpointEnergy B crossPoint := by
  constructor
  · apply (path_equal_iff crossPoint).2
    right
    unfold crossPoint
    dsimp only
    ring
  · have hd := endpoint_difference_formula crossPoint
    have hc : 0 < 16 * (2 - sqrt3) :=
      mul_pos (by norm_num) two_minus_sqrt3_pos
    have hs : 0 < endpointSeam crossPoint := by
      unfold endpointSeam crossPoint
      dsimp only
      have hq : 0 < 2 * sqrt3 := mul_pos (by norm_num) sqrt3_pos
      simpa using hq
    have hprod : 0 < 16 * (2 - sqrt3) * endpointSeam crossPoint := mul_pos hc hs
    nlinarith

/-- The half-seat direction favours order B in both scalar measurements. -/
theorem fifteen_B_longer_in_both_measurements :
    endpointEnergy A fifteenPoint < endpointEnergy B fifteenPoint ∧
      pathEnergyA fifteenPoint < pathEnergyB fifteenPoint := by
  constructor
  · have hd := endpoint_difference_formula fifteenPoint
    have hc : 0 < 16 * (2 - sqrt3) :=
      mul_pos (by norm_num) two_minus_sqrt3_pos
    have hs : 0 < endpointSeam fifteenPoint := by
      unfold endpointSeam fifteenPoint
      dsimp only
      simpa using two_minus_sqrt3_pos
    have hprod : 0 < 16 * (2 - sqrt3) * endpointSeam fifteenPoint := mul_pos hc hs
    nlinarith
  · have hd := path_difference_formula fifteenPoint
    have hc : 0 < 4 * (2 - sqrt3) :=
      mul_pos (by norm_num) two_minus_sqrt3_pos
    have hs : 0 < pathSeam fifteenPoint := by
      unfold pathSeam fifteenPoint
      dsimp only
      have hsum : 0 < sqrt3 + 2 := by linarith [sqrt3_pos]
      have := mul_pos two_minus_sqrt3_pos hsum
      convert this using 1 <;> ring
    have hprod : 0 < 4 * (2 - sqrt3) * pathSeam fifteenPoint := mul_pos hc hs
    nlinarith

/-- RED CONTROL: even both scalar agreements together do not imply the same motion. -/
theorem two_measurements_still_do_not_identify_motion :
    endpointEnergy A xPoint = endpointEnergy B xPoint ∧
    pathEnergyA xPoint = pathEnergyB xPoint ∧
    A xPoint ≠ B xPoint := by
  have hboth := shared_plane_forgets_both xPoint (by norm_num [xPoint])
  refine ⟨hboth.1, hboth.2, ?_⟩
  intro h
  have hy := congrArg R3.y h
  unfold A B xPoint at hy
  dsimp only at hy
  have hs := sqrt3_sq
  have hn : 0 ≤ sqrt3 := le_of_lt sqrt3_pos
  nlinarith

/-! ## Certificate -/

theorem two_measurements_test_15E_certificate :
    (∀ v, endpointEnergy B v - endpointEnergy A v =
      16 * (2 - sqrt3) * endpointSeam v) ∧
    (∀ v, pathEnergyB v - pathEnergyA v =
      4 * (2 - sqrt3) * pathSeam v) ∧
    (∀ v, endpointEnergy A v = endpointEnergy B v ↔
      v.x = 0 ∨ v.y + v.z = 0) ∧
    (∀ v, pathEnergyA v = pathEnergyB v ↔
      v.y + v.z = 0 ∨ 2 * sqrt3 * v.x + v.z - v.y = 0) ∧
    (endpointEnergy A yPoint = endpointEnergy B yPoint ∧
      pathEnergyB yPoint < pathEnergyA yPoint) ∧
    (pathEnergyA crossPoint = pathEnergyB crossPoint ∧
      endpointEnergy A crossPoint < endpointEnergy B crossPoint) ∧
    (endpointEnergy A fifteenPoint < endpointEnergy B fifteenPoint ∧
      pathEnergyA fifteenPoint < pathEnergyB fifteenPoint) ∧
    (endpointEnergy A xPoint = endpointEnergy B xPoint ∧
      pathEnergyA xPoint = pathEnergyB xPoint ∧ A xPoint ≠ B xPoint) :=
  ⟨endpoint_difference_formula,
   path_difference_formula,
   endpoint_equal_iff,
   path_equal_iff,
   endpoint_can_forget_what_path_detects,
   path_can_forget_what_endpoint_detects,
   fifteen_B_longer_in_both_measurements,
   two_measurements_still_do_not_identify_motion⟩

#print axioms endpoint_difference_formula
#print axioms path_difference_formula
#print axioms A_is_Ry_after_Rz
#print axioms B_is_Rz_after_Ry
#print axioms endpoint_equal_iff
#print axioms path_equal_iff
#print axioms shared_plane_forgets_both
#print axioms endpoint_can_forget_what_path_detects
#print axioms path_can_forget_what_endpoint_detects
#print axioms fifteen_B_longer_in_both_measurements
#print axioms two_measurements_still_do_not_identify_motion
#print axioms two_measurements_test_15E_certificate

end

end FoundationStoneTestFifteenE
