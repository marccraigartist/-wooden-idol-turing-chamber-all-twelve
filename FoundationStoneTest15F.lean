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
      (convert this using 1; ring)
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


end

end FoundationStoneTestFifteenE

/-!
# TEST 15F — DISTANCE ACTUALLY TRAVELLED

Self-contained: the exact 15E model is included above without modification of
its definitions. The new namespace measures length by integrating speed.

Each 30-degree rotation follows its circular orbit about its stated axis.
These are generally small-circle tracks, NOT shortest great-circle arcs.
No fixed-axis combined rotation is substituted for the two ordered legs.

The helix calculation below proves the length of the explicitly parametrised
single helix (rotating planar coordinates, axial coordinate pitch*t). It does
not silently insert translations into the two-axis globe dynamics.
-/
namespace FoundationStoneTestFifteenF
open FoundationStoneTestFifteenE
noncomputable section

def angle : ℝ := Real.pi / 6
theorem angle_pos : 0 < angle := by unfold angle; positivity

def turnX (u v t : ℝ) := u * Real.cos t - v * Real.sin t
def turnY (u v t : ℝ) := u * Real.sin t + v * Real.cos t

theorem dx (u v t : ℝ) :
    HasDerivAt (turnX u v) (-u * Real.sin t - v * Real.cos t) t := by
  convert (HasDerivAt.const_mul u (Real.hasDerivAt_cos t)).sub
    (HasDerivAt.const_mul v (Real.hasDerivAt_sin t)) using 1
  · funext s; rfl
  · ring

theorem dy (u v t : ℝ) :
    HasDerivAt (turnY u v) (u * Real.cos t - v * Real.sin t) t := by
  convert (HasDerivAt.const_mul u (Real.hasDerivAt_sin t)).add
    (HasDerivAt.const_mul v (Real.hasDerivAt_cos t)) using 1
  · funext s; rfl
  · ring

/-- Actual speed squared of (turnX u v t, turnY u v t, pitch*t). -/
def speedSq (u v pitch t : ℝ) : ℝ :=
  (deriv (turnX u v) t)^2 + (deriv (turnY u v) t)^2 +
    (deriv (fun s : ℝ => pitch * s) t)^2

theorem speedSq_exact (u v pitch t : ℝ) :
    speedSq u v pitch t = u^2 + v^2 + pitch^2 := by
  unfold speedSq
  have hp : HasDerivAt (fun s : ℝ => pitch*s) pitch t := by
    simpa using HasDerivAt.const_mul pitch (hasDerivAt_id t)
  rw [(dx u v t).deriv, (dy u v t).deriv, hp.deriv]
  linear_combination (u^2 + v^2) * Real.sin_sq_add_cos_sq t

/-- Speed-integral length of the parametrised helix for a positive 30-degree turn. -/
def legLength (u v pitch : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..angle, Real.sqrt (speedSq u v pitch t)

theorem legLength_exact (u v pitch : ℝ) :
    legLength u v pitch = angle * Real.sqrt (u^2 + v^2 + pitch^2) := by
  unfold legLength
  simp_rw [speedSq_exact]
  simp [intervalIntegral.integral_const]

theorem helix_strictly_longer (u v pitch : ℝ) (hp : pitch ≠ 0) :
    legLength u v 0 < legLength u v pitch := by
  rw [legLength_exact, legLength_exact]
  apply mul_lt_mul_of_pos_left _ angle_pos
  apply Real.sqrt_lt_sqrt
  · positivity
  · nlinarith [sq_pos_of_ne_zero hp]

/-- At zero pitch the helix length reduces to the circular track length. -/
theorem zero_pitch_control (u v : ℝ) :
    legLength u v 0 = angle * Real.sqrt (u^2 + v^2) := by
  simp [legLength_exact]

/-- Longer than a circle does not by itself detect the sign of the pitch. -/
theorem pitch_sign_length_control (u v p : ℝ) :
    legLength u v (-p) = legLength u v p := by
  simp [legLength_exact]

/-- The planar orbit really reaches the same 30-degree endpoint used in 15E. -/
theorem turn_endpoint (u v : ℝ) :
    turnX u v angle = (sqrt3 * u - v) / 2 ∧
    turnY u v angle = (u + sqrt3 * v) / 2 := by
  unfold turnX turnY angle sqrt3
  rw [Real.cos_pi_div_six, Real.sin_pi_div_six]
  constructor <;> ring

/-- Unscaled intermediate x-coordinates for z-first and y-first. -/
def zx (v : R3) : ℝ := (sqrt3 * v.x - v.y) / 2
def yx (v : R3) : ℝ := (sqrt3 * v.x + v.z) / 2

theorem intermediate_coordinates (v : R3) :
    zx v = (scale (1/2) (Rz2 v)).x ∧
    yx v = (scale (1/2) (Ry2 v)).x := by
  constructor <;> simp [zx, yx, scale, Rz2, Ry2] <;> ring

/-- The actual spatial paths, including their unchanged axial coordinates. -/
def circleZ (v : R3) (t : ℝ) : R3 :=
  ⟨turnX v.x v.y t, turnY v.x v.y t, v.z⟩
def circleY (v : R3) (t : ℝ) : R3 :=
  ⟨turnX v.x (-v.z) t, v.y, -turnY v.x (-v.z) t⟩
def curveSpeedSq (g : ℝ → R3) (t : ℝ) : ℝ :=
  (deriv (fun s => (g s).x) t)^2 +
  (deriv (fun s => (g s).y) t)^2 +
  (deriv (fun s => (g s).z) t)^2
def curveLength (g : ℝ → R3) : ℝ :=
  ∫ t in (0 : ℝ)..angle, Real.sqrt (curveSpeedSq g t)

theorem spatial_endpoints (v : R3) :
    circleZ v angle = scale (1/2) (Rz2 v) ∧
    circleY v angle = scale (1/2) (Ry2 v) := by
  have hz := turn_endpoint v.x v.y
  have hy := turn_endpoint v.x (-v.z)
  constructor <;> apply R3.ext <;>
    simp only [circleZ, circleY, scale, Rz2, Ry2, hz.1, hz.2, hy.1, hy.2] <;> ring

theorem spatial_speeds (v : R3) (t : ℝ) :
    curveSpeedSq (circleZ v) t = v.x^2 + v.y^2 ∧
    curveSpeedSq (circleY v) t = v.x^2 + v.z^2 := by
  constructor
  · dsimp only [curveSpeedSq, circleZ]
    rw [(dx v.x v.y t).deriv, (dy v.x v.y t).deriv]
    simp only [deriv_const, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
    linear_combination (v.x^2 + v.y^2) * Real.sin_sq_add_cos_sq t
  · dsimp only [curveSpeedSq, circleY]
    have hn : HasDerivAt (fun s : ℝ => -turnY v.x (-v.z) s)
        (-(v.x * Real.cos t - (-v.z) * Real.sin t)) t := by
      convert (dy v.x (-v.z) t).neg using 1
    rw [(dx v.x (-v.z) t).deriv, hn.deriv]
    simp only [deriv_const, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
    linear_combination (v.x^2 + v.z^2) * Real.sin_sq_add_cos_sq t

theorem spatial_lengths (v : R3) :
    curveLength (circleZ v) = legLength v.x v.y 0 ∧
    curveLength (circleY v) = legLength v.x (-v.z) 0 := by
  constructor
  · unfold curveLength
    simp_rw [(spatial_speeds v _).1]
    simp [legLength_exact, intervalIntegral.integral_const]
  · unfold curveLength
    simp_rw [(spatial_speeds v _).2]
    simp [legLength_exact, intervalIntegral.integral_const]

/-- z then y. For the y leg use coordinates (x,-z); reversing its second
coordinate recovers the usual y rotation and preserves Euclidean speed. -/
def lengthA (v : R3) : ℝ :=
  legLength v.x v.y 0 + legLength (zx v) (-v.z) 0

/-- y then z, with both legs measured before forgetting the intermediate point. -/
def lengthB (v : R3) : ℝ :=
  legLength v.x (-v.z) 0 + legLength (yx v) v.y 0

/-- Neither total substitutes a shorter connecting path for the second rotation. -/
theorem actual_two_leg_paths (v : R3) :
    lengthA v = curveLength (circleZ v) + curveLength (circleY (circleZ v angle)) ∧
    lengthB v = curveLength (circleY v) + curveLength (circleZ (circleY v angle)) := by
  constructor
  · rw [(spatial_lengths v).1, (spatial_lengths (circleZ v angle)).2]
    unfold lengthA
    congr 2
    dsimp only [circleZ]
    exact (turn_endpoint v.x v.y).1.symm
  · rw [(spatial_lengths v).2, (spatial_lengths (circleY v angle)).1]
    unfold lengthB
    congr 2
    dsimp only [circleY]
    rw [(turn_endpoint v.x (-v.z)).1]
    simp [yx]

/-- Both continuous two-leg journeys finish at the exact unscaled 15E endpoints. -/
theorem two_leg_endpoints (v : R3) :
    circleY (circleZ v angle) angle = scale (1/4) (A v) ∧
    circleZ (circleY v angle) angle = scale (1/4) (B v) := by
  constructor
  · rw [(spatial_endpoints _).2, (spatial_endpoints v).1, A_is_Ry_after_Rz]
    apply R3.ext <;> simp only [scale, Ry2] <;> ring
  · rw [(spatial_endpoints _).1, (spatial_endpoints v).2, B_is_Rz_after_Ry]
    apply R3.ext <;> simp only [scale, Rz2] <;> ring

theorem lengthA_exact (v : R3) :
    lengthA v = angle * (Real.sqrt (v.x^2 + v.y^2) +
      Real.sqrt ((zx v)^2 + v.z^2)) := by
  simp [lengthA, legLength_exact, mul_add]

theorem lengthB_exact (v : R3) :
    lengthB v = angle * (Real.sqrt (v.x^2 + v.z^2) +
      Real.sqrt ((yx v)^2 + v.y^2)) := by
  simp [lengthB, legLength_exact, mul_add]

/-- The shared symmetry plane survives the change to actual path length. -/
theorem shared_plane_length (v : R3) (h : v.y + v.z = 0) :
    lengthA v = lengthB v := by
  have hz : v.z = -v.y := by linarith
  rw [lengthA_exact, lengthB_exact]
  simp [zx, yx, hz, sub_eq_add_neg]

/-- The exact half-seat point: B travels farther along the two circular tracks. -/
theorem half_seat_length_asymmetry : lengthA fifteenPoint < lengthB fifteenPoint := by
  have hs := sqrt3_sq
  have h1 : (sqrt3 / 2)^2 = (3 : ℝ)/4 := by nlinarith
  have h2 : (sqrt3 + (2 - sqrt3))/2 = (1 : ℝ) := by ring
  rw [lengthA_exact, lengthB_exact]
  simp only [fifteenPoint, zx, yx, mul_one, sub_zero, one_pow, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, h2, h1, Real.sqrt_one]
  apply mul_lt_mul_of_pos_left _ angle_pos
  have ht : Real.sqrt ((3 : ℝ)/4 + (2-sqrt3)^2) <
      Real.sqrt (1 + (2-sqrt3)^2) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  linarith

/-- A useful exact length comparison: equal sums of squared leg lengths
can still have strictly different sums of leg lengths. -/
theorem equal_energy_unequal_length :
    Real.sqrt 13 + Real.sqrt ((3 : ℝ)/4) <
      1 + Real.sqrt ((51 : ℝ)/4) := by
  have ha := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  have hb := Real.sq_sqrt (show (0 : ℝ) ≤ 3/4 by norm_num)
  have hc := Real.sq_sqrt (show (0 : ℝ) ≤ 51/4 by norm_num)
  have hna := Real.sqrt_nonneg (13 : ℝ)
  have hnb := Real.sqrt_nonneg ((3 : ℝ)/4)
  have hnc := Real.sqrt_nonneg ((51 : ℝ)/4)
  have hp : (Real.sqrt 13 * Real.sqrt ((3 : ℝ)/4))^2 = (39 : ℝ)/4 := by
    rw [mul_pow, ha, hb]; norm_num
  have hprod : Real.sqrt 13 * Real.sqrt ((3 : ℝ)/4) < Real.sqrt ((51 : ℝ)/4) := by
    nlinarith [mul_nonneg hna hnb]
  nlinarith [sq_nonneg (Real.sqrt 13 + Real.sqrt ((3 : ℝ)/4) -
    (1 + Real.sqrt ((51 : ℝ)/4)))]

/-- RED CONTROL: the oblique ENERGY seam from 15E is NOT a length seam. -/
theorem energy_tie_does_not_imply_length_tie :
    pathEnergyA crossPoint = pathEnergyB crossPoint ∧
      lengthA crossPoint < lengthB crossPoint := by
  refine ⟨path_can_forget_what_endpoint_detects.1, ?_⟩
  have hs := sqrt3_sq
  have h1 : 1 + (2 * sqrt3)^2 = (13 : ℝ) := by nlinarith
  have h2 : ((sqrt3 - 2*sqrt3)/2)^2 = (3 : ℝ)/4 := by nlinarith
  have h3 : (sqrt3/2)^2 + (2*sqrt3)^2 = (51 : ℝ)/4 := by nlinarith
  rw [lengthA_exact, lengthB_exact]
  simp only [crossPoint, zx, yx, mul_one, add_zero, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, one_pow, h1, h2, h3, Real.sqrt_one]
  exact mul_lt_mul_of_pos_left equal_energy_unequal_length angle_pos

theorem seat_length_tie_but_different_endpoints :
    lengthA xPoint = lengthB xPoint ∧ A xPoint ≠ B xPoint := by
  constructor
  · rw [lengthA_exact, lengthB_exact]
    simp [xPoint, zx, yx]
  · exact two_measurements_still_do_not_identify_motion.2.2

theorem y_axis_order_control : lengthB yPoint < lengthA yPoint := by
  have hq : Real.sqrt ((1 : ℝ)/4) = (1 : ℝ)/2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1/4 by norm_num)
    have hn := Real.sqrt_nonneg ((1 : ℝ)/4)
    nlinarith
  rw [lengthA_exact, lengthB_exact]
  norm_num [yPoint, zx, yx, hq]
  nlinarith [angle_pos]

/-- General law explaining why the new observable is stronger in a different
direction: at equal squared totals, the larger product gives the longer sum. -/
theorem equal_squares_length_iff (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : a^2 + b^2 = c^2 + d^2) :
    a + b < c + d ↔ a*b < c*d := by
  constructor <;> intro h <;> nlinarith [sq_nonneg (a+b-c-d)]

theorem test15F_certificate :
    (∀ u v p, p ≠ 0 → legLength u v 0 < legLength u v p) ∧
    lengthA fifteenPoint < lengthB fifteenPoint ∧
    (pathEnergyA crossPoint = pathEnergyB crossPoint ∧
      lengthA crossPoint < lengthB crossPoint) ∧
    (∀ v : R3, v.y + v.z = 0 → lengthA v = lengthB v) ∧
    (lengthA xPoint = lengthB xPoint ∧ A xPoint ≠ B xPoint) ∧
    lengthB yPoint < lengthA yPoint :=
  ⟨helix_strictly_longer, half_seat_length_asymmetry,
    energy_tie_does_not_imply_length_tie, shared_plane_length,
    seat_length_tie_but_different_endpoints, y_axis_order_control⟩

/-- The half-seat length claim also holds directly for the actual 3D paths. -/
theorem spatial_half_seat_certificate :
    curveLength (circleZ fifteenPoint) +
      curveLength (circleY (circleZ fifteenPoint angle)) <
    curveLength (circleY fifteenPoint) +
      curveLength (circleZ (circleY fifteenPoint angle)) := by
  rw [← (actual_two_leg_paths fifteenPoint).1, ← (actual_two_leg_paths fifteenPoint).2]
  exact half_seat_length_asymmetry

#print axioms speedSq_exact
#print axioms legLength_exact
#print axioms turn_endpoint
#print axioms intermediate_coordinates
#print axioms spatial_endpoints
#print axioms spatial_speeds
#print axioms actual_two_leg_paths
#print axioms two_leg_endpoints
#print axioms helix_strictly_longer
#print axioms zero_pitch_control
#print axioms pitch_sign_length_control
#print axioms half_seat_length_asymmetry
#print axioms energy_tie_does_not_imply_length_tie
#print axioms shared_plane_length
#print axioms seat_length_tie_but_different_endpoints
#print axioms y_axis_order_control
#print axioms equal_squares_length_iff
#print axioms test15F_certificate
#print axioms spatial_half_seat_certificate

end
end FoundationStoneTestFifteenF
