import FoundationStoneTest4

/-!
# THE FOUNDATION STONE — TEST 5: THE SECOND-BODY RELAY

Tests 2–4 were one-body results.  Test 5 introduces two genuine coordinate frames.
Body B's local clock is antipodal to body A's: B-local seat `k` is seen from A at
`k + 6`.  With seat `0 = B12`, B's own B1 is therefore A's B7.

A message contains a source body, a formula written in that body's local language,
a point recorded in the shared A-frame, and a Boolean answer.  Relaying changes the
source and transports the formula, while the shared point and answer remain fixed.

Lean checks:
* B-own-B1 really is A-B7, and conversely;
* formula/frame transport preserves meaning and genuine certificates;
* two relays return the exact original message;
* answer-only erasure loses a real source-policy capability;
* merely changing the source label forges the frame and is rejected;
* the antipode is not magenta, although the two involutions commute;
* their composite is a third fixed-point-free involution;
* the truth chart shifted by +6 is neither Truth nor Discovery;
* a richer mask language, closed under the frame change, freshly satisfies All12.

This is a two-frame equivariance and provenance result.  It is not Gödel, Tarski,
Turing, undecidability, or a P-versus-NP result.
-/

namespace FoundationStoneTestFive

open FoundationStoneTestTwo
open FoundationStoneTestThree

inductive Body
  | A
  | B
deriving DecidableEq

def other : Body → Body
  | .A => .B
  | .B => .A

theorem other_twice : ∀ body, other (other body) = body := by
  intro body
  cases body <;> rfl

/-- The coordinate change between the bodies. -/
def antipode (seat : Seat) : Seat := seat + 6

theorem antipode_twice : ∀ seat, antipode (antipode seat) = seat := by decide
theorem antipode_ne : ∀ seat, antipode seat ≠ seat := by decide
theorem antipode_injective : Function.Injective antipode := by decide

/-- Local seat `k` expressed in the shared A-frame. -/
def inAFrame : Body → Seat → Seat
  | .A, seat => seat
  | .B, seat => antipode seat

/-- A shared A-frame seat expressed in a body's local coordinates. -/
def inLocalFrame : Body → Seat → Seat
  | .A, seat => seat
  | .B, seat => antipode seat

/-- Marc's index claim, now an exact theorem: B's own B1 is A's B7. -/
theorem B_own_B1_is_A_B7 : inAFrame .B (1 : Seat) = (7 : Seat) := by decide

theorem A_B7_is_B_own_B1 : inLocalFrame .B (7 : Seat) = (1 : Seat) := by decide

/-- The two operations are different. -/
theorem antipode_is_not_magenta : antipode ≠ magenta := by
  intro h
  have bad := congrFun h (0 : Seat)
  have hv := congrArg Fin.val bad
  norm_num [antipode, magenta] at hv

/-- But they commute, so their order does not create ambiguity. -/
theorem antipode_commutes_with_magenta : ∀ seat,
    antipode (magenta seat) = magenta (antipode seat) := by decide

/-- Their composite is a third movement. -/
def thirdTurn (seat : Seat) : Seat := antipode (magenta seat)

theorem third_turn_twice : ∀ seat, thirdTurn (thirdTurn seat) = seat := by decide
theorem third_turn_ne : ∀ seat, thirdTurn seat ≠ seat := by decide
theorem third_turn_not_antipode : thirdTurn ≠ antipode := by
  intro h
  have bad := congrFun h (0 : Seat)
  have hv := congrArg Fin.val bad
  norm_num [thirdTurn, antipode, magenta] at hv
theorem third_turn_not_magenta : thirdTurn ≠ magenta := by
  intro h
  have bad := congrFun h (0 : Seat)
  have hv := congrArg Fin.val bad
  norm_num [thirdTurn, antipode, magenta] at hv

def shiftedTruth (seat : Seat) : Bool := truthChart (antipode seat)
def discoveryChart (seat : Seat) : Bool := !truthChart seat

/-- The second-body truth chart is not the original truth chart. -/
theorem shifted_truth_is_not_truth : shiftedTruth ≠ truthChart := by
  intro h
  have bad := congrFun h (1 : Seat)
  norm_num [shiftedTruth, antipode, truthChart] at bad

/-- Nor is it simply Discovery.  The second frame forces a genuinely third chart. -/
theorem shifted_truth_is_not_discovery : shiftedTruth ≠ discoveryChart := by
  intro h
  have bad := congrFun h (0 : Seat)
  norm_num [shiftedTruth, discoveryChart, antipode, truthChart] at bad

/-! ## A language closed under the A/B frame change -/

inductive RelayFormula
  | mask (reading : Seat → Bool)
  | addressEven
  | top
  | bot
  | neg (body : RelayFormula)
  | and (left right : RelayFormula)
  | or (left right : RelayFormula)

def evalRelay : RelayFormula → NativePoint → Bool
  | .mask reading, p => reading p.2
  | .addressEven, p => p.1 % 2 == 0
  | .top, _ => true
  | .bot, _ => false
  | .neg body, p => !(evalRelay body p)
  | .and left right, p => evalRelay left p && evalRelay right p
  | .or left right, p => evalRelay left p || evalRelay right p

/-- Change the formula from one body's local coordinates to the other's. -/
def frameTransport : RelayFormula → RelayFormula
  | .mask reading => .mask (fun seat => reading (antipode seat))
  | .addressEven => .addressEven
  | .top => .top
  | .bot => .bot
  | .neg body => .neg (frameTransport body)
  | .and left right => .and (frameTransport left) (frameTransport right)
  | .or left right => .or (frameTransport left) (frameTransport right)

/-- Frame transport is exactly precomposition by the +6 coordinate change. -/
theorem frame_transport_semantics (sentence : RelayFormula) (address : Nat) (seat : Seat) :
    evalRelay (frameTransport sentence) (address, seat) =
      evalRelay sentence (address, antipode seat) := by
  induction sentence with
  | mask reading => rfl
  | addressEven => rfl
  | top => rfl
  | bot => rfl
  | neg body ih => simp [frameTransport, evalRelay, ih]
  | and left right ihLeft ihRight => simp [frameTransport, evalRelay, ihLeft, ihRight]
  | or left right ihLeft ihRight => simp [frameTransport, evalRelay, ihLeft, ihRight]

theorem frame_transport_twice : ∀ sentence,
    frameTransport (frameTransport sentence) = sentence := by
  intro sentence
  induction sentence with
  | mask reading =>
      simp only [frameTransport]
      congr 1
      funext seat
      rw [antipode_twice]
  | addressEven => rfl
  | top => rfl
  | bot => rfl
  | neg body ih => simp [frameTransport, ih]
  | and left right ihLeft ihRight => simp [frameTransport, ihLeft, ihRight]
  | or left right ihLeft ihRight => simp [frameTransport, ihLeft, ihRight]

def evalFrom (source : Body) (sentence : RelayFormula) (point : NativePoint) : Bool :=
  evalRelay sentence (point.1, inLocalFrame source point.2)

theorem relay_equivariance (source : Body) (sentence : RelayFormula) (point : NativePoint) :
    evalFrom (other source) (frameTransport sentence) point =
      evalFrom source sentence point := by
  rcases point with ⟨address, seat⟩
  cases source with
  | A =>
      simp only [other, evalFrom, inLocalFrame]
      rw [frame_transport_semantics, antipode_twice]
  | B =>
      simp only [other, evalFrom, inLocalFrame]
      exact frame_transport_semantics sentence address seat

/-! ## Provenance-bearing messages -/

structure Message where
  source : Body
  sentence : RelayFormula
  point : NativePoint
  answer : Bool

def Genuine (message : Message) : Prop :=
  message.answer = evalFrom message.source message.sentence message.point

def relay (message : Message) : Message where
  source := other message.source
  sentence := frameTransport message.sentence
  point := message.point
  answer := message.answer

theorem relay_preserves_genuine (message : Message) (h : Genuine message) :
    Genuine (relay message) := by
  unfold Genuine relay
  dsimp only
  rw [relay_equivariance]
  exact h

theorem relay_twice (message : Message) : relay (relay message) = message := by
  cases message with
  | mk source sentence point answer =>
      simp [relay, other_twice, frame_transport_twice]

def truthFormula : RelayFormula := .mask truthChart

def messageA : Message :=
  ⟨.A, truthFormula, (0, (1 : Seat)), true⟩

/-- A genuine B-origin message with the same bare answer but different provenance. -/
def messageB : Message :=
  ⟨.B, truthFormula, (0, (7 : Seat)), true⟩

theorem messageA_genuine : Genuine messageA := by
  rfl

theorem messageB_genuine : Genuine messageB := by
  rfl

def answerOnly (message : Message) : Bool := message.answer

theorem same_answer_different_provenance :
    answerOnly messageA = answerOnly messageB ∧ messageA ≠ messageB := by
  constructor
  · rfl
  · intro h
    have bad := congrArg Message.source h
    cases bad

def AcceptFrom (expected : Body) (message : Message) : Prop :=
  Genuine message ∧ message.source = expected

/-- Answer-only inspection cannot enforce this source policy. -/
theorem provenance_adds_source_policy_capability :
    answerOnly messageA = answerOnly messageB ∧
    AcceptFrom .A messageA ∧ ¬ AcceptFrom .A messageB := by
  refine ⟨rfl, ⟨messageA_genuine, rfl⟩, ?_⟩
  intro h
  exact (by decide : Body.B ≠ Body.A) h.2

/-- Forgery: change only the source label, without translating the formula. -/
def forgedFrame : Message := { messageA with source := .B }

theorem forged_frame_is_rejected : ¬ Genuine forgedFrame := by
  intro h
  norm_num [Genuine, forgedFrame, messageA, evalFrom, inLocalFrame,
    truthFormula, evalRelay, antipode, truthChart] at h

/-- Correct relay succeeds where the forged relabelling fails. -/
theorem translated_frame_is_accepted : Genuine (relay messageA) :=
  relay_preserves_genuine messageA messageA_genuine

/-! ## The richer language still faces the twelve-station wall -/

def relayDen (sentence : RelayFormula) (point : NativePoint) : Prop :=
  evalRelay sentence point = true

theorem relay_zero_two_indistinguishable (sentence : RelayFormula) (seat : Seat) :
    evalRelay sentence (0, seat) = evalRelay sentence (2, seat) := by
  induction sentence with
  | mask reading => rfl
  | addressEven => simp [evalRelay]
  | top => rfl
  | bot => rfl
  | neg body ih => simp [evalRelay, ih]
  | and left right ihLeft ihRight => simp [evalRelay, ihLeft, ihRight]
  | or left right ihLeft ihRight => simp [evalRelay, ihLeft, ihRight]

theorem address_zero_is_not_relay_named :
    ¬ ∃ sentence : RelayFormula, ∀ p, relayDen sentence p ↔ addressZero p := by
  rintro ⟨sentence, h⟩
  have hzero : evalRelay sentence (0, (0 : Seat)) = true :=
    (h _).mpr (by simp [addressZero])
  have htwo : evalRelay sentence (2, (0 : Seat)) = true := by
    rw [← relay_zero_two_indistinguishable sentence 0]
    exact hzero
  exact (by simpa [addressZero, relayDen] using (h _).mp htwo)

def RelayWall : System where
  X := NativePoint
  T := nativeTurn
  Φ := Bool
  φ := true
  L := RelayFormula
  falsum := .bot
  con := .top
  den := relayDen
  Prf := fun _ => False
  R := CoOrbit nativeTurn
  C := fun x _ => x
  interp := nativeInterp
  finuniversal := native_finite_universal

theorem relay_B1 : RelayWall.B1 := by
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

theorem relay_B2 : RelayWall.B2 := by
  refine ⟨(0, (1 : Seat)), native_turn_ne _, ?_⟩
  intro sentence hs n
  refine ⟨2 * (n + 1), by omega, ?_⟩
  change relayDen sentence (iter nativeTurn (2 * (n + 1)) (0, (1 : Seat)))
  rw [native_turn_even]
  exact hs

theorem relay_B3 : RelayWall.B3 :=
  ⟨addressZero, address_zero_invariant, address_zero_backward,
   address_zero_is_not_relay_named⟩

theorem relay_B4 : RelayWall.B4 := fun _ _ => Iff.rfl
theorem relay_B5 : RelayWall.B5 :=
  ⟨by simp [Consistent, RelayWall], by simp [RelayWall]⟩

theorem relay_B6 : RelayWall.B6 := by
  refine ⟨false, ?_⟩
  change false ≠ true
  decide

theorem relay_B7 : RelayWall.B7 := ⟨nativeTurn, native_turn_ne⟩

theorem relay_B8 : RelayWall.B8 := by
  refine ⟨fun p => truthChart p.2 = true,
    ⟨(0, (1 : Seat)), by decide⟩, ⟨(0, (0 : Seat)), by decide⟩, ?_, ?_⟩
  · intro x y hx
    exact hx
  · intro x y hx
    exact Or.inl hx

theorem relay_B9 : RelayWall.B9 := native_turn_ne

theorem relay_B10 : RelayWall.B10 := by
  refine ⟨native_turn_injective, truthFormula, (0, (1 : Seat)), ?_, ?_⟩
  · simp [RelayWall, relayDen, truthFormula, evalRelay, truthChart]
  · intro hall
    have hfalse : ¬ relayDen truthFormula ((0, (0 : Seat)) : NativePoint) := by
      simp [relayDen, truthFormula, evalRelay, truthChart]
    exact hfalse (hall (0, 0))

theorem relay_B11 : RelayWall.B11 := by
  refine ⟨addressZero, address_zero_invariant, ?_, ?_, address_zero_is_not_relay_named⟩
  · intro h
    have hz : addressZero ((0, (0 : Seat)) : NativePoint) := by simp [addressZero]
    exact (Iff.of_eq (congrFun h (0, (0 : Seat)))).mp hz
  · intro h
    have hn : ¬ addressZero ((1, (0 : Seat)) : NativePoint) := by simp [addressZero]
    exact hn ((Iff.of_eq (congrFun h (1, (0 : Seat)))).mpr trivial)

theorem relay_B12 : RelayWall.B12 := by
  intro p
  exact ⟨1, nativeTurn p, by decide, rfl, native_turn_ne (nativeTurn p)⟩

theorem relay_all12 : All12 RelayWall :=
  ⟨relay_B1, relay_B2, relay_B3, relay_B4, relay_B5, relay_B6,
   relay_B7, relay_B8, relay_B9, relay_B10, relay_B11, relay_B12⟩

theorem foundation_stone_test_five :
    inAFrame .B (1 : Seat) = (7 : Seat) ∧
    inLocalFrame .B (7 : Seat) = (1 : Seat) ∧
    antipode ≠ magenta ∧
    (∀ seat, antipode (magenta seat) = magenta (antipode seat)) ∧
    shiftedTruth ≠ truthChart ∧
    shiftedTruth ≠ discoveryChart ∧
    (∀ message, Genuine message → Genuine (relay message)) ∧
    (∀ message, relay (relay message) = message) ∧
    answerOnly messageA = answerOnly messageB ∧
    AcceptFrom .A messageA ∧ ¬ AcceptFrom .A messageB ∧
    ¬ Genuine forgedFrame ∧ Genuine (relay messageA) ∧
    All12 RelayWall :=
  ⟨B_own_B1_is_A_B7, A_B7_is_B_own_B1, antipode_is_not_magenta,
   antipode_commutes_with_magenta, shifted_truth_is_not_truth,
   shifted_truth_is_not_discovery, relay_preserves_genuine, relay_twice,
   rfl, provenance_adds_source_policy_capability.2.1,
   provenance_adds_source_policy_capability.2.2, forged_frame_is_rejected,
   translated_frame_is_accepted, relay_all12⟩

#print axioms B_own_B1_is_A_B7
#print axioms antipode_is_not_magenta
#print axioms antipode_commutes_with_magenta
#print axioms shifted_truth_is_not_truth
#print axioms shifted_truth_is_not_discovery
#print axioms frame_transport_semantics
#print axioms frame_transport_twice
#print axioms relay_equivariance
#print axioms relay_preserves_genuine
#print axioms relay_twice
#print axioms provenance_adds_source_policy_capability
#print axioms forged_frame_is_rejected
#print axioms address_zero_is_not_relay_named
#print axioms relay_B1
#print axioms relay_all12
#print axioms foundation_stone_test_five

end FoundationStoneTestFive
