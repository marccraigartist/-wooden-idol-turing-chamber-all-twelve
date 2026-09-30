/-!
# THE COUNTER-ROTATING HELICES — FOUNDATION STONE TEST 16P

Core Lean only; no imports.

16O proved transfer on two naked counters.  This test restores the twelve-seat
clock carried by each body and installs the antipodal `+6` frame translation.

For an A→B transfer:

* pickup makes A descend one helix level and move one seat backward;
* delivery makes B climb one helix level and move one seat forward;
* between them, one unit is held by the relay;
* every clock always shows its own height modulo 12.

Lean certifies:

1. every pickup and delivery preserves the helix-shadow invariant;
2. after `2n` primitive steps, A has height `amount-n` and B has
   `received+n`, with the corresponding clock readings;
3. after `2n+1` steps, the next unit is in the relay;
4. transferring twelve units sends heights `(12,0)` to `(0,12)` in 25 steps,
   while both visible clocks begin and end at B12;
5. B's local B1 is A-frame B7, but this is a frame translation—not the
   transfer step itself;
6. during the twelve-unit journey the two bodies occupy the same physical
   clock direction (after translating B into A's frame) exactly after three
   and nine completed transfers;
7. at the first completed transfer A reads B11, B reads local B1, and that B1
   is A-frame B7: the three readings are distinct and explicit.

So the circle returns while the helix ownership changes.  The antipode tells
how the bodies compare their clocks; the relay tells how height crosses between
them.  They are compatible layers, not the same operation.
-/

namespace FoundationStoneTest16P

abbrev Body := Bool
abbrev Seat := Fin 12
abbrev InstrCode := Nat × Body × Nat × Nat
abbrev Program := List InstrCode

def forward (k : Seat) : Seat := k + 1
def back (k : Seat) : Seat := k + 11

def seatOfHeight (n : Nat) : Seat := ⟨n % 12, Nat.mod_lt _ (by decide)⟩

structure BodyState where
  height : Nat
  seat : Seat
deriving DecidableEq

def canonicalBody (n : Nat) : BodyState := ⟨n, seatOfHeight n⟩
def climb (s : BodyState) : BodyState := ⟨s.height + 1, forward s.seat⟩
def descend (s : BodyState) : BodyState := ⟨s.height - 1, back s.seat⟩

theorem climb_canonical (n : Nat) : climb (canonicalBody n) = canonicalBody (n + 1) := by
  simp only [climb, canonicalBody, BodyState.mk.injEq]
  constructor
  · trivial
  · apply Fin.ext
    simp [forward, seatOfHeight, Fin.val_add]

theorem descend_canonical (n : Nat) :
    descend (canonicalBody (n + 1)) = canonicalBody n := by
  simp only [descend, canonicalBody, BodyState.mk.injEq]
  constructor
  · omega
  · apply Fin.ext
    simp [back, seatOfHeight, Fin.val_add]
    omega

def Shadow (s : BodyState) : Prop := s.seat.val = s.height % 12

theorem canonical_shadow (n : Nat) : Shadow (canonicalBody n) := rfl

inductive Instr
  | up (b : Body) (next : Nat)
  | down (b : Body) (next ground : Nat)
  | stop
deriving DecidableEq

def stopCode : InstrCode := (0, false, 0, 0)
def upCode (b : Body) (next : Nat) : InstrCode := (1, b, next, 0)
def downCode (b : Body) (next ground : Nat) : InstrCode := (2, b, next, ground)

def decodeInstr (i : InstrCode) : Instr :=
  if i.1 = 1 then .up i.2.1 i.2.2.1
  else if i.1 = 2 then .down i.2.1 i.2.2.1 i.2.2.2
  else .stop

def fetch (p : Program) (pc : Nat) : Instr :=
  decodeInstr ((p[pc]?).getD stopCode)

structure HState where
  pc : Nat
  bodyA : BodyState
  bodyB : BodyState
deriving DecidableEq

def get (h : HState) : Body → BodyState
  | false => h.bodyA
  | true => h.bodyB

def set (h : HState) (pc : Nat) : Body → BodyState → HState
  | false, v => ⟨pc, v, h.bodyB⟩
  | true, v => ⟨pc, h.bodyA, v⟩

def hstep (p : Program) (h : HState) : Option HState :=
  match fetch p h.pc with
  | .up b nx => some (set h nx b (climb (get h b)))
  | .down b nx gr =>
      if (get h b).height = 0 then some { h with pc := gr }
      else some (set h nx b (descend (get h b)))
  | .stop => none

def hrun (p : Program) : Nat → HState → Option HState
  | 0, h => some h
  | n + 1, h =>
      match hstep p h with
      | none => none
      | some h' => hrun p n h'

theorem hrun_add (p : Program) (m n : Nat) (h : HState) :
    hrun p (m + n) h =
      match hrun p m h with
      | none => none
      | some h' => hrun p n h' := by
  induction m generalizing h with
  | zero => simp [hrun]
  | succ m ih =>
      simp only [Nat.succ_add]
      change
        (match hstep p h with
          | none => none
          | some h' => hrun p (m + n) h') =
        match (match hstep p h with
          | none => none
          | some h' => hrun p m h') with
        | none => none
        | some h' => hrun p n h'
      cases hstep p h with
      | none => rfl
      | some h' => simp only; exact ih h'

/-! ## 1. The geometric A→B relay -/

def transferProgram (exit : Nat) : Program :=
  [downCode false 1 exit, upCode true 0]

def entryH (amount received : Nat) : HState :=
  ⟨0, canonicalBody amount, canonicalBody received⟩

def betweenH (remaining received : Nat) : HState :=
  ⟨1, canonicalBody remaining, canonicalBody received⟩

def movedH (exit amount received : Nat) : HState :=
  ⟨exit, canonicalBody 0, canonicalBody (received + amount)⟩

def BothShadow (h : HState) : Prop := Shadow h.bodyA ∧ Shadow h.bodyB

theorem entry_has_both_shadows (amount received : Nat) : BothShadow (entryH amount received) :=
  ⟨canonical_shadow _, canonical_shadow _⟩

theorem between_has_both_shadows (remaining received : Nat) :
    BothShadow (betweenH remaining received) :=
  ⟨canonical_shadow _, canonical_shadow _⟩

theorem moved_has_both_shadows (exit amount received : Nat) :
    BothShadow (movedH exit amount received) :=
  ⟨canonical_shadow _, canonical_shadow _⟩

/-- Pickup: A descends/backward and the relay becomes occupied. -/
theorem pickup_geometry (exit amount received : Nat) :
    hstep (transferProgram exit) (entryH (amount + 1) received) =
      some (betweenH amount received) := by
  have hp : (canonicalBody (amount + 1)).height ≠ 0 := by
    simp [canonicalBody]
  simp [hstep, transferProgram, fetch, decodeInstr, downCode, entryH, betweenH,
    get, set, hp, descend_canonical]

/-- Delivery: B climbs/forward and the relay becomes empty. -/
theorem delivery_geometry (exit amount received : Nat) :
    hstep (transferProgram exit) (betweenH amount received) =
      some (entryH amount (received + 1)) := by
  simp [hstep, transferProgram, fetch, decodeInstr, upCode, betweenH, entryH,
    get, set, climb_canonical]

theorem transfer_cycle (exit amount received : Nat) :
    hrun (transferProgram exit) 2 (entryH (amount + 1) received) =
      some (entryH amount (received + 1)) := by
  unfold hrun
  rw [pickup_geometry]
  simp only
  unfold hrun
  rw [delivery_geometry]
  rfl

theorem transfer_zero (exit amount received : Nat) :
    hstep (transferProgram exit) (entryH 0 (received + amount)) =
      some (movedH exit amount received) := by
  simp [hstep, transferProgram, fetch, decodeInstr, downCode, entryH, movedH,
    canonicalBody, seatOfHeight, get, Nat.add_comm]

/-! ## 2. Exact counter-rotating prefixes -/

theorem transfer_even_prefix (exit amount received : Nat) :
    ∀ n, n ≤ amount →
      hrun (transferProgram exit) (2 * n) (entryH amount received) =
        some (entryH (amount - n) (received + n)) := by
  intro n hn
  induction n generalizing amount received with
  | zero => simp [hrun]
  | succ n ih =>
      obtain ⟨h, rfl⟩ : ∃ h, amount = h + 1 := ⟨amount - 1, by omega⟩
      rw [show 2 * (n + 1) = 2 + 2 * n by omega, hrun_add, transfer_cycle]
      simp only
      have hn' : n ≤ h := by omega
      have hrem : h + 1 - (n + 1) = h - n := by omega
      have hgot : received + (n + 1) = (received + 1) + n := by omega
      rw [hrem, hgot, ih h (received + 1) hn']

theorem transfer_odd_prefix (exit amount received n : Nat) (hn : n < amount) :
    hrun (transferProgram exit) (2 * n + 1) (entryH amount received) =
      some (betweenH (amount - (n + 1)) (received + n)) := by
  rw [hrun_add, transfer_even_prefix exit amount received n (by omega)]
  simp only
  obtain ⟨h, heq⟩ : ∃ h, amount - n = h + 1 :=
    ⟨amount - (n + 1), by omega⟩
  rw [heq]
  unfold hrun
  rw [pickup_geometry]
  simp only
  have hh : h = amount - (n + 1) := by omega
  rw [hh]
  rfl

theorem transfer_completes (exit amount received : Nat) :
    hrun (transferProgram exit) (2 * amount + 1) (entryH amount received) =
      some (movedH exit amount received) := by
  rw [hrun_add, transfer_even_prefix exit amount received amount (Nat.le_refl _)]
  simp only [Nat.sub_self]
  unfold hrun
  rw [transfer_zero]
  rfl

/-! ## 3. The twelve-unit clock/helix separation -/

def twelveStart : HState := entryH 12 0
def twelveEnd : HState := movedH 2 12 0

theorem twelve_transfer_takes_twenty_five :
    hrun (transferProgram 2) 25 twelveStart = some twelveEnd := by
  simpa [twelveStart, twelveEnd] using transfer_completes 2 12 0

/-- Both visible clocks are B12 before and after, but the heights are exchanged. -/
theorem clocks_return_heights_do_not :
    twelveStart.bodyA.seat = 0 ∧ twelveStart.bodyB.seat = 0 ∧
    twelveEnd.bodyA.seat = 0 ∧ twelveEnd.bodyB.seat = 0 ∧
    twelveStart.bodyA.height = 12 ∧ twelveStart.bodyB.height = 0 ∧
    twelveEnd.bodyA.height = 0 ∧ twelveEnd.bodyB.height = 12 := by decide

/-- Every even boundary of the twelve-transfer journey, including both ends. -/
theorem twelve_boundary_state (n : Fin 13) :
    hrun (transferProgram 2) (2 * n.val) twelveStart =
      some (entryH (12 - n.val) n.val) := by
  simpa [twelveStart] using
    transfer_even_prefix 2 12 0 n.val (by omega)

/-- The exact counter-rotating readings: A goes backward, B goes forward. -/
theorem twelve_boundary_readings (n : Fin 13) :
    (entryH (12 - n.val) n.val).bodyA.seat.val = (12 - n.val) % 12 ∧
    (entryH (12 - n.val) n.val).bodyB.seat.val = n.val % 12 := by
  exact ⟨rfl, rfl⟩

/-! ## 4. The antipodal frame is a comparison layer -/

/-- Translate a seat named in B's local clock into A's clock frame. -/
def bToAFrame (k : Seat) : Seat := k + 6

theorem Bs_B1_is_As_B7 : bToAFrame 1 = 7 := by decide
theorem Bs_B7_is_As_B1 : bToAFrame 7 = 1 := by decide

/-- After the first completed transfer: A reads B11, B reads local B1, and
that local B1 is A-frame B7.  It is not a direct B1→B7 transfer. -/
theorem first_transfer_three_readings :
    (entryH 11 1).bodyA.seat = 11 ∧
    (entryH 11 1).bodyB.seat = 1 ∧
    bToAFrame (entryH 11 1).bodyB.seat = 7 := by decide

/-- In the twelve-unit journey, translated physical alignment occurs exactly
at n=3 and n=9 completed transfers—not at every antipodal name-pair. -/
theorem physical_alignment_exactly_three_and_nine :
    ∀ n : Fin 13,
      ((entryH (12 - n.val) n.val).bodyA.seat =
        bToAFrame (entryH (12 - n.val) n.val).bodyB.seat) ↔
      (n.val = 3 ∨ n.val = 9) := by decide

theorem alignment_readings :
    (entryH 9 3).bodyA.seat = 9 ∧
    bToAFrame (entryH 9 3).bodyB.seat = 9 ∧
    (entryH 3 9).bodyA.seat = 3 ∧
    bToAFrame (entryH 3 9).bodyB.seat = 3 := by decide

/-! ## 5. The relay token remains necessary with clocks restored -/

def bodyHeight (h : HState) : Nat := h.bodyA.height + h.bodyB.height
def relayToken (h : HState) : Nat := if h.pc = 1 then 1 else 0
def totalHeight (h : HState) : Nat := bodyHeight h + relayToken h

theorem boundary_height_conserved (amount received n : Nat) (hn : n ≤ amount) :
    totalHeight (entryH (amount - n) (received + n)) = amount + received := by
  simp [totalHeight, bodyHeight, relayToken, entryH, canonicalBody]
  omega

theorem midpoint_height_needs_token (amount received n : Nat) (hn : n < amount) :
    bodyHeight (betweenH (amount - (n + 1)) (received + n)) + 1 =
      amount + received ∧
    totalHeight (betweenH (amount - (n + 1)) (received + n)) =
      amount + received := by
  constructor <;> simp [totalHeight, bodyHeight, relayToken, betweenH, canonicalBody] <;>
    omega

/-! ## Certificate -/

theorem counter_rotating_helices_certificate :
    hrun (transferProgram 2) 25 twelveStart = some twelveEnd ∧
    (twelveStart.bodyA.seat = 0 ∧ twelveStart.bodyB.seat = 0 ∧
      twelveEnd.bodyA.seat = 0 ∧ twelveEnd.bodyB.seat = 0) ∧
    (twelveStart.bodyA.height = 12 ∧ twelveStart.bodyB.height = 0 ∧
      twelveEnd.bodyA.height = 0 ∧ twelveEnd.bodyB.height = 12) ∧
    bToAFrame 1 = 7 ∧
    (∀ n : Fin 13,
      ((entryH (12 - n.val) n.val).bodyA.seat =
        bToAFrame (entryH (12 - n.val) n.val).bodyB.seat) ↔
      (n.val = 3 ∨ n.val = 9)) :=
  ⟨twelve_transfer_takes_twenty_five,
   ⟨clocks_return_heights_do_not.1, clocks_return_heights_do_not.2.1,
    clocks_return_heights_do_not.2.2.1, clocks_return_heights_do_not.2.2.2.1⟩,
   ⟨clocks_return_heights_do_not.2.2.2.2.1,
    clocks_return_heights_do_not.2.2.2.2.2.1,
    clocks_return_heights_do_not.2.2.2.2.2.2.1,
    clocks_return_heights_do_not.2.2.2.2.2.2.2⟩,
   Bs_B1_is_As_B7, physical_alignment_exactly_three_and_nine⟩

#print axioms climb_canonical
#print axioms descend_canonical
#print axioms hrun_add
#print axioms pickup_geometry
#print axioms delivery_geometry
#print axioms transfer_even_prefix
#print axioms transfer_odd_prefix
#print axioms transfer_completes
#print axioms twelve_transfer_takes_twenty_five
#print axioms clocks_return_heights_do_not
#print axioms twelve_boundary_state
#print axioms Bs_B1_is_As_B7
#print axioms first_transfer_three_readings
#print axioms physical_alignment_exactly_three_and_nine
#print axioms alignment_readings
#print axioms midpoint_height_needs_token
#print axioms counter_rotating_helices_certificate

end FoundationStoneTest16P
