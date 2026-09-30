import FoundationStoneTest16BK

/-!
# THE TURING CHAMBER — TEST 16BL: PHYSICAL PRIME DECREMENT AND ZERO TEST

Lean 4.35.0-rc2 / pinned Mathlib.

The packed zero test is divisibility by the register's prime.  A primitive
division probe consumes A and leaves quotient in B, so a failed divisibility
test has destroyed the original number.  The verified restoration block
repairs that loss.

* remainder zero: transfer the quotient to A and take `positive`;
* remainder nonzero: transfer the quotient, multiply it by p using 16BK,
  add back the remembered finite remainder, and take `zero`.

Thus the divisible path performs packed decrement, while the nondivisible path
restores the packed state exactly.  Every executed transition is literal
two-counter increment or decrement/zero-test.  This file proves the two paths
as composable primitive blocks.  Allocating both behind one global typed
instruction label—and restricting the ambient `Nat` indices to finite reachable
support—is the next linker step, not hidden here.
-/

namespace FoundationStoneTest16BL

open FoundationStoneTest16AW

def mapTransferInstr {K : Type} (f : TLabel → K) : Instr TLabel → Instr K
  | .inc body next => .inc body (f next)
  | .dec body positive zero => .dec body (f positive) (f zero)
  | .halt => .halt

/-! The restoration program is indexed by the finite remainder discovered by
the division probe. -/

inductive RestoreLabel
  | transfer (l : TLabel)
  | bridge
  | multiply (l : FoundationStoneTest16BK.IncLabel)
  | multiplyBridge
  | add (remaining : Nat)
  | done
deriving DecidableEq, Repr

def restoreProgram (p r : Nat) : RestoreLabel → Instr RestoreLabel
  | .transfer .exit => .inc false .bridge
  | .transfer l => mapTransferInstr .transfer (transferProgram l)
  | .bridge => .dec false (.multiply (.mul .loop)) (.multiply (.mul .loop))
  | .multiply .done => .inc false .multiplyBridge
  | .multiply l =>
      match FoundationStoneTest16BK.incBlock p l with
      | .inc body next => .inc body (.multiply next)
      | .dec body positive zero => .dec body (.multiply positive) (.multiply zero)
      | .halt => .halt
  | .multiplyBridge => .dec false (.add r) (.add r)
  | .add 0 => .halt
  | .add (k + 1) => .inc false (if k = 0 then .done else .add k)
  | .done => .halt

def wrapState {L K : Type} (f : L → K) (s : State L) : State K :=
  ⟨f s.pc, s.a, s.b⟩

theorem run_wrap_of_step {L K : Type} (P : L → Instr L) (Q : K → Instr K)
    (f : L → K)
    (hs : ∀ s t, step P s = some t → step Q (wrapState f s) = some (wrapState f t)) :
    ∀ n s t, run P n s = some t → run Q n (wrapState f s) = some (wrapState f t) := by
  intro n
  induction n with
  | zero =>
      intro s t h
      simp only [run, Option.some.injEq] at h ⊢
      subst t
      rfl
  | succ n ih =>
      intro s t h
      unfold run at h ⊢
      cases h1 : step P s with
      | none => rw [h1] at h; contradiction
      | some s' =>
          rw [h1] at h
          rw [hs s s' h1]
          exact ih s' t h

theorem transfer_step_restore (p r : Nat) (s t : State TLabel)
    (h : step transferProgram s = some t) :
    step (restoreProgram p r) (wrapState RestoreLabel.transfer s) =
      some (wrapState RestoreLabel.transfer t) := by
  rcases s with ⟨pc,a,b⟩
  rcases t with ⟨pc',a',b'⟩
  unfold step at h ⊢
  cases pc with
  | exit => simp [transferProgram] at h
  | loop =>
      simp only [transferProgram, restoreProgram, mapTransferInstr, wrapState] at h ⊢
      by_cases hz : b = 0 <;> simp_all [FoundationStoneTest16AW.get,
        FoundationStoneTest16AW.set]
  | credit => simp_all [transferProgram, restoreProgram, mapTransferInstr,
      wrapState, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

theorem inc_step_restore (p r : Nat)
    (s t : State FoundationStoneTest16BK.IncLabel)
    (h : step (FoundationStoneTest16BK.incBlock p) s = some t) :
    step (restoreProgram p r) (wrapState RestoreLabel.multiply s) =
      some (wrapState RestoreLabel.multiply t) := by
  rcases s with ⟨pc,a,b⟩
  rcases t with ⟨pc',a',b'⟩
  have hdone : pc ≠ FoundationStoneTest16BK.IncLabel.done := by
    intro he
    subst pc
    simp [FoundationStoneTest16BK.incBlock, step] at h
  unfold step at h ⊢
  cases hi : FoundationStoneTest16BK.incBlock p pc with
  | halt => simp [hi] at h
  | inc body next =>
      cases body <;> simp_all [restoreProgram, wrapState, hdone,
        FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
  | dec body positive zero =>
      cases body with
      | false =>
          by_cases hz : a = 0 <;> simp_all [restoreProgram, wrapState, hdone,
            FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
      | true =>
          by_cases hz : b = 0 <;> simp_all [restoreProgram, wrapState, hdone,
            FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

theorem restore_transfer_embeds (p r : Nat) : ∀ n s t,
    run transferProgram n s = some t →
    run (restoreProgram p r) n (wrapState RestoreLabel.transfer s) =
      some (wrapState RestoreLabel.transfer t) :=
  run_wrap_of_step transferProgram (restoreProgram p r) RestoreLabel.transfer
    (transfer_step_restore p r)

theorem restore_inc_embeds (p r : Nat) : ∀ n s t,
    run (FoundationStoneTest16BK.incBlock p) n s = some t →
    run (restoreProgram p r) n (wrapState RestoreLabel.multiply s) =
      some (wrapState RestoreLabel.multiply t) :=
  run_wrap_of_step (FoundationStoneTest16BK.incBlock p) (restoreProgram p r)
    RestoreLabel.multiply (inc_step_restore p r)

theorem restore_bridge_one (p r q : Nat) :
    run (restoreProgram p r) 2 ⟨.transfer .exit, q, 0⟩ =
      some ⟨.multiply (.mul .loop), q, 0⟩ := by
  simp [run, step, restoreProgram, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

theorem restore_bridge_two (p r q : Nat) :
    run (restoreProgram p r) 2 ⟨.multiply .done, q, 0⟩ =
      some ⟨.add r, q, 0⟩ := by
  simp [run, step, restoreProgram, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

theorem add_remainder_general (p outer : Nat) : ∀ k a, 0 < k →
    run (restoreProgram p outer) k ⟨.add k, a, 0⟩ =
      some ⟨.done, a + k, 0⟩ := by
  intro k
  induction k with
  | zero => intro a hk; omega
  | succ k ih =>
      intro a _
      cases k with
      | zero => simp [run, step, restoreProgram, FoundationStoneTest16AW.get,
          FoundationStoneTest16AW.set]
      | succ k =>
          rw [show k + 1 + 1 = 1 + (k + 1) by omega, run_add]
          have h1 : run (restoreProgram p outer) 1
              ⟨RestoreLabel.add (1 + (k + 1)), a, 0⟩ =
                some ⟨RestoreLabel.add (k + 1), a + 1, 0⟩ := by
            simp [run, step, restoreProgram, FoundationStoneTest16AW.get,
              FoundationStoneTest16AW.set] <;> omega
          rw [h1]
          simp only
          have h := ih (a + 1) (by omega)
          simpa [Nat.add_assoc] using h

theorem add_remainder_exact (p r a : Nat) :
    run (restoreProgram p (r + 1)) (r + 1) ⟨.add (r + 1), a, 0⟩ =
      some ⟨.done, a + (r + 1), 0⟩ :=
  add_remainder_general p (r + 1) (r + 1) a (by omega)

/-- Reconstruction theorem: from quotient in B, restore `p*q+r` in A. -/
theorem restore_nonzero_remainder (p q r : Nat) (hp : 0 < p) (hr : 0 < r) :
    ∃ steps,
      run (restoreProgram p r) steps ⟨.transfer .loop, 0, q⟩ =
        some ⟨.done, p * q + r, 0⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  let s₁ := 2 * q + 1
  let s₂ := (3 * p + 1) * q + 6
  refine ⟨s₁ + 2 + s₂ + 2 + (k + 1), ?_⟩
  have ht := restore_transfer_embeds p (k + 1) s₁
    (⟨TLabel.loop, 0, q⟩ : State TLabel)
    (⟨TLabel.exit, q, 0⟩ : State TLabel)
    (by simpa [s₁] using transfer_exact 0 q)
  have hm := restore_inc_embeds p (k + 1) s₂
    (⟨FoundationStoneTest16BK.IncLabel.mul .loop, q, 0⟩ :
      State FoundationStoneTest16BK.IncLabel)
    (⟨FoundationStoneTest16BK.IncLabel.done, p * q, 0⟩ :
      State FoundationStoneTest16BK.IncLabel)
    (by simpa [s₂] using FoundationStoneTest16BK.inc_block_exact p q hp)
  simp only [wrapState] at ht hm
  rw [run_add, run_add, run_add, run_add, ht]
  simp only
  rw [restore_bridge_one]
  simp only
  rw [hm]
  simp only
  rw [restore_bridge_two]
  simp only
  rw [add_remainder_exact]

/-! The complete division probe is kept explicit. -/
theorem division_probe_exact (p n : Nat) (hp : 0 < p) :
    FoundationStoneTest16AV.run (FoundationStoneTest16AV.divProgram p)
        ((p + 1) * (n / p) + (n % p + 1))
        ⟨FoundationStoneTest16AV.Label.scan 0, n, 0⟩ =
      some ⟨FoundationStoneTest16AV.Label.exit (n % p), 0, n / p⟩ :=
  by simpa using FoundationStoneTest16AV.divmod_exact p n 0 hp

theorem physical_positive_result (p n : Nat) (hp : 0 < p) (hd : p ∣ n) :
    ∃ probeSteps restoreSteps,
      FoundationStoneTest16AV.run (FoundationStoneTest16AV.divProgram p) probeSteps
          ⟨FoundationStoneTest16AV.Label.scan 0, n, 0⟩ =
        some ⟨FoundationStoneTest16AV.Label.exit 0, 0, n / p⟩ ∧
      run transferProgram restoreSteps ⟨TLabel.loop, 0, n / p⟩ =
        some ⟨TLabel.exit, n / p, 0⟩ := by
  refine ⟨(p + 1) * (n / p) + (n % p + 1), 2 * (n / p) + 1, ?_, ?_⟩
  · have hm : n % p = 0 := Nat.mod_eq_zero_of_dvd hd
    simpa [hm] using division_probe_exact p n hp
  · simpa using transfer_exact 0 (n / p)

theorem physical_zero_result (p n : Nat) (hp : 0 < p) (hnd : ¬ p ∣ n) :
    ∃ probeSteps restoreSteps,
      FoundationStoneTest16AV.run (FoundationStoneTest16AV.divProgram p) probeSteps
          ⟨FoundationStoneTest16AV.Label.scan 0, n, 0⟩ =
        some ⟨FoundationStoneTest16AV.Label.exit (n % p), 0, n / p⟩ ∧
      run (restoreProgram p (n % p)) restoreSteps
          ⟨RestoreLabel.transfer .loop, 0, n / p⟩ =
        some ⟨RestoreLabel.done, n, 0⟩ := by
  have hr : 0 < n % p := by
    have hm : n % p ≠ 0 := by
      intro h
      exact hnd ((Nat.dvd_iff_mod_eq_zero).2 h)
    exact Nat.pos_of_ne_zero hm
  obtain ⟨steps, hs⟩ := restore_nonzero_remainder p (n / p) (n % p) hp hr
  refine ⟨(p + 1) * (n / p) + (n % p + 1), steps,
    division_probe_exact p n hp, ?_⟩
  have hn : p * (n / p) + n % p = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n p
  simpa [hn] using hs

/-! ## Installation in the five-prime packing -/

theorem packed_positive_branch_is_physical
    (c : FoundationStoneTest16BJ.Reg5 → Nat)
    (i : FoundationStoneTest16BJ.Reg5) (hi : 0 < c i) :
    ∃ probeSteps restoreSteps,
      FoundationStoneTest16AV.run
          (FoundationStoneTest16AV.divProgram (FoundationStoneTest16BJ.prime i))
          probeSteps
          ⟨FoundationStoneTest16AV.Label.scan 0,
            FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c), 0⟩ =
        some ⟨FoundationStoneTest16AV.Label.exit 0, 0,
          FoundationStoneTest16AM.pack
            (FoundationStoneTest16BJ.fromVec
              (Function.update c i (c i - 1)))⟩ ∧
      run transferProgram restoreSteps
          ⟨TLabel.loop, 0,
            FoundationStoneTest16AM.pack
              (FoundationStoneTest16BJ.fromVec
                (Function.update c i (c i - 1)))⟩ =
        some ⟨TLabel.exit,
          FoundationStoneTest16AM.pack
            (FoundationStoneTest16BJ.fromVec
              (Function.update c i (c i - 1))), 0⟩ := by
  let p := FoundationStoneTest16BJ.prime i
  let a := FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c)
  have hp : 0 < p := FoundationStoneTest16BK.selected_prime_positive i
  have hd : p ∣ a := (FoundationStoneTest16BJ.prime_dvd_pack_iff c i).2 hi
  obtain ⟨ps, rs, hprobe, hrestore⟩ := physical_positive_result p a hp hd
  have hdec := FoundationStoneTest16BJ.pack_update_dec c i hi
  refine ⟨ps, rs, ?_, ?_⟩
  · simpa [p, a, hdec] using hprobe
  · simpa [p, a, hdec] using hrestore

theorem packed_zero_branch_is_physical
    (c : FoundationStoneTest16BJ.Reg5 → Nat)
    (i : FoundationStoneTest16BJ.Reg5) (hi : c i = 0) :
    ∃ probeSteps restoreSteps,
      FoundationStoneTest16AV.run
          (FoundationStoneTest16AV.divProgram (FoundationStoneTest16BJ.prime i))
          probeSteps
          ⟨FoundationStoneTest16AV.Label.scan 0,
            FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c), 0⟩ =
        some ⟨FoundationStoneTest16AV.Label.exit
          (FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c) %
            FoundationStoneTest16BJ.prime i), 0,
          FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c) /
            FoundationStoneTest16BJ.prime i⟩ ∧
      run (restoreProgram (FoundationStoneTest16BJ.prime i)
          (FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c) %
            FoundationStoneTest16BJ.prime i)) restoreSteps
          ⟨RestoreLabel.transfer .loop, 0,
            FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c) /
              FoundationStoneTest16BJ.prime i⟩ =
        some ⟨RestoreLabel.done,
          FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c), 0⟩ := by
  let p := FoundationStoneTest16BJ.prime i
  let a := FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c)
  have hp : 0 < p := FoundationStoneTest16BK.selected_prime_positive i
  have hnd : ¬ p ∣ a := by
    rw [FoundationStoneTest16BJ.prime_dvd_pack_iff]
    omega
  simpa [p, a] using physical_zero_result p a hp hnd

/-! Red control: after a failed probe, keeping only the quotient does not
preserve the original number. -/
theorem quotient_alone_loses_remainder (p n : Nat) (hp : 0 < p)
    (hnd : ¬ p ∣ n) : p * (n / p) ≠ n := by
  have hr : n % p ≠ 0 := by
    intro h
    exact hnd ((Nat.dvd_iff_mod_eq_zero).2 h)
  have hn : p * (n / p) + n % p = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n p
  omega

theorem turing_chamber_16BL_certificate :
    (∀ p n, 0 < p → p ∣ n →
      ∃ probeSteps restoreSteps,
        FoundationStoneTest16AV.run (FoundationStoneTest16AV.divProgram p) probeSteps
            ⟨FoundationStoneTest16AV.Label.scan 0, n, 0⟩ =
          some ⟨FoundationStoneTest16AV.Label.exit 0, 0, n / p⟩ ∧
        run transferProgram restoreSteps ⟨TLabel.loop, 0, n / p⟩ =
          some ⟨TLabel.exit, n / p, 0⟩) ∧
    (∀ p n, 0 < p → ¬ p ∣ n →
      ∃ probeSteps restoreSteps,
        FoundationStoneTest16AV.run (FoundationStoneTest16AV.divProgram p) probeSteps
            ⟨FoundationStoneTest16AV.Label.scan 0, n, 0⟩ =
          some ⟨FoundationStoneTest16AV.Label.exit (n % p), 0, n / p⟩ ∧
        run (restoreProgram p (n % p)) restoreSteps
            ⟨RestoreLabel.transfer .loop, 0, n / p⟩ =
          some ⟨RestoreLabel.done, n, 0⟩) ∧
    (∀ p n, 0 < p → ¬ p ∣ n → p * (n / p) ≠ n) ∧
    (∀ c i, 0 < c i →
      ∃ probeSteps restoreSteps,
        FoundationStoneTest16AV.run
            (FoundationStoneTest16AV.divProgram (FoundationStoneTest16BJ.prime i))
            probeSteps
            ⟨FoundationStoneTest16AV.Label.scan 0,
              FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c), 0⟩ =
          some ⟨FoundationStoneTest16AV.Label.exit 0, 0,
            FoundationStoneTest16AM.pack
              (FoundationStoneTest16BJ.fromVec
                (Function.update c i (c i - 1)))⟩ ∧
        run transferProgram restoreSteps
            ⟨TLabel.loop, 0,
              FoundationStoneTest16AM.pack
                (FoundationStoneTest16BJ.fromVec
                  (Function.update c i (c i - 1)))⟩ =
          some ⟨TLabel.exit,
            FoundationStoneTest16AM.pack
              (FoundationStoneTest16BJ.fromVec
                (Function.update c i (c i - 1))), 0⟩) :=
  ⟨physical_positive_result, physical_zero_result, quotient_alone_loses_remainder,
   packed_positive_branch_is_physical⟩

#print axioms restore_nonzero_remainder
#print axioms physical_positive_result
#print axioms physical_zero_result
#print axioms packed_positive_branch_is_physical
#print axioms packed_zero_branch_is_physical
#print axioms quotient_alone_loses_remainder
#print axioms turing_chamber_16BL_certificate

end FoundationStoneTest16BL
