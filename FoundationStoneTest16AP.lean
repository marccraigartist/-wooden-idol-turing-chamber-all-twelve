import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AP: THE EFFECTIVE PRIME ENTRANCE

Lean 4.35.0-rc2 / pinned Mathlib.

The five logical counters used by the TM2 simulation are encoded as

  2^c0 * 3^c1 * 5^c2 * 7^c3 * 11^temp.

16AM proved that this encoding is injective and has the intended valuation
semantics.  Here Lean proves the separate effectiveness obligation: producing
the packed initial counter is primitive recursive.  Thus the eventual
many-one reduction will not hide an oracle in its input translation.
-/

namespace FoundationStoneTest16AP

/-- A product presentation is used so Mathlib's existing `Primcodable`
instances apply without a custom encoding. -/
abbrev Five := Nat × (Nat × (Nat × (Nat × Nat)))

def c0 (s : Five) := s.1
def c1 (s : Five) := s.2.1
def c2 (s : Five) := s.2.2.1
def c3 (s : Five) := s.2.2.2.1
def temp (s : Five) := s.2.2.2.2

def pack (s : Five) : Nat :=
  2 ^ c0 s * 3 ^ c1 s * 5 ^ c2 s * 7 ^ c3 s * 11 ^ temp s

private theorem pow_prim : Primrec₂ (fun x y : Nat => x ^ y) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

private theorem pc0 : Primrec c0 := Primrec.fst
private theorem pc1 : Primrec c1 := Primrec.fst.comp Primrec.snd
private theorem pc2 : Primrec c2 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem pc3 : Primrec c3 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
private theorem ptemp : Primrec temp :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem ppow (k : Nat) {f : Five → Nat} (hf : Primrec f) :
    Primrec (fun s => k ^ f s) :=
  pow_prim.comp (Primrec.const k) hf

theorem pack_primrec : Primrec pack := by
  unfold pack
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_mul.comp (ppow 2 pc0) (ppow 3 pc1))
        (ppow 5 pc2))
      (ppow 7 pc3))
    (ppow 11 ptemp)

theorem pack_computable : Computable pack := pack_primrec.to_comp

/-- A complete problem instance consists of a finite program code and the two
physical counters.  Only A is loaded; B starts as genuine zero scratch. -/
def initialProblem (programCode : Nat) (s : Five) : Nat × (Nat × Nat) :=
  (programCode, (pack s, 0))

theorem initialProblem_primrec (programCode : Nat) :
    Primrec (initialProblem programCode) := by
  exact Primrec.pair (Primrec.const programCode)
    (Primrec.pair pack_primrec (Primrec.const 0))

theorem initialProblem_computable (programCode : Nat) :
    Computable (initialProblem programCode) :=
  (initialProblem_primrec programCode).to_comp

/-! Red control: replacing the five exponents by their sum is effective but
not injective.  Effectiveness alone is not semantic correctness. -/

def badPack (s : Five) : Nat := c0 s + c1 s + c2 s + c3 s + temp s

def leftWitness : Five := (1, (0, (0, (0, 0))))
def rightWitness : Five := (0, (1, (0, (0, 0))))

theorem bad_pack_collision :
    badPack leftWitness = badPack rightWitness := by decide

theorem bad_pack_not_injective : ¬ Function.Injective badPack := by
  intro h
  have e := h bad_pack_collision
  have n : leftWitness ≠ rightWitness := by decide
  exact n e

theorem turing_chamber_16AP_certificate (programCode : Nat) :
    Computable pack ∧ Computable (initialProblem programCode) ∧
      ¬ Function.Injective badPack :=
  ⟨pack_computable, initialProblem_computable programCode,
   bad_pack_not_injective⟩

#print axioms pack_primrec
#print axioms initialProblem_primrec
#print axioms bad_pack_not_injective
#print axioms turing_chamber_16AP_certificate

end FoundationStoneTest16AP
