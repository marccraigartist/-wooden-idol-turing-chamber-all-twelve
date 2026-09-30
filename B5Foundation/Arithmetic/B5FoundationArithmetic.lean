import Foundation.FirstOrder.Incompleteness.Definability

/-!
# Arithmetic-only B5 prerequisite check

No Chamber module is imported and the containing Lake package has no Chamber
dependency. These declarations test the exact arithmetic facts needed by the
adapter, using the names exported by the pinned Foundation revision.

Importing Definability is intentional: at this pinned Foundation revision it
exports the canonical Delta-1 instances for the arithmetic induction schemes,
allowing the I-Sigma-1 theory itself to instantiate the hypotheses required by
the formalized second incompleteness theorem.

This file does not assert a Chamber certificate.
-/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace TuringChamberGodelArithmetic

set_option autoImplicit false

theorem isigma1_falsum_unprovable :
    𝗜𝚺₁ ⊬ (⊥ : ArithmeticSentence) := by
  exact Entailment.Consistent.not_bot (𝓢 := 𝗜𝚺₁)

theorem isigma1_consistency_unprovable :
    𝗜𝚺₁ ⊬ (𝗜𝚺₁).consistent.val := by
  exact consistent_unprovable 𝗜𝚺₁

theorem isigma1_verum_provable :
    𝗜𝚺₁ ⊢ (⊤ : ArithmeticSentence) := by
  exact FFL.Entailment.verum

#print axioms isigma1_falsum_unprovable
#print axioms isigma1_consistency_unprovable
#print axioms isigma1_verum_provable

end TuringChamberGodelArithmetic
