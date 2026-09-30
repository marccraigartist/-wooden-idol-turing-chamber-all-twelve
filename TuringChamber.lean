import FoundationStoneTest16BU
import WoodenIdolTuringBridgePhase2C
import WoodenIdolTuringBridgeB12
import WoodenIdolTuringBridgeCanonicalB12

/-!
# THE WOODEN IDOL — TURING CHAMBER

Headline aggregate for the Turing Chamber theorem chain.

The Lake library registers the retained Foundation Stone modules and
bridge modules as explicit roots.

The revised 16BO and 16BP use their canonical module names.
Superseded originals remain outside the active import graph.

Some experimental snapshots share namespaces and are checked as
separate roots.

The K31 B12 slice is included below. Its connection to the original
Stage3.System remains a separate verification obligation.
-/

#check FoundationStoneTest16BU.helix_halting_is_not_computable
#check FoundationStoneTest16BU.fixed_helix_program_exists
#check FoundationStoneTest16BU.turing_chamber_16BU_certificate
#check WoodenIdolTuringBridgePhase2C.phase2C_irreducibility_certificate
#check WoodenIdolTuringBridgeB12.turing_chamber_B12_bridge_certificate
#check WoodenIdolTuringBridgeCanonicalB12.canonical_K31_B12_bridge_certificate

#print axioms WoodenIdolTuringBridgeCanonicalB12.canonical_K31_B12_bridge_certificate
