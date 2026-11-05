import Mathlib.Tactic.Sat.FromLRAT

/-!
# Kernel-checked propositional refutation for eleven-phase saturation

The certificate is a concrete CNF/LRAT pair. The command invokes Mathlib's LRAT proof
constructor, which generates ordinary Lean proof terms and adds no axiom. The semantic
connection to row families is proved separately.
-/

open Lean Elab Term Command Mathlib.Tactic

elab "lrat_raw " n:ident ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let c ← unsafe evalTerm String (mkConst ``String) cnf
    let p ← unsafe evalTerm String (mkConst ``String) lrat
    let (_, ctx, _, proof) ← Sat.fromLRATAux c p name
    let formulaName := name ++ `formula
    addDecl <| Declaration.defnDecl {
      name := formulaName
      levelParams := []
      type := mkConst ``_root_.Sat.Fmla
      value := ctx
      hints := ReducibilityHints.regular 0
      safety := DefinitionSafety.safe }
    addDecl <| Declaration.thmDecl {
      name := name
      levelParams := []
      type := mkApp2 (mkConst ``_root_.Sat.Fmla.proof) (mkConst formulaName)
        (mkConst ``_root_.Sat.Clause.nil)
      value := proof }

namespace JSP000404Research.ElevenPhase

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lrat_raw packing_refutation
  (include_str "ElevenPhaseCertificate/packing.cnf")
  (include_str "ElevenPhaseCertificate/packing.lrat")

#print axioms packing_refutation

end JSP000404Research.ElevenPhase
