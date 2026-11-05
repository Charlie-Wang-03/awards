import JSP000404Research.OriginalFortyCases

import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

-- collectAxioms is the same transitive collector used by #print axioms.
-- Select by defining module, so private declarations are included too.
-- Dependencies in Mathlib/Lean are followed by collectAxioms, not omitted.
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut modules := 0
  let mut declarations := 0
  let mut failures : Array Name := #[]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    let modText := modName.toString
    if modText == "JSP000404Research" ||
        modText.startsWith "JSP000404Research." ||
        modText.startsWith "JSP404." ||
        modText.startsWith "Jsp000404." then
      modules := modules + 1
      let data := env.header.moduleData[i]!
      for name in data.constNames do
        declarations := declarations + 1
        if ((env.setExporting false).find? name).isNone then
          throwError "Declaration unavailable to the audit: {name}"
        let axs ← liftCoreM <| Lean.collectAxioms name
        liftIO <| IO.println s!"AXIOMS\t{modName}\t{name}\t{axs}"
        if axs.any (fun ax => !allowed.contains ax) then
          failures := failures.push name
  liftIO <| IO.println s!"AUDIT_COUNTS modules={modules} declarations={declarations} failures={failures.size}"
  if modules == 0 || declarations == 0 then
    throwError "Empty audit: no research declarations were inspected"
  if !failures.isEmpty then
    throwError "Unexpected transitive axioms in {failures.size} declarations: {failures}"
  logInfo "AXIOM_AUDIT_PASS for the imported research closure only; the original all-N lower theorem is absent"

#check JSP000404Research.NinePhase.catalog_completion
#check JSP000404Research.NinePhase.no_full_cover_avoiding_cores
#check JSP000404Research.NinePhase.core_not_coherent
#check JSP000404Research.NinePhase.card_le_twenty_of_coherent_rows
#check JSP000404Research.OrderedWires.card_le_twenty_of_winding
#check JSP000404Research.planar_card_le_twenty_of_strict_angles
#check JSP000404Research.planar_four_fifths_angle
#check JSP000404Research.original_lower_three_through_forty
