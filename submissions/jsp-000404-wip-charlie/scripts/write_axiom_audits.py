"""Generate two standalone Lean audits in the project's ignored artifacts/.

The umbrella and admitted root remain separate checks. Neither is a theorem
of the original problem. The admitted audit is expected to fail on sorryAx.
Run the generated files with `lake env lean` after their targets build.
"""

from pathlib import Path
import argparse


BODY = r'''
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
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, help="Directory inside this project's artifacts/")
    args = parser.parse_args()
    project = Path(__file__).resolve().parent.parent
    artifacts = (project / "artifacts").resolve()
    destination = Path(args.output).resolve()
    if not destination.is_relative_to(artifacts):
        parser.error("The output directory must be inside this project's artifacts/.")
    destination.mkdir(parents=True, exist_ok=True)
    targets = {
        "RootAxiomAudit": "JSP000404Research",
        "AdmittedAxiomAudit": "JSP000404Research.PlanarLowerBranchProofAdmittedWIP",
    }
    for filename, target in targets.items():
        path = destination / f"{filename}.lean"
        path.write_text(f"import {target}\n" + BODY, encoding="utf-8", newline="\n")
        print(path)


if __name__ == "__main__":
    main()
