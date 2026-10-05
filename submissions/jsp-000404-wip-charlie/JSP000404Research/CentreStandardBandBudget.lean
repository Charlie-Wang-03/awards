
import JSP000404Research.CentreStandardBandBudgetCore
import Mathlib.Tactic

/-!
# Centre exponent to standard-band one-layer budget

LocalDirectionCycle proves the exact one-dimensional inequality

  localExponent(i) + card(incidentBands_{n+1}(i)) <= n+1.

For the standard (n+1)-band OrderedEdgeColoring, incidentBands are exactly the
active colours.

Therefore, once the remaining projective-cut bridge identifies

  localExponent(i) = centreExponent(i),

the genuine Sendov centre exponent satisfies

  centreExponent(i) + card(active(i)) <= n+1,

equivalently

  card(active(i)) <= n-centreExponent(i)+1

when centreExponent(i)<=n.

No additional geometry or profile hypothesis is needed at this stage.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring



end DirectionData
end JSP000404Research
