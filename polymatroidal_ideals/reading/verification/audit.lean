import Characterizations.AuditCore
import Characterizations.AuditSectionFour
import Characterizations.AuditTriangular
import Characterizations.AuditZeroBoundary
import Characterizations.AuditSectionFive

/-! Complete principal-theorem audit. Each imported audit fails on any
transitive axiom other than `propext`, `Classical.choice`, and `Quot.sound`.
Exact checked-environment dependency graphs are exported by section.
-/
