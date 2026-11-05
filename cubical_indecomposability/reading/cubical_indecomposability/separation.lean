import cubical_indecomposability.certificates.separation00
import cubical_indecomposability.certificates.separation01
import cubical_indecomposability.certificates.separation02
import cubical_indecomposability.certificates.separation03
import cubical_indecomposability.certificates.separation04
import cubical_indecomposability.certificates.separation05
import cubical_indecomposability.certificates.separation06
import cubical_indecomposability.certificates.separation07
import cubical_indecomposability.certificates.separation08
import cubical_indecomposability.certificates.separation09
import cubical_indecomposability.certificates.separation10
import cubical_indecomposability.certificates.separation11
import cubical_indecomposability.separating_witness
import Mathlib.Tactic.FinCases

/-! Exact integer arithmetic and finite incidences, checked by Lean's kernel.
`decide +kernel` below proves closed propositions by reduction.  It invokes no native
oracle and introduces no mathematical assumptions.  Row lemmas keep the
kernel reduction and subsequent rebuilds small.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability

theorem separatingData (v w : Fin 144) (h : v ≠ w) :
    incident (separatingWitness v w) v ∧ ¬incident (separatingWitness v w) w := by
  fin_cases v
  · exact separatingRow000 w h
  · exact separatingRow001 w h
  · exact separatingRow002 w h
  · exact separatingRow003 w h
  · exact separatingRow004 w h
  · exact separatingRow005 w h
  · exact separatingRow006 w h
  · exact separatingRow007 w h
  · exact separatingRow008 w h
  · exact separatingRow009 w h
  · exact separatingRow010 w h
  · exact separatingRow011 w h
  · exact separatingRow012 w h
  · exact separatingRow013 w h
  · exact separatingRow014 w h
  · exact separatingRow015 w h
  · exact separatingRow016 w h
  · exact separatingRow017 w h
  · exact separatingRow018 w h
  · exact separatingRow019 w h
  · exact separatingRow020 w h
  · exact separatingRow021 w h
  · exact separatingRow022 w h
  · exact separatingRow023 w h
  · exact separatingRow024 w h
  · exact separatingRow025 w h
  · exact separatingRow026 w h
  · exact separatingRow027 w h
  · exact separatingRow028 w h
  · exact separatingRow029 w h
  · exact separatingRow030 w h
  · exact separatingRow031 w h
  · exact separatingRow032 w h
  · exact separatingRow033 w h
  · exact separatingRow034 w h
  · exact separatingRow035 w h
  · exact separatingRow036 w h
  · exact separatingRow037 w h
  · exact separatingRow038 w h
  · exact separatingRow039 w h
  · exact separatingRow040 w h
  · exact separatingRow041 w h
  · exact separatingRow042 w h
  · exact separatingRow043 w h
  · exact separatingRow044 w h
  · exact separatingRow045 w h
  · exact separatingRow046 w h
  · exact separatingRow047 w h
  · exact separatingRow048 w h
  · exact separatingRow049 w h
  · exact separatingRow050 w h
  · exact separatingRow051 w h
  · exact separatingRow052 w h
  · exact separatingRow053 w h
  · exact separatingRow054 w h
  · exact separatingRow055 w h
  · exact separatingRow056 w h
  · exact separatingRow057 w h
  · exact separatingRow058 w h
  · exact separatingRow059 w h
  · exact separatingRow060 w h
  · exact separatingRow061 w h
  · exact separatingRow062 w h
  · exact separatingRow063 w h
  · exact separatingRow064 w h
  · exact separatingRow065 w h
  · exact separatingRow066 w h
  · exact separatingRow067 w h
  · exact separatingRow068 w h
  · exact separatingRow069 w h
  · exact separatingRow070 w h
  · exact separatingRow071 w h
  · exact separatingRow072 w h
  · exact separatingRow073 w h
  · exact separatingRow074 w h
  · exact separatingRow075 w h
  · exact separatingRow076 w h
  · exact separatingRow077 w h
  · exact separatingRow078 w h
  · exact separatingRow079 w h
  · exact separatingRow080 w h
  · exact separatingRow081 w h
  · exact separatingRow082 w h
  · exact separatingRow083 w h
  · exact separatingRow084 w h
  · exact separatingRow085 w h
  · exact separatingRow086 w h
  · exact separatingRow087 w h
  · exact separatingRow088 w h
  · exact separatingRow089 w h
  · exact separatingRow090 w h
  · exact separatingRow091 w h
  · exact separatingRow092 w h
  · exact separatingRow093 w h
  · exact separatingRow094 w h
  · exact separatingRow095 w h
  · exact separatingRow096 w h
  · exact separatingRow097 w h
  · exact separatingRow098 w h
  · exact separatingRow099 w h
  · exact separatingRow100 w h
  · exact separatingRow101 w h
  · exact separatingRow102 w h
  · exact separatingRow103 w h
  · exact separatingRow104 w h
  · exact separatingRow105 w h
  · exact separatingRow106 w h
  · exact separatingRow107 w h
  · exact separatingRow108 w h
  · exact separatingRow109 w h
  · exact separatingRow110 w h
  · exact separatingRow111 w h
  · exact separatingRow112 w h
  · exact separatingRow113 w h
  · exact separatingRow114 w h
  · exact separatingRow115 w h
  · exact separatingRow116 w h
  · exact separatingRow117 w h
  · exact separatingRow118 w h
  · exact separatingRow119 w h
  · exact separatingRow120 w h
  · exact separatingRow121 w h
  · exact separatingRow122 w h
  · exact separatingRow123 w h
  · exact separatingRow124 w h
  · exact separatingRow125 w h
  · exact separatingRow126 w h
  · exact separatingRow127 w h
  · exact separatingRow128 w h
  · exact separatingRow129 w h
  · exact separatingRow130 w h
  · exact separatingRow131 w h
  · exact separatingRow132 w h
  · exact separatingRow133 w h
  · exact separatingRow134 w h
  · exact separatingRow135 w h
  · exact separatingRow136 w h
  · exact separatingRow137 w h
  · exact separatingRow138 w h
  · exact separatingRow139 w h
  · exact separatingRow140 w h
  · exact separatingRow141 w h
  · exact separatingRow142 w h
  · exact separatingRow143 w h

end CubicalIndecomposability
