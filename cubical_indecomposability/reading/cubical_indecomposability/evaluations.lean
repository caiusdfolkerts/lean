import cubical_indecomposability.certificates.support00
import cubical_indecomposability.certificates.support01
import cubical_indecomposability.certificates.support02
import cubical_indecomposability.certificates.support03
import cubical_indecomposability.certificates.support04
import cubical_indecomposability.certificates.support05
import cubical_indecomposability.certificates.support06
import cubical_indecomposability.certificates.support07
import cubical_indecomposability.certificates.support08
import cubical_indecomposability.certificates.support09
import cubical_indecomposability.certificates.support10
import cubical_indecomposability.certificates.support11
import cubical_indecomposability.certificates.support12
import cubical_indecomposability.data
import Mathlib.Tactic.FinCases

/-! Exact integer arithmetic and finite incidences, checked by Lean's kernel.
`decide +kernel` below proves closed propositions by reduction.  It invokes no native
oracle and introduces no mathematical assumptions.  Row lemmas keep the
kernel reduction and subsequent rebuilds small.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability

theorem homogeneous_last_pos : ∀ v : Fin 144, 0 < q v 4 := by decide +kernel

theorem supportData (f : Fin 130) (v : Fin 144) :
    0 ≤ slackNumerator f v ∧ (slackNumerator f v = 0 ↔ incident f v) := by
  fin_cases f
  · exact supportRow000 v
  · exact supportRow001 v
  · exact supportRow002 v
  · exact supportRow003 v
  · exact supportRow004 v
  · exact supportRow005 v
  · exact supportRow006 v
  · exact supportRow007 v
  · exact supportRow008 v
  · exact supportRow009 v
  · exact supportRow010 v
  · exact supportRow011 v
  · exact supportRow012 v
  · exact supportRow013 v
  · exact supportRow014 v
  · exact supportRow015 v
  · exact supportRow016 v
  · exact supportRow017 v
  · exact supportRow018 v
  · exact supportRow019 v
  · exact supportRow020 v
  · exact supportRow021 v
  · exact supportRow022 v
  · exact supportRow023 v
  · exact supportRow024 v
  · exact supportRow025 v
  · exact supportRow026 v
  · exact supportRow027 v
  · exact supportRow028 v
  · exact supportRow029 v
  · exact supportRow030 v
  · exact supportRow031 v
  · exact supportRow032 v
  · exact supportRow033 v
  · exact supportRow034 v
  · exact supportRow035 v
  · exact supportRow036 v
  · exact supportRow037 v
  · exact supportRow038 v
  · exact supportRow039 v
  · exact supportRow040 v
  · exact supportRow041 v
  · exact supportRow042 v
  · exact supportRow043 v
  · exact supportRow044 v
  · exact supportRow045 v
  · exact supportRow046 v
  · exact supportRow047 v
  · exact supportRow048 v
  · exact supportRow049 v
  · exact supportRow050 v
  · exact supportRow051 v
  · exact supportRow052 v
  · exact supportRow053 v
  · exact supportRow054 v
  · exact supportRow055 v
  · exact supportRow056 v
  · exact supportRow057 v
  · exact supportRow058 v
  · exact supportRow059 v
  · exact supportRow060 v
  · exact supportRow061 v
  · exact supportRow062 v
  · exact supportRow063 v
  · exact supportRow064 v
  · exact supportRow065 v
  · exact supportRow066 v
  · exact supportRow067 v
  · exact supportRow068 v
  · exact supportRow069 v
  · exact supportRow070 v
  · exact supportRow071 v
  · exact supportRow072 v
  · exact supportRow073 v
  · exact supportRow074 v
  · exact supportRow075 v
  · exact supportRow076 v
  · exact supportRow077 v
  · exact supportRow078 v
  · exact supportRow079 v
  · exact supportRow080 v
  · exact supportRow081 v
  · exact supportRow082 v
  · exact supportRow083 v
  · exact supportRow084 v
  · exact supportRow085 v
  · exact supportRow086 v
  · exact supportRow087 v
  · exact supportRow088 v
  · exact supportRow089 v
  · exact supportRow090 v
  · exact supportRow091 v
  · exact supportRow092 v
  · exact supportRow093 v
  · exact supportRow094 v
  · exact supportRow095 v
  · exact supportRow096 v
  · exact supportRow097 v
  · exact supportRow098 v
  · exact supportRow099 v
  · exact supportRow100 v
  · exact supportRow101 v
  · exact supportRow102 v
  · exact supportRow103 v
  · exact supportRow104 v
  · exact supportRow105 v
  · exact supportRow106 v
  · exact supportRow107 v
  · exact supportRow108 v
  · exact supportRow109 v
  · exact supportRow110 v
  · exact supportRow111 v
  · exact supportRow112 v
  · exact supportRow113 v
  · exact supportRow114 v
  · exact supportRow115 v
  · exact supportRow116 v
  · exact supportRow117 v
  · exact supportRow118 v
  · exact supportRow119 v
  · exact supportRow120 v
  · exact supportRow121 v
  · exact supportRow122 v
  · exact supportRow123 v
  · exact supportRow124 v
  · exact supportRow125 v
  · exact supportRow126 v
  · exact supportRow127 v
  · exact supportRow128 v
  · exact supportRow129 v

end CubicalIndecomposability
