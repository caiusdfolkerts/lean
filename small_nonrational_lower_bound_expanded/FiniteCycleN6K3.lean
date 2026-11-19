module

public import FiniteCycleData6
public import FiniteCycleWitnessChecks

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FiniteCycleCandidates.N6
open MatroidChecked

noncomputable def coverageTable3 : LiteralLookup ℕ := (.node 113 (.node 61 (.node 30 (.node 20 (.node 15 (.node 10 (.node 9 (.leaf 0) (.leaf 1)) (.node 11 (.leaf 2) (.node 12 (.leaf 3) (.leaf 0)))) (.node 17 (.node 16 (.leaf 4) (.leaf 5)) (.node 18 (.leaf 6) (.node 19 (.leaf 0) (.leaf 1))))) (.node 25 (.node 22 (.node 21 (.leaf 4) (.leaf 0)) (.node 23 (.leaf 7) (.node 24 (.leaf 8) (.leaf 0)))) (.node 27 (.node 26 (.leaf 2) (.leaf 5)) (.node 28 (.leaf 7) (.node 29 (.leaf 0) (.leaf 9)))))) (.node 51 (.node 35 (.node 32 (.node 31 (.leaf 0) (.leaf 3)) (.node 33 (.leaf 6) (.node 34 (.leaf 8) (.leaf 9)))) (.node 40 (.node 39 (.leaf 0) (.leaf 1)) (.node 41 (.leaf 2) (.node 42 (.leaf 3) (.leaf 0))))) (.node 56 (.node 53 (.node 52 (.leaf 10) (.leaf 11)) (.node 54 (.leaf 12) (.node 55 (.leaf 1) (.leaf 0)))) (.node 58 (.node 57 (.leaf 10) (.leaf 0)) (.node 59 (.leaf 13) (.node 60 (.leaf 14) (.leaf 2))))))) (.node 91 (.node 71 (.node 66 (.node 63 (.node 62 (.leaf 0) (.leaf 11)) (.node 64 (.leaf 13) (.node 65 (.leaf 0) (.leaf 15)))) (.node 68 (.node 67 (.leaf 3) (.leaf 0)) (.node 69 (.leaf 12) (.node 70 (.leaf 14) (.leaf 15))))) (.node 81 (.node 76 (.node 75 (.leaf 0) (.leaf 4)) (.node 77 (.leaf 5) (.node 78 (.leaf 6) (.leaf 0)))) (.node 83 (.node 82 (.leaf 10) (.leaf 11)) (.node 84 (.leaf 12) (.node 90 (.leaf 0) (.leaf 4)))))) (.node 102 (.node 97 (.node 94 (.node 92 (.leaf 10) (.leaf 0)) (.node 95 (.leaf 16) (.node 96 (.leaf 17) (.leaf 5)))) (.node 99 (.node 98 (.leaf 11) (.leaf 0)) (.node 100 (.leaf 16) (.node 101 (.leaf 0) (.leaf 18))))) (.node 107 (.node 104 (.node 103 (.leaf 6) (.leaf 12)) (.node 105 (.leaf 0) (.node 106 (.leaf 17) (.leaf 18)))) (.node 110 (.node 109 (.leaf 0) (.leaf 1)) (.node 111 (.leaf 4) (.node 112 (.leaf 0) (.leaf 7)))))))) (.node 161 (.node 140 (.node 124 (.node 118 (.node 115 (.node 114 (.leaf 8) (.leaf 1)) (.node 116 (.leaf 0) (.node 117 (.leaf 10) (.leaf 0)))) (.node 120 (.node 119 (.leaf 13) (.leaf 14)) (.node 121 (.leaf 4) (.node 122 (.leaf 10) (.leaf 0))))) (.node 134 (.node 126 (.node 125 (.leaf 16) (.leaf 17)) (.node 132 (.leaf 0) (.node 133 (.leaf 7) (.leaf 13)))) (.node 137 (.node 135 (.leaf 16) (.leaf 0)) (.node 138 (.leaf 19) (.node 139 (.leaf 8) (.leaf 14)))))) (.node 151 (.node 146 (.node 142 (.node 141 (.leaf 17) (.leaf 0)) (.node 143 (.leaf 19) (.node 145 (.leaf 0) (.leaf 2)))) (.node 148 (.node 147 (.leaf 5) (.leaf 7)) (.node 149 (.leaf 0) (.node 150 (.leaf 9) (.leaf 2))))) (.node 156 (.node 153 (.node 152 (.leaf 0) (.leaf 11)) (.node 154 (.leaf 13) (.node 155 (.leaf 0) (.leaf 15)))) (.node 158 (.node 157 (.leaf 5) (.leaf 11)) (.node 159 (.leaf 0) (.node 160 (.leaf 16) (.leaf 0))))))) (.node 189 (.node 177 (.node 167 (.node 163 (.node 162 (.leaf 18) (.leaf 7)) (.node 164 (.leaf 13) (.node 165 (.leaf 16) (.leaf 0)))) (.node 174 (.node 168 (.leaf 19) (.leaf 0)) (.node 175 (.leaf 9) (.node 176 (.leaf 15) (.leaf 18))))) (.node 184 (.node 181 (.node 178 (.leaf 19) (.leaf 0)) (.node 182 (.leaf 3) (.node 183 (.leaf 6) (.leaf 8)))) (.node 186 (.node 185 (.leaf 9) (.leaf 0)) (.node 187 (.leaf 3) (.node 188 (.leaf 0) (.leaf 12)))))) (.node 199 (.node 194 (.node 191 (.node 190 (.leaf 14) (.leaf 15)) (.node 192 (.leaf 0) (.node 193 (.leaf 6) (.leaf 12)))) (.node 196 (.node 195 (.leaf 0) (.leaf 17)) (.node 197 (.leaf 18) (.node 198 (.leaf 0) (.leaf 8))))) (.node 204 (.node 201 (.node 200 (.leaf 14) (.leaf 17)) (.node 202 (.leaf 0) (.node 203 (.leaf 19) (.leaf 0)))) (.node 206 (.node 205 (.leaf 9) (.leaf 15)) (.node 207 (.leaf 18) (.node 208 (.leaf 19) (.leaf 0)))))))))
noncomputable def permutationTable3 : LiteralLookup ℕ := (.node 60 (.node 26 (.node 11 (.node 10 (.leaf 0) (.leaf 2)) (.node 12 (.leaf 3) (.node 25 (.leaf 0) (.leaf 2)))) (.node 40 (.node 31 (.leaf 0) (.node 32 (.leaf 3) (.leaf 0))) (.node 41 (.leaf 2) (.node 42 (.leaf 3) (.leaf 0))))) (.node 150 (.node 67 (.node 61 (.leaf 2) (.node 66 (.leaf 0) (.leaf 3))) (.node 145 (.leaf 0) (.node 146 (.leaf 2) (.leaf 0)))) (.node 182 (.node 151 (.leaf 2) (.node 181 (.leaf 0) (.leaf 3))) (.node 186 (.leaf 0) (.node 187 (.leaf 3) (.leaf 0))))))
noncomputable def neighborTable3 : LiteralLookup ℕ := (.node 61 (.node 31 (.node 19 (.node 9 (.leaf 0) (.node 12 (.leaf 1) (.leaf 0))) (.node 25 (.node 20 (.leaf 1) (.leaf 0)) (.node 26 (.leaf 1) (.leaf 0)))) (.node 42 (.node 32 (.leaf 1) (.node 39 (.leaf 0) (.leaf 1))) (.node 55 (.node 54 (.leaf 0) (.leaf 1)) (.node 60 (.leaf 0) (.leaf 1))))) (.node 145 (.node 109 (.node 66 (.leaf 0) (.node 67 (.leaf 1) (.leaf 0))) (.node 114 (.node 110 (.leaf 1) (.leaf 0)) (.node 115 (.leaf 1) (.leaf 0)))) (.node 181 (.node 150 (.node 146 (.leaf 1) (.leaf 0)) (.node 151 (.leaf 1) (.leaf 0))) (.node 186 (.node 182 (.leaf 1) (.leaf 0)) (.node 187 (.leaf 1) (.leaf 0))))))

noncomputable def coverageWitness3 (code : ℕ) : Fin 65 :=
  Fin.ofNat 65 (coverageTable3.get code)
noncomputable def permutationWitness3 (code : ℕ) : Fin 6 :=
  Fin.ofNat 6 (permutationTable3.get code)
noncomputable def neighborWitness3 (code : ℕ) : Fin 65 :=
  Fin.ofNat 65 (neighborTable3.get code)

noncomputable def coveredTest3 (code : ℕ) : Bool :=
  coverageAt cells (triangle 6 (by decide)) (decodeFunction 6 (by decide) 3 code)
    (coverageWitness3 code)
noncomputable def neighborTest3 (code : ℕ) : Bool :=
  neighborAt cells neighbors (by decide) permMaps (decodeFunction 6 (by decide) 3 code)
    (permutationWitness3 code) (neighborWitness3 code)

theorem covered_3_codes_000000 : CodeInterval coveredTest3 0 128 :=
  codeInterval_of_check coveredTest3 0 128 (by decide +kernel)

theorem covered_3_codes_000128 : CodeInterval coveredTest3 128 216 :=
  codeInterval_of_check coveredTest3 128 88 (by decide +kernel)

theorem covered_3_join_000000_000216 : CodeInterval coveredTest3 0 216 :=
  codeInterval_append coveredTest3 0 128 216 covered_3_codes_000000 covered_3_codes_000128

theorem covered_3 : ∀ f : Fin 3 → Fin 6, Covered cells (triangle 6 (by decide)) f :=
  covered_of_code_checks (by decide) cells (triangle 6 (by decide)) coverageWitness3 covered_3_join_000000_000216

theorem neighbor_3_codes_000000 : CodeInterval neighborTest3 0 128 :=
  codeInterval_of_check neighborTest3 0 128 (by decide +kernel)

theorem neighbor_3_codes_000128 : CodeInterval neighborTest3 128 216 :=
  codeInterval_of_check neighborTest3 128 88 (by decide +kernel)

theorem neighbor_3_join_000000_000216 : CodeInterval neighborTest3 0 216 :=
  codeInterval_append neighborTest3 0 128 216 neighbor_3_codes_000000 neighbor_3_codes_000128

theorem neighbor_3 : ∀ f : Fin 3 → Fin 6, NeighborWitness cells neighbors (by decide) permMaps f :=
  neighbor_of_code_checks (by decide) (by decide) cells neighbors permMaps
    permutationWitness3 neighborWitness3 neighbor_3_join_000000_000216

end Papers.RationalityTen.FiniteCycleCandidates.N6
