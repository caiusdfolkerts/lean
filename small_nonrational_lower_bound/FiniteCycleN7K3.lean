module

public import FiniteCycleData7
public import FiniteInjectionWitnessChecks

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FiniteCycleCandidates.N7
open MatroidChecked

noncomputable def coverageTable3 : LiteralLookup ℕ := (.node 105 (.node 53 (.node 26 (.node 13 (.node 6 (.node 4 (.node 3 (.leaf 0) (.leaf 1)) (.node 5 (.leaf 2) (.leaf 3))) (.node 10 (.node 7 (.leaf 4) (.leaf 0)) (.node 11 (.leaf 1) (.node 12 (.leaf 2) (.leaf 3))))) (.node 19 (.node 16 (.node 14 (.leaf 4) (.leaf 1)) (.node 18 (.leaf 5) (.leaf 6))) (.node 21 (.node 20 (.leaf 7) (.leaf 8)) (.node 23 (.leaf 2) (.node 24 (.leaf 6) (.leaf 9)))))) (.node 38 (.node 31 (.node 28 (.node 27 (.leaf 10) (.leaf 11)) (.node 30 (.leaf 3) (.leaf 7))) (.node 34 (.node 32 (.leaf 10) (.leaf 12)) (.node 35 (.leaf 13) (.node 37 (.leaf 4) (.leaf 8))))) (.node 46 (.node 40 (.node 39 (.leaf 11) (.leaf 13)) (.node 42 (.leaf 14) (.node 44 (.leaf 1) (.leaf 5)))) (.node 48 (.node 47 (.leaf 6) (.leaf 7)) (.node 49 (.leaf 8) (.node 50 (.leaf 5) (.leaf 15))))))) (.node 78 (.node 64 (.node 57 (.node 55 (.node 54 (.leaf 16) (.leaf 17)) (.node 56 (.leaf 18) (.leaf 5))) (.node 61 (.node 60 (.leaf 15) (.leaf 16)) (.node 62 (.leaf 17) (.node 63 (.leaf 18) (.leaf 6))))) (.node 71 (.node 68 (.node 66 (.leaf 16) (.leaf 19)) (.node 69 (.leaf 20) (.node 70 (.leaf 21) (.leaf 7)))) (.node 74 (.node 73 (.leaf 17) (.leaf 20)) (.node 76 (.leaf 22) (.node 77 (.leaf 23) (.leaf 8)))))) (.node 91 (.node 84 (.node 81 (.node 80 (.leaf 18) (.leaf 21)) (.node 82 (.leaf 23) (.leaf 24))) (.node 87 (.node 86 (.leaf 2) (.leaf 6)) (.node 89 (.leaf 9) (.node 90 (.leaf 10) (.leaf 11))))) (.node 98 (.node 94 (.node 92 (.leaf 6) (.leaf 16)) (.node 96 (.leaf 19) (.node 97 (.leaf 20) (.leaf 21)))) (.node 100 (.node 99 (.leaf 9) (.leaf 19)) (.node 103 (.leaf 25) (.node 104 (.leaf 26) (.leaf 27)))))))) (.node 156 (.node 130 (.node 118 (.node 111 (.node 107 (.node 106 (.leaf 9) (.leaf 19)) (.node 110 (.leaf 25) (.leaf 26))) (.node 113 (.node 112 (.leaf 27) (.leaf 10)) (.node 114 (.leaf 20) (.node 116 (.leaf 26) (.leaf 28))))) (.node 123 (.node 120 (.node 119 (.leaf 29) (.leaf 11)) (.node 121 (.leaf 21) (.leaf 27))) (.node 126 (.node 124 (.leaf 29) (.leaf 30)) (.node 128 (.leaf 3) (.node 129 (.leaf 7) (.leaf 10)))))) (.node 142 (.node 136 (.node 133 (.node 132 (.leaf 12) (.leaf 13)) (.node 134 (.leaf 7) (.leaf 17))) (.node 139 (.node 137 (.leaf 20) (.leaf 22)) (.node 140 (.leaf 23) (.node 141 (.leaf 10) (.leaf 20))))) (.node 149 (.node 146 (.node 144 (.leaf 26) (.leaf 28)) (.node 147 (.leaf 29) (.node 148 (.leaf 12) (.leaf 22)))) (.node 153 (.node 150 (.leaf 28) (.leaf 31)) (.node 154 (.leaf 32) (.node 155 (.leaf 12) (.leaf 22))))))) (.node 183 (.node 170 (.node 162 (.node 160 (.node 157 (.leaf 28) (.leaf 31)) (.node 161 (.leaf 32) (.leaf 13))) (.node 164 (.node 163 (.leaf 23) (.leaf 29)) (.node 166 (.leaf 32) (.node 168 (.leaf 33) (.leaf 4))))) (.node 176 (.node 172 (.node 171 (.leaf 8) (.leaf 11)) (.node 173 (.leaf 13) (.node 175 (.leaf 14) (.leaf 8)))) (.node 179 (.node 178 (.leaf 18) (.leaf 21)) (.node 180 (.leaf 23) (.node 182 (.leaf 24) (.leaf 11)))))) (.node 196 (.node 189 (.node 186 (.node 184 (.leaf 21) (.leaf 27)) (.node 187 (.leaf 29) (.leaf 30))) (.node 191 (.node 190 (.leaf 13) (.leaf 23)) (.node 192 (.leaf 29) (.node 194 (.leaf 32) (.leaf 33))))) (.node 203 (.node 198 (.node 197 (.leaf 14) (.leaf 24)) (.node 199 (.leaf 30) (.node 200 (.leaf 33) (.leaf 34)))) (.node 205 (.node 204 (.leaf 14) (.leaf 24)) (.node 206 (.leaf 30) (.node 207 (.leaf 33) (.leaf 34)))))))))
noncomputable def permutationTable3 : LiteralLookup ℕ := (.node 23 (.node 11 (.node 5 (.node 4 (.leaf 0) (.leaf 6)) (.node 6 (.leaf 8) (.node 7 (.leaf 9) (.leaf 0)))) (.node 13 (.node 12 (.leaf 6) (.leaf 8)) (.node 14 (.leaf 9) (.node 21 (.leaf 0) (.leaf 6))))) (.node 84 (.node 30 (.node 28 (.leaf 0) (.leaf 8)) (.node 35 (.leaf 0) (.node 37 (.leaf 9) (.leaf 0)))) (.node 128 (.node 86 (.leaf 6) (.node 126 (.leaf 0) (.leaf 8))) (.node 168 (.leaf 0) (.node 170 (.leaf 9) (.leaf 0))))))
noncomputable def neighborTable3 : LiteralLookup ℕ := (.node 35 (.node 16 (.node 7 (.node 3 (.leaf 0) (.leaf 1)) (.node 10 (.leaf 0) (.leaf 1))) (.node 23 (.node 21 (.leaf 0) (.leaf 1)) (.node 28 (.leaf 0) (.node 30 (.leaf 1) (.leaf 0))))) (.node 86 (.node 42 (.node 37 (.leaf 1) (.leaf 0)) (.node 44 (.leaf 1) (.node 84 (.leaf 0) (.leaf 1)))) (.node 128 (.node 126 (.leaf 0) (.leaf 1)) (.node 168 (.leaf 0) (.node 170 (.leaf 1) (.leaf 0))))))

noncomputable def coverageWitness3 (code : ℕ) : Fin 290 :=
  Fin.ofNat 290 (coverageTable3.get code)
noncomputable def permutationWitness3 (code : ℕ) : Fin 24 :=
  Fin.ofNat 24 (permutationTable3.get code)
noncomputable def neighborWitness3 (code : ℕ) : Fin 290 :=
  Fin.ofNat 290 (neighborTable3.get code)

noncomputable def coveredTest3 (code : ℕ) : Bool :=
  coverageAt cells (triangle 7 (by decide)) (decodeInjection 7 3 (by decide) code)
    (coverageWitness3 code)
noncomputable def neighborTest3 (code : ℕ) : Bool :=
  neighborAt cells neighbors (by decide) permMaps (decodeInjection 7 3 (by decide) code)
    (permutationWitness3 code) (neighborWitness3 code)

theorem covered_3_codes_000000 : CodeInterval coveredTest3 0 64 :=
  codeInterval_of_check coveredTest3 0 64 (by decide +kernel)

theorem covered_3_codes_000064 : CodeInterval coveredTest3 64 128 :=
  codeInterval_of_check coveredTest3 64 64 (by decide +kernel)

theorem covered_3_codes_000128 : CodeInterval coveredTest3 128 192 :=
  codeInterval_of_check coveredTest3 128 64 (by decide +kernel)

theorem covered_3_codes_000192 : CodeInterval coveredTest3 192 210 :=
  codeInterval_of_check coveredTest3 192 18 (by decide +kernel)

theorem covered_3_join_000000_000128 : CodeInterval coveredTest3 0 128 :=
  codeInterval_append coveredTest3 0 64 128 covered_3_codes_000000 covered_3_codes_000064

theorem covered_3_join_000128_000210 : CodeInterval coveredTest3 128 210 :=
  codeInterval_append coveredTest3 128 192 210 covered_3_codes_000128 covered_3_codes_000192

theorem covered_3_join_000000_000210 : CodeInterval coveredTest3 0 210 :=
  codeInterval_append coveredTest3 0 128 210 covered_3_join_000000_000128 covered_3_join_000128_000210

theorem covered_3 : ∀ f : Fin 3 → Fin 7, Covered cells (triangle 7 (by decide)) f :=
  covered_of_injection_checks (by decide) cells (triangle 7 (by decide)) coverageWitness3 covered_3_join_000000_000210

theorem neighbor_3_codes_000000 : CodeInterval neighborTest3 0 64 :=
  codeInterval_of_check neighborTest3 0 64 (by decide +kernel)

theorem neighbor_3_codes_000064 : CodeInterval neighborTest3 64 128 :=
  codeInterval_of_check neighborTest3 64 64 (by decide +kernel)

theorem neighbor_3_codes_000128 : CodeInterval neighborTest3 128 192 :=
  codeInterval_of_check neighborTest3 128 64 (by decide +kernel)

theorem neighbor_3_codes_000192 : CodeInterval neighborTest3 192 210 :=
  codeInterval_of_check neighborTest3 192 18 (by decide +kernel)

theorem neighbor_3_join_000000_000128 : CodeInterval neighborTest3 0 128 :=
  codeInterval_append neighborTest3 0 64 128 neighbor_3_codes_000000 neighbor_3_codes_000064

theorem neighbor_3_join_000128_000210 : CodeInterval neighborTest3 128 210 :=
  codeInterval_append neighborTest3 128 192 210 neighbor_3_codes_000128 neighbor_3_codes_000192

theorem neighbor_3_join_000000_000210 : CodeInterval neighborTest3 0 210 :=
  codeInterval_append neighborTest3 0 128 210 neighbor_3_join_000000_000128 neighbor_3_join_000128_000210

theorem neighbor_3 : ∀ f : Fin 3 → Fin 7, NeighborWitness cells neighbors (by decide) permMaps f :=
  neighbor_of_injection_checks (by decide) (by decide) cells neighbors permMaps
    permutationWitness3 neighborWitness3 neighbor_3_join_000000_000210

end Papers.RationalityTen.FiniteCycleCandidates.N7
