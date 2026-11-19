module

public import FiniteCycleData6
public import FiniteInjectionWitnessChecks

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FiniteCycleCandidates.N6
open MatroidChecked

noncomputable def coverageTable4 : LiteralLookup ℕ := (.node 212 (.node 136 (.node 86 (.node 58 (.node 29 (.node 23 (.node 21 (.leaf 0) (.node 22 (.leaf 20) (.leaf 21))) (.node 27 (.node 24 (.leaf 23) (.leaf 0)) (.node 28 (.leaf 22) (.leaf 24)))) (.node 52 (.node 30 (.leaf 25) (.node 51 (.leaf 0) (.leaf 21))) (.node 54 (.node 53 (.leaf 20) (.leaf 22)) (.node 57 (.leaf 0) (.leaf 23))))) (.node 78 (.node 72 (.node 59 (.leaf 25) (.node 60 (.leaf 24) (.leaf 0))) (.node 74 (.node 73 (.leaf 21) (.leaf 20)) (.node 75 (.leaf 26) (.leaf 0)))) (.node 82 (.node 79 (.leaf 20) (.node 80 (.leaf 21) (.leaf 27))) (.node 84 (.node 83 (.leaf 26) (.leaf 28)) (.node 85 (.leaf 22) (.leaf 23)))))) (.node 115 (.node 105 (.node 90 (.node 88 (.leaf 29) (.node 89 (.leaf 31) (.leaf 30))) (.node 103 (.node 102 (.leaf 0) (.leaf 23)) (.node 104 (.leaf 22) (.leaf 28)))) (.node 110 (.node 108 (.leaf 0) (.node 109 (.leaf 25) (.leaf 24))) (.node 112 (.node 111 (.leaf 30) (.leaf 32)) (.node 114 (.leaf 34) (.leaf 24))))) (.node 125 (.node 119 (.node 116 (.leaf 25) (.node 117 (.leaf 31) (.leaf 33))) (.node 123 (.node 120 (.leaf 32) (.leaf 0)) (.node 124 (.leaf 21) (.leaf 20)))) (.node 130 (.node 126 (.leaf 22) (.node 129 (.leaf 0) (.leaf 20))) (.node 132 (.node 131 (.leaf 21) (.leaf 23)) (.node 135 (.leaf 0) (.leaf 26))))))) (.node 174 (.node 155 (.node 147 (.node 141 (.node 137 (.leaf 27) (.node 138 (.leaf 29) (.leaf 0))) (.node 143 (.node 142 (.leaf 26) (.leaf 27)) (.node 144 (.leaf 29) (.leaf 0)))) (.node 150 (.node 148 (.leaf 28) (.node 149 (.leaf 30) (.leaf 31))) (.node 152 (.node 151 (.leaf 20) (.leaf 21)) (.node 154 (.leaf 27) (.leaf 26))))) (.node 165 (.node 158 (.node 156 (.leaf 28) (.node 157 (.leaf 26) (.leaf 35))) (.node 161 (.node 160 (.leaf 36) (.leaf 35)) (.node 162 (.leaf 37) (.leaf 0)))) (.node 168 (.node 166 (.leaf 35) (.node 167 (.leaf 36) (.leaf 38))) (.node 172 (.node 171 (.leaf 0) (.leaf 35)) (.node 173 (.leaf 36) (.leaf 38)))))) (.node 194 (.node 183 (.node 179 (.node 177 (.leaf 0) (.node 178 (.leaf 37) (.leaf 39))) (.node 181 (.node 180 (.leaf 40) (.leaf 21)) (.node 182 (.leaf 20) (.leaf 26)))) (.node 188 (.node 186 (.leaf 0) (.node 187 (.leaf 27) (.leaf 36))) (.node 192 (.node 189 (.leaf 35) (.leaf 0)) (.node 193 (.leaf 27) (.leaf 36))))) (.node 204 (.node 199 (.node 195 (.leaf 35) (.node 198 (.leaf 0) (.leaf 26))) (.node 202 (.node 200 (.leaf 35) (.leaf 36)) (.node 203 (.leaf 35) (.leaf 37)))) (.node 208 (.node 205 (.leaf 28) (.node 206 (.leaf 37) (.leaf 38))) (.node 210 (.node 209 (.leaf 40) (.leaf 39)) (.node 211 (.leaf 23) (.leaf 22)))))))) (.node 292 (.node 252 (.node 232 (.node 223 (.node 217 (.node 213 (.leaf 28) (.node 216 (.leaf 0) (.leaf 29))) (.node 219 (.node 218 (.leaf 38) (.leaf 37)) (.node 222 (.leaf 0) (.leaf 29)))) (.node 228 (.node 224 (.leaf 38) (.node 225 (.leaf 37) (.leaf 0))) (.node 230 (.node 229 (.leaf 31) (.leaf 40)) (.node 231 (.leaf 39) (.leaf 41))))) (.node 243 (.node 236 (.node 234 (.leaf 43) (.node 235 (.leaf 30) (.leaf 39))) (.node 239 (.node 237 (.leaf 40) (.leaf 42)) (.node 240 (.leaf 41) (.leaf 0)))) (.node 246 (.node 244 (.leaf 23) (.node 245 (.leaf 25) (.leaf 24))) (.node 250 (.node 249 (.leaf 0) (.leaf 22)) (.node 251 (.leaf 24) (.leaf 25)))))) (.node 272 (.node 263 (.node 257 (.node 255 (.leaf 0) (.node 256 (.leaf 28) (.leaf 30))) (.node 261 (.node 258 (.leaf 31) (.leaf 0)) (.node 262 (.leaf 34) (.leaf 32)))) (.node 268 (.node 264 (.leaf 33) (.node 267 (.leaf 0) (.leaf 34))) (.node 270 (.node 269 (.leaf 32) (.leaf 33)) (.node 271 (.leaf 22) (.leaf 23))))) (.node 281 (.node 276 (.node 274 (.leaf 29) (.node 275 (.leaf 31) (.leaf 30))) (.node 278 (.node 277 (.leaf 28) (.leaf 37)) (.node 280 (.leaf 38) (.leaf 40)))) (.node 286 (.node 282 (.leaf 39) (.node 285 (.leaf 0) (.leaf 37))) (.node 288 (.node 287 (.leaf 39) (.leaf 40)) (.node 291 (.leaf 0) (.leaf 43))))))) (.node 326 (.node 309 (.node 301 (.node 297 (.node 293 (.leaf 41) (.node 294 (.leaf 42) (.leaf 0))) (.node 299 (.node 298 (.leaf 43) (.leaf 41)) (.node 300 (.leaf 42) (.leaf 24)))) (.node 305 (.node 302 (.leaf 25) (.node 303 (.leaf 31) (.leaf 33))) (.node 307 (.node 306 (.leaf 32) (.leaf 30)) (.node 308 (.leaf 39) (.leaf 40))))) (.node 318 (.node 313 (.node 311 (.leaf 42) (.node 312 (.leaf 41) (.leaf 32))) (.node 315 (.node 314 (.leaf 41) (.leaf 44)) (.node 317 (.leaf 45) (.leaf 44)))) (.node 322 (.node 319 (.leaf 34) (.node 320 (.leaf 43) (.leaf 46))) (.node 324 (.node 323 (.leaf 44) (.leaf 45)) (.node 325 (.leaf 34) (.leaf 43)))))) (.node 343 (.node 334 (.node 330 (.node 328 (.leaf 46) (.node 329 (.leaf 44) (.leaf 45))) (.node 332 (.node 331 (.leaf 25) (.leaf 24)) (.node 333 (.leaf 30) (.leaf 32)))) (.node 338 (.node 336 (.leaf 34) (.node 337 (.leaf 31) (.leaf 40))) (.node 340 (.node 339 (.leaf 39) (.leaf 41)) (.node 342 (.leaf 43) (.leaf 33))))) (.node 351 (.node 346 (.node 344 (.leaf 42) (.node 345 (.leaf 45) (.leaf 44))) (.node 349 (.node 348 (.leaf 46) (.leaf 33)) (.node 350 (.leaf 42) (.leaf 45)))) (.node 355 (.node 352 (.leaf 44) (.node 354 (.leaf 46) (.leaf 32))) (.node 357 (.node 356 (.leaf 41) (.leaf 44)) (.node 359 (.leaf 45) (.leaf 44)))))))))
noncomputable def permutationTable4 : LiteralLookup ℕ := (.node 116 (.node 60 (.node 30 (.node 24 (.node 22 (.leaf 0) (.node 23 (.leaf 2) (.leaf 3))) (.node 28 (.node 27 (.leaf 0) (.leaf 1)) (.node 29 (.leaf 4) (.leaf 5)))) (.node 54 (.node 52 (.node 51 (.leaf 0) (.leaf 2)) (.node 53 (.leaf 0) (.leaf 1))) (.node 58 (.node 57 (.leaf 0) (.leaf 3)) (.node 59 (.leaf 5) (.leaf 4))))) (.node 102 (.node 80 (.node 73 (.node 72 (.leaf 0) (.leaf 2)) (.node 79 (.leaf 0) (.leaf 2))) (.node 85 (.node 84 (.leaf 0) (.leaf 1)) (.node 86 (.leaf 3) (.leaf 0)))) (.node 109 (.node 104 (.node 103 (.leaf 3) (.leaf 1)) (.node 108 (.leaf 0) (.leaf 5))) (.node 114 (.node 110 (.leaf 4) (.leaf 0)) (.node 115 (.leaf 4) (.leaf 5)))))) (.node 244 (.node 151 (.node 126 (.node 124 (.node 123 (.leaf 0) (.leaf 2)) (.node 125 (.leaf 0) (.leaf 1))) (.node 131 (.node 130 (.leaf 0) (.leaf 2)) (.node 132 (.leaf 3) (.leaf 0)))) (.node 210 (.node 180 (.node 152 (.leaf 2) (.leaf 0)) (.node 181 (.leaf 2) (.leaf 0))) (.node 212 (.node 211 (.leaf 3) (.leaf 1)) (.node 243 (.leaf 0) (.leaf 3))))) (.node 271 (.node 250 (.node 246 (.node 245 (.leaf 5) (.leaf 4)) (.node 249 (.leaf 0) (.leaf 1))) (.node 252 (.node 251 (.leaf 4) (.leaf 5)) (.node 270 (.leaf 0) (.leaf 1)))) (.node 302 (.node 300 (.node 272 (.leaf 3) (.leaf 0)) (.node 301 (.leaf 4) (.leaf 5))) (.node 331 (.node 330 (.leaf 0) (.leaf 5)) (.node 332 (.leaf 4) (.leaf 0)))))))
noncomputable def neighborTable4 : LiteralLookup ℕ := (.node 116 (.node 74 (.node 51 (.node 24 (.node 21 (.leaf 0) (.leaf 20)) (.node 27 (.leaf 0) (.node 30 (.leaf 20) (.leaf 0)))) (.node 57 (.node 54 (.leaf 20) (.leaf 0)) (.node 60 (.leaf 20) (.node 72 (.leaf 0) (.leaf 20))))) (.node 102 (.node 80 (.node 78 (.leaf 0) (.leaf 20)) (.node 84 (.leaf 0) (.node 86 (.leaf 20) (.leaf 0)))) (.node 108 (.node 104 (.leaf 20) (.leaf 0)) (.node 110 (.leaf 20) (.node 114 (.leaf 0) (.leaf 20)))))) (.node 212 (.node 150 (.node 126 (.node 123 (.leaf 0) (.leaf 20)) (.node 129 (.leaf 0) (.node 132 (.leaf 20) (.leaf 0)))) (.node 180 (.node 152 (.leaf 20) (.leaf 0)) (.node 182 (.leaf 20) (.node 210 (.leaf 0) (.leaf 20))))) (.node 270 (.node 246 (.node 243 (.leaf 0) (.leaf 20)) (.node 249 (.leaf 0) (.node 252 (.leaf 20) (.leaf 0)))) (.node 302 (.node 272 (.leaf 20) (.node 300 (.leaf 0) (.leaf 20))) (.node 330 (.leaf 0) (.node 332 (.leaf 20) (.leaf 0)))))))

noncomputable def coverageWitness4 (code : ℕ) : Fin 65 :=
  Fin.ofNat 65 (coverageTable4.get code)
noncomputable def permutationWitness4 (code : ℕ) : Fin 6 :=
  Fin.ofNat 6 (permutationTable4.get code)
noncomputable def neighborWitness4 (code : ℕ) : Fin 65 :=
  Fin.ofNat 65 (neighborTable4.get code)

noncomputable def coveredTest4 (code : ℕ) : Bool :=
  coverageAt cells (triangle 6 (by decide)) (decodeInjection 6 4 (by decide) code)
    (coverageWitness4 code)
noncomputable def neighborTest4 (code : ℕ) : Bool :=
  neighborAt cells neighbors (by decide) permMaps (decodeInjection 6 4 (by decide) code)
    (permutationWitness4 code) (neighborWitness4 code)

theorem covered_4_codes_000000 : CodeInterval coveredTest4 0 64 :=
  codeInterval_of_check coveredTest4 0 64 (by decide +kernel)

theorem covered_4_codes_000064 : CodeInterval coveredTest4 64 128 :=
  codeInterval_of_check coveredTest4 64 64 (by decide +kernel)

theorem covered_4_codes_000128 : CodeInterval coveredTest4 128 192 :=
  codeInterval_of_check coveredTest4 128 64 (by decide +kernel)

theorem covered_4_codes_000192 : CodeInterval coveredTest4 192 256 :=
  codeInterval_of_check coveredTest4 192 64 (by decide +kernel)

theorem covered_4_codes_000256 : CodeInterval coveredTest4 256 320 :=
  codeInterval_of_check coveredTest4 256 64 (by decide +kernel)

theorem covered_4_codes_000320 : CodeInterval coveredTest4 320 360 :=
  codeInterval_of_check coveredTest4 320 40 (by decide +kernel)

theorem covered_4_join_000064_000192 : CodeInterval coveredTest4 64 192 :=
  codeInterval_append coveredTest4 64 128 192 covered_4_codes_000064 covered_4_codes_000128

theorem covered_4_join_000000_000192 : CodeInterval coveredTest4 0 192 :=
  codeInterval_append coveredTest4 0 64 192 covered_4_codes_000000 covered_4_join_000064_000192

theorem covered_4_join_000256_000360 : CodeInterval coveredTest4 256 360 :=
  codeInterval_append coveredTest4 256 320 360 covered_4_codes_000256 covered_4_codes_000320

theorem covered_4_join_000192_000360 : CodeInterval coveredTest4 192 360 :=
  codeInterval_append coveredTest4 192 256 360 covered_4_codes_000192 covered_4_join_000256_000360

theorem covered_4_join_000000_000360 : CodeInterval coveredTest4 0 360 :=
  codeInterval_append coveredTest4 0 192 360 covered_4_join_000000_000192 covered_4_join_000192_000360

theorem covered_4 : ∀ f : Fin 4 → Fin 6, Covered cells (triangle 6 (by decide)) f :=
  covered_of_injection_checks (by decide) cells (triangle 6 (by decide)) coverageWitness4 covered_4_join_000000_000360

theorem neighbor_4_codes_000000 : CodeInterval neighborTest4 0 64 :=
  codeInterval_of_check neighborTest4 0 64 (by decide +kernel)

theorem neighbor_4_codes_000064 : CodeInterval neighborTest4 64 128 :=
  codeInterval_of_check neighborTest4 64 64 (by decide +kernel)

theorem neighbor_4_codes_000128 : CodeInterval neighborTest4 128 192 :=
  codeInterval_of_check neighborTest4 128 64 (by decide +kernel)

theorem neighbor_4_codes_000192 : CodeInterval neighborTest4 192 256 :=
  codeInterval_of_check neighborTest4 192 64 (by decide +kernel)

theorem neighbor_4_codes_000256 : CodeInterval neighborTest4 256 320 :=
  codeInterval_of_check neighborTest4 256 64 (by decide +kernel)

theorem neighbor_4_codes_000320 : CodeInterval neighborTest4 320 360 :=
  codeInterval_of_check neighborTest4 320 40 (by decide +kernel)

theorem neighbor_4_join_000064_000192 : CodeInterval neighborTest4 64 192 :=
  codeInterval_append neighborTest4 64 128 192 neighbor_4_codes_000064 neighbor_4_codes_000128

theorem neighbor_4_join_000000_000192 : CodeInterval neighborTest4 0 192 :=
  codeInterval_append neighborTest4 0 64 192 neighbor_4_codes_000000 neighbor_4_join_000064_000192

theorem neighbor_4_join_000256_000360 : CodeInterval neighborTest4 256 360 :=
  codeInterval_append neighborTest4 256 320 360 neighbor_4_codes_000256 neighbor_4_codes_000320

theorem neighbor_4_join_000192_000360 : CodeInterval neighborTest4 192 360 :=
  codeInterval_append neighborTest4 192 256 360 neighbor_4_codes_000192 neighbor_4_join_000256_000360

theorem neighbor_4_join_000000_000360 : CodeInterval neighborTest4 0 360 :=
  codeInterval_append neighborTest4 0 192 360 neighbor_4_join_000000_000192 neighbor_4_join_000192_000360

theorem neighbor_4 : ∀ f : Fin 4 → Fin 6, NeighborWitness cells neighbors (by decide) permMaps f :=
  neighbor_of_injection_checks (by decide) (by decide) cells neighbors permMaps
    permutationWitness4 neighborWitness4 neighbor_4_join_000000_000360

end Papers.RationalityTen.FiniteCycleCandidates.N6
