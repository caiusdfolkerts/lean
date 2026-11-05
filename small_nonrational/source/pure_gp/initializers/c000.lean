module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C000

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C000
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 2
def globalNegation : Bool := Bool.true
def edgeTable : Table SupportEdge := (Table.node 137 (Table.node 68 (Table.node 34 (Table.node 17 (Table.node 8 (Table.node 4 (Table.node 2 (Table.node 1 (Table.leaf (SupportEdge.mk 2 3 Bool.false)) (Table.leaf (SupportEdge.mk 2 4 Bool.false))) (Table.node 3 (Table.leaf (SupportEdge.mk 2 5 Bool.false)) (Table.leaf (SupportEdge.mk 7 8 Bool.false)))) (Table.node 6 (Table.node 5 (Table.leaf (SupportEdge.mk 7 9 Bool.false)) (Table.leaf (SupportEdge.mk 7 10 Bool.false))) (Table.node 7 (Table.leaf (SupportEdge.mk 11 12 Bool.false)) (Table.leaf (SupportEdge.mk 11 13 Bool.false))))) (Table.node 12 (Table.node 10 (Table.node 9 (Table.leaf (SupportEdge.mk 11 14 Bool.false)) (Table.leaf (SupportEdge.mk 22 23 Bool.false))) (Table.node 11 (Table.leaf (SupportEdge.mk 22 24 Bool.false)) (Table.leaf (SupportEdge.mk 22 25 Bool.false)))) (Table.node 14 (Table.node 13 (Table.leaf (SupportEdge.mk 26 27 Bool.false)) (Table.leaf (SupportEdge.mk 26 28 Bool.false))) (Table.node 15 (Table.leaf (SupportEdge.mk 26 29 Bool.false)) (Table.node 16 (Table.leaf (SupportEdge.mk 36 37 Bool.false)) (Table.leaf (SupportEdge.mk 36 38 Bool.false))))))) (Table.node 25 (Table.node 21 (Table.node 19 (Table.node 18 (Table.leaf (SupportEdge.mk 36 39 Bool.false)) (Table.leaf (SupportEdge.mk 57 58 Bool.false))) (Table.node 20 (Table.leaf (SupportEdge.mk 57 59 Bool.false)) (Table.leaf (SupportEdge.mk 57 60 Bool.false)))) (Table.node 23 (Table.node 22 (Table.leaf (SupportEdge.mk 61 62 Bool.false)) (Table.leaf (SupportEdge.mk 61 63 Bool.false))) (Table.node 24 (Table.leaf (SupportEdge.mk 61 64 Bool.false)) (Table.leaf (SupportEdge.mk 71 72 Bool.false))))) (Table.node 29 (Table.node 27 (Table.node 26 (Table.leaf (SupportEdge.mk 71 73 Bool.false)) (Table.leaf (SupportEdge.mk 71 74 Bool.false))) (Table.node 28 (Table.leaf (SupportEdge.mk 91 92 Bool.false)) (Table.leaf (SupportEdge.mk 91 93 Bool.false)))) (Table.node 31 (Table.node 30 (Table.leaf (SupportEdge.mk 91 94 Bool.false)) (Table.leaf (SupportEdge.mk 127 128 Bool.false))) (Table.node 32 (Table.leaf (SupportEdge.mk 127 129 Bool.false)) (Table.node 33 (Table.leaf (SupportEdge.mk 127 130 Bool.false)) (Table.leaf (SupportEdge.mk 131 132 Bool.false)))))))) (Table.node 51 (Table.node 42 (Table.node 38 (Table.node 36 (Table.node 35 (Table.leaf (SupportEdge.mk 131 133 Bool.false)) (Table.leaf (SupportEdge.mk 131 134 Bool.false))) (Table.node 37 (Table.leaf (SupportEdge.mk 141 142 Bool.false)) (Table.leaf (SupportEdge.mk 141 143 Bool.false)))) (Table.node 40 (Table.node 39 (Table.leaf (SupportEdge.mk 141 144 Bool.false)) (Table.leaf (SupportEdge.mk 161 162 Bool.false))) (Table.node 41 (Table.leaf (SupportEdge.mk 161 163 Bool.false)) (Table.leaf (SupportEdge.mk 161 164 Bool.false))))) (Table.node 46 (Table.node 44 (Table.node 43 (Table.leaf (SupportEdge.mk 196 197 Bool.false)) (Table.leaf (SupportEdge.mk 196 198 Bool.false))) (Table.node 45 (Table.leaf (SupportEdge.mk 196 199 Bool.false)) (Table.leaf (SupportEdge.mk 2 7 Bool.false)))) (Table.node 48 (Table.node 47 (Table.leaf (SupportEdge.mk 2 11 Bool.false)) (Table.leaf (SupportEdge.mk 2 15 Bool.true))) (Table.node 49 (Table.leaf (SupportEdge.mk 2 16 Bool.true)) (Table.node 50 (Table.leaf (SupportEdge.mk 5 10 Bool.false)) (Table.leaf (SupportEdge.mk 5 14 Bool.false))))))) (Table.node 59 (Table.node 55 (Table.node 53 (Table.node 52 (Table.leaf (SupportEdge.mk 5 19 Bool.false)) (Table.leaf (SupportEdge.mk 5 20 Bool.false))) (Table.node 54 (Table.leaf (SupportEdge.mk 32 42 Bool.false)) (Table.leaf (SupportEdge.mk 32 48 Bool.false)))) (Table.node 57 (Table.node 56 (Table.leaf (SupportEdge.mk 32 53 Bool.true)) (Table.leaf (SupportEdge.mk 32 54 Bool.true))) (Table.node 58 (Table.leaf (SupportEdge.mk 67 77 Bool.false)) (Table.leaf (SupportEdge.mk 67 83 Bool.false))))) (Table.node 63 (Table.node 61 (Table.node 60 (Table.leaf (SupportEdge.mk 67 88 Bool.true)) (Table.leaf (SupportEdge.mk 67 89 Bool.true))) (Table.node 62 (Table.leaf (SupportEdge.mk 137 147 Bool.false)) (Table.leaf (SupportEdge.mk 137 153 Bool.false)))) (Table.node 65 (Table.node 64 (Table.leaf (SupportEdge.mk 137 158 Bool.true)) (Table.leaf (SupportEdge.mk 137 159 Bool.true))) (Table.node 66 (Table.leaf (SupportEdge.mk 2 22 Bool.true)) (Table.node 67 (Table.leaf (SupportEdge.mk 2 26 Bool.true)) (Table.leaf (SupportEdge.mk 2 31 Bool.false))))))))) (Table.node 102 (Table.node 85 (Table.node 76 (Table.node 72 (Table.node 70 (Table.node 69 (Table.leaf (SupportEdge.mk 2 32 Bool.false)) (Table.leaf (SupportEdge.mk 3 23 Bool.true))) (Table.node 71 (Table.leaf (SupportEdge.mk 3 27 Bool.true)) (Table.leaf (SupportEdge.mk 3 33 Bool.false)))) (Table.node 74 (Table.node 73 (Table.leaf (SupportEdge.mk 3 34 Bool.false)) (Table.leaf (SupportEdge.mk 15 40 Bool.false))) (Table.node 75 (Table.leaf (SupportEdge.mk 15 46 Bool.false)) (Table.leaf (SupportEdge.mk 15 52 Bool.false))))) (Table.node 80 (Table.node 78 (Table.node 77 (Table.leaf (SupportEdge.mk 15 53 Bool.false)) (Table.leaf (SupportEdge.mk 65 95 Bool.true))) (Table.node 79 (Table.leaf (SupportEdge.mk 65 101 Bool.true)) (Table.leaf (SupportEdge.mk 65 107 Bool.true)))) (Table.node 82 (Table.node 81 (Table.leaf (SupportEdge.mk 65 108 Bool.true)) (Table.leaf (SupportEdge.mk 135 165 Bool.true))) (Table.node 83 (Table.leaf (SupportEdge.mk 135 171 Bool.true)) (Table.node 84 (Table.leaf (SupportEdge.mk 135 177 Bool.true)) (Table.leaf (SupportEdge.mk 135 178 Bool.true))))))) (Table.node 93 (Table.node 89 (Table.node 87 (Table.node 86 (Table.leaf (SupportEdge.mk 3 58 Bool.false)) (Table.leaf (SupportEdge.mk 3 62 Bool.false))) (Table.node 88 (Table.leaf (SupportEdge.mk 3 65 Bool.false)) (Table.leaf (SupportEdge.mk 3 68 Bool.true)))) (Table.node 91 (Table.node 90 (Table.leaf (SupportEdge.mk 5 60 Bool.false)) (Table.leaf (SupportEdge.mk 5 64 Bool.false))) (Table.node 92 (Table.leaf (SupportEdge.mk 5 67 Bool.false)) (Table.leaf (SupportEdge.mk 5 70 Bool.false))))) (Table.node 97 (Table.node 95 (Table.node 94 (Table.leaf (SupportEdge.mk 19 79 Bool.true)) (Table.leaf (SupportEdge.mk 19 85 Bool.true))) (Table.node 96 (Table.leaf (SupportEdge.mk 19 88 Bool.true)) (Table.leaf (SupportEdge.mk 19 90 Bool.false)))) (Table.node 99 (Table.node 98 (Table.leaf (SupportEdge.mk 34 99 Bool.true)) (Table.leaf (SupportEdge.mk 34 105 Bool.true))) (Table.node 100 (Table.leaf (SupportEdge.mk 34 108 Bool.true)) (Table.node 101 (Table.leaf (SupportEdge.mk 34 110 Bool.false)) (Table.leaf (SupportEdge.mk 139 204 Bool.false)))))))) (Table.node 119 (Table.node 110 (Table.node 106 (Table.node 104 (Table.node 103 (Table.leaf (SupportEdge.mk 139 210 Bool.false)) (Table.leaf (SupportEdge.mk 139 213 Bool.false))) (Table.node 105 (Table.leaf (SupportEdge.mk 139 215 Bool.true)) (Table.leaf (SupportEdge.mk 52 87 Bool.false)))) (Table.node 108 (Table.node 107 (Table.leaf (SupportEdge.mk 52 107 Bool.false)) (Table.leaf (SupportEdge.mk 52 117 Bool.false))) (Table.node 109 (Table.leaf (SupportEdge.mk 52 121 Bool.false)) (Table.leaf (SupportEdge.mk 53 88 Bool.false))))) (Table.node 114 (Table.node 112 (Table.node 111 (Table.leaf (SupportEdge.mk 53 108 Bool.false)) (Table.leaf (SupportEdge.mk 53 118 Bool.false))) (Table.node 113 (Table.leaf (SupportEdge.mk 53 122 Bool.false)) (Table.leaf (SupportEdge.mk 54 89 Bool.false)))) (Table.node 116 (Table.node 115 (Table.leaf (SupportEdge.mk 54 109 Bool.false)) (Table.leaf (SupportEdge.mk 54 119 Bool.false))) (Table.node 117 (Table.leaf (SupportEdge.mk 54 123 Bool.false)) (Table.node 118 (Table.leaf (SupportEdge.mk 55 90 Bool.false)) (Table.leaf (SupportEdge.mk 55 110 Bool.false))))))) (Table.node 128 (Table.node 123 (Table.node 121 (Table.node 120 (Table.leaf (SupportEdge.mk 55 120 Bool.false)) (Table.leaf (SupportEdge.mk 55 124 Bool.false))) (Table.node 122 (Table.leaf (SupportEdge.mk 195 230 Bool.false)) (Table.leaf (SupportEdge.mk 195 245 Bool.false)))) (Table.node 125 (Table.node 124 (Table.leaf (SupportEdge.mk 195 250 Bool.false)) (Table.leaf (SupportEdge.mk 195 251 Bool.false))) (Table.node 126 (Table.leaf (SupportEdge.mk 9 129 Bool.false)) (Table.node 127 (Table.leaf (SupportEdge.mk 9 143 Bool.true)) (Table.leaf (SupportEdge.mk 9 146 Bool.true)))))) (Table.node 132 (Table.node 130 (Table.node 129 (Table.leaf (SupportEdge.mk 9 148 Bool.true)) (Table.leaf (SupportEdge.mk 10 130 Bool.false))) (Table.node 131 (Table.leaf (SupportEdge.mk 10 144 Bool.true)) (Table.leaf (SupportEdge.mk 10 147 Bool.true)))) (Table.node 134 (Table.node 133 (Table.leaf (SupportEdge.mk 10 149 Bool.true)) (Table.leaf (SupportEdge.mk 20 140 Bool.false))) (Table.node 135 (Table.leaf (SupportEdge.mk 20 156 Bool.false)) (Table.node 136 (Table.leaf (SupportEdge.mk 20 159 Bool.false)) (Table.leaf (SupportEdge.mk 20 160 Bool.false)))))))))) (Table.node 206 (Table.node 171 (Table.node 154 (Table.node 145 (Table.node 141 (Table.node 139 (Table.node 138 (Table.leaf (SupportEdge.mk 45 170 Bool.true)) (Table.leaf (SupportEdge.mk 45 186 Bool.false))) (Table.node 140 (Table.leaf (SupportEdge.mk 45 189 Bool.false)) (Table.leaf (SupportEdge.mk 45 190 Bool.false)))) (Table.node 143 (Table.node 142 (Table.leaf (SupportEdge.mk 80 205 Bool.true)) (Table.leaf (SupportEdge.mk 80 221 Bool.false))) (Table.node 144 (Table.leaf (SupportEdge.mk 80 224 Bool.false)) (Table.leaf (SupportEdge.mk 80 225 Bool.false))))) (Table.node 149 (Table.node 147 (Table.node 146 (Table.leaf (SupportEdge.mk 21 126 Bool.true)) (Table.leaf (SupportEdge.mk 21 163 Bool.false))) (Table.node 148 (Table.leaf (SupportEdge.mk 21 164 Bool.false)) (Table.leaf (SupportEdge.mk 22 127 Bool.true)))) (Table.node 151 (Table.node 150 (Table.leaf (SupportEdge.mk 22 166 Bool.false)) (Table.leaf (SupportEdge.mk 22 167 Bool.false))) (Table.node 152 (Table.leaf (SupportEdge.mk 23 128 Bool.true)) (Table.node 153 (Table.leaf (SupportEdge.mk 23 168 Bool.false)) (Table.leaf (SupportEdge.mk 23 169 Bool.false))))))) (Table.node 162 (Table.node 158 (Table.node 156 (Table.node 155 (Table.leaf (SupportEdge.mk 26 131 Bool.true)) (Table.leaf (SupportEdge.mk 26 172 Bool.false))) (Table.node 157 (Table.leaf (SupportEdge.mk 26 173 Bool.false)) (Table.leaf (SupportEdge.mk 27 132 Bool.true)))) (Table.node 160 (Table.node 159 (Table.leaf (SupportEdge.mk 27 174 Bool.false)) (Table.leaf (SupportEdge.mk 27 175 Bool.false))) (Table.node 161 (Table.leaf (SupportEdge.mk 30 135 Bool.true)) (Table.leaf (SupportEdge.mk 30 177 Bool.false))))) (Table.node 166 (Table.node 164 (Table.node 163 (Table.leaf (SupportEdge.mk 30 178 Bool.false)) (Table.leaf (SupportEdge.mk 36 141 Bool.true))) (Table.node 165 (Table.leaf (SupportEdge.mk 36 182 Bool.false)) (Table.leaf (SupportEdge.mk 36 183 Bool.false)))) (Table.node 168 (Table.node 167 (Table.leaf (SupportEdge.mk 37 142 Bool.true)) (Table.leaf (SupportEdge.mk 37 184 Bool.false))) (Table.node 169 (Table.leaf (SupportEdge.mk 37 185 Bool.false)) (Table.node 170 (Table.leaf (SupportEdge.mk 40 145 Bool.true)) (Table.leaf (SupportEdge.mk 40 187 Bool.false)))))))) (Table.node 188 (Table.node 179 (Table.node 175 (Table.node 173 (Table.node 172 (Table.leaf (SupportEdge.mk 40 188 Bool.false)) (Table.leaf (SupportEdge.mk 46 151 Bool.true))) (Table.node 174 (Table.leaf (SupportEdge.mk 46 191 Bool.false)) (Table.leaf (SupportEdge.mk 46 192 Bool.false)))) (Table.node 177 (Table.node 176 (Table.leaf (SupportEdge.mk 91 196 Bool.false)) (Table.leaf (SupportEdge.mk 91 232 Bool.false))) (Table.node 178 (Table.leaf (SupportEdge.mk 91 233 Bool.false)) (Table.leaf (SupportEdge.mk 92 197 Bool.false))))) (Table.node 183 (Table.node 181 (Table.node 180 (Table.leaf (SupportEdge.mk 92 234 Bool.false)) (Table.leaf (SupportEdge.mk 92 235 Bool.false))) (Table.node 182 (Table.leaf (SupportEdge.mk 95 200 Bool.false)) (Table.leaf (SupportEdge.mk 95 237 Bool.false)))) (Table.node 185 (Table.node 184 (Table.leaf (SupportEdge.mk 95 238 Bool.false)) (Table.leaf (SupportEdge.mk 101 206 Bool.false))) (Table.node 186 (Table.leaf (SupportEdge.mk 101 241 Bool.false)) (Table.node 187 (Table.leaf (SupportEdge.mk 101 242 Bool.false)) (Table.leaf (SupportEdge.mk 111 216 Bool.false))))))) (Table.node 197 (Table.node 192 (Table.node 190 (Table.node 189 (Table.leaf (SupportEdge.mk 111 246 Bool.false)) (Table.leaf (SupportEdge.mk 111 247 Bool.false))) (Table.node 191 (Table.leaf (SupportEdge.mk 41 146 Bool.true)) (Table.leaf (SupportEdge.mk 41 166 Bool.true)))) (Table.node 194 (Table.node 193 (Table.leaf (SupportEdge.mk 41 182 Bool.false)) (Table.leaf (SupportEdge.mk 41 187 Bool.true))) (Table.node 195 (Table.leaf (SupportEdge.mk 42 147 Bool.true)) (Table.node 196 (Table.leaf (SupportEdge.mk 42 167 Bool.true)) (Table.leaf (SupportEdge.mk 42 183 Bool.false)))))) (Table.node 201 (Table.node 199 (Table.node 198 (Table.leaf (SupportEdge.mk 42 188 Bool.true)) (Table.leaf (SupportEdge.mk 45 150 Bool.true))) (Table.node 200 (Table.leaf (SupportEdge.mk 45 170 Bool.true)) (Table.leaf (SupportEdge.mk 45 186 Bool.false)))) (Table.node 203 (Table.node 202 (Table.leaf (SupportEdge.mk 45 190 Bool.false)) (Table.leaf (SupportEdge.mk 54 159 Bool.true))) (Table.node 204 (Table.leaf (SupportEdge.mk 54 179 Bool.true)) (Table.node 205 (Table.leaf (SupportEdge.mk 54 193 Bool.true)) (Table.leaf (SupportEdge.mk 54 195 Bool.false))))))))) (Table.node 240 (Table.node 223 (Table.node 214 (Table.node 210 (Table.node 208 (Table.node 207 (Table.leaf (SupportEdge.mk 119 224 Bool.false)) (Table.leaf (SupportEdge.mk 119 239 Bool.false))) (Table.node 209 (Table.leaf (SupportEdge.mk 119 248 Bool.true)) (Table.leaf (SupportEdge.mk 119 250 Bool.false)))) (Table.node 212 (Table.node 211 (Table.leaf (SupportEdge.mk 63 133 Bool.false)) (Table.leaf (SupportEdge.mk 63 198 Bool.false))) (Table.node 213 (Table.leaf (SupportEdge.mk 63 207 Bool.true)) (Table.leaf (SupportEdge.mk 63 209 Bool.true))))) (Table.node 218 (Table.node 216 (Table.node 215 (Table.leaf (SupportEdge.mk 64 134 Bool.false)) (Table.leaf (SupportEdge.mk 64 199 Bool.false))) (Table.node 217 (Table.leaf (SupportEdge.mk 64 208 Bool.true)) (Table.leaf (SupportEdge.mk 64 210 Bool.true)))) (Table.node 220 (Table.node 219 (Table.leaf (SupportEdge.mk 70 140 Bool.false)) (Table.leaf (SupportEdge.mk 70 205 Bool.false))) (Table.node 221 (Table.leaf (SupportEdge.mk 70 214 Bool.false)) (Table.node 222 (Table.leaf (SupportEdge.mk 70 215 Bool.false)) (Table.leaf (SupportEdge.mk 86 156 Bool.false))))))) (Table.node 231 (Table.node 227 (Table.node 225 (Table.node 224 (Table.leaf (SupportEdge.mk 86 221 Bool.true)) (Table.leaf (SupportEdge.mk 86 228 Bool.false))) (Table.node 226 (Table.leaf (SupportEdge.mk 86 229 Bool.false)) (Table.leaf (SupportEdge.mk 106 176 Bool.false)))) (Table.node 229 (Table.node 228 (Table.leaf (SupportEdge.mk 106 236 Bool.true)) (Table.leaf (SupportEdge.mk 106 243 Bool.false))) (Table.node 230 (Table.leaf (SupportEdge.mk 106 244 Bool.false)) (Table.leaf (SupportEdge.mk 73 143 Bool.false))))) (Table.node 235 (Table.node 233 (Table.node 232 (Table.leaf (SupportEdge.mk 73 198 Bool.true)) (Table.leaf (SupportEdge.mk 73 217 Bool.true))) (Table.node 234 (Table.leaf (SupportEdge.mk 73 219 Bool.true)) (Table.leaf (SupportEdge.mk 73 221 Bool.false)))) (Table.node 237 (Table.node 236 (Table.leaf (SupportEdge.mk 104 174 Bool.false)) (Table.leaf (SupportEdge.mk 104 209 Bool.false))) (Table.node 238 (Table.leaf (SupportEdge.mk 104 234 Bool.true)) (Table.node 239 (Table.leaf (SupportEdge.mk 104 241 Bool.false)) (Table.leaf (SupportEdge.mk 105 175 Bool.false)))))))) (Table.node 257 (Table.node 248 (Table.node 244 (Table.node 242 (Table.node 241 (Table.leaf (SupportEdge.mk 105 210 Bool.false)) (Table.leaf (SupportEdge.mk 105 235 Bool.true))) (Table.node 243 (Table.leaf (SupportEdge.mk 105 242 Bool.false)) (Table.leaf (SupportEdge.mk 106 176 Bool.false)))) (Table.node 246 (Table.node 245 (Table.leaf (SupportEdge.mk 106 211 Bool.false)) (Table.leaf (SupportEdge.mk 106 236 Bool.true))) (Table.node 247 (Table.leaf (SupportEdge.mk 106 243 Bool.false)) (Table.leaf (SupportEdge.mk 110 180 Bool.false))))) (Table.node 252 (Table.node 250 (Table.node 249 (Table.leaf (SupportEdge.mk 110 215 Bool.false)) (Table.leaf (SupportEdge.mk 110 240 Bool.true))) (Table.node 251 (Table.leaf (SupportEdge.mk 110 245 Bool.true)) (Table.leaf (SupportEdge.mk 124 194 Bool.false)))) (Table.node 254 (Table.node 253 (Table.leaf (SupportEdge.mk 124 229 Bool.false)) (Table.leaf (SupportEdge.mk 124 249 Bool.false))) (Table.node 255 (Table.leaf (SupportEdge.mk 124 251 Bool.true)) (Table.node 256 (Table.leaf (SupportEdge.mk 111 181 Bool.false)) (Table.leaf (SupportEdge.mk 111 216 Bool.false))))))) (Table.node 266 (Table.node 261 (Table.node 259 (Table.node 258 (Table.leaf (SupportEdge.mk 111 231 Bool.false)) (Table.leaf (SupportEdge.mk 111 247 Bool.false))) (Table.node 260 (Table.leaf (SupportEdge.mk 112 182 Bool.false)) (Table.leaf (SupportEdge.mk 112 217 Bool.false)))) (Table.node 263 (Table.node 262 (Table.leaf (SupportEdge.mk 112 232 Bool.false)) (Table.leaf (SupportEdge.mk 112 248 Bool.false))) (Table.node 264 (Table.leaf (SupportEdge.mk 114 184 Bool.false)) (Table.node 265 (Table.leaf (SupportEdge.mk 114 219 Bool.false)) (Table.leaf (SupportEdge.mk 114 234 Bool.false)))))) (Table.node 270 (Table.node 268 (Table.node 267 (Table.leaf (SupportEdge.mk 114 249 Bool.false)) (Table.leaf (SupportEdge.mk 117 187 Bool.false))) (Table.node 269 (Table.leaf (SupportEdge.mk 117 222 Bool.false)) (Table.leaf (SupportEdge.mk 117 237 Bool.false)))) (Table.node 272 (Table.node 271 (Table.leaf (SupportEdge.mk 117 250 Bool.false)) (Table.leaf (SupportEdge.mk 121 191 Bool.false))) (Table.node 273 (Table.leaf (SupportEdge.mk 121 226 Bool.false)) (Table.node 274 (Table.leaf (SupportEdge.mk 121 241 Bool.false)) (Table.leaf (SupportEdge.mk 121 251 Bool.false)))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 18 (Table.node 9 (Table.node 4 (Table.node 2 (Table.node 1 (Table.leaf 0) (Table.leaf 1)) (Table.node 3 (Table.leaf 6) (Table.leaf 17))) (Table.node 6 (Table.node 5 (Table.leaf 21) (Table.leaf 30)) (Table.node 7 (Table.leaf 45) (Table.node 8 (Table.leaf 56) (Table.leaf 69))))) (Table.node 13 (Table.node 11 (Table.node 10 (Table.leaf 106) (Table.leaf 111)) (Table.node 12 (Table.leaf 125) (Table.leaf 126))) (Table.node 15 (Table.node 14 (Table.leaf 135) (Table.leaf 150)) (Table.node 16 (Table.leaf 161) (Table.node 17 (Table.leaf 162) (Table.leaf 163)))))) (Table.node 27 (Table.node 22 (Table.node 20 (Table.node 19 (Table.leaf 164) (Table.leaf 165)) (Table.node 21 (Table.leaf 170) (Table.leaf 171))) (Table.node 24 (Table.node 23 (Table.leaf 176) (Table.leaf 177)) (Table.node 25 (Table.leaf 178) (Table.node 26 (Table.leaf 181) (Table.leaf 186))))) (Table.node 32 (Table.node 29 (Table.node 28 (Table.leaf 189) (Table.leaf 190)) (Table.node 30 (Table.leaf 211) (Table.node 31 (Table.leaf 216) (Table.leaf 231)))) (Table.node 34 (Table.node 33 (Table.leaf 236) (Table.leaf 243)) (Table.node 35 (Table.leaf 244) (Table.node 36 (Table.leaf 246) (Table.leaf 247)))))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 275 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 37 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C000.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode3 : Eq (assignment 3) Sign.positive :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode4 : Eq (assignment 4) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode5 : Eq (assignment 5) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode7 : Eq (assignment 7) Sign.positive :=
    Eq.trans (h_support 45 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode11 : Eq (assignment 11) Sign.positive :=
    Eq.trans (h_support 46 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode15 : Eq (assignment 15) Sign.negative :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode16 : Eq (assignment 16) Sign.negative :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode22 : Eq (assignment 22) Sign.negative :=
    Eq.trans (h_support 65 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode26 : Eq (assignment 26) Sign.negative :=
    Eq.trans (h_support 66 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode31 : Eq (assignment 31) Sign.positive :=
    Eq.trans (h_support 67 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode32 : Eq (assignment 32) Sign.positive :=
    Eq.trans (h_support 68 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode8 : Eq (assignment 8) Sign.positive :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode7)
  let hnode9 : Eq (assignment 9) Sign.positive :=
    Eq.trans (h_support 4 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode7)
  let hnode10 : Eq (assignment 10) Sign.positive :=
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode12 : Eq (assignment 12) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode13 : Eq (assignment 13) Sign.positive :=
    Eq.trans (h_support 7 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode14 : Eq (assignment 14) Sign.positive :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode19 : Eq (assignment 19) Sign.positive :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode20 : Eq (assignment 20) Sign.positive :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode23 : Eq (assignment 23) Sign.negative :=
    Eq.trans (h_support 69 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode24 : Eq (assignment 24) Sign.negative :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode25 : Eq (assignment 25) Sign.negative :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode27 : Eq (assignment 27) Sign.negative :=
    Eq.trans (h_support 70 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode28 : Eq (assignment 28) Sign.negative :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode29 : Eq (assignment 29) Sign.negative :=
    Eq.trans (h_support 14 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode33 : Eq (assignment 33) Sign.positive :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode34 : Eq (assignment 34) Sign.positive :=
    Eq.trans (h_support 72 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode40 : Eq (assignment 40) Sign.negative :=
    Eq.trans (h_support 73 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode42 : Eq (assignment 42) Sign.positive :=
    Eq.trans (h_support 53 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode46 : Eq (assignment 46) Sign.negative :=
    Eq.trans (h_support 74 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode48 : Eq (assignment 48) Sign.positive :=
    Eq.trans (h_support 54 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode52 : Eq (assignment 52) Sign.negative :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode53 : Eq (assignment 53) Sign.negative :=
    Eq.trans (h_support 76 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode54 : Eq (assignment 54) Sign.negative :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode58 : Eq (assignment 58) Sign.positive :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode60 : Eq (assignment 60) Sign.positive :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode62 : Eq (assignment 62) Sign.positive :=
    Eq.trans (h_support 86 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode64 : Eq (assignment 64) Sign.positive :=
    Eq.trans (h_support 90 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode65 : Eq (assignment 65) Sign.positive :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode67 : Eq (assignment 67) Sign.positive :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode68 : Eq (assignment 68) Sign.negative :=
    Eq.trans (h_support 88 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode70 : Eq (assignment 70) Sign.positive :=
    Eq.trans (h_support 92 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode127 : Eq (assignment 127) Sign.positive :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode131 : Eq (assignment 131) Sign.positive :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode166 : Eq (assignment 166) Sign.negative :=
    Eq.trans (h_support 149 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode167 : Eq (assignment 167) Sign.negative :=
    Eq.trans (h_support 150 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode172 : Eq (assignment 172) Sign.negative :=
    Eq.trans (h_support 155 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode173 : Eq (assignment 173) Sign.negative :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode41 : Eq (assignment 41) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 191 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode166)
  let hnode57 : Eq (assignment 57) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 18 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode61 : Eq (assignment 61) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 21 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode62)
  let hnode77 : Eq (assignment 77) Sign.positive :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode67)
  let hnode79 : Eq (assignment 79) Sign.negative :=
    Eq.trans (h_support 93 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode19)
  let hnode83 : Eq (assignment 83) Sign.positive :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode67)
  let hnode85 : Eq (assignment 85) Sign.negative :=
    Eq.trans (h_support 94 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode19)
  let hnode87 : Eq (assignment 87) Sign.negative :=
    Eq.trans (h_support 105 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode52)
  let hnode88 : Eq (assignment 88) Sign.negative :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode19)
  let hnode89 : Eq (assignment 89) Sign.negative :=
    Eq.trans (h_support 60 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode67)
  let hnode90 : Eq (assignment 90) Sign.positive :=
    Eq.trans (h_support 96 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode95 : Eq (assignment 95) Sign.negative :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode65)
  let hnode99 : Eq (assignment 99) Sign.negative :=
    Eq.trans (h_support 97 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode101 : Eq (assignment 101) Sign.negative :=
    Eq.trans (h_support 78 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode65)
  let hnode105 : Eq (assignment 105) Sign.negative :=
    Eq.trans (h_support 98 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode107 : Eq (assignment 107) Sign.negative :=
    Eq.trans (h_support 79 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode65)
  let hnode108 : Eq (assignment 108) Sign.negative :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode109 : Eq (assignment 109) Sign.negative :=
    Eq.trans (h_support 114 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode110 : Eq (assignment 110) Sign.positive :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode117 : Eq (assignment 117) Sign.negative :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode52)
  let hnode118 : Eq (assignment 118) Sign.negative :=
    Eq.trans (h_support 111 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode119 : Eq (assignment 119) Sign.negative :=
    Eq.trans (h_support 115 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode121 : Eq (assignment 121) Sign.negative :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode52)
  let hnode122 : Eq (assignment 122) Sign.negative :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode123 : Eq (assignment 123) Sign.negative :=
    Eq.trans (h_support 116 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode128 : Eq (assignment 128) Sign.positive :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode129 : Eq (assignment 129) Sign.positive :=
    Eq.trans (h_support 125 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode130 : Eq (assignment 130) Sign.positive :=
    Eq.trans (h_support 129 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode132 : Eq (assignment 132) Sign.positive :=
    Eq.trans (h_support 157 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode133 : Eq (assignment 133) Sign.positive :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode131)
  let hnode134 : Eq (assignment 134) Sign.positive :=
    Eq.trans (h_support 214 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode64)
  let hnode140 : Eq (assignment 140) Sign.positive :=
    Eq.trans (h_support 133 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode143 : Eq (assignment 143) Sign.negative :=
    Eq.trans (h_support 126 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode144 : Eq (assignment 144) Sign.negative :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode145 : Eq (assignment 145) Sign.positive :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode146 : Eq (assignment 146) Sign.negative :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode147 : Eq (assignment 147) Sign.negative :=
    Eq.trans (h_support 131 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode148 : Eq (assignment 148) Sign.negative :=
    Eq.trans (h_support 128 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode149 : Eq (assignment 149) Sign.negative :=
    Eq.trans (h_support 132 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode151 : Eq (assignment 151) Sign.positive :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode46)
  let hnode156 : Eq (assignment 156) Sign.positive :=
    Eq.trans (h_support 134 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode159 : Eq (assignment 159) Sign.positive :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode160 : Eq (assignment 160) Sign.positive :=
    Eq.trans (h_support 136 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode168 : Eq (assignment 168) Sign.negative :=
    Eq.trans (h_support 152 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode169 : Eq (assignment 169) Sign.negative :=
    Eq.trans (h_support 153 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode174 : Eq (assignment 174) Sign.negative :=
    Eq.trans (h_support 158 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode175 : Eq (assignment 175) Sign.negative :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode179 : Eq (assignment 179) Sign.positive :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode183 : Eq (assignment 183) Sign.positive :=
    Eq.trans (h_support 196 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode42)
  let hnode187 : Eq (assignment 187) Sign.negative :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode188 : Eq (assignment 188) Sign.negative :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode191 : Eq (assignment 191) Sign.negative :=
    Eq.trans (h_support 173 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode192 : Eq (assignment 192) Sign.negative :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode193 : Eq (assignment 193) Sign.positive :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode195 : Eq (assignment 195) Sign.negative :=
    Eq.trans (h_support 205 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode199 : Eq (assignment 199) Sign.positive :=
    Eq.trans (h_support 215 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode64)
  let hnode205 : Eq (assignment 205) Sign.positive :=
    Eq.trans (h_support 219 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode208 : Eq (assignment 208) Sign.negative :=
    Eq.trans (h_support 216 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode64)
  let hnode210 : Eq (assignment 210) Sign.negative :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode64)
  let hnode214 : Eq (assignment 214) Sign.positive :=
    Eq.trans (h_support 220 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode215 : Eq (assignment 215) Sign.positive :=
    Eq.trans (h_support 221 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode36 : Eq (assignment 36) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 165 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode183)
  let hnode55 : Eq (assignment 55) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 118 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode110)
  let hnode59 : Eq (assignment 59) Sign.positive :=
    Eq.trans (h_support 19 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode57)
  let hnode63 : Eq (assignment 63) Sign.positive :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode61)
  let hnode73 : Eq (assignment 73) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 230 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode143)
  let hnode80 : Eq (assignment 80) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 141 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode205)
  let hnode86 : Eq (assignment 86) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 222 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode156)
  let hnode104 : Eq (assignment 104) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 235 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode174)
  let hnode137 : Eq (assignment 137) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 61 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode147)
  let hnode139 : Eq (assignment 139) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 102 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode210)
  let hnode141 : Eq (assignment 141) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 38 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode144)
  let hnode180 : Eq (assignment 180) Sign.positive :=
    Eq.trans (h_support 247 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode110)
  let hnode182 : Eq (assignment 182) Sign.positive :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode196 : Eq (assignment 196) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 44 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode199)
  let hnode200 : Eq (assignment 200) Sign.negative :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode206 : Eq (assignment 206) Sign.negative :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode101)
  let hnode222 : Eq (assignment 222) Sign.negative :=
    Eq.trans (h_support 268 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode117)
  let hnode224 : Eq (assignment 224) Sign.negative :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode119)
  let hnode226 : Eq (assignment 226) Sign.negative :=
    Eq.trans (h_support 272 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode230 : Eq (assignment 230) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode195)
  let hnode235 : Eq (assignment 235) Sign.positive :=
    Eq.trans (h_support 241 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode105)
  let hnode237 : Eq (assignment 237) Sign.negative :=
    Eq.trans (h_support 182 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode238 : Eq (assignment 238) Sign.negative :=
    Eq.trans (h_support 183 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode239 : Eq (assignment 239) Sign.negative :=
    Eq.trans (h_support 207 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode119)
  let hnode240 : Eq (assignment 240) Sign.negative :=
    Eq.trans (h_support 249 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode110)
  let hnode241 : Eq (assignment 241) Sign.negative :=
    Eq.trans (h_support 185 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode101)
  let hnode242 : Eq (assignment 242) Sign.negative :=
    Eq.trans (h_support 242 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode105)
  let hnode245 : Eq (assignment 245) Sign.negative :=
    Eq.trans (h_support 250 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode110)
  let hnode248 : Eq (assignment 248) Sign.positive :=
    Eq.trans (h_support 208 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode119)
  let hnode250 : Eq (assignment 250) Sign.negative :=
    Eq.trans (h_support 270 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode117)
  let hnode251 : Eq (assignment 251) Sign.negative :=
    Eq.trans (h_support 274 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode37 : Eq (assignment 37) Sign.positive :=
    Eq.trans (h_support 15 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode38 : Eq (assignment 38) Sign.positive :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode39 : Eq (assignment 39) Sign.positive :=
    Eq.trans (h_support 17 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode71 : Eq (assignment 71) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 25 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode73)
  let hnode91 : Eq (assignment 91) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 175 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode196)
  let hnode92 : Eq (assignment 92) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 180 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode235)
  let hnode112 : Eq (assignment 112) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 259 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode182)
  let hnode120 : Eq (assignment 120) Sign.positive :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode124 : Eq (assignment 124) Sign.positive :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode142 : Eq (assignment 142) Sign.negative :=
    Eq.trans (h_support 36 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode141)
  let hnode153 : Eq (assignment 153) Sign.negative :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode137)
  let hnode158 : Eq (assignment 158) Sign.positive :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode137)
  let hnode197 : Eq (assignment 197) Sign.positive :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode196)
  let hnode198 : Eq (assignment 198) Sign.positive :=
    Eq.trans (h_support 211 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode63)
  let hnode204 : Eq (assignment 204) Sign.negative :=
    Eq.trans (h_support 101 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode139)
  let hnode207 : Eq (assignment 207) Sign.negative :=
    Eq.trans (h_support 212 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode209 : Eq (assignment 209) Sign.negative :=
    Eq.trans (h_support 236 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode213 : Eq (assignment 213) Sign.negative :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode139)
  let hnode217 : Eq (assignment 217) Sign.positive :=
    Eq.trans (h_support 232 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode73)
  let hnode219 : Eq (assignment 219) Sign.positive :=
    Eq.trans (h_support 233 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode73)
  let hnode221 : Eq (assignment 221) Sign.negative :=
    Eq.trans (h_support 223 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode86)
  let hnode225 : Eq (assignment 225) Sign.negative :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode228 : Eq (assignment 228) Sign.positive :=
    Eq.trans (h_support 224 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode86)
  let hnode229 : Eq (assignment 229) Sign.positive :=
    Eq.trans (h_support 225 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode86)
  let hnode234 : Eq (assignment 234) Sign.positive :=
    Eq.trans (h_support 237 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode104)
  let hnode72 : Eq (assignment 72) Sign.negative :=
    Eq.trans (h_support 24 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode74 : Eq (assignment 74) Sign.negative :=
    Eq.trans (h_support 26 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode93 : Eq (assignment 93) Sign.positive :=
    Eq.trans (h_support 28 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode94 : Eq (assignment 94) Sign.positive :=
    Eq.trans (h_support 29 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode114 : Eq (assignment 114) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 265 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode234)
  let hnode184 : Eq (assignment 184) Sign.positive :=
    Eq.trans (h_support 167 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode185 : Eq (assignment 185) Sign.positive :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode194 : Eq (assignment 194) Sign.positive :=
    Eq.trans (h_support 251 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode124)
  let hnode232 : Eq (assignment 232) Sign.positive :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode233 : Eq (assignment 233) Sign.positive :=
    Eq.trans (h_support 177 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode249 : Eq (assignment 249) Sign.positive :=
    Eq.trans (h_support 253 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode124)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C000.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (domain_from_eq (domain := Cases.C000.initial 0) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded2 := below_succ bounded1 (domain_from_eq (domain := Cases.C000.initial 1) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded3 := below_succ bounded2 (domain_from_eq (domain := Cases.C000.initial 2) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded4 := below_succ bounded3 (domain_from_eq (domain := Cases.C000.initial 3) (congrArg (Sign.withNegation globalNegation) hnode3) (Eq.refl Bool.true))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C000.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Cases.C000.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Cases.C000.initial 6) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Cases.C000.initial 7) (congrArg (Sign.withNegation globalNegation) hnode7) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C000.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Cases.C000.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C000.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (domain_from_eq (domain := Cases.C000.initial 11) (congrArg (Sign.withNegation globalNegation) hnode11) (Eq.refl Bool.true))
  let bounded13 := below_succ bounded12 (domain_from_eq (domain := Cases.C000.initial 12) (congrArg (Sign.withNegation globalNegation) hnode12) (Eq.refl Bool.true))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C000.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C000.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Cases.C000.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Cases.C000.initial 16) (congrArg (Sign.withNegation globalNegation) hnode16) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C000.initial 17) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (top_allows (Sign.withNegation globalNegation (assignment 18)))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C000.initial 19) (congrArg (Sign.withNegation globalNegation) hnode19) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Cases.C000.initial 20) (congrArg (Sign.withNegation globalNegation) hnode20) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C000.initial 21) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (domain_from_eq (domain := Cases.C000.initial 22) (congrArg (Sign.withNegation globalNegation) hnode22) (Eq.refl Bool.true))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C000.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C000.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C000.initial 25) (congrArg (Sign.withNegation globalNegation) hnode25) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Cases.C000.initial 26) (congrArg (Sign.withNegation globalNegation) hnode26) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C000.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C000.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C000.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (domain_from_eq (domain := Cases.C000.initial 30) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded32 := below_succ bounded31 (domain_from_eq (domain := Cases.C000.initial 31) (congrArg (Sign.withNegation globalNegation) hnode31) (Eq.refl Bool.true))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C000.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C000.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C000.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (top_allows (Sign.withNegation globalNegation (assignment 35)))
  let bounded37 := below_succ bounded36 (domain_from_eq (domain := Cases.C000.initial 36) (congrArg (Sign.withNegation globalNegation) hnode36) (Eq.refl Bool.true))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C000.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C000.initial 38) (congrArg (Sign.withNegation globalNegation) hnode38) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (domain_from_eq (domain := Cases.C000.initial 39) (congrArg (Sign.withNegation globalNegation) hnode39) (Eq.refl Bool.true))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Cases.C000.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C000.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C000.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (top_allows (Sign.withNegation globalNegation (assignment 43)))
  let bounded45 := below_succ bounded44 (top_allows (Sign.withNegation globalNegation (assignment 44)))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C000.initial 45) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (domain_from_eq (domain := Cases.C000.initial 46) (congrArg (Sign.withNegation globalNegation) hnode46) (Eq.refl Bool.true))
  let bounded48 := below_succ bounded47 (top_allows (Sign.withNegation globalNegation (assignment 47)))
  let bounded49 := below_succ bounded48 (domain_from_eq (domain := Cases.C000.initial 48) (congrArg (Sign.withNegation globalNegation) hnode48) (Eq.refl Bool.true))
  let bounded50 := below_succ bounded49 (top_allows (Sign.withNegation globalNegation (assignment 49)))
  let bounded51 := below_succ bounded50 (top_allows (Sign.withNegation globalNegation (assignment 50)))
  let bounded52 := below_succ bounded51 (top_allows (Sign.withNegation globalNegation (assignment 51)))
  let bounded53 := below_succ bounded52 (domain_from_eq (domain := Cases.C000.initial 52) (congrArg (Sign.withNegation globalNegation) hnode52) (Eq.refl Bool.true))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Cases.C000.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Cases.C000.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (domain_from_eq (domain := Cases.C000.initial 55) (congrArg (Sign.withNegation globalNegation) hnode55) (Eq.refl Bool.true))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C000.initial 56) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C000.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C000.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C000.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C000.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Cases.C000.initial 61) (congrArg (Sign.withNegation globalNegation) hnode61) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C000.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C000.initial 63) (congrArg (Sign.withNegation globalNegation) hnode63) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C000.initial 64) (congrArg (Sign.withNegation globalNegation) hnode64) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (domain_from_eq (domain := Cases.C000.initial 65) (congrArg (Sign.withNegation globalNegation) hnode65) (Eq.refl Bool.true))
  let bounded67 := below_succ bounded66 (top_allows (Sign.withNegation globalNegation (assignment 66)))
  let bounded68 := below_succ bounded67 (domain_from_eq (domain := Cases.C000.initial 67) (congrArg (Sign.withNegation globalNegation) hnode67) (Eq.refl Bool.true))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C000.initial 68) (congrArg (Sign.withNegation globalNegation) hnode68) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C000.initial 69) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C000.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C000.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C000.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C000.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C000.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (top_allows (Sign.withNegation globalNegation (assignment 75)))
  let bounded77 := below_succ bounded76 (top_allows (Sign.withNegation globalNegation (assignment 76)))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C000.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (top_allows (Sign.withNegation globalNegation (assignment 78)))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C000.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (domain_from_eq (domain := Cases.C000.initial 80) (congrArg (Sign.withNegation globalNegation) hnode80) (Eq.refl Bool.true))
  let bounded82 := below_succ bounded81 (top_allows (Sign.withNegation globalNegation (assignment 81)))
  let bounded83 := below_succ bounded82 (top_allows (Sign.withNegation globalNegation (assignment 82)))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C000.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (top_allows (Sign.withNegation globalNegation (assignment 84)))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C000.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C000.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C000.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Cases.C000.initial 88) (congrArg (Sign.withNegation globalNegation) hnode88) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (domain_from_eq (domain := Cases.C000.initial 89) (congrArg (Sign.withNegation globalNegation) hnode89) (Eq.refl Bool.true))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C000.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C000.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C000.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C000.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C000.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C000.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (top_allows (Sign.withNegation globalNegation (assignment 96)))
  let bounded98 := below_succ bounded97 (top_allows (Sign.withNegation globalNegation (assignment 97)))
  let bounded99 := below_succ bounded98 (top_allows (Sign.withNegation globalNegation (assignment 98)))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C000.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (top_allows (Sign.withNegation globalNegation (assignment 100)))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C000.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (top_allows (Sign.withNegation globalNegation (assignment 102)))
  let bounded104 := below_succ bounded103 (top_allows (Sign.withNegation globalNegation (assignment 103)))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C000.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C000.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C000.initial 106) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C000.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C000.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C000.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C000.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C000.initial 111) (congrArg (Sign.withNegation globalNegation) (h_zero 10 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C000.initial 112) (congrArg (Sign.withNegation globalNegation) hnode112) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (top_allows (Sign.withNegation globalNegation (assignment 113)))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C000.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (top_allows (Sign.withNegation globalNegation (assignment 115)))
  let bounded117 := below_succ bounded116 (top_allows (Sign.withNegation globalNegation (assignment 116)))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C000.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C000.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C000.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C000.initial 120) (congrArg (Sign.withNegation globalNegation) hnode120) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C000.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C000.initial 122) (congrArg (Sign.withNegation globalNegation) hnode122) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C000.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C000.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Cases.C000.initial 125) (congrArg (Sign.withNegation globalNegation) (h_zero 11 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (domain_from_eq (domain := Cases.C000.initial 126) (congrArg (Sign.withNegation globalNegation) (h_zero 12 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded128 := below_succ bounded127 (domain_from_eq (domain := Cases.C000.initial 127) (congrArg (Sign.withNegation globalNegation) hnode127) (Eq.refl Bool.true))
  let bounded129 := below_succ bounded128 (domain_from_eq (domain := Cases.C000.initial 128) (congrArg (Sign.withNegation globalNegation) hnode128) (Eq.refl Bool.true))
  let bounded130 := below_succ bounded129 (domain_from_eq (domain := Cases.C000.initial 129) (congrArg (Sign.withNegation globalNegation) hnode129) (Eq.refl Bool.true))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C000.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C000.initial 131) (congrArg (Sign.withNegation globalNegation) hnode131) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C000.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C000.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C000.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C000.initial 135) (congrArg (Sign.withNegation globalNegation) (h_zero 13 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (top_allows (Sign.withNegation globalNegation (assignment 136)))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C000.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (top_allows (Sign.withNegation globalNegation (assignment 138)))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C000.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C000.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C000.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C000.initial 142) (congrArg (Sign.withNegation globalNegation) hnode142) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C000.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C000.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C000.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C000.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C000.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C000.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C000.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C000.initial 150) (congrArg (Sign.withNegation globalNegation) (h_zero 14 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C000.initial 151) (congrArg (Sign.withNegation globalNegation) hnode151) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (top_allows (Sign.withNegation globalNegation (assignment 152)))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C000.initial 153) (congrArg (Sign.withNegation globalNegation) hnode153) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (top_allows (Sign.withNegation globalNegation (assignment 154)))
  let bounded156 := below_succ bounded155 (top_allows (Sign.withNegation globalNegation (assignment 155)))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C000.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (top_allows (Sign.withNegation globalNegation (assignment 157)))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C000.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C000.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C000.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (domain_from_eq (domain := Cases.C000.initial 161) (congrArg (Sign.withNegation globalNegation) (h_zero 15 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Cases.C000.initial 162) (congrArg (Sign.withNegation globalNegation) (h_zero 16 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C000.initial 163) (congrArg (Sign.withNegation globalNegation) (h_zero 17 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C000.initial 164) (congrArg (Sign.withNegation globalNegation) (h_zero 18 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C000.initial 165) (congrArg (Sign.withNegation globalNegation) (h_zero 19 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C000.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C000.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (domain_from_eq (domain := Cases.C000.initial 168) (congrArg (Sign.withNegation globalNegation) hnode168) (Eq.refl Bool.true))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C000.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C000.initial 170) (congrArg (Sign.withNegation globalNegation) (h_zero 20 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C000.initial 171) (congrArg (Sign.withNegation globalNegation) (h_zero 21 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C000.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C000.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C000.initial 174) (congrArg (Sign.withNegation globalNegation) hnode174) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C000.initial 175) (congrArg (Sign.withNegation globalNegation) hnode175) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C000.initial 176) (congrArg (Sign.withNegation globalNegation) (h_zero 22 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Cases.C000.initial 177) (congrArg (Sign.withNegation globalNegation) (h_zero 23 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C000.initial 178) (congrArg (Sign.withNegation globalNegation) (h_zero 24 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C000.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C000.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C000.initial 181) (congrArg (Sign.withNegation globalNegation) (h_zero 25 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C000.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C000.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Cases.C000.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C000.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Cases.C000.initial 186) (congrArg (Sign.withNegation globalNegation) (h_zero 26 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C000.initial 187) (congrArg (Sign.withNegation globalNegation) hnode187) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C000.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C000.initial 189) (congrArg (Sign.withNegation globalNegation) (h_zero 27 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C000.initial 190) (congrArg (Sign.withNegation globalNegation) (h_zero 28 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C000.initial 191) (congrArg (Sign.withNegation globalNegation) hnode191) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C000.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C000.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Cases.C000.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C000.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (domain_from_eq (domain := Cases.C000.initial 196) (congrArg (Sign.withNegation globalNegation) hnode196) (Eq.refl Bool.true))
  let bounded198 := below_succ bounded197 (domain_from_eq (domain := Cases.C000.initial 197) (congrArg (Sign.withNegation globalNegation) hnode197) (Eq.refl Bool.true))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Cases.C000.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (domain_from_eq (domain := Cases.C000.initial 199) (congrArg (Sign.withNegation globalNegation) hnode199) (Eq.refl Bool.true))
  let bounded201 := below_succ bounded200 (domain_from_eq (domain := Cases.C000.initial 200) (congrArg (Sign.withNegation globalNegation) hnode200) (Eq.refl Bool.true))
  let bounded202 := below_succ bounded201 (top_allows (Sign.withNegation globalNegation (assignment 201)))
  let bounded203 := below_succ bounded202 (top_allows (Sign.withNegation globalNegation (assignment 202)))
  let bounded204 := below_succ bounded203 (top_allows (Sign.withNegation globalNegation (assignment 203)))
  let bounded205 := below_succ bounded204 (domain_from_eq (domain := Cases.C000.initial 204) (congrArg (Sign.withNegation globalNegation) hnode204) (Eq.refl Bool.true))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C000.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Cases.C000.initial 206) (congrArg (Sign.withNegation globalNegation) hnode206) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Cases.C000.initial 207) (congrArg (Sign.withNegation globalNegation) hnode207) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C000.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C000.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C000.initial 210) (congrArg (Sign.withNegation globalNegation) hnode210) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C000.initial 211) (congrArg (Sign.withNegation globalNegation) (h_zero 29 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (top_allows (Sign.withNegation globalNegation (assignment 212)))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C000.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C000.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (domain_from_eq (domain := Cases.C000.initial 215) (congrArg (Sign.withNegation globalNegation) hnode215) (Eq.refl Bool.true))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C000.initial 216) (congrArg (Sign.withNegation globalNegation) (h_zero 30 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C000.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (top_allows (Sign.withNegation globalNegation (assignment 218)))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Cases.C000.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (top_allows (Sign.withNegation globalNegation (assignment 220)))
  let bounded222 := below_succ bounded221 (domain_from_eq (domain := Cases.C000.initial 221) (congrArg (Sign.withNegation globalNegation) hnode221) (Eq.refl Bool.true))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C000.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (top_allows (Sign.withNegation globalNegation (assignment 223)))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C000.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C000.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C000.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (top_allows (Sign.withNegation globalNegation (assignment 227)))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C000.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Cases.C000.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C000.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (domain_from_eq (domain := Cases.C000.initial 231) (congrArg (Sign.withNegation globalNegation) (h_zero 31 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C000.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (domain_from_eq (domain := Cases.C000.initial 233) (congrArg (Sign.withNegation globalNegation) hnode233) (Eq.refl Bool.true))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C000.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C000.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (domain_from_eq (domain := Cases.C000.initial 236) (congrArg (Sign.withNegation globalNegation) (h_zero 32 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C000.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C000.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Cases.C000.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (domain_from_eq (domain := Cases.C000.initial 240) (congrArg (Sign.withNegation globalNegation) hnode240) (Eq.refl Bool.true))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C000.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C000.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C000.initial 243) (congrArg (Sign.withNegation globalNegation) (h_zero 33 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C000.initial 244) (congrArg (Sign.withNegation globalNegation) (h_zero 34 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C000.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C000.initial 246) (congrArg (Sign.withNegation globalNegation) (h_zero 35 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C000.initial 247) (congrArg (Sign.withNegation globalNegation) (h_zero 36 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C000.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (domain_from_eq (domain := Cases.C000.initial 249) (congrArg (Sign.withNegation globalNegation) hnode249) (Eq.refl Bool.true))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Cases.C000.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C000.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C000.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C000
#print axioms Papers.RationalityTen.PureGP.Initializers.C000.support_sign_contradiction
