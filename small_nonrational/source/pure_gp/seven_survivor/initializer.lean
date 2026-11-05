module
prelude
public import PureGP.SevenSurvivor.Trace

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.SevenSurvivor.Initializer
def anchor : Nat := 3
def globalNegation : Bool := Bool.false
def edgeTable : Table SupportEdge := (Table.node 127 (Table.node 63 (Table.node 31 (Table.node 15 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 3 4 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 3 5 Bool.false)) (Table.leaf (SupportEdge.mk 8 9 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 8 10 Bool.false)) (Table.leaf (SupportEdge.mk 12 13 Bool.false))) (Table.node 6 (Table.leaf (SupportEdge.mk 12 14 Bool.false)) (Table.leaf (SupportEdge.mk 15 16 Bool.false))))) (Table.node 11 (Table.node 9 (Table.node 8 (Table.leaf (SupportEdge.mk 15 17 Bool.false)) (Table.leaf (SupportEdge.mk 23 24 Bool.false))) (Table.node 10 (Table.leaf (SupportEdge.mk 23 25 Bool.false)) (Table.leaf (SupportEdge.mk 27 28 Bool.false)))) (Table.node 13 (Table.node 12 (Table.leaf (SupportEdge.mk 27 29 Bool.false)) (Table.leaf (SupportEdge.mk 30 31 Bool.false))) (Table.node 14 (Table.leaf (SupportEdge.mk 30 32 Bool.false)) (Table.leaf (SupportEdge.mk 37 38 Bool.false)))))) (Table.node 23 (Table.node 19 (Table.node 17 (Table.node 16 (Table.leaf (SupportEdge.mk 37 39 Bool.false)) (Table.leaf (SupportEdge.mk 40 41 Bool.false))) (Table.node 18 (Table.leaf (SupportEdge.mk 40 42 Bool.false)) (Table.leaf (SupportEdge.mk 46 47 Bool.false)))) (Table.node 21 (Table.node 20 (Table.leaf (SupportEdge.mk 46 48 Bool.false)) (Table.leaf (SupportEdge.mk 58 59 Bool.false))) (Table.node 22 (Table.leaf (SupportEdge.mk 58 60 Bool.false)) (Table.leaf (SupportEdge.mk 62 63 Bool.false))))) (Table.node 27 (Table.node 25 (Table.node 24 (Table.leaf (SupportEdge.mk 62 64 Bool.false)) (Table.leaf (SupportEdge.mk 65 66 Bool.false))) (Table.node 26 (Table.leaf (SupportEdge.mk 65 67 Bool.false)) (Table.leaf (SupportEdge.mk 72 73 Bool.false)))) (Table.node 29 (Table.node 28 (Table.leaf (SupportEdge.mk 72 74 Bool.false)) (Table.leaf (SupportEdge.mk 75 76 Bool.false))) (Table.node 30 (Table.leaf (SupportEdge.mk 75 77 Bool.false)) (Table.leaf (SupportEdge.mk 81 82 Bool.false))))))) (Table.node 47 (Table.node 39 (Table.node 35 (Table.node 33 (Table.node 32 (Table.leaf (SupportEdge.mk 81 83 Bool.false)) (Table.leaf (SupportEdge.mk 92 93 Bool.false))) (Table.node 34 (Table.leaf (SupportEdge.mk 92 94 Bool.false)) (Table.leaf (SupportEdge.mk 95 96 Bool.false)))) (Table.node 37 (Table.node 36 (Table.leaf (SupportEdge.mk 95 97 Bool.false)) (Table.leaf (SupportEdge.mk 101 102 Bool.false))) (Table.node 38 (Table.leaf (SupportEdge.mk 101 103 Bool.false)) (Table.leaf (SupportEdge.mk 111 112 Bool.false))))) (Table.node 43 (Table.node 41 (Table.node 40 (Table.leaf (SupportEdge.mk 111 113 Bool.false)) (Table.leaf (SupportEdge.mk 128 129 Bool.false))) (Table.node 42 (Table.leaf (SupportEdge.mk 128 130 Bool.false)) (Table.leaf (SupportEdge.mk 132 133 Bool.false)))) (Table.node 45 (Table.node 44 (Table.leaf (SupportEdge.mk 132 134 Bool.false)) (Table.leaf (SupportEdge.mk 135 136 Bool.false))) (Table.node 46 (Table.leaf (SupportEdge.mk 135 137 Bool.false)) (Table.leaf (SupportEdge.mk 142 143 Bool.false)))))) (Table.node 55 (Table.node 51 (Table.node 49 (Table.node 48 (Table.leaf (SupportEdge.mk 142 144 Bool.false)) (Table.leaf (SupportEdge.mk 145 146 Bool.false))) (Table.node 50 (Table.leaf (SupportEdge.mk 145 147 Bool.false)) (Table.leaf (SupportEdge.mk 151 152 Bool.false)))) (Table.node 53 (Table.node 52 (Table.leaf (SupportEdge.mk 151 153 Bool.false)) (Table.leaf (SupportEdge.mk 162 163 Bool.false))) (Table.node 54 (Table.leaf (SupportEdge.mk 162 164 Bool.false)) (Table.leaf (SupportEdge.mk 165 166 Bool.false))))) (Table.node 59 (Table.node 57 (Table.node 56 (Table.leaf (SupportEdge.mk 165 167 Bool.false)) (Table.leaf (SupportEdge.mk 171 172 Bool.false))) (Table.node 58 (Table.leaf (SupportEdge.mk 171 173 Bool.false)) (Table.leaf (SupportEdge.mk 181 182 Bool.false)))) (Table.node 61 (Table.node 60 (Table.leaf (SupportEdge.mk 181 183 Bool.false)) (Table.leaf (SupportEdge.mk 197 198 Bool.false))) (Table.node 62 (Table.leaf (SupportEdge.mk 197 199 Bool.false)) (Table.leaf (SupportEdge.mk 200 201 Bool.false)))))))) (Table.node 95 (Table.node 79 (Table.node 71 (Table.node 67 (Table.node 65 (Table.node 64 (Table.leaf (SupportEdge.mk 200 202 Bool.false)) (Table.leaf (SupportEdge.mk 206 207 Bool.false))) (Table.node 66 (Table.leaf (SupportEdge.mk 206 208 Bool.false)) (Table.leaf (SupportEdge.mk 216 217 Bool.false)))) (Table.node 69 (Table.node 68 (Table.leaf (SupportEdge.mk 216 218 Bool.false)) (Table.leaf (SupportEdge.mk 231 232 Bool.false))) (Table.node 70 (Table.leaf (SupportEdge.mk 231 233 Bool.false)) (Table.leaf (SupportEdge.mk 10 60 Bool.true))))) (Table.node 75 (Table.node 73 (Table.node 72 (Table.leaf (SupportEdge.mk 10 74 Bool.false)) (Table.leaf (SupportEdge.mk 10 77 Bool.false))) (Table.node 74 (Table.leaf (SupportEdge.mk 10 79 Bool.false)) (Table.leaf (SupportEdge.mk 10 80 Bool.false)))) (Table.node 77 (Table.node 76 (Table.leaf (SupportEdge.mk 3 8 Bool.false)) (Table.leaf (SupportEdge.mk 3 12 Bool.false))) (Table.node 78 (Table.leaf (SupportEdge.mk 3 15 Bool.false)) (Table.leaf (SupportEdge.mk 3 18 Bool.true)))))) (Table.node 87 (Table.node 83 (Table.node 81 (Table.node 80 (Table.leaf (SupportEdge.mk 5 10 Bool.false)) (Table.leaf (SupportEdge.mk 5 14 Bool.false))) (Table.node 82 (Table.leaf (SupportEdge.mk 5 17 Bool.false)) (Table.leaf (SupportEdge.mk 5 20 Bool.false)))) (Table.node 85 (Table.node 84 (Table.leaf (SupportEdge.mk 34 44 Bool.false)) (Table.leaf (SupportEdge.mk 34 50 Bool.false))) (Table.node 86 (Table.leaf (SupportEdge.mk 34 53 Bool.false)) (Table.leaf (SupportEdge.mk 34 55 Bool.true))))) (Table.node 91 (Table.node 89 (Table.node 88 (Table.leaf (SupportEdge.mk 69 79 Bool.false)) (Table.leaf (SupportEdge.mk 69 85 Bool.false))) (Table.node 90 (Table.leaf (SupportEdge.mk 69 88 Bool.false)) (Table.leaf (SupportEdge.mk 69 90 Bool.true)))) (Table.node 93 (Table.node 92 (Table.leaf (SupportEdge.mk 139 149 Bool.false)) (Table.leaf (SupportEdge.mk 139 155 Bool.false))) (Table.node 94 (Table.leaf (SupportEdge.mk 139 158 Bool.false)) (Table.leaf (SupportEdge.mk 139 160 Bool.true))))))) (Table.node 111 (Table.node 103 (Table.node 99 (Table.node 97 (Table.node 96 (Table.leaf (SupportEdge.mk 0 21 Bool.false)) (Table.leaf (SupportEdge.mk 0 22 Bool.false))) (Table.node 98 (Table.leaf (SupportEdge.mk 0 24 Bool.false)) (Table.leaf (SupportEdge.mk 0 25 Bool.false)))) (Table.node 101 (Table.node 100 (Table.leaf (SupportEdge.mk 3 27 Bool.true)) (Table.leaf (SupportEdge.mk 3 30 Bool.true))) (Table.node 102 (Table.leaf (SupportEdge.mk 3 33 Bool.false)) (Table.leaf (SupportEdge.mk 3 34 Bool.false))))) (Table.node 107 (Table.node 105 (Table.node 104 (Table.leaf (SupportEdge.mk 8 37 Bool.true)) (Table.leaf (SupportEdge.mk 8 40 Bool.true))) (Table.node 106 (Table.leaf (SupportEdge.mk 8 43 Bool.false)) (Table.leaf (SupportEdge.mk 8 44 Bool.false)))) (Table.node 109 (Table.node 108 (Table.leaf (SupportEdge.mk 58 92 Bool.false)) (Table.leaf (SupportEdge.mk 58 95 Bool.false))) (Table.node 110 (Table.leaf (SupportEdge.mk 58 98 Bool.true)) (Table.leaf (SupportEdge.mk 58 99 Bool.true)))))) (Table.node 119 (Table.node 115 (Table.node 113 (Table.node 112 (Table.leaf (SupportEdge.mk 128 162 Bool.false)) (Table.leaf (SupportEdge.mk 128 165 Bool.false))) (Table.node 114 (Table.leaf (SupportEdge.mk 128 168 Bool.true)) (Table.leaf (SupportEdge.mk 128 169 Bool.true)))) (Table.node 117 (Table.node 116 (Table.leaf (SupportEdge.mk 43 78 Bool.false)) (Table.leaf (SupportEdge.mk 43 98 Bool.false))) (Table.node 118 (Table.leaf (SupportEdge.mk 43 114 Bool.true)) (Table.leaf (SupportEdge.mk 43 117 Bool.true))))) (Table.node 123 (Table.node 121 (Table.node 120 (Table.leaf (SupportEdge.mk 44 79 Bool.false)) (Table.leaf (SupportEdge.mk 44 99 Bool.false))) (Table.node 122 (Table.leaf (SupportEdge.mk 44 115 Bool.true)) (Table.leaf (SupportEdge.mk 44 118 Bool.true)))) (Table.node 125 (Table.node 124 (Table.leaf (SupportEdge.mk 45 80 Bool.false)) (Table.leaf (SupportEdge.mk 45 100 Bool.false))) (Table.node 126 (Table.leaf (SupportEdge.mk 45 116 Bool.true)) (Table.leaf (SupportEdge.mk 45 119 Bool.true))))))))) (Table.node 191 (Table.node 159 (Table.node 143 (Table.node 135 (Table.node 131 (Table.node 129 (Table.node 128 (Table.leaf (SupportEdge.mk 55 90 Bool.false)) (Table.leaf (SupportEdge.mk 55 110 Bool.false))) (Table.node 130 (Table.leaf (SupportEdge.mk 55 124 Bool.false)) (Table.leaf (SupportEdge.mk 55 125 Bool.false)))) (Table.node 133 (Table.node 132 (Table.leaf (SupportEdge.mk 190 225 Bool.false)) (Table.leaf (SupportEdge.mk 190 240 Bool.false))) (Table.node 134 (Table.leaf (SupportEdge.mk 190 249 Bool.true)) (Table.leaf (SupportEdge.mk 190 250 Bool.true))))) (Table.node 139 (Table.node 137 (Table.node 136 (Table.leaf (SupportEdge.mk 11 131 Bool.false)) (Table.leaf (SupportEdge.mk 11 141 Bool.false))) (Table.node 138 (Table.leaf (SupportEdge.mk 11 151 Bool.false)) (Table.leaf (SupportEdge.mk 11 152 Bool.false)))) (Table.node 141 (Table.node 140 (Table.leaf (SupportEdge.mk 14 134 Bool.false)) (Table.leaf (SupportEdge.mk 14 144 Bool.false))) (Table.node 142 (Table.leaf (SupportEdge.mk 14 155 Bool.true)) (Table.leaf (SupportEdge.mk 14 156 Bool.true)))))) (Table.node 151 (Table.node 147 (Table.node 145 (Table.node 144 (Table.leaf (SupportEdge.mk 17 137 Bool.false)) (Table.leaf (SupportEdge.mk 17 147 Bool.false))) (Table.node 146 (Table.leaf (SupportEdge.mk 17 158 Bool.true)) (Table.leaf (SupportEdge.mk 17 159 Bool.true)))) (Table.node 149 (Table.node 148 (Table.leaf (SupportEdge.mk 48 173 Bool.true)) (Table.leaf (SupportEdge.mk 48 183 Bool.true))) (Table.node 150 (Table.leaf (SupportEdge.mk 48 192 Bool.true)) (Table.leaf (SupportEdge.mk 48 193 Bool.true))))) (Table.node 155 (Table.node 153 (Table.node 152 (Table.leaf (SupportEdge.mk 83 208 Bool.true)) (Table.leaf (SupportEdge.mk 83 218 Bool.true))) (Table.node 154 (Table.leaf (SupportEdge.mk 83 227 Bool.true)) (Table.leaf (SupportEdge.mk 83 228 Bool.true)))) (Table.node 157 (Table.node 156 (Table.leaf (SupportEdge.mk 30 135 Bool.true)) (Table.leaf (SupportEdge.mk 30 165 Bool.false))) (Table.node 158 (Table.leaf (SupportEdge.mk 30 171 Bool.false)) (Table.leaf (SupportEdge.mk 30 178 Bool.false))))))) (Table.node 175 (Table.node 167 (Table.node 163 (Table.node 161 (Table.node 160 (Table.leaf (SupportEdge.mk 31 136 Bool.true)) (Table.leaf (SupportEdge.mk 31 166 Bool.false))) (Table.node 162 (Table.leaf (SupportEdge.mk 31 172 Bool.false)) (Table.leaf (SupportEdge.mk 31 179 Bool.false)))) (Table.node 165 (Table.node 164 (Table.leaf (SupportEdge.mk 33 138 Bool.true)) (Table.leaf (SupportEdge.mk 33 168 Bool.false))) (Table.node 166 (Table.leaf (SupportEdge.mk 33 174 Bool.false)) (Table.leaf (SupportEdge.mk 33 180 Bool.false))))) (Table.node 171 (Table.node 169 (Table.node 168 (Table.leaf (SupportEdge.mk 52 157 Bool.true)) (Table.leaf (SupportEdge.mk 52 187 Bool.true))) (Table.node 170 (Table.leaf (SupportEdge.mk 52 191 Bool.true)) (Table.leaf (SupportEdge.mk 52 195 Bool.false)))) (Table.node 173 (Table.node 172 (Table.leaf (SupportEdge.mk 107 212 Bool.false)) (Table.leaf (SupportEdge.mk 107 237 Bool.true))) (Table.node 174 (Table.leaf (SupportEdge.mk 107 241 Bool.true)) (Table.leaf (SupportEdge.mk 107 245 Bool.false)))))) (Table.node 183 (Table.node 179 (Table.node 177 (Table.node 176 (Table.leaf (SupportEdge.mk 52 157 Bool.true)) (Table.leaf (SupportEdge.mk 52 177 Bool.true))) (Table.node 178 (Table.leaf (SupportEdge.mk 52 187 Bool.true)) (Table.leaf (SupportEdge.mk 52 191 Bool.true)))) (Table.node 181 (Table.node 180 (Table.leaf (SupportEdge.mk 53 158 Bool.true)) (Table.leaf (SupportEdge.mk 53 178 Bool.true))) (Table.node 182 (Table.leaf (SupportEdge.mk 53 188 Bool.true)) (Table.leaf (SupportEdge.mk 53 192 Bool.true))))) (Table.node 187 (Table.node 185 (Table.node 184 (Table.leaf (SupportEdge.mk 54 159 Bool.true)) (Table.leaf (SupportEdge.mk 54 179 Bool.true))) (Table.node 186 (Table.leaf (SupportEdge.mk 54 189 Bool.true)) (Table.leaf (SupportEdge.mk 54 193 Bool.true)))) (Table.node 189 (Table.node 188 (Table.leaf (SupportEdge.mk 55 160 Bool.true)) (Table.leaf (SupportEdge.mk 55 180 Bool.true))) (Table.node 190 (Table.leaf (SupportEdge.mk 55 190 Bool.true)) (Table.leaf (SupportEdge.mk 55 194 Bool.true)))))))) (Table.node 223 (Table.node 207 (Table.node 199 (Table.node 195 (Table.node 193 (Table.node 192 (Table.leaf (SupportEdge.mk 125 230 Bool.false)) (Table.leaf (SupportEdge.mk 125 245 Bool.false))) (Table.node 194 (Table.leaf (SupportEdge.mk 125 250 Bool.false)) (Table.leaf (SupportEdge.mk 125 251 Bool.false)))) (Table.node 197 (Table.node 196 (Table.leaf (SupportEdge.mk 73 143 Bool.false)) (Table.leaf (SupportEdge.mk 73 198 Bool.true))) (Table.node 198 (Table.leaf (SupportEdge.mk 73 217 Bool.true)) (Table.leaf (SupportEdge.mk 73 219 Bool.true))))) (Table.node 203 (Table.node 201 (Table.node 200 (Table.leaf (SupportEdge.mk 74 144 Bool.false)) (Table.leaf (SupportEdge.mk 74 199 Bool.true))) (Table.node 202 (Table.leaf (SupportEdge.mk 74 218 Bool.true)) (Table.leaf (SupportEdge.mk 74 220 Bool.true)))) (Table.node 205 (Table.node 204 (Table.leaf (SupportEdge.mk 80 150 Bool.false)) (Table.leaf (SupportEdge.mk 80 205 Bool.true))) (Table.node 206 (Table.leaf (SupportEdge.mk 80 224 Bool.false)) (Table.leaf (SupportEdge.mk 80 225 Bool.false)))))) (Table.node 215 (Table.node 211 (Table.node 209 (Table.node 208 (Table.leaf (SupportEdge.mk 86 156 Bool.false)) (Table.leaf (SupportEdge.mk 86 211 Bool.true))) (Table.node 210 (Table.leaf (SupportEdge.mk 86 228 Bool.false)) (Table.leaf (SupportEdge.mk 86 229 Bool.false)))) (Table.node 213 (Table.node 212 (Table.leaf (SupportEdge.mk 116 186 Bool.false)) (Table.leaf (SupportEdge.mk 116 236 Bool.false))) (Table.node 214 (Table.leaf (SupportEdge.mk 116 248 Bool.false)) (Table.leaf (SupportEdge.mk 116 249 Bool.false))))) (Table.node 219 (Table.node 217 (Table.node 216 (Table.leaf (SupportEdge.mk 92 162 Bool.false)) (Table.leaf (SupportEdge.mk 92 197 Bool.false))) (Table.node 218 (Table.leaf (SupportEdge.mk 92 231 Bool.true)) (Table.leaf (SupportEdge.mk 92 235 Bool.false)))) (Table.node 221 (Table.node 220 (Table.leaf (SupportEdge.mk 93 163 Bool.false)) (Table.leaf (SupportEdge.mk 93 198 Bool.false))) (Table.node 222 (Table.leaf (SupportEdge.mk 93 232 Bool.true)) (Table.leaf (SupportEdge.mk 93 236 Bool.false))))))) (Table.node 239 (Table.node 231 (Table.node 227 (Table.node 225 (Table.node 224 (Table.leaf (SupportEdge.mk 98 168 Bool.false)) (Table.leaf (SupportEdge.mk 98 203 Bool.false))) (Table.node 226 (Table.leaf (SupportEdge.mk 98 237 Bool.false)) (Table.leaf (SupportEdge.mk 98 240 Bool.false)))) (Table.node 229 (Table.node 228 (Table.leaf (SupportEdge.mk 104 174 Bool.false)) (Table.leaf (SupportEdge.mk 104 209 Bool.false))) (Table.node 230 (Table.leaf (SupportEdge.mk 104 241 Bool.false)) (Table.leaf (SupportEdge.mk 104 244 Bool.false))))) (Table.node 235 (Table.node 233 (Table.node 232 (Table.leaf (SupportEdge.mk 114 184 Bool.false)) (Table.leaf (SupportEdge.mk 114 219 Bool.false))) (Table.node 234 (Table.leaf (SupportEdge.mk 114 246 Bool.false)) (Table.leaf (SupportEdge.mk 114 249 Bool.false)))) (Table.node 237 (Table.node 236 (Table.leaf (SupportEdge.mk 102 172 Bool.false)) (Table.leaf (SupportEdge.mk 102 207 Bool.false))) (Table.node 238 (Table.leaf (SupportEdge.mk 102 232 Bool.true)) (Table.leaf (SupportEdge.mk 102 241 Bool.true)))))) (Table.node 247 (Table.node 243 (Table.node 241 (Table.node 240 (Table.leaf (SupportEdge.mk 103 173 Bool.false)) (Table.leaf (SupportEdge.mk 103 208 Bool.false))) (Table.node 242 (Table.leaf (SupportEdge.mk 103 233 Bool.true)) (Table.leaf (SupportEdge.mk 103 242 Bool.true)))) (Table.node 245 (Table.node 244 (Table.leaf (SupportEdge.mk 106 176 Bool.false)) (Table.leaf (SupportEdge.mk 106 211 Bool.false))) (Table.node 246 (Table.leaf (SupportEdge.mk 106 236 Bool.true)) (Table.leaf (SupportEdge.mk 106 244 Bool.false))))) (Table.node 251 (Table.node 249 (Table.node 248 (Table.leaf (SupportEdge.mk 109 179 Bool.false)) (Table.leaf (SupportEdge.mk 109 214 Bool.false))) (Table.node 250 (Table.leaf (SupportEdge.mk 109 239 Bool.true)) (Table.leaf (SupportEdge.mk 109 245 Bool.false)))) (Table.node 253 (Table.node 252 (Table.leaf (SupportEdge.mk 123 193 Bool.false)) (Table.leaf (SupportEdge.mk 123 228 Bool.false))) (Table.node 254 (Table.leaf (SupportEdge.mk 123 248 Bool.false)) (Table.leaf (SupportEdge.mk 123 251 Bool.false))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 19 (Table.node 9 (Table.node 4 (Table.node 2 (Table.node 1 (Table.leaf 0) (Table.leaf 1)) (Table.node 3 (Table.leaf 2) (Table.leaf 6))) (Table.node 6 (Table.node 5 (Table.leaf 7) (Table.leaf 11)) (Table.node 7 (Table.leaf 19) (Table.node 8 (Table.leaf 21) (Table.leaf 22))))) (Table.node 14 (Table.node 11 (Table.node 10 (Table.leaf 23) (Table.leaf 24)) (Table.node 12 (Table.leaf 25) (Table.node 13 (Table.leaf 26) (Table.leaf 36)))) (Table.node 16 (Table.node 15 (Table.leaf 52) (Table.leaf 56)) (Table.node 17 (Table.leaf 57) (Table.node 18 (Table.leaf 61) (Table.leaf 71)))))) (Table.node 28 (Table.node 23 (Table.node 21 (Table.node 20 (Table.leaf 91) (Table.leaf 120)) (Table.node 22 (Table.leaf 126) (Table.leaf 127))) (Table.node 25 (Table.node 24 (Table.leaf 131) (Table.leaf 141)) (Table.node 26 (Table.leaf 151) (Table.node 27 (Table.leaf 152) (Table.leaf 153))))) (Table.node 33 (Table.node 30 (Table.node 29 (Table.leaf 157) (Table.leaf 161)) (Table.node 31 (Table.leaf 177) (Table.node 32 (Table.leaf 187) (Table.leaf 191)))) (Table.node 35 (Table.node 34 (Table.leaf 195) (Table.leaf 196)) (Table.node 36 (Table.leaf 221) (Table.node 37 (Table.leaf 234) (Table.leaf 243)))))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 255 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 38 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 → Eq ((Trace.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode4 : Eq (assignment 4) Sign.positive :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode5 : Eq (assignment 5) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode8 : Eq (assignment 8) Sign.positive :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode12 : Eq (assignment 12) Sign.positive :=
    Eq.trans (h_support 76 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode15 : Eq (assignment 15) Sign.positive :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode18 : Eq (assignment 18) Sign.negative :=
    Eq.trans (h_support 78 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode27 : Eq (assignment 27) Sign.negative :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode30 : Eq (assignment 30) Sign.negative :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode33 : Eq (assignment 33) Sign.positive :=
    Eq.trans (h_support 101 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode34 : Eq (assignment 34) Sign.positive :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode9 : Eq (assignment 9) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode10 : Eq (assignment 10) Sign.positive :=
    Eq.trans (h_support 79 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode13 : Eq (assignment 13) Sign.positive :=
    Eq.trans (h_support 4 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode14 : Eq (assignment 14) Sign.positive :=
    Eq.trans (h_support 80 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode16 : Eq (assignment 16) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode17 : Eq (assignment 17) Sign.positive :=
    Eq.trans (h_support 81 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode20 : Eq (assignment 20) Sign.positive :=
    Eq.trans (h_support 82 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode28 : Eq (assignment 28) Sign.negative :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode29 : Eq (assignment 29) Sign.negative :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode31 : Eq (assignment 31) Sign.negative :=
    Eq.trans (h_support 12 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode30)
  let hnode32 : Eq (assignment 32) Sign.negative :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode30)
  let hnode37 : Eq (assignment 37) Sign.negative :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode40 : Eq (assignment 40) Sign.negative :=
    Eq.trans (h_support 104 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode43 : Eq (assignment 43) Sign.positive :=
    Eq.trans (h_support 105 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode44 : Eq (assignment 44) Sign.positive :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode50 : Eq (assignment 50) Sign.positive :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode53 : Eq (assignment 53) Sign.positive :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode55 : Eq (assignment 55) Sign.negative :=
    Eq.trans (h_support 86 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode135 : Eq (assignment 135) Sign.positive :=
    Eq.trans (h_support 155 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode138 : Eq (assignment 138) Sign.negative :=
    Eq.trans (h_support 163 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode165 : Eq (assignment 165) Sign.negative :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode30)
  let hnode168 : Eq (assignment 168) Sign.positive :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode171 : Eq (assignment 171) Sign.negative :=
    Eq.trans (h_support 157 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode30)
  let hnode174 : Eq (assignment 174) Sign.positive :=
    Eq.trans (h_support 165 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode178 : Eq (assignment 178) Sign.negative :=
    Eq.trans (h_support 158 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode30)
  let hnode180 : Eq (assignment 180) Sign.positive :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode38 : Eq (assignment 38) Sign.negative :=
    Eq.trans (h_support 14 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode39 : Eq (assignment 39) Sign.negative :=
    Eq.trans (h_support 15 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode41 : Eq (assignment 41) Sign.negative :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode42 : Eq (assignment 42) Sign.negative :=
    Eq.trans (h_support 17 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode60 : Eq (assignment 60) Sign.negative :=
    Eq.trans (h_support 70 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode74 : Eq (assignment 74) Sign.positive :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode77 : Eq (assignment 77) Sign.positive :=
    Eq.trans (h_support 72 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode78 : Eq (assignment 78) Sign.positive :=
    Eq.trans (h_support 115 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode79 : Eq (assignment 79) Sign.positive :=
    Eq.trans (h_support 73 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode80 : Eq (assignment 80) Sign.positive :=
    Eq.trans (h_support 74 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode90 : Eq (assignment 90) Sign.negative :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode98 : Eq (assignment 98) Sign.positive :=
    Eq.trans (h_support 116 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode99 : Eq (assignment 99) Sign.positive :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode104 : Eq (assignment 104) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 227 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode174)
  let hnode110 : Eq (assignment 110) Sign.negative :=
    Eq.trans (h_support 128 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode114 : Eq (assignment 114) Sign.negative :=
    Eq.trans (h_support 117 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode115 : Eq (assignment 115) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode117 : Eq (assignment 117) Sign.negative :=
    Eq.trans (h_support 118 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode118 : Eq (assignment 118) Sign.negative :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode124 : Eq (assignment 124) Sign.negative :=
    Eq.trans (h_support 129 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode125 : Eq (assignment 125) Sign.negative :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode128 : Eq (assignment 128) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 112 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode165)
  let hnode134 : Eq (assignment 134) Sign.positive :=
    Eq.trans (h_support 139 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode136 : Eq (assignment 136) Sign.positive :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode31)
  let hnode137 : Eq (assignment 137) Sign.positive :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode144 : Eq (assignment 144) Sign.positive :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode147 : Eq (assignment 147) Sign.positive :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode155 : Eq (assignment 155) Sign.negative :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode156 : Eq (assignment 156) Sign.negative :=
    Eq.trans (h_support 142 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode158 : Eq (assignment 158) Sign.negative :=
    Eq.trans (h_support 145 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode159 : Eq (assignment 159) Sign.negative :=
    Eq.trans (h_support 146 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode160 : Eq (assignment 160) Sign.positive :=
    Eq.trans (h_support 187 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode55)
  let hnode166 : Eq (assignment 166) Sign.negative :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode167 : Eq (assignment 167) Sign.negative :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode165)
  let hnode172 : Eq (assignment 172) Sign.negative :=
    Eq.trans (h_support 161 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode173 : Eq (assignment 173) Sign.negative :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode171)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 162 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode188 : Eq (assignment 188) Sign.negative :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode190 : Eq (assignment 190) Sign.positive :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode55)
  let hnode192 : Eq (assignment 192) Sign.negative :=
    Eq.trans (h_support 182 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode194 : Eq (assignment 194) Sign.positive :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode55)
  let hnode45 : Eq (assignment 45) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 123 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode48 : Eq (assignment 48) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 147 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode173)
  let hnode54 : Eq (assignment 54) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 183 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode159)
  let hnode58 : Eq (assignment 58) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 21 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode60)
  let hnode69 : Eq (assignment 69) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 87 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode79)
  let hnode72 : Eq (assignment 72) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 27 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode74)
  let hnode75 : Eq (assignment 75) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 29 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode77)
  let hnode86 : Eq (assignment 86) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 207 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode156)
  let hnode102 : Eq (assignment 102) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 235 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode172)
  let hnode103 : Eq (assignment 103) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 239 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode173)
  let hnode109 : Eq (assignment 109) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 247 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode179)
  let hnode129 : Eq (assignment 129) Sign.negative :=
    Eq.trans (h_support 40 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode128)
  let hnode130 : Eq (assignment 130) Sign.negative :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode128)
  let hnode132 : Eq (assignment 132) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 43 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode134)
  let hnode139 : Eq (assignment 139) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 92 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode155)
  let hnode142 : Eq (assignment 142) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 47 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode144)
  let hnode145 : Eq (assignment 145) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 49 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode147)
  let hnode150 : Eq (assignment 150) Sign.positive :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode162 : Eq (assignment 162) Sign.negative :=
    Eq.trans (h_support 111 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode128)
  let hnode169 : Eq (assignment 169) Sign.positive :=
    Eq.trans (h_support 114 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode128)
  let hnode184 : Eq (assignment 184) Sign.negative :=
    Eq.trans (h_support 231 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode114)
  let hnode199 : Eq (assignment 199) Sign.negative :=
    Eq.trans (h_support 200 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode203 : Eq (assignment 203) Sign.positive :=
    Eq.trans (h_support 224 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode98)
  let hnode205 : Eq (assignment 205) Sign.negative :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode80)
  let hnode209 : Eq (assignment 209) Sign.positive :=
    Eq.trans (h_support 228 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode218 : Eq (assignment 218) Sign.negative :=
    Eq.trans (h_support 201 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode219 : Eq (assignment 219) Sign.negative :=
    Eq.trans (h_support 232 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode114)
  let hnode220 : Eq (assignment 220) Sign.negative :=
    Eq.trans (h_support 202 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode224 : Eq (assignment 224) Sign.positive :=
    Eq.trans (h_support 205 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode225 : Eq (assignment 225) Sign.positive :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode230 : Eq (assignment 230) Sign.negative :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode125)
  let hnode237 : Eq (assignment 237) Sign.positive :=
    Eq.trans (h_support 225 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode98)
  let hnode240 : Eq (assignment 240) Sign.positive :=
    Eq.trans (h_support 226 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode98)
  let hnode241 : Eq (assignment 241) Sign.positive :=
    Eq.trans (h_support 229 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 230 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode245 : Eq (assignment 245) Sign.negative :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode125)
  let hnode246 : Eq (assignment 246) Sign.negative :=
    Eq.trans (h_support 233 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode114)
  let hnode249 : Eq (assignment 249) Sign.negative :=
    Eq.trans (h_support 234 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode114)
  let hnode250 : Eq (assignment 250) Sign.negative :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode125)
  let hnode251 : Eq (assignment 251) Sign.negative :=
    Eq.trans (h_support 194 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode125)
  let hnode46 : Eq (assignment 46) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 19 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode59 : Eq (assignment 59) Sign.negative :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode73 : Eq (assignment 73) Sign.positive :=
    Eq.trans (h_support 26 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode72)
  let hnode76 : Eq (assignment 76) Sign.positive :=
    Eq.trans (h_support 28 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode75)
  let hnode83 : Eq (assignment 83) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 152 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode218)
  let hnode85 : Eq (assignment 85) Sign.positive :=
    Eq.trans (h_support 88 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode88 : Eq (assignment 88) Sign.positive :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode92 : Eq (assignment 92) Sign.negative :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode95 : Eq (assignment 95) Sign.negative :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode100 : Eq (assignment 100) Sign.positive :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode101 : Eq (assignment 101) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 36 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode102)
  let hnode106 : Eq (assignment 106) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 246 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode244)
  let hnode107 : Eq (assignment 107) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 172 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode237)
  let hnode116 : Eq (assignment 116) Sign.negative :=
    Eq.trans (h_support 125 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode119 : Eq (assignment 119) Sign.negative :=
    Eq.trans (h_support 126 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode123 : Eq (assignment 123) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 254 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode251)
  let hnode133 : Eq (assignment 133) Sign.positive :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode132)
  let hnode143 : Eq (assignment 143) Sign.positive :=
    Eq.trans (h_support 46 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode142)
  let hnode146 : Eq (assignment 146) Sign.positive :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode145)
  let hnode149 : Eq (assignment 149) Sign.negative :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode139)
  let hnode163 : Eq (assignment 163) Sign.negative :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode162)
  let hnode164 : Eq (assignment 164) Sign.negative :=
    Eq.trans (h_support 53 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode162)
  let hnode183 : Eq (assignment 183) Sign.negative :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode189 : Eq (assignment 189) Sign.negative :=
    Eq.trans (h_support 185 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode193 : Eq (assignment 193) Sign.negative :=
    Eq.trans (h_support 186 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode197 : Eq (assignment 197) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 61 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode199)
  let hnode207 : Eq (assignment 207) Sign.negative :=
    Eq.trans (h_support 236 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode102)
  let hnode208 : Eq (assignment 208) Sign.negative :=
    Eq.trans (h_support 240 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode103)
  let hnode211 : Eq (assignment 211) Sign.positive :=
    Eq.trans (h_support 208 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode86)
  let hnode214 : Eq (assignment 214) Sign.negative :=
    Eq.trans (h_support 248 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode109)
  let hnode216 : Eq (assignment 216) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 67 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode218)
  let hnode228 : Eq (assignment 228) Sign.negative :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode86)
  let hnode229 : Eq (assignment 229) Sign.negative :=
    Eq.trans (h_support 210 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode86)
  let hnode232 : Eq (assignment 232) Sign.positive :=
    Eq.trans (h_support 237 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode102)
  let hnode233 : Eq (assignment 233) Sign.positive :=
    Eq.trans (h_support 241 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode103)
  let hnode239 : Eq (assignment 239) Sign.positive :=
    Eq.trans (h_support 249 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode109)
  let hnode242 : Eq (assignment 242) Sign.positive :=
    Eq.trans (h_support 242 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode103)
  let hnode47 : Eq (assignment 47) Sign.positive :=
    Eq.trans (h_support 18 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode81 : Eq (assignment 81) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 31 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode83)
  let hnode93 : Eq (assignment 93) Sign.negative :=
    Eq.trans (h_support 32 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode94 : Eq (assignment 94) Sign.negative :=
    Eq.trans (h_support 33 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode96 : Eq (assignment 96) Sign.negative :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode97 : Eq (assignment 97) Sign.negative :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode176 : Eq (assignment 176) Sign.positive :=
    Eq.trans (h_support 243 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode106)
  let hnode181 : Eq (assignment 181) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 59 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode183)
  let hnode186 : Eq (assignment 186) Sign.negative :=
    Eq.trans (h_support 211 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode116)
  let hnode198 : Eq (assignment 198) Sign.negative :=
    Eq.trans (h_support 196 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode73)
  let hnode206 : Eq (assignment 206) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 64 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode207)
  let hnode212 : Eq (assignment 212) Sign.negative :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode107)
  let hnode217 : Eq (assignment 217) Sign.negative :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode73)
  let hnode227 : Eq (assignment 227) Sign.negative :=
    Eq.trans (h_support 153 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode231 : Eq (assignment 231) Sign.positive :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode92)
  let hnode235 : Eq (assignment 235) Sign.negative :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode236 : Eq (assignment 236) Sign.negative :=
    Eq.trans (h_support 212 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode116)
  let hnode248 : Eq (assignment 248) Sign.negative :=
    Eq.trans (h_support 213 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode116)
  let hnode82 : Eq (assignment 82) Sign.positive :=
    Eq.trans (h_support 30 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode81)
  let hnode182 : Eq (assignment 182) Sign.negative :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode181)
  let predicate : Nat → Prop := fun index => Eq ((Trace.initial index).allows
    (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (domain_from_eq (domain := Trace.initial 0) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded2 := below_succ bounded1 (domain_from_eq (domain := Trace.initial 1) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded3 := below_succ bounded2 (domain_from_eq (domain := Trace.initial 2) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded4 := below_succ bounded3 (domain_from_eq (domain := Trace.initial 3) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Trace.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Trace.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Trace.initial 6) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Trace.initial 7) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Trace.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Trace.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Trace.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (domain_from_eq (domain := Trace.initial 11) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded13 := below_succ bounded12 (domain_from_eq (domain := Trace.initial 12) (congrArg (Sign.withNegation globalNegation) hnode12) (Eq.refl Bool.true))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Trace.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Trace.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Trace.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Trace.initial 16) (congrArg (Sign.withNegation globalNegation) hnode16) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Trace.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (domain_from_eq (domain := Trace.initial 18) (congrArg (Sign.withNegation globalNegation) hnode18) (Eq.refl Bool.true))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Trace.initial 19) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Trace.initial 20) (congrArg (Sign.withNegation globalNegation) hnode20) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Trace.initial 21) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (domain_from_eq (domain := Trace.initial 22) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Trace.initial 23) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Trace.initial 24) (congrArg (Sign.withNegation globalNegation) (h_zero 10 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Trace.initial 25) (congrArg (Sign.withNegation globalNegation) (h_zero 11 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Trace.initial 26) (congrArg (Sign.withNegation globalNegation) (h_zero 12 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Trace.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Trace.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Trace.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (domain_from_eq (domain := Trace.initial 30) (congrArg (Sign.withNegation globalNegation) hnode30) (Eq.refl Bool.true))
  let bounded32 := below_succ bounded31 (domain_from_eq (domain := Trace.initial 31) (congrArg (Sign.withNegation globalNegation) hnode31) (Eq.refl Bool.true))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Trace.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Trace.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Trace.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (top_allows (Sign.withNegation globalNegation (assignment 35)))
  let bounded37 := below_succ bounded36 (domain_from_eq (domain := Trace.initial 36) (congrArg (Sign.withNegation globalNegation) (h_zero 13 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Trace.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Trace.initial 38) (congrArg (Sign.withNegation globalNegation) hnode38) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (domain_from_eq (domain := Trace.initial 39) (congrArg (Sign.withNegation globalNegation) hnode39) (Eq.refl Bool.true))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Trace.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Trace.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Trace.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (domain_from_eq (domain := Trace.initial 43) (congrArg (Sign.withNegation globalNegation) hnode43) (Eq.refl Bool.true))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Trace.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Trace.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (domain_from_eq (domain := Trace.initial 46) (congrArg (Sign.withNegation globalNegation) hnode46) (Eq.refl Bool.true))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Trace.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (domain_from_eq (domain := Trace.initial 48) (congrArg (Sign.withNegation globalNegation) hnode48) (Eq.refl Bool.true))
  let bounded50 := below_succ bounded49 (top_allows (Sign.withNegation globalNegation (assignment 49)))
  let bounded51 := below_succ bounded50 (domain_from_eq (domain := Trace.initial 50) (congrArg (Sign.withNegation globalNegation) hnode50) (Eq.refl Bool.true))
  let bounded52 := below_succ bounded51 (top_allows (Sign.withNegation globalNegation (assignment 51)))
  let bounded53 := below_succ bounded52 (domain_from_eq (domain := Trace.initial 52) (congrArg (Sign.withNegation globalNegation) (h_zero 14 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Trace.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Trace.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (domain_from_eq (domain := Trace.initial 55) (congrArg (Sign.withNegation globalNegation) hnode55) (Eq.refl Bool.true))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Trace.initial 56) (congrArg (Sign.withNegation globalNegation) (h_zero 15 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Trace.initial 57) (congrArg (Sign.withNegation globalNegation) (h_zero 16 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Trace.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Trace.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Trace.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Trace.initial 61) (congrArg (Sign.withNegation globalNegation) (h_zero 17 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (top_allows (Sign.withNegation globalNegation (assignment 62)))
  let bounded64 := below_succ bounded63 (top_allows (Sign.withNegation globalNegation (assignment 63)))
  let bounded65 := below_succ bounded64 (top_allows (Sign.withNegation globalNegation (assignment 64)))
  let bounded66 := below_succ bounded65 (top_allows (Sign.withNegation globalNegation (assignment 65)))
  let bounded67 := below_succ bounded66 (top_allows (Sign.withNegation globalNegation (assignment 66)))
  let bounded68 := below_succ bounded67 (top_allows (Sign.withNegation globalNegation (assignment 67)))
  let bounded69 := below_succ bounded68 (top_allows (Sign.withNegation globalNegation (assignment 68)))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Trace.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (top_allows (Sign.withNegation globalNegation (assignment 70)))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Trace.initial 71) (congrArg (Sign.withNegation globalNegation) (h_zero 18 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Trace.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Trace.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Trace.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Trace.initial 75) (congrArg (Sign.withNegation globalNegation) hnode75) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Trace.initial 76) (congrArg (Sign.withNegation globalNegation) hnode76) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Trace.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Trace.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Trace.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (domain_from_eq (domain := Trace.initial 80) (congrArg (Sign.withNegation globalNegation) hnode80) (Eq.refl Bool.true))
  let bounded82 := below_succ bounded81 (domain_from_eq (domain := Trace.initial 81) (congrArg (Sign.withNegation globalNegation) hnode81) (Eq.refl Bool.true))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Trace.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Trace.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (top_allows (Sign.withNegation globalNegation (assignment 84)))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Trace.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Trace.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (top_allows (Sign.withNegation globalNegation (assignment 87)))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Trace.initial 88) (congrArg (Sign.withNegation globalNegation) hnode88) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (top_allows (Sign.withNegation globalNegation (assignment 89)))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Trace.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Trace.initial 91) (congrArg (Sign.withNegation globalNegation) (h_zero 19 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Trace.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Trace.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Trace.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Trace.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Trace.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (domain_from_eq (domain := Trace.initial 97) (congrArg (Sign.withNegation globalNegation) hnode97) (Eq.refl Bool.true))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Trace.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Trace.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Trace.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Trace.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Trace.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Trace.initial 103) (congrArg (Sign.withNegation globalNegation) hnode103) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Trace.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (top_allows (Sign.withNegation globalNegation (assignment 105)))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Trace.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Trace.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (top_allows (Sign.withNegation globalNegation (assignment 108)))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Trace.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Trace.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (top_allows (Sign.withNegation globalNegation (assignment 111)))
  let bounded113 := below_succ bounded112 (top_allows (Sign.withNegation globalNegation (assignment 112)))
  let bounded114 := below_succ bounded113 (top_allows (Sign.withNegation globalNegation (assignment 113)))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Trace.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Trace.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Trace.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Trace.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Trace.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Trace.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Trace.initial 120) (congrArg (Sign.withNegation globalNegation) (h_zero 20 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (top_allows (Sign.withNegation globalNegation (assignment 121)))
  let bounded123 := below_succ bounded122 (top_allows (Sign.withNegation globalNegation (assignment 122)))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Trace.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Trace.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Trace.initial 125) (congrArg (Sign.withNegation globalNegation) hnode125) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (domain_from_eq (domain := Trace.initial 126) (congrArg (Sign.withNegation globalNegation) (h_zero 21 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded128 := below_succ bounded127 (domain_from_eq (domain := Trace.initial 127) (congrArg (Sign.withNegation globalNegation) (h_zero 22 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded129 := below_succ bounded128 (domain_from_eq (domain := Trace.initial 128) (congrArg (Sign.withNegation globalNegation) hnode128) (Eq.refl Bool.true))
  let bounded130 := below_succ bounded129 (domain_from_eq (domain := Trace.initial 129) (congrArg (Sign.withNegation globalNegation) hnode129) (Eq.refl Bool.true))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Trace.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Trace.initial 131) (congrArg (Sign.withNegation globalNegation) (h_zero 23 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Trace.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Trace.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Trace.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Trace.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Trace.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Trace.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Trace.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Trace.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (top_allows (Sign.withNegation globalNegation (assignment 140)))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Trace.initial 141) (congrArg (Sign.withNegation globalNegation) (h_zero 24 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Trace.initial 142) (congrArg (Sign.withNegation globalNegation) hnode142) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Trace.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Trace.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Trace.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Trace.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Trace.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (top_allows (Sign.withNegation globalNegation (assignment 148)))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Trace.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Trace.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Trace.initial 151) (congrArg (Sign.withNegation globalNegation) (h_zero 25 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Trace.initial 152) (congrArg (Sign.withNegation globalNegation) (h_zero 26 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Trace.initial 153) (congrArg (Sign.withNegation globalNegation) (h_zero 27 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (top_allows (Sign.withNegation globalNegation (assignment 154)))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Trace.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Trace.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Trace.initial 157) (congrArg (Sign.withNegation globalNegation) (h_zero 28 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Trace.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Trace.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Trace.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (domain_from_eq (domain := Trace.initial 161) (congrArg (Sign.withNegation globalNegation) (h_zero 29 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Trace.initial 162) (congrArg (Sign.withNegation globalNegation) hnode162) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Trace.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Trace.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Trace.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Trace.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Trace.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (domain_from_eq (domain := Trace.initial 168) (congrArg (Sign.withNegation globalNegation) hnode168) (Eq.refl Bool.true))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Trace.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (top_allows (Sign.withNegation globalNegation (assignment 170)))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Trace.initial 171) (congrArg (Sign.withNegation globalNegation) hnode171) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Trace.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Trace.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Trace.initial 174) (congrArg (Sign.withNegation globalNegation) hnode174) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (top_allows (Sign.withNegation globalNegation (assignment 175)))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Trace.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Trace.initial 177) (congrArg (Sign.withNegation globalNegation) (h_zero 30 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Trace.initial 178) (congrArg (Sign.withNegation globalNegation) hnode178) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Trace.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Trace.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Trace.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Trace.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Trace.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Trace.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (top_allows (Sign.withNegation globalNegation (assignment 185)))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Trace.initial 186) (congrArg (Sign.withNegation globalNegation) hnode186) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Trace.initial 187) (congrArg (Sign.withNegation globalNegation) (h_zero 31 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Trace.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Trace.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Trace.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Trace.initial 191) (congrArg (Sign.withNegation globalNegation) (h_zero 32 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Trace.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Trace.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Trace.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Trace.initial 195) (congrArg (Sign.withNegation globalNegation) (h_zero 33 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (domain_from_eq (domain := Trace.initial 196) (congrArg (Sign.withNegation globalNegation) (h_zero 34 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded198 := below_succ bounded197 (domain_from_eq (domain := Trace.initial 197) (congrArg (Sign.withNegation globalNegation) hnode197) (Eq.refl Bool.true))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Trace.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (domain_from_eq (domain := Trace.initial 199) (congrArg (Sign.withNegation globalNegation) hnode199) (Eq.refl Bool.true))
  let bounded201 := below_succ bounded200 (top_allows (Sign.withNegation globalNegation (assignment 200)))
  let bounded202 := below_succ bounded201 (top_allows (Sign.withNegation globalNegation (assignment 201)))
  let bounded203 := below_succ bounded202 (top_allows (Sign.withNegation globalNegation (assignment 202)))
  let bounded204 := below_succ bounded203 (domain_from_eq (domain := Trace.initial 203) (congrArg (Sign.withNegation globalNegation) hnode203) (Eq.refl Bool.true))
  let bounded205 := below_succ bounded204 (top_allows (Sign.withNegation globalNegation (assignment 204)))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Trace.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Trace.initial 206) (congrArg (Sign.withNegation globalNegation) hnode206) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Trace.initial 207) (congrArg (Sign.withNegation globalNegation) hnode207) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Trace.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Trace.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (top_allows (Sign.withNegation globalNegation (assignment 210)))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Trace.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Trace.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (top_allows (Sign.withNegation globalNegation (assignment 213)))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Trace.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (top_allows (Sign.withNegation globalNegation (assignment 215)))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Trace.initial 216) (congrArg (Sign.withNegation globalNegation) hnode216) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Trace.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Trace.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Trace.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Trace.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (domain_from_eq (domain := Trace.initial 221) (congrArg (Sign.withNegation globalNegation) (h_zero 35 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded223 := below_succ bounded222 (top_allows (Sign.withNegation globalNegation (assignment 222)))
  let bounded224 := below_succ bounded223 (top_allows (Sign.withNegation globalNegation (assignment 223)))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Trace.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Trace.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (top_allows (Sign.withNegation globalNegation (assignment 226)))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Trace.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Trace.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Trace.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Trace.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (domain_from_eq (domain := Trace.initial 231) (congrArg (Sign.withNegation globalNegation) hnode231) (Eq.refl Bool.true))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Trace.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (domain_from_eq (domain := Trace.initial 233) (congrArg (Sign.withNegation globalNegation) hnode233) (Eq.refl Bool.true))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Trace.initial 234) (congrArg (Sign.withNegation globalNegation) (h_zero 36 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Trace.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (domain_from_eq (domain := Trace.initial 236) (congrArg (Sign.withNegation globalNegation) hnode236) (Eq.refl Bool.true))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Trace.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (top_allows (Sign.withNegation globalNegation (assignment 238)))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Trace.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (domain_from_eq (domain := Trace.initial 240) (congrArg (Sign.withNegation globalNegation) hnode240) (Eq.refl Bool.true))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Trace.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Trace.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Trace.initial 243) (congrArg (Sign.withNegation globalNegation) (h_zero 37 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Trace.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Trace.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Trace.initial 246) (congrArg (Sign.withNegation globalNegation) hnode246) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (top_allows (Sign.withNegation globalNegation (assignment 247)))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Trace.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (domain_from_eq (domain := Trace.initial 249) (congrArg (Sign.withNegation globalNegation) hnode249) (Eq.refl Bool.true))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Trace.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Trace.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Trace.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.SevenSurvivor.Initializer
#print axioms Papers.RationalityTen.PureGP.SevenSurvivor.Initializer.support_sign_contradiction
