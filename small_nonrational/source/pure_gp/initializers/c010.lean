module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C010

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C010
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 3
def globalNegation : Bool := Bool.true
def edgeTable : Table SupportEdge := (Table.node 120 (Table.node 60 (Table.node 30 (Table.node 15 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 3 8 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 3 12 Bool.false)) (Table.leaf (SupportEdge.mk 3 15 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 3 18 Bool.true)) (Table.leaf (SupportEdge.mk 5 10 Bool.false))) (Table.node 6 (Table.leaf (SupportEdge.mk 5 14 Bool.false)) (Table.leaf (SupportEdge.mk 5 17 Bool.false))))) (Table.node 11 (Table.node 9 (Table.node 8 (Table.leaf (SupportEdge.mk 5 20 Bool.false)) (Table.leaf (SupportEdge.mk 34 44 Bool.false))) (Table.node 10 (Table.leaf (SupportEdge.mk 34 50 Bool.false)) (Table.leaf (SupportEdge.mk 34 53 Bool.false)))) (Table.node 13 (Table.node 12 (Table.leaf (SupportEdge.mk 34 55 Bool.true)) (Table.leaf (SupportEdge.mk 69 79 Bool.false))) (Table.node 14 (Table.leaf (SupportEdge.mk 69 85 Bool.false)) (Table.leaf (SupportEdge.mk 69 88 Bool.false)))))) (Table.node 22 (Table.node 18 (Table.node 16 (Table.leaf (SupportEdge.mk 69 90 Bool.true)) (Table.node 17 (Table.leaf (SupportEdge.mk 139 149 Bool.false)) (Table.leaf (SupportEdge.mk 139 155 Bool.false)))) (Table.node 20 (Table.node 19 (Table.leaf (SupportEdge.mk 139 158 Bool.false)) (Table.leaf (SupportEdge.mk 139 160 Bool.true))) (Table.node 21 (Table.leaf (SupportEdge.mk 4 24 Bool.true)) (Table.leaf (SupportEdge.mk 4 28 Bool.true))))) (Table.node 26 (Table.node 24 (Table.node 23 (Table.leaf (SupportEdge.mk 4 31 Bool.true)) (Table.leaf (SupportEdge.mk 4 33 Bool.true))) (Table.node 25 (Table.leaf (SupportEdge.mk 5 25 Bool.true)) (Table.leaf (SupportEdge.mk 5 29 Bool.true)))) (Table.node 28 (Table.node 27 (Table.leaf (SupportEdge.mk 5 32 Bool.true)) (Table.leaf (SupportEdge.mk 5 34 Bool.true))) (Table.node 29 (Table.leaf (SupportEdge.mk 20 45 Bool.false)) (Table.leaf (SupportEdge.mk 20 51 Bool.false))))))) (Table.node 45 (Table.node 37 (Table.node 33 (Table.node 31 (Table.leaf (SupportEdge.mk 20 54 Bool.false)) (Table.node 32 (Table.leaf (SupportEdge.mk 20 55 Bool.false)) (Table.leaf (SupportEdge.mk 70 100 Bool.true)))) (Table.node 35 (Table.node 34 (Table.leaf (SupportEdge.mk 70 106 Bool.true)) (Table.leaf (SupportEdge.mk 70 109 Bool.true))) (Table.node 36 (Table.leaf (SupportEdge.mk 70 110 Bool.true)) (Table.leaf (SupportEdge.mk 140 170 Bool.true))))) (Table.node 41 (Table.node 39 (Table.node 38 (Table.leaf (SupportEdge.mk 140 176 Bool.true)) (Table.leaf (SupportEdge.mk 140 179 Bool.true))) (Table.node 40 (Table.leaf (SupportEdge.mk 140 180 Bool.true)) (Table.leaf (SupportEdge.mk 6 21 Bool.false)))) (Table.node 43 (Table.node 42 (Table.leaf (SupportEdge.mk 6 36 Bool.false)) (Table.leaf (SupportEdge.mk 6 38 Bool.false))) (Table.node 44 (Table.leaf (SupportEdge.mk 6 39 Bool.false)) (Table.leaf (SupportEdge.mk 8 23 Bool.false)))))) (Table.node 52 (Table.node 48 (Table.node 46 (Table.leaf (SupportEdge.mk 8 40 Bool.true)) (Table.node 47 (Table.leaf (SupportEdge.mk 8 43 Bool.false)) (Table.leaf (SupportEdge.mk 8 44 Bool.false)))) (Table.node 50 (Table.node 49 (Table.leaf (SupportEdge.mk 12 27 Bool.false)) (Table.leaf (SupportEdge.mk 12 46 Bool.true))) (Table.node 51 (Table.leaf (SupportEdge.mk 12 49 Bool.false)) (Table.leaf (SupportEdge.mk 12 50 Bool.false))))) (Table.node 56 (Table.node 54 (Table.node 53 (Table.leaf (SupportEdge.mk 72 92 Bool.false)) (Table.leaf (SupportEdge.mk 72 111 Bool.false))) (Table.node 55 (Table.leaf (SupportEdge.mk 72 114 Bool.true)) (Table.leaf (SupportEdge.mk 72 115 Bool.true)))) (Table.node 58 (Table.node 57 (Table.leaf (SupportEdge.mk 142 162 Bool.false)) (Table.leaf (SupportEdge.mk 142 181 Bool.false))) (Table.node 59 (Table.leaf (SupportEdge.mk 142 184 Bool.true)) (Table.leaf (SupportEdge.mk 142 185 Bool.true)))))))) (Table.node 90 (Table.node 75 (Table.node 67 (Table.node 63 (Table.node 61 (Table.leaf (SupportEdge.mk 6 21 Bool.false)) (Table.node 62 (Table.leaf (SupportEdge.mk 6 36 Bool.false)) (Table.leaf (SupportEdge.mk 6 37 Bool.false)))) (Table.node 65 (Table.node 64 (Table.leaf (SupportEdge.mk 6 39 Bool.false)) (Table.leaf (SupportEdge.mk 9 24 Bool.false))) (Table.node 66 (Table.leaf (SupportEdge.mk 9 41 Bool.true)) (Table.leaf (SupportEdge.mk 9 43 Bool.true))))) (Table.node 71 (Table.node 69 (Table.node 68 (Table.leaf (SupportEdge.mk 9 45 Bool.false)) (Table.leaf (SupportEdge.mk 13 28 Bool.false))) (Table.node 70 (Table.leaf (SupportEdge.mk 13 47 Bool.true)) (Table.leaf (SupportEdge.mk 13 49 Bool.true)))) (Table.node 73 (Table.node 72 (Table.leaf (SupportEdge.mk 13 51 Bool.false)) (Table.leaf (SupportEdge.mk 73 93 Bool.false))) (Table.node 74 (Table.leaf (SupportEdge.mk 73 112 Bool.false)) (Table.leaf (SupportEdge.mk 73 114 Bool.false)))))) (Table.node 82 (Table.node 78 (Table.node 76 (Table.leaf (SupportEdge.mk 73 116 Bool.true)) (Table.node 77 (Table.leaf (SupportEdge.mk 143 163 Bool.false)) (Table.leaf (SupportEdge.mk 143 182 Bool.false)))) (Table.node 80 (Table.node 79 (Table.leaf (SupportEdge.mk 143 184 Bool.false)) (Table.leaf (SupportEdge.mk 143 186 Bool.true))) (Table.node 81 (Table.leaf (SupportEdge.mk 7 57 Bool.true)) (Table.leaf (SupportEdge.mk 7 71 Bool.false))))) (Table.node 86 (Table.node 84 (Table.node 83 (Table.leaf (SupportEdge.mk 7 76 Bool.true)) (Table.leaf (SupportEdge.mk 7 77 Bool.true))) (Table.node 85 (Table.leaf (SupportEdge.mk 8 58 Bool.true)) (Table.leaf (SupportEdge.mk 8 72 Bool.false)))) (Table.node 88 (Table.node 87 (Table.leaf (SupportEdge.mk 8 78 Bool.true)) (Table.leaf (SupportEdge.mk 8 79 Bool.true))) (Table.node 89 (Table.leaf (SupportEdge.mk 15 65 Bool.true)) (Table.leaf (SupportEdge.mk 15 81 Bool.true))))))) (Table.node 105 (Table.node 97 (Table.node 93 (Table.node 91 (Table.leaf (SupportEdge.mk 15 87 Bool.true)) (Table.node 92 (Table.leaf (SupportEdge.mk 15 88 Bool.true)) (Table.leaf (SupportEdge.mk 40 95 Bool.false)))) (Table.node 95 (Table.node 94 (Table.leaf (SupportEdge.mk 40 111 Bool.true)) (Table.leaf (SupportEdge.mk 40 117 Bool.true))) (Table.node 96 (Table.leaf (SupportEdge.mk 40 118 Bool.true)) (Table.leaf (SupportEdge.mk 145 200 Bool.true))))) (Table.node 101 (Table.node 99 (Table.node 98 (Table.leaf (SupportEdge.mk 145 216 Bool.false)) (Table.leaf (SupportEdge.mk 145 222 Bool.false))) (Table.node 100 (Table.leaf (SupportEdge.mk 145 223 Bool.false)) (Table.leaf (SupportEdge.mk 9 59 Bool.true)))) (Table.node 103 (Table.node 102 (Table.leaf (SupportEdge.mk 9 73 Bool.false)) (Table.leaf (SupportEdge.mk 9 76 Bool.false))) (Table.node 104 (Table.leaf (SupportEdge.mk 9 78 Bool.false)) (Table.leaf (SupportEdge.mk 10 60 Bool.true)))))) (Table.node 112 (Table.node 108 (Table.node 106 (Table.leaf (SupportEdge.mk 10 74 Bool.false)) (Table.node 107 (Table.leaf (SupportEdge.mk 10 77 Bool.false)) (Table.leaf (SupportEdge.mk 10 79 Bool.false)))) (Table.node 110 (Table.node 109 (Table.leaf (SupportEdge.mk 20 70 Bool.true)) (Table.leaf (SupportEdge.mk 20 86 Bool.true))) (Table.node 111 (Table.leaf (SupportEdge.mk 20 89 Bool.true)) (Table.leaf (SupportEdge.mk 20 90 Bool.true))))) (Table.node 116 (Table.node 114 (Table.node 113 (Table.leaf (SupportEdge.mk 45 100 Bool.false)) (Table.leaf (SupportEdge.mk 45 116 Bool.true))) (Table.node 115 (Table.leaf (SupportEdge.mk 45 119 Bool.true)) (Table.leaf (SupportEdge.mk 45 120 Bool.true)))) (Table.node 118 (Table.node 117 (Table.leaf (SupportEdge.mk 150 205 Bool.true)) (Table.leaf (SupportEdge.mk 150 221 Bool.false))) (Table.node 119 (Table.leaf (SupportEdge.mk 150 224 Bool.false)) (Table.leaf (SupportEdge.mk 150 225 Bool.false))))))))) (Table.node 180 (Table.node 150 (Table.node 135 (Table.node 127 (Table.node 123 (Table.node 121 (Table.leaf (SupportEdge.mk 26 131 Bool.true)) (Table.node 122 (Table.leaf (SupportEdge.mk 26 161 Bool.false)) (Table.leaf (SupportEdge.mk 26 171 Bool.false)))) (Table.node 125 (Table.node 124 (Table.leaf (SupportEdge.mk 26 173 Bool.false)) (Table.leaf (SupportEdge.mk 28 133 Bool.true))) (Table.node 126 (Table.leaf (SupportEdge.mk 28 163 Bool.false)) (Table.leaf (SupportEdge.mk 28 174 Bool.true))))) (Table.node 131 (Table.node 129 (Table.node 128 (Table.leaf (SupportEdge.mk 28 176 Bool.false)) (Table.leaf (SupportEdge.mk 31 136 Bool.true))) (Table.node 130 (Table.leaf (SupportEdge.mk 31 166 Bool.false)) (Table.leaf (SupportEdge.mk 31 177 Bool.true)))) (Table.node 133 (Table.node 132 (Table.leaf (SupportEdge.mk 31 179 Bool.false)) (Table.leaf (SupportEdge.mk 47 152 Bool.true))) (Table.node 134 (Table.leaf (SupportEdge.mk 47 182 Bool.true)) (Table.leaf (SupportEdge.mk 47 191 Bool.true)))))) (Table.node 142 (Table.node 138 (Table.node 136 (Table.leaf (SupportEdge.mk 47 193 Bool.false)) (Table.node 137 (Table.leaf (SupportEdge.mk 102 207 Bool.false)) (Table.leaf (SupportEdge.mk 102 232 Bool.true)))) (Table.node 140 (Table.node 139 (Table.leaf (SupportEdge.mk 102 241 Bool.true)) (Table.leaf (SupportEdge.mk 102 243 Bool.false))) (Table.node 141 (Table.leaf (SupportEdge.mk 27 132 Bool.true)) (Table.leaf (SupportEdge.mk 27 162 Bool.false))))) (Table.node 146 (Table.node 144 (Table.node 143 (Table.leaf (SupportEdge.mk 27 171 Bool.true)) (Table.leaf (SupportEdge.mk 27 174 Bool.false))) (Table.node 145 (Table.leaf (SupportEdge.mk 29 134 Bool.true)) (Table.leaf (SupportEdge.mk 29 164 Bool.false)))) (Table.node 148 (Table.node 147 (Table.leaf (SupportEdge.mk 29 173 Bool.true)) (Table.leaf (SupportEdge.mk 29 176 Bool.true))) (Table.node 149 (Table.leaf (SupportEdge.mk 34 139 Bool.true)) (Table.leaf (SupportEdge.mk 34 169 Bool.false))))))) (Table.node 165 (Table.node 157 (Table.node 153 (Table.node 151 (Table.leaf (SupportEdge.mk 34 178 Bool.false)) (Table.node 152 (Table.leaf (SupportEdge.mk 34 180 Bool.true)) (Table.leaf (SupportEdge.mk 50 155 Bool.true)))) (Table.node 155 (Table.node 154 (Table.leaf (SupportEdge.mk 50 185 Bool.true)) (Table.leaf (SupportEdge.mk 50 192 Bool.false))) (Table.node 156 (Table.leaf (SupportEdge.mk 50 194 Bool.true)) (Table.leaf (SupportEdge.mk 105 210 Bool.false))))) (Table.node 161 (Table.node 159 (Table.node 158 (Table.leaf (SupportEdge.mk 105 235 Bool.true)) (Table.leaf (SupportEdge.mk 105 242 Bool.false))) (Table.node 160 (Table.leaf (SupportEdge.mk 105 244 Bool.true)) (Table.leaf (SupportEdge.mk 65 135 Bool.false)))) (Table.node 163 (Table.node 162 (Table.leaf (SupportEdge.mk 65 200 Bool.false)) (Table.leaf (SupportEdge.mk 65 206 Bool.false))) (Table.node 164 (Table.leaf (SupportEdge.mk 65 212 Bool.false)) (Table.leaf (SupportEdge.mk 67 137 Bool.false)))))) (Table.node 172 (Table.node 168 (Table.node 166 (Table.leaf (SupportEdge.mk 67 202 Bool.false)) (Table.node 167 (Table.leaf (SupportEdge.mk 67 208 Bool.false)) (Table.leaf (SupportEdge.mk 67 214 Bool.true)))) (Table.node 170 (Table.node 169 (Table.leaf (SupportEdge.mk 69 139 Bool.false)) (Table.leaf (SupportEdge.mk 69 204 Bool.false))) (Table.node 171 (Table.leaf (SupportEdge.mk 69 210 Bool.false)) (Table.leaf (SupportEdge.mk 69 215 Bool.true))))) (Table.node 176 (Table.node 174 (Table.node 173 (Table.leaf (SupportEdge.mk 88 158 Bool.false)) (Table.leaf (SupportEdge.mk 88 223 Bool.true))) (Table.node 175 (Table.leaf (SupportEdge.mk 88 227 Bool.true)) (Table.leaf (SupportEdge.mk 88 230 Bool.true)))) (Table.node 178 (Table.node 177 (Table.leaf (SupportEdge.mk 108 178 Bool.false)) (Table.leaf (SupportEdge.mk 108 238 Bool.true))) (Table.node 179 (Table.leaf (SupportEdge.mk 108 242 Bool.true)) (Table.leaf (SupportEdge.mk 108 245 Bool.true)))))))) (Table.node 210 (Table.node 195 (Table.node 187 (Table.node 183 (Table.node 181 (Table.leaf (SupportEdge.mk 66 136 Bool.false)) (Table.node 182 (Table.leaf (SupportEdge.mk 66 201 Bool.false)) (Table.leaf (SupportEdge.mk 66 207 Bool.false)))) (Table.node 185 (Table.node 184 (Table.leaf (SupportEdge.mk 66 212 Bool.true)) (Table.leaf (SupportEdge.mk 67 137 Bool.false))) (Table.node 186 (Table.leaf (SupportEdge.mk 67 202 Bool.false)) (Table.leaf (SupportEdge.mk 67 208 Bool.false))))) (Table.node 191 (Table.node 189 (Table.node 188 (Table.leaf (SupportEdge.mk 67 213 Bool.true)) (Table.leaf (SupportEdge.mk 70 140 Bool.false))) (Table.node 190 (Table.leaf (SupportEdge.mk 70 205 Bool.false)) (Table.leaf (SupportEdge.mk 70 211 Bool.false)))) (Table.node 193 (Table.node 192 (Table.leaf (SupportEdge.mk 70 215 Bool.false)) (Table.leaf (SupportEdge.mk 89 159 Bool.false))) (Table.node 194 (Table.leaf (SupportEdge.mk 89 224 Bool.true)) (Table.leaf (SupportEdge.mk 89 228 Bool.true)))))) (Table.node 202 (Table.node 198 (Table.node 196 (Table.leaf (SupportEdge.mk 89 230 Bool.false)) (Table.node 197 (Table.leaf (SupportEdge.mk 109 179 Bool.false)) (Table.leaf (SupportEdge.mk 109 239 Bool.true)))) (Table.node 200 (Table.node 199 (Table.leaf (SupportEdge.mk 109 243 Bool.true)) (Table.leaf (SupportEdge.mk 109 245 Bool.false))) (Table.node 201 (Table.leaf (SupportEdge.mk 71 141 Bool.false)) (Table.leaf (SupportEdge.mk 71 196 Bool.true))))) (Table.node 206 (Table.node 204 (Table.node 203 (Table.leaf (SupportEdge.mk 71 216 Bool.false)) (Table.leaf (SupportEdge.mk 71 218 Bool.false))) (Table.node 205 (Table.leaf (SupportEdge.mk 73 143 Bool.false)) (Table.leaf (SupportEdge.mk 73 198 Bool.true)))) (Table.node 208 (Table.node 207 (Table.leaf (SupportEdge.mk 73 219 Bool.true)) (Table.leaf (SupportEdge.mk 73 221 Bool.false))) (Table.node 209 (Table.leaf (SupportEdge.mk 76 146 Bool.false)) (Table.leaf (SupportEdge.mk 76 201 Bool.true))))))) (Table.node 225 (Table.node 217 (Table.node 213 (Table.node 211 (Table.leaf (SupportEdge.mk 76 222 Bool.true)) (Table.node 212 (Table.leaf (SupportEdge.mk 76 224 Bool.false)) (Table.leaf (SupportEdge.mk 82 152 Bool.false)))) (Table.node 215 (Table.node 214 (Table.leaf (SupportEdge.mk 82 207 Bool.true)) (Table.leaf (SupportEdge.mk 82 226 Bool.true))) (Table.node 216 (Table.leaf (SupportEdge.mk 82 228 Bool.false)) (Table.leaf (SupportEdge.mk 112 182 Bool.false))))) (Table.node 221 (Table.node 219 (Table.node 218 (Table.leaf (SupportEdge.mk 112 232 Bool.false)) (Table.leaf (SupportEdge.mk 112 246 Bool.true))) (Table.node 220 (Table.leaf (SupportEdge.mk 112 248 Bool.false)) (Table.leaf (SupportEdge.mk 91 161 Bool.false)))) (Table.node 223 (Table.node 222 (Table.leaf (SupportEdge.mk 91 196 Bool.false)) (Table.leaf (SupportEdge.mk 91 232 Bool.false))) (Table.node 224 (Table.leaf (SupportEdge.mk 91 233 Bool.false)) (Table.leaf (SupportEdge.mk 92 162 Bool.false)))))) (Table.node 232 (Table.node 228 (Table.node 226 (Table.leaf (SupportEdge.mk 92 197 Bool.false)) (Table.node 227 (Table.leaf (SupportEdge.mk 92 234 Bool.false)) (Table.leaf (SupportEdge.mk 92 235 Bool.false)))) (Table.node 230 (Table.node 229 (Table.leaf (SupportEdge.mk 95 165 Bool.false)) (Table.leaf (SupportEdge.mk 95 200 Bool.false))) (Table.node 231 (Table.leaf (SupportEdge.mk 95 237 Bool.false)) (Table.leaf (SupportEdge.mk 95 238 Bool.false))))) (Table.node 236 (Table.node 234 (Table.node 233 (Table.leaf (SupportEdge.mk 101 171 Bool.false)) (Table.leaf (SupportEdge.mk 101 206 Bool.false))) (Table.node 235 (Table.leaf (SupportEdge.mk 101 241 Bool.false)) (Table.leaf (SupportEdge.mk 101 242 Bool.false)))) (Table.node 238 (Table.node 237 (Table.leaf (SupportEdge.mk 111 181 Bool.false)) (Table.leaf (SupportEdge.mk 111 216 Bool.false))) (Table.node 239 (Table.leaf (SupportEdge.mk 111 246 Bool.false)) (Table.leaf (SupportEdge.mk 111 247 Bool.false))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 10 (Table.node 5 (Table.node 2 (Table.node 1 (Table.leaf 6) (Table.leaf 19)) (Table.node 3 (Table.leaf 21) (Table.node 4 (Table.leaf 35) (Table.leaf 36)))) (Table.node 7 (Table.node 6 (Table.leaf 37) (Table.leaf 38)) (Table.node 8 (Table.leaf 39) (Table.node 9 (Table.leaf 67) (Table.leaf 75))))) (Table.node 15 (Table.node 12 (Table.node 11 (Table.leaf 80) (Table.leaf 137)) (Table.node 13 (Table.leaf 172) (Table.node 14 (Table.leaf 175) (Table.leaf 202)))) (Table.node 17 (Table.node 16 (Table.leaf 208) (Table.leaf 213)) (Table.node 18 (Table.leaf 214) (Table.node 19 (Table.leaf 217) (Table.leaf 231))))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 240 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 20 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C010.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode8 : Eq (assignment 8) Sign.positive :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode12 : Eq (assignment 12) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode15 : Eq (assignment 15) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode18 : Eq (assignment 18) Sign.negative :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode23 : Eq (assignment 23) Sign.positive :=
    Eq.trans (h_support 44 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode27 : Eq (assignment 27) Sign.positive :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode40 : Eq (assignment 40) Sign.negative :=
    Eq.trans (h_support 45 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode43 : Eq (assignment 43) Sign.positive :=
    Eq.trans (h_support 46 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode44 : Eq (assignment 44) Sign.positive :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode46 : Eq (assignment 46) Sign.negative :=
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode12)
  let hnode49 : Eq (assignment 49) Sign.positive :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode50 : Eq (assignment 50) Sign.positive :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode58 : Eq (assignment 58) Sign.negative :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode65 : Eq (assignment 65) Sign.negative :=
    Eq.trans (h_support 88 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode15)
  let hnode72 : Eq (assignment 72) Sign.positive :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode78 : Eq (assignment 78) Sign.negative :=
    Eq.trans (h_support 86 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode79 : Eq (assignment 79) Sign.negative :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode81 : Eq (assignment 81) Sign.negative :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode15)
  let hnode87 : Eq (assignment 87) Sign.negative :=
    Eq.trans (h_support 90 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode15)
  let hnode88 : Eq (assignment 88) Sign.negative :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode15)
  let hnode9 : Eq (assignment 9) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 66 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode10 : Eq (assignment 10) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 107 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode79)
  let hnode13 : Eq (assignment 13) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 70 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode49)
  let hnode34 : Eq (assignment 34) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 8 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode69 : Eq (assignment 69) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 12 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode79)
  let hnode92 : Eq (assignment 92) Sign.positive :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode72)
  let hnode95 : Eq (assignment 95) Sign.negative :=
    Eq.trans (h_support 92 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode111 : Eq (assignment 111) Sign.positive :=
    Eq.trans (h_support 93 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode114 : Eq (assignment 114) Sign.negative :=
    Eq.trans (h_support 54 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode72)
  let hnode115 : Eq (assignment 115) Sign.negative :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode72)
  let hnode117 : Eq (assignment 117) Sign.positive :=
    Eq.trans (h_support 94 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode118 : Eq (assignment 118) Sign.positive :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode132 : Eq (assignment 132) Sign.negative :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode135 : Eq (assignment 135) Sign.negative :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode65)
  let hnode155 : Eq (assignment 155) Sign.negative :=
    Eq.trans (h_support 152 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode50)
  let hnode158 : Eq (assignment 158) Sign.negative :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode88)
  let hnode162 : Eq (assignment 162) Sign.positive :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode171 : Eq (assignment 171) Sign.negative :=
    Eq.trans (h_support 142 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode174 : Eq (assignment 174) Sign.positive :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode185 : Eq (assignment 185) Sign.negative :=
    Eq.trans (h_support 153 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode50)
  let hnode192 : Eq (assignment 192) Sign.positive :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode50)
  let hnode194 : Eq (assignment 194) Sign.negative :=
    Eq.trans (h_support 155 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode50)
  let hnode200 : Eq (assignment 200) Sign.negative :=
    Eq.trans (h_support 161 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode65)
  let hnode206 : Eq (assignment 206) Sign.negative :=
    Eq.trans (h_support 162 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode65)
  let hnode212 : Eq (assignment 212) Sign.negative :=
    Eq.trans (h_support 163 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode65)
  let hnode223 : Eq (assignment 223) Sign.positive :=
    Eq.trans (h_support 173 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode227 : Eq (assignment 227) Sign.positive :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode230 : Eq (assignment 230) Sign.positive :=
    Eq.trans (h_support 175 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode5 : Eq (assignment 5) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 27 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode24 : Eq (assignment 24) Sign.negative :=
    Eq.trans (h_support 64 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode26 : Eq (assignment 26) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 122 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode171)
  let hnode28 : Eq (assignment 28) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 126 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode174)
  let hnode41 : Eq (assignment 41) Sign.positive :=
    Eq.trans (h_support 65 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode45 : Eq (assignment 45) Sign.negative :=
    Eq.trans (h_support 67 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode47 : Eq (assignment 47) Sign.positive :=
    Eq.trans (h_support 69 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode51 : Eq (assignment 51) Sign.negative :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode53 : Eq (assignment 53) Sign.positive :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode55 : Eq (assignment 55) Sign.negative :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode59 : Eq (assignment 59) Sign.positive :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode60 : Eq (assignment 60) Sign.positive :=
    Eq.trans (h_support 104 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode66 : Eq (assignment 66) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 183 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode212)
  let hnode73 : Eq (assignment 73) Sign.negative :=
    Eq.trans (h_support 101 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode74 : Eq (assignment 74) Sign.negative :=
    Eq.trans (h_support 105 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode76 : Eq (assignment 76) Sign.negative :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode77 : Eq (assignment 77) Sign.negative :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode85 : Eq (assignment 85) Sign.negative :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode89 : Eq (assignment 89) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 195 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode230)
  let hnode90 : Eq (assignment 90) Sign.positive :=
    Eq.trans (h_support 15 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode69)
  let hnode101 : Eq (assignment 101) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 232 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode171)
  let hnode139 : Eq (assignment 139) Sign.negative :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode142 : Eq (assignment 142) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 56 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode162)
  let hnode145 : Eq (assignment 145) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 96 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode200)
  let hnode165 : Eq (assignment 165) Sign.negative :=
    Eq.trans (h_support 228 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode169 : Eq (assignment 169) Sign.positive :=
    Eq.trans (h_support 149 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode178 : Eq (assignment 178) Sign.positive :=
    Eq.trans (h_support 150 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode180 : Eq (assignment 180) Sign.negative :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode181 : Eq (assignment 181) Sign.positive :=
    Eq.trans (h_support 236 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode197 : Eq (assignment 197) Sign.positive :=
    Eq.trans (h_support 225 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode204 : Eq (assignment 204) Sign.negative :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode210 : Eq (assignment 210) Sign.negative :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode215 : Eq (assignment 215) Sign.positive :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode69)
  let hnode216 : Eq (assignment 216) Sign.positive :=
    Eq.trans (h_support 237 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode234 : Eq (assignment 234) Sign.positive :=
    Eq.trans (h_support 226 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode235 : Eq (assignment 235) Sign.positive :=
    Eq.trans (h_support 227 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode237 : Eq (assignment 237) Sign.negative :=
    Eq.trans (h_support 230 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode238 : Eq (assignment 238) Sign.negative :=
    Eq.trans (h_support 231 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode246 : Eq (assignment 246) Sign.positive :=
    Eq.trans (h_support 238 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode247 : Eq (assignment 247) Sign.positive :=
    Eq.trans (h_support 239 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode4 : Eq (assignment 4) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 20 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode7 : Eq (assignment 7) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 82 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode76)
  let hnode14 : Eq (assignment 14) Sign.negative :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode17 : Eq (assignment 17) Sign.negative :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode20 : Eq (assignment 20) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 28 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode25 : Eq (assignment 25) Sign.positive :=
    Eq.trans (h_support 24 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode29 : Eq (assignment 29) Sign.positive :=
    Eq.trans (h_support 25 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode32 : Eq (assignment 32) Sign.positive :=
    Eq.trans (h_support 26 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode70 : Eq (assignment 70) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 191 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode215)
  let hnode71 : Eq (assignment 71) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 202 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode216)
  let hnode93 : Eq (assignment 93) Sign.negative :=
    Eq.trans (h_support 72 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode73)
  let hnode100 : Eq (assignment 100) Sign.negative :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode105 : Eq (assignment 105) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 157 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode235)
  let hnode108 : Eq (assignment 108) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 177 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode238)
  let hnode112 : Eq (assignment 112) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 218 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode246)
  let hnode116 : Eq (assignment 116) Sign.positive :=
    Eq.trans (h_support 113 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode119 : Eq (assignment 119) Sign.positive :=
    Eq.trans (h_support 114 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode120 : Eq (assignment 120) Sign.positive :=
    Eq.trans (h_support 115 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode131 : Eq (assignment 131) Sign.positive :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode133 : Eq (assignment 133) Sign.positive :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode136 : Eq (assignment 136) Sign.positive :=
    Eq.trans (h_support 180 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode140 : Eq (assignment 140) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 39 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode180)
  let hnode143 : Eq (assignment 143) Sign.negative :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode73)
  let hnode146 : Eq (assignment 146) Sign.negative :=
    Eq.trans (h_support 208 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode76)
  let hnode149 : Eq (assignment 149) Sign.negative :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode139)
  let hnode152 : Eq (assignment 152) Sign.negative :=
    Eq.trans (h_support 132 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode159 : Eq (assignment 159) Sign.positive :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode89)
  let hnode160 : Eq (assignment 160) Sign.positive :=
    Eq.trans (h_support 19 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode139)
  let hnode161 : Eq (assignment 161) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode163 : Eq (assignment 163) Sign.negative :=
    Eq.trans (h_support 125 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode173 : Eq (assignment 173) Sign.negative :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode176 : Eq (assignment 176) Sign.negative :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode182 : Eq (assignment 182) Sign.negative :=
    Eq.trans (h_support 133 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode184 : Eq (assignment 184) Sign.negative :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode142)
  let hnode191 : Eq (assignment 191) Sign.negative :=
    Eq.trans (h_support 134 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode193 : Eq (assignment 193) Sign.positive :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode198 : Eq (assignment 198) Sign.positive :=
    Eq.trans (h_support 205 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode73)
  let hnode201 : Eq (assignment 201) Sign.positive :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode76)
  let hnode207 : Eq (assignment 207) Sign.positive :=
    Eq.trans (h_support 182 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode219 : Eq (assignment 219) Sign.positive :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode73)
  let hnode221 : Eq (assignment 221) Sign.negative :=
    Eq.trans (h_support 207 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode73)
  let hnode222 : Eq (assignment 222) Sign.positive :=
    Eq.trans (h_support 210 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode76)
  let hnode224 : Eq (assignment 224) Sign.negative :=
    Eq.trans (h_support 211 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode76)
  let hnode228 : Eq (assignment 228) Sign.negative :=
    Eq.trans (h_support 194 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode89)
  let hnode241 : Eq (assignment 241) Sign.negative :=
    Eq.trans (h_support 234 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode101)
  let hnode242 : Eq (assignment 242) Sign.negative :=
    Eq.trans (h_support 235 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode101)
  let hnode31 : Eq (assignment 31) Sign.negative :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode33 : Eq (assignment 33) Sign.negative :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode54 : Eq (assignment 54) Sign.negative :=
    Eq.trans (h_support 30 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode57 : Eq (assignment 57) Sign.negative :=
    Eq.trans (h_support 80 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode7)
  let hnode82 : Eq (assignment 82) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 212 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode152)
  let hnode86 : Eq (assignment 86) Sign.positive :=
    Eq.trans (h_support 109 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode20)
  let hnode91 : Eq (assignment 91) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 220 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode161)
  let hnode102 : Eq (assignment 102) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 138 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode241)
  let hnode106 : Eq (assignment 106) Sign.negative :=
    Eq.trans (h_support 33 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode70)
  let hnode109 : Eq (assignment 109) Sign.negative :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode70)
  let hnode110 : Eq (assignment 110) Sign.negative :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode70)
  let hnode134 : Eq (assignment 134) Sign.negative :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode141 : Eq (assignment 141) Sign.positive :=
    Eq.trans (h_support 200 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode150 : Eq (assignment 150) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 117 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode221)
  let hnode164 : Eq (assignment 164) Sign.positive :=
    Eq.trans (h_support 145 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode170 : Eq (assignment 170) Sign.negative :=
    Eq.trans (h_support 36 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode140)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 38 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode140)
  let hnode186 : Eq (assignment 186) Sign.positive :=
    Eq.trans (h_support 79 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode143)
  let hnode196 : Eq (assignment 196) Sign.negative :=
    Eq.trans (h_support 201 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode71)
  let hnode205 : Eq (assignment 205) Sign.positive :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode211 : Eq (assignment 211) Sign.positive :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode218 : Eq (assignment 218) Sign.positive :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode232 : Eq (assignment 232) Sign.negative :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode105)
  let hnode245 : Eq (assignment 245) Sign.negative :=
    Eq.trans (h_support 179 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode108)
  let hnode248 : Eq (assignment 248) Sign.negative :=
    Eq.trans (h_support 219 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode166 : Eq (assignment 166) Sign.negative :=
    Eq.trans (h_support 129 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode177 : Eq (assignment 177) Sign.positive :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode31)
  let hnode225 : Eq (assignment 225) Sign.negative :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode150)
  let hnode226 : Eq (assignment 226) Sign.positive :=
    Eq.trans (h_support 214 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode82)
  let hnode233 : Eq (assignment 233) Sign.negative :=
    Eq.trans (h_support 223 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode239 : Eq (assignment 239) Sign.positive :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode109)
  let hnode243 : Eq (assignment 243) Sign.positive :=
    Eq.trans (h_support 198 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode109)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C010.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (top_allows (Sign.withNegation globalNegation (assignment 0)))
  let bounded2 := below_succ bounded1 (top_allows (Sign.withNegation globalNegation (assignment 1)))
  let bounded3 := below_succ bounded2 (top_allows (Sign.withNegation globalNegation (assignment 2)))
  let bounded4 := below_succ bounded3 (domain_from_eq (domain := Cases.C010.initial 3) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C010.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Cases.C010.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Cases.C010.initial 6) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Cases.C010.initial 7) (congrArg (Sign.withNegation globalNegation) hnode7) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C010.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Cases.C010.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C010.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (top_allows (Sign.withNegation globalNegation (assignment 11)))
  let bounded13 := below_succ bounded12 (domain_from_eq (domain := Cases.C010.initial 12) (congrArg (Sign.withNegation globalNegation) hnode12) (Eq.refl Bool.true))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C010.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C010.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Cases.C010.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (top_allows (Sign.withNegation globalNegation (assignment 16)))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C010.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (domain_from_eq (domain := Cases.C010.initial 18) (congrArg (Sign.withNegation globalNegation) hnode18) (Eq.refl Bool.true))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C010.initial 19) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Cases.C010.initial 20) (congrArg (Sign.withNegation globalNegation) hnode20) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C010.initial 21) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (top_allows (Sign.withNegation globalNegation (assignment 22)))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C010.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C010.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C010.initial 25) (congrArg (Sign.withNegation globalNegation) hnode25) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Cases.C010.initial 26) (congrArg (Sign.withNegation globalNegation) hnode26) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C010.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C010.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C010.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (top_allows (Sign.withNegation globalNegation (assignment 30)))
  let bounded32 := below_succ bounded31 (domain_from_eq (domain := Cases.C010.initial 31) (congrArg (Sign.withNegation globalNegation) hnode31) (Eq.refl Bool.true))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C010.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C010.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C010.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (domain_from_eq (domain := Cases.C010.initial 35) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded37 := below_succ bounded36 (domain_from_eq (domain := Cases.C010.initial 36) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C010.initial 37) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C010.initial 38) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (domain_from_eq (domain := Cases.C010.initial 39) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Cases.C010.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C010.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (top_allows (Sign.withNegation globalNegation (assignment 42)))
  let bounded44 := below_succ bounded43 (domain_from_eq (domain := Cases.C010.initial 43) (congrArg (Sign.withNegation globalNegation) hnode43) (Eq.refl Bool.true))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Cases.C010.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C010.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (domain_from_eq (domain := Cases.C010.initial 46) (congrArg (Sign.withNegation globalNegation) hnode46) (Eq.refl Bool.true))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C010.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (top_allows (Sign.withNegation globalNegation (assignment 48)))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C010.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (domain_from_eq (domain := Cases.C010.initial 50) (congrArg (Sign.withNegation globalNegation) hnode50) (Eq.refl Bool.true))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C010.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (top_allows (Sign.withNegation globalNegation (assignment 52)))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Cases.C010.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Cases.C010.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (domain_from_eq (domain := Cases.C010.initial 55) (congrArg (Sign.withNegation globalNegation) hnode55) (Eq.refl Bool.true))
  let bounded57 := below_succ bounded56 (top_allows (Sign.withNegation globalNegation (assignment 56)))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C010.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C010.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C010.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C010.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (top_allows (Sign.withNegation globalNegation (assignment 61)))
  let bounded63 := below_succ bounded62 (top_allows (Sign.withNegation globalNegation (assignment 62)))
  let bounded64 := below_succ bounded63 (top_allows (Sign.withNegation globalNegation (assignment 63)))
  let bounded65 := below_succ bounded64 (top_allows (Sign.withNegation globalNegation (assignment 64)))
  let bounded66 := below_succ bounded65 (domain_from_eq (domain := Cases.C010.initial 65) (congrArg (Sign.withNegation globalNegation) hnode65) (Eq.refl Bool.true))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C010.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (domain_from_eq (domain := Cases.C010.initial 67) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded69 := below_succ bounded68 (top_allows (Sign.withNegation globalNegation (assignment 68)))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C010.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C010.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C010.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C010.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C010.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C010.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Cases.C010.initial 75) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Cases.C010.initial 76) (congrArg (Sign.withNegation globalNegation) hnode76) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C010.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C010.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C010.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (domain_from_eq (domain := Cases.C010.initial 80) (congrArg (Sign.withNegation globalNegation) (h_zero 10 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded82 := below_succ bounded81 (domain_from_eq (domain := Cases.C010.initial 81) (congrArg (Sign.withNegation globalNegation) hnode81) (Eq.refl Bool.true))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Cases.C010.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (top_allows (Sign.withNegation globalNegation (assignment 83)))
  let bounded85 := below_succ bounded84 (top_allows (Sign.withNegation globalNegation (assignment 84)))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C010.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C010.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C010.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Cases.C010.initial 88) (congrArg (Sign.withNegation globalNegation) hnode88) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (domain_from_eq (domain := Cases.C010.initial 89) (congrArg (Sign.withNegation globalNegation) hnode89) (Eq.refl Bool.true))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C010.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C010.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C010.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C010.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (top_allows (Sign.withNegation globalNegation (assignment 94)))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C010.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (top_allows (Sign.withNegation globalNegation (assignment 96)))
  let bounded98 := below_succ bounded97 (top_allows (Sign.withNegation globalNegation (assignment 97)))
  let bounded99 := below_succ bounded98 (top_allows (Sign.withNegation globalNegation (assignment 98)))
  let bounded100 := below_succ bounded99 (top_allows (Sign.withNegation globalNegation (assignment 99)))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C010.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C010.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C010.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (top_allows (Sign.withNegation globalNegation (assignment 103)))
  let bounded105 := below_succ bounded104 (top_allows (Sign.withNegation globalNegation (assignment 104)))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C010.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C010.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (top_allows (Sign.withNegation globalNegation (assignment 107)))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C010.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C010.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C010.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C010.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C010.initial 112) (congrArg (Sign.withNegation globalNegation) hnode112) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (top_allows (Sign.withNegation globalNegation (assignment 113)))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C010.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C010.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C010.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C010.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C010.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C010.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C010.initial 120) (congrArg (Sign.withNegation globalNegation) hnode120) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (top_allows (Sign.withNegation globalNegation (assignment 121)))
  let bounded123 := below_succ bounded122 (top_allows (Sign.withNegation globalNegation (assignment 122)))
  let bounded124 := below_succ bounded123 (top_allows (Sign.withNegation globalNegation (assignment 123)))
  let bounded125 := below_succ bounded124 (top_allows (Sign.withNegation globalNegation (assignment 124)))
  let bounded126 := below_succ bounded125 (top_allows (Sign.withNegation globalNegation (assignment 125)))
  let bounded127 := below_succ bounded126 (top_allows (Sign.withNegation globalNegation (assignment 126)))
  let bounded128 := below_succ bounded127 (top_allows (Sign.withNegation globalNegation (assignment 127)))
  let bounded129 := below_succ bounded128 (top_allows (Sign.withNegation globalNegation (assignment 128)))
  let bounded130 := below_succ bounded129 (top_allows (Sign.withNegation globalNegation (assignment 129)))
  let bounded131 := below_succ bounded130 (top_allows (Sign.withNegation globalNegation (assignment 130)))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C010.initial 131) (congrArg (Sign.withNegation globalNegation) hnode131) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C010.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C010.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C010.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C010.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C010.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C010.initial 137) (congrArg (Sign.withNegation globalNegation) (h_zero 11 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (top_allows (Sign.withNegation globalNegation (assignment 138)))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C010.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C010.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C010.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C010.initial 142) (congrArg (Sign.withNegation globalNegation) hnode142) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C010.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (top_allows (Sign.withNegation globalNegation (assignment 144)))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C010.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C010.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (top_allows (Sign.withNegation globalNegation (assignment 147)))
  let bounded149 := below_succ bounded148 (top_allows (Sign.withNegation globalNegation (assignment 148)))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C010.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C010.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (top_allows (Sign.withNegation globalNegation (assignment 151)))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C010.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (top_allows (Sign.withNegation globalNegation (assignment 153)))
  let bounded155 := below_succ bounded154 (top_allows (Sign.withNegation globalNegation (assignment 154)))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C010.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (top_allows (Sign.withNegation globalNegation (assignment 156)))
  let bounded158 := below_succ bounded157 (top_allows (Sign.withNegation globalNegation (assignment 157)))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C010.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C010.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C010.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (domain_from_eq (domain := Cases.C010.initial 161) (congrArg (Sign.withNegation globalNegation) hnode161) (Eq.refl Bool.true))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Cases.C010.initial 162) (congrArg (Sign.withNegation globalNegation) hnode162) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C010.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C010.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C010.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C010.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (top_allows (Sign.withNegation globalNegation (assignment 167)))
  let bounded169 := below_succ bounded168 (top_allows (Sign.withNegation globalNegation (assignment 168)))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C010.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C010.initial 170) (congrArg (Sign.withNegation globalNegation) hnode170) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C010.initial 171) (congrArg (Sign.withNegation globalNegation) hnode171) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C010.initial 172) (congrArg (Sign.withNegation globalNegation) (h_zero 12 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C010.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C010.initial 174) (congrArg (Sign.withNegation globalNegation) hnode174) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C010.initial 175) (congrArg (Sign.withNegation globalNegation) (h_zero 13 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C010.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Cases.C010.initial 177) (congrArg (Sign.withNegation globalNegation) hnode177) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C010.initial 178) (congrArg (Sign.withNegation globalNegation) hnode178) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C010.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C010.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C010.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C010.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (top_allows (Sign.withNegation globalNegation (assignment 183)))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Cases.C010.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C010.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Cases.C010.initial 186) (congrArg (Sign.withNegation globalNegation) hnode186) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (top_allows (Sign.withNegation globalNegation (assignment 187)))
  let bounded189 := below_succ bounded188 (top_allows (Sign.withNegation globalNegation (assignment 188)))
  let bounded190 := below_succ bounded189 (top_allows (Sign.withNegation globalNegation (assignment 189)))
  let bounded191 := below_succ bounded190 (top_allows (Sign.withNegation globalNegation (assignment 190)))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C010.initial 191) (congrArg (Sign.withNegation globalNegation) hnode191) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C010.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C010.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Cases.C010.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (top_allows (Sign.withNegation globalNegation (assignment 195)))
  let bounded197 := below_succ bounded196 (domain_from_eq (domain := Cases.C010.initial 196) (congrArg (Sign.withNegation globalNegation) hnode196) (Eq.refl Bool.true))
  let bounded198 := below_succ bounded197 (domain_from_eq (domain := Cases.C010.initial 197) (congrArg (Sign.withNegation globalNegation) hnode197) (Eq.refl Bool.true))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Cases.C010.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (top_allows (Sign.withNegation globalNegation (assignment 199)))
  let bounded201 := below_succ bounded200 (domain_from_eq (domain := Cases.C010.initial 200) (congrArg (Sign.withNegation globalNegation) hnode200) (Eq.refl Bool.true))
  let bounded202 := below_succ bounded201 (domain_from_eq (domain := Cases.C010.initial 201) (congrArg (Sign.withNegation globalNegation) hnode201) (Eq.refl Bool.true))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C010.initial 202) (congrArg (Sign.withNegation globalNegation) (h_zero 14 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (top_allows (Sign.withNegation globalNegation (assignment 203)))
  let bounded205 := below_succ bounded204 (domain_from_eq (domain := Cases.C010.initial 204) (congrArg (Sign.withNegation globalNegation) hnode204) (Eq.refl Bool.true))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C010.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Cases.C010.initial 206) (congrArg (Sign.withNegation globalNegation) hnode206) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Cases.C010.initial 207) (congrArg (Sign.withNegation globalNegation) hnode207) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C010.initial 208) (congrArg (Sign.withNegation globalNegation) (h_zero 15 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (top_allows (Sign.withNegation globalNegation (assignment 209)))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C010.initial 210) (congrArg (Sign.withNegation globalNegation) hnode210) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C010.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C010.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C010.initial 213) (congrArg (Sign.withNegation globalNegation) (h_zero 16 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C010.initial 214) (congrArg (Sign.withNegation globalNegation) (h_zero 17 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (domain_from_eq (domain := Cases.C010.initial 215) (congrArg (Sign.withNegation globalNegation) hnode215) (Eq.refl Bool.true))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C010.initial 216) (congrArg (Sign.withNegation globalNegation) hnode216) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C010.initial 217) (congrArg (Sign.withNegation globalNegation) (h_zero 18 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C010.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Cases.C010.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (top_allows (Sign.withNegation globalNegation (assignment 220)))
  let bounded222 := below_succ bounded221 (domain_from_eq (domain := Cases.C010.initial 221) (congrArg (Sign.withNegation globalNegation) hnode221) (Eq.refl Bool.true))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C010.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C010.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C010.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C010.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C010.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C010.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C010.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (top_allows (Sign.withNegation globalNegation (assignment 229)))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C010.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (domain_from_eq (domain := Cases.C010.initial 231) (congrArg (Sign.withNegation globalNegation) (h_zero 19 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C010.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (domain_from_eq (domain := Cases.C010.initial 233) (congrArg (Sign.withNegation globalNegation) hnode233) (Eq.refl Bool.true))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C010.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C010.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (top_allows (Sign.withNegation globalNegation (assignment 236)))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C010.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C010.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Cases.C010.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (top_allows (Sign.withNegation globalNegation (assignment 240)))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C010.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C010.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C010.initial 243) (congrArg (Sign.withNegation globalNegation) hnode243) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C010.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C010.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C010.initial 246) (congrArg (Sign.withNegation globalNegation) hnode246) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C010.initial 247) (congrArg (Sign.withNegation globalNegation) hnode247) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C010.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (top_allows (Sign.withNegation globalNegation (assignment 249)))
  let bounded251 := below_succ bounded250 (top_allows (Sign.withNegation globalNegation (assignment 250)))
  let bounded252 := below_succ bounded251 (top_allows (Sign.withNegation globalNegation (assignment 251)))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C010.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C010
#print axioms Papers.RationalityTen.PureGP.Initializers.C010.support_sign_contradiction
