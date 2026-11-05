module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C013

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C013
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 1
def globalNegation : Bool := Bool.false
def edgeTable : Table SupportEdge := (Table.node 115 (Table.node 57 (Table.node 28 (Table.node 14 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 1 21 Bool.true)) (Table.node 2 (Table.leaf (SupportEdge.mk 1 26 Bool.false)) (Table.leaf (SupportEdge.mk 1 27 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 1 29 Bool.false)) (Table.leaf (SupportEdge.mk 4 24 Bool.true))) (Table.node 6 (Table.leaf (SupportEdge.mk 4 31 Bool.true)) (Table.leaf (SupportEdge.mk 4 33 Bool.true))))) (Table.node 10 (Table.node 8 (Table.leaf (SupportEdge.mk 4 35 Bool.false)) (Table.node 9 (Table.leaf (SupportEdge.mk 13 38 Bool.false)) (Table.leaf (SupportEdge.mk 13 47 Bool.true)))) (Table.node 12 (Table.node 11 (Table.leaf (SupportEdge.mk 13 49 Bool.true)) (Table.leaf (SupportEdge.mk 13 51 Bool.false))) (Table.node 13 (Table.leaf (SupportEdge.mk 63 93 Bool.true)) (Table.leaf (SupportEdge.mk 63 102 Bool.false)))))) (Table.node 21 (Table.node 17 (Table.node 15 (Table.leaf (SupportEdge.mk 63 104 Bool.false)) (Table.node 16 (Table.leaf (SupportEdge.mk 63 106 Bool.true)) (Table.leaf (SupportEdge.mk 133 163 Bool.true)))) (Table.node 19 (Table.node 18 (Table.leaf (SupportEdge.mk 133 172 Bool.false)) (Table.leaf (SupportEdge.mk 133 174 Bool.false))) (Table.node 20 (Table.leaf (SupportEdge.mk 133 176 Bool.true)) (Table.leaf (SupportEdge.mk 1 56 Bool.false))))) (Table.node 24 (Table.node 22 (Table.leaf (SupportEdge.mk 1 61 Bool.true)) (Table.node 23 (Table.leaf (SupportEdge.mk 1 63 Bool.true)) (Table.leaf (SupportEdge.mk 1 64 Bool.true)))) (Table.node 26 (Table.node 25 (Table.leaf (SupportEdge.mk 3 58 Bool.false)) (Table.leaf (SupportEdge.mk 3 65 Bool.false))) (Table.node 27 (Table.leaf (SupportEdge.mk 3 68 Bool.true)) (Table.leaf (SupportEdge.mk 3 69 Bool.true))))))) (Table.node 42 (Table.node 35 (Table.node 31 (Table.node 29 (Table.leaf (SupportEdge.mk 12 72 Bool.true)) (Table.node 30 (Table.leaf (SupportEdge.mk 12 81 Bool.false)) (Table.leaf (SupportEdge.mk 12 84 Bool.true)))) (Table.node 33 (Table.node 32 (Table.leaf (SupportEdge.mk 12 85 Bool.true)) (Table.leaf (SupportEdge.mk 27 92 Bool.true))) (Table.node 34 (Table.leaf (SupportEdge.mk 27 101 Bool.false)) (Table.leaf (SupportEdge.mk 27 104 Bool.true))))) (Table.node 38 (Table.node 36 (Table.leaf (SupportEdge.mk 27 105 Bool.true)) (Table.node 37 (Table.leaf (SupportEdge.mk 132 197 Bool.false)) (Table.leaf (SupportEdge.mk 132 206 Bool.true)))) (Table.node 40 (Table.node 39 (Table.leaf (SupportEdge.mk 132 209 Bool.false)) (Table.leaf (SupportEdge.mk 132 210 Bool.false))) (Table.node 41 (Table.leaf (SupportEdge.mk 6 56 Bool.true)) (Table.leaf (SupportEdge.mk 6 71 Bool.true)))))) (Table.node 49 (Table.node 45 (Table.node 43 (Table.leaf (SupportEdge.mk 6 72 Bool.true)) (Table.node 44 (Table.leaf (SupportEdge.mk 6 74 Bool.true)) (Table.leaf (SupportEdge.mk 9 59 Bool.true)))) (Table.node 47 (Table.node 46 (Table.leaf (SupportEdge.mk 9 76 Bool.false)) (Table.leaf (SupportEdge.mk 9 78 Bool.false))) (Table.node 48 (Table.leaf (SupportEdge.mk 9 80 Bool.true)) (Table.leaf (SupportEdge.mk 13 63 Bool.true))))) (Table.node 53 (Table.node 51 (Table.node 50 (Table.leaf (SupportEdge.mk 13 82 Bool.false)) (Table.leaf (SupportEdge.mk 13 84 Bool.false))) (Table.node 52 (Table.leaf (SupportEdge.mk 13 86 Bool.true)) (Table.leaf (SupportEdge.mk 38 93 Bool.false)))) (Table.node 55 (Table.node 54 (Table.leaf (SupportEdge.mk 38 112 Bool.false)) (Table.leaf (SupportEdge.mk 38 114 Bool.false))) (Table.node 56 (Table.leaf (SupportEdge.mk 38 116 Bool.true)) (Table.leaf (SupportEdge.mk 143 198 Bool.true)))))))) (Table.node 86 (Table.node 71 (Table.node 64 (Table.node 60 (Table.node 58 (Table.leaf (SupportEdge.mk 143 217 Bool.true)) (Table.node 59 (Table.leaf (SupportEdge.mk 143 219 Bool.true)) (Table.leaf (SupportEdge.mk 143 221 Bool.false)))) (Table.node 62 (Table.node 61 (Table.leaf (SupportEdge.mk 7 57 Bool.true)) (Table.leaf (SupportEdge.mk 7 71 Bool.false))) (Table.node 63 (Table.leaf (SupportEdge.mk 7 76 Bool.true)) (Table.leaf (SupportEdge.mk 7 77 Bool.true))))) (Table.node 67 (Table.node 65 (Table.leaf (SupportEdge.mk 8 58 Bool.true)) (Table.node 66 (Table.leaf (SupportEdge.mk 8 72 Bool.false)) (Table.leaf (SupportEdge.mk 8 78 Bool.true)))) (Table.node 69 (Table.node 68 (Table.leaf (SupportEdge.mk 8 79 Bool.true)) (Table.leaf (SupportEdge.mk 15 65 Bool.true))) (Table.node 70 (Table.leaf (SupportEdge.mk 15 81 Bool.true)) (Table.leaf (SupportEdge.mk 15 87 Bool.true)))))) (Table.node 78 (Table.node 74 (Table.node 72 (Table.leaf (SupportEdge.mk 15 88 Bool.true)) (Table.node 73 (Table.leaf (SupportEdge.mk 40 95 Bool.false)) (Table.leaf (SupportEdge.mk 40 111 Bool.true)))) (Table.node 76 (Table.node 75 (Table.leaf (SupportEdge.mk 40 117 Bool.true)) (Table.leaf (SupportEdge.mk 40 118 Bool.true))) (Table.node 77 (Table.leaf (SupportEdge.mk 145 200 Bool.true)) (Table.leaf (SupportEdge.mk 145 216 Bool.false))))) (Table.node 82 (Table.node 80 (Table.node 79 (Table.leaf (SupportEdge.mk 145 222 Bool.false)) (Table.leaf (SupportEdge.mk 145 223 Bool.false))) (Table.node 81 (Table.leaf (SupportEdge.mk 23 58 Bool.false)) (Table.leaf (SupportEdge.mk 23 92 Bool.false)))) (Table.node 84 (Table.node 83 (Table.leaf (SupportEdge.mk 23 95 Bool.false)) (Table.leaf (SupportEdge.mk 23 98 Bool.true))) (Table.node 85 (Table.leaf (SupportEdge.mk 23 99 Bool.true)) (Table.leaf (SupportEdge.mk 24 59 Bool.false))))))) (Table.node 100 (Table.node 93 (Table.node 89 (Table.node 87 (Table.leaf (SupportEdge.mk 24 93 Bool.false)) (Table.node 88 (Table.leaf (SupportEdge.mk 24 96 Bool.false)) (Table.leaf (SupportEdge.mk 24 98 Bool.false)))) (Table.node 91 (Table.node 90 (Table.leaf (SupportEdge.mk 25 60 Bool.false)) (Table.leaf (SupportEdge.mk 25 94 Bool.false))) (Table.node 92 (Table.leaf (SupportEdge.mk 25 97 Bool.false)) (Table.leaf (SupportEdge.mk 25 99 Bool.false))))) (Table.node 96 (Table.node 94 (Table.leaf (SupportEdge.mk 35 70 Bool.false)) (Table.node 95 (Table.leaf (SupportEdge.mk 35 106 Bool.true)) (Table.leaf (SupportEdge.mk 35 109 Bool.true)))) (Table.node 98 (Table.node 97 (Table.leaf (SupportEdge.mk 35 110 Bool.true)) (Table.leaf (SupportEdge.mk 45 80 Bool.false))) (Table.node 99 (Table.leaf (SupportEdge.mk 45 116 Bool.true)) (Table.leaf (SupportEdge.mk 45 119 Bool.true)))))) (Table.node 107 (Table.node 103 (Table.node 101 (Table.leaf (SupportEdge.mk 45 120 Bool.true)) (Table.node 102 (Table.leaf (SupportEdge.mk 170 205 Bool.false)) (Table.leaf (SupportEdge.mk 170 236 Bool.false)))) (Table.node 105 (Table.node 104 (Table.leaf (SupportEdge.mk 170 239 Bool.false)) (Table.leaf (SupportEdge.mk 170 240 Bool.false))) (Table.node 106 (Table.leaf (SupportEdge.mk 12 132 Bool.false)) (Table.leaf (SupportEdge.mk 12 142 Bool.false))))) (Table.node 111 (Table.node 109 (Table.node 108 (Table.leaf (SupportEdge.mk 12 151 Bool.true)) (Table.leaf (SupportEdge.mk 12 155 Bool.false))) (Table.node 110 (Table.leaf (SupportEdge.mk 13 133 Bool.false)) (Table.leaf (SupportEdge.mk 13 143 Bool.false)))) (Table.node 113 (Table.node 112 (Table.leaf (SupportEdge.mk 13 152 Bool.true)) (Table.leaf (SupportEdge.mk 13 156 Bool.false))) (Table.node 114 (Table.leaf (SupportEdge.mk 18 138 Bool.false)) (Table.leaf (SupportEdge.mk 18 148 Bool.false))))))))) (Table.node 172 (Table.node 143 (Table.node 129 (Table.node 122 (Table.node 118 (Table.node 116 (Table.leaf (SupportEdge.mk 18 157 Bool.false)) (Table.node 117 (Table.leaf (SupportEdge.mk 18 160 Bool.false)) (Table.leaf (SupportEdge.mk 49 174 Bool.true)))) (Table.node 120 (Table.node 119 (Table.leaf (SupportEdge.mk 49 184 Bool.true)) (Table.leaf (SupportEdge.mk 49 191 Bool.false))) (Table.node 121 (Table.leaf (SupportEdge.mk 49 194 Bool.false)) (Table.leaf (SupportEdge.mk 84 209 Bool.true))))) (Table.node 125 (Table.node 123 (Table.leaf (SupportEdge.mk 84 219 Bool.true)) (Table.node 124 (Table.leaf (SupportEdge.mk 84 226 Bool.false)) (Table.leaf (SupportEdge.mk 84 229 Bool.false)))) (Table.node 127 (Table.node 126 (Table.leaf (SupportEdge.mk 15 135 Bool.false)) (Table.leaf (SupportEdge.mk 15 145 Bool.false))) (Table.node 128 (Table.leaf (SupportEdge.mk 15 151 Bool.false)) (Table.leaf (SupportEdge.mk 15 158 Bool.false)))))) (Table.node 136 (Table.node 132 (Table.node 130 (Table.leaf (SupportEdge.mk 16 136 Bool.false)) (Table.node 131 (Table.leaf (SupportEdge.mk 16 146 Bool.false)) (Table.leaf (SupportEdge.mk 16 152 Bool.false)))) (Table.node 134 (Table.node 133 (Table.leaf (SupportEdge.mk 16 159 Bool.false)) (Table.leaf (SupportEdge.mk 18 138 Bool.false))) (Table.node 135 (Table.leaf (SupportEdge.mk 18 148 Bool.false)) (Table.leaf (SupportEdge.mk 18 154 Bool.false))))) (Table.node 139 (Table.node 137 (Table.leaf (SupportEdge.mk 18 160 Bool.false)) (Table.node 138 (Table.leaf (SupportEdge.mk 52 177 Bool.true)) (Table.leaf (SupportEdge.mk 52 187 Bool.true)))) (Table.node 141 (Table.node 140 (Table.leaf (SupportEdge.mk 52 191 Bool.true)) (Table.leaf (SupportEdge.mk 52 195 Bool.false))) (Table.node 142 (Table.leaf (SupportEdge.mk 87 212 Bool.true)) (Table.leaf (SupportEdge.mk 87 222 Bool.true))))))) (Table.node 157 (Table.node 150 (Table.node 146 (Table.node 144 (Table.leaf (SupportEdge.mk 87 226 Bool.true)) (Table.node 145 (Table.leaf (SupportEdge.mk 87 230 Bool.false)) (Table.leaf (SupportEdge.mk 27 132 Bool.true)))) (Table.node 148 (Table.node 147 (Table.leaf (SupportEdge.mk 27 162 Bool.false)) (Table.leaf (SupportEdge.mk 27 171 Bool.true))) (Table.node 149 (Table.leaf (SupportEdge.mk 27 174 Bool.false)) (Table.leaf (SupportEdge.mk 29 134 Bool.true))))) (Table.node 153 (Table.node 151 (Table.leaf (SupportEdge.mk 29 164 Bool.false)) (Table.node 152 (Table.leaf (SupportEdge.mk 29 173 Bool.true)) (Table.leaf (SupportEdge.mk 29 176 Bool.true)))) (Table.node 155 (Table.node 154 (Table.leaf (SupportEdge.mk 34 139 Bool.true)) (Table.leaf (SupportEdge.mk 34 169 Bool.false))) (Table.node 156 (Table.leaf (SupportEdge.mk 34 178 Bool.false)) (Table.leaf (SupportEdge.mk 34 180 Bool.true)))))) (Table.node 164 (Table.node 160 (Table.node 158 (Table.leaf (SupportEdge.mk 50 155 Bool.true)) (Table.node 159 (Table.leaf (SupportEdge.mk 50 185 Bool.true)) (Table.leaf (SupportEdge.mk 50 192 Bool.false)))) (Table.node 162 (Table.node 161 (Table.leaf (SupportEdge.mk 50 194 Bool.true)) (Table.leaf (SupportEdge.mk 105 210 Bool.false))) (Table.node 163 (Table.leaf (SupportEdge.mk 105 235 Bool.true)) (Table.leaf (SupportEdge.mk 105 242 Bool.false))))) (Table.node 168 (Table.node 166 (Table.node 165 (Table.leaf (SupportEdge.mk 105 244 Bool.true)) (Table.leaf (SupportEdge.mk 31 136 Bool.true))) (Table.node 167 (Table.leaf (SupportEdge.mk 31 166 Bool.false)) (Table.leaf (SupportEdge.mk 31 172 Bool.false)))) (Table.node 170 (Table.node 169 (Table.leaf (SupportEdge.mk 31 177 Bool.true)) (Table.leaf (SupportEdge.mk 32 137 Bool.true))) (Table.node 171 (Table.leaf (SupportEdge.mk 32 167 Bool.false)) (Table.leaf (SupportEdge.mk 32 173 Bool.false)))))))) (Table.node 201 (Table.node 186 (Table.node 179 (Table.node 175 (Table.node 173 (Table.leaf (SupportEdge.mk 32 178 Bool.true)) (Table.node 174 (Table.leaf (SupportEdge.mk 35 140 Bool.true)) (Table.leaf (SupportEdge.mk 35 170 Bool.false)))) (Table.node 177 (Table.node 176 (Table.leaf (SupportEdge.mk 35 176 Bool.false)) (Table.leaf (SupportEdge.mk 35 180 Bool.false))) (Table.node 178 (Table.leaf (SupportEdge.mk 54 159 Bool.true)) (Table.leaf (SupportEdge.mk 54 189 Bool.true))))) (Table.node 182 (Table.node 180 (Table.leaf (SupportEdge.mk 54 193 Bool.true)) (Table.node 181 (Table.leaf (SupportEdge.mk 54 195 Bool.false)) (Table.leaf (SupportEdge.mk 109 214 Bool.false)))) (Table.node 184 (Table.node 183 (Table.leaf (SupportEdge.mk 109 239 Bool.true)) (Table.leaf (SupportEdge.mk 109 243 Bool.true))) (Table.node 185 (Table.leaf (SupportEdge.mk 109 245 Bool.false)) (Table.leaf (SupportEdge.mk 40 145 Bool.true)))))) (Table.node 193 (Table.node 189 (Table.node 187 (Table.leaf (SupportEdge.mk 40 165 Bool.true)) (Table.node 188 (Table.leaf (SupportEdge.mk 40 181 Bool.false)) (Table.leaf (SupportEdge.mk 40 187 Bool.false)))) (Table.node 191 (Table.node 190 (Table.leaf (SupportEdge.mk 42 147 Bool.true)) (Table.leaf (SupportEdge.mk 42 167 Bool.true))) (Table.node 192 (Table.leaf (SupportEdge.mk 42 183 Bool.false)) (Table.leaf (SupportEdge.mk 42 189 Bool.true))))) (Table.node 197 (Table.node 195 (Table.node 194 (Table.leaf (SupportEdge.mk 44 149 Bool.true)) (Table.leaf (SupportEdge.mk 44 169 Bool.true))) (Table.node 196 (Table.leaf (SupportEdge.mk 44 185 Bool.false)) (Table.leaf (SupportEdge.mk 44 190 Bool.true)))) (Table.node 199 (Table.node 198 (Table.leaf (SupportEdge.mk 53 158 Bool.true)) (Table.leaf (SupportEdge.mk 53 178 Bool.true))) (Table.node 200 (Table.leaf (SupportEdge.mk 53 192 Bool.true)) (Table.leaf (SupportEdge.mk 53 195 Bool.true))))))) (Table.node 215 (Table.node 208 (Table.node 204 (Table.node 202 (Table.leaf (SupportEdge.mk 118 223 Bool.false)) (Table.node 203 (Table.leaf (SupportEdge.mk 118 238 Bool.false)) (Table.leaf (SupportEdge.mk 118 247 Bool.true)))) (Table.node 206 (Table.node 205 (Table.leaf (SupportEdge.mk 118 250 Bool.true)) (Table.leaf (SupportEdge.mk 76 146 Bool.false))) (Table.node 207 (Table.leaf (SupportEdge.mk 76 201 Bool.true)) (Table.leaf (SupportEdge.mk 76 217 Bool.false))))) (Table.node 211 (Table.node 209 (Table.leaf (SupportEdge.mk 76 222 Bool.true)) (Table.node 210 (Table.leaf (SupportEdge.mk 77 147 Bool.false)) (Table.leaf (SupportEdge.mk 77 202 Bool.true)))) (Table.node 213 (Table.node 212 (Table.leaf (SupportEdge.mk 77 218 Bool.false)) (Table.leaf (SupportEdge.mk 77 223 Bool.true))) (Table.node 214 (Table.leaf (SupportEdge.mk 80 150 Bool.false)) (Table.leaf (SupportEdge.mk 80 205 Bool.true)))))) (Table.node 222 (Table.node 218 (Table.node 216 (Table.leaf (SupportEdge.mk 80 221 Bool.false)) (Table.node 217 (Table.leaf (SupportEdge.mk 80 225 Bool.false)) (Table.leaf (SupportEdge.mk 89 159 Bool.false)))) (Table.node 220 (Table.node 219 (Table.leaf (SupportEdge.mk 89 214 Bool.true)) (Table.leaf (SupportEdge.mk 89 228 Bool.true))) (Table.node 221 (Table.leaf (SupportEdge.mk 89 230 Bool.false)) (Table.leaf (SupportEdge.mk 119 189 Bool.false))))) (Table.node 226 (Table.node 224 (Table.node 223 (Table.leaf (SupportEdge.mk 119 239 Bool.false)) (Table.leaf (SupportEdge.mk 119 248 Bool.true))) (Table.node 225 (Table.leaf (SupportEdge.mk 119 250 Bool.false)) (Table.leaf (SupportEdge.mk 99 169 Bool.false)))) (Table.node 228 (Table.node 227 (Table.leaf (SupportEdge.mk 99 204 Bool.false)) (Table.leaf (SupportEdge.mk 99 235 Bool.false))) (Table.node 229 (Table.leaf (SupportEdge.mk 99 238 Bool.false)) (Table.leaf (SupportEdge.mk 99 240 Bool.true))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf 18) (Table.node 2 (Table.leaf 28) (Table.leaf 62))) (Table.node 5 (Table.node 4 (Table.leaf 73) (Table.leaf 75)) (Table.node 6 (Table.leaf 100) (Table.leaf 138)))) (Table.node 11 (Table.node 9 (Table.node 8 (Table.leaf 148) (Table.leaf 154)) (Table.node 10 (Table.leaf 157) (Table.leaf 160))) (Table.node 13 (Table.node 12 (Table.leaf 175) (Table.leaf 179)) (Table.node 14 (Table.leaf 188) (Table.leaf 224)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 230 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 15 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C013.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode21 : Eq (assignment 21) Sign.negative :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode26 : Eq (assignment 26) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode27 : Eq (assignment 27) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode29 : Eq (assignment 29) Sign.positive :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode56 : Eq (assignment 56) Sign.positive :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode61 : Eq (assignment 61) Sign.negative :=
    Eq.trans (h_support 21 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode63 : Eq (assignment 63) Sign.negative :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode64 : Eq (assignment 64) Sign.negative :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode6 : Eq (assignment 6) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 40 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode56)
  let hnode13 : Eq (assignment 13) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 48 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode92 : Eq (assignment 92) Sign.negative :=
    Eq.trans (h_support 32 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode93 : Eq (assignment 93) Sign.positive :=
    Eq.trans (h_support 12 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode101 : Eq (assignment 101) Sign.positive :=
    Eq.trans (h_support 33 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode102 : Eq (assignment 102) Sign.negative :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode63)
  let hnode104 : Eq (assignment 104) Sign.negative :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode105 : Eq (assignment 105) Sign.negative :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode106 : Eq (assignment 106) Sign.positive :=
    Eq.trans (h_support 15 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode132 : Eq (assignment 132) Sign.negative :=
    Eq.trans (h_support 145 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode134 : Eq (assignment 134) Sign.negative :=
    Eq.trans (h_support 149 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode162 : Eq (assignment 162) Sign.positive :=
    Eq.trans (h_support 146 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode164 : Eq (assignment 164) Sign.positive :=
    Eq.trans (h_support 150 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode171 : Eq (assignment 171) Sign.negative :=
    Eq.trans (h_support 147 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode173 : Eq (assignment 173) Sign.negative :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode174 : Eq (assignment 174) Sign.positive :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode176 : Eq (assignment 176) Sign.negative :=
    Eq.trans (h_support 152 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode12 : Eq (assignment 12) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 105 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode132)
  let hnode23 : Eq (assignment 23) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 81 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode24 : Eq (assignment 24) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 86 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode93)
  let hnode32 : Eq (assignment 32) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 171 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode173)
  let hnode35 : Eq (assignment 35) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 175 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode176)
  let hnode38 : Eq (assignment 38) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 52 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode93)
  let hnode47 : Eq (assignment 47) Sign.negative :=
    Eq.trans (h_support 9 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode49 : Eq (assignment 49) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 117 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode174)
  let hnode51 : Eq (assignment 51) Sign.positive :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode71 : Eq (assignment 71) Sign.positive :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode72 : Eq (assignment 72) Sign.positive :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode74 : Eq (assignment 74) Sign.positive :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode82 : Eq (assignment 82) Sign.positive :=
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode84 : Eq (assignment 84) Sign.positive :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode86 : Eq (assignment 86) Sign.negative :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode133 : Eq (assignment 133) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 18 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode174)
  let hnode143 : Eq (assignment 143) Sign.positive :=
    Eq.trans (h_support 110 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode152 : Eq (assignment 152) Sign.negative :=
    Eq.trans (h_support 111 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode156 : Eq (assignment 156) Sign.positive :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode197 : Eq (assignment 197) Sign.negative :=
    Eq.trans (h_support 36 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode132)
  let hnode206 : Eq (assignment 206) Sign.positive :=
    Eq.trans (h_support 37 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode132)
  let hnode209 : Eq (assignment 209) Sign.negative :=
    Eq.trans (h_support 38 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode132)
  let hnode210 : Eq (assignment 210) Sign.negative :=
    Eq.trans (h_support 161 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode105)
  let hnode235 : Eq (assignment 235) Sign.positive :=
    Eq.trans (h_support 162 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode105)
  let hnode242 : Eq (assignment 242) Sign.negative :=
    Eq.trans (h_support 163 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode105)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode105)
  let hnode4 : Eq (assignment 4) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 7 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode7 : Eq (assignment 7) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 61 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode8 : Eq (assignment 8) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 65 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode72)
  let hnode16 : Eq (assignment 16) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 131 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode152)
  let hnode58 : Eq (assignment 58) Sign.negative :=
    Eq.trans (h_support 80 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode59 : Eq (assignment 59) Sign.positive :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode24)
  let hnode70 : Eq (assignment 70) Sign.negative :=
    Eq.trans (h_support 93 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode81 : Eq (assignment 81) Sign.negative :=
    Eq.trans (h_support 29 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode85 : Eq (assignment 85) Sign.positive :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode12)
  let hnode95 : Eq (assignment 95) Sign.negative :=
    Eq.trans (h_support 82 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode96 : Eq (assignment 96) Sign.positive :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode24)
  let hnode98 : Eq (assignment 98) Sign.positive :=
    Eq.trans (h_support 83 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode99 : Eq (assignment 99) Sign.positive :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode109 : Eq (assignment 109) Sign.positive :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode35)
  let hnode110 : Eq (assignment 110) Sign.positive :=
    Eq.trans (h_support 96 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode35)
  let hnode112 : Eq (assignment 112) Sign.positive :=
    Eq.trans (h_support 53 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode114 : Eq (assignment 114) Sign.positive :=
    Eq.trans (h_support 54 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode116 : Eq (assignment 116) Sign.negative :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode137 : Eq (assignment 137) Sign.positive :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode140 : Eq (assignment 140) Sign.positive :=
    Eq.trans (h_support 173 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode35)
  let hnode142 : Eq (assignment 142) Sign.negative :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode151 : Eq (assignment 151) Sign.positive :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode12)
  let hnode155 : Eq (assignment 155) Sign.negative :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode163 : Eq (assignment 163) Sign.negative :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode133)
  let hnode167 : Eq (assignment 167) Sign.negative :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode170 : Eq (assignment 170) Sign.negative :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode172 : Eq (assignment 172) Sign.positive :=
    Eq.trans (h_support 17 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode133)
  let hnode178 : Eq (assignment 178) Sign.positive :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode180 : Eq (assignment 180) Sign.negative :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode184 : Eq (assignment 184) Sign.positive :=
    Eq.trans (h_support 118 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode49)
  let hnode191 : Eq (assignment 191) Sign.negative :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode49)
  let hnode194 : Eq (assignment 194) Sign.negative :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode49)
  let hnode198 : Eq (assignment 198) Sign.negative :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode143)
  let hnode217 : Eq (assignment 217) Sign.negative :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode143)
  let hnode219 : Eq (assignment 219) Sign.negative :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode84)
  let hnode221 : Eq (assignment 221) Sign.positive :=
    Eq.trans (h_support 59 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode143)
  let hnode226 : Eq (assignment 226) Sign.positive :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode84)
  let hnode229 : Eq (assignment 229) Sign.positive :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode84)
  let hnode3 : Eq (assignment 3) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 24 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode9 : Eq (assignment 9) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 44 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode59)
  let hnode15 : Eq (assignment 15) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 69 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode81)
  let hnode25 : Eq (assignment 25) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 92 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode99)
  let hnode31 : Eq (assignment 31) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 167 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode172)
  let hnode33 : Eq (assignment 33) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode34 : Eq (assignment 34) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 155 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode178)
  let hnode40 : Eq (assignment 40) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 72 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode42 : Eq (assignment 42) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 190 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode167)
  let hnode45 : Eq (assignment 45) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 98 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode116)
  let hnode50 : Eq (assignment 50) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 157 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode155)
  let hnode52 : Eq (assignment 52) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 139 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode191)
  let hnode53 : Eq (assignment 53) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 198 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode178)
  let hnode57 : Eq (assignment 57) Sign.negative :=
    Eq.trans (h_support 60 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode7)
  let hnode76 : Eq (assignment 76) Sign.negative :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode7)
  let hnode77 : Eq (assignment 77) Sign.negative :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode7)
  let hnode78 : Eq (assignment 78) Sign.negative :=
    Eq.trans (h_support 66 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode79 : Eq (assignment 79) Sign.negative :=
    Eq.trans (h_support 67 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode80 : Eq (assignment 80) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 215 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode221)
  let hnode87 : Eq (assignment 87) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 143 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode226)
  let hnode136 : Eq (assignment 136) Sign.negative :=
    Eq.trans (h_support 129 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode146 : Eq (assignment 146) Sign.negative :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode159 : Eq (assignment 159) Sign.negative :=
    Eq.trans (h_support 132 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode169 : Eq (assignment 169) Sign.positive :=
    Eq.trans (h_support 225 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode99)
  let hnode204 : Eq (assignment 204) Sign.positive :=
    Eq.trans (h_support 226 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode99)
  let hnode205 : Eq (assignment 205) Sign.negative :=
    Eq.trans (h_support 101 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode170)
  let hnode214 : Eq (assignment 214) Sign.positive :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode109)
  let hnode236 : Eq (assignment 236) Sign.negative :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode170)
  let hnode238 : Eq (assignment 238) Sign.positive :=
    Eq.trans (h_support 228 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode99)
  let hnode239 : Eq (assignment 239) Sign.negative :=
    Eq.trans (h_support 182 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode109)
  let hnode240 : Eq (assignment 240) Sign.negative :=
    Eq.trans (h_support 229 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode99)
  let hnode243 : Eq (assignment 243) Sign.negative :=
    Eq.trans (h_support 183 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode109)
  let hnode245 : Eq (assignment 245) Sign.positive :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode109)
  let hnode44 : Eq (assignment 44) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 194 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode169)
  let hnode54 : Eq (assignment 54) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 177 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode159)
  let hnode60 : Eq (assignment 60) Sign.positive :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode65 : Eq (assignment 65) Sign.negative :=
    Eq.trans (h_support 25 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode68 : Eq (assignment 68) Sign.positive :=
    Eq.trans (h_support 26 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode69 : Eq (assignment 69) Sign.positive :=
    Eq.trans (h_support 27 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode88 : Eq (assignment 88) Sign.negative :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode15)
  let hnode89 : Eq (assignment 89) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 218 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode214)
  let hnode94 : Eq (assignment 94) Sign.positive :=
    Eq.trans (h_support 90 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode97 : Eq (assignment 97) Sign.positive :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode111 : Eq (assignment 111) Sign.positive :=
    Eq.trans (h_support 73 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode117 : Eq (assignment 117) Sign.positive :=
    Eq.trans (h_support 74 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode118 : Eq (assignment 118) Sign.positive :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode119 : Eq (assignment 119) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 222 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode239)
  let hnode120 : Eq (assignment 120) Sign.negative :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode135 : Eq (assignment 135) Sign.positive :=
    Eq.trans (h_support 125 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode139 : Eq (assignment 139) Sign.negative :=
    Eq.trans (h_support 153 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode145 : Eq (assignment 145) Sign.positive :=
    Eq.trans (h_support 185 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode147 : Eq (assignment 147) Sign.negative :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode42)
  let hnode150 : Eq (assignment 150) Sign.positive :=
    Eq.trans (h_support 213 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode158 : Eq (assignment 158) Sign.positive :=
    Eq.trans (h_support 128 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode165 : Eq (assignment 165) Sign.positive :=
    Eq.trans (h_support 186 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode166 : Eq (assignment 166) Sign.positive :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode177 : Eq (assignment 177) Sign.negative :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode31)
  let hnode181 : Eq (assignment 181) Sign.negative :=
    Eq.trans (h_support 187 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode183 : Eq (assignment 183) Sign.positive :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode42)
  let hnode185 : Eq (assignment 185) Sign.negative :=
    Eq.trans (h_support 158 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode50)
  let hnode187 : Eq (assignment 187) Sign.negative :=
    Eq.trans (h_support 188 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode189 : Eq (assignment 189) Sign.negative :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode42)
  let hnode192 : Eq (assignment 192) Sign.positive :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode50)
  let hnode195 : Eq (assignment 195) Sign.positive :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode52)
  let hnode201 : Eq (assignment 201) Sign.positive :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode76)
  let hnode202 : Eq (assignment 202) Sign.positive :=
    Eq.trans (h_support 210 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode77)
  let hnode212 : Eq (assignment 212) Sign.positive :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode87)
  let hnode218 : Eq (assignment 218) Sign.negative :=
    Eq.trans (h_support 211 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode77)
  let hnode222 : Eq (assignment 222) Sign.positive :=
    Eq.trans (h_support 208 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode76)
  let hnode223 : Eq (assignment 223) Sign.positive :=
    Eq.trans (h_support 212 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode77)
  let hnode225 : Eq (assignment 225) Sign.positive :=
    Eq.trans (h_support 216 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode230 : Eq (assignment 230) Sign.negative :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode87)
  let hnode149 : Eq (assignment 149) Sign.positive :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode190 : Eq (assignment 190) Sign.positive :=
    Eq.trans (h_support 196 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode193 : Eq (assignment 193) Sign.negative :=
    Eq.trans (h_support 179 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode200 : Eq (assignment 200) Sign.negative :=
    Eq.trans (h_support 76 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode145)
  let hnode216 : Eq (assignment 216) Sign.positive :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode145)
  let hnode228 : Eq (assignment 228) Sign.positive :=
    Eq.trans (h_support 219 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode89)
  let hnode247 : Eq (assignment 247) Sign.negative :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode118)
  let hnode248 : Eq (assignment 248) Sign.positive :=
    Eq.trans (h_support 223 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode119)
  let hnode250 : Eq (assignment 250) Sign.negative :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode118)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C013.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (top_allows (Sign.withNegation globalNegation (assignment 0)))
  let bounded2 := below_succ bounded1 (domain_from_eq (domain := Cases.C013.initial 1) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded3 := below_succ bounded2 (top_allows (Sign.withNegation globalNegation (assignment 2)))
  let bounded4 := below_succ bounded3 (domain_from_eq (domain := Cases.C013.initial 3) (congrArg (Sign.withNegation globalNegation) hnode3) (Eq.refl Bool.true))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C013.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (top_allows (Sign.withNegation globalNegation (assignment 5)))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Cases.C013.initial 6) (congrArg (Sign.withNegation globalNegation) hnode6) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Cases.C013.initial 7) (congrArg (Sign.withNegation globalNegation) hnode7) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C013.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Cases.C013.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (top_allows (Sign.withNegation globalNegation (assignment 10)))
  let bounded12 := below_succ bounded11 (top_allows (Sign.withNegation globalNegation (assignment 11)))
  let bounded13 := below_succ bounded12 (domain_from_eq (domain := Cases.C013.initial 12) (congrArg (Sign.withNegation globalNegation) hnode12) (Eq.refl Bool.true))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C013.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (top_allows (Sign.withNegation globalNegation (assignment 14)))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Cases.C013.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Cases.C013.initial 16) (congrArg (Sign.withNegation globalNegation) hnode16) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (top_allows (Sign.withNegation globalNegation (assignment 17)))
  let bounded19 := below_succ bounded18 (domain_from_eq (domain := Cases.C013.initial 18) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded20 := below_succ bounded19 (top_allows (Sign.withNegation globalNegation (assignment 19)))
  let bounded21 := below_succ bounded20 (top_allows (Sign.withNegation globalNegation (assignment 20)))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C013.initial 21) (congrArg (Sign.withNegation globalNegation) hnode21) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (top_allows (Sign.withNegation globalNegation (assignment 22)))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C013.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C013.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C013.initial 25) (congrArg (Sign.withNegation globalNegation) hnode25) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Cases.C013.initial 26) (congrArg (Sign.withNegation globalNegation) hnode26) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C013.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C013.initial 28) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C013.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (top_allows (Sign.withNegation globalNegation (assignment 30)))
  let bounded32 := below_succ bounded31 (domain_from_eq (domain := Cases.C013.initial 31) (congrArg (Sign.withNegation globalNegation) hnode31) (Eq.refl Bool.true))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C013.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C013.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C013.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (domain_from_eq (domain := Cases.C013.initial 35) (congrArg (Sign.withNegation globalNegation) hnode35) (Eq.refl Bool.true))
  let bounded37 := below_succ bounded36 (top_allows (Sign.withNegation globalNegation (assignment 36)))
  let bounded38 := below_succ bounded37 (top_allows (Sign.withNegation globalNegation (assignment 37)))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C013.initial 38) (congrArg (Sign.withNegation globalNegation) hnode38) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (top_allows (Sign.withNegation globalNegation (assignment 39)))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Cases.C013.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (top_allows (Sign.withNegation globalNegation (assignment 41)))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C013.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (top_allows (Sign.withNegation globalNegation (assignment 43)))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Cases.C013.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C013.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (top_allows (Sign.withNegation globalNegation (assignment 46)))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C013.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (top_allows (Sign.withNegation globalNegation (assignment 48)))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C013.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (domain_from_eq (domain := Cases.C013.initial 50) (congrArg (Sign.withNegation globalNegation) hnode50) (Eq.refl Bool.true))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C013.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (domain_from_eq (domain := Cases.C013.initial 52) (congrArg (Sign.withNegation globalNegation) hnode52) (Eq.refl Bool.true))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Cases.C013.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Cases.C013.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (top_allows (Sign.withNegation globalNegation (assignment 55)))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C013.initial 56) (congrArg (Sign.withNegation globalNegation) hnode56) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C013.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C013.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C013.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C013.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Cases.C013.initial 61) (congrArg (Sign.withNegation globalNegation) hnode61) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C013.initial 62) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C013.initial 63) (congrArg (Sign.withNegation globalNegation) hnode63) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C013.initial 64) (congrArg (Sign.withNegation globalNegation) hnode64) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (domain_from_eq (domain := Cases.C013.initial 65) (congrArg (Sign.withNegation globalNegation) hnode65) (Eq.refl Bool.true))
  let bounded67 := below_succ bounded66 (top_allows (Sign.withNegation globalNegation (assignment 66)))
  let bounded68 := below_succ bounded67 (top_allows (Sign.withNegation globalNegation (assignment 67)))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C013.initial 68) (congrArg (Sign.withNegation globalNegation) hnode68) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C013.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C013.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C013.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C013.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C013.initial 73) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C013.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Cases.C013.initial 75) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Cases.C013.initial 76) (congrArg (Sign.withNegation globalNegation) hnode76) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C013.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C013.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C013.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (domain_from_eq (domain := Cases.C013.initial 80) (congrArg (Sign.withNegation globalNegation) hnode80) (Eq.refl Bool.true))
  let bounded82 := below_succ bounded81 (domain_from_eq (domain := Cases.C013.initial 81) (congrArg (Sign.withNegation globalNegation) hnode81) (Eq.refl Bool.true))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Cases.C013.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (top_allows (Sign.withNegation globalNegation (assignment 83)))
  let bounded85 := below_succ bounded84 (domain_from_eq (domain := Cases.C013.initial 84) (congrArg (Sign.withNegation globalNegation) hnode84) (Eq.refl Bool.true))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C013.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C013.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C013.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Cases.C013.initial 88) (congrArg (Sign.withNegation globalNegation) hnode88) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (domain_from_eq (domain := Cases.C013.initial 89) (congrArg (Sign.withNegation globalNegation) hnode89) (Eq.refl Bool.true))
  let bounded91 := below_succ bounded90 (top_allows (Sign.withNegation globalNegation (assignment 90)))
  let bounded92 := below_succ bounded91 (top_allows (Sign.withNegation globalNegation (assignment 91)))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C013.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C013.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C013.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C013.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C013.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (domain_from_eq (domain := Cases.C013.initial 97) (congrArg (Sign.withNegation globalNegation) hnode97) (Eq.refl Bool.true))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C013.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C013.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C013.initial 100) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C013.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C013.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (top_allows (Sign.withNegation globalNegation (assignment 103)))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C013.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C013.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C013.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (top_allows (Sign.withNegation globalNegation (assignment 107)))
  let bounded109 := below_succ bounded108 (top_allows (Sign.withNegation globalNegation (assignment 108)))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C013.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C013.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C013.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C013.initial 112) (congrArg (Sign.withNegation globalNegation) hnode112) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (top_allows (Sign.withNegation globalNegation (assignment 113)))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C013.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (top_allows (Sign.withNegation globalNegation (assignment 115)))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C013.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C013.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C013.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C013.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C013.initial 120) (congrArg (Sign.withNegation globalNegation) hnode120) (Eq.refl Bool.true))
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
  let bounded132 := below_succ bounded131 (top_allows (Sign.withNegation globalNegation (assignment 131)))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C013.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C013.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C013.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C013.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C013.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C013.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C013.initial 138) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C013.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C013.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (top_allows (Sign.withNegation globalNegation (assignment 141)))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C013.initial 142) (congrArg (Sign.withNegation globalNegation) hnode142) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C013.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (top_allows (Sign.withNegation globalNegation (assignment 144)))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C013.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C013.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C013.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C013.initial 148) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C013.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C013.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C013.initial 151) (congrArg (Sign.withNegation globalNegation) hnode151) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C013.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (top_allows (Sign.withNegation globalNegation (assignment 153)))
  let bounded155 := below_succ bounded154 (domain_from_eq (domain := Cases.C013.initial 154) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C013.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C013.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C013.initial 157) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C013.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C013.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C013.initial 160) (congrArg (Sign.withNegation globalNegation) (h_zero 10 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (top_allows (Sign.withNegation globalNegation (assignment 161)))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Cases.C013.initial 162) (congrArg (Sign.withNegation globalNegation) hnode162) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C013.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C013.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C013.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C013.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C013.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (top_allows (Sign.withNegation globalNegation (assignment 168)))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C013.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C013.initial 170) (congrArg (Sign.withNegation globalNegation) hnode170) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C013.initial 171) (congrArg (Sign.withNegation globalNegation) hnode171) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C013.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C013.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C013.initial 174) (congrArg (Sign.withNegation globalNegation) hnode174) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C013.initial 175) (congrArg (Sign.withNegation globalNegation) (h_zero 11 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C013.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Cases.C013.initial 177) (congrArg (Sign.withNegation globalNegation) hnode177) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C013.initial 178) (congrArg (Sign.withNegation globalNegation) hnode178) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C013.initial 179) (congrArg (Sign.withNegation globalNegation) (h_zero 12 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C013.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C013.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (top_allows (Sign.withNegation globalNegation (assignment 182)))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C013.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Cases.C013.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C013.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (top_allows (Sign.withNegation globalNegation (assignment 186)))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C013.initial 187) (congrArg (Sign.withNegation globalNegation) hnode187) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C013.initial 188) (congrArg (Sign.withNegation globalNegation) (h_zero 13 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C013.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C013.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C013.initial 191) (congrArg (Sign.withNegation globalNegation) hnode191) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C013.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C013.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Cases.C013.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C013.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (top_allows (Sign.withNegation globalNegation (assignment 196)))
  let bounded198 := below_succ bounded197 (domain_from_eq (domain := Cases.C013.initial 197) (congrArg (Sign.withNegation globalNegation) hnode197) (Eq.refl Bool.true))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Cases.C013.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (top_allows (Sign.withNegation globalNegation (assignment 199)))
  let bounded201 := below_succ bounded200 (domain_from_eq (domain := Cases.C013.initial 200) (congrArg (Sign.withNegation globalNegation) hnode200) (Eq.refl Bool.true))
  let bounded202 := below_succ bounded201 (domain_from_eq (domain := Cases.C013.initial 201) (congrArg (Sign.withNegation globalNegation) hnode201) (Eq.refl Bool.true))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C013.initial 202) (congrArg (Sign.withNegation globalNegation) hnode202) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (top_allows (Sign.withNegation globalNegation (assignment 203)))
  let bounded205 := below_succ bounded204 (domain_from_eq (domain := Cases.C013.initial 204) (congrArg (Sign.withNegation globalNegation) hnode204) (Eq.refl Bool.true))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C013.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Cases.C013.initial 206) (congrArg (Sign.withNegation globalNegation) hnode206) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (top_allows (Sign.withNegation globalNegation (assignment 207)))
  let bounded209 := below_succ bounded208 (top_allows (Sign.withNegation globalNegation (assignment 208)))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C013.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C013.initial 210) (congrArg (Sign.withNegation globalNegation) hnode210) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (top_allows (Sign.withNegation globalNegation (assignment 211)))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C013.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (top_allows (Sign.withNegation globalNegation (assignment 213)))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C013.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (top_allows (Sign.withNegation globalNegation (assignment 215)))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C013.initial 216) (congrArg (Sign.withNegation globalNegation) hnode216) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C013.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C013.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Cases.C013.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (top_allows (Sign.withNegation globalNegation (assignment 220)))
  let bounded222 := below_succ bounded221 (domain_from_eq (domain := Cases.C013.initial 221) (congrArg (Sign.withNegation globalNegation) hnode221) (Eq.refl Bool.true))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C013.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C013.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C013.initial 224) (congrArg (Sign.withNegation globalNegation) (h_zero 14 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C013.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C013.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (top_allows (Sign.withNegation globalNegation (assignment 227)))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C013.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Cases.C013.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C013.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (top_allows (Sign.withNegation globalNegation (assignment 231)))
  let bounded233 := below_succ bounded232 (top_allows (Sign.withNegation globalNegation (assignment 232)))
  let bounded234 := below_succ bounded233 (top_allows (Sign.withNegation globalNegation (assignment 233)))
  let bounded235 := below_succ bounded234 (top_allows (Sign.withNegation globalNegation (assignment 234)))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C013.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (domain_from_eq (domain := Cases.C013.initial 236) (congrArg (Sign.withNegation globalNegation) hnode236) (Eq.refl Bool.true))
  let bounded238 := below_succ bounded237 (top_allows (Sign.withNegation globalNegation (assignment 237)))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C013.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Cases.C013.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (domain_from_eq (domain := Cases.C013.initial 240) (congrArg (Sign.withNegation globalNegation) hnode240) (Eq.refl Bool.true))
  let bounded242 := below_succ bounded241 (top_allows (Sign.withNegation globalNegation (assignment 241)))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C013.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C013.initial 243) (congrArg (Sign.withNegation globalNegation) hnode243) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C013.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C013.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (top_allows (Sign.withNegation globalNegation (assignment 246)))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C013.initial 247) (congrArg (Sign.withNegation globalNegation) hnode247) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C013.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (top_allows (Sign.withNegation globalNegation (assignment 249)))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Cases.C013.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (top_allows (Sign.withNegation globalNegation (assignment 251)))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C013.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C013
#print axioms Papers.RationalityTen.PureGP.Initializers.C013.support_sign_contradiction
