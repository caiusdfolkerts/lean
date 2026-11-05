module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C034

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C034
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 1
def globalNegation : Bool := Bool.true
def edgeTable : Table SupportEdge := (Table.node 117 (Table.node 58 (Table.node 29 (Table.node 14 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 1 21 Bool.true)) (Table.node 2 (Table.leaf (SupportEdge.mk 1 26 Bool.false)) (Table.leaf (SupportEdge.mk 1 27 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 1 29 Bool.false)) (Table.leaf (SupportEdge.mk 4 24 Bool.true))) (Table.node 6 (Table.leaf (SupportEdge.mk 4 31 Bool.true)) (Table.leaf (SupportEdge.mk 4 33 Bool.true))))) (Table.node 10 (Table.node 8 (Table.leaf (SupportEdge.mk 4 35 Bool.false)) (Table.node 9 (Table.leaf (SupportEdge.mk 13 38 Bool.false)) (Table.leaf (SupportEdge.mk 13 47 Bool.true)))) (Table.node 12 (Table.node 11 (Table.leaf (SupportEdge.mk 13 49 Bool.true)) (Table.leaf (SupportEdge.mk 13 51 Bool.false))) (Table.node 13 (Table.leaf (SupportEdge.mk 63 93 Bool.true)) (Table.leaf (SupportEdge.mk 63 102 Bool.false)))))) (Table.node 21 (Table.node 17 (Table.node 15 (Table.leaf (SupportEdge.mk 63 104 Bool.false)) (Table.node 16 (Table.leaf (SupportEdge.mk 63 106 Bool.true)) (Table.leaf (SupportEdge.mk 133 163 Bool.true)))) (Table.node 19 (Table.node 18 (Table.leaf (SupportEdge.mk 133 172 Bool.false)) (Table.leaf (SupportEdge.mk 133 174 Bool.false))) (Table.node 20 (Table.leaf (SupportEdge.mk 133 176 Bool.true)) (Table.leaf (SupportEdge.mk 8 58 Bool.true))))) (Table.node 25 (Table.node 23 (Table.node 22 (Table.leaf (SupportEdge.mk 8 72 Bool.false)) (Table.leaf (SupportEdge.mk 8 75 Bool.false))) (Table.node 24 (Table.leaf (SupportEdge.mk 8 78 Bool.true)) (Table.leaf (SupportEdge.mk 10 60 Bool.true)))) (Table.node 27 (Table.node 26 (Table.leaf (SupportEdge.mk 10 74 Bool.false)) (Table.leaf (SupportEdge.mk 10 77 Bool.false))) (Table.node 28 (Table.leaf (SupportEdge.mk 10 80 Bool.false)) (Table.leaf (SupportEdge.mk 19 69 Bool.true))))))) (Table.node 43 (Table.node 36 (Table.node 32 (Table.node 30 (Table.leaf (SupportEdge.mk 19 85 Bool.true)) (Table.node 31 (Table.leaf (SupportEdge.mk 19 88 Bool.true)) (Table.leaf (SupportEdge.mk 19 90 Bool.false)))) (Table.node 34 (Table.node 33 (Table.leaf (SupportEdge.mk 44 99 Bool.false)) (Table.leaf (SupportEdge.mk 44 115 Bool.true))) (Table.node 35 (Table.leaf (SupportEdge.mk 44 118 Bool.true)) (Table.leaf (SupportEdge.mk 44 120 Bool.false))))) (Table.node 39 (Table.node 37 (Table.leaf (SupportEdge.mk 149 204 Bool.true)) (Table.node 38 (Table.leaf (SupportEdge.mk 149 220 Bool.false)) (Table.leaf (SupportEdge.mk 149 223 Bool.false)))) (Table.node 41 (Table.node 40 (Table.leaf (SupportEdge.mk 149 225 Bool.true)) (Table.leaf (SupportEdge.mk 21 56 Bool.false))) (Table.node 42 (Table.leaf (SupportEdge.mk 21 91 Bool.true)) (Table.leaf (SupportEdge.mk 21 93 Bool.true)))))) (Table.node 50 (Table.node 46 (Table.node 44 (Table.leaf (SupportEdge.mk 21 94 Bool.true)) (Table.node 45 (Table.leaf (SupportEdge.mk 23 58 Bool.false)) (Table.leaf (SupportEdge.mk 23 95 Bool.false)))) (Table.node 48 (Table.node 47 (Table.leaf (SupportEdge.mk 23 98 Bool.true)) (Table.leaf (SupportEdge.mk 23 99 Bool.true))) (Table.node 49 (Table.leaf (SupportEdge.mk 27 62 Bool.false)) (Table.leaf (SupportEdge.mk 27 101 Bool.false))))) (Table.node 54 (Table.node 52 (Table.node 51 (Table.leaf (SupportEdge.mk 27 104 Bool.true)) (Table.leaf (SupportEdge.mk 27 105 Bool.true))) (Table.node 53 (Table.leaf (SupportEdge.mk 37 72 Bool.false)) (Table.leaf (SupportEdge.mk 37 111 Bool.false)))) (Table.node 56 (Table.node 55 (Table.leaf (SupportEdge.mk 37 114 Bool.true)) (Table.leaf (SupportEdge.mk 37 115 Bool.true))) (Table.node 57 (Table.leaf (SupportEdge.mk 162 197 Bool.false)) (Table.leaf (SupportEdge.mk 162 231 Bool.true)))))))) (Table.node 87 (Table.node 72 (Table.node 65 (Table.node 61 (Table.node 59 (Table.leaf (SupportEdge.mk 162 234 Bool.false)) (Table.node 60 (Table.leaf (SupportEdge.mk 162 235 Bool.false)) (Table.leaf (SupportEdge.mk 33 68 Bool.false)))) (Table.node 63 (Table.node 62 (Table.leaf (SupportEdge.mk 33 98 Bool.true)) (Table.leaf (SupportEdge.mk 33 104 Bool.true))) (Table.node 64 (Table.leaf (SupportEdge.mk 33 107 Bool.true)) (Table.leaf (SupportEdge.mk 34 69 Bool.false))))) (Table.node 68 (Table.node 66 (Table.leaf (SupportEdge.mk 34 99 Bool.true)) (Table.node 67 (Table.leaf (SupportEdge.mk 34 105 Bool.true)) (Table.leaf (SupportEdge.mk 34 108 Bool.true)))) (Table.node 70 (Table.node 69 (Table.leaf (SupportEdge.mk 35 70 Bool.false)) (Table.leaf (SupportEdge.mk 35 100 Bool.true))) (Table.node 71 (Table.leaf (SupportEdge.mk 35 106 Bool.true)) (Table.leaf (SupportEdge.mk 35 109 Bool.true)))))) (Table.node 79 (Table.node 75 (Table.node 73 (Table.leaf (SupportEdge.mk 55 90 Bool.false)) (Table.node 74 (Table.leaf (SupportEdge.mk 55 120 Bool.false)) (Table.leaf (SupportEdge.mk 55 124 Bool.false)))) (Table.node 77 (Table.node 76 (Table.leaf (SupportEdge.mk 55 125 Bool.false)) (Table.leaf (SupportEdge.mk 180 215 Bool.false))) (Table.node 78 (Table.leaf (SupportEdge.mk 180 240 Bool.true)) (Table.leaf (SupportEdge.mk 180 244 Bool.true))))) (Table.node 83 (Table.node 81 (Table.node 80 (Table.leaf (SupportEdge.mk 180 245 Bool.true)) (Table.leaf (SupportEdge.mk 36 71 Bool.false))) (Table.node 82 (Table.leaf (SupportEdge.mk 36 91 Bool.false)) (Table.leaf (SupportEdge.mk 36 111 Bool.true)))) (Table.node 85 (Table.node 84 (Table.leaf (SupportEdge.mk 36 113 Bool.true)) (Table.leaf (SupportEdge.mk 38 73 Bool.false))) (Table.node 86 (Table.leaf (SupportEdge.mk 38 93 Bool.false)) (Table.leaf (SupportEdge.mk 38 114 Bool.false))))))) (Table.node 102 (Table.node 94 (Table.node 90 (Table.node 88 (Table.leaf (SupportEdge.mk 38 116 Bool.true)) (Table.node 89 (Table.leaf (SupportEdge.mk 41 76 Bool.false)) (Table.leaf (SupportEdge.mk 41 96 Bool.false)))) (Table.node 92 (Table.node 91 (Table.leaf (SupportEdge.mk 41 117 Bool.false)) (Table.leaf (SupportEdge.mk 41 119 Bool.true))) (Table.node 93 (Table.leaf (SupportEdge.mk 47 82 Bool.false)) (Table.leaf (SupportEdge.mk 47 102 Bool.false))))) (Table.node 98 (Table.node 96 (Table.node 95 (Table.leaf (SupportEdge.mk 47 121 Bool.false)) (Table.leaf (SupportEdge.mk 47 123 Bool.true))) (Table.node 97 (Table.leaf (SupportEdge.mk 182 217 Bool.false)) (Table.leaf (SupportEdge.mk 182 232 Bool.false)))) (Table.node 100 (Table.node 99 (Table.leaf (SupportEdge.mk 182 246 Bool.true)) (Table.leaf (SupportEdge.mk 182 248 Bool.false))) (Table.node 101 (Table.leaf (SupportEdge.mk 45 80 Bool.false)) (Table.leaf (SupportEdge.mk 45 100 Bool.false)))))) (Table.node 109 (Table.node 105 (Table.node 103 (Table.leaf (SupportEdge.mk 45 116 Bool.true)) (Table.node 104 (Table.leaf (SupportEdge.mk 45 119 Bool.true)) (Table.leaf (SupportEdge.mk 45 120 Bool.true)))) (Table.node 107 (Table.node 106 (Table.leaf (SupportEdge.mk 4 129 Bool.true)) (Table.leaf (SupportEdge.mk 4 133 Bool.true))) (Table.node 108 (Table.leaf (SupportEdge.mk 4 136 Bool.true)) (Table.leaf (SupportEdge.mk 4 138 Bool.true))))) (Table.node 113 (Table.node 111 (Table.node 110 (Table.leaf (SupportEdge.mk 5 130 Bool.true)) (Table.leaf (SupportEdge.mk 5 134 Bool.true))) (Table.node 112 (Table.leaf (SupportEdge.mk 5 137 Bool.true)) (Table.leaf (SupportEdge.mk 5 139 Bool.true)))) (Table.node 115 (Table.node 114 (Table.leaf (SupportEdge.mk 20 150 Bool.false)) (Table.leaf (SupportEdge.mk 20 156 Bool.false))) (Table.node 116 (Table.leaf (SupportEdge.mk 20 159 Bool.false)) (Table.leaf (SupportEdge.mk 20 160 Bool.false))))))))) (Table.node 176 (Table.node 146 (Table.node 131 (Table.node 124 (Table.node 120 (Table.node 118 (Table.leaf (SupportEdge.mk 35 170 Bool.false)) (Table.node 119 (Table.leaf (SupportEdge.mk 35 176 Bool.false)) (Table.leaf (SupportEdge.mk 35 179 Bool.false)))) (Table.node 122 (Table.node 121 (Table.leaf (SupportEdge.mk 35 180 Bool.false)) (Table.leaf (SupportEdge.mk 70 205 Bool.false))) (Table.node 123 (Table.leaf (SupportEdge.mk 70 211 Bool.false)) (Table.leaf (SupportEdge.mk 70 214 Bool.false))))) (Table.node 127 (Table.node 125 (Table.leaf (SupportEdge.mk 70 215 Bool.false)) (Table.node 126 (Table.leaf (SupportEdge.mk 7 127 Bool.false)) (Table.leaf (SupportEdge.mk 7 141 Bool.true)))) (Table.node 129 (Table.node 128 (Table.leaf (SupportEdge.mk 7 145 Bool.false)) (Table.leaf (SupportEdge.mk 7 147 Bool.false))) (Table.node 130 (Table.leaf (SupportEdge.mk 9 129 Bool.false)) (Table.leaf (SupportEdge.mk 9 143 Bool.true)))))) (Table.node 138 (Table.node 134 (Table.node 132 (Table.leaf (SupportEdge.mk 9 148 Bool.true)) (Table.node 133 (Table.leaf (SupportEdge.mk 9 150 Bool.false)) (Table.leaf (SupportEdge.mk 16 136 Bool.false)))) (Table.node 136 (Table.node 135 (Table.leaf (SupportEdge.mk 16 152 Bool.false)) (Table.leaf (SupportEdge.mk 16 157 Bool.true))) (Table.node 137 (Table.leaf (SupportEdge.mk 16 159 Bool.false)) (Table.leaf (SupportEdge.mk 41 166 Bool.true))))) (Table.node 142 (Table.node 140 (Table.node 139 (Table.leaf (SupportEdge.mk 41 182 Bool.false)) (Table.leaf (SupportEdge.mk 41 187 Bool.true))) (Table.node 141 (Table.leaf (SupportEdge.mk 41 189 Bool.false)) (Table.leaf (SupportEdge.mk 76 201 Bool.true)))) (Table.node 144 (Table.node 143 (Table.leaf (SupportEdge.mk 76 217 Bool.false)) (Table.leaf (SupportEdge.mk 76 222 Bool.true))) (Table.node 145 (Table.leaf (SupportEdge.mk 76 224 Bool.false)) (Table.leaf (SupportEdge.mk 15 135 Bool.false))))))) (Table.node 161 (Table.node 153 (Table.node 149 (Table.node 147 (Table.leaf (SupportEdge.mk 15 145 Bool.false)) (Table.node 148 (Table.leaf (SupportEdge.mk 15 151 Bool.false)) (Table.leaf (SupportEdge.mk 15 157 Bool.false)))) (Table.node 151 (Table.node 150 (Table.leaf (SupportEdge.mk 17 137 Bool.false)) (Table.leaf (SupportEdge.mk 17 147 Bool.false))) (Table.node 152 (Table.leaf (SupportEdge.mk 17 153 Bool.false)) (Table.leaf (SupportEdge.mk 17 159 Bool.true))))) (Table.node 157 (Table.node 155 (Table.node 154 (Table.leaf (SupportEdge.mk 19 139 Bool.false)) (Table.leaf (SupportEdge.mk 19 149 Bool.false))) (Table.node 156 (Table.leaf (SupportEdge.mk 19 155 Bool.false)) (Table.leaf (SupportEdge.mk 19 160 Bool.true)))) (Table.node 159 (Table.node 158 (Table.leaf (SupportEdge.mk 53 178 Bool.true)) (Table.leaf (SupportEdge.mk 53 188 Bool.true))) (Table.node 160 (Table.leaf (SupportEdge.mk 53 192 Bool.true)) (Table.leaf (SupportEdge.mk 53 195 Bool.true)))))) (Table.node 168 (Table.node 164 (Table.node 162 (Table.leaf (SupportEdge.mk 88 213 Bool.true)) (Table.node 163 (Table.leaf (SupportEdge.mk 88 223 Bool.true)) (Table.leaf (SupportEdge.mk 88 227 Bool.true)))) (Table.node 166 (Table.node 165 (Table.leaf (SupportEdge.mk 88 230 Bool.true)) (Table.leaf (SupportEdge.mk 26 131 Bool.true))) (Table.node 167 (Table.leaf (SupportEdge.mk 26 161 Bool.false)) (Table.leaf (SupportEdge.mk 26 171 Bool.false))))) (Table.node 172 (Table.node 170 (Table.node 169 (Table.leaf (SupportEdge.mk 26 172 Bool.false)) (Table.leaf (SupportEdge.mk 29 134 Bool.true))) (Table.node 171 (Table.leaf (SupportEdge.mk 29 164 Bool.false)) (Table.leaf (SupportEdge.mk 29 175 Bool.true)))) (Table.node 174 (Table.node 173 (Table.leaf (SupportEdge.mk 29 176 Bool.true)) (Table.leaf (SupportEdge.mk 32 137 Bool.true))) (Table.node 175 (Table.leaf (SupportEdge.mk 32 167 Bool.false)) (Table.leaf (SupportEdge.mk 32 178 Bool.true)))))))) (Table.node 205 (Table.node 190 (Table.node 183 (Table.node 179 (Table.node 177 (Table.leaf (SupportEdge.mk 32 179 Bool.true)) (Table.node 178 (Table.leaf (SupportEdge.mk 48 153 Bool.true)) (Table.leaf (SupportEdge.mk 48 183 Bool.true)))) (Table.node 181 (Table.node 180 (Table.leaf (SupportEdge.mk 48 192 Bool.true)) (Table.leaf (SupportEdge.mk 48 193 Bool.true))) (Table.node 182 (Table.leaf (SupportEdge.mk 103 208 Bool.false)) (Table.leaf (SupportEdge.mk 103 233 Bool.true))))) (Table.node 186 (Table.node 184 (Table.leaf (SupportEdge.mk 103 242 Bool.true)) (Table.node 185 (Table.leaf (SupportEdge.mk 103 243 Bool.true)) (Table.leaf (SupportEdge.mk 47 152 Bool.true)))) (Table.node 188 (Table.node 187 (Table.leaf (SupportEdge.mk 47 172 Bool.true)) (Table.leaf (SupportEdge.mk 47 182 Bool.true))) (Table.node 189 (Table.leaf (SupportEdge.mk 47 191 Bool.true)) (Table.leaf (SupportEdge.mk 47 193 Bool.false)))))) (Table.node 197 (Table.node 193 (Table.node 191 (Table.leaf (SupportEdge.mk 71 141 Bool.false)) (Table.node 192 (Table.leaf (SupportEdge.mk 71 196 Bool.true)) (Table.leaf (SupportEdge.mk 71 217 Bool.false)))) (Table.node 195 (Table.node 194 (Table.leaf (SupportEdge.mk 71 218 Bool.false)) (Table.leaf (SupportEdge.mk 72 142 Bool.false))) (Table.node 196 (Table.leaf (SupportEdge.mk 72 197 Bool.true)) (Table.leaf (SupportEdge.mk 72 219 Bool.false))))) (Table.node 201 (Table.node 199 (Table.node 198 (Table.leaf (SupportEdge.mk 72 220 Bool.false)) (Table.leaf (SupportEdge.mk 75 145 Bool.false))) (Table.node 200 (Table.leaf (SupportEdge.mk 75 200 Bool.true)) (Table.leaf (SupportEdge.mk 75 222 Bool.false)))) (Table.node 203 (Table.node 202 (Table.leaf (SupportEdge.mk 75 223 Bool.false)) (Table.leaf (SupportEdge.mk 81 151 Bool.false))) (Table.node 204 (Table.leaf (SupportEdge.mk 81 206 Bool.true)) (Table.leaf (SupportEdge.mk 81 226 Bool.false))))))) (Table.node 220 (Table.node 212 (Table.node 208 (Table.node 206 (Table.leaf (SupportEdge.mk 81 227 Bool.false)) (Table.node 207 (Table.leaf (SupportEdge.mk 111 181 Bool.false)) (Table.leaf (SupportEdge.mk 111 231 Bool.false)))) (Table.node 210 (Table.node 209 (Table.leaf (SupportEdge.mk 111 246 Bool.false)) (Table.leaf (SupportEdge.mk 111 247 Bool.false))) (Table.node 211 (Table.leaf (SupportEdge.mk 80 150 Bool.false)) (Table.leaf (SupportEdge.mk 80 205 Bool.true))))) (Table.node 216 (Table.node 214 (Table.node 213 (Table.leaf (SupportEdge.mk 80 221 Bool.false)) (Table.leaf (SupportEdge.mk 80 224 Bool.false))) (Table.node 215 (Table.leaf (SupportEdge.mk 80 225 Bool.false)) (Table.leaf (SupportEdge.mk 101 171 Bool.false)))) (Table.node 218 (Table.node 217 (Table.leaf (SupportEdge.mk 101 206 Bool.false)) (Table.leaf (SupportEdge.mk 101 231 Bool.true))) (Table.node 219 (Table.leaf (SupportEdge.mk 101 241 Bool.false)) (Table.leaf (SupportEdge.mk 103 173 Bool.false)))))) (Table.node 227 (Table.node 223 (Table.node 221 (Table.leaf (SupportEdge.mk 103 208 Bool.false)) (Table.node 222 (Table.leaf (SupportEdge.mk 103 233 Bool.true)) (Table.leaf (SupportEdge.mk 103 243 Bool.true)))) (Table.node 225 (Table.node 224 (Table.leaf (SupportEdge.mk 105 175 Bool.false)) (Table.leaf (SupportEdge.mk 105 210 Bool.false))) (Table.node 226 (Table.leaf (SupportEdge.mk 105 235 Bool.true)) (Table.leaf (SupportEdge.mk 105 244 Bool.true))))) (Table.node 231 (Table.node 229 (Table.node 228 (Table.leaf (SupportEdge.mk 108 178 Bool.false)) (Table.leaf (SupportEdge.mk 108 213 Bool.false))) (Table.node 230 (Table.leaf (SupportEdge.mk 108 238 Bool.true)) (Table.leaf (SupportEdge.mk 108 245 Bool.true)))) (Table.node 233 (Table.node 232 (Table.leaf (SupportEdge.mk 122 192 Bool.false)) (Table.leaf (SupportEdge.mk 122 227 Bool.false))) (Table.node 234 (Table.leaf (SupportEdge.mk 122 247 Bool.false)) (Table.leaf (SupportEdge.mk 122 251 Bool.true))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf 28) (Table.node 2 (Table.leaf 79) (Table.leaf 92))) (Table.node 5 (Table.node 4 (Table.leaf 103) (Table.leaf 110)) (Table.node 6 (Table.leaf 112) (Table.leaf 140)))) (Table.node 11 (Table.node 9 (Table.node 8 (Table.leaf 146) (Table.leaf 158)) (Table.node 10 (Table.leaf 173) (Table.leaf 208))) (Table.node 13 (Table.node 12 (Table.leaf 216) (Table.leaf 233)) (Table.node 14 (Table.leaf 242) (Table.leaf 243)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 235 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 15 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C034.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode21 : Eq (assignment 21) Sign.negative :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode26 : Eq (assignment 26) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode27 : Eq (assignment 27) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode29 : Eq (assignment 29) Sign.positive :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode56 : Eq (assignment 56) Sign.negative :=
    Eq.trans (h_support 40 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode21)
  let hnode62 : Eq (assignment 62) Sign.positive :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode91 : Eq (assignment 91) Sign.positive :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode93 : Eq (assignment 93) Sign.positive :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode94 : Eq (assignment 94) Sign.positive :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode101 : Eq (assignment 101) Sign.positive :=
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode104 : Eq (assignment 104) Sign.negative :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode105 : Eq (assignment 105) Sign.negative :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode131 : Eq (assignment 131) Sign.negative :=
    Eq.trans (h_support 165 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode134 : Eq (assignment 134) Sign.negative :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode161 : Eq (assignment 161) Sign.positive :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode164 : Eq (assignment 164) Sign.positive :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode171 : Eq (assignment 171) Sign.positive :=
    Eq.trans (h_support 167 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode172 : Eq (assignment 172) Sign.positive :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode175 : Eq (assignment 175) Sign.negative :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode176 : Eq (assignment 176) Sign.negative :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode5 : Eq (assignment 5) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 110 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode134)
  let hnode33 : Eq (assignment 33) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 62 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode104)
  let hnode34 : Eq (assignment 34) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 66 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode105)
  let hnode35 : Eq (assignment 35) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 118 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode176)
  let hnode36 : Eq (assignment 36) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 81 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode38 : Eq (assignment 38) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 85 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode93)
  let hnode47 : Eq (assignment 47) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 186 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode172)
  let hnode63 : Eq (assignment 63) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 12 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode93)
  let hnode133 : Eq (assignment 133) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 17 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode172)
  let hnode206 : Eq (assignment 206) Sign.positive :=
    Eq.trans (h_support 216 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode101)
  let hnode210 : Eq (assignment 210) Sign.negative :=
    Eq.trans (h_support 224 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode105)
  let hnode231 : Eq (assignment 231) Sign.negative :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode101)
  let hnode235 : Eq (assignment 235) Sign.positive :=
    Eq.trans (h_support 225 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode105)
  let hnode241 : Eq (assignment 241) Sign.positive :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode101)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 226 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode105)
  let hnode4 : Eq (assignment 4) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 106 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode133)
  let hnode13 : Eq (assignment 13) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 8 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode68 : Eq (assignment 68) Sign.positive :=
    Eq.trans (h_support 60 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode69 : Eq (assignment 69) Sign.positive :=
    Eq.trans (h_support 64 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode70 : Eq (assignment 70) Sign.negative :=
    Eq.trans (h_support 68 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode71 : Eq (assignment 71) Sign.positive :=
    Eq.trans (h_support 80 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode73 : Eq (assignment 73) Sign.positive :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode81 : Eq (assignment 81) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 203 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode206)
  let hnode82 : Eq (assignment 82) Sign.negative :=
    Eq.trans (h_support 92 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode98 : Eq (assignment 98) Sign.negative :=
    Eq.trans (h_support 61 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode99 : Eq (assignment 99) Sign.negative :=
    Eq.trans (h_support 65 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode100 : Eq (assignment 100) Sign.positive :=
    Eq.trans (h_support 69 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode35)
  let hnode102 : Eq (assignment 102) Sign.negative :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode63)
  let hnode106 : Eq (assignment 106) Sign.positive :=
    Eq.trans (h_support 15 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode107 : Eq (assignment 107) Sign.negative :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode108 : Eq (assignment 108) Sign.negative :=
    Eq.trans (h_support 67 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode109 : Eq (assignment 109) Sign.positive :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode35)
  let hnode111 : Eq (assignment 111) Sign.negative :=
    Eq.trans (h_support 82 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode36)
  let hnode113 : Eq (assignment 113) Sign.negative :=
    Eq.trans (h_support 83 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode36)
  let hnode114 : Eq (assignment 114) Sign.positive :=
    Eq.trans (h_support 86 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode116 : Eq (assignment 116) Sign.negative :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode121 : Eq (assignment 121) Sign.negative :=
    Eq.trans (h_support 94 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode123 : Eq (assignment 123) Sign.positive :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode130 : Eq (assignment 130) Sign.negative :=
    Eq.trans (h_support 109 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode137 : Eq (assignment 137) Sign.negative :=
    Eq.trans (h_support 111 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode139 : Eq (assignment 139) Sign.negative :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode152 : Eq (assignment 152) Sign.positive :=
    Eq.trans (h_support 185 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode162 : Eq (assignment 162) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 57 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode231)
  let hnode163 : Eq (assignment 163) Sign.negative :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode133)
  let hnode170 : Eq (assignment 170) Sign.negative :=
    Eq.trans (h_support 117 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode174 : Eq (assignment 174) Sign.positive :=
    Eq.trans (h_support 18 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode133)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode180 : Eq (assignment 180) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 78 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode244)
  let hnode182 : Eq (assignment 182) Sign.positive :=
    Eq.trans (h_support 187 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode191 : Eq (assignment 191) Sign.positive :=
    Eq.trans (h_support 188 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode193 : Eq (assignment 193) Sign.negative :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode16 : Eq (assignment 16) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 134 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode152)
  let hnode17 : Eq (assignment 17) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 149 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode137)
  let hnode19 : Eq (assignment 19) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 28 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode69)
  let hnode23 : Eq (assignment 23) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 46 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode98)
  let hnode24 : Eq (assignment 24) Sign.positive :=
    Eq.trans (h_support 4 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode31 : Eq (assignment 31) Sign.positive :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode32 : Eq (assignment 32) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 173 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode137)
  let hnode37 : Eq (assignment 37) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 53 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode41 : Eq (assignment 41) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 138 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode182)
  let hnode44 : Eq (assignment 44) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 32 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode99)
  let hnode45 : Eq (assignment 45) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 102 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode116)
  let hnode48 : Eq (assignment 48) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 180 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode193)
  let hnode49 : Eq (assignment 49) Sign.negative :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode51 : Eq (assignment 51) Sign.positive :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode129 : Eq (assignment 129) Sign.positive :=
    Eq.trans (h_support 105 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode136 : Eq (assignment 136) Sign.positive :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode138 : Eq (assignment 138) Sign.positive :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode141 : Eq (assignment 141) Sign.positive :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode151 : Eq (assignment 151) Sign.negative :=
    Eq.trans (h_support 202 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode81)
  let hnode178 : Eq (assignment 178) Sign.negative :=
    Eq.trans (h_support 227 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode108)
  let hnode181 : Eq (assignment 181) Sign.negative :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode196 : Eq (assignment 196) Sign.negative :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode71)
  let hnode197 : Eq (assignment 197) Sign.positive :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode162)
  let hnode205 : Eq (assignment 205) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode211 : Eq (assignment 211) Sign.negative :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode213 : Eq (assignment 213) Sign.negative :=
    Eq.trans (h_support 228 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode108)
  let hnode214 : Eq (assignment 214) Sign.negative :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode215 : Eq (assignment 215) Sign.negative :=
    Eq.trans (h_support 76 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode180)
  let hnode217 : Eq (assignment 217) Sign.positive :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode218 : Eq (assignment 218) Sign.positive :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode226 : Eq (assignment 226) Sign.negative :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode81)
  let hnode227 : Eq (assignment 227) Sign.negative :=
    Eq.trans (h_support 205 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode81)
  let hnode232 : Eq (assignment 232) Sign.positive :=
    Eq.trans (h_support 97 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode182)
  let hnode234 : Eq (assignment 234) Sign.positive :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode162)
  let hnode238 : Eq (assignment 238) Sign.positive :=
    Eq.trans (h_support 229 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode108)
  let hnode240 : Eq (assignment 240) Sign.positive :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode180)
  let hnode245 : Eq (assignment 245) Sign.positive :=
    Eq.trans (h_support 230 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode108)
  let hnode246 : Eq (assignment 246) Sign.negative :=
    Eq.trans (h_support 208 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode247 : Eq (assignment 247) Sign.negative :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode248 : Eq (assignment 248) Sign.positive :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode182)
  let hnode7 : Eq (assignment 7) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 126 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode141)
  let hnode9 : Eq (assignment 9) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 129 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode129)
  let hnode15 : Eq (assignment 15) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 147 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode151)
  let hnode53 : Eq (assignment 53) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 157 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode178)
  let hnode58 : Eq (assignment 58) Sign.positive :=
    Eq.trans (h_support 44 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode72 : Eq (assignment 72) Sign.negative :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode76 : Eq (assignment 76) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 142 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode217)
  let hnode80 : Eq (assignment 80) Sign.positive :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode85 : Eq (assignment 85) Sign.positive :=
    Eq.trans (h_support 29 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode19)
  let hnode88 : Eq (assignment 88) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 163 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode227)
  let hnode90 : Eq (assignment 90) Sign.negative :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode95 : Eq (assignment 95) Sign.positive :=
    Eq.trans (h_support 45 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode96 : Eq (assignment 96) Sign.positive :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode115 : Eq (assignment 115) Sign.positive :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode37)
  let hnode117 : Eq (assignment 117) Sign.positive :=
    Eq.trans (h_support 90 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode118 : Eq (assignment 118) Sign.positive :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode119 : Eq (assignment 119) Sign.negative :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode120 : Eq (assignment 120) Sign.negative :=
    Eq.trans (h_support 104 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode122 : Eq (assignment 122) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 233 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode247)
  let hnode147 : Eq (assignment 147) Sign.negative :=
    Eq.trans (h_support 150 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode149 : Eq (assignment 149) Sign.negative :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode153 : Eq (assignment 153) Sign.negative :=
    Eq.trans (h_support 177 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode155 : Eq (assignment 155) Sign.negative :=
    Eq.trans (h_support 155 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode157 : Eq (assignment 157) Sign.negative :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode16)
  let hnode159 : Eq (assignment 159) Sign.positive :=
    Eq.trans (h_support 136 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode160 : Eq (assignment 160) Sign.positive :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode19)
  let hnode166 : Eq (assignment 166) Sign.negative :=
    Eq.trans (h_support 137 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode167 : Eq (assignment 167) Sign.positive :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode183 : Eq (assignment 183) Sign.negative :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode187 : Eq (assignment 187) Sign.negative :=
    Eq.trans (h_support 139 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode189 : Eq (assignment 189) Sign.positive :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode192 : Eq (assignment 192) Sign.negative :=
    Eq.trans (h_support 179 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode8 : Eq (assignment 8) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 21 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode72)
  let hnode10 : Eq (assignment 10) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 27 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode20 : Eq (assignment 20) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 115 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode159)
  let hnode55 : Eq (assignment 55) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 73 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode120)
  let hnode127 : Eq (assignment 127) Sign.negative :=
    Eq.trans (h_support 125 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode7)
  let hnode135 : Eq (assignment 135) Sign.negative :=
    Eq.trans (h_support 145 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode142 : Eq (assignment 142) Sign.negative :=
    Eq.trans (h_support 194 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode72)
  let hnode143 : Eq (assignment 143) Sign.negative :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode145 : Eq (assignment 145) Sign.negative :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode7)
  let hnode148 : Eq (assignment 148) Sign.negative :=
    Eq.trans (h_support 131 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode150 : Eq (assignment 150) Sign.positive :=
    Eq.trans (h_support 210 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode188 : Eq (assignment 188) Sign.negative :=
    Eq.trans (h_support 158 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode195 : Eq (assignment 195) Sign.negative :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode201 : Eq (assignment 201) Sign.negative :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode76)
  let hnode204 : Eq (assignment 204) Sign.positive :=
    Eq.trans (h_support 36 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode149)
  let hnode219 : Eq (assignment 219) Sign.negative :=
    Eq.trans (h_support 196 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode72)
  let hnode220 : Eq (assignment 220) Sign.negative :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode72)
  let hnode221 : Eq (assignment 221) Sign.positive :=
    Eq.trans (h_support 212 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode222 : Eq (assignment 222) Sign.negative :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode76)
  let hnode223 : Eq (assignment 223) Sign.negative :=
    Eq.trans (h_support 162 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode224 : Eq (assignment 224) Sign.positive :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode76)
  let hnode225 : Eq (assignment 225) Sign.positive :=
    Eq.trans (h_support 214 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode230 : Eq (assignment 230) Sign.negative :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode251 : Eq (assignment 251) Sign.positive :=
    Eq.trans (h_support 234 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode122)
  let hnode60 : Eq (assignment 60) Sign.negative :=
    Eq.trans (h_support 24 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode74 : Eq (assignment 74) Sign.positive :=
    Eq.trans (h_support 25 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode75 : Eq (assignment 75) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 198 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode145)
  let hnode77 : Eq (assignment 77) Sign.positive :=
    Eq.trans (h_support 26 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode78 : Eq (assignment 78) Sign.positive :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode124 : Eq (assignment 124) Sign.negative :=
    Eq.trans (h_support 74 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode125 : Eq (assignment 125) Sign.negative :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode156 : Eq (assignment 156) Sign.positive :=
    Eq.trans (h_support 114 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode200 : Eq (assignment 200) Sign.positive :=
    Eq.trans (h_support 199 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode75)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C034.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (top_allows (Sign.withNegation globalNegation (assignment 0)))
  let bounded2 := below_succ bounded1 (domain_from_eq (domain := Cases.C034.initial 1) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded3 := below_succ bounded2 (top_allows (Sign.withNegation globalNegation (assignment 2)))
  let bounded4 := below_succ bounded3 (top_allows (Sign.withNegation globalNegation (assignment 3)))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C034.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Cases.C034.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (top_allows (Sign.withNegation globalNegation (assignment 6)))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Cases.C034.initial 7) (congrArg (Sign.withNegation globalNegation) hnode7) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C034.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Cases.C034.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C034.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (top_allows (Sign.withNegation globalNegation (assignment 11)))
  let bounded13 := below_succ bounded12 (top_allows (Sign.withNegation globalNegation (assignment 12)))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C034.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (top_allows (Sign.withNegation globalNegation (assignment 14)))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Cases.C034.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Cases.C034.initial 16) (congrArg (Sign.withNegation globalNegation) hnode16) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C034.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (top_allows (Sign.withNegation globalNegation (assignment 18)))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C034.initial 19) (congrArg (Sign.withNegation globalNegation) hnode19) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Cases.C034.initial 20) (congrArg (Sign.withNegation globalNegation) hnode20) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C034.initial 21) (congrArg (Sign.withNegation globalNegation) hnode21) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (top_allows (Sign.withNegation globalNegation (assignment 22)))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C034.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C034.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (top_allows (Sign.withNegation globalNegation (assignment 25)))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Cases.C034.initial 26) (congrArg (Sign.withNegation globalNegation) hnode26) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C034.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C034.initial 28) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C034.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (top_allows (Sign.withNegation globalNegation (assignment 30)))
  let bounded32 := below_succ bounded31 (domain_from_eq (domain := Cases.C034.initial 31) (congrArg (Sign.withNegation globalNegation) hnode31) (Eq.refl Bool.true))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C034.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C034.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C034.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (domain_from_eq (domain := Cases.C034.initial 35) (congrArg (Sign.withNegation globalNegation) hnode35) (Eq.refl Bool.true))
  let bounded37 := below_succ bounded36 (domain_from_eq (domain := Cases.C034.initial 36) (congrArg (Sign.withNegation globalNegation) hnode36) (Eq.refl Bool.true))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C034.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C034.initial 38) (congrArg (Sign.withNegation globalNegation) hnode38) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (top_allows (Sign.withNegation globalNegation (assignment 39)))
  let bounded41 := below_succ bounded40 (top_allows (Sign.withNegation globalNegation (assignment 40)))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C034.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (top_allows (Sign.withNegation globalNegation (assignment 42)))
  let bounded44 := below_succ bounded43 (top_allows (Sign.withNegation globalNegation (assignment 43)))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Cases.C034.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C034.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (top_allows (Sign.withNegation globalNegation (assignment 46)))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C034.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (domain_from_eq (domain := Cases.C034.initial 48) (congrArg (Sign.withNegation globalNegation) hnode48) (Eq.refl Bool.true))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C034.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (top_allows (Sign.withNegation globalNegation (assignment 50)))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C034.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (top_allows (Sign.withNegation globalNegation (assignment 52)))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Cases.C034.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (top_allows (Sign.withNegation globalNegation (assignment 54)))
  let bounded56 := below_succ bounded55 (domain_from_eq (domain := Cases.C034.initial 55) (congrArg (Sign.withNegation globalNegation) hnode55) (Eq.refl Bool.true))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C034.initial 56) (congrArg (Sign.withNegation globalNegation) hnode56) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (top_allows (Sign.withNegation globalNegation (assignment 57)))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C034.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (top_allows (Sign.withNegation globalNegation (assignment 59)))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C034.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (top_allows (Sign.withNegation globalNegation (assignment 61)))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C034.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C034.initial 63) (congrArg (Sign.withNegation globalNegation) hnode63) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (top_allows (Sign.withNegation globalNegation (assignment 64)))
  let bounded66 := below_succ bounded65 (top_allows (Sign.withNegation globalNegation (assignment 65)))
  let bounded67 := below_succ bounded66 (top_allows (Sign.withNegation globalNegation (assignment 66)))
  let bounded68 := below_succ bounded67 (top_allows (Sign.withNegation globalNegation (assignment 67)))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C034.initial 68) (congrArg (Sign.withNegation globalNegation) hnode68) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C034.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C034.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C034.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C034.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C034.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C034.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Cases.C034.initial 75) (congrArg (Sign.withNegation globalNegation) hnode75) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Cases.C034.initial 76) (congrArg (Sign.withNegation globalNegation) hnode76) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C034.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C034.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C034.initial 79) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (domain_from_eq (domain := Cases.C034.initial 80) (congrArg (Sign.withNegation globalNegation) hnode80) (Eq.refl Bool.true))
  let bounded82 := below_succ bounded81 (domain_from_eq (domain := Cases.C034.initial 81) (congrArg (Sign.withNegation globalNegation) hnode81) (Eq.refl Bool.true))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Cases.C034.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (top_allows (Sign.withNegation globalNegation (assignment 83)))
  let bounded85 := below_succ bounded84 (top_allows (Sign.withNegation globalNegation (assignment 84)))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C034.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (top_allows (Sign.withNegation globalNegation (assignment 86)))
  let bounded88 := below_succ bounded87 (top_allows (Sign.withNegation globalNegation (assignment 87)))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Cases.C034.initial 88) (congrArg (Sign.withNegation globalNegation) hnode88) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (top_allows (Sign.withNegation globalNegation (assignment 89)))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C034.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C034.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C034.initial 92) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C034.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C034.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C034.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C034.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (top_allows (Sign.withNegation globalNegation (assignment 97)))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C034.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C034.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C034.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C034.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C034.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C034.initial 103) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C034.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C034.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C034.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C034.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C034.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C034.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C034.initial 110) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C034.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C034.initial 112) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C034.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C034.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C034.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C034.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C034.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C034.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C034.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C034.initial 120) (congrArg (Sign.withNegation globalNegation) hnode120) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C034.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C034.initial 122) (congrArg (Sign.withNegation globalNegation) hnode122) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C034.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C034.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Cases.C034.initial 125) (congrArg (Sign.withNegation globalNegation) hnode125) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (top_allows (Sign.withNegation globalNegation (assignment 126)))
  let bounded128 := below_succ bounded127 (domain_from_eq (domain := Cases.C034.initial 127) (congrArg (Sign.withNegation globalNegation) hnode127) (Eq.refl Bool.true))
  let bounded129 := below_succ bounded128 (top_allows (Sign.withNegation globalNegation (assignment 128)))
  let bounded130 := below_succ bounded129 (domain_from_eq (domain := Cases.C034.initial 129) (congrArg (Sign.withNegation globalNegation) hnode129) (Eq.refl Bool.true))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C034.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C034.initial 131) (congrArg (Sign.withNegation globalNegation) hnode131) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (top_allows (Sign.withNegation globalNegation (assignment 132)))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C034.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C034.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C034.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C034.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C034.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C034.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C034.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C034.initial 140) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C034.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C034.initial 142) (congrArg (Sign.withNegation globalNegation) hnode142) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C034.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (top_allows (Sign.withNegation globalNegation (assignment 144)))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C034.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C034.initial 146) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C034.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C034.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C034.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C034.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C034.initial 151) (congrArg (Sign.withNegation globalNegation) hnode151) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C034.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C034.initial 153) (congrArg (Sign.withNegation globalNegation) hnode153) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (top_allows (Sign.withNegation globalNegation (assignment 154)))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C034.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C034.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C034.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C034.initial 158) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C034.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C034.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (domain_from_eq (domain := Cases.C034.initial 161) (congrArg (Sign.withNegation globalNegation) hnode161) (Eq.refl Bool.true))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Cases.C034.initial 162) (congrArg (Sign.withNegation globalNegation) hnode162) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C034.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C034.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (top_allows (Sign.withNegation globalNegation (assignment 165)))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C034.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C034.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (top_allows (Sign.withNegation globalNegation (assignment 168)))
  let bounded170 := below_succ bounded169 (top_allows (Sign.withNegation globalNegation (assignment 169)))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C034.initial 170) (congrArg (Sign.withNegation globalNegation) hnode170) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C034.initial 171) (congrArg (Sign.withNegation globalNegation) hnode171) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C034.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C034.initial 173) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C034.initial 174) (congrArg (Sign.withNegation globalNegation) hnode174) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C034.initial 175) (congrArg (Sign.withNegation globalNegation) hnode175) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C034.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (top_allows (Sign.withNegation globalNegation (assignment 177)))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C034.initial 178) (congrArg (Sign.withNegation globalNegation) hnode178) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C034.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C034.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C034.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C034.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C034.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (top_allows (Sign.withNegation globalNegation (assignment 184)))
  let bounded186 := below_succ bounded185 (top_allows (Sign.withNegation globalNegation (assignment 185)))
  let bounded187 := below_succ bounded186 (top_allows (Sign.withNegation globalNegation (assignment 186)))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C034.initial 187) (congrArg (Sign.withNegation globalNegation) hnode187) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C034.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C034.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (top_allows (Sign.withNegation globalNegation (assignment 190)))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C034.initial 191) (congrArg (Sign.withNegation globalNegation) hnode191) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C034.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C034.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (top_allows (Sign.withNegation globalNegation (assignment 194)))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C034.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (domain_from_eq (domain := Cases.C034.initial 196) (congrArg (Sign.withNegation globalNegation) hnode196) (Eq.refl Bool.true))
  let bounded198 := below_succ bounded197 (domain_from_eq (domain := Cases.C034.initial 197) (congrArg (Sign.withNegation globalNegation) hnode197) (Eq.refl Bool.true))
  let bounded199 := below_succ bounded198 (top_allows (Sign.withNegation globalNegation (assignment 198)))
  let bounded200 := below_succ bounded199 (top_allows (Sign.withNegation globalNegation (assignment 199)))
  let bounded201 := below_succ bounded200 (domain_from_eq (domain := Cases.C034.initial 200) (congrArg (Sign.withNegation globalNegation) hnode200) (Eq.refl Bool.true))
  let bounded202 := below_succ bounded201 (domain_from_eq (domain := Cases.C034.initial 201) (congrArg (Sign.withNegation globalNegation) hnode201) (Eq.refl Bool.true))
  let bounded203 := below_succ bounded202 (top_allows (Sign.withNegation globalNegation (assignment 202)))
  let bounded204 := below_succ bounded203 (top_allows (Sign.withNegation globalNegation (assignment 203)))
  let bounded205 := below_succ bounded204 (domain_from_eq (domain := Cases.C034.initial 204) (congrArg (Sign.withNegation globalNegation) hnode204) (Eq.refl Bool.true))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C034.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Cases.C034.initial 206) (congrArg (Sign.withNegation globalNegation) hnode206) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (top_allows (Sign.withNegation globalNegation (assignment 207)))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C034.initial 208) (congrArg (Sign.withNegation globalNegation) (h_zero 10 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (top_allows (Sign.withNegation globalNegation (assignment 209)))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C034.initial 210) (congrArg (Sign.withNegation globalNegation) hnode210) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C034.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (top_allows (Sign.withNegation globalNegation (assignment 212)))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C034.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C034.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (domain_from_eq (domain := Cases.C034.initial 215) (congrArg (Sign.withNegation globalNegation) hnode215) (Eq.refl Bool.true))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C034.initial 216) (congrArg (Sign.withNegation globalNegation) (h_zero 11 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C034.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C034.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Cases.C034.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C034.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (domain_from_eq (domain := Cases.C034.initial 221) (congrArg (Sign.withNegation globalNegation) hnode221) (Eq.refl Bool.true))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C034.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C034.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C034.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C034.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C034.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C034.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (top_allows (Sign.withNegation globalNegation (assignment 228)))
  let bounded230 := below_succ bounded229 (top_allows (Sign.withNegation globalNegation (assignment 229)))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C034.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (domain_from_eq (domain := Cases.C034.initial 231) (congrArg (Sign.withNegation globalNegation) hnode231) (Eq.refl Bool.true))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C034.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (domain_from_eq (domain := Cases.C034.initial 233) (congrArg (Sign.withNegation globalNegation) (h_zero 12 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C034.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C034.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (top_allows (Sign.withNegation globalNegation (assignment 236)))
  let bounded238 := below_succ bounded237 (top_allows (Sign.withNegation globalNegation (assignment 237)))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C034.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (top_allows (Sign.withNegation globalNegation (assignment 239)))
  let bounded241 := below_succ bounded240 (domain_from_eq (domain := Cases.C034.initial 240) (congrArg (Sign.withNegation globalNegation) hnode240) (Eq.refl Bool.true))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C034.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C034.initial 242) (congrArg (Sign.withNegation globalNegation) (h_zero 13 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C034.initial 243) (congrArg (Sign.withNegation globalNegation) (h_zero 14 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C034.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C034.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C034.initial 246) (congrArg (Sign.withNegation globalNegation) hnode246) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C034.initial 247) (congrArg (Sign.withNegation globalNegation) hnode247) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C034.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (top_allows (Sign.withNegation globalNegation (assignment 249)))
  let bounded251 := below_succ bounded250 (top_allows (Sign.withNegation globalNegation (assignment 250)))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C034.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C034.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C034
#print axioms Papers.RationalityTen.PureGP.Initializers.C034.support_sign_contradiction
