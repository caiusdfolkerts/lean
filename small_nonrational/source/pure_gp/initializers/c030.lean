module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C030

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C030
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 3
def globalNegation : Bool := Bool.false
def edgeTable : Table SupportEdge := (Table.node 117 (Table.node 58 (Table.node 29 (Table.node 14 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 4 24 Bool.true)) (Table.node 2 (Table.leaf (SupportEdge.mk 4 28 Bool.true)) (Table.leaf (SupportEdge.mk 4 31 Bool.true)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 4 33 Bool.true)) (Table.leaf (SupportEdge.mk 5 25 Bool.true))) (Table.node 6 (Table.leaf (SupportEdge.mk 5 29 Bool.true)) (Table.leaf (SupportEdge.mk 5 32 Bool.true))))) (Table.node 10 (Table.node 8 (Table.leaf (SupportEdge.mk 5 34 Bool.true)) (Table.node 9 (Table.leaf (SupportEdge.mk 20 45 Bool.false)) (Table.leaf (SupportEdge.mk 20 51 Bool.false)))) (Table.node 12 (Table.node 11 (Table.leaf (SupportEdge.mk 20 54 Bool.false)) (Table.leaf (SupportEdge.mk 20 55 Bool.false))) (Table.node 13 (Table.leaf (SupportEdge.mk 70 100 Bool.true)) (Table.leaf (SupportEdge.mk 70 106 Bool.true)))))) (Table.node 21 (Table.node 17 (Table.node 15 (Table.leaf (SupportEdge.mk 70 109 Bool.true)) (Table.node 16 (Table.leaf (SupportEdge.mk 70 110 Bool.true)) (Table.leaf (SupportEdge.mk 140 170 Bool.true)))) (Table.node 19 (Table.node 18 (Table.leaf (SupportEdge.mk 140 176 Bool.true)) (Table.leaf (SupportEdge.mk 140 179 Bool.true))) (Table.node 20 (Table.leaf (SupportEdge.mk 140 180 Bool.true)) (Table.leaf (SupportEdge.mk 6 56 Bool.true))))) (Table.node 25 (Table.node 23 (Table.node 22 (Table.leaf (SupportEdge.mk 6 71 Bool.true)) (Table.leaf (SupportEdge.mk 6 72 Bool.true))) (Table.node 24 (Table.leaf (SupportEdge.mk 6 73 Bool.true)) (Table.leaf (SupportEdge.mk 10 60 Bool.true)))) (Table.node 27 (Table.node 26 (Table.leaf (SupportEdge.mk 10 77 Bool.false)) (Table.leaf (SupportEdge.mk 10 79 Bool.false))) (Table.node 28 (Table.leaf (SupportEdge.mk 10 80 Bool.false)) (Table.leaf (SupportEdge.mk 14 64 Bool.true))))))) (Table.node 43 (Table.node 36 (Table.node 32 (Table.node 30 (Table.leaf (SupportEdge.mk 14 83 Bool.false)) (Table.node 31 (Table.leaf (SupportEdge.mk 14 85 Bool.false)) (Table.leaf (SupportEdge.mk 14 86 Bool.false)))) (Table.node 34 (Table.node 33 (Table.leaf (SupportEdge.mk 39 94 Bool.false)) (Table.leaf (SupportEdge.mk 39 113 Bool.false))) (Table.node 35 (Table.leaf (SupportEdge.mk 39 115 Bool.false)) (Table.leaf (SupportEdge.mk 39 116 Bool.false))))) (Table.node 39 (Table.node 37 (Table.leaf (SupportEdge.mk 144 199 Bool.true)) (Table.node 38 (Table.leaf (SupportEdge.mk 144 218 Bool.true)) (Table.leaf (SupportEdge.mk 144 220 Bool.true)))) (Table.node 41 (Table.node 40 (Table.leaf (SupportEdge.mk 144 221 Bool.true)) (Table.leaf (SupportEdge.mk 22 57 Bool.false))) (Table.node 42 (Table.leaf (SupportEdge.mk 22 91 Bool.false)) (Table.leaf (SupportEdge.mk 22 95 Bool.true)))))) (Table.node 50 (Table.node 46 (Table.node 44 (Table.leaf (SupportEdge.mk 22 96 Bool.true)) (Table.node 45 (Table.leaf (SupportEdge.mk 25 60 Bool.false)) (Table.leaf (SupportEdge.mk 25 94 Bool.false)))) (Table.node 48 (Table.node 47 (Table.leaf (SupportEdge.mk 25 99 Bool.false)) (Table.leaf (SupportEdge.mk 25 100 Bool.false))) (Table.node 49 (Table.leaf (SupportEdge.mk 32 67 Bool.false)) (Table.leaf (SupportEdge.mk 32 103 Bool.true))))) (Table.node 54 (Table.node 52 (Table.node 51 (Table.leaf (SupportEdge.mk 32 108 Bool.false)) (Table.leaf (SupportEdge.mk 32 109 Bool.false))) (Table.node 53 (Table.leaf (SupportEdge.mk 42 77 Bool.false)) (Table.leaf (SupportEdge.mk 42 113 Bool.true)))) (Table.node 56 (Table.node 55 (Table.leaf (SupportEdge.mk 42 118 Bool.false)) (Table.leaf (SupportEdge.mk 42 119 Bool.false))) (Table.node 57 (Table.leaf (SupportEdge.mk 167 202 Bool.false)) (Table.leaf (SupportEdge.mk 167 233 Bool.false)))))))) (Table.node 87 (Table.node 72 (Table.node 65 (Table.node 61 (Table.node 59 (Table.leaf (SupportEdge.mk 167 238 Bool.true)) (Table.node 60 (Table.leaf (SupportEdge.mk 167 239 Bool.true)) (Table.leaf (SupportEdge.mk 30 65 Bool.false)))) (Table.node 63 (Table.node 62 (Table.leaf (SupportEdge.mk 30 95 Bool.true)) (Table.leaf (SupportEdge.mk 30 101 Bool.true))) (Table.node 64 (Table.leaf (SupportEdge.mk 30 108 Bool.true)) (Table.leaf (SupportEdge.mk 31 66 Bool.false))))) (Table.node 68 (Table.node 66 (Table.leaf (SupportEdge.mk 31 96 Bool.true)) (Table.node 67 (Table.leaf (SupportEdge.mk 31 102 Bool.true)) (Table.leaf (SupportEdge.mk 31 109 Bool.true)))) (Table.node 70 (Table.node 69 (Table.leaf (SupportEdge.mk 33 68 Bool.false)) (Table.leaf (SupportEdge.mk 33 98 Bool.true))) (Table.node 71 (Table.leaf (SupportEdge.mk 33 104 Bool.true)) (Table.leaf (SupportEdge.mk 33 110 Bool.true)))))) (Table.node 79 (Table.node 75 (Table.node 73 (Table.leaf (SupportEdge.mk 52 87 Bool.false)) (Table.node 74 (Table.leaf (SupportEdge.mk 52 117 Bool.false)) (Table.leaf (SupportEdge.mk 52 121 Bool.false)))) (Table.node 77 (Table.node 76 (Table.leaf (SupportEdge.mk 52 125 Bool.true)) (Table.leaf (SupportEdge.mk 177 212 Bool.false))) (Table.node 78 (Table.leaf (SupportEdge.mk 177 237 Bool.true)) (Table.leaf (SupportEdge.mk 177 241 Bool.true))))) (Table.node 83 (Table.node 81 (Table.node 80 (Table.leaf (SupportEdge.mk 177 245 Bool.false)) (Table.leaf (SupportEdge.mk 38 73 Bool.false))) (Table.node 82 (Table.leaf (SupportEdge.mk 38 93 Bool.false)) (Table.leaf (SupportEdge.mk 38 112 Bool.false)))) (Table.node 85 (Table.node 84 (Table.leaf (SupportEdge.mk 38 114 Bool.false)) (Table.leaf (SupportEdge.mk 38 116 Bool.true))) (Table.node 86 (Table.leaf (SupportEdge.mk 41 76 Bool.false)) (Table.leaf (SupportEdge.mk 41 96 Bool.false))))))) (Table.node 102 (Table.node 94 (Table.node 90 (Table.node 88 (Table.leaf (SupportEdge.mk 41 112 Bool.true)) (Table.node 89 (Table.leaf (SupportEdge.mk 41 117 Bool.false)) (Table.leaf (SupportEdge.mk 41 119 Bool.true)))) (Table.node 92 (Table.node 91 (Table.leaf (SupportEdge.mk 51 86 Bool.false)) (Table.leaf (SupportEdge.mk 51 106 Bool.false))) (Table.node 93 (Table.leaf (SupportEdge.mk 51 116 Bool.false)) (Table.leaf (SupportEdge.mk 51 123 Bool.true))))) (Table.node 98 (Table.node 96 (Table.node 95 (Table.leaf (SupportEdge.mk 51 124 Bool.true)) (Table.leaf (SupportEdge.mk 2 127 Bool.true))) (Table.node 97 (Table.leaf (SupportEdge.mk 2 131 Bool.true)) (Table.leaf (SupportEdge.mk 2 136 Bool.false)))) (Table.node 100 (Table.node 99 (Table.leaf (SupportEdge.mk 2 137 Bool.false)) (Table.leaf (SupportEdge.mk 3 128 Bool.true))) (Table.node 101 (Table.leaf (SupportEdge.mk 3 132 Bool.true)) (Table.leaf (SupportEdge.mk 3 138 Bool.false)))))) (Table.node 109 (Table.node 105 (Table.node 103 (Table.leaf (SupportEdge.mk 3 139 Bool.false)) (Table.node 104 (Table.leaf (SupportEdge.mk 15 145 Bool.false)) (Table.leaf (SupportEdge.mk 15 151 Bool.false)))) (Table.node 107 (Table.node 106 (Table.leaf (SupportEdge.mk 15 157 Bool.false)) (Table.leaf (SupportEdge.mk 15 158 Bool.false))) (Table.node 108 (Table.leaf (SupportEdge.mk 30 165 Bool.false)) (Table.leaf (SupportEdge.mk 30 171 Bool.false))))) (Table.node 113 (Table.node 111 (Table.node 110 (Table.leaf (SupportEdge.mk 30 177 Bool.false)) (Table.leaf (SupportEdge.mk 30 178 Bool.false))) (Table.node 112 (Table.leaf (SupportEdge.mk 65 200 Bool.false)) (Table.leaf (SupportEdge.mk 65 206 Bool.false)))) (Table.node 115 (Table.node 114 (Table.leaf (SupportEdge.mk 65 212 Bool.false)) (Table.leaf (SupportEdge.mk 65 213 Bool.false))) (Table.node 116 (Table.leaf (SupportEdge.mk 2 127 Bool.true)) (Table.leaf (SupportEdge.mk 2 131 Bool.true))))))))) (Table.node 176 (Table.node 146 (Table.node 131 (Table.node 124 (Table.node 120 (Table.node 118 (Table.leaf (SupportEdge.mk 2 135 Bool.false)) (Table.node 119 (Table.leaf (SupportEdge.mk 2 136 Bool.false)) (Table.leaf (SupportEdge.mk 5 130 Bool.true)))) (Table.node 122 (Table.node 121 (Table.leaf (SupportEdge.mk 5 134 Bool.true)) (Table.leaf (SupportEdge.mk 5 139 Bool.true))) (Table.node 123 (Table.leaf (SupportEdge.mk 5 140 Bool.true)) (Table.leaf (SupportEdge.mk 17 147 Bool.false))))) (Table.node 127 (Table.node 125 (Table.leaf (SupportEdge.mk 17 153 Bool.false)) (Table.node 126 (Table.leaf (SupportEdge.mk 17 158 Bool.true)) (Table.leaf (SupportEdge.mk 17 159 Bool.true)))) (Table.node 129 (Table.node 128 (Table.leaf (SupportEdge.mk 32 167 Bool.false)) (Table.leaf (SupportEdge.mk 32 173 Bool.false))) (Table.node 130 (Table.leaf (SupportEdge.mk 32 178 Bool.true)) (Table.leaf (SupportEdge.mk 32 179 Bool.true)))))) (Table.node 138 (Table.node 134 (Table.node 132 (Table.leaf (SupportEdge.mk 67 202 Bool.false)) (Table.node 133 (Table.leaf (SupportEdge.mk 67 208 Bool.false)) (Table.leaf (SupportEdge.mk 67 213 Bool.true)))) (Table.node 136 (Table.node 135 (Table.leaf (SupportEdge.mk 67 214 Bool.true)) (Table.leaf (SupportEdge.mk 6 126 Bool.false))) (Table.node 137 (Table.leaf (SupportEdge.mk 6 141 Bool.false)) (Table.leaf (SupportEdge.mk 6 143 Bool.false))))) (Table.node 142 (Table.node 140 (Table.node 139 (Table.leaf (SupportEdge.mk 6 144 Bool.false)) (Table.leaf (SupportEdge.mk 8 128 Bool.false))) (Table.node 141 (Table.leaf (SupportEdge.mk 8 145 Bool.true)) (Table.leaf (SupportEdge.mk 8 148 Bool.false)))) (Table.node 144 (Table.node 143 (Table.leaf (SupportEdge.mk 8 149 Bool.false)) (Table.leaf (SupportEdge.mk 12 132 Bool.false))) (Table.node 145 (Table.leaf (SupportEdge.mk 12 151 Bool.true)) (Table.leaf (SupportEdge.mk 12 154 Bool.false))))))) (Table.node 161 (Table.node 153 (Table.node 149 (Table.node 147 (Table.leaf (SupportEdge.mk 12 155 Bool.false)) (Table.node 148 (Table.leaf (SupportEdge.mk 37 162 Bool.true)) (Table.leaf (SupportEdge.mk 37 181 Bool.true)))) (Table.node 151 (Table.node 150 (Table.leaf (SupportEdge.mk 37 184 Bool.false)) (Table.leaf (SupportEdge.mk 37 185 Bool.false))) (Table.node 152 (Table.leaf (SupportEdge.mk 72 197 Bool.true)) (Table.leaf (SupportEdge.mk 72 216 Bool.true))))) (Table.node 157 (Table.node 155 (Table.node 154 (Table.leaf (SupportEdge.mk 72 219 Bool.false)) (Table.leaf (SupportEdge.mk 72 220 Bool.false))) (Table.node 156 (Table.leaf (SupportEdge.mk 13 133 Bool.false)) (Table.leaf (SupportEdge.mk 13 143 Bool.false)))) (Table.node 159 (Table.node 158 (Table.leaf (SupportEdge.mk 13 152 Bool.true)) (Table.leaf (SupportEdge.mk 13 154 Bool.true))) (Table.node 160 (Table.leaf (SupportEdge.mk 14 134 Bool.false)) (Table.leaf (SupportEdge.mk 14 144 Bool.false)))))) (Table.node 168 (Table.node 164 (Table.node 162 (Table.leaf (SupportEdge.mk 14 153 Bool.true)) (Table.node 163 (Table.leaf (SupportEdge.mk 14 155 Bool.true)) (Table.leaf (SupportEdge.mk 20 140 Bool.false)))) (Table.node 166 (Table.node 165 (Table.leaf (SupportEdge.mk 20 150 Bool.false)) (Table.leaf (SupportEdge.mk 20 159 Bool.false))) (Table.node 167 (Table.leaf (SupportEdge.mk 20 160 Bool.false)) (Table.leaf (SupportEdge.mk 51 176 Bool.true))))) (Table.node 172 (Table.node 170 (Table.node 169 (Table.leaf (SupportEdge.mk 51 186 Bool.true)) (Table.leaf (SupportEdge.mk 51 193 Bool.false))) (Table.node 171 (Table.leaf (SupportEdge.mk 51 194 Bool.false)) (Table.leaf (SupportEdge.mk 86 211 Bool.true)))) (Table.node 174 (Table.node 173 (Table.leaf (SupportEdge.mk 86 221 Bool.true)) (Table.leaf (SupportEdge.mk 86 228 Bool.false))) (Table.node 175 (Table.leaf (SupportEdge.mk 86 229 Bool.false)) (Table.leaf (SupportEdge.mk 27 132 Bool.true)))))))) (Table.node 205 (Table.node 190 (Table.node 183 (Table.node 179 (Table.node 177 (Table.leaf (SupportEdge.mk 27 162 Bool.false)) (Table.node 178 (Table.leaf (SupportEdge.mk 27 171 Bool.true)) (Table.leaf (SupportEdge.mk 27 175 Bool.false)))) (Table.node 181 (Table.node 180 (Table.leaf (SupportEdge.mk 28 133 Bool.true)) (Table.leaf (SupportEdge.mk 28 163 Bool.false))) (Table.node 182 (Table.leaf (SupportEdge.mk 28 172 Bool.true)) (Table.leaf (SupportEdge.mk 28 176 Bool.false))))) (Table.node 186 (Table.node 184 (Table.leaf (SupportEdge.mk 33 138 Bool.true)) (Table.node 185 (Table.leaf (SupportEdge.mk 33 168 Bool.false)) (Table.leaf (SupportEdge.mk 33 177 Bool.false)))) (Table.node 188 (Table.node 187 (Table.leaf (SupportEdge.mk 33 180 Bool.false)) (Table.leaf (SupportEdge.mk 49 154 Bool.true))) (Table.node 189 (Table.leaf (SupportEdge.mk 49 184 Bool.true)) (Table.leaf (SupportEdge.mk 49 191 Bool.false)))))) (Table.node 197 (Table.node 193 (Table.node 191 (Table.leaf (SupportEdge.mk 49 194 Bool.false)) (Table.node 192 (Table.leaf (SupportEdge.mk 104 209 Bool.false)) (Table.leaf (SupportEdge.mk 104 234 Bool.true)))) (Table.node 195 (Table.node 194 (Table.leaf (SupportEdge.mk 104 241 Bool.false)) (Table.leaf (SupportEdge.mk 104 244 Bool.false))) (Table.node 196 (Table.leaf (SupportEdge.mk 75 145 Bool.false)) (Table.leaf (SupportEdge.mk 75 200 Bool.true))))) (Table.node 201 (Table.node 199 (Table.node 198 (Table.leaf (SupportEdge.mk 75 216 Bool.false)) (Table.leaf (SupportEdge.mk 75 222 Bool.false))) (Table.node 200 (Table.leaf (SupportEdge.mk 77 147 Bool.false)) (Table.leaf (SupportEdge.mk 77 202 Bool.true)))) (Table.node 203 (Table.node 202 (Table.leaf (SupportEdge.mk 77 218 Bool.false)) (Table.leaf (SupportEdge.mk 77 224 Bool.true))) (Table.node 204 (Table.leaf (SupportEdge.mk 79 149 Bool.false)) (Table.leaf (SupportEdge.mk 79 204 Bool.true))))))) (Table.node 220 (Table.node 212 (Table.node 208 (Table.node 206 (Table.leaf (SupportEdge.mk 79 220 Bool.false)) (Table.node 207 (Table.leaf (SupportEdge.mk 79 225 Bool.true)) (Table.leaf (SupportEdge.mk 88 158 Bool.false)))) (Table.node 210 (Table.node 209 (Table.leaf (SupportEdge.mk 88 213 Bool.true)) (Table.leaf (SupportEdge.mk 88 227 Bool.true))) (Table.node 211 (Table.leaf (SupportEdge.mk 88 230 Bool.true)) (Table.leaf (SupportEdge.mk 118 188 Bool.false))))) (Table.node 216 (Table.node 214 (Table.node 213 (Table.leaf (SupportEdge.mk 118 238 Bool.false)) (Table.leaf (SupportEdge.mk 118 247 Bool.true))) (Table.node 215 (Table.leaf (SupportEdge.mk 118 250 Bool.true)) (Table.leaf (SupportEdge.mk 111 181 Bool.false)))) (Table.node 218 (Table.node 217 (Table.leaf (SupportEdge.mk 111 216 Bool.false)) (Table.leaf (SupportEdge.mk 111 231 Bool.false))) (Table.node 219 (Table.leaf (SupportEdge.mk 111 247 Bool.false)) (Table.leaf (SupportEdge.mk 112 182 Bool.false)))))) (Table.node 227 (Table.node 223 (Table.node 221 (Table.leaf (SupportEdge.mk 112 217 Bool.false)) (Table.node 222 (Table.leaf (SupportEdge.mk 112 232 Bool.false)) (Table.leaf (SupportEdge.mk 112 248 Bool.false)))) (Table.node 225 (Table.node 224 (Table.leaf (SupportEdge.mk 114 184 Bool.false)) (Table.leaf (SupportEdge.mk 114 219 Bool.false))) (Table.node 226 (Table.leaf (SupportEdge.mk 114 234 Bool.false)) (Table.leaf (SupportEdge.mk 114 249 Bool.false))))) (Table.node 231 (Table.node 229 (Table.node 228 (Table.leaf (SupportEdge.mk 117 187 Bool.false)) (Table.leaf (SupportEdge.mk 117 222 Bool.false))) (Table.node 230 (Table.leaf (SupportEdge.mk 117 237 Bool.false)) (Table.leaf (SupportEdge.mk 117 250 Bool.false)))) (Table.node 233 (Table.node 232 (Table.leaf (SupportEdge.mk 121 191 Bool.false)) (Table.leaf (SupportEdge.mk 121 226 Bool.false))) (Table.node 234 (Table.leaf (SupportEdge.mk 121 241 Bool.false)) (Table.leaf (SupportEdge.mk 121 251 Bool.false))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf 2) (Table.node 2 (Table.leaf 35) (Table.leaf 74))) (Table.node 5 (Table.node 4 (Table.leaf 97) (Table.leaf 107)) (Table.node 6 (Table.leaf 127) (Table.leaf 131)))) (Table.node 11 (Table.node 9 (Table.node 8 (Table.leaf 135) (Table.leaf 136)) (Table.node 10 (Table.leaf 137) (Table.leaf 142))) (Table.node 13 (Table.node 12 (Table.leaf 156) (Table.leaf 174)) (Table.node 14 (Table.leaf 223) (Table.leaf 246)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 235 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 15 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C030.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode128 : Eq (assignment 128) Sign.negative :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode132 : Eq (assignment 132) Sign.negative :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode138 : Eq (assignment 138) Sign.positive :=
    Eq.trans (h_support 101 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode139 : Eq (assignment 139) Sign.positive :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode5 : Eq (assignment 5) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 121 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode139)
  let hnode8 : Eq (assignment 8) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 139 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode128)
  let hnode12 : Eq (assignment 12) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 143 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode132)
  let hnode27 : Eq (assignment 27) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 175 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode132)
  let hnode33 : Eq (assignment 33) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 183 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode138)
  let hnode4 : Eq (assignment 4) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 3 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode25 : Eq (assignment 25) Sign.positive :=
    Eq.trans (h_support 4 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode29 : Eq (assignment 29) Sign.positive :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode32 : Eq (assignment 32) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode34 : Eq (assignment 34) Sign.positive :=
    Eq.trans (h_support 7 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode68 : Eq (assignment 68) Sign.negative :=
    Eq.trans (h_support 68 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode98 : Eq (assignment 98) Sign.positive :=
    Eq.trans (h_support 69 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode104 : Eq (assignment 104) Sign.positive :=
    Eq.trans (h_support 70 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode110 : Eq (assignment 110) Sign.positive :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode130 : Eq (assignment 130) Sign.positive :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode134 : Eq (assignment 134) Sign.positive :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode140 : Eq (assignment 140) Sign.positive :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode145 : Eq (assignment 145) Sign.positive :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode148 : Eq (assignment 148) Sign.negative :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode149 : Eq (assignment 149) Sign.negative :=
    Eq.trans (h_support 142 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode151 : Eq (assignment 151) Sign.positive :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode12)
  let hnode154 : Eq (assignment 154) Sign.negative :=
    Eq.trans (h_support 145 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode155 : Eq (assignment 155) Sign.negative :=
    Eq.trans (h_support 146 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode162 : Eq (assignment 162) Sign.positive :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode168 : Eq (assignment 168) Sign.negative :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode171 : Eq (assignment 171) Sign.negative :=
    Eq.trans (h_support 177 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode175 : Eq (assignment 175) Sign.positive :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode177 : Eq (assignment 177) Sign.negative :=
    Eq.trans (h_support 185 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode180 : Eq (assignment 180) Sign.negative :=
    Eq.trans (h_support 186 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode13 : Eq (assignment 13) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 158 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode154)
  let hnode14 : Eq (assignment 14) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 162 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode155)
  let hnode15 : Eq (assignment 15) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 103 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode145)
  let hnode20 : Eq (assignment 20) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 163 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode140)
  let hnode24 : Eq (assignment 24) Sign.negative :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode28 : Eq (assignment 28) Sign.negative :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode30 : Eq (assignment 30) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 108 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode171)
  let hnode31 : Eq (assignment 31) Sign.negative :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode37 : Eq (assignment 37) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 147 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode162)
  let hnode49 : Eq (assignment 49) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 187 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode154)
  let hnode60 : Eq (assignment 60) Sign.positive :=
    Eq.trans (h_support 44 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode67 : Eq (assignment 67) Sign.positive :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode70 : Eq (assignment 70) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 15 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode110)
  let hnode75 : Eq (assignment 75) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 195 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode145)
  let hnode79 : Eq (assignment 79) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 203 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode149)
  let hnode94 : Eq (assignment 94) Sign.positive :=
    Eq.trans (h_support 45 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode99 : Eq (assignment 99) Sign.positive :=
    Eq.trans (h_support 46 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode100 : Eq (assignment 100) Sign.positive :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode103 : Eq (assignment 103) Sign.negative :=
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode108 : Eq (assignment 108) Sign.positive :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode109 : Eq (assignment 109) Sign.positive :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode167 : Eq (assignment 167) Sign.positive :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode170 : Eq (assignment 170) Sign.negative :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode140)
  let hnode173 : Eq (assignment 173) Sign.positive :=
    Eq.trans (h_support 128 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode176 : Eq (assignment 176) Sign.negative :=
    Eq.trans (h_support 17 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode140)
  let hnode178 : Eq (assignment 178) Sign.negative :=
    Eq.trans (h_support 129 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode209 : Eq (assignment 209) Sign.positive :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode212 : Eq (assignment 212) Sign.negative :=
    Eq.trans (h_support 76 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode177)
  let hnode234 : Eq (assignment 234) Sign.negative :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode104)
  let hnode237 : Eq (assignment 237) Sign.positive :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode177)
  let hnode241 : Eq (assignment 241) Sign.positive :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 194 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode245 : Eq (assignment 245) Sign.negative :=
    Eq.trans (h_support 79 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode177)
  let hnode10 : Eq (assignment 10) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 26 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode79)
  let hnode39 : Eq (assignment 39) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 32 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode94)
  let hnode45 : Eq (assignment 45) Sign.positive :=
    Eq.trans (h_support 8 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode51 : Eq (assignment 51) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 167 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode176)
  let hnode54 : Eq (assignment 54) Sign.positive :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode55 : Eq (assignment 55) Sign.positive :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode64 : Eq (assignment 64) Sign.negative :=
    Eq.trans (h_support 28 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode65 : Eq (assignment 65) Sign.negative :=
    Eq.trans (h_support 60 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode30)
  let hnode66 : Eq (assignment 66) Sign.negative :=
    Eq.trans (h_support 64 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode83 : Eq (assignment 83) Sign.positive :=
    Eq.trans (h_support 29 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode85 : Eq (assignment 85) Sign.positive :=
    Eq.trans (h_support 30 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode86 : Eq (assignment 86) Sign.positive :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode95 : Eq (assignment 95) Sign.positive :=
    Eq.trans (h_support 61 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode96 : Eq (assignment 96) Sign.positive :=
    Eq.trans (h_support 65 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode31)
  let hnode101 : Eq (assignment 101) Sign.positive :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode102 : Eq (assignment 102) Sign.positive :=
    Eq.trans (h_support 66 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode31)
  let hnode106 : Eq (assignment 106) Sign.positive :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode70)
  let hnode114 : Eq (assignment 114) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 225 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode234)
  let hnode117 : Eq (assignment 117) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 229 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode237)
  let hnode121 : Eq (assignment 121) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 233 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode241)
  let hnode133 : Eq (assignment 133) Sign.positive :=
    Eq.trans (h_support 155 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode143 : Eq (assignment 143) Sign.positive :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode144 : Eq (assignment 144) Sign.positive :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode150 : Eq (assignment 150) Sign.positive :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode152 : Eq (assignment 152) Sign.negative :=
    Eq.trans (h_support 157 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode153 : Eq (assignment 153) Sign.negative :=
    Eq.trans (h_support 161 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode157 : Eq (assignment 157) Sign.positive :=
    Eq.trans (h_support 105 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode158 : Eq (assignment 158) Sign.positive :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode159 : Eq (assignment 159) Sign.positive :=
    Eq.trans (h_support 165 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode160 : Eq (assignment 160) Sign.positive :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode163 : Eq (assignment 163) Sign.negative :=
    Eq.trans (h_support 180 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode165 : Eq (assignment 165) Sign.negative :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode30)
  let hnode172 : Eq (assignment 172) Sign.positive :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode181 : Eq (assignment 181) Sign.positive :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode37)
  let hnode184 : Eq (assignment 184) Sign.negative :=
    Eq.trans (h_support 188 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode49)
  let hnode185 : Eq (assignment 185) Sign.negative :=
    Eq.trans (h_support 150 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode191 : Eq (assignment 191) Sign.positive :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode49)
  let hnode194 : Eq (assignment 194) Sign.positive :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode49)
  let hnode200 : Eq (assignment 200) Sign.negative :=
    Eq.trans (h_support 196 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode75)
  let hnode202 : Eq (assignment 202) Sign.positive :=
    Eq.trans (h_support 131 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode67)
  let hnode204 : Eq (assignment 204) Sign.positive :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode79)
  let hnode208 : Eq (assignment 208) Sign.positive :=
    Eq.trans (h_support 132 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode67)
  let hnode213 : Eq (assignment 213) Sign.negative :=
    Eq.trans (h_support 133 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode67)
  let hnode214 : Eq (assignment 214) Sign.negative :=
    Eq.trans (h_support 134 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode67)
  let hnode216 : Eq (assignment 216) Sign.positive :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode75)
  let hnode220 : Eq (assignment 220) Sign.negative :=
    Eq.trans (h_support 205 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode79)
  let hnode222 : Eq (assignment 222) Sign.positive :=
    Eq.trans (h_support 198 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode75)
  let hnode225 : Eq (assignment 225) Sign.positive :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode79)
  let hnode233 : Eq (assignment 233) Sign.positive :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode167)
  let hnode238 : Eq (assignment 238) Sign.negative :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode167)
  let hnode239 : Eq (assignment 239) Sign.negative :=
    Eq.trans (h_support 59 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode167)
  let hnode6 : Eq (assignment 6) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 137 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode143)
  let hnode17 : Eq (assignment 17) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 125 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode158)
  let hnode22 : Eq (assignment 22) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 42 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode95)
  let hnode38 : Eq (assignment 38) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 83 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode114)
  let hnode41 : Eq (assignment 41) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 86 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode96)
  let hnode52 : Eq (assignment 52) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 74 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode72 : Eq (assignment 72) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 152 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode216)
  let hnode77 : Eq (assignment 77) Sign.negative :=
    Eq.trans (h_support 25 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode80 : Eq (assignment 80) Sign.negative :=
    Eq.trans (h_support 27 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode88 : Eq (assignment 88) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 207 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode158)
  let hnode111 : Eq (assignment 111) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 216 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode216)
  let hnode113 : Eq (assignment 113) Sign.positive :=
    Eq.trans (h_support 33 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode39)
  let hnode115 : Eq (assignment 115) Sign.positive :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode39)
  let hnode116 : Eq (assignment 116) Sign.positive :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode39)
  let hnode118 : Eq (assignment 118) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 212 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode238)
  let hnode123 : Eq (assignment 123) Sign.negative :=
    Eq.trans (h_support 93 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode51)
  let hnode124 : Eq (assignment 124) Sign.negative :=
    Eq.trans (h_support 94 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode51)
  let hnode186 : Eq (assignment 186) Sign.negative :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode51)
  let hnode187 : Eq (assignment 187) Sign.positive :=
    Eq.trans (h_support 227 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode117)
  let hnode193 : Eq (assignment 193) Sign.positive :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode51)
  let hnode199 : Eq (assignment 199) Sign.negative :=
    Eq.trans (h_support 36 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode144)
  let hnode206 : Eq (assignment 206) Sign.negative :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode65)
  let hnode211 : Eq (assignment 211) Sign.negative :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode86)
  let hnode218 : Eq (assignment 218) Sign.negative :=
    Eq.trans (h_support 37 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode144)
  let hnode219 : Eq (assignment 219) Sign.negative :=
    Eq.trans (h_support 224 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode114)
  let hnode221 : Eq (assignment 221) Sign.negative :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode86)
  let hnode226 : Eq (assignment 226) Sign.positive :=
    Eq.trans (h_support 232 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode228 : Eq (assignment 228) Sign.positive :=
    Eq.trans (h_support 173 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode86)
  let hnode229 : Eq (assignment 229) Sign.positive :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode86)
  let hnode249 : Eq (assignment 249) Sign.negative :=
    Eq.trans (h_support 226 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode114)
  let hnode250 : Eq (assignment 250) Sign.positive :=
    Eq.trans (h_support 230 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode117)
  let hnode251 : Eq (assignment 251) Sign.positive :=
    Eq.trans (h_support 234 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode42 : Eq (assignment 42) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 52 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode77)
  let hnode56 : Eq (assignment 56) Sign.negative :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode57 : Eq (assignment 57) Sign.negative :=
    Eq.trans (h_support 40 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode71 : Eq (assignment 71) Sign.negative :=
    Eq.trans (h_support 21 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode73 : Eq (assignment 73) Sign.negative :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode76 : Eq (assignment 76) Sign.positive :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode87 : Eq (assignment 87) Sign.positive :=
    Eq.trans (h_support 72 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode52)
  let hnode91 : Eq (assignment 91) Sign.negative :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode93 : Eq (assignment 93) Sign.negative :=
    Eq.trans (h_support 81 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode112 : Eq (assignment 112) Sign.negative :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode119 : Eq (assignment 119) Sign.negative :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode125 : Eq (assignment 125) Sign.negative :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode52)
  let hnode126 : Eq (assignment 126) Sign.positive :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode6)
  let hnode141 : Eq (assignment 141) Sign.positive :=
    Eq.trans (h_support 136 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode6)
  let hnode147 : Eq (assignment 147) Sign.negative :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode188 : Eq (assignment 188) Sign.negative :=
    Eq.trans (h_support 211 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode118)
  let hnode197 : Eq (assignment 197) Sign.positive :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode72)
  let hnode224 : Eq (assignment 224) Sign.positive :=
    Eq.trans (h_support 202 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode77)
  let hnode227 : Eq (assignment 227) Sign.negative :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode230 : Eq (assignment 230) Sign.negative :=
    Eq.trans (h_support 210 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode231 : Eq (assignment 231) Sign.positive :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode247 : Eq (assignment 247) Sign.positive :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode182 : Eq (assignment 182) Sign.negative :=
    Eq.trans (h_support 219 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode217 : Eq (assignment 217) Sign.negative :=
    Eq.trans (h_support 220 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode232 : Eq (assignment 232) Sign.negative :=
    Eq.trans (h_support 221 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode248 : Eq (assignment 248) Sign.negative :=
    Eq.trans (h_support 222 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C030.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (top_allows (Sign.withNegation globalNegation (assignment 0)))
  let bounded2 := below_succ bounded1 (top_allows (Sign.withNegation globalNegation (assignment 1)))
  let bounded3 := below_succ bounded2 (domain_from_eq (domain := Cases.C030.initial 2) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded4 := below_succ bounded3 (domain_from_eq (domain := Cases.C030.initial 3) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C030.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Cases.C030.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Cases.C030.initial 6) (congrArg (Sign.withNegation globalNegation) hnode6) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (top_allows (Sign.withNegation globalNegation (assignment 7)))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C030.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (top_allows (Sign.withNegation globalNegation (assignment 9)))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C030.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (top_allows (Sign.withNegation globalNegation (assignment 11)))
  let bounded13 := below_succ bounded12 (domain_from_eq (domain := Cases.C030.initial 12) (congrArg (Sign.withNegation globalNegation) hnode12) (Eq.refl Bool.true))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C030.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C030.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Cases.C030.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (top_allows (Sign.withNegation globalNegation (assignment 16)))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C030.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (top_allows (Sign.withNegation globalNegation (assignment 18)))
  let bounded20 := below_succ bounded19 (top_allows (Sign.withNegation globalNegation (assignment 19)))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Cases.C030.initial 20) (congrArg (Sign.withNegation globalNegation) hnode20) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (top_allows (Sign.withNegation globalNegation (assignment 21)))
  let bounded23 := below_succ bounded22 (domain_from_eq (domain := Cases.C030.initial 22) (congrArg (Sign.withNegation globalNegation) hnode22) (Eq.refl Bool.true))
  let bounded24 := below_succ bounded23 (top_allows (Sign.withNegation globalNegation (assignment 23)))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C030.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C030.initial 25) (congrArg (Sign.withNegation globalNegation) hnode25) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (top_allows (Sign.withNegation globalNegation (assignment 26)))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C030.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C030.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C030.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (domain_from_eq (domain := Cases.C030.initial 30) (congrArg (Sign.withNegation globalNegation) hnode30) (Eq.refl Bool.true))
  let bounded32 := below_succ bounded31 (domain_from_eq (domain := Cases.C030.initial 31) (congrArg (Sign.withNegation globalNegation) hnode31) (Eq.refl Bool.true))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C030.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C030.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C030.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (domain_from_eq (domain := Cases.C030.initial 35) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded37 := below_succ bounded36 (top_allows (Sign.withNegation globalNegation (assignment 36)))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C030.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C030.initial 38) (congrArg (Sign.withNegation globalNegation) hnode38) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (domain_from_eq (domain := Cases.C030.initial 39) (congrArg (Sign.withNegation globalNegation) hnode39) (Eq.refl Bool.true))
  let bounded41 := below_succ bounded40 (top_allows (Sign.withNegation globalNegation (assignment 40)))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C030.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C030.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (top_allows (Sign.withNegation globalNegation (assignment 43)))
  let bounded45 := below_succ bounded44 (top_allows (Sign.withNegation globalNegation (assignment 44)))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C030.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (top_allows (Sign.withNegation globalNegation (assignment 46)))
  let bounded48 := below_succ bounded47 (top_allows (Sign.withNegation globalNegation (assignment 47)))
  let bounded49 := below_succ bounded48 (top_allows (Sign.withNegation globalNegation (assignment 48)))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C030.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (top_allows (Sign.withNegation globalNegation (assignment 50)))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C030.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (domain_from_eq (domain := Cases.C030.initial 52) (congrArg (Sign.withNegation globalNegation) hnode52) (Eq.refl Bool.true))
  let bounded54 := below_succ bounded53 (top_allows (Sign.withNegation globalNegation (assignment 53)))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Cases.C030.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (domain_from_eq (domain := Cases.C030.initial 55) (congrArg (Sign.withNegation globalNegation) hnode55) (Eq.refl Bool.true))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C030.initial 56) (congrArg (Sign.withNegation globalNegation) hnode56) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C030.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (top_allows (Sign.withNegation globalNegation (assignment 58)))
  let bounded60 := below_succ bounded59 (top_allows (Sign.withNegation globalNegation (assignment 59)))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C030.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (top_allows (Sign.withNegation globalNegation (assignment 61)))
  let bounded63 := below_succ bounded62 (top_allows (Sign.withNegation globalNegation (assignment 62)))
  let bounded64 := below_succ bounded63 (top_allows (Sign.withNegation globalNegation (assignment 63)))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C030.initial 64) (congrArg (Sign.withNegation globalNegation) hnode64) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (domain_from_eq (domain := Cases.C030.initial 65) (congrArg (Sign.withNegation globalNegation) hnode65) (Eq.refl Bool.true))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C030.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (domain_from_eq (domain := Cases.C030.initial 67) (congrArg (Sign.withNegation globalNegation) hnode67) (Eq.refl Bool.true))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C030.initial 68) (congrArg (Sign.withNegation globalNegation) hnode68) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (top_allows (Sign.withNegation globalNegation (assignment 69)))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C030.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C030.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C030.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C030.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C030.initial 74) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Cases.C030.initial 75) (congrArg (Sign.withNegation globalNegation) hnode75) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Cases.C030.initial 76) (congrArg (Sign.withNegation globalNegation) hnode76) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C030.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (top_allows (Sign.withNegation globalNegation (assignment 78)))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C030.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (domain_from_eq (domain := Cases.C030.initial 80) (congrArg (Sign.withNegation globalNegation) hnode80) (Eq.refl Bool.true))
  let bounded82 := below_succ bounded81 (top_allows (Sign.withNegation globalNegation (assignment 81)))
  let bounded83 := below_succ bounded82 (top_allows (Sign.withNegation globalNegation (assignment 82)))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C030.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (top_allows (Sign.withNegation globalNegation (assignment 84)))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C030.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C030.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C030.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Cases.C030.initial 88) (congrArg (Sign.withNegation globalNegation) hnode88) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (top_allows (Sign.withNegation globalNegation (assignment 89)))
  let bounded91 := below_succ bounded90 (top_allows (Sign.withNegation globalNegation (assignment 90)))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C030.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (top_allows (Sign.withNegation globalNegation (assignment 92)))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C030.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C030.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C030.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C030.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (domain_from_eq (domain := Cases.C030.initial 97) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C030.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C030.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C030.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C030.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C030.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C030.initial 103) (congrArg (Sign.withNegation globalNegation) hnode103) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C030.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (top_allows (Sign.withNegation globalNegation (assignment 105)))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C030.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C030.initial 107) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C030.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C030.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C030.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C030.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C030.initial 112) (congrArg (Sign.withNegation globalNegation) hnode112) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C030.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C030.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C030.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C030.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C030.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C030.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C030.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (top_allows (Sign.withNegation globalNegation (assignment 120)))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C030.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (top_allows (Sign.withNegation globalNegation (assignment 122)))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C030.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C030.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Cases.C030.initial 125) (congrArg (Sign.withNegation globalNegation) hnode125) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (domain_from_eq (domain := Cases.C030.initial 126) (congrArg (Sign.withNegation globalNegation) hnode126) (Eq.refl Bool.true))
  let bounded128 := below_succ bounded127 (domain_from_eq (domain := Cases.C030.initial 127) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded129 := below_succ bounded128 (domain_from_eq (domain := Cases.C030.initial 128) (congrArg (Sign.withNegation globalNegation) hnode128) (Eq.refl Bool.true))
  let bounded130 := below_succ bounded129 (top_allows (Sign.withNegation globalNegation (assignment 129)))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C030.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C030.initial 131) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C030.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C030.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C030.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C030.initial 135) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C030.initial 136) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C030.initial 137) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C030.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C030.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C030.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C030.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C030.initial 142) (congrArg (Sign.withNegation globalNegation) (h_zero 10 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C030.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C030.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C030.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (top_allows (Sign.withNegation globalNegation (assignment 146)))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C030.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C030.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C030.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C030.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C030.initial 151) (congrArg (Sign.withNegation globalNegation) hnode151) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C030.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C030.initial 153) (congrArg (Sign.withNegation globalNegation) hnode153) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (domain_from_eq (domain := Cases.C030.initial 154) (congrArg (Sign.withNegation globalNegation) hnode154) (Eq.refl Bool.true))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C030.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C030.initial 156) (congrArg (Sign.withNegation globalNegation) (h_zero 11 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C030.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C030.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C030.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C030.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (top_allows (Sign.withNegation globalNegation (assignment 161)))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Cases.C030.initial 162) (congrArg (Sign.withNegation globalNegation) hnode162) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C030.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (top_allows (Sign.withNegation globalNegation (assignment 164)))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C030.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (top_allows (Sign.withNegation globalNegation (assignment 166)))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C030.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (domain_from_eq (domain := Cases.C030.initial 168) (congrArg (Sign.withNegation globalNegation) hnode168) (Eq.refl Bool.true))
  let bounded170 := below_succ bounded169 (top_allows (Sign.withNegation globalNegation (assignment 169)))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C030.initial 170) (congrArg (Sign.withNegation globalNegation) hnode170) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C030.initial 171) (congrArg (Sign.withNegation globalNegation) hnode171) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C030.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C030.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C030.initial 174) (congrArg (Sign.withNegation globalNegation) (h_zero 12 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C030.initial 175) (congrArg (Sign.withNegation globalNegation) hnode175) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C030.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Cases.C030.initial 177) (congrArg (Sign.withNegation globalNegation) hnode177) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C030.initial 178) (congrArg (Sign.withNegation globalNegation) hnode178) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C030.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C030.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C030.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C030.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (top_allows (Sign.withNegation globalNegation (assignment 183)))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Cases.C030.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C030.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Cases.C030.initial 186) (congrArg (Sign.withNegation globalNegation) hnode186) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C030.initial 187) (congrArg (Sign.withNegation globalNegation) hnode187) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C030.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (top_allows (Sign.withNegation globalNegation (assignment 189)))
  let bounded191 := below_succ bounded190 (top_allows (Sign.withNegation globalNegation (assignment 190)))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C030.initial 191) (congrArg (Sign.withNegation globalNegation) hnode191) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (top_allows (Sign.withNegation globalNegation (assignment 192)))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C030.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Cases.C030.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (top_allows (Sign.withNegation globalNegation (assignment 195)))
  let bounded197 := below_succ bounded196 (top_allows (Sign.withNegation globalNegation (assignment 196)))
  let bounded198 := below_succ bounded197 (domain_from_eq (domain := Cases.C030.initial 197) (congrArg (Sign.withNegation globalNegation) hnode197) (Eq.refl Bool.true))
  let bounded199 := below_succ bounded198 (top_allows (Sign.withNegation globalNegation (assignment 198)))
  let bounded200 := below_succ bounded199 (domain_from_eq (domain := Cases.C030.initial 199) (congrArg (Sign.withNegation globalNegation) hnode199) (Eq.refl Bool.true))
  let bounded201 := below_succ bounded200 (domain_from_eq (domain := Cases.C030.initial 200) (congrArg (Sign.withNegation globalNegation) hnode200) (Eq.refl Bool.true))
  let bounded202 := below_succ bounded201 (top_allows (Sign.withNegation globalNegation (assignment 201)))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C030.initial 202) (congrArg (Sign.withNegation globalNegation) hnode202) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (top_allows (Sign.withNegation globalNegation (assignment 203)))
  let bounded205 := below_succ bounded204 (domain_from_eq (domain := Cases.C030.initial 204) (congrArg (Sign.withNegation globalNegation) hnode204) (Eq.refl Bool.true))
  let bounded206 := below_succ bounded205 (top_allows (Sign.withNegation globalNegation (assignment 205)))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Cases.C030.initial 206) (congrArg (Sign.withNegation globalNegation) hnode206) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (top_allows (Sign.withNegation globalNegation (assignment 207)))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C030.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C030.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (top_allows (Sign.withNegation globalNegation (assignment 210)))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C030.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C030.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C030.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C030.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (top_allows (Sign.withNegation globalNegation (assignment 215)))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C030.initial 216) (congrArg (Sign.withNegation globalNegation) hnode216) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C030.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C030.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Cases.C030.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C030.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (domain_from_eq (domain := Cases.C030.initial 221) (congrArg (Sign.withNegation globalNegation) hnode221) (Eq.refl Bool.true))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C030.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C030.initial 223) (congrArg (Sign.withNegation globalNegation) (h_zero 13 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C030.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C030.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C030.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C030.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C030.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Cases.C030.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C030.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (domain_from_eq (domain := Cases.C030.initial 231) (congrArg (Sign.withNegation globalNegation) hnode231) (Eq.refl Bool.true))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C030.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (domain_from_eq (domain := Cases.C030.initial 233) (congrArg (Sign.withNegation globalNegation) hnode233) (Eq.refl Bool.true))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C030.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (top_allows (Sign.withNegation globalNegation (assignment 235)))
  let bounded237 := below_succ bounded236 (top_allows (Sign.withNegation globalNegation (assignment 236)))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C030.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C030.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Cases.C030.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (top_allows (Sign.withNegation globalNegation (assignment 240)))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C030.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (top_allows (Sign.withNegation globalNegation (assignment 242)))
  let bounded244 := below_succ bounded243 (top_allows (Sign.withNegation globalNegation (assignment 243)))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C030.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C030.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C030.initial 246) (congrArg (Sign.withNegation globalNegation) (h_zero 14 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C030.initial 247) (congrArg (Sign.withNegation globalNegation) hnode247) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C030.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (domain_from_eq (domain := Cases.C030.initial 249) (congrArg (Sign.withNegation globalNegation) hnode249) (Eq.refl Bool.true))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Cases.C030.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C030.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C030.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C030
#print axioms Papers.RationalityTen.PureGP.Initializers.C030.support_sign_contradiction
