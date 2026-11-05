module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C029

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C029
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 1
def globalNegation : Bool := Bool.false
def edgeTable : Table SupportEdge := (Table.node 117 (Table.node 58 (Table.node 29 (Table.node 14 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 11 26 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 11 36 Bool.false)) (Table.leaf (SupportEdge.mk 11 46 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 11 47 Bool.false)) (Table.leaf (SupportEdge.mk 14 29 Bool.false))) (Table.node 6 (Table.leaf (SupportEdge.mk 14 39 Bool.false)) (Table.leaf (SupportEdge.mk 14 50 Bool.true))))) (Table.node 10 (Table.node 8 (Table.leaf (SupportEdge.mk 14 51 Bool.true)) (Table.node 9 (Table.leaf (SupportEdge.mk 17 32 Bool.false)) (Table.leaf (SupportEdge.mk 17 42 Bool.false)))) (Table.node 12 (Table.node 11 (Table.leaf (SupportEdge.mk 17 53 Bool.true)) (Table.leaf (SupportEdge.mk 17 54 Bool.true))) (Table.node 13 (Table.leaf (SupportEdge.mk 83 103 Bool.false)) (Table.leaf (SupportEdge.mk 83 113 Bool.false)))))) (Table.node 21 (Table.node 17 (Table.node 15 (Table.leaf (SupportEdge.mk 83 122 Bool.false)) (Table.node 16 (Table.leaf (SupportEdge.mk 83 123 Bool.false)) (Table.leaf (SupportEdge.mk 153 173 Bool.false)))) (Table.node 19 (Table.node 18 (Table.leaf (SupportEdge.mk 153 183 Bool.false)) (Table.leaf (SupportEdge.mk 153 192 Bool.false))) (Table.node 20 (Table.leaf (SupportEdge.mk 153 193 Bool.false)) (Table.leaf (SupportEdge.mk 1 56 Bool.false))))) (Table.node 25 (Table.node 23 (Table.node 22 (Table.leaf (SupportEdge.mk 1 61 Bool.true)) (Table.leaf (SupportEdge.mk 1 62 Bool.true))) (Table.node 24 (Table.leaf (SupportEdge.mk 1 64 Bool.true)) (Table.leaf (SupportEdge.mk 4 59 Bool.false)))) (Table.node 27 (Table.node 26 (Table.leaf (SupportEdge.mk 4 66 Bool.false)) (Table.leaf (SupportEdge.mk 4 68 Bool.false))) (Table.node 28 (Table.leaf (SupportEdge.mk 4 70 Bool.true)) (Table.leaf (SupportEdge.mk 13 73 Bool.true))))))) (Table.node 43 (Table.node 36 (Table.node 32 (Table.node 30 (Table.leaf (SupportEdge.mk 13 82 Bool.false)) (Table.node 31 (Table.leaf (SupportEdge.mk 13 84 Bool.false)) (Table.leaf (SupportEdge.mk 13 86 Bool.true)))) (Table.node 34 (Table.node 33 (Table.leaf (SupportEdge.mk 28 93 Bool.true)) (Table.leaf (SupportEdge.mk 28 102 Bool.false))) (Table.node 35 (Table.leaf (SupportEdge.mk 28 104 Bool.false)) (Table.leaf (SupportEdge.mk 28 106 Bool.true))))) (Table.node 39 (Table.node 37 (Table.leaf (SupportEdge.mk 133 198 Bool.false)) (Table.node 38 (Table.leaf (SupportEdge.mk 133 207 Bool.true)) (Table.leaf (SupportEdge.mk 133 209 Bool.true)))) (Table.node 41 (Table.node 40 (Table.leaf (SupportEdge.mk 133 211 Bool.false)) (Table.leaf (SupportEdge.mk 22 57 Bool.false))) (Table.node 42 (Table.leaf (SupportEdge.mk 22 91 Bool.false)) (Table.leaf (SupportEdge.mk 22 95 Bool.true)))))) (Table.node 50 (Table.node 46 (Table.node 44 (Table.leaf (SupportEdge.mk 22 96 Bool.true)) (Table.node 45 (Table.leaf (SupportEdge.mk 25 60 Bool.false)) (Table.leaf (SupportEdge.mk 25 94 Bool.false)))) (Table.node 48 (Table.node 47 (Table.leaf (SupportEdge.mk 25 99 Bool.false)) (Table.leaf (SupportEdge.mk 25 100 Bool.false))) (Table.node 49 (Table.leaf (SupportEdge.mk 32 67 Bool.false)) (Table.leaf (SupportEdge.mk 32 103 Bool.true))))) (Table.node 54 (Table.node 52 (Table.node 51 (Table.leaf (SupportEdge.mk 32 108 Bool.false)) (Table.leaf (SupportEdge.mk 32 109 Bool.false))) (Table.node 53 (Table.leaf (SupportEdge.mk 42 77 Bool.false)) (Table.leaf (SupportEdge.mk 42 113 Bool.true)))) (Table.node 56 (Table.node 55 (Table.leaf (SupportEdge.mk 42 118 Bool.false)) (Table.leaf (SupportEdge.mk 42 119 Bool.false))) (Table.node 57 (Table.leaf (SupportEdge.mk 167 202 Bool.false)) (Table.leaf (SupportEdge.mk 167 233 Bool.false)))))))) (Table.node 87 (Table.node 72 (Table.node 65 (Table.node 61 (Table.node 59 (Table.leaf (SupportEdge.mk 167 238 Bool.true)) (Table.node 60 (Table.leaf (SupportEdge.mk 167 239 Bool.true)) (Table.leaf (SupportEdge.mk 23 58 Bool.false)))) (Table.node 63 (Table.node 62 (Table.leaf (SupportEdge.mk 23 92 Bool.false)) (Table.leaf (SupportEdge.mk 23 95 Bool.false))) (Table.node 64 (Table.leaf (SupportEdge.mk 23 99 Bool.true)) (Table.leaf (SupportEdge.mk 24 59 Bool.false))))) (Table.node 68 (Table.node 66 (Table.leaf (SupportEdge.mk 24 93 Bool.false)) (Table.node 67 (Table.leaf (SupportEdge.mk 24 96 Bool.false)) (Table.leaf (SupportEdge.mk 24 100 Bool.true)))) (Table.node 70 (Table.node 69 (Table.leaf (SupportEdge.mk 33 68 Bool.false)) (Table.leaf (SupportEdge.mk 33 104 Bool.true))) (Table.node 71 (Table.leaf (SupportEdge.mk 33 107 Bool.true)) (Table.leaf (SupportEdge.mk 33 110 Bool.true)))))) (Table.node 79 (Table.node 75 (Table.node 73 (Table.leaf (SupportEdge.mk 43 78 Bool.false)) (Table.node 74 (Table.leaf (SupportEdge.mk 43 114 Bool.true)) (Table.leaf (SupportEdge.mk 43 117 Bool.true)))) (Table.node 77 (Table.node 76 (Table.leaf (SupportEdge.mk 43 120 Bool.true)) (Table.leaf (SupportEdge.mk 168 203 Bool.false))) (Table.node 78 (Table.leaf (SupportEdge.mk 168 234 Bool.false)) (Table.leaf (SupportEdge.mk 168 237 Bool.false))))) (Table.node 83 (Table.node 81 (Table.node 80 (Table.leaf (SupportEdge.mk 168 240 Bool.false)) (Table.leaf (SupportEdge.mk 29 64 Bool.false))) (Table.node 82 (Table.leaf (SupportEdge.mk 29 94 Bool.true)) (Table.leaf (SupportEdge.mk 29 103 Bool.false)))) (Table.node 85 (Table.node 84 (Table.leaf (SupportEdge.mk 29 105 Bool.false)) (Table.leaf (SupportEdge.mk 29 106 Bool.false))) (Table.node 86 (Table.leaf (SupportEdge.mk 36 71 Bool.false)) (Table.leaf (SupportEdge.mk 36 91 Bool.false))))))) (Table.node 102 (Table.node 94 (Table.node 90 (Table.node 88 (Table.leaf (SupportEdge.mk 36 111 Bool.true)) (Table.node 89 (Table.leaf (SupportEdge.mk 36 113 Bool.true)) (Table.leaf (SupportEdge.mk 38 73 Bool.false)))) (Table.node 92 (Table.node 91 (Table.leaf (SupportEdge.mk 38 93 Bool.false)) (Table.leaf (SupportEdge.mk 38 114 Bool.false))) (Table.node 93 (Table.leaf (SupportEdge.mk 38 116 Bool.true)) (Table.leaf (SupportEdge.mk 41 76 Bool.false))))) (Table.node 98 (Table.node 96 (Table.node 95 (Table.leaf (SupportEdge.mk 41 96 Bool.false)) (Table.leaf (SupportEdge.mk 41 117 Bool.false))) (Table.node 97 (Table.leaf (SupportEdge.mk 41 119 Bool.true)) (Table.leaf (SupportEdge.mk 47 82 Bool.false)))) (Table.node 100 (Table.node 99 (Table.leaf (SupportEdge.mk 47 102 Bool.false)) (Table.leaf (SupportEdge.mk 47 121 Bool.false))) (Table.node 101 (Table.leaf (SupportEdge.mk 47 123 Bool.true)) (Table.leaf (SupportEdge.mk 182 217 Bool.false)))))) (Table.node 109 (Table.node 105 (Table.node 103 (Table.leaf (SupportEdge.mk 182 232 Bool.false)) (Table.node 104 (Table.leaf (SupportEdge.mk 182 246 Bool.true)) (Table.leaf (SupportEdge.mk 182 248 Bool.false)))) (Table.node 107 (Table.node 106 (Table.leaf (SupportEdge.mk 1 126 Bool.true)) (Table.leaf (SupportEdge.mk 1 131 Bool.false))) (Table.node 108 (Table.leaf (SupportEdge.mk 1 132 Bool.false)) (Table.leaf (SupportEdge.mk 1 133 Bool.false))))) (Table.node 113 (Table.node 111 (Table.node 110 (Table.leaf (SupportEdge.mk 5 130 Bool.true)) (Table.leaf (SupportEdge.mk 5 137 Bool.true))) (Table.node 112 (Table.leaf (SupportEdge.mk 5 139 Bool.true)) (Table.leaf (SupportEdge.mk 5 140 Bool.true)))) (Table.node 115 (Table.node 114 (Table.leaf (SupportEdge.mk 14 144 Bool.false)) (Table.leaf (SupportEdge.mk 14 153 Bool.true))) (Table.node 116 (Table.leaf (SupportEdge.mk 14 155 Bool.true)) (Table.leaf (SupportEdge.mk 14 156 Bool.true))))))))) (Table.node 176 (Table.node 146 (Table.node 131 (Table.node 124 (Table.node 120 (Table.node 118 (Table.leaf (SupportEdge.mk 29 164 Bool.false)) (Table.node 119 (Table.leaf (SupportEdge.mk 29 173 Bool.true)) (Table.leaf (SupportEdge.mk 29 175 Bool.true)))) (Table.node 122 (Table.node 121 (Table.leaf (SupportEdge.mk 29 176 Bool.true)) (Table.leaf (SupportEdge.mk 64 199 Bool.false))) (Table.node 123 (Table.leaf (SupportEdge.mk 64 208 Bool.true)) (Table.leaf (SupportEdge.mk 64 210 Bool.true))))) (Table.node 127 (Table.node 125 (Table.leaf (SupportEdge.mk 64 211 Bool.true)) (Table.node 126 (Table.leaf (SupportEdge.mk 8 128 Bool.false)) (Table.leaf (SupportEdge.mk 8 142 Bool.true)))) (Table.node 129 (Table.node 128 (Table.leaf (SupportEdge.mk 8 145 Bool.true)) (Table.leaf (SupportEdge.mk 8 148 Bool.false))) (Table.node 130 (Table.leaf (SupportEdge.mk 10 130 Bool.false)) (Table.leaf (SupportEdge.mk 10 144 Bool.true)))))) (Table.node 138 (Table.node 134 (Table.node 132 (Table.leaf (SupportEdge.mk 10 147 Bool.true)) (Table.node 133 (Table.leaf (SupportEdge.mk 10 150 Bool.true)) (Table.leaf (SupportEdge.mk 19 139 Bool.false)))) (Table.node 136 (Table.node 135 (Table.leaf (SupportEdge.mk 19 155 Bool.false)) (Table.leaf (SupportEdge.mk 19 158 Bool.false))) (Table.node 137 (Table.leaf (SupportEdge.mk 19 160 Bool.true)) (Table.leaf (SupportEdge.mk 44 169 Bool.true))))) (Table.node 142 (Table.node 140 (Table.node 139 (Table.leaf (SupportEdge.mk 44 185 Bool.false)) (Table.leaf (SupportEdge.mk 44 188 Bool.false))) (Table.node 141 (Table.leaf (SupportEdge.mk 44 190 Bool.true)) (Table.leaf (SupportEdge.mk 79 204 Bool.true)))) (Table.node 144 (Table.node 143 (Table.leaf (SupportEdge.mk 79 220 Bool.false)) (Table.leaf (SupportEdge.mk 79 223 Bool.false))) (Table.node 145 (Table.leaf (SupportEdge.mk 79 225 Bool.true)) (Table.leaf (SupportEdge.mk 11 131 Bool.false))))))) (Table.node 161 (Table.node 153 (Table.node 149 (Table.node 147 (Table.leaf (SupportEdge.mk 11 141 Bool.false)) (Table.node 148 (Table.leaf (SupportEdge.mk 11 152 Bool.false)) (Table.leaf (SupportEdge.mk 11 153 Bool.false)))) (Table.node 151 (Table.node 150 (Table.leaf (SupportEdge.mk 12 132 Bool.false)) (Table.leaf (SupportEdge.mk 12 142 Bool.false))) (Table.node 152 (Table.leaf (SupportEdge.mk 12 154 Bool.false)) (Table.leaf (SupportEdge.mk 12 155 Bool.false))))) (Table.node 157 (Table.node 155 (Table.node 154 (Table.leaf (SupportEdge.mk 15 135 Bool.false)) (Table.leaf (SupportEdge.mk 15 145 Bool.false))) (Table.node 156 (Table.leaf (SupportEdge.mk 15 157 Bool.false)) (Table.leaf (SupportEdge.mk 15 158 Bool.false)))) (Table.node 159 (Table.node 158 (Table.leaf (SupportEdge.mk 46 171 Bool.true)) (Table.leaf (SupportEdge.mk 46 181 Bool.true))) (Table.node 160 (Table.leaf (SupportEdge.mk 46 191 Bool.false)) (Table.leaf (SupportEdge.mk 46 192 Bool.false)))))) (Table.node 168 (Table.node 164 (Table.node 162 (Table.leaf (SupportEdge.mk 81 206 Bool.true)) (Table.node 163 (Table.leaf (SupportEdge.mk 81 216 Bool.true)) (Table.leaf (SupportEdge.mk 81 226 Bool.false)))) (Table.node 166 (Table.node 165 (Table.leaf (SupportEdge.mk 81 227 Bool.false)) (Table.leaf (SupportEdge.mk 40 145 Bool.true))) (Table.node 167 (Table.leaf (SupportEdge.mk 40 165 Bool.true)) (Table.leaf (SupportEdge.mk 40 181 Bool.false))))) (Table.node 172 (Table.node 170 (Table.node 169 (Table.leaf (SupportEdge.mk 40 188 Bool.false)) (Table.leaf (SupportEdge.mk 41 146 Bool.true))) (Table.node 171 (Table.leaf (SupportEdge.mk 41 166 Bool.true)) (Table.leaf (SupportEdge.mk 41 182 Bool.false)))) (Table.node 174 (Table.node 173 (Table.leaf (SupportEdge.mk 41 189 Bool.false)) (Table.leaf (SupportEdge.mk 43 148 Bool.true))) (Table.node 175 (Table.leaf (SupportEdge.mk 43 168 Bool.true)) (Table.leaf (SupportEdge.mk 43 184 Bool.false)))))))) (Table.node 205 (Table.node 190 (Table.node 183 (Table.node 179 (Table.node 177 (Table.leaf (SupportEdge.mk 43 190 Bool.false)) (Table.node 178 (Table.leaf (SupportEdge.mk 52 157 Bool.true)) (Table.leaf (SupportEdge.mk 52 177 Bool.true)))) (Table.node 181 (Table.node 180 (Table.leaf (SupportEdge.mk 52 191 Bool.true)) (Table.leaf (SupportEdge.mk 52 195 Bool.false))) (Table.node 182 (Table.leaf (SupportEdge.mk 117 222 Bool.false)) (Table.leaf (SupportEdge.mk 117 237 Bool.false))))) (Table.node 186 (Table.node 184 (Table.leaf (SupportEdge.mk 117 246 Bool.true)) (Table.node 185 (Table.leaf (SupportEdge.mk 117 250 Bool.false)) (Table.leaf (SupportEdge.mk 42 147 Bool.true)))) (Table.node 188 (Table.node 187 (Table.leaf (SupportEdge.mk 42 167 Bool.true)) (Table.leaf (SupportEdge.mk 42 183 Bool.false))) (Table.node 189 (Table.leaf (SupportEdge.mk 42 188 Bool.true)) (Table.leaf (SupportEdge.mk 42 189 Bool.true)))))) (Table.node 197 (Table.node 193 (Table.node 191 (Table.leaf (SupportEdge.mk 68 138 Bool.false)) (Table.node 192 (Table.leaf (SupportEdge.mk 68 203 Bool.false)) (Table.leaf (SupportEdge.mk 68 209 Bool.false)))) (Table.node 195 (Table.node 194 (Table.leaf (SupportEdge.mk 68 212 Bool.false)) (Table.leaf (SupportEdge.mk 69 139 Bool.false))) (Table.node 196 (Table.leaf (SupportEdge.mk 69 204 Bool.false)) (Table.leaf (SupportEdge.mk 69 210 Bool.false))))) (Table.node 201 (Table.node 199 (Table.node 198 (Table.leaf (SupportEdge.mk 69 213 Bool.false)) (Table.leaf (SupportEdge.mk 70 140 Bool.false))) (Table.node 200 (Table.leaf (SupportEdge.mk 70 205 Bool.false)) (Table.leaf (SupportEdge.mk 70 211 Bool.false)))) (Table.node 203 (Table.node 202 (Table.leaf (SupportEdge.mk 70 214 Bool.false)) (Table.leaf (SupportEdge.mk 90 160 Bool.false))) (Table.node 204 (Table.leaf (SupportEdge.mk 90 225 Bool.true)) (Table.leaf (SupportEdge.mk 90 229 Bool.true))))))) (Table.node 220 (Table.node 212 (Table.node 208 (Table.node 206 (Table.leaf (SupportEdge.mk 90 230 Bool.true)) (Table.node 207 (Table.leaf (SupportEdge.mk 110 180 Bool.false)) (Table.leaf (SupportEdge.mk 110 240 Bool.true)))) (Table.node 210 (Table.node 209 (Table.leaf (SupportEdge.mk 110 244 Bool.true)) (Table.leaf (SupportEdge.mk 110 245 Bool.true))) (Table.node 211 (Table.leaf (SupportEdge.mk 81 151 Bool.false)) (Table.leaf (SupportEdge.mk 81 206 Bool.true))))) (Table.node 216 (Table.node 214 (Table.node 213 (Table.leaf (SupportEdge.mk 81 216 Bool.true)) (Table.leaf (SupportEdge.mk 81 227 Bool.false))) (Table.node 215 (Table.leaf (SupportEdge.mk 82 152 Bool.false)) (Table.leaf (SupportEdge.mk 82 207 Bool.true)))) (Table.node 218 (Table.node 217 (Table.leaf (SupportEdge.mk 82 217 Bool.true)) (Table.leaf (SupportEdge.mk 82 228 Bool.false))) (Table.node 219 (Table.leaf (SupportEdge.mk 84 154 Bool.false)) (Table.leaf (SupportEdge.mk 84 209 Bool.true)))))) (Table.node 227 (Table.node 223 (Table.node 221 (Table.leaf (SupportEdge.mk 84 219 Bool.true)) (Table.node 222 (Table.leaf (SupportEdge.mk 84 229 Bool.false)) (Table.leaf (SupportEdge.mk 87 157 Bool.false)))) (Table.node 225 (Table.node 224 (Table.leaf (SupportEdge.mk 87 212 Bool.true)) (Table.leaf (SupportEdge.mk 87 222 Bool.true))) (Table.node 226 (Table.leaf (SupportEdge.mk 87 230 Bool.false)) (Table.leaf (SupportEdge.mk 121 191 Bool.false))))) (Table.node 231 (Table.node 229 (Table.node 228 (Table.leaf (SupportEdge.mk 121 241 Bool.false)) (Table.leaf (SupportEdge.mk 121 246 Bool.false))) (Table.node 230 (Table.leaf (SupportEdge.mk 121 251 Bool.false)) (Table.leaf (SupportEdge.mk 99 169 Bool.false)))) (Table.node 233 (Table.node 232 (Table.leaf (SupportEdge.mk 99 204 Bool.false)) (Table.leaf (SupportEdge.mk 99 235 Bool.false))) (Table.node 234 (Table.leaf (SupportEdge.mk 99 238 Bool.false)) (Table.leaf (SupportEdge.mk 99 240 Bool.true))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf 48) (Table.node 2 (Table.leaf 63) (Table.leaf 81))) (Table.node 5 (Table.node 4 (Table.leaf 97) (Table.leaf 98)) (Table.node 6 (Table.leaf 112) (Table.leaf 134)))) (Table.node 11 (Table.node 9 (Table.node 8 (Table.leaf 149) (Table.leaf 151)) (Table.node 10 (Table.leaf 187) (Table.leaf 206))) (Table.node 13 (Table.node 12 (Table.leaf 215) (Table.leaf 216)) (Table.node 14 (Table.leaf 226) (Table.leaf 227)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 235 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 15 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C029.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode56 : Eq (assignment 56) Sign.positive :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode61 : Eq (assignment 61) Sign.negative :=
    Eq.trans (h_support 21 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode62 : Eq (assignment 62) Sign.negative :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode64 : Eq (assignment 64) Sign.negative :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode126 : Eq (assignment 126) Sign.negative :=
    Eq.trans (h_support 105 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode131 : Eq (assignment 131) Sign.positive :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode132 : Eq (assignment 132) Sign.positive :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode133 : Eq (assignment 133) Sign.positive :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode11 : Eq (assignment 11) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 145 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode131)
  let hnode12 : Eq (assignment 12) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 149 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode132)
  let hnode29 : Eq (assignment 29) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 80 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode64)
  let hnode198 : Eq (assignment 198) Sign.positive :=
    Eq.trans (h_support 36 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode133)
  let hnode199 : Eq (assignment 199) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode64)
  let hnode207 : Eq (assignment 207) Sign.negative :=
    Eq.trans (h_support 37 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode133)
  let hnode208 : Eq (assignment 208) Sign.positive :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode64)
  let hnode209 : Eq (assignment 209) Sign.negative :=
    Eq.trans (h_support 38 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode133)
  let hnode210 : Eq (assignment 210) Sign.positive :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode64)
  let hnode211 : Eq (assignment 211) Sign.positive :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode64)
  let hnode14 : Eq (assignment 14) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 4 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode26 : Eq (assignment 26) Sign.positive :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode36 : Eq (assignment 36) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode46 : Eq (assignment 46) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode47 : Eq (assignment 47) Sign.positive :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode68 : Eq (assignment 68) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 192 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode209)
  let hnode69 : Eq (assignment 69) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 196 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode210)
  let hnode70 : Eq (assignment 70) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 200 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode211)
  let hnode82 : Eq (assignment 82) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 215 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode207)
  let hnode84 : Eq (assignment 84) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 219 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode209)
  let hnode94 : Eq (assignment 94) Sign.positive :=
    Eq.trans (h_support 81 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode103 : Eq (assignment 103) Sign.negative :=
    Eq.trans (h_support 82 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode105 : Eq (assignment 105) Sign.negative :=
    Eq.trans (h_support 83 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode106 : Eq (assignment 106) Sign.negative :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode141 : Eq (assignment 141) Sign.positive :=
    Eq.trans (h_support 146 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode142 : Eq (assignment 142) Sign.positive :=
    Eq.trans (h_support 150 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode152 : Eq (assignment 152) Sign.positive :=
    Eq.trans (h_support 147 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode153 : Eq (assignment 153) Sign.positive :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode154 : Eq (assignment 154) Sign.positive :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode155 : Eq (assignment 155) Sign.positive :=
    Eq.trans (h_support 152 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode164 : Eq (assignment 164) Sign.negative :=
    Eq.trans (h_support 117 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode173 : Eq (assignment 173) Sign.positive :=
    Eq.trans (h_support 118 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode175 : Eq (assignment 175) Sign.positive :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode176 : Eq (assignment 176) Sign.positive :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode4 : Eq (assignment 4) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 27 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode70)
  let hnode8 : Eq (assignment 8) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 126 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode142)
  let hnode13 : Eq (assignment 13) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 29 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode82)
  let hnode19 : Eq (assignment 19) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 134 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode155)
  let hnode25 : Eq (assignment 25) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 45 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode94)
  let hnode28 : Eq (assignment 28) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 35 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode106)
  let hnode32 : Eq (assignment 32) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 49 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode103)
  let hnode33 : Eq (assignment 33) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 68 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode39 : Eq (assignment 39) Sign.negative :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode50 : Eq (assignment 50) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode51 : Eq (assignment 51) Sign.positive :=
    Eq.trans (h_support 7 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode71 : Eq (assignment 71) Sign.positive :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode83 : Eq (assignment 83) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 12 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode103)
  let hnode91 : Eq (assignment 91) Sign.positive :=
    Eq.trans (h_support 86 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode102 : Eq (assignment 102) Sign.positive :=
    Eq.trans (h_support 98 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode111 : Eq (assignment 111) Sign.negative :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode36)
  let hnode113 : Eq (assignment 113) Sign.negative :=
    Eq.trans (h_support 88 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode36)
  let hnode121 : Eq (assignment 121) Sign.positive :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode123 : Eq (assignment 123) Sign.negative :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode138 : Eq (assignment 138) Sign.negative :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode139 : Eq (assignment 139) Sign.positive :=
    Eq.trans (h_support 194 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode140 : Eq (assignment 140) Sign.positive :=
    Eq.trans (h_support 198 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode144 : Eq (assignment 144) Sign.negative :=
    Eq.trans (h_support 113 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode156 : Eq (assignment 156) Sign.positive :=
    Eq.trans (h_support 116 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode171 : Eq (assignment 171) Sign.negative :=
    Eq.trans (h_support 157 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode46)
  let hnode181 : Eq (assignment 181) Sign.negative :=
    Eq.trans (h_support 158 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode46)
  let hnode183 : Eq (assignment 183) Sign.positive :=
    Eq.trans (h_support 17 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode153)
  let hnode191 : Eq (assignment 191) Sign.positive :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode192 : Eq (assignment 192) Sign.positive :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode193 : Eq (assignment 193) Sign.positive :=
    Eq.trans (h_support 19 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode153)
  let hnode203 : Eq (assignment 203) Sign.negative :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode204 : Eq (assignment 204) Sign.positive :=
    Eq.trans (h_support 195 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode205 : Eq (assignment 205) Sign.positive :=
    Eq.trans (h_support 199 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode212 : Eq (assignment 212) Sign.negative :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode213 : Eq (assignment 213) Sign.positive :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode214 : Eq (assignment 214) Sign.positive :=
    Eq.trans (h_support 201 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode217 : Eq (assignment 217) Sign.negative :=
    Eq.trans (h_support 216 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode82)
  let hnode219 : Eq (assignment 219) Sign.negative :=
    Eq.trans (h_support 220 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode84)
  let hnode228 : Eq (assignment 228) Sign.positive :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode82)
  let hnode229 : Eq (assignment 229) Sign.positive :=
    Eq.trans (h_support 221 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode84)
  let hnode5 : Eq (assignment 5) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 111 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode139)
  let hnode10 : Eq (assignment 10) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 130 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode144)
  let hnode17 : Eq (assignment 17) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 8 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode22 : Eq (assignment 22) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 41 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode40 : Eq (assignment 40) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 167 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode181)
  let hnode42 : Eq (assignment 42) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 53 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode113)
  let hnode52 : Eq (assignment 52) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 179 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode191)
  let hnode59 : Eq (assignment 59) Sign.negative :=
    Eq.trans (h_support 24 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode60 : Eq (assignment 60) Sign.positive :=
    Eq.trans (h_support 44 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode66 : Eq (assignment 66) Sign.negative :=
    Eq.trans (h_support 25 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode67 : Eq (assignment 67) Sign.positive :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode73 : Eq (assignment 73) Sign.negative :=
    Eq.trans (h_support 28 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode79 : Eq (assignment 79) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 141 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode204)
  let hnode86 : Eq (assignment 86) Sign.negative :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode87 : Eq (assignment 87) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 223 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode212)
  let hnode90 : Eq (assignment 90) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 204 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode229)
  let hnode93 : Eq (assignment 93) Sign.negative :=
    Eq.trans (h_support 32 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode99 : Eq (assignment 99) Sign.positive :=
    Eq.trans (h_support 46 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode100 : Eq (assignment 100) Sign.positive :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode104 : Eq (assignment 104) Sign.positive :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode107 : Eq (assignment 107) Sign.positive :=
    Eq.trans (h_support 70 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode108 : Eq (assignment 108) Sign.positive :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode109 : Eq (assignment 109) Sign.positive :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode110 : Eq (assignment 110) Sign.positive :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode122 : Eq (assignment 122) Sign.negative :=
    Eq.trans (h_support 14 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode83)
  let hnode128 : Eq (assignment 128) Sign.negative :=
    Eq.trans (h_support 125 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode145 : Eq (assignment 145) Sign.positive :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode148 : Eq (assignment 148) Sign.negative :=
    Eq.trans (h_support 128 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode158 : Eq (assignment 158) Sign.positive :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode160 : Eq (assignment 160) Sign.negative :=
    Eq.trans (h_support 136 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode19)
  let hnode168 : Eq (assignment 168) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 76 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode203)
  let hnode182 : Eq (assignment 182) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 101 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode217)
  let hnode241 : Eq (assignment 241) Sign.positive :=
    Eq.trans (h_support 227 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode246 : Eq (assignment 246) Sign.positive :=
    Eq.trans (h_support 228 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode251 : Eq (assignment 251) Sign.positive :=
    Eq.trans (h_support 229 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode15 : Eq (assignment 15) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 154 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode145)
  let hnode23 : Eq (assignment 23) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 63 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode99)
  let hnode24 : Eq (assignment 24) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 67 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode100)
  let hnode38 : Eq (assignment 38) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 90 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode93)
  let hnode41 : Eq (assignment 41) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 171 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode182)
  let hnode43 : Eq (assignment 43) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 173 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode148)
  let hnode53 : Eq (assignment 53) Sign.negative :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode54 : Eq (assignment 54) Sign.negative :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode57 : Eq (assignment 57) Sign.positive :=
    Eq.trans (h_support 40 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode77 : Eq (assignment 77) Sign.positive :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode42)
  let hnode95 : Eq (assignment 95) Sign.negative :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode96 : Eq (assignment 96) Sign.negative :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode117 : Eq (assignment 117) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 183 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode246)
  let hnode118 : Eq (assignment 118) Sign.positive :=
    Eq.trans (h_support 54 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode42)
  let hnode119 : Eq (assignment 119) Sign.positive :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode42)
  let hnode130 : Eq (assignment 130) Sign.positive :=
    Eq.trans (h_support 129 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode137 : Eq (assignment 137) Sign.positive :=
    Eq.trans (h_support 110 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode147 : Eq (assignment 147) Sign.negative :=
    Eq.trans (h_support 131 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode150 : Eq (assignment 150) Sign.negative :=
    Eq.trans (h_support 132 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode157 : Eq (assignment 157) Sign.positive :=
    Eq.trans (h_support 177 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode52)
  let hnode165 : Eq (assignment 165) Sign.positive :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode167 : Eq (assignment 167) Sign.negative :=
    Eq.trans (h_support 186 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode42)
  let hnode169 : Eq (assignment 169) Sign.positive :=
    Eq.trans (h_support 230 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode99)
  let hnode177 : Eq (assignment 177) Sign.positive :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode52)
  let hnode180 : Eq (assignment 180) Sign.positive :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode110)
  let hnode188 : Eq (assignment 188) Sign.negative :=
    Eq.trans (h_support 188 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode42)
  let hnode189 : Eq (assignment 189) Sign.negative :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode42)
  let hnode195 : Eq (assignment 195) Sign.negative :=
    Eq.trans (h_support 180 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode52)
  let hnode220 : Eq (assignment 220) Sign.negative :=
    Eq.trans (h_support 142 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode79)
  let hnode222 : Eq (assignment 222) Sign.negative :=
    Eq.trans (h_support 224 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode87)
  let hnode223 : Eq (assignment 223) Sign.negative :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode79)
  let hnode225 : Eq (assignment 225) Sign.positive :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode79)
  let hnode230 : Eq (assignment 230) Sign.positive :=
    Eq.trans (h_support 225 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode87)
  let hnode232 : Eq (assignment 232) Sign.negative :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode182)
  let hnode234 : Eq (assignment 234) Sign.negative :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode168)
  let hnode235 : Eq (assignment 235) Sign.positive :=
    Eq.trans (h_support 232 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode99)
  let hnode237 : Eq (assignment 237) Sign.negative :=
    Eq.trans (h_support 78 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode168)
  let hnode238 : Eq (assignment 238) Sign.positive :=
    Eq.trans (h_support 233 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode99)
  let hnode240 : Eq (assignment 240) Sign.negative :=
    Eq.trans (h_support 234 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode99)
  let hnode244 : Eq (assignment 244) Sign.negative :=
    Eq.trans (h_support 208 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode110)
  let hnode245 : Eq (assignment 245) Sign.negative :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode110)
  let hnode248 : Eq (assignment 248) Sign.negative :=
    Eq.trans (h_support 104 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode182)
  let hnode44 : Eq (assignment 44) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 137 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode169)
  let hnode58 : Eq (assignment 58) Sign.negative :=
    Eq.trans (h_support 60 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode76 : Eq (assignment 76) Sign.negative :=
    Eq.trans (h_support 93 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode78 : Eq (assignment 78) Sign.positive :=
    Eq.trans (h_support 72 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode92 : Eq (assignment 92) Sign.negative :=
    Eq.trans (h_support 61 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode114 : Eq (assignment 114) Sign.negative :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode116 : Eq (assignment 116) Sign.positive :=
    Eq.trans (h_support 92 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode120 : Eq (assignment 120) Sign.negative :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode135 : Eq (assignment 135) Sign.positive :=
    Eq.trans (h_support 153 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode146 : Eq (assignment 146) Sign.positive :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode166 : Eq (assignment 166) Sign.positive :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode184 : Eq (assignment 184) Sign.positive :=
    Eq.trans (h_support 175 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode190 : Eq (assignment 190) Sign.positive :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode202 : Eq (assignment 202) Sign.negative :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode167)
  let hnode233 : Eq (assignment 233) Sign.negative :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode167)
  let hnode239 : Eq (assignment 239) Sign.positive :=
    Eq.trans (h_support 59 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode167)
  let hnode250 : Eq (assignment 250) Sign.negative :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode117)
  let hnode185 : Eq (assignment 185) Sign.negative :=
    Eq.trans (h_support 138 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C029.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (top_allows (Sign.withNegation globalNegation (assignment 0)))
  let bounded2 := below_succ bounded1 (domain_from_eq (domain := Cases.C029.initial 1) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded3 := below_succ bounded2 (top_allows (Sign.withNegation globalNegation (assignment 2)))
  let bounded4 := below_succ bounded3 (top_allows (Sign.withNegation globalNegation (assignment 3)))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C029.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Cases.C029.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (top_allows (Sign.withNegation globalNegation (assignment 6)))
  let bounded8 := below_succ bounded7 (top_allows (Sign.withNegation globalNegation (assignment 7)))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C029.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (top_allows (Sign.withNegation globalNegation (assignment 9)))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C029.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (domain_from_eq (domain := Cases.C029.initial 11) (congrArg (Sign.withNegation globalNegation) hnode11) (Eq.refl Bool.true))
  let bounded13 := below_succ bounded12 (domain_from_eq (domain := Cases.C029.initial 12) (congrArg (Sign.withNegation globalNegation) hnode12) (Eq.refl Bool.true))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C029.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C029.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Cases.C029.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (top_allows (Sign.withNegation globalNegation (assignment 16)))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C029.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (top_allows (Sign.withNegation globalNegation (assignment 18)))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C029.initial 19) (congrArg (Sign.withNegation globalNegation) hnode19) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (top_allows (Sign.withNegation globalNegation (assignment 20)))
  let bounded22 := below_succ bounded21 (top_allows (Sign.withNegation globalNegation (assignment 21)))
  let bounded23 := below_succ bounded22 (domain_from_eq (domain := Cases.C029.initial 22) (congrArg (Sign.withNegation globalNegation) hnode22) (Eq.refl Bool.true))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C029.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C029.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C029.initial 25) (congrArg (Sign.withNegation globalNegation) hnode25) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Cases.C029.initial 26) (congrArg (Sign.withNegation globalNegation) hnode26) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (top_allows (Sign.withNegation globalNegation (assignment 27)))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C029.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C029.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (top_allows (Sign.withNegation globalNegation (assignment 30)))
  let bounded32 := below_succ bounded31 (top_allows (Sign.withNegation globalNegation (assignment 31)))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C029.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C029.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (top_allows (Sign.withNegation globalNegation (assignment 34)))
  let bounded36 := below_succ bounded35 (top_allows (Sign.withNegation globalNegation (assignment 35)))
  let bounded37 := below_succ bounded36 (domain_from_eq (domain := Cases.C029.initial 36) (congrArg (Sign.withNegation globalNegation) hnode36) (Eq.refl Bool.true))
  let bounded38 := below_succ bounded37 (top_allows (Sign.withNegation globalNegation (assignment 37)))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C029.initial 38) (congrArg (Sign.withNegation globalNegation) hnode38) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (domain_from_eq (domain := Cases.C029.initial 39) (congrArg (Sign.withNegation globalNegation) hnode39) (Eq.refl Bool.true))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Cases.C029.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C029.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C029.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (domain_from_eq (domain := Cases.C029.initial 43) (congrArg (Sign.withNegation globalNegation) hnode43) (Eq.refl Bool.true))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Cases.C029.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (top_allows (Sign.withNegation globalNegation (assignment 45)))
  let bounded47 := below_succ bounded46 (domain_from_eq (domain := Cases.C029.initial 46) (congrArg (Sign.withNegation globalNegation) hnode46) (Eq.refl Bool.true))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C029.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (domain_from_eq (domain := Cases.C029.initial 48) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded50 := below_succ bounded49 (top_allows (Sign.withNegation globalNegation (assignment 49)))
  let bounded51 := below_succ bounded50 (domain_from_eq (domain := Cases.C029.initial 50) (congrArg (Sign.withNegation globalNegation) hnode50) (Eq.refl Bool.true))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C029.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (domain_from_eq (domain := Cases.C029.initial 52) (congrArg (Sign.withNegation globalNegation) hnode52) (Eq.refl Bool.true))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Cases.C029.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Cases.C029.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (top_allows (Sign.withNegation globalNegation (assignment 55)))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C029.initial 56) (congrArg (Sign.withNegation globalNegation) hnode56) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C029.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C029.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C029.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C029.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Cases.C029.initial 61) (congrArg (Sign.withNegation globalNegation) hnode61) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C029.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C029.initial 63) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C029.initial 64) (congrArg (Sign.withNegation globalNegation) hnode64) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (top_allows (Sign.withNegation globalNegation (assignment 65)))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C029.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (domain_from_eq (domain := Cases.C029.initial 67) (congrArg (Sign.withNegation globalNegation) hnode67) (Eq.refl Bool.true))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C029.initial 68) (congrArg (Sign.withNegation globalNegation) hnode68) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C029.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C029.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C029.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (top_allows (Sign.withNegation globalNegation (assignment 72)))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C029.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (top_allows (Sign.withNegation globalNegation (assignment 74)))
  let bounded76 := below_succ bounded75 (top_allows (Sign.withNegation globalNegation (assignment 75)))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Cases.C029.initial 76) (congrArg (Sign.withNegation globalNegation) hnode76) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C029.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C029.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C029.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (top_allows (Sign.withNegation globalNegation (assignment 80)))
  let bounded82 := below_succ bounded81 (domain_from_eq (domain := Cases.C029.initial 81) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Cases.C029.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C029.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (domain_from_eq (domain := Cases.C029.initial 84) (congrArg (Sign.withNegation globalNegation) hnode84) (Eq.refl Bool.true))
  let bounded86 := below_succ bounded85 (top_allows (Sign.withNegation globalNegation (assignment 85)))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C029.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C029.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (top_allows (Sign.withNegation globalNegation (assignment 88)))
  let bounded90 := below_succ bounded89 (top_allows (Sign.withNegation globalNegation (assignment 89)))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C029.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C029.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C029.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C029.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C029.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C029.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C029.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (domain_from_eq (domain := Cases.C029.initial 97) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C029.initial 98) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C029.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C029.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (top_allows (Sign.withNegation globalNegation (assignment 101)))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C029.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C029.initial 103) (congrArg (Sign.withNegation globalNegation) hnode103) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C029.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C029.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C029.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C029.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C029.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C029.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C029.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C029.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C029.initial 112) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C029.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C029.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (top_allows (Sign.withNegation globalNegation (assignment 115)))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C029.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C029.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C029.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C029.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C029.initial 120) (congrArg (Sign.withNegation globalNegation) hnode120) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C029.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C029.initial 122) (congrArg (Sign.withNegation globalNegation) hnode122) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C029.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (top_allows (Sign.withNegation globalNegation (assignment 124)))
  let bounded126 := below_succ bounded125 (top_allows (Sign.withNegation globalNegation (assignment 125)))
  let bounded127 := below_succ bounded126 (domain_from_eq (domain := Cases.C029.initial 126) (congrArg (Sign.withNegation globalNegation) hnode126) (Eq.refl Bool.true))
  let bounded128 := below_succ bounded127 (top_allows (Sign.withNegation globalNegation (assignment 127)))
  let bounded129 := below_succ bounded128 (domain_from_eq (domain := Cases.C029.initial 128) (congrArg (Sign.withNegation globalNegation) hnode128) (Eq.refl Bool.true))
  let bounded130 := below_succ bounded129 (top_allows (Sign.withNegation globalNegation (assignment 129)))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C029.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C029.initial 131) (congrArg (Sign.withNegation globalNegation) hnode131) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C029.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C029.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C029.initial 134) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C029.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (top_allows (Sign.withNegation globalNegation (assignment 136)))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C029.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C029.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C029.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C029.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C029.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C029.initial 142) (congrArg (Sign.withNegation globalNegation) hnode142) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (top_allows (Sign.withNegation globalNegation (assignment 143)))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C029.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C029.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C029.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C029.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C029.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C029.initial 149) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C029.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C029.initial 151) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C029.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C029.initial 153) (congrArg (Sign.withNegation globalNegation) hnode153) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (domain_from_eq (domain := Cases.C029.initial 154) (congrArg (Sign.withNegation globalNegation) hnode154) (Eq.refl Bool.true))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C029.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C029.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C029.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C029.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (top_allows (Sign.withNegation globalNegation (assignment 159)))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C029.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (top_allows (Sign.withNegation globalNegation (assignment 161)))
  let bounded163 := below_succ bounded162 (top_allows (Sign.withNegation globalNegation (assignment 162)))
  let bounded164 := below_succ bounded163 (top_allows (Sign.withNegation globalNegation (assignment 163)))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C029.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C029.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C029.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C029.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (domain_from_eq (domain := Cases.C029.initial 168) (congrArg (Sign.withNegation globalNegation) hnode168) (Eq.refl Bool.true))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C029.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (top_allows (Sign.withNegation globalNegation (assignment 170)))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C029.initial 171) (congrArg (Sign.withNegation globalNegation) hnode171) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (top_allows (Sign.withNegation globalNegation (assignment 172)))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C029.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (top_allows (Sign.withNegation globalNegation (assignment 174)))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C029.initial 175) (congrArg (Sign.withNegation globalNegation) hnode175) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C029.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Cases.C029.initial 177) (congrArg (Sign.withNegation globalNegation) hnode177) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (top_allows (Sign.withNegation globalNegation (assignment 178)))
  let bounded180 := below_succ bounded179 (top_allows (Sign.withNegation globalNegation (assignment 179)))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C029.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C029.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C029.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C029.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Cases.C029.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C029.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (top_allows (Sign.withNegation globalNegation (assignment 186)))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C029.initial 187) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C029.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C029.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C029.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C029.initial 191) (congrArg (Sign.withNegation globalNegation) hnode191) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C029.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C029.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (top_allows (Sign.withNegation globalNegation (assignment 194)))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C029.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (top_allows (Sign.withNegation globalNegation (assignment 196)))
  let bounded198 := below_succ bounded197 (top_allows (Sign.withNegation globalNegation (assignment 197)))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Cases.C029.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (domain_from_eq (domain := Cases.C029.initial 199) (congrArg (Sign.withNegation globalNegation) hnode199) (Eq.refl Bool.true))
  let bounded201 := below_succ bounded200 (top_allows (Sign.withNegation globalNegation (assignment 200)))
  let bounded202 := below_succ bounded201 (top_allows (Sign.withNegation globalNegation (assignment 201)))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C029.initial 202) (congrArg (Sign.withNegation globalNegation) hnode202) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (domain_from_eq (domain := Cases.C029.initial 203) (congrArg (Sign.withNegation globalNegation) hnode203) (Eq.refl Bool.true))
  let bounded205 := below_succ bounded204 (domain_from_eq (domain := Cases.C029.initial 204) (congrArg (Sign.withNegation globalNegation) hnode204) (Eq.refl Bool.true))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C029.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Cases.C029.initial 206) (congrArg (Sign.withNegation globalNegation) (h_zero 10 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Cases.C029.initial 207) (congrArg (Sign.withNegation globalNegation) hnode207) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C029.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C029.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C029.initial 210) (congrArg (Sign.withNegation globalNegation) hnode210) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C029.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C029.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C029.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C029.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (domain_from_eq (domain := Cases.C029.initial 215) (congrArg (Sign.withNegation globalNegation) (h_zero 11 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C029.initial 216) (congrArg (Sign.withNegation globalNegation) (h_zero 12 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C029.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (top_allows (Sign.withNegation globalNegation (assignment 218)))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Cases.C029.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C029.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (top_allows (Sign.withNegation globalNegation (assignment 221)))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C029.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C029.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (top_allows (Sign.withNegation globalNegation (assignment 224)))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C029.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C029.initial 226) (congrArg (Sign.withNegation globalNegation) (h_zero 13 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C029.initial 227) (congrArg (Sign.withNegation globalNegation) (h_zero 14 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C029.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Cases.C029.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C029.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (top_allows (Sign.withNegation globalNegation (assignment 231)))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C029.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (domain_from_eq (domain := Cases.C029.initial 233) (congrArg (Sign.withNegation globalNegation) hnode233) (Eq.refl Bool.true))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C029.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C029.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (top_allows (Sign.withNegation globalNegation (assignment 236)))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C029.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C029.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Cases.C029.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (domain_from_eq (domain := Cases.C029.initial 240) (congrArg (Sign.withNegation globalNegation) hnode240) (Eq.refl Bool.true))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C029.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (top_allows (Sign.withNegation globalNegation (assignment 242)))
  let bounded244 := below_succ bounded243 (top_allows (Sign.withNegation globalNegation (assignment 243)))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C029.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C029.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C029.initial 246) (congrArg (Sign.withNegation globalNegation) hnode246) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (top_allows (Sign.withNegation globalNegation (assignment 247)))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C029.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (top_allows (Sign.withNegation globalNegation (assignment 249)))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Cases.C029.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C029.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C029.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C029
#print axioms Papers.RationalityTen.PureGP.Initializers.C029.support_sign_contradiction
