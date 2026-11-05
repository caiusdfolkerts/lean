module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C005

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C005
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 2
def globalNegation : Bool := Bool.false
def edgeTable : Table SupportEdge := (Table.node 120 (Table.node 60 (Table.node 30 (Table.node 15 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 2 3 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 2 4 Bool.false)) (Table.leaf (SupportEdge.mk 2 5 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 7 8 Bool.false)) (Table.leaf (SupportEdge.mk 7 9 Bool.false))) (Table.node 6 (Table.leaf (SupportEdge.mk 7 10 Bool.false)) (Table.leaf (SupportEdge.mk 11 12 Bool.false))))) (Table.node 11 (Table.node 9 (Table.node 8 (Table.leaf (SupportEdge.mk 11 13 Bool.false)) (Table.leaf (SupportEdge.mk 11 14 Bool.false))) (Table.node 10 (Table.leaf (SupportEdge.mk 22 23 Bool.false)) (Table.leaf (SupportEdge.mk 22 24 Bool.false)))) (Table.node 13 (Table.node 12 (Table.leaf (SupportEdge.mk 22 25 Bool.false)) (Table.leaf (SupportEdge.mk 26 27 Bool.false))) (Table.node 14 (Table.leaf (SupportEdge.mk 26 28 Bool.false)) (Table.leaf (SupportEdge.mk 26 29 Bool.false)))))) (Table.node 22 (Table.node 18 (Table.node 16 (Table.leaf (SupportEdge.mk 36 37 Bool.false)) (Table.node 17 (Table.leaf (SupportEdge.mk 36 38 Bool.false)) (Table.leaf (SupportEdge.mk 36 39 Bool.false)))) (Table.node 20 (Table.node 19 (Table.leaf (SupportEdge.mk 57 58 Bool.false)) (Table.leaf (SupportEdge.mk 57 59 Bool.false))) (Table.node 21 (Table.leaf (SupportEdge.mk 57 60 Bool.false)) (Table.leaf (SupportEdge.mk 61 62 Bool.false))))) (Table.node 26 (Table.node 24 (Table.node 23 (Table.leaf (SupportEdge.mk 61 63 Bool.false)) (Table.leaf (SupportEdge.mk 61 64 Bool.false))) (Table.node 25 (Table.leaf (SupportEdge.mk 71 72 Bool.false)) (Table.leaf (SupportEdge.mk 71 73 Bool.false)))) (Table.node 28 (Table.node 27 (Table.leaf (SupportEdge.mk 71 74 Bool.false)) (Table.leaf (SupportEdge.mk 91 92 Bool.false))) (Table.node 29 (Table.leaf (SupportEdge.mk 91 93 Bool.false)) (Table.leaf (SupportEdge.mk 91 94 Bool.false))))))) (Table.node 45 (Table.node 37 (Table.node 33 (Table.node 31 (Table.leaf (SupportEdge.mk 127 128 Bool.false)) (Table.node 32 (Table.leaf (SupportEdge.mk 127 129 Bool.false)) (Table.leaf (SupportEdge.mk 127 130 Bool.false)))) (Table.node 35 (Table.node 34 (Table.leaf (SupportEdge.mk 131 132 Bool.false)) (Table.leaf (SupportEdge.mk 131 133 Bool.false))) (Table.node 36 (Table.leaf (SupportEdge.mk 131 134 Bool.false)) (Table.leaf (SupportEdge.mk 141 142 Bool.false))))) (Table.node 41 (Table.node 39 (Table.node 38 (Table.leaf (SupportEdge.mk 141 143 Bool.false)) (Table.leaf (SupportEdge.mk 141 144 Bool.false))) (Table.node 40 (Table.leaf (SupportEdge.mk 161 162 Bool.false)) (Table.leaf (SupportEdge.mk 161 163 Bool.false)))) (Table.node 43 (Table.node 42 (Table.leaf (SupportEdge.mk 161 164 Bool.false)) (Table.leaf (SupportEdge.mk 196 197 Bool.false))) (Table.node 44 (Table.leaf (SupportEdge.mk 196 198 Bool.false)) (Table.leaf (SupportEdge.mk 196 199 Bool.false)))))) (Table.node 52 (Table.node 48 (Table.node 46 (Table.leaf (SupportEdge.mk 2 7 Bool.false)) (Table.node 47 (Table.leaf (SupportEdge.mk 2 11 Bool.false)) (Table.leaf (SupportEdge.mk 2 15 Bool.true)))) (Table.node 50 (Table.node 49 (Table.leaf (SupportEdge.mk 2 17 Bool.true)) (Table.leaf (SupportEdge.mk 4 9 Bool.false))) (Table.node 51 (Table.leaf (SupportEdge.mk 4 13 Bool.false)) (Table.leaf (SupportEdge.mk 4 18 Bool.false))))) (Table.node 56 (Table.node 54 (Table.node 53 (Table.leaf (SupportEdge.mk 4 20 Bool.true)) (Table.leaf (SupportEdge.mk 31 41 Bool.false))) (Table.node 55 (Table.leaf (SupportEdge.mk 31 47 Bool.false)) (Table.leaf (SupportEdge.mk 31 52 Bool.true)))) (Table.node 58 (Table.node 57 (Table.leaf (SupportEdge.mk 31 54 Bool.false)) (Table.leaf (SupportEdge.mk 66 76 Bool.false))) (Table.node 59 (Table.leaf (SupportEdge.mk 66 82 Bool.false)) (Table.leaf (SupportEdge.mk 66 87 Bool.true)))))))) (Table.node 90 (Table.node 75 (Table.node 67 (Table.node 63 (Table.node 61 (Table.leaf (SupportEdge.mk 66 89 Bool.false)) (Table.node 62 (Table.leaf (SupportEdge.mk 136 146 Bool.false)) (Table.leaf (SupportEdge.mk 136 152 Bool.false)))) (Table.node 65 (Table.node 64 (Table.leaf (SupportEdge.mk 136 157 Bool.true)) (Table.leaf (SupportEdge.mk 136 159 Bool.false))) (Table.node 66 (Table.leaf (SupportEdge.mk 2 22 Bool.true)) (Table.leaf (SupportEdge.mk 2 26 Bool.true))))) (Table.node 71 (Table.node 69 (Table.node 68 (Table.leaf (SupportEdge.mk 2 31 Bool.false)) (Table.leaf (SupportEdge.mk 2 32 Bool.false))) (Table.node 70 (Table.leaf (SupportEdge.mk 3 23 Bool.true)) (Table.leaf (SupportEdge.mk 3 27 Bool.true)))) (Table.node 73 (Table.node 72 (Table.leaf (SupportEdge.mk 3 33 Bool.false)) (Table.leaf (SupportEdge.mk 3 34 Bool.false))) (Table.node 74 (Table.leaf (SupportEdge.mk 15 40 Bool.false)) (Table.leaf (SupportEdge.mk 15 46 Bool.false)))))) (Table.node 82 (Table.node 78 (Table.node 76 (Table.leaf (SupportEdge.mk 15 52 Bool.false)) (Table.node 77 (Table.leaf (SupportEdge.mk 15 53 Bool.false)) (Table.leaf (SupportEdge.mk 65 95 Bool.true)))) (Table.node 80 (Table.node 79 (Table.leaf (SupportEdge.mk 65 101 Bool.true)) (Table.leaf (SupportEdge.mk 65 107 Bool.true))) (Table.node 81 (Table.leaf (SupportEdge.mk 65 108 Bool.true)) (Table.leaf (SupportEdge.mk 135 165 Bool.true))))) (Table.node 86 (Table.node 84 (Table.node 83 (Table.leaf (SupportEdge.mk 135 171 Bool.true)) (Table.leaf (SupportEdge.mk 135 177 Bool.true))) (Table.node 85 (Table.leaf (SupportEdge.mk 135 178 Bool.true)) (Table.leaf (SupportEdge.mk 3 58 Bool.false)))) (Table.node 88 (Table.node 87 (Table.leaf (SupportEdge.mk 3 62 Bool.false)) (Table.leaf (SupportEdge.mk 3 65 Bool.false))) (Table.node 89 (Table.leaf (SupportEdge.mk 3 69 Bool.true)) (Table.leaf (SupportEdge.mk 4 59 Bool.false))))))) (Table.node 105 (Table.node 97 (Table.node 93 (Table.node 91 (Table.leaf (SupportEdge.mk 4 63 Bool.false)) (Table.node 92 (Table.leaf (SupportEdge.mk 4 66 Bool.false)) (Table.leaf (SupportEdge.mk 4 70 Bool.true)))) (Table.node 95 (Table.node 94 (Table.leaf (SupportEdge.mk 18 78 Bool.true)) (Table.leaf (SupportEdge.mk 18 84 Bool.true))) (Table.node 96 (Table.leaf (SupportEdge.mk 18 87 Bool.true)) (Table.leaf (SupportEdge.mk 18 90 Bool.true))))) (Table.node 101 (Table.node 99 (Table.node 98 (Table.leaf (SupportEdge.mk 33 98 Bool.true)) (Table.leaf (SupportEdge.mk 33 104 Bool.true))) (Table.node 100 (Table.leaf (SupportEdge.mk 33 107 Bool.true)) (Table.leaf (SupportEdge.mk 33 110 Bool.true)))) (Table.node 103 (Table.node 102 (Table.leaf (SupportEdge.mk 138 203 Bool.false)) (Table.leaf (SupportEdge.mk 138 209 Bool.false))) (Table.node 104 (Table.leaf (SupportEdge.mk 138 212 Bool.false)) (Table.leaf (SupportEdge.mk 138 215 Bool.false)))))) (Table.node 112 (Table.node 108 (Table.node 106 (Table.leaf (SupportEdge.mk 52 87 Bool.false)) (Table.node 107 (Table.leaf (SupportEdge.mk 52 107 Bool.false)) (Table.leaf (SupportEdge.mk 52 117 Bool.false)))) (Table.node 110 (Table.node 109 (Table.leaf (SupportEdge.mk 52 121 Bool.false)) (Table.leaf (SupportEdge.mk 53 88 Bool.false))) (Table.node 111 (Table.leaf (SupportEdge.mk 53 108 Bool.false)) (Table.leaf (SupportEdge.mk 53 118 Bool.false))))) (Table.node 116 (Table.node 114 (Table.node 113 (Table.leaf (SupportEdge.mk 53 122 Bool.false)) (Table.leaf (SupportEdge.mk 54 89 Bool.false))) (Table.node 115 (Table.leaf (SupportEdge.mk 54 109 Bool.false)) (Table.leaf (SupportEdge.mk 54 119 Bool.false)))) (Table.node 118 (Table.node 117 (Table.leaf (SupportEdge.mk 54 123 Bool.false)) (Table.leaf (SupportEdge.mk 55 90 Bool.false))) (Table.node 119 (Table.leaf (SupportEdge.mk 55 110 Bool.false)) (Table.leaf (SupportEdge.mk 55 120 Bool.false))))))))) (Table.node 180 (Table.node 150 (Table.node 135 (Table.node 127 (Table.node 123 (Table.node 121 (Table.leaf (SupportEdge.mk 55 124 Bool.false)) (Table.node 122 (Table.leaf (SupportEdge.mk 195 230 Bool.false)) (Table.leaf (SupportEdge.mk 195 245 Bool.false)))) (Table.node 125 (Table.node 124 (Table.leaf (SupportEdge.mk 195 250 Bool.false)) (Table.leaf (SupportEdge.mk 195 251 Bool.false))) (Table.node 126 (Table.leaf (SupportEdge.mk 9 129 Bool.false)) (Table.leaf (SupportEdge.mk 9 143 Bool.true))))) (Table.node 131 (Table.node 129 (Table.node 128 (Table.leaf (SupportEdge.mk 9 146 Bool.true)) (Table.leaf (SupportEdge.mk 9 148 Bool.true))) (Table.node 130 (Table.leaf (SupportEdge.mk 9 150 Bool.false)) (Table.leaf (SupportEdge.mk 21 126 Bool.true)))) (Table.node 133 (Table.node 132 (Table.leaf (SupportEdge.mk 21 162 Bool.false)) (Table.leaf (SupportEdge.mk 21 163 Bool.false))) (Table.node 134 (Table.leaf (SupportEdge.mk 21 164 Bool.false)) (Table.leaf (SupportEdge.mk 22 127 Bool.true)))))) (Table.node 142 (Table.node 138 (Table.node 136 (Table.leaf (SupportEdge.mk 22 165 Bool.false)) (Table.node 137 (Table.leaf (SupportEdge.mk 22 166 Bool.false)) (Table.leaf (SupportEdge.mk 22 167 Bool.false)))) (Table.node 140 (Table.node 139 (Table.leaf (SupportEdge.mk 26 131 Bool.true)) (Table.leaf (SupportEdge.mk 26 171 Bool.false))) (Table.node 141 (Table.leaf (SupportEdge.mk 26 172 Bool.false)) (Table.leaf (SupportEdge.mk 26 173 Bool.false))))) (Table.node 146 (Table.node 144 (Table.node 143 (Table.leaf (SupportEdge.mk 36 141 Bool.true)) (Table.leaf (SupportEdge.mk 36 181 Bool.false))) (Table.node 145 (Table.leaf (SupportEdge.mk 36 182 Bool.false)) (Table.leaf (SupportEdge.mk 36 183 Bool.false)))) (Table.node 148 (Table.node 147 (Table.leaf (SupportEdge.mk 91 196 Bool.false)) (Table.leaf (SupportEdge.mk 91 231 Bool.false))) (Table.node 149 (Table.leaf (SupportEdge.mk 91 232 Bool.false)) (Table.leaf (SupportEdge.mk 91 233 Bool.false))))))) (Table.node 165 (Table.node 157 (Table.node 153 (Table.node 151 (Table.leaf (SupportEdge.mk 41 146 Bool.true)) (Table.node 152 (Table.leaf (SupportEdge.mk 41 166 Bool.true)) (Table.leaf (SupportEdge.mk 41 182 Bool.false)))) (Table.node 155 (Table.node 154 (Table.leaf (SupportEdge.mk 41 187 Bool.true)) (Table.leaf (SupportEdge.mk 42 147 Bool.true))) (Table.node 156 (Table.leaf (SupportEdge.mk 42 167 Bool.true)) (Table.leaf (SupportEdge.mk 42 183 Bool.false))))) (Table.node 161 (Table.node 159 (Table.node 158 (Table.leaf (SupportEdge.mk 42 188 Bool.true)) (Table.leaf (SupportEdge.mk 45 150 Bool.true))) (Table.node 160 (Table.leaf (SupportEdge.mk 45 170 Bool.true)) (Table.leaf (SupportEdge.mk 45 186 Bool.false)))) (Table.node 163 (Table.node 162 (Table.leaf (SupportEdge.mk 45 190 Bool.false)) (Table.leaf (SupportEdge.mk 54 159 Bool.true))) (Table.node 164 (Table.leaf (SupportEdge.mk 54 179 Bool.true)) (Table.leaf (SupportEdge.mk 54 193 Bool.true)))))) (Table.node 172 (Table.node 168 (Table.node 166 (Table.leaf (SupportEdge.mk 54 195 Bool.false)) (Table.node 167 (Table.leaf (SupportEdge.mk 119 224 Bool.false)) (Table.leaf (SupportEdge.mk 119 239 Bool.false)))) (Table.node 170 (Table.node 169 (Table.leaf (SupportEdge.mk 119 248 Bool.true)) (Table.leaf (SupportEdge.mk 119 250 Bool.false))) (Table.node 171 (Table.leaf (SupportEdge.mk 62 132 Bool.false)) (Table.leaf (SupportEdge.mk 62 197 Bool.false))))) (Table.node 176 (Table.node 174 (Table.node 173 (Table.leaf (SupportEdge.mk 62 206 Bool.true)) (Table.leaf (SupportEdge.mk 62 209 Bool.false))) (Table.node 175 (Table.leaf (SupportEdge.mk 64 134 Bool.false)) (Table.leaf (SupportEdge.mk 64 199 Bool.false)))) (Table.node 178 (Table.node 177 (Table.leaf (SupportEdge.mk 64 208 Bool.true)) (Table.leaf (SupportEdge.mk 64 211 Bool.true))) (Table.node 179 (Table.leaf (SupportEdge.mk 69 139 Bool.false)) (Table.leaf (SupportEdge.mk 69 204 Bool.false)))))))) (Table.node 210 (Table.node 195 (Table.node 187 (Table.node 183 (Table.node 181 (Table.leaf (SupportEdge.mk 69 213 Bool.false)) (Table.node 182 (Table.leaf (SupportEdge.mk 69 215 Bool.true)) (Table.leaf (SupportEdge.mk 85 155 Bool.false)))) (Table.node 185 (Table.node 184 (Table.leaf (SupportEdge.mk 85 220 Bool.true)) (Table.leaf (SupportEdge.mk 85 227 Bool.false))) (Table.node 186 (Table.leaf (SupportEdge.mk 85 229 Bool.true)) (Table.leaf (SupportEdge.mk 105 175 Bool.false))))) (Table.node 191 (Table.node 189 (Table.node 188 (Table.leaf (SupportEdge.mk 105 235 Bool.true)) (Table.leaf (SupportEdge.mk 105 242 Bool.false))) (Table.node 190 (Table.leaf (SupportEdge.mk 105 244 Bool.true)) (Table.leaf (SupportEdge.mk 73 143 Bool.false)))) (Table.node 193 (Table.node 192 (Table.leaf (SupportEdge.mk 73 198 Bool.true)) (Table.leaf (SupportEdge.mk 73 217 Bool.true))) (Table.node 194 (Table.leaf (SupportEdge.mk 73 219 Bool.true)) (Table.leaf (SupportEdge.mk 74 144 Bool.false)))))) (Table.node 202 (Table.node 198 (Table.node 196 (Table.leaf (SupportEdge.mk 74 199 Bool.true)) (Table.node 197 (Table.leaf (SupportEdge.mk 74 218 Bool.true)) (Table.leaf (SupportEdge.mk 74 220 Bool.true)))) (Table.node 200 (Table.node 199 (Table.leaf (SupportEdge.mk 80 150 Bool.false)) (Table.leaf (SupportEdge.mk 80 205 Bool.true))) (Table.node 201 (Table.leaf (SupportEdge.mk 80 224 Bool.false)) (Table.leaf (SupportEdge.mk 80 225 Bool.false))))) (Table.node 206 (Table.node 204 (Table.node 203 (Table.leaf (SupportEdge.mk 86 156 Bool.false)) (Table.leaf (SupportEdge.mk 86 211 Bool.true))) (Table.node 205 (Table.leaf (SupportEdge.mk 86 228 Bool.false)) (Table.leaf (SupportEdge.mk 86 229 Bool.false)))) (Table.node 208 (Table.node 207 (Table.leaf (SupportEdge.mk 116 186 Bool.false)) (Table.leaf (SupportEdge.mk 116 236 Bool.false))) (Table.node 209 (Table.leaf (SupportEdge.mk 116 248 Bool.false)) (Table.leaf (SupportEdge.mk 116 249 Bool.false))))))) (Table.node 225 (Table.node 217 (Table.node 213 (Table.node 211 (Table.leaf (SupportEdge.mk 90 160 Bool.false)) (Table.node 212 (Table.leaf (SupportEdge.mk 90 215 Bool.true)) (Table.leaf (SupportEdge.mk 90 225 Bool.true)))) (Table.node 215 (Table.node 214 (Table.leaf (SupportEdge.mk 90 229 Bool.true)) (Table.leaf (SupportEdge.mk 90 230 Bool.true))) (Table.node 216 (Table.leaf (SupportEdge.mk 101 171 Bool.false)) (Table.leaf (SupportEdge.mk 101 206 Bool.false))))) (Table.node 221 (Table.node 219 (Table.node 218 (Table.leaf (SupportEdge.mk 101 231 Bool.true)) (Table.leaf (SupportEdge.mk 101 241 Bool.false))) (Table.node 220 (Table.leaf (SupportEdge.mk 101 242 Bool.false)) (Table.leaf (SupportEdge.mk 111 181 Bool.false)))) (Table.node 223 (Table.node 222 (Table.leaf (SupportEdge.mk 111 216 Bool.false)) (Table.leaf (SupportEdge.mk 111 231 Bool.false))) (Table.node 224 (Table.leaf (SupportEdge.mk 111 246 Bool.false)) (Table.leaf (SupportEdge.mk 113 183 Bool.false)))))) (Table.node 232 (Table.node 228 (Table.node 226 (Table.leaf (SupportEdge.mk 113 218 Bool.false)) (Table.node 227 (Table.leaf (SupportEdge.mk 113 233 Bool.false)) (Table.leaf (SupportEdge.mk 113 248 Bool.true)))) (Table.node 230 (Table.node 229 (Table.leaf (SupportEdge.mk 115 185 Bool.false)) (Table.leaf (SupportEdge.mk 115 220 Bool.false))) (Table.node 231 (Table.leaf (SupportEdge.mk 115 235 Bool.false)) (Table.leaf (SupportEdge.mk 115 249 Bool.true))))) (Table.node 236 (Table.node 234 (Table.node 233 (Table.leaf (SupportEdge.mk 118 188 Bool.false)) (Table.leaf (SupportEdge.mk 118 223 Bool.false))) (Table.node 235 (Table.leaf (SupportEdge.mk 118 238 Bool.false)) (Table.leaf (SupportEdge.mk 118 250 Bool.true)))) (Table.node 238 (Table.node 237 (Table.leaf (SupportEdge.mk 122 192 Bool.false)) (Table.leaf (SupportEdge.mk 122 227 Bool.false))) (Table.node 239 (Table.leaf (SupportEdge.mk 122 242 Bool.false)) (Table.leaf (SupportEdge.mk 122 251 Bool.true))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 9 (Table.node 4 (Table.node 2 (Table.node 1 (Table.leaf 0) (Table.leaf 1)) (Table.node 3 (Table.leaf 6) (Table.leaf 16))) (Table.node 6 (Table.node 5 (Table.leaf 21) (Table.leaf 30)) (Table.node 7 (Table.leaf 56) (Table.node 8 (Table.leaf 68) (Table.leaf 125))))) (Table.node 13 (Table.node 11 (Table.node 10 (Table.leaf 126) (Table.leaf 161)) (Table.node 12 (Table.leaf 162) (Table.leaf 163))) (Table.node 15 (Table.node 14 (Table.leaf 164) (Table.leaf 189)) (Table.node 16 (Table.leaf 210) (Table.node 17 (Table.leaf 221) (Table.leaf 247))))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 240 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 18 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C005.initial index).allows
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
  let hnode17 : Eq (assignment 17) Sign.negative :=
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
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode10 : Eq (assignment 10) Sign.positive :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode7)
  let hnode12 : Eq (assignment 12) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode13 : Eq (assignment 13) Sign.positive :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode14 : Eq (assignment 14) Sign.positive :=
    Eq.trans (h_support 8 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode18 : Eq (assignment 18) Sign.positive :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode20 : Eq (assignment 20) Sign.negative :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
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
  let hnode41 : Eq (assignment 41) Sign.positive :=
    Eq.trans (h_support 53 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode46 : Eq (assignment 46) Sign.negative :=
    Eq.trans (h_support 74 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode47 : Eq (assignment 47) Sign.positive :=
    Eq.trans (h_support 54 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode52 : Eq (assignment 52) Sign.negative :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode53 : Eq (assignment 53) Sign.negative :=
    Eq.trans (h_support 76 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode54 : Eq (assignment 54) Sign.positive :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode58 : Eq (assignment 58) Sign.positive :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode59 : Eq (assignment 59) Sign.positive :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode62 : Eq (assignment 62) Sign.positive :=
    Eq.trans (h_support 86 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode63 : Eq (assignment 63) Sign.positive :=
    Eq.trans (h_support 90 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode65 : Eq (assignment 65) Sign.positive :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode66 : Eq (assignment 66) Sign.positive :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode69 : Eq (assignment 69) Sign.negative :=
    Eq.trans (h_support 88 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode70 : Eq (assignment 70) Sign.negative :=
    Eq.trans (h_support 92 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode127 : Eq (assignment 127) Sign.positive :=
    Eq.trans (h_support 134 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode131 : Eq (assignment 131) Sign.positive :=
    Eq.trans (h_support 138 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode165 : Eq (assignment 165) Sign.negative :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode166 : Eq (assignment 166) Sign.negative :=
    Eq.trans (h_support 136 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode167 : Eq (assignment 167) Sign.negative :=
    Eq.trans (h_support 137 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode171 : Eq (assignment 171) Sign.negative :=
    Eq.trans (h_support 139 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode172 : Eq (assignment 172) Sign.negative :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode173 : Eq (assignment 173) Sign.negative :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode42 : Eq (assignment 42) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 155 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode167)
  let hnode57 : Eq (assignment 57) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 18 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode61 : Eq (assignment 61) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 21 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode62)
  let hnode76 : Eq (assignment 76) Sign.positive :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode78 : Eq (assignment 78) Sign.negative :=
    Eq.trans (h_support 93 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode82 : Eq (assignment 82) Sign.positive :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode84 : Eq (assignment 84) Sign.negative :=
    Eq.trans (h_support 94 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode87 : Eq (assignment 87) Sign.negative :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode88 : Eq (assignment 88) Sign.negative :=
    Eq.trans (h_support 109 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode89 : Eq (assignment 89) Sign.positive :=
    Eq.trans (h_support 60 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode90 : Eq (assignment 90) Sign.negative :=
    Eq.trans (h_support 96 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode95 : Eq (assignment 95) Sign.negative :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode65)
  let hnode98 : Eq (assignment 98) Sign.negative :=
    Eq.trans (h_support 97 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode101 : Eq (assignment 101) Sign.negative :=
    Eq.trans (h_support 78 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode65)
  let hnode104 : Eq (assignment 104) Sign.negative :=
    Eq.trans (h_support 98 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode107 : Eq (assignment 107) Sign.negative :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode108 : Eq (assignment 108) Sign.negative :=
    Eq.trans (h_support 80 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode65)
  let hnode109 : Eq (assignment 109) Sign.positive :=
    Eq.trans (h_support 114 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode110 : Eq (assignment 110) Sign.negative :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode117 : Eq (assignment 117) Sign.negative :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode52)
  let hnode118 : Eq (assignment 118) Sign.negative :=
    Eq.trans (h_support 111 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode119 : Eq (assignment 119) Sign.positive :=
    Eq.trans (h_support 115 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode121 : Eq (assignment 121) Sign.negative :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode52)
  let hnode122 : Eq (assignment 122) Sign.negative :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode123 : Eq (assignment 123) Sign.positive :=
    Eq.trans (h_support 116 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode128 : Eq (assignment 128) Sign.positive :=
    Eq.trans (h_support 30 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode127)
  let hnode129 : Eq (assignment 129) Sign.positive :=
    Eq.trans (h_support 125 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode130 : Eq (assignment 130) Sign.positive :=
    Eq.trans (h_support 32 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode127)
  let hnode132 : Eq (assignment 132) Sign.positive :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode62)
  let hnode133 : Eq (assignment 133) Sign.positive :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode131)
  let hnode134 : Eq (assignment 134) Sign.positive :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode131)
  let hnode135 : Eq (assignment 135) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 81 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode165)
  let hnode139 : Eq (assignment 139) Sign.negative :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode143 : Eq (assignment 143) Sign.negative :=
    Eq.trans (h_support 126 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode146 : Eq (assignment 146) Sign.negative :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode148 : Eq (assignment 148) Sign.negative :=
    Eq.trans (h_support 128 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode150 : Eq (assignment 150) Sign.positive :=
    Eq.trans (h_support 129 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode159 : Eq (assignment 159) Sign.negative :=
    Eq.trans (h_support 162 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 163 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode182 : Eq (assignment 182) Sign.positive :=
    Eq.trans (h_support 152 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode187 : Eq (assignment 187) Sign.negative :=
    Eq.trans (h_support 153 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode193 : Eq (assignment 193) Sign.negative :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode195 : Eq (assignment 195) Sign.positive :=
    Eq.trans (h_support 165 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode197 : Eq (assignment 197) Sign.positive :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode62)
  let hnode204 : Eq (assignment 204) Sign.negative :=
    Eq.trans (h_support 179 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode206 : Eq (assignment 206) Sign.negative :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode62)
  let hnode209 : Eq (assignment 209) Sign.positive :=
    Eq.trans (h_support 173 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode62)
  let hnode213 : Eq (assignment 213) Sign.negative :=
    Eq.trans (h_support 180 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode215 : Eq (assignment 215) Sign.positive :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode69)
  let hnode36 : Eq (assignment 36) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 144 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode182)
  let hnode45 : Eq (assignment 45) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 158 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode150)
  let hnode55 : Eq (assignment 55) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 118 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode110)
  let hnode60 : Eq (assignment 60) Sign.positive :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode57)
  let hnode64 : Eq (assignment 64) Sign.positive :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode61)
  let hnode73 : Eq (assignment 73) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 190 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode143)
  let hnode80 : Eq (assignment 80) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 198 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode150)
  let hnode136 : Eq (assignment 136) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 61 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode146)
  let hnode138 : Eq (assignment 138) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 102 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode209)
  let hnode141 : Eq (assignment 141) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 37 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode143)
  let hnode147 : Eq (assignment 147) Sign.negative :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode42)
  let hnode160 : Eq (assignment 160) Sign.negative :=
    Eq.trans (h_support 210 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode90)
  let hnode177 : Eq (assignment 177) Sign.negative :=
    Eq.trans (h_support 83 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode135)
  let hnode178 : Eq (assignment 178) Sign.negative :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode135)
  let hnode183 : Eq (assignment 183) Sign.positive :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode42)
  let hnode188 : Eq (assignment 188) Sign.negative :=
    Eq.trans (h_support 232 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode118)
  let hnode192 : Eq (assignment 192) Sign.negative :=
    Eq.trans (h_support 236 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode122)
  let hnode196 : Eq (assignment 196) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 42 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode197)
  let hnode223 : Eq (assignment 223) Sign.negative :=
    Eq.trans (h_support 233 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode118)
  let hnode224 : Eq (assignment 224) Sign.positive :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode119)
  let hnode225 : Eq (assignment 225) Sign.positive :=
    Eq.trans (h_support 212 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode90)
  let hnode227 : Eq (assignment 227) Sign.negative :=
    Eq.trans (h_support 237 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode122)
  let hnode229 : Eq (assignment 229) Sign.positive :=
    Eq.trans (h_support 213 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode90)
  let hnode230 : Eq (assignment 230) Sign.positive :=
    Eq.trans (h_support 214 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode90)
  let hnode231 : Eq (assignment 231) Sign.positive :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode101)
  let hnode238 : Eq (assignment 238) Sign.negative :=
    Eq.trans (h_support 234 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode118)
  let hnode239 : Eq (assignment 239) Sign.positive :=
    Eq.trans (h_support 167 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode119)
  let hnode241 : Eq (assignment 241) Sign.negative :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode101)
  let hnode242 : Eq (assignment 242) Sign.negative :=
    Eq.trans (h_support 219 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode101)
  let hnode245 : Eq (assignment 245) Sign.positive :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode195)
  let hnode248 : Eq (assignment 248) Sign.negative :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode119)
  let hnode250 : Eq (assignment 250) Sign.positive :=
    Eq.trans (h_support 235 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode118)
  let hnode251 : Eq (assignment 251) Sign.positive :=
    Eq.trans (h_support 239 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode122)
  let hnode37 : Eq (assignment 37) Sign.positive :=
    Eq.trans (h_support 15 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode38 : Eq (assignment 38) Sign.positive :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode39 : Eq (assignment 39) Sign.positive :=
    Eq.trans (h_support 17 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode71 : Eq (assignment 71) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 25 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode73)
  let hnode85 : Eq (assignment 85) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 185 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode229)
  let hnode86 : Eq (assignment 86) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 205 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode229)
  let hnode91 : Eq (assignment 91) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 146 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode196)
  let hnode105 : Eq (assignment 105) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 188 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode242)
  let hnode111 : Eq (assignment 111) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 222 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode231)
  let hnode113 : Eq (assignment 113) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 224 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode183)
  let hnode116 : Eq (assignment 116) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 208 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode248)
  let hnode120 : Eq (assignment 120) Sign.negative :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode124 : Eq (assignment 124) Sign.negative :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode142 : Eq (assignment 142) Sign.negative :=
    Eq.trans (h_support 36 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode141)
  let hnode144 : Eq (assignment 144) Sign.negative :=
    Eq.trans (h_support 38 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode141)
  let hnode152 : Eq (assignment 152) Sign.negative :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode136)
  let hnode157 : Eq (assignment 157) Sign.positive :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode136)
  let hnode170 : Eq (assignment 170) Sign.positive :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode181 : Eq (assignment 181) Sign.positive :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode186 : Eq (assignment 186) Sign.negative :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode190 : Eq (assignment 190) Sign.negative :=
    Eq.trans (h_support 161 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode198 : Eq (assignment 198) Sign.positive :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode196)
  let hnode199 : Eq (assignment 199) Sign.positive :=
    Eq.trans (h_support 175 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode64)
  let hnode203 : Eq (assignment 203) Sign.positive :=
    Eq.trans (h_support 101 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode138)
  let hnode205 : Eq (assignment 205) Sign.negative :=
    Eq.trans (h_support 199 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode80)
  let hnode208 : Eq (assignment 208) Sign.negative :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode64)
  let hnode211 : Eq (assignment 211) Sign.negative :=
    Eq.trans (h_support 177 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode64)
  let hnode212 : Eq (assignment 212) Sign.positive :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode138)
  let hnode217 : Eq (assignment 217) Sign.positive :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode73)
  let hnode219 : Eq (assignment 219) Sign.positive :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode73)
  let hnode72 : Eq (assignment 72) Sign.negative :=
    Eq.trans (h_support 24 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode74 : Eq (assignment 74) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 195 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode199)
  let hnode92 : Eq (assignment 92) Sign.positive :=
    Eq.trans (h_support 27 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode93 : Eq (assignment 93) Sign.positive :=
    Eq.trans (h_support 28 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode94 : Eq (assignment 94) Sign.positive :=
    Eq.trans (h_support 29 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode155 : Eq (assignment 155) Sign.negative :=
    Eq.trans (h_support 182 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode85)
  let hnode156 : Eq (assignment 156) Sign.positive :=
    Eq.trans (h_support 202 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode86)
  let hnode175 : Eq (assignment 175) Sign.negative :=
    Eq.trans (h_support 186 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode105)
  let hnode216 : Eq (assignment 216) Sign.positive :=
    Eq.trans (h_support 221 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode218 : Eq (assignment 218) Sign.positive :=
    Eq.trans (h_support 225 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode113)
  let hnode220 : Eq (assignment 220) Sign.positive :=
    Eq.trans (h_support 183 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode85)
  let hnode228 : Eq (assignment 228) Sign.positive :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode86)
  let hnode232 : Eq (assignment 232) Sign.positive :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode233 : Eq (assignment 233) Sign.positive :=
    Eq.trans (h_support 149 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode235 : Eq (assignment 235) Sign.positive :=
    Eq.trans (h_support 187 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode105)
  let hnode236 : Eq (assignment 236) Sign.negative :=
    Eq.trans (h_support 207 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode116)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode105)
  let hnode246 : Eq (assignment 246) Sign.positive :=
    Eq.trans (h_support 223 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode111)
  let hnode249 : Eq (assignment 249) Sign.negative :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode116)
  let hnode115 : Eq (assignment 115) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 230 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode235)
  let hnode185 : Eq (assignment 185) Sign.positive :=
    Eq.trans (h_support 228 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode115)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C005.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (domain_from_eq (domain := Cases.C005.initial 0) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded2 := below_succ bounded1 (domain_from_eq (domain := Cases.C005.initial 1) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded3 := below_succ bounded2 (domain_from_eq (domain := Cases.C005.initial 2) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded4 := below_succ bounded3 (domain_from_eq (domain := Cases.C005.initial 3) (congrArg (Sign.withNegation globalNegation) hnode3) (Eq.refl Bool.true))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C005.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Cases.C005.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Cases.C005.initial 6) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Cases.C005.initial 7) (congrArg (Sign.withNegation globalNegation) hnode7) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C005.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Cases.C005.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C005.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (domain_from_eq (domain := Cases.C005.initial 11) (congrArg (Sign.withNegation globalNegation) hnode11) (Eq.refl Bool.true))
  let bounded13 := below_succ bounded12 (domain_from_eq (domain := Cases.C005.initial 12) (congrArg (Sign.withNegation globalNegation) hnode12) (Eq.refl Bool.true))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C005.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C005.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Cases.C005.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Cases.C005.initial 16) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C005.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (domain_from_eq (domain := Cases.C005.initial 18) (congrArg (Sign.withNegation globalNegation) hnode18) (Eq.refl Bool.true))
  let bounded20 := below_succ bounded19 (top_allows (Sign.withNegation globalNegation (assignment 19)))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Cases.C005.initial 20) (congrArg (Sign.withNegation globalNegation) hnode20) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C005.initial 21) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (domain_from_eq (domain := Cases.C005.initial 22) (congrArg (Sign.withNegation globalNegation) hnode22) (Eq.refl Bool.true))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C005.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C005.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C005.initial 25) (congrArg (Sign.withNegation globalNegation) hnode25) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Cases.C005.initial 26) (congrArg (Sign.withNegation globalNegation) hnode26) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C005.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C005.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C005.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (domain_from_eq (domain := Cases.C005.initial 30) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded32 := below_succ bounded31 (domain_from_eq (domain := Cases.C005.initial 31) (congrArg (Sign.withNegation globalNegation) hnode31) (Eq.refl Bool.true))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C005.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C005.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C005.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (top_allows (Sign.withNegation globalNegation (assignment 35)))
  let bounded37 := below_succ bounded36 (domain_from_eq (domain := Cases.C005.initial 36) (congrArg (Sign.withNegation globalNegation) hnode36) (Eq.refl Bool.true))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C005.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C005.initial 38) (congrArg (Sign.withNegation globalNegation) hnode38) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (domain_from_eq (domain := Cases.C005.initial 39) (congrArg (Sign.withNegation globalNegation) hnode39) (Eq.refl Bool.true))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Cases.C005.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C005.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C005.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (top_allows (Sign.withNegation globalNegation (assignment 43)))
  let bounded45 := below_succ bounded44 (top_allows (Sign.withNegation globalNegation (assignment 44)))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C005.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (domain_from_eq (domain := Cases.C005.initial 46) (congrArg (Sign.withNegation globalNegation) hnode46) (Eq.refl Bool.true))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C005.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (top_allows (Sign.withNegation globalNegation (assignment 48)))
  let bounded50 := below_succ bounded49 (top_allows (Sign.withNegation globalNegation (assignment 49)))
  let bounded51 := below_succ bounded50 (top_allows (Sign.withNegation globalNegation (assignment 50)))
  let bounded52 := below_succ bounded51 (top_allows (Sign.withNegation globalNegation (assignment 51)))
  let bounded53 := below_succ bounded52 (domain_from_eq (domain := Cases.C005.initial 52) (congrArg (Sign.withNegation globalNegation) hnode52) (Eq.refl Bool.true))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Cases.C005.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Cases.C005.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (domain_from_eq (domain := Cases.C005.initial 55) (congrArg (Sign.withNegation globalNegation) hnode55) (Eq.refl Bool.true))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C005.initial 56) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C005.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C005.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C005.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C005.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Cases.C005.initial 61) (congrArg (Sign.withNegation globalNegation) hnode61) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C005.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C005.initial 63) (congrArg (Sign.withNegation globalNegation) hnode63) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C005.initial 64) (congrArg (Sign.withNegation globalNegation) hnode64) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (domain_from_eq (domain := Cases.C005.initial 65) (congrArg (Sign.withNegation globalNegation) hnode65) (Eq.refl Bool.true))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C005.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (top_allows (Sign.withNegation globalNegation (assignment 67)))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C005.initial 68) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C005.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C005.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C005.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C005.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C005.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C005.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (top_allows (Sign.withNegation globalNegation (assignment 75)))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Cases.C005.initial 76) (congrArg (Sign.withNegation globalNegation) hnode76) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (top_allows (Sign.withNegation globalNegation (assignment 77)))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C005.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (top_allows (Sign.withNegation globalNegation (assignment 79)))
  let bounded81 := below_succ bounded80 (domain_from_eq (domain := Cases.C005.initial 80) (congrArg (Sign.withNegation globalNegation) hnode80) (Eq.refl Bool.true))
  let bounded82 := below_succ bounded81 (top_allows (Sign.withNegation globalNegation (assignment 81)))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Cases.C005.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (top_allows (Sign.withNegation globalNegation (assignment 83)))
  let bounded85 := below_succ bounded84 (domain_from_eq (domain := Cases.C005.initial 84) (congrArg (Sign.withNegation globalNegation) hnode84) (Eq.refl Bool.true))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C005.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C005.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C005.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Cases.C005.initial 88) (congrArg (Sign.withNegation globalNegation) hnode88) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (domain_from_eq (domain := Cases.C005.initial 89) (congrArg (Sign.withNegation globalNegation) hnode89) (Eq.refl Bool.true))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C005.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C005.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C005.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C005.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C005.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C005.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (top_allows (Sign.withNegation globalNegation (assignment 96)))
  let bounded98 := below_succ bounded97 (top_allows (Sign.withNegation globalNegation (assignment 97)))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C005.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (top_allows (Sign.withNegation globalNegation (assignment 99)))
  let bounded101 := below_succ bounded100 (top_allows (Sign.withNegation globalNegation (assignment 100)))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C005.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (top_allows (Sign.withNegation globalNegation (assignment 102)))
  let bounded104 := below_succ bounded103 (top_allows (Sign.withNegation globalNegation (assignment 103)))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C005.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C005.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (top_allows (Sign.withNegation globalNegation (assignment 106)))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C005.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C005.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C005.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C005.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C005.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (top_allows (Sign.withNegation globalNegation (assignment 112)))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C005.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (top_allows (Sign.withNegation globalNegation (assignment 114)))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C005.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C005.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C005.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C005.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C005.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C005.initial 120) (congrArg (Sign.withNegation globalNegation) hnode120) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C005.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C005.initial 122) (congrArg (Sign.withNegation globalNegation) hnode122) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C005.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C005.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Cases.C005.initial 125) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (domain_from_eq (domain := Cases.C005.initial 126) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded128 := below_succ bounded127 (domain_from_eq (domain := Cases.C005.initial 127) (congrArg (Sign.withNegation globalNegation) hnode127) (Eq.refl Bool.true))
  let bounded129 := below_succ bounded128 (domain_from_eq (domain := Cases.C005.initial 128) (congrArg (Sign.withNegation globalNegation) hnode128) (Eq.refl Bool.true))
  let bounded130 := below_succ bounded129 (domain_from_eq (domain := Cases.C005.initial 129) (congrArg (Sign.withNegation globalNegation) hnode129) (Eq.refl Bool.true))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C005.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C005.initial 131) (congrArg (Sign.withNegation globalNegation) hnode131) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C005.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C005.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C005.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C005.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C005.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (top_allows (Sign.withNegation globalNegation (assignment 137)))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C005.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C005.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (top_allows (Sign.withNegation globalNegation (assignment 140)))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C005.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C005.initial 142) (congrArg (Sign.withNegation globalNegation) hnode142) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C005.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C005.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (top_allows (Sign.withNegation globalNegation (assignment 145)))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C005.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C005.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C005.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (top_allows (Sign.withNegation globalNegation (assignment 149)))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C005.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (top_allows (Sign.withNegation globalNegation (assignment 151)))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C005.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (top_allows (Sign.withNegation globalNegation (assignment 153)))
  let bounded155 := below_succ bounded154 (top_allows (Sign.withNegation globalNegation (assignment 154)))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C005.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C005.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C005.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (top_allows (Sign.withNegation globalNegation (assignment 158)))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C005.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C005.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (domain_from_eq (domain := Cases.C005.initial 161) (congrArg (Sign.withNegation globalNegation) (h_zero 10 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Cases.C005.initial 162) (congrArg (Sign.withNegation globalNegation) (h_zero 11 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C005.initial 163) (congrArg (Sign.withNegation globalNegation) (h_zero 12 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C005.initial 164) (congrArg (Sign.withNegation globalNegation) (h_zero 13 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C005.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C005.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C005.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (top_allows (Sign.withNegation globalNegation (assignment 168)))
  let bounded170 := below_succ bounded169 (top_allows (Sign.withNegation globalNegation (assignment 169)))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C005.initial 170) (congrArg (Sign.withNegation globalNegation) hnode170) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C005.initial 171) (congrArg (Sign.withNegation globalNegation) hnode171) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C005.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C005.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (top_allows (Sign.withNegation globalNegation (assignment 174)))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C005.initial 175) (congrArg (Sign.withNegation globalNegation) hnode175) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (top_allows (Sign.withNegation globalNegation (assignment 176)))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Cases.C005.initial 177) (congrArg (Sign.withNegation globalNegation) hnode177) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C005.initial 178) (congrArg (Sign.withNegation globalNegation) hnode178) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C005.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (top_allows (Sign.withNegation globalNegation (assignment 180)))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C005.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C005.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C005.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (top_allows (Sign.withNegation globalNegation (assignment 184)))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C005.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Cases.C005.initial 186) (congrArg (Sign.withNegation globalNegation) hnode186) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C005.initial 187) (congrArg (Sign.withNegation globalNegation) hnode187) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C005.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C005.initial 189) (congrArg (Sign.withNegation globalNegation) (h_zero 14 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C005.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (top_allows (Sign.withNegation globalNegation (assignment 191)))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C005.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C005.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (top_allows (Sign.withNegation globalNegation (assignment 194)))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C005.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (domain_from_eq (domain := Cases.C005.initial 196) (congrArg (Sign.withNegation globalNegation) hnode196) (Eq.refl Bool.true))
  let bounded198 := below_succ bounded197 (domain_from_eq (domain := Cases.C005.initial 197) (congrArg (Sign.withNegation globalNegation) hnode197) (Eq.refl Bool.true))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Cases.C005.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (domain_from_eq (domain := Cases.C005.initial 199) (congrArg (Sign.withNegation globalNegation) hnode199) (Eq.refl Bool.true))
  let bounded201 := below_succ bounded200 (top_allows (Sign.withNegation globalNegation (assignment 200)))
  let bounded202 := below_succ bounded201 (top_allows (Sign.withNegation globalNegation (assignment 201)))
  let bounded203 := below_succ bounded202 (top_allows (Sign.withNegation globalNegation (assignment 202)))
  let bounded204 := below_succ bounded203 (domain_from_eq (domain := Cases.C005.initial 203) (congrArg (Sign.withNegation globalNegation) hnode203) (Eq.refl Bool.true))
  let bounded205 := below_succ bounded204 (domain_from_eq (domain := Cases.C005.initial 204) (congrArg (Sign.withNegation globalNegation) hnode204) (Eq.refl Bool.true))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C005.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Cases.C005.initial 206) (congrArg (Sign.withNegation globalNegation) hnode206) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (top_allows (Sign.withNegation globalNegation (assignment 207)))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C005.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C005.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C005.initial 210) (congrArg (Sign.withNegation globalNegation) (h_zero 15 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C005.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C005.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C005.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (top_allows (Sign.withNegation globalNegation (assignment 214)))
  let bounded216 := below_succ bounded215 (domain_from_eq (domain := Cases.C005.initial 215) (congrArg (Sign.withNegation globalNegation) hnode215) (Eq.refl Bool.true))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C005.initial 216) (congrArg (Sign.withNegation globalNegation) hnode216) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C005.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C005.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Cases.C005.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C005.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (domain_from_eq (domain := Cases.C005.initial 221) (congrArg (Sign.withNegation globalNegation) (h_zero 16 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded223 := below_succ bounded222 (top_allows (Sign.withNegation globalNegation (assignment 222)))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C005.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C005.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C005.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (top_allows (Sign.withNegation globalNegation (assignment 226)))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C005.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C005.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Cases.C005.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C005.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (domain_from_eq (domain := Cases.C005.initial 231) (congrArg (Sign.withNegation globalNegation) hnode231) (Eq.refl Bool.true))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C005.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (domain_from_eq (domain := Cases.C005.initial 233) (congrArg (Sign.withNegation globalNegation) hnode233) (Eq.refl Bool.true))
  let bounded235 := below_succ bounded234 (top_allows (Sign.withNegation globalNegation (assignment 234)))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C005.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (domain_from_eq (domain := Cases.C005.initial 236) (congrArg (Sign.withNegation globalNegation) hnode236) (Eq.refl Bool.true))
  let bounded238 := below_succ bounded237 (top_allows (Sign.withNegation globalNegation (assignment 237)))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C005.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Cases.C005.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (top_allows (Sign.withNegation globalNegation (assignment 240)))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C005.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C005.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (top_allows (Sign.withNegation globalNegation (assignment 243)))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C005.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C005.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C005.initial 246) (congrArg (Sign.withNegation globalNegation) hnode246) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C005.initial 247) (congrArg (Sign.withNegation globalNegation) (h_zero 17 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C005.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (domain_from_eq (domain := Cases.C005.initial 249) (congrArg (Sign.withNegation globalNegation) hnode249) (Eq.refl Bool.true))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Cases.C005.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C005.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C005.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C005
#print axioms Papers.RationalityTen.PureGP.Initializers.C005.support_sign_contradiction
