module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C011

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C011
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 1
def globalNegation : Bool := Bool.false
def edgeTable : Table SupportEdge := (Table.node 115 (Table.node 57 (Table.node 28 (Table.node 14 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 1 21 Bool.true)) (Table.node 2 (Table.leaf (SupportEdge.mk 1 26 Bool.false)) (Table.leaf (SupportEdge.mk 1 28 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 1 29 Bool.false)) (Table.leaf (SupportEdge.mk 3 23 Bool.true))) (Table.node 6 (Table.leaf (SupportEdge.mk 3 30 Bool.true)) (Table.leaf (SupportEdge.mk 3 33 Bool.false))))) (Table.node 10 (Table.node 8 (Table.leaf (SupportEdge.mk 3 34 Bool.false)) (Table.node 9 (Table.leaf (SupportEdge.mk 12 37 Bool.false)) (Table.leaf (SupportEdge.mk 12 46 Bool.true)))) (Table.node 12 (Table.node 11 (Table.leaf (SupportEdge.mk 12 49 Bool.false)) (Table.leaf (SupportEdge.mk 12 50 Bool.false))) (Table.node 13 (Table.leaf (SupportEdge.mk 62 92 Bool.true)) (Table.leaf (SupportEdge.mk 62 101 Bool.false)))))) (Table.node 21 (Table.node 17 (Table.node 15 (Table.leaf (SupportEdge.mk 62 104 Bool.true)) (Table.node 16 (Table.leaf (SupportEdge.mk 62 105 Bool.true)) (Table.leaf (SupportEdge.mk 132 162 Bool.true)))) (Table.node 19 (Table.node 18 (Table.leaf (SupportEdge.mk 132 171 Bool.false)) (Table.leaf (SupportEdge.mk 132 174 Bool.true))) (Table.node 20 (Table.leaf (SupportEdge.mk 132 175 Bool.true)) (Table.leaf (SupportEdge.mk 7 57 Bool.true))))) (Table.node 24 (Table.node 22 (Table.leaf (SupportEdge.mk 7 71 Bool.false)) (Table.node 23 (Table.leaf (SupportEdge.mk 7 75 Bool.true)) (Table.leaf (SupportEdge.mk 7 77 Bool.true)))) (Table.node 26 (Table.node 25 (Table.leaf (SupportEdge.mk 9 59 Bool.true)) (Table.leaf (SupportEdge.mk 9 73 Bool.false))) (Table.node 27 (Table.leaf (SupportEdge.mk 9 78 Bool.false)) (Table.leaf (SupportEdge.mk 9 80 Bool.true))))))) (Table.node 42 (Table.node 35 (Table.node 31 (Table.node 29 (Table.leaf (SupportEdge.mk 16 66 Bool.true)) (Table.node 30 (Table.leaf (SupportEdge.mk 16 82 Bool.true)) (Table.leaf (SupportEdge.mk 16 87 Bool.false)))) (Table.node 33 (Table.node 32 (Table.leaf (SupportEdge.mk 16 89 Bool.true)) (Table.leaf (SupportEdge.mk 41 96 Bool.false))) (Table.node 34 (Table.leaf (SupportEdge.mk 41 112 Bool.true)) (Table.leaf (SupportEdge.mk 41 117 Bool.false))))) (Table.node 38 (Table.node 36 (Table.leaf (SupportEdge.mk 41 119 Bool.true)) (Table.node 37 (Table.leaf (SupportEdge.mk 146 201 Bool.true)) (Table.leaf (SupportEdge.mk 146 217 Bool.false)))) (Table.node 40 (Table.node 39 (Table.leaf (SupportEdge.mk 146 222 Bool.true)) (Table.leaf (SupportEdge.mk 146 224 Bool.false))) (Table.node 41 (Table.leaf (SupportEdge.mk 21 56 Bool.false)) (Table.leaf (SupportEdge.mk 21 91 Bool.true)))))) (Table.node 49 (Table.node 45 (Table.node 43 (Table.leaf (SupportEdge.mk 21 92 Bool.true)) (Table.node 44 (Table.leaf (SupportEdge.mk 21 94 Bool.true)) (Table.leaf (SupportEdge.mk 24 59 Bool.false)))) (Table.node 47 (Table.node 46 (Table.leaf (SupportEdge.mk 24 96 Bool.false)) (Table.leaf (SupportEdge.mk 24 98 Bool.false))) (Table.node 48 (Table.leaf (SupportEdge.mk 24 100 Bool.true)) (Table.leaf (SupportEdge.mk 28 63 Bool.false))))) (Table.node 53 (Table.node 51 (Table.node 50 (Table.leaf (SupportEdge.mk 28 102 Bool.false)) (Table.leaf (SupportEdge.mk 28 104 Bool.false))) (Table.node 52 (Table.leaf (SupportEdge.mk 28 106 Bool.true)) (Table.leaf (SupportEdge.mk 38 73 Bool.false)))) (Table.node 55 (Table.node 54 (Table.leaf (SupportEdge.mk 38 112 Bool.false)) (Table.leaf (SupportEdge.mk 38 114 Bool.false))) (Table.node 56 (Table.leaf (SupportEdge.mk 38 116 Bool.true)) (Table.leaf (SupportEdge.mk 163 198 Bool.false)))))))) (Table.node 86 (Table.node 71 (Table.node 64 (Table.node 60 (Table.node 58 (Table.leaf (SupportEdge.mk 163 232 Bool.true)) (Table.node 59 (Table.leaf (SupportEdge.mk 163 234 Bool.true)) (Table.leaf (SupportEdge.mk 163 236 Bool.false)))) (Table.node 62 (Table.node 61 (Table.leaf (SupportEdge.mk 22 57 Bool.false)) (Table.leaf (SupportEdge.mk 22 91 Bool.false))) (Table.node 63 (Table.leaf (SupportEdge.mk 22 96 Bool.true)) (Table.leaf (SupportEdge.mk 22 97 Bool.true))))) (Table.node 67 (Table.node 65 (Table.leaf (SupportEdge.mk 23 58 Bool.false)) (Table.node 66 (Table.leaf (SupportEdge.mk 23 92 Bool.false)) (Table.leaf (SupportEdge.mk 23 98 Bool.true)))) (Table.node 69 (Table.node 68 (Table.leaf (SupportEdge.mk 23 99 Bool.true)) (Table.leaf (SupportEdge.mk 30 65 Bool.false))) (Table.node 70 (Table.leaf (SupportEdge.mk 30 101 Bool.true)) (Table.leaf (SupportEdge.mk 30 107 Bool.true)))))) (Table.node 78 (Table.node 74 (Table.node 72 (Table.leaf (SupportEdge.mk 30 108 Bool.true)) (Table.node 73 (Table.leaf (SupportEdge.mk 40 75 Bool.false)) (Table.leaf (SupportEdge.mk 40 111 Bool.true)))) (Table.node 76 (Table.node 75 (Table.leaf (SupportEdge.mk 40 117 Bool.true)) (Table.leaf (SupportEdge.mk 40 118 Bool.true))) (Table.node 77 (Table.leaf (SupportEdge.mk 165 200 Bool.false)) (Table.leaf (SupportEdge.mk 165 231 Bool.false))))) (Table.node 82 (Table.node 80 (Table.node 79 (Table.leaf (SupportEdge.mk 165 237 Bool.false)) (Table.leaf (SupportEdge.mk 165 238 Bool.false))) (Table.node 81 (Table.leaf (SupportEdge.mk 46 81 Bool.false)) (Table.leaf (SupportEdge.mk 46 101 Bool.false)))) (Table.node 84 (Table.node 83 (Table.leaf (SupportEdge.mk 46 111 Bool.false)) (Table.leaf (SupportEdge.mk 46 121 Bool.true))) (Table.node 85 (Table.leaf (SupportEdge.mk 46 122 Bool.true)) (Table.leaf (SupportEdge.mk 47 82 Bool.false))))))) (Table.node 100 (Table.node 93 (Table.node 89 (Table.node 87 (Table.leaf (SupportEdge.mk 47 102 Bool.false)) (Table.node 88 (Table.leaf (SupportEdge.mk 47 112 Bool.false)) (Table.leaf (SupportEdge.mk 47 121 Bool.false)))) (Table.node 91 (Table.node 90 (Table.leaf (SupportEdge.mk 48 83 Bool.false)) (Table.leaf (SupportEdge.mk 48 103 Bool.false))) (Table.node 92 (Table.leaf (SupportEdge.mk 48 113 Bool.false)) (Table.leaf (SupportEdge.mk 48 122 Bool.false))))) (Table.node 96 (Table.node 94 (Table.leaf (SupportEdge.mk 51 86 Bool.false)) (Table.node 95 (Table.leaf (SupportEdge.mk 51 106 Bool.false)) (Table.leaf (SupportEdge.mk 51 116 Bool.false)))) (Table.node 98 (Table.node 97 (Table.leaf (SupportEdge.mk 51 124 Bool.true)) (Table.leaf (SupportEdge.mk 54 89 Bool.false))) (Table.node 99 (Table.leaf (SupportEdge.mk 54 109 Bool.false)) (Table.leaf (SupportEdge.mk 54 119 Bool.false)))))) (Table.node 107 (Table.node 103 (Table.node 101 (Table.leaf (SupportEdge.mk 54 125 Bool.true)) (Table.node 102 (Table.leaf (SupportEdge.mk 193 228 Bool.false)) (Table.leaf (SupportEdge.mk 193 243 Bool.false)))) (Table.node 105 (Table.node 104 (Table.leaf (SupportEdge.mk 193 248 Bool.false)) (Table.leaf (SupportEdge.mk 193 251 Bool.false))) (Table.node 106 (Table.leaf (SupportEdge.mk 0 126 Bool.false)) (Table.leaf (SupportEdge.mk 0 127 Bool.false))))) (Table.node 111 (Table.node 109 (Table.node 108 (Table.leaf (SupportEdge.mk 0 129 Bool.false)) (Table.leaf (SupportEdge.mk 0 130 Bool.false))) (Table.node 110 (Table.leaf (SupportEdge.mk 3 132 Bool.true)) (Table.leaf (SupportEdge.mk 3 135 Bool.true)))) (Table.node 113 (Table.node 112 (Table.leaf (SupportEdge.mk 3 138 Bool.false)) (Table.leaf (SupportEdge.mk 3 139 Bool.false))) (Table.node 114 (Table.leaf (SupportEdge.mk 8 142 Bool.true)) (Table.leaf (SupportEdge.mk 8 145 Bool.true))))))))) (Table.node 172 (Table.node 143 (Table.node 129 (Table.node 122 (Table.node 118 (Table.node 116 (Table.leaf (SupportEdge.mk 8 148 Bool.false)) (Table.node 117 (Table.leaf (SupportEdge.mk 8 149 Bool.false)) (Table.leaf (SupportEdge.mk 23 162 Bool.true)))) (Table.node 120 (Table.node 119 (Table.leaf (SupportEdge.mk 23 165 Bool.true)) (Table.leaf (SupportEdge.mk 23 168 Bool.false))) (Table.node 121 (Table.leaf (SupportEdge.mk 23 169 Bool.false)) (Table.leaf (SupportEdge.mk 58 197 Bool.true))))) (Table.node 125 (Table.node 123 (Table.leaf (SupportEdge.mk 58 200 Bool.true)) (Table.node 124 (Table.leaf (SupportEdge.mk 58 203 Bool.false)) (Table.leaf (SupportEdge.mk 58 204 Bool.false)))) (Table.node 127 (Table.node 126 (Table.leaf (SupportEdge.mk 0 126 Bool.false)) (Table.leaf (SupportEdge.mk 0 127 Bool.false))) (Table.node 128 (Table.leaf (SupportEdge.mk 0 128 Bool.false)) (Table.leaf (SupportEdge.mk 0 130 Bool.false)))))) (Table.node 136 (Table.node 132 (Table.node 130 (Table.leaf (SupportEdge.mk 4 133 Bool.true)) (Table.node 131 (Table.leaf (SupportEdge.mk 4 136 Bool.true)) (Table.leaf (SupportEdge.mk 4 138 Bool.true)))) (Table.node 134 (Table.node 133 (Table.leaf (SupportEdge.mk 4 140 Bool.false)) (Table.leaf (SupportEdge.mk 9 143 Bool.true))) (Table.node 135 (Table.leaf (SupportEdge.mk 9 146 Bool.true)) (Table.leaf (SupportEdge.mk 9 148 Bool.true))))) (Table.node 139 (Table.node 137 (Table.leaf (SupportEdge.mk 9 150 Bool.false)) (Table.node 138 (Table.leaf (SupportEdge.mk 24 163 Bool.true)) (Table.leaf (SupportEdge.mk 24 166 Bool.true)))) (Table.node 141 (Table.node 140 (Table.leaf (SupportEdge.mk 24 168 Bool.true)) (Table.leaf (SupportEdge.mk 24 170 Bool.false))) (Table.node 142 (Table.leaf (SupportEdge.mk 59 198 Bool.true)) (Table.leaf (SupportEdge.mk 59 201 Bool.true))))))) (Table.node 157 (Table.node 150 (Table.node 146 (Table.node 144 (Table.leaf (SupportEdge.mk 59 203 Bool.true)) (Table.node 145 (Table.leaf (SupportEdge.mk 59 205 Bool.false)) (Table.leaf (SupportEdge.mk 12 132 Bool.false)))) (Table.node 148 (Table.node 147 (Table.leaf (SupportEdge.mk 12 142 Bool.false)) (Table.leaf (SupportEdge.mk 12 151 Bool.true))) (Table.node 149 (Table.leaf (SupportEdge.mk 12 154 Bool.false)) (Table.leaf (SupportEdge.mk 14 134 Bool.false))))) (Table.node 153 (Table.node 151 (Table.leaf (SupportEdge.mk 14 144 Bool.false)) (Table.node 152 (Table.leaf (SupportEdge.mk 14 153 Bool.true)) (Table.leaf (SupportEdge.mk 14 156 Bool.true)))) (Table.node 155 (Table.node 154 (Table.leaf (SupportEdge.mk 19 139 Bool.false)) (Table.leaf (SupportEdge.mk 19 149 Bool.false))) (Table.node 156 (Table.leaf (SupportEdge.mk 19 158 Bool.false)) (Table.leaf (SupportEdge.mk 19 160 Bool.true)))))) (Table.node 164 (Table.node 160 (Table.node 158 (Table.leaf (SupportEdge.mk 50 175 Bool.true)) (Table.node 159 (Table.leaf (SupportEdge.mk 50 185 Bool.true)) (Table.leaf (SupportEdge.mk 50 192 Bool.false)))) (Table.node 162 (Table.node 161 (Table.leaf (SupportEdge.mk 50 194 Bool.true)) (Table.leaf (SupportEdge.mk 85 210 Bool.true))) (Table.node 163 (Table.leaf (SupportEdge.mk 85 220 Bool.true)) (Table.leaf (SupportEdge.mk 85 227 Bool.false))))) (Table.node 168 (Table.node 166 (Table.node 165 (Table.leaf (SupportEdge.mk 85 229 Bool.true)) (Table.leaf (SupportEdge.mk 16 136 Bool.false))) (Table.node 167 (Table.leaf (SupportEdge.mk 16 146 Bool.false)) (Table.leaf (SupportEdge.mk 16 152 Bool.false)))) (Table.node 170 (Table.node 169 (Table.leaf (SupportEdge.mk 16 157 Bool.true)) (Table.leaf (SupportEdge.mk 17 137 Bool.false))) (Table.node 171 (Table.leaf (SupportEdge.mk 17 147 Bool.false)) (Table.leaf (SupportEdge.mk 17 153 Bool.false)))))))) (Table.node 201 (Table.node 186 (Table.node 179 (Table.node 175 (Table.node 173 (Table.leaf (SupportEdge.mk 17 158 Bool.true)) (Table.node 174 (Table.leaf (SupportEdge.mk 20 140 Bool.false)) (Table.leaf (SupportEdge.mk 20 150 Bool.false)))) (Table.node 177 (Table.node 176 (Table.leaf (SupportEdge.mk 20 156 Bool.false)) (Table.leaf (SupportEdge.mk 20 160 Bool.false))) (Table.node 178 (Table.leaf (SupportEdge.mk 54 179 Bool.true)) (Table.leaf (SupportEdge.mk 54 189 Bool.true))))) (Table.node 182 (Table.node 180 (Table.leaf (SupportEdge.mk 54 193 Bool.true)) (Table.node 181 (Table.leaf (SupportEdge.mk 54 195 Bool.false)) (Table.leaf (SupportEdge.mk 89 214 Bool.true)))) (Table.node 184 (Table.node 183 (Table.leaf (SupportEdge.mk 89 224 Bool.true)) (Table.leaf (SupportEdge.mk 89 228 Bool.true))) (Table.node 185 (Table.leaf (SupportEdge.mk 89 230 Bool.false)) (Table.leaf (SupportEdge.mk 28 133 Bool.true)))))) (Table.node 193 (Table.node 189 (Table.node 187 (Table.leaf (SupportEdge.mk 28 163 Bool.false)) (Table.node 188 (Table.leaf (SupportEdge.mk 28 172 Bool.true)) (Table.leaf (SupportEdge.mk 28 174 Bool.true)))) (Table.node 191 (Table.node 190 (Table.leaf (SupportEdge.mk 29 134 Bool.true)) (Table.leaf (SupportEdge.mk 29 164 Bool.false))) (Table.node 192 (Table.leaf (SupportEdge.mk 29 173 Bool.true)) (Table.leaf (SupportEdge.mk 29 175 Bool.true))))) (Table.node 197 (Table.node 195 (Table.node 194 (Table.leaf (SupportEdge.mk 35 140 Bool.true)) (Table.leaf (SupportEdge.mk 35 170 Bool.false))) (Table.node 196 (Table.leaf (SupportEdge.mk 35 179 Bool.false)) (Table.leaf (SupportEdge.mk 35 180 Bool.false)))) (Table.node 199 (Table.node 198 (Table.leaf (SupportEdge.mk 51 156 Bool.true)) (Table.leaf (SupportEdge.mk 51 186 Bool.true))) (Table.node 200 (Table.leaf (SupportEdge.mk 51 193 Bool.false)) (Table.leaf (SupportEdge.mk 51 194 Bool.false))))))) (Table.node 215 (Table.node 208 (Table.node 204 (Table.node 202 (Table.leaf (SupportEdge.mk 106 211 Bool.false)) (Table.node 203 (Table.leaf (SupportEdge.mk 106 236 Bool.true)) (Table.leaf (SupportEdge.mk 106 243 Bool.false)))) (Table.node 206 (Table.node 205 (Table.leaf (SupportEdge.mk 106 244 Bool.false)) (Table.leaf (SupportEdge.mk 75 145 Bool.false))) (Table.node 207 (Table.leaf (SupportEdge.mk 75 200 Bool.true)) (Table.leaf (SupportEdge.mk 75 216 Bool.false))))) (Table.node 211 (Table.node 209 (Table.leaf (SupportEdge.mk 75 222 Bool.false)) (Table.node 210 (Table.leaf (SupportEdge.mk 77 147 Bool.false)) (Table.leaf (SupportEdge.mk 77 202 Bool.true)))) (Table.node 213 (Table.node 212 (Table.leaf (SupportEdge.mk 77 218 Bool.false)) (Table.leaf (SupportEdge.mk 77 224 Bool.true))) (Table.node 214 (Table.leaf (SupportEdge.mk 79 149 Bool.false)) (Table.leaf (SupportEdge.mk 79 204 Bool.true)))))) (Table.node 222 (Table.node 218 (Table.node 216 (Table.leaf (SupportEdge.mk 79 220 Bool.false)) (Table.node 217 (Table.leaf (SupportEdge.mk 79 225 Bool.true)) (Table.leaf (SupportEdge.mk 88 158 Bool.false)))) (Table.node 220 (Table.node 219 (Table.leaf (SupportEdge.mk 88 213 Bool.true)) (Table.leaf (SupportEdge.mk 88 227 Bool.true))) (Table.node 221 (Table.leaf (SupportEdge.mk 88 230 Bool.true)) (Table.leaf (SupportEdge.mk 118 188 Bool.false))))) (Table.node 226 (Table.node 224 (Table.node 223 (Table.leaf (SupportEdge.mk 118 238 Bool.false)) (Table.leaf (SupportEdge.mk 118 247 Bool.true))) (Table.node 225 (Table.leaf (SupportEdge.mk 118 250 Bool.true)) (Table.leaf (SupportEdge.mk 122 192 Bool.false)))) (Table.node 228 (Table.node 227 (Table.leaf (SupportEdge.mk 122 227 Bool.false)) (Table.leaf (SupportEdge.mk 122 242 Bool.false))) (Table.node 229 (Table.leaf (SupportEdge.mk 122 247 Bool.false)) (Table.leaf (SupportEdge.mk 122 251 Bool.true))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf 0) (Table.node 2 (Table.leaf 27) (Table.leaf 76))) (Table.node 5 (Table.node 4 (Table.leaf 93) (Table.leaf 95)) (Table.node 6 (Table.leaf 123) (Table.leaf 126)))) (Table.node 11 (Table.node 9 (Table.node 8 (Table.leaf 127) (Table.leaf 128)) (Table.node 10 (Table.leaf 129) (Table.leaf 130))) (Table.node 13 (Table.node 12 (Table.leaf 155) (Table.leaf 159)) (Table.node 14 (Table.leaf 176) (Table.leaf 223)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 230 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 15 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C011.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode21 : Eq (assignment 21) Sign.negative :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode26 : Eq (assignment 26) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode28 : Eq (assignment 28) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode29 : Eq (assignment 29) Sign.positive :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode56 : Eq (assignment 56) Sign.negative :=
    Eq.trans (h_support 40 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode21)
  let hnode63 : Eq (assignment 63) Sign.positive :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode91 : Eq (assignment 91) Sign.positive :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode92 : Eq (assignment 92) Sign.positive :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode94 : Eq (assignment 94) Sign.positive :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode102 : Eq (assignment 102) Sign.positive :=
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode104 : Eq (assignment 104) Sign.positive :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode106 : Eq (assignment 106) Sign.negative :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode133 : Eq (assignment 133) Sign.negative :=
    Eq.trans (h_support 185 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode134 : Eq (assignment 134) Sign.negative :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode163 : Eq (assignment 163) Sign.positive :=
    Eq.trans (h_support 186 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode164 : Eq (assignment 164) Sign.positive :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode172 : Eq (assignment 172) Sign.negative :=
    Eq.trans (h_support 187 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode173 : Eq (assignment 173) Sign.negative :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode174 : Eq (assignment 174) Sign.negative :=
    Eq.trans (h_support 188 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode175 : Eq (assignment 175) Sign.negative :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode4 : Eq (assignment 4) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 129 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode133)
  let hnode14 : Eq (assignment 14) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 149 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode134)
  let hnode22 : Eq (assignment 22) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 61 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode23 : Eq (assignment 23) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 65 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode24 : Eq (assignment 24) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 137 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode163)
  let hnode47 : Eq (assignment 47) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 86 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode102)
  let hnode50 : Eq (assignment 50) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 157 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode175)
  let hnode51 : Eq (assignment 51) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 94 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode106)
  let hnode62 : Eq (assignment 62) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 12 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode92)
  let hnode132 : Eq (assignment 132) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 18 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode174)
  let hnode198 : Eq (assignment 198) Sign.positive :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode163)
  let hnode211 : Eq (assignment 211) Sign.negative :=
    Eq.trans (h_support 201 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode106)
  let hnode232 : Eq (assignment 232) Sign.negative :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode163)
  let hnode234 : Eq (assignment 234) Sign.negative :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode163)
  let hnode236 : Eq (assignment 236) Sign.positive :=
    Eq.trans (h_support 202 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode106)
  let hnode243 : Eq (assignment 243) Sign.negative :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode106)
  let hnode244 : Eq (assignment 244) Sign.negative :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode106)
  let hnode3 : Eq (assignment 3) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 4 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode12 : Eq (assignment 12) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 145 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode132)
  let hnode57 : Eq (assignment 57) Sign.positive :=
    Eq.trans (h_support 60 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode58 : Eq (assignment 58) Sign.positive :=
    Eq.trans (h_support 64 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode59 : Eq (assignment 59) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 141 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode198)
  let hnode82 : Eq (assignment 82) Sign.positive :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode86 : Eq (assignment 86) Sign.negative :=
    Eq.trans (h_support 93 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode51)
  let hnode96 : Eq (assignment 96) Sign.negative :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode97 : Eq (assignment 97) Sign.negative :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode98 : Eq (assignment 98) Sign.negative :=
    Eq.trans (h_support 66 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode99 : Eq (assignment 99) Sign.negative :=
    Eq.trans (h_support 67 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode100 : Eq (assignment 100) Sign.positive :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode101 : Eq (assignment 101) Sign.negative :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode62)
  let hnode105 : Eq (assignment 105) Sign.positive :=
    Eq.trans (h_support 15 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode62)
  let hnode112 : Eq (assignment 112) Sign.positive :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode116 : Eq (assignment 116) Sign.negative :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode51)
  let hnode121 : Eq (assignment 121) Sign.positive :=
    Eq.trans (h_support 88 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode124 : Eq (assignment 124) Sign.positive :=
    Eq.trans (h_support 96 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode51)
  let hnode136 : Eq (assignment 136) Sign.negative :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode138 : Eq (assignment 138) Sign.negative :=
    Eq.trans (h_support 131 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode140 : Eq (assignment 140) Sign.positive :=
    Eq.trans (h_support 132 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode144 : Eq (assignment 144) Sign.negative :=
    Eq.trans (h_support 150 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode153 : Eq (assignment 153) Sign.positive :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode156 : Eq (assignment 156) Sign.positive :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode51)
  let hnode162 : Eq (assignment 162) Sign.negative :=
    Eq.trans (h_support 117 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode165 : Eq (assignment 165) Sign.negative :=
    Eq.trans (h_support 118 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode166 : Eq (assignment 166) Sign.positive :=
    Eq.trans (h_support 138 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode168 : Eq (assignment 168) Sign.positive :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode169 : Eq (assignment 169) Sign.positive :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode170 : Eq (assignment 170) Sign.negative :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode24)
  let hnode171 : Eq (assignment 171) Sign.positive :=
    Eq.trans (h_support 17 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode132)
  let hnode185 : Eq (assignment 185) Sign.negative :=
    Eq.trans (h_support 158 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode50)
  let hnode186 : Eq (assignment 186) Sign.positive :=
    Eq.trans (h_support 198 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode51)
  let hnode192 : Eq (assignment 192) Sign.positive :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode50)
  let hnode193 : Eq (assignment 193) Sign.negative :=
    Eq.trans (h_support 199 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode51)
  let hnode194 : Eq (assignment 194) Sign.negative :=
    Eq.trans (h_support 200 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode51)
  let hnode7 : Eq (assignment 7) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 20 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode57)
  let hnode9 : Eq (assignment 9) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 24 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode59)
  let hnode16 : Eq (assignment 16) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 29 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode82)
  let hnode17 : Eq (assignment 17) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 171 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode153)
  let hnode20 : Eq (assignment 20) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 175 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode156)
  let hnode30 : Eq (assignment 30) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 69 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode101)
  let hnode33 : Eq (assignment 33) Sign.negative :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode34 : Eq (assignment 34) Sign.negative :=
    Eq.trans (h_support 7 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode35 : Eq (assignment 35) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 193 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode140)
  let hnode37 : Eq (assignment 37) Sign.positive :=
    Eq.trans (h_support 8 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode38 : Eq (assignment 38) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 53 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode41 : Eq (assignment 41) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 32 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode96)
  let hnode46 : Eq (assignment 46) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 81 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode101)
  let hnode49 : Eq (assignment 49) Sign.positive :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode54 : Eq (assignment 54) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 179 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode193)
  let hnode122 : Eq (assignment 122) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 225 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode192)
  let hnode135 : Eq (assignment 135) Sign.positive :=
    Eq.trans (h_support 110 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode139 : Eq (assignment 139) Sign.negative :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode142 : Eq (assignment 142) Sign.positive :=
    Eq.trans (h_support 146 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode151 : Eq (assignment 151) Sign.negative :=
    Eq.trans (h_support 147 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode12)
  let hnode154 : Eq (assignment 154) Sign.positive :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode197 : Eq (assignment 197) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode58)
  let hnode200 : Eq (assignment 200) Sign.negative :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode58)
  let hnode201 : Eq (assignment 201) Sign.positive :=
    Eq.trans (h_support 142 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode59)
  let hnode203 : Eq (assignment 203) Sign.positive :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode204 : Eq (assignment 204) Sign.positive :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode205 : Eq (assignment 205) Sign.negative :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode59)
  let hnode228 : Eq (assignment 228) Sign.negative :=
    Eq.trans (h_support 101 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode193)
  let hnode231 : Eq (assignment 231) Sign.negative :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode165)
  let hnode237 : Eq (assignment 237) Sign.negative :=
    Eq.trans (h_support 78 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode165)
  let hnode238 : Eq (assignment 238) Sign.negative :=
    Eq.trans (h_support 79 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode165)
  let hnode248 : Eq (assignment 248) Sign.negative :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode193)
  let hnode251 : Eq (assignment 251) Sign.negative :=
    Eq.trans (h_support 104 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode193)
  let hnode8 : Eq (assignment 8) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 113 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode142)
  let hnode19 : Eq (assignment 19) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 153 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode139)
  let hnode48 : Eq (assignment 48) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 92 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode122)
  let hnode65 : Eq (assignment 65) Sign.positive :=
    Eq.trans (h_support 68 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode30)
  let hnode66 : Eq (assignment 66) Sign.positive :=
    Eq.trans (h_support 28 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode16)
  let hnode71 : Eq (assignment 71) Sign.negative :=
    Eq.trans (h_support 21 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode7)
  let hnode73 : Eq (assignment 73) Sign.positive :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode75 : Eq (assignment 75) Sign.positive :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode7)
  let hnode77 : Eq (assignment 77) Sign.positive :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode7)
  let hnode78 : Eq (assignment 78) Sign.positive :=
    Eq.trans (h_support 26 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode79 : Eq (assignment 79) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 214 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode204)
  let hnode80 : Eq (assignment 80) Sign.negative :=
    Eq.trans (h_support 27 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode81 : Eq (assignment 81) Sign.negative :=
    Eq.trans (h_support 80 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode87 : Eq (assignment 87) Sign.negative :=
    Eq.trans (h_support 30 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode89 : Eq (assignment 89) Sign.positive :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode16)
  let hnode107 : Eq (assignment 107) Sign.negative :=
    Eq.trans (h_support 70 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode108 : Eq (assignment 108) Sign.negative :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode109 : Eq (assignment 109) Sign.positive :=
    Eq.trans (h_support 98 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode111 : Eq (assignment 111) Sign.negative :=
    Eq.trans (h_support 82 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode114 : Eq (assignment 114) Sign.positive :=
    Eq.trans (h_support 54 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode117 : Eq (assignment 117) Sign.negative :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode118 : Eq (assignment 118) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 222 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode238)
  let hnode119 : Eq (assignment 119) Sign.positive :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode125 : Eq (assignment 125) Sign.negative :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode137 : Eq (assignment 137) Sign.positive :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode143 : Eq (assignment 143) Sign.negative :=
    Eq.trans (h_support 133 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode146 : Eq (assignment 146) Sign.negative :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode147 : Eq (assignment 147) Sign.positive :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode148 : Eq (assignment 148) Sign.negative :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode150 : Eq (assignment 150) Sign.positive :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode152 : Eq (assignment 152) Sign.negative :=
    Eq.trans (h_support 167 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode157 : Eq (assignment 157) Sign.positive :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode16)
  let hnode158 : Eq (assignment 158) Sign.negative :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode160 : Eq (assignment 160) Sign.positive :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 177 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode180 : Eq (assignment 180) Sign.negative :=
    Eq.trans (h_support 196 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode189 : Eq (assignment 189) Sign.negative :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode195 : Eq (assignment 195) Sign.positive :=
    Eq.trans (h_support 180 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode227 : Eq (assignment 227) Sign.positive :=
    Eq.trans (h_support 226 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode122)
  let hnode242 : Eq (assignment 242) Sign.positive :=
    Eq.trans (h_support 227 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode122)
  let hnode247 : Eq (assignment 247) Sign.positive :=
    Eq.trans (h_support 228 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode122)
  let hnode40 : Eq (assignment 40) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 72 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode75)
  let hnode83 : Eq (assignment 83) Sign.positive :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode85 : Eq (assignment 85) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 163 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode227)
  let hnode88 : Eq (assignment 88) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 217 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode158)
  let hnode103 : Eq (assignment 103) Sign.positive :=
    Eq.trans (h_support 90 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode113 : Eq (assignment 113) Sign.positive :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode145 : Eq (assignment 145) Sign.positive :=
    Eq.trans (h_support 205 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode75)
  let hnode149 : Eq (assignment 149) Sign.negative :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode188 : Eq (assignment 188) Sign.negative :=
    Eq.trans (h_support 221 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode118)
  let hnode202 : Eq (assignment 202) Sign.negative :=
    Eq.trans (h_support 210 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode77)
  let hnode214 : Eq (assignment 214) Sign.negative :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode89)
  let hnode216 : Eq (assignment 216) Sign.positive :=
    Eq.trans (h_support 207 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode75)
  let hnode217 : Eq (assignment 217) Sign.negative :=
    Eq.trans (h_support 37 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode146)
  let hnode218 : Eq (assignment 218) Sign.positive :=
    Eq.trans (h_support 211 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode77)
  let hnode220 : Eq (assignment 220) Sign.negative :=
    Eq.trans (h_support 215 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode79)
  let hnode222 : Eq (assignment 222) Sign.positive :=
    Eq.trans (h_support 208 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode75)
  let hnode224 : Eq (assignment 224) Sign.negative :=
    Eq.trans (h_support 212 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode77)
  let hnode225 : Eq (assignment 225) Sign.positive :=
    Eq.trans (h_support 216 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode79)
  let hnode230 : Eq (assignment 230) Sign.positive :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode89)
  let hnode250 : Eq (assignment 250) Sign.positive :=
    Eq.trans (h_support 224 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode118)
  let hnode210 : Eq (assignment 210) Sign.negative :=
    Eq.trans (h_support 161 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode85)
  let hnode213 : Eq (assignment 213) Sign.positive :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode229 : Eq (assignment 229) Sign.negative :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode85)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C011.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (domain_from_eq (domain := Cases.C011.initial 0) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded2 := below_succ bounded1 (domain_from_eq (domain := Cases.C011.initial 1) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded3 := below_succ bounded2 (top_allows (Sign.withNegation globalNegation (assignment 2)))
  let bounded4 := below_succ bounded3 (domain_from_eq (domain := Cases.C011.initial 3) (congrArg (Sign.withNegation globalNegation) hnode3) (Eq.refl Bool.true))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C011.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (top_allows (Sign.withNegation globalNegation (assignment 5)))
  let bounded7 := below_succ bounded6 (top_allows (Sign.withNegation globalNegation (assignment 6)))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Cases.C011.initial 7) (congrArg (Sign.withNegation globalNegation) hnode7) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C011.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Cases.C011.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (top_allows (Sign.withNegation globalNegation (assignment 10)))
  let bounded12 := below_succ bounded11 (top_allows (Sign.withNegation globalNegation (assignment 11)))
  let bounded13 := below_succ bounded12 (domain_from_eq (domain := Cases.C011.initial 12) (congrArg (Sign.withNegation globalNegation) hnode12) (Eq.refl Bool.true))
  let bounded14 := below_succ bounded13 (top_allows (Sign.withNegation globalNegation (assignment 13)))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C011.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (top_allows (Sign.withNegation globalNegation (assignment 15)))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Cases.C011.initial 16) (congrArg (Sign.withNegation globalNegation) hnode16) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C011.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (top_allows (Sign.withNegation globalNegation (assignment 18)))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C011.initial 19) (congrArg (Sign.withNegation globalNegation) hnode19) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Cases.C011.initial 20) (congrArg (Sign.withNegation globalNegation) hnode20) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C011.initial 21) (congrArg (Sign.withNegation globalNegation) hnode21) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (domain_from_eq (domain := Cases.C011.initial 22) (congrArg (Sign.withNegation globalNegation) hnode22) (Eq.refl Bool.true))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C011.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C011.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (top_allows (Sign.withNegation globalNegation (assignment 25)))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Cases.C011.initial 26) (congrArg (Sign.withNegation globalNegation) hnode26) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C011.initial 27) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C011.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C011.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (domain_from_eq (domain := Cases.C011.initial 30) (congrArg (Sign.withNegation globalNegation) hnode30) (Eq.refl Bool.true))
  let bounded32 := below_succ bounded31 (top_allows (Sign.withNegation globalNegation (assignment 31)))
  let bounded33 := below_succ bounded32 (top_allows (Sign.withNegation globalNegation (assignment 32)))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C011.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C011.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (domain_from_eq (domain := Cases.C011.initial 35) (congrArg (Sign.withNegation globalNegation) hnode35) (Eq.refl Bool.true))
  let bounded37 := below_succ bounded36 (top_allows (Sign.withNegation globalNegation (assignment 36)))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C011.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C011.initial 38) (congrArg (Sign.withNegation globalNegation) hnode38) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (top_allows (Sign.withNegation globalNegation (assignment 39)))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Cases.C011.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C011.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (top_allows (Sign.withNegation globalNegation (assignment 42)))
  let bounded44 := below_succ bounded43 (top_allows (Sign.withNegation globalNegation (assignment 43)))
  let bounded45 := below_succ bounded44 (top_allows (Sign.withNegation globalNegation (assignment 44)))
  let bounded46 := below_succ bounded45 (top_allows (Sign.withNegation globalNegation (assignment 45)))
  let bounded47 := below_succ bounded46 (domain_from_eq (domain := Cases.C011.initial 46) (congrArg (Sign.withNegation globalNegation) hnode46) (Eq.refl Bool.true))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C011.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (domain_from_eq (domain := Cases.C011.initial 48) (congrArg (Sign.withNegation globalNegation) hnode48) (Eq.refl Bool.true))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C011.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (domain_from_eq (domain := Cases.C011.initial 50) (congrArg (Sign.withNegation globalNegation) hnode50) (Eq.refl Bool.true))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C011.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (top_allows (Sign.withNegation globalNegation (assignment 52)))
  let bounded54 := below_succ bounded53 (top_allows (Sign.withNegation globalNegation (assignment 53)))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Cases.C011.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (top_allows (Sign.withNegation globalNegation (assignment 55)))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C011.initial 56) (congrArg (Sign.withNegation globalNegation) hnode56) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C011.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C011.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C011.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (top_allows (Sign.withNegation globalNegation (assignment 60)))
  let bounded62 := below_succ bounded61 (top_allows (Sign.withNegation globalNegation (assignment 61)))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C011.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C011.initial 63) (congrArg (Sign.withNegation globalNegation) hnode63) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (top_allows (Sign.withNegation globalNegation (assignment 64)))
  let bounded66 := below_succ bounded65 (domain_from_eq (domain := Cases.C011.initial 65) (congrArg (Sign.withNegation globalNegation) hnode65) (Eq.refl Bool.true))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C011.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (top_allows (Sign.withNegation globalNegation (assignment 67)))
  let bounded69 := below_succ bounded68 (top_allows (Sign.withNegation globalNegation (assignment 68)))
  let bounded70 := below_succ bounded69 (top_allows (Sign.withNegation globalNegation (assignment 69)))
  let bounded71 := below_succ bounded70 (top_allows (Sign.withNegation globalNegation (assignment 70)))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C011.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (top_allows (Sign.withNegation globalNegation (assignment 72)))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C011.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (top_allows (Sign.withNegation globalNegation (assignment 74)))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Cases.C011.initial 75) (congrArg (Sign.withNegation globalNegation) hnode75) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Cases.C011.initial 76) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C011.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C011.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C011.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (domain_from_eq (domain := Cases.C011.initial 80) (congrArg (Sign.withNegation globalNegation) hnode80) (Eq.refl Bool.true))
  let bounded82 := below_succ bounded81 (domain_from_eq (domain := Cases.C011.initial 81) (congrArg (Sign.withNegation globalNegation) hnode81) (Eq.refl Bool.true))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Cases.C011.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C011.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (top_allows (Sign.withNegation globalNegation (assignment 84)))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C011.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C011.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C011.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Cases.C011.initial 88) (congrArg (Sign.withNegation globalNegation) hnode88) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (domain_from_eq (domain := Cases.C011.initial 89) (congrArg (Sign.withNegation globalNegation) hnode89) (Eq.refl Bool.true))
  let bounded91 := below_succ bounded90 (top_allows (Sign.withNegation globalNegation (assignment 90)))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C011.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C011.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C011.initial 93) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C011.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C011.initial 95) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C011.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (domain_from_eq (domain := Cases.C011.initial 97) (congrArg (Sign.withNegation globalNegation) hnode97) (Eq.refl Bool.true))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C011.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C011.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C011.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C011.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C011.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C011.initial 103) (congrArg (Sign.withNegation globalNegation) hnode103) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C011.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C011.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C011.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C011.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C011.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C011.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (top_allows (Sign.withNegation globalNegation (assignment 110)))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C011.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C011.initial 112) (congrArg (Sign.withNegation globalNegation) hnode112) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C011.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C011.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (top_allows (Sign.withNegation globalNegation (assignment 115)))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C011.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C011.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C011.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C011.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (top_allows (Sign.withNegation globalNegation (assignment 120)))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C011.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C011.initial 122) (congrArg (Sign.withNegation globalNegation) hnode122) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C011.initial 123) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C011.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Cases.C011.initial 125) (congrArg (Sign.withNegation globalNegation) hnode125) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (domain_from_eq (domain := Cases.C011.initial 126) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded128 := below_succ bounded127 (domain_from_eq (domain := Cases.C011.initial 127) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded129 := below_succ bounded128 (domain_from_eq (domain := Cases.C011.initial 128) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded130 := below_succ bounded129 (domain_from_eq (domain := Cases.C011.initial 129) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C011.initial 130) (congrArg (Sign.withNegation globalNegation) (h_zero 10 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (top_allows (Sign.withNegation globalNegation (assignment 131)))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C011.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C011.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C011.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C011.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C011.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C011.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C011.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C011.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C011.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (top_allows (Sign.withNegation globalNegation (assignment 141)))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C011.initial 142) (congrArg (Sign.withNegation globalNegation) hnode142) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C011.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C011.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C011.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C011.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C011.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C011.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C011.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C011.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C011.initial 151) (congrArg (Sign.withNegation globalNegation) hnode151) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C011.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C011.initial 153) (congrArg (Sign.withNegation globalNegation) hnode153) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (domain_from_eq (domain := Cases.C011.initial 154) (congrArg (Sign.withNegation globalNegation) hnode154) (Eq.refl Bool.true))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C011.initial 155) (congrArg (Sign.withNegation globalNegation) (h_zero 11 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C011.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C011.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C011.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C011.initial 159) (congrArg (Sign.withNegation globalNegation) (h_zero 12 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C011.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (top_allows (Sign.withNegation globalNegation (assignment 161)))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Cases.C011.initial 162) (congrArg (Sign.withNegation globalNegation) hnode162) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C011.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C011.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C011.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C011.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (top_allows (Sign.withNegation globalNegation (assignment 167)))
  let bounded169 := below_succ bounded168 (domain_from_eq (domain := Cases.C011.initial 168) (congrArg (Sign.withNegation globalNegation) hnode168) (Eq.refl Bool.true))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C011.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C011.initial 170) (congrArg (Sign.withNegation globalNegation) hnode170) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C011.initial 171) (congrArg (Sign.withNegation globalNegation) hnode171) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C011.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C011.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C011.initial 174) (congrArg (Sign.withNegation globalNegation) hnode174) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C011.initial 175) (congrArg (Sign.withNegation globalNegation) hnode175) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C011.initial 176) (congrArg (Sign.withNegation globalNegation) (h_zero 13 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (top_allows (Sign.withNegation globalNegation (assignment 177)))
  let bounded179 := below_succ bounded178 (top_allows (Sign.withNegation globalNegation (assignment 178)))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C011.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C011.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (top_allows (Sign.withNegation globalNegation (assignment 181)))
  let bounded183 := below_succ bounded182 (top_allows (Sign.withNegation globalNegation (assignment 182)))
  let bounded184 := below_succ bounded183 (top_allows (Sign.withNegation globalNegation (assignment 183)))
  let bounded185 := below_succ bounded184 (top_allows (Sign.withNegation globalNegation (assignment 184)))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C011.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Cases.C011.initial 186) (congrArg (Sign.withNegation globalNegation) hnode186) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (top_allows (Sign.withNegation globalNegation (assignment 187)))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C011.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C011.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (top_allows (Sign.withNegation globalNegation (assignment 190)))
  let bounded192 := below_succ bounded191 (top_allows (Sign.withNegation globalNegation (assignment 191)))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C011.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C011.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Cases.C011.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C011.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (top_allows (Sign.withNegation globalNegation (assignment 196)))
  let bounded198 := below_succ bounded197 (domain_from_eq (domain := Cases.C011.initial 197) (congrArg (Sign.withNegation globalNegation) hnode197) (Eq.refl Bool.true))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Cases.C011.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (top_allows (Sign.withNegation globalNegation (assignment 199)))
  let bounded201 := below_succ bounded200 (domain_from_eq (domain := Cases.C011.initial 200) (congrArg (Sign.withNegation globalNegation) hnode200) (Eq.refl Bool.true))
  let bounded202 := below_succ bounded201 (domain_from_eq (domain := Cases.C011.initial 201) (congrArg (Sign.withNegation globalNegation) hnode201) (Eq.refl Bool.true))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C011.initial 202) (congrArg (Sign.withNegation globalNegation) hnode202) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (domain_from_eq (domain := Cases.C011.initial 203) (congrArg (Sign.withNegation globalNegation) hnode203) (Eq.refl Bool.true))
  let bounded205 := below_succ bounded204 (domain_from_eq (domain := Cases.C011.initial 204) (congrArg (Sign.withNegation globalNegation) hnode204) (Eq.refl Bool.true))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C011.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (top_allows (Sign.withNegation globalNegation (assignment 206)))
  let bounded208 := below_succ bounded207 (top_allows (Sign.withNegation globalNegation (assignment 207)))
  let bounded209 := below_succ bounded208 (top_allows (Sign.withNegation globalNegation (assignment 208)))
  let bounded210 := below_succ bounded209 (top_allows (Sign.withNegation globalNegation (assignment 209)))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C011.initial 210) (congrArg (Sign.withNegation globalNegation) hnode210) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C011.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (top_allows (Sign.withNegation globalNegation (assignment 212)))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C011.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C011.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (top_allows (Sign.withNegation globalNegation (assignment 215)))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C011.initial 216) (congrArg (Sign.withNegation globalNegation) hnode216) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C011.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C011.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (top_allows (Sign.withNegation globalNegation (assignment 219)))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C011.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (top_allows (Sign.withNegation globalNegation (assignment 221)))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C011.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C011.initial 223) (congrArg (Sign.withNegation globalNegation) (h_zero 14 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C011.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C011.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (top_allows (Sign.withNegation globalNegation (assignment 226)))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C011.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C011.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Cases.C011.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C011.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (domain_from_eq (domain := Cases.C011.initial 231) (congrArg (Sign.withNegation globalNegation) hnode231) (Eq.refl Bool.true))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C011.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (top_allows (Sign.withNegation globalNegation (assignment 233)))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C011.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (top_allows (Sign.withNegation globalNegation (assignment 235)))
  let bounded237 := below_succ bounded236 (domain_from_eq (domain := Cases.C011.initial 236) (congrArg (Sign.withNegation globalNegation) hnode236) (Eq.refl Bool.true))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C011.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C011.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (top_allows (Sign.withNegation globalNegation (assignment 239)))
  let bounded241 := below_succ bounded240 (top_allows (Sign.withNegation globalNegation (assignment 240)))
  let bounded242 := below_succ bounded241 (top_allows (Sign.withNegation globalNegation (assignment 241)))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C011.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C011.initial 243) (congrArg (Sign.withNegation globalNegation) hnode243) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C011.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (top_allows (Sign.withNegation globalNegation (assignment 245)))
  let bounded247 := below_succ bounded246 (top_allows (Sign.withNegation globalNegation (assignment 246)))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C011.initial 247) (congrArg (Sign.withNegation globalNegation) hnode247) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C011.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (top_allows (Sign.withNegation globalNegation (assignment 249)))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Cases.C011.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C011.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C011.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C011
#print axioms Papers.RationalityTen.PureGP.Initializers.C011.support_sign_contradiction
