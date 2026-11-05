module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C022

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C022
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 0
def globalNegation : Bool := Bool.true
def edgeTable : Table SupportEdge := (Table.node 110 (Table.node 55 (Table.node 27 (Table.node 13 (Table.node 6 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 0 21 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 0 22 Bool.false)) (Table.leaf (SupportEdge.mk 0 23 Bool.false)))) (Table.node 4 (Table.leaf (SupportEdge.mk 0 24 Bool.false)) (Table.node 5 (Table.leaf (SupportEdge.mk 5 29 Bool.true)) (Table.leaf (SupportEdge.mk 5 32 Bool.true))))) (Table.node 9 (Table.node 7 (Table.leaf (SupportEdge.mk 5 34 Bool.true)) (Table.node 8 (Table.leaf (SupportEdge.mk 5 35 Bool.true)) (Table.leaf (SupportEdge.mk 10 39 Bool.true)))) (Table.node 11 (Table.node 10 (Table.leaf (SupportEdge.mk 10 42 Bool.true)) (Table.leaf (SupportEdge.mk 10 44 Bool.true))) (Table.node 12 (Table.leaf (SupportEdge.mk 10 45 Bool.true)) (Table.leaf (SupportEdge.mk 60 94 Bool.false)))))) (Table.node 20 (Table.node 16 (Table.node 14 (Table.leaf (SupportEdge.mk 60 97 Bool.false)) (Table.node 15 (Table.leaf (SupportEdge.mk 60 99 Bool.false)) (Table.leaf (SupportEdge.mk 60 100 Bool.false)))) (Table.node 18 (Table.node 17 (Table.leaf (SupportEdge.mk 130 164 Bool.false)) (Table.leaf (SupportEdge.mk 130 167 Bool.false))) (Table.node 19 (Table.leaf (SupportEdge.mk 130 169 Bool.false)) (Table.leaf (SupportEdge.mk 130 170 Bool.false))))) (Table.node 23 (Table.node 21 (Table.leaf (SupportEdge.mk 1 56 Bool.false)) (Table.node 22 (Table.leaf (SupportEdge.mk 1 61 Bool.true)) (Table.leaf (SupportEdge.mk 1 62 Bool.true)))) (Table.node 25 (Table.node 24 (Table.leaf (SupportEdge.mk 1 63 Bool.true)) (Table.leaf (SupportEdge.mk 5 60 Bool.false))) (Table.node 26 (Table.leaf (SupportEdge.mk 5 67 Bool.false)) (Table.leaf (SupportEdge.mk 5 69 Bool.false))))))) (Table.node 41 (Table.node 34 (Table.node 30 (Table.node 28 (Table.leaf (SupportEdge.mk 5 70 Bool.false)) (Table.node 29 (Table.leaf (SupportEdge.mk 14 74 Bool.true)) (Table.leaf (SupportEdge.mk 14 83 Bool.false)))) (Table.node 32 (Table.node 31 (Table.leaf (SupportEdge.mk 14 85 Bool.false)) (Table.leaf (SupportEdge.mk 14 86 Bool.false))) (Table.node 33 (Table.leaf (SupportEdge.mk 29 94 Bool.true)) (Table.leaf (SupportEdge.mk 29 103 Bool.false))))) (Table.node 37 (Table.node 35 (Table.leaf (SupportEdge.mk 29 105 Bool.false)) (Table.node 36 (Table.leaf (SupportEdge.mk 29 106 Bool.false)) (Table.leaf (SupportEdge.mk 134 199 Bool.false)))) (Table.node 39 (Table.node 38 (Table.leaf (SupportEdge.mk 134 208 Bool.true)) (Table.leaf (SupportEdge.mk 134 210 Bool.true))) (Table.node 40 (Table.leaf (SupportEdge.mk 134 211 Bool.true)) (Table.leaf (SupportEdge.mk 24 59 Bool.false)))))) (Table.node 48 (Table.node 44 (Table.node 42 (Table.leaf (SupportEdge.mk 24 93 Bool.false)) (Table.node 43 (Table.leaf (SupportEdge.mk 24 96 Bool.false)) (Table.leaf (SupportEdge.mk 24 98 Bool.false)))) (Table.node 46 (Table.node 45 (Table.leaf (SupportEdge.mk 24 100 Bool.true)) (Table.leaf (SupportEdge.mk 27 62 Bool.false))) (Table.node 47 (Table.leaf (SupportEdge.mk 27 92 Bool.true)) (Table.leaf (SupportEdge.mk 27 101 Bool.false))))) (Table.node 51 (Table.node 49 (Table.leaf (SupportEdge.mk 27 105 Bool.true)) (Table.node 50 (Table.leaf (SupportEdge.mk 28 63 Bool.false)) (Table.leaf (SupportEdge.mk 28 93 Bool.true)))) (Table.node 53 (Table.node 52 (Table.leaf (SupportEdge.mk 28 102 Bool.false)) (Table.leaf (SupportEdge.mk 28 106 Bool.true))) (Table.node 54 (Table.leaf (SupportEdge.mk 33 68 Bool.false)) (Table.leaf (SupportEdge.mk 33 98 Bool.true)))))))) (Table.node 82 (Table.node 68 (Table.node 61 (Table.node 58 (Table.node 56 (Table.leaf (SupportEdge.mk 33 107 Bool.true)) (Table.node 57 (Table.leaf (SupportEdge.mk 33 110 Bool.true)) (Table.leaf (SupportEdge.mk 49 84 Bool.false)))) (Table.node 59 (Table.leaf (SupportEdge.mk 49 114 Bool.false)) (Table.node 60 (Table.leaf (SupportEdge.mk 49 121 Bool.true)) (Table.leaf (SupportEdge.mk 49 124 Bool.true))))) (Table.node 64 (Table.node 62 (Table.leaf (SupportEdge.mk 174 209 Bool.false)) (Table.node 63 (Table.leaf (SupportEdge.mk 174 234 Bool.true)) (Table.leaf (SupportEdge.mk 174 241 Bool.false)))) (Table.node 66 (Table.node 65 (Table.leaf (SupportEdge.mk 174 244 Bool.false)) (Table.leaf (SupportEdge.mk 37 72 Bool.false))) (Table.node 67 (Table.leaf (SupportEdge.mk 37 92 Bool.false)) (Table.leaf (SupportEdge.mk 37 111 Bool.false)))))) (Table.node 75 (Table.node 71 (Table.node 69 (Table.leaf (SupportEdge.mk 37 114 Bool.true)) (Table.node 70 (Table.leaf (SupportEdge.mk 39 74 Bool.false)) (Table.leaf (SupportEdge.mk 39 94 Bool.false)))) (Table.node 73 (Table.node 72 (Table.leaf (SupportEdge.mk 39 113 Bool.false)) (Table.leaf (SupportEdge.mk 39 116 Bool.false))) (Table.node 74 (Table.leaf (SupportEdge.mk 44 79 Bool.false)) (Table.leaf (SupportEdge.mk 44 99 Bool.false))))) (Table.node 78 (Table.node 76 (Table.leaf (SupportEdge.mk 44 118 Bool.true)) (Table.node 77 (Table.leaf (SupportEdge.mk 44 120 Bool.false)) (Table.leaf (SupportEdge.mk 50 85 Bool.false)))) (Table.node 80 (Table.node 79 (Table.leaf (SupportEdge.mk 50 105 Bool.false)) (Table.leaf (SupportEdge.mk 50 122 Bool.true))) (Table.node 81 (Table.leaf (SupportEdge.mk 50 124 Bool.false)) (Table.leaf (SupportEdge.mk 185 220 Bool.false))))))) (Table.node 96 (Table.node 89 (Table.node 85 (Table.node 83 (Table.leaf (SupportEdge.mk 185 235 Bool.false)) (Table.node 84 (Table.leaf (SupportEdge.mk 185 247 Bool.false)) (Table.leaf (SupportEdge.mk 185 249 Bool.true)))) (Table.node 87 (Table.node 86 (Table.leaf (SupportEdge.mk 40 75 Bool.false)) (Table.leaf (SupportEdge.mk 40 95 Bool.false))) (Table.node 88 (Table.leaf (SupportEdge.mk 40 111 Bool.true)) (Table.leaf (SupportEdge.mk 40 118 Bool.true))))) (Table.node 92 (Table.node 90 (Table.leaf (SupportEdge.mk 41 76 Bool.false)) (Table.node 91 (Table.leaf (SupportEdge.mk 41 96 Bool.false)) (Table.leaf (SupportEdge.mk 41 112 Bool.true)))) (Table.node 94 (Table.node 93 (Table.leaf (SupportEdge.mk 41 119 Bool.true)) (Table.leaf (SupportEdge.mk 43 78 Bool.false))) (Table.node 95 (Table.leaf (SupportEdge.mk 43 98 Bool.false)) (Table.leaf (SupportEdge.mk 43 114 Bool.true)))))) (Table.node 103 (Table.node 99 (Table.node 97 (Table.leaf (SupportEdge.mk 43 120 Bool.true)) (Table.node 98 (Table.leaf (SupportEdge.mk 52 87 Bool.false)) (Table.leaf (SupportEdge.mk 52 107 Bool.false)))) (Table.node 101 (Table.node 100 (Table.leaf (SupportEdge.mk 52 121 Bool.false)) (Table.leaf (SupportEdge.mk 52 125 Bool.true))) (Table.node 102 (Table.leaf (SupportEdge.mk 187 222 Bool.false)) (Table.leaf (SupportEdge.mk 187 237 Bool.false))))) (Table.node 106 (Table.node 104 (Table.leaf (SupportEdge.mk 187 246 Bool.true)) (Table.node 105 (Table.leaf (SupportEdge.mk 187 250 Bool.false)) (Table.leaf (SupportEdge.mk 1 126 Bool.true)))) (Table.node 108 (Table.node 107 (Table.leaf (SupportEdge.mk 1 131 Bool.false)) (Table.leaf (SupportEdge.mk 1 132 Bool.false))) (Table.node 109 (Table.leaf (SupportEdge.mk 1 134 Bool.false)) (Table.leaf (SupportEdge.mk 4 129 Bool.true))))))))) (Table.node 165 (Table.node 137 (Table.node 123 (Table.node 116 (Table.node 113 (Table.node 111 (Table.leaf (SupportEdge.mk 4 136 Bool.true)) (Table.node 112 (Table.leaf (SupportEdge.mk 4 138 Bool.true)) (Table.leaf (SupportEdge.mk 4 140 Bool.false)))) (Table.node 114 (Table.leaf (SupportEdge.mk 13 143 Bool.false)) (Table.node 115 (Table.leaf (SupportEdge.mk 13 152 Bool.true)) (Table.leaf (SupportEdge.mk 13 154 Bool.true))))) (Table.node 119 (Table.node 117 (Table.leaf (SupportEdge.mk 13 156 Bool.false)) (Table.node 118 (Table.leaf (SupportEdge.mk 28 163 Bool.false)) (Table.leaf (SupportEdge.mk 28 172 Bool.true)))) (Table.node 121 (Table.node 120 (Table.leaf (SupportEdge.mk 28 174 Bool.true)) (Table.leaf (SupportEdge.mk 28 176 Bool.false))) (Table.node 122 (Table.leaf (SupportEdge.mk 63 198 Bool.false)) (Table.leaf (SupportEdge.mk 63 207 Bool.true)))))) (Table.node 130 (Table.node 126 (Table.node 124 (Table.leaf (SupportEdge.mk 63 209 Bool.true)) (Table.node 125 (Table.leaf (SupportEdge.mk 63 211 Bool.false)) (Table.leaf (SupportEdge.mk 2 127 Bool.true)))) (Table.node 128 (Table.node 127 (Table.leaf (SupportEdge.mk 2 131 Bool.true)) (Table.leaf (SupportEdge.mk 2 135 Bool.false))) (Table.node 129 (Table.leaf (SupportEdge.mk 2 136 Bool.false)) (Table.leaf (SupportEdge.mk 5 130 Bool.true))))) (Table.node 133 (Table.node 131 (Table.leaf (SupportEdge.mk 5 134 Bool.true)) (Table.node 132 (Table.leaf (SupportEdge.mk 5 139 Bool.true)) (Table.leaf (SupportEdge.mk 5 140 Bool.true)))) (Table.node 135 (Table.node 134 (Table.leaf (SupportEdge.mk 17 147 Bool.false)) (Table.leaf (SupportEdge.mk 17 153 Bool.false))) (Table.node 136 (Table.leaf (SupportEdge.mk 17 158 Bool.true)) (Table.leaf (SupportEdge.mk 17 159 Bool.true))))))) (Table.node 151 (Table.node 144 (Table.node 140 (Table.node 138 (Table.leaf (SupportEdge.mk 32 167 Bool.false)) (Table.node 139 (Table.leaf (SupportEdge.mk 32 173 Bool.false)) (Table.leaf (SupportEdge.mk 32 178 Bool.true)))) (Table.node 142 (Table.node 141 (Table.leaf (SupportEdge.mk 32 179 Bool.true)) (Table.leaf (SupportEdge.mk 67 202 Bool.false))) (Table.node 143 (Table.leaf (SupportEdge.mk 67 208 Bool.false)) (Table.leaf (SupportEdge.mk 67 213 Bool.true))))) (Table.node 147 (Table.node 145 (Table.leaf (SupportEdge.mk 67 214 Bool.true)) (Table.node 146 (Table.leaf (SupportEdge.mk 7 127 Bool.false)) (Table.leaf (SupportEdge.mk 7 141 Bool.true)))) (Table.node 149 (Table.node 148 (Table.leaf (SupportEdge.mk 7 145 Bool.false)) (Table.leaf (SupportEdge.mk 7 147 Bool.false))) (Table.node 150 (Table.leaf (SupportEdge.mk 9 129 Bool.false)) (Table.leaf (SupportEdge.mk 9 143 Bool.true)))))) (Table.node 158 (Table.node 154 (Table.node 152 (Table.leaf (SupportEdge.mk 9 148 Bool.true)) (Table.node 153 (Table.leaf (SupportEdge.mk 9 150 Bool.false)) (Table.leaf (SupportEdge.mk 16 136 Bool.false)))) (Table.node 156 (Table.node 155 (Table.leaf (SupportEdge.mk 16 152 Bool.false)) (Table.leaf (SupportEdge.mk 16 157 Bool.true))) (Table.node 157 (Table.leaf (SupportEdge.mk 16 159 Bool.false)) (Table.leaf (SupportEdge.mk 41 166 Bool.true))))) (Table.node 161 (Table.node 159 (Table.leaf (SupportEdge.mk 41 182 Bool.false)) (Table.node 160 (Table.leaf (SupportEdge.mk 41 187 Bool.true)) (Table.leaf (SupportEdge.mk 41 189 Bool.false)))) (Table.node 163 (Table.node 162 (Table.leaf (SupportEdge.mk 76 201 Bool.true)) (Table.leaf (SupportEdge.mk 76 217 Bool.false))) (Table.node 164 (Table.leaf (SupportEdge.mk 76 222 Bool.true)) (Table.leaf (SupportEdge.mk 76 224 Bool.false)))))))) (Table.node 192 (Table.node 178 (Table.node 171 (Table.node 168 (Table.node 166 (Table.leaf (SupportEdge.mk 24 129 Bool.true)) (Table.node 167 (Table.leaf (SupportEdge.mk 24 163 Bool.true)) (Table.leaf (SupportEdge.mk 24 166 Bool.true)))) (Table.node 169 (Table.leaf (SupportEdge.mk 24 168 Bool.true)) (Table.node 170 (Table.leaf (SupportEdge.mk 24 170 Bool.false)) (Table.leaf (SupportEdge.mk 40 145 Bool.true))))) (Table.node 174 (Table.node 172 (Table.leaf (SupportEdge.mk 40 165 Bool.true)) (Table.node 173 (Table.leaf (SupportEdge.mk 40 181 Bool.false)) (Table.leaf (SupportEdge.mk 40 187 Bool.false)))) (Table.node 176 (Table.node 175 (Table.leaf (SupportEdge.mk 42 147 Bool.true)) (Table.leaf (SupportEdge.mk 42 167 Bool.true))) (Table.node 177 (Table.leaf (SupportEdge.mk 42 183 Bool.false)) (Table.leaf (SupportEdge.mk 42 189 Bool.true)))))) (Table.node 185 (Table.node 181 (Table.node 179 (Table.leaf (SupportEdge.mk 44 149 Bool.true)) (Table.node 180 (Table.leaf (SupportEdge.mk 44 169 Bool.true)) (Table.leaf (SupportEdge.mk 44 185 Bool.false)))) (Table.node 183 (Table.node 182 (Table.leaf (SupportEdge.mk 44 190 Bool.true)) (Table.leaf (SupportEdge.mk 53 158 Bool.true))) (Table.node 184 (Table.leaf (SupportEdge.mk 53 178 Bool.true)) (Table.leaf (SupportEdge.mk 53 192 Bool.true))))) (Table.node 188 (Table.node 186 (Table.leaf (SupportEdge.mk 53 195 Bool.true)) (Table.node 187 (Table.leaf (SupportEdge.mk 118 223 Bool.false)) (Table.leaf (SupportEdge.mk 118 238 Bool.false)))) (Table.node 190 (Table.node 189 (Table.leaf (SupportEdge.mk 118 247 Bool.true)) (Table.leaf (SupportEdge.mk 118 250 Bool.true))) (Table.node 191 (Table.leaf (SupportEdge.mk 82 152 Bool.false)) (Table.leaf (SupportEdge.mk 82 207 Bool.true))))))) (Table.node 206 (Table.node 199 (Table.node 195 (Table.node 193 (Table.leaf (SupportEdge.mk 82 217 Bool.true)) (Table.node 194 (Table.leaf (SupportEdge.mk 82 226 Bool.true)) (Table.leaf (SupportEdge.mk 82 228 Bool.false)))) (Table.node 197 (Table.node 196 (Table.leaf (SupportEdge.mk 83 153 Bool.false)) (Table.leaf (SupportEdge.mk 83 208 Bool.true))) (Table.node 198 (Table.leaf (SupportEdge.mk 83 218 Bool.true)) (Table.leaf (SupportEdge.mk 83 227 Bool.true))))) (Table.node 202 (Table.node 200 (Table.leaf (SupportEdge.mk 83 228 Bool.true)) (Table.node 201 (Table.leaf (SupportEdge.mk 121 191 Bool.false)) (Table.leaf (SupportEdge.mk 121 226 Bool.false)))) (Table.node 204 (Table.node 203 (Table.leaf (SupportEdge.mk 121 241 Bool.false)) (Table.leaf (SupportEdge.mk 121 246 Bool.false))) (Table.node 205 (Table.leaf (SupportEdge.mk 122 192 Bool.false)) (Table.leaf (SupportEdge.mk 122 227 Bool.false)))))) (Table.node 213 (Table.node 209 (Table.node 207 (Table.leaf (SupportEdge.mk 122 242 Bool.false)) (Table.node 208 (Table.leaf (SupportEdge.mk 122 247 Bool.false)) (Table.leaf (SupportEdge.mk 123 193 Bool.false)))) (Table.node 211 (Table.node 210 (Table.leaf (SupportEdge.mk 123 228 Bool.false)) (Table.leaf (SupportEdge.mk 123 243 Bool.false))) (Table.node 212 (Table.leaf (SupportEdge.mk 123 248 Bool.false)) (Table.leaf (SupportEdge.mk 124 194 Bool.false))))) (Table.node 216 (Table.node 214 (Table.leaf (SupportEdge.mk 124 229 Bool.false)) (Table.node 215 (Table.leaf (SupportEdge.mk 124 244 Bool.false)) (Table.leaf (SupportEdge.mk 124 249 Bool.false)))) (Table.node 218 (Table.node 217 (Table.leaf (SupportEdge.mk 125 195 Bool.false)) (Table.leaf (SupportEdge.mk 125 230 Bool.false))) (Table.node 219 (Table.leaf (SupportEdge.mk 125 245 Bool.false)) (Table.leaf (SupportEdge.mk 125 250 Bool.false))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 5 (Table.node 2 (Table.node 1 (Table.leaf 25) (Table.leaf 64)) (Table.node 3 (Table.leaf 104) (Table.node 4 (Table.leaf 115) (Table.leaf 117)))) (Table.node 7 (Table.node 6 (Table.leaf 133) (Table.leaf 137)) (Table.node 8 (Table.leaf 146) (Table.node 9 (Table.leaf 188) (Table.leaf 251)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 220 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 10 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C022.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode21 : Eq (assignment 21) Sign.positive :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode22 : Eq (assignment 22) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode23 : Eq (assignment 23) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode24 : Eq (assignment 24) Sign.positive :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode59 : Eq (assignment 59) Sign.positive :=
    Eq.trans (h_support 40 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode24)
  let hnode93 : Eq (assignment 93) Sign.positive :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode24)
  let hnode96 : Eq (assignment 96) Sign.positive :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode24)
  let hnode98 : Eq (assignment 98) Sign.positive :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode24)
  let hnode100 : Eq (assignment 100) Sign.negative :=
    Eq.trans (h_support 44 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode129 : Eq (assignment 129) Sign.negative :=
    Eq.trans (h_support 165 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode163 : Eq (assignment 163) Sign.negative :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode166 : Eq (assignment 166) Sign.negative :=
    Eq.trans (h_support 167 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode168 : Eq (assignment 168) Sign.negative :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode170 : Eq (assignment 170) Sign.positive :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode24)
  let hnode4 : Eq (assignment 4) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 109 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode129)
  let hnode9 : Eq (assignment 9) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 149 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode129)
  let hnode28 : Eq (assignment 28) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 50 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode93)
  let hnode33 : Eq (assignment 33) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 54 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode98)
  let hnode41 : Eq (assignment 41) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 90 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode96)
  let hnode43 : Eq (assignment 43) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 94 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode98)
  let hnode60 : Eq (assignment 60) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 15 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode100)
  let hnode130 : Eq (assignment 130) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 19 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode170)
  let hnode5 : Eq (assignment 5) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 24 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode60)
  let hnode63 : Eq (assignment 63) Sign.negative :=
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode68 : Eq (assignment 68) Sign.negative :=
    Eq.trans (h_support 53 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode76 : Eq (assignment 76) Sign.positive :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode78 : Eq (assignment 78) Sign.positive :=
    Eq.trans (h_support 93 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode94 : Eq (assignment 94) Sign.negative :=
    Eq.trans (h_support 12 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode60)
  let hnode97 : Eq (assignment 97) Sign.negative :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode60)
  let hnode99 : Eq (assignment 99) Sign.negative :=
    Eq.trans (h_support 14 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode60)
  let hnode102 : Eq (assignment 102) Sign.negative :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode106 : Eq (assignment 106) Sign.positive :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode107 : Eq (assignment 107) Sign.positive :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode110 : Eq (assignment 110) Sign.positive :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode112 : Eq (assignment 112) Sign.negative :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode114 : Eq (assignment 114) Sign.negative :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode119 : Eq (assignment 119) Sign.negative :=
    Eq.trans (h_support 92 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode120 : Eq (assignment 120) Sign.negative :=
    Eq.trans (h_support 96 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode136 : Eq (assignment 136) Sign.negative :=
    Eq.trans (h_support 110 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode138 : Eq (assignment 138) Sign.negative :=
    Eq.trans (h_support 111 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode140 : Eq (assignment 140) Sign.positive :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode143 : Eq (assignment 143) Sign.positive :=
    Eq.trans (h_support 150 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode148 : Eq (assignment 148) Sign.positive :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode150 : Eq (assignment 150) Sign.negative :=
    Eq.trans (h_support 152 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode164 : Eq (assignment 164) Sign.positive :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode130)
  let hnode167 : Eq (assignment 167) Sign.positive :=
    Eq.trans (h_support 17 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode130)
  let hnode169 : Eq (assignment 169) Sign.positive :=
    Eq.trans (h_support 18 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode130)
  let hnode172 : Eq (assignment 172) Sign.positive :=
    Eq.trans (h_support 118 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode174 : Eq (assignment 174) Sign.positive :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode176 : Eq (assignment 176) Sign.negative :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode182 : Eq (assignment 182) Sign.positive :=
    Eq.trans (h_support 158 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode187 : Eq (assignment 187) Sign.negative :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode189 : Eq (assignment 189) Sign.positive :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode1 : Eq (assignment 1) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 23 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode2 : Eq (assignment 2) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 128 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode136)
  let hnode13 : Eq (assignment 13) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 113 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode143)
  let hnode16 : Eq (assignment 16) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 153 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode136)
  let hnode29 : Eq (assignment 29) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 35 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode106)
  let hnode32 : Eq (assignment 32) Sign.positive :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode34 : Eq (assignment 34) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode35 : Eq (assignment 35) Sign.positive :=
    Eq.trans (h_support 7 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode37 : Eq (assignment 37) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 68 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode114)
  let hnode39 : Eq (assignment 39) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 70 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode94)
  let hnode40 : Eq (assignment 40) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 173 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode187)
  let hnode42 : Eq (assignment 42) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 177 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode189)
  let hnode44 : Eq (assignment 44) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 76 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode120)
  let hnode49 : Eq (assignment 49) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 58 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode114)
  let hnode52 : Eq (assignment 52) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 98 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode107)
  let hnode67 : Eq (assignment 67) Sign.negative :=
    Eq.trans (h_support 25 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode69 : Eq (assignment 69) Sign.negative :=
    Eq.trans (h_support 26 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode70 : Eq (assignment 70) Sign.negative :=
    Eq.trans (h_support 27 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode134 : Eq (assignment 134) Sign.positive :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode139 : Eq (assignment 139) Sign.positive :=
    Eq.trans (h_support 131 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode198 : Eq (assignment 198) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode63)
  let hnode201 : Eq (assignment 201) Sign.negative :=
    Eq.trans (h_support 161 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode76)
  let hnode207 : Eq (assignment 207) Sign.positive :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode209 : Eq (assignment 209) Sign.positive :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode211 : Eq (assignment 211) Sign.negative :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode63)
  let hnode217 : Eq (assignment 217) Sign.positive :=
    Eq.trans (h_support 162 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode76)
  let hnode222 : Eq (assignment 222) Sign.negative :=
    Eq.trans (h_support 163 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode76)
  let hnode224 : Eq (assignment 224) Sign.positive :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode76)
  let hnode234 : Eq (assignment 234) Sign.negative :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode174)
  let hnode237 : Eq (assignment 237) Sign.negative :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode187)
  let hnode241 : Eq (assignment 241) Sign.positive :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode174)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 64 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode174)
  let hnode246 : Eq (assignment 246) Sign.positive :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode187)
  let hnode250 : Eq (assignment 250) Sign.negative :=
    Eq.trans (h_support 104 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode187)
  let hnode10 : Eq (assignment 10) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 9 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode42)
  let hnode56 : Eq (assignment 56) Sign.positive :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode1)
  let hnode61 : Eq (assignment 61) Sign.negative :=
    Eq.trans (h_support 21 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode1)
  let hnode62 : Eq (assignment 62) Sign.negative :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode1)
  let hnode72 : Eq (assignment 72) Sign.positive :=
    Eq.trans (h_support 65 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode74 : Eq (assignment 74) Sign.negative :=
    Eq.trans (h_support 69 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode39)
  let hnode75 : Eq (assignment 75) Sign.negative :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode79 : Eq (assignment 79) Sign.negative :=
    Eq.trans (h_support 73 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode82 : Eq (assignment 82) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 191 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode207)
  let hnode84 : Eq (assignment 84) Sign.negative :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode49)
  let hnode87 : Eq (assignment 87) Sign.positive :=
    Eq.trans (h_support 97 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode52)
  let hnode92 : Eq (assignment 92) Sign.positive :=
    Eq.trans (h_support 66 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode95 : Eq (assignment 95) Sign.negative :=
    Eq.trans (h_support 86 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode103 : Eq (assignment 103) Sign.positive :=
    Eq.trans (h_support 33 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode105 : Eq (assignment 105) Sign.positive :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode111 : Eq (assignment 111) Sign.positive :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode113 : Eq (assignment 113) Sign.negative :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode39)
  let hnode116 : Eq (assignment 116) Sign.negative :=
    Eq.trans (h_support 72 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode39)
  let hnode118 : Eq (assignment 118) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 189 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode250)
  let hnode121 : Eq (assignment 121) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 202 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode241)
  let hnode124 : Eq (assignment 124) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 214 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode244)
  let hnode125 : Eq (assignment 125) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 219 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode250)
  let hnode126 : Eq (assignment 126) Sign.negative :=
    Eq.trans (h_support 105 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode1)
  let hnode127 : Eq (assignment 127) Sign.positive :=
    Eq.trans (h_support 125 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode2)
  let hnode131 : Eq (assignment 131) Sign.positive :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode1)
  let hnode132 : Eq (assignment 132) Sign.positive :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode1)
  let hnode135 : Eq (assignment 135) Sign.negative :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode2)
  let hnode145 : Eq (assignment 145) Sign.positive :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode147 : Eq (assignment 147) Sign.positive :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode42)
  let hnode149 : Eq (assignment 149) Sign.positive :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode152 : Eq (assignment 152) Sign.negative :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode154 : Eq (assignment 154) Sign.negative :=
    Eq.trans (h_support 115 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode156 : Eq (assignment 156) Sign.positive :=
    Eq.trans (h_support 116 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode157 : Eq (assignment 157) Sign.positive :=
    Eq.trans (h_support 155 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode16)
  let hnode159 : Eq (assignment 159) Sign.negative :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode165 : Eq (assignment 165) Sign.positive :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode173 : Eq (assignment 173) Sign.positive :=
    Eq.trans (h_support 138 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode178 : Eq (assignment 178) Sign.negative :=
    Eq.trans (h_support 139 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode181 : Eq (assignment 181) Sign.negative :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode183 : Eq (assignment 183) Sign.negative :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode42)
  let hnode185 : Eq (assignment 185) Sign.negative :=
    Eq.trans (h_support 180 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode190 : Eq (assignment 190) Sign.positive :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode199 : Eq (assignment 199) Sign.positive :=
    Eq.trans (h_support 36 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode134)
  let hnode202 : Eq (assignment 202) Sign.negative :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode67)
  let hnode208 : Eq (assignment 208) Sign.negative :=
    Eq.trans (h_support 142 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode67)
  let hnode210 : Eq (assignment 210) Sign.negative :=
    Eq.trans (h_support 38 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode134)
  let hnode213 : Eq (assignment 213) Sign.positive :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode67)
  let hnode214 : Eq (assignment 214) Sign.positive :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode67)
  let hnode7 : Eq (assignment 7) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 147 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode145)
  let hnode14 : Eq (assignment 14) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 28 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode17 : Eq (assignment 17) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 133 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode147)
  let hnode27 : Eq (assignment 27) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 45 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode62)
  let hnode45 : Eq (assignment 45) Sign.negative :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode50 : Eq (assignment 50) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 78 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode105)
  let hnode53 : Eq (assignment 53) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 183 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode178)
  let hnode83 : Eq (assignment 83) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 196 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode208)
  let hnode191 : Eq (assignment 191) Sign.positive :=
    Eq.trans (h_support 200 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode194 : Eq (assignment 194) Sign.positive :=
    Eq.trans (h_support 212 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode124)
  let hnode195 : Eq (assignment 195) Sign.negative :=
    Eq.trans (h_support 216 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode125)
  let hnode220 : Eq (assignment 220) Sign.negative :=
    Eq.trans (h_support 81 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode185)
  let hnode223 : Eq (assignment 223) Sign.positive :=
    Eq.trans (h_support 186 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode118)
  let hnode226 : Eq (assignment 226) Sign.positive :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode82)
  let hnode228 : Eq (assignment 228) Sign.negative :=
    Eq.trans (h_support 194 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode82)
  let hnode229 : Eq (assignment 229) Sign.positive :=
    Eq.trans (h_support 213 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode124)
  let hnode230 : Eq (assignment 230) Sign.negative :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode125)
  let hnode235 : Eq (assignment 235) Sign.negative :=
    Eq.trans (h_support 82 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode185)
  let hnode238 : Eq (assignment 238) Sign.positive :=
    Eq.trans (h_support 187 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode118)
  let hnode245 : Eq (assignment 245) Sign.negative :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode125)
  let hnode247 : Eq (assignment 247) Sign.negative :=
    Eq.trans (h_support 188 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode118)
  let hnode249 : Eq (assignment 249) Sign.positive :=
    Eq.trans (h_support 215 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode124)
  let hnode85 : Eq (assignment 85) Sign.positive :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode50)
  let hnode86 : Eq (assignment 86) Sign.positive :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode101 : Eq (assignment 101) Sign.negative :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode122 : Eq (assignment 122) Sign.negative :=
    Eq.trans (h_support 79 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode50)
  let hnode123 : Eq (assignment 123) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 209 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode228)
  let hnode141 : Eq (assignment 141) Sign.negative :=
    Eq.trans (h_support 146 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode7)
  let hnode153 : Eq (assignment 153) Sign.positive :=
    Eq.trans (h_support 134 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode158 : Eq (assignment 158) Sign.negative :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode192 : Eq (assignment 192) Sign.negative :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode218 : Eq (assignment 218) Sign.negative :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode227 : Eq (assignment 227) Sign.negative :=
    Eq.trans (h_support 198 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode193 : Eq (assignment 193) Sign.negative :=
    Eq.trans (h_support 208 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode123)
  let hnode242 : Eq (assignment 242) Sign.negative :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode122)
  let hnode243 : Eq (assignment 243) Sign.negative :=
    Eq.trans (h_support 210 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode123)
  let hnode248 : Eq (assignment 248) Sign.negative :=
    Eq.trans (h_support 211 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode123)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C022.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (domain_from_eq (domain := Cases.C022.initial 0) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded2 := below_succ bounded1 (domain_from_eq (domain := Cases.C022.initial 1) (congrArg (Sign.withNegation globalNegation) hnode1) (Eq.refl Bool.true))
  let bounded3 := below_succ bounded2 (domain_from_eq (domain := Cases.C022.initial 2) (congrArg (Sign.withNegation globalNegation) hnode2) (Eq.refl Bool.true))
  let bounded4 := below_succ bounded3 (top_allows (Sign.withNegation globalNegation (assignment 3)))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C022.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Cases.C022.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (top_allows (Sign.withNegation globalNegation (assignment 6)))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Cases.C022.initial 7) (congrArg (Sign.withNegation globalNegation) hnode7) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (top_allows (Sign.withNegation globalNegation (assignment 8)))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Cases.C022.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C022.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (top_allows (Sign.withNegation globalNegation (assignment 11)))
  let bounded13 := below_succ bounded12 (top_allows (Sign.withNegation globalNegation (assignment 12)))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C022.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C022.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (top_allows (Sign.withNegation globalNegation (assignment 15)))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Cases.C022.initial 16) (congrArg (Sign.withNegation globalNegation) hnode16) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C022.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (top_allows (Sign.withNegation globalNegation (assignment 18)))
  let bounded20 := below_succ bounded19 (top_allows (Sign.withNegation globalNegation (assignment 19)))
  let bounded21 := below_succ bounded20 (top_allows (Sign.withNegation globalNegation (assignment 20)))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C022.initial 21) (congrArg (Sign.withNegation globalNegation) hnode21) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (domain_from_eq (domain := Cases.C022.initial 22) (congrArg (Sign.withNegation globalNegation) hnode22) (Eq.refl Bool.true))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C022.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C022.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C022.initial 25) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (top_allows (Sign.withNegation globalNegation (assignment 26)))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C022.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C022.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C022.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (top_allows (Sign.withNegation globalNegation (assignment 30)))
  let bounded32 := below_succ bounded31 (top_allows (Sign.withNegation globalNegation (assignment 31)))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C022.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C022.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C022.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (domain_from_eq (domain := Cases.C022.initial 35) (congrArg (Sign.withNegation globalNegation) hnode35) (Eq.refl Bool.true))
  let bounded37 := below_succ bounded36 (top_allows (Sign.withNegation globalNegation (assignment 36)))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C022.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (top_allows (Sign.withNegation globalNegation (assignment 38)))
  let bounded40 := below_succ bounded39 (domain_from_eq (domain := Cases.C022.initial 39) (congrArg (Sign.withNegation globalNegation) hnode39) (Eq.refl Bool.true))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Cases.C022.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C022.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C022.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (domain_from_eq (domain := Cases.C022.initial 43) (congrArg (Sign.withNegation globalNegation) hnode43) (Eq.refl Bool.true))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Cases.C022.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C022.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (top_allows (Sign.withNegation globalNegation (assignment 46)))
  let bounded48 := below_succ bounded47 (top_allows (Sign.withNegation globalNegation (assignment 47)))
  let bounded49 := below_succ bounded48 (top_allows (Sign.withNegation globalNegation (assignment 48)))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C022.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (domain_from_eq (domain := Cases.C022.initial 50) (congrArg (Sign.withNegation globalNegation) hnode50) (Eq.refl Bool.true))
  let bounded52 := below_succ bounded51 (top_allows (Sign.withNegation globalNegation (assignment 51)))
  let bounded53 := below_succ bounded52 (domain_from_eq (domain := Cases.C022.initial 52) (congrArg (Sign.withNegation globalNegation) hnode52) (Eq.refl Bool.true))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Cases.C022.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (top_allows (Sign.withNegation globalNegation (assignment 54)))
  let bounded56 := below_succ bounded55 (top_allows (Sign.withNegation globalNegation (assignment 55)))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C022.initial 56) (congrArg (Sign.withNegation globalNegation) hnode56) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (top_allows (Sign.withNegation globalNegation (assignment 57)))
  let bounded59 := below_succ bounded58 (top_allows (Sign.withNegation globalNegation (assignment 58)))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C022.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C022.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Cases.C022.initial 61) (congrArg (Sign.withNegation globalNegation) hnode61) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C022.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C022.initial 63) (congrArg (Sign.withNegation globalNegation) hnode63) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C022.initial 64) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (top_allows (Sign.withNegation globalNegation (assignment 65)))
  let bounded67 := below_succ bounded66 (top_allows (Sign.withNegation globalNegation (assignment 66)))
  let bounded68 := below_succ bounded67 (domain_from_eq (domain := Cases.C022.initial 67) (congrArg (Sign.withNegation globalNegation) hnode67) (Eq.refl Bool.true))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C022.initial 68) (congrArg (Sign.withNegation globalNegation) hnode68) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C022.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C022.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (top_allows (Sign.withNegation globalNegation (assignment 71)))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C022.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (top_allows (Sign.withNegation globalNegation (assignment 73)))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C022.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Cases.C022.initial 75) (congrArg (Sign.withNegation globalNegation) hnode75) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Cases.C022.initial 76) (congrArg (Sign.withNegation globalNegation) hnode76) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (top_allows (Sign.withNegation globalNegation (assignment 77)))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C022.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C022.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (top_allows (Sign.withNegation globalNegation (assignment 80)))
  let bounded82 := below_succ bounded81 (top_allows (Sign.withNegation globalNegation (assignment 81)))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Cases.C022.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C022.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (domain_from_eq (domain := Cases.C022.initial 84) (congrArg (Sign.withNegation globalNegation) hnode84) (Eq.refl Bool.true))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C022.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C022.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C022.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (top_allows (Sign.withNegation globalNegation (assignment 88)))
  let bounded90 := below_succ bounded89 (top_allows (Sign.withNegation globalNegation (assignment 89)))
  let bounded91 := below_succ bounded90 (top_allows (Sign.withNegation globalNegation (assignment 90)))
  let bounded92 := below_succ bounded91 (top_allows (Sign.withNegation globalNegation (assignment 91)))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C022.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C022.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C022.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C022.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C022.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (domain_from_eq (domain := Cases.C022.initial 97) (congrArg (Sign.withNegation globalNegation) hnode97) (Eq.refl Bool.true))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C022.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C022.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C022.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C022.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C022.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C022.initial 103) (congrArg (Sign.withNegation globalNegation) hnode103) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C022.initial 104) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C022.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C022.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C022.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (top_allows (Sign.withNegation globalNegation (assignment 108)))
  let bounded110 := below_succ bounded109 (top_allows (Sign.withNegation globalNegation (assignment 109)))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C022.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C022.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C022.initial 112) (congrArg (Sign.withNegation globalNegation) hnode112) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C022.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C022.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C022.initial 115) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C022.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C022.initial 117) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C022.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C022.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C022.initial 120) (congrArg (Sign.withNegation globalNegation) hnode120) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C022.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C022.initial 122) (congrArg (Sign.withNegation globalNegation) hnode122) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C022.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C022.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Cases.C022.initial 125) (congrArg (Sign.withNegation globalNegation) hnode125) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (domain_from_eq (domain := Cases.C022.initial 126) (congrArg (Sign.withNegation globalNegation) hnode126) (Eq.refl Bool.true))
  let bounded128 := below_succ bounded127 (domain_from_eq (domain := Cases.C022.initial 127) (congrArg (Sign.withNegation globalNegation) hnode127) (Eq.refl Bool.true))
  let bounded129 := below_succ bounded128 (top_allows (Sign.withNegation globalNegation (assignment 128)))
  let bounded130 := below_succ bounded129 (domain_from_eq (domain := Cases.C022.initial 129) (congrArg (Sign.withNegation globalNegation) hnode129) (Eq.refl Bool.true))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C022.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C022.initial 131) (congrArg (Sign.withNegation globalNegation) hnode131) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C022.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C022.initial 133) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C022.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C022.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C022.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C022.initial 137) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C022.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C022.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C022.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C022.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (top_allows (Sign.withNegation globalNegation (assignment 142)))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C022.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (top_allows (Sign.withNegation globalNegation (assignment 144)))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C022.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C022.initial 146) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C022.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C022.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C022.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C022.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (top_allows (Sign.withNegation globalNegation (assignment 151)))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C022.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C022.initial 153) (congrArg (Sign.withNegation globalNegation) hnode153) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (domain_from_eq (domain := Cases.C022.initial 154) (congrArg (Sign.withNegation globalNegation) hnode154) (Eq.refl Bool.true))
  let bounded156 := below_succ bounded155 (top_allows (Sign.withNegation globalNegation (assignment 155)))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C022.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C022.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C022.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C022.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (top_allows (Sign.withNegation globalNegation (assignment 160)))
  let bounded162 := below_succ bounded161 (top_allows (Sign.withNegation globalNegation (assignment 161)))
  let bounded163 := below_succ bounded162 (top_allows (Sign.withNegation globalNegation (assignment 162)))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C022.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C022.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C022.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C022.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C022.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (domain_from_eq (domain := Cases.C022.initial 168) (congrArg (Sign.withNegation globalNegation) hnode168) (Eq.refl Bool.true))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C022.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C022.initial 170) (congrArg (Sign.withNegation globalNegation) hnode170) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (top_allows (Sign.withNegation globalNegation (assignment 171)))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C022.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C022.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C022.initial 174) (congrArg (Sign.withNegation globalNegation) hnode174) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (top_allows (Sign.withNegation globalNegation (assignment 175)))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C022.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (top_allows (Sign.withNegation globalNegation (assignment 177)))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C022.initial 178) (congrArg (Sign.withNegation globalNegation) hnode178) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C022.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (top_allows (Sign.withNegation globalNegation (assignment 180)))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C022.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C022.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C022.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (top_allows (Sign.withNegation globalNegation (assignment 184)))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C022.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (top_allows (Sign.withNegation globalNegation (assignment 186)))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C022.initial 187) (congrArg (Sign.withNegation globalNegation) hnode187) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C022.initial 188) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C022.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C022.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C022.initial 191) (congrArg (Sign.withNegation globalNegation) hnode191) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C022.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C022.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Cases.C022.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C022.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (top_allows (Sign.withNegation globalNegation (assignment 196)))
  let bounded198 := below_succ bounded197 (top_allows (Sign.withNegation globalNegation (assignment 197)))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Cases.C022.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (domain_from_eq (domain := Cases.C022.initial 199) (congrArg (Sign.withNegation globalNegation) hnode199) (Eq.refl Bool.true))
  let bounded201 := below_succ bounded200 (top_allows (Sign.withNegation globalNegation (assignment 200)))
  let bounded202 := below_succ bounded201 (domain_from_eq (domain := Cases.C022.initial 201) (congrArg (Sign.withNegation globalNegation) hnode201) (Eq.refl Bool.true))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C022.initial 202) (congrArg (Sign.withNegation globalNegation) hnode202) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (top_allows (Sign.withNegation globalNegation (assignment 203)))
  let bounded205 := below_succ bounded204 (top_allows (Sign.withNegation globalNegation (assignment 204)))
  let bounded206 := below_succ bounded205 (top_allows (Sign.withNegation globalNegation (assignment 205)))
  let bounded207 := below_succ bounded206 (top_allows (Sign.withNegation globalNegation (assignment 206)))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Cases.C022.initial 207) (congrArg (Sign.withNegation globalNegation) hnode207) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C022.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C022.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C022.initial 210) (congrArg (Sign.withNegation globalNegation) hnode210) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C022.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (top_allows (Sign.withNegation globalNegation (assignment 212)))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C022.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C022.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (top_allows (Sign.withNegation globalNegation (assignment 215)))
  let bounded217 := below_succ bounded216 (top_allows (Sign.withNegation globalNegation (assignment 216)))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C022.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C022.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (top_allows (Sign.withNegation globalNegation (assignment 219)))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C022.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (top_allows (Sign.withNegation globalNegation (assignment 221)))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C022.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C022.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C022.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (top_allows (Sign.withNegation globalNegation (assignment 225)))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C022.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C022.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C022.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Cases.C022.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C022.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (top_allows (Sign.withNegation globalNegation (assignment 231)))
  let bounded233 := below_succ bounded232 (top_allows (Sign.withNegation globalNegation (assignment 232)))
  let bounded234 := below_succ bounded233 (top_allows (Sign.withNegation globalNegation (assignment 233)))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C022.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C022.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (top_allows (Sign.withNegation globalNegation (assignment 236)))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C022.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C022.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (top_allows (Sign.withNegation globalNegation (assignment 239)))
  let bounded241 := below_succ bounded240 (top_allows (Sign.withNegation globalNegation (assignment 240)))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C022.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C022.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C022.initial 243) (congrArg (Sign.withNegation globalNegation) hnode243) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C022.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C022.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C022.initial 246) (congrArg (Sign.withNegation globalNegation) hnode246) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C022.initial 247) (congrArg (Sign.withNegation globalNegation) hnode247) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C022.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (domain_from_eq (domain := Cases.C022.initial 249) (congrArg (Sign.withNegation globalNegation) hnode249) (Eq.refl Bool.true))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Cases.C022.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C022.initial 251) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C022.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C022
#print axioms Papers.RationalityTen.PureGP.Initializers.C022.support_sign_contradiction
