module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C035

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C035
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 0
def globalNegation : Bool := Bool.false
def edgeTable : Table SupportEdge := (Table.node 112 (Table.node 56 (Table.node 28 (Table.node 14 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 0 21 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 0 22 Bool.false)) (Table.leaf (SupportEdge.mk 0 24 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 0 25 Bool.false)) (Table.leaf (SupportEdge.mk 3 27 Bool.true))) (Table.node 6 (Table.leaf (SupportEdge.mk 3 30 Bool.true)) (Table.leaf (SupportEdge.mk 3 33 Bool.false))))) (Table.node 10 (Table.node 8 (Table.leaf (SupportEdge.mk 3 34 Bool.false)) (Table.node 9 (Table.leaf (SupportEdge.mk 8 37 Bool.true)) (Table.leaf (SupportEdge.mk 8 40 Bool.true)))) (Table.node 12 (Table.node 11 (Table.leaf (SupportEdge.mk 8 43 Bool.false)) (Table.leaf (SupportEdge.mk 8 44 Bool.false))) (Table.node 13 (Table.leaf (SupportEdge.mk 58 92 Bool.false)) (Table.leaf (SupportEdge.mk 58 95 Bool.false)))))) (Table.node 21 (Table.node 17 (Table.node 15 (Table.leaf (SupportEdge.mk 58 98 Bool.true)) (Table.node 16 (Table.leaf (SupportEdge.mk 58 99 Bool.true)) (Table.leaf (SupportEdge.mk 128 162 Bool.false)))) (Table.node 19 (Table.node 18 (Table.leaf (SupportEdge.mk 128 165 Bool.false)) (Table.leaf (SupportEdge.mk 128 168 Bool.true))) (Table.node 20 (Table.leaf (SupportEdge.mk 128 169 Bool.true)) (Table.leaf (SupportEdge.mk 12 62 Bool.true))))) (Table.node 24 (Table.node 22 (Table.leaf (SupportEdge.mk 12 72 Bool.true)) (Table.node 23 (Table.leaf (SupportEdge.mk 12 81 Bool.false)) (Table.leaf (SupportEdge.mk 12 85 Bool.true)))) (Table.node 26 (Table.node 25 (Table.leaf (SupportEdge.mk 13 63 Bool.true)) (Table.leaf (SupportEdge.mk 13 73 Bool.true))) (Table.node 27 (Table.leaf (SupportEdge.mk 13 82 Bool.false)) (Table.leaf (SupportEdge.mk 13 86 Bool.true))))))) (Table.node 42 (Table.node 35 (Table.node 31 (Table.node 29 (Table.leaf (SupportEdge.mk 18 68 Bool.true)) (Table.node 30 (Table.leaf (SupportEdge.mk 18 78 Bool.true)) (Table.leaf (SupportEdge.mk 18 87 Bool.true)))) (Table.node 33 (Table.node 32 (Table.leaf (SupportEdge.mk 18 90 Bool.true)) (Table.leaf (SupportEdge.mk 49 104 Bool.false))) (Table.node 34 (Table.leaf (SupportEdge.mk 49 114 Bool.false)) (Table.leaf (SupportEdge.mk 49 121 Bool.true))))) (Table.node 38 (Table.node 36 (Table.leaf (SupportEdge.mk 49 124 Bool.true)) (Table.node 37 (Table.leaf (SupportEdge.mk 154 209 Bool.true)) (Table.leaf (SupportEdge.mk 154 219 Bool.true)))) (Table.node 40 (Table.node 39 (Table.leaf (SupportEdge.mk 154 226 Bool.false)) (Table.leaf (SupportEdge.mk 154 229 Bool.false))) (Table.node 41 (Table.leaf (SupportEdge.mk 22 57 Bool.false)) (Table.leaf (SupportEdge.mk 22 91 Bool.false)))))) (Table.node 49 (Table.node 45 (Table.node 43 (Table.leaf (SupportEdge.mk 22 95 Bool.true)) (Table.node 44 (Table.leaf (SupportEdge.mk 22 96 Bool.true)) (Table.leaf (SupportEdge.mk 25 60 Bool.false)))) (Table.node 47 (Table.node 46 (Table.leaf (SupportEdge.mk 25 94 Bool.false)) (Table.leaf (SupportEdge.mk 25 99 Bool.false))) (Table.node 48 (Table.leaf (SupportEdge.mk 25 100 Bool.false)) (Table.leaf (SupportEdge.mk 32 67 Bool.false))))) (Table.node 52 (Table.node 50 (Table.leaf (SupportEdge.mk 32 103 Bool.true)) (Table.node 51 (Table.leaf (SupportEdge.mk 32 108 Bool.false)) (Table.leaf (SupportEdge.mk 32 109 Bool.false)))) (Table.node 54 (Table.node 53 (Table.leaf (SupportEdge.mk 42 77 Bool.false)) (Table.leaf (SupportEdge.mk 42 113 Bool.true))) (Table.node 55 (Table.leaf (SupportEdge.mk 42 118 Bool.false)) (Table.leaf (SupportEdge.mk 42 119 Bool.false)))))))) (Table.node 84 (Table.node 70 (Table.node 63 (Table.node 59 (Table.node 57 (Table.leaf (SupportEdge.mk 167 202 Bool.false)) (Table.node 58 (Table.leaf (SupportEdge.mk 167 233 Bool.false)) (Table.leaf (SupportEdge.mk 167 238 Bool.true)))) (Table.node 61 (Table.node 60 (Table.leaf (SupportEdge.mk 167 239 Bool.true)) (Table.leaf (SupportEdge.mk 26 61 Bool.false))) (Table.node 62 (Table.leaf (SupportEdge.mk 26 91 Bool.true)) (Table.leaf (SupportEdge.mk 26 101 Bool.true))))) (Table.node 66 (Table.node 64 (Table.leaf (SupportEdge.mk 26 103 Bool.true)) (Table.node 65 (Table.leaf (SupportEdge.mk 28 63 Bool.false)) (Table.leaf (SupportEdge.mk 28 93 Bool.true)))) (Table.node 68 (Table.node 67 (Table.leaf (SupportEdge.mk 28 104 Bool.false)) (Table.leaf (SupportEdge.mk 28 106 Bool.true))) (Table.node 69 (Table.leaf (SupportEdge.mk 31 66 Bool.false)) (Table.leaf (SupportEdge.mk 31 96 Bool.true)))))) (Table.node 77 (Table.node 73 (Table.node 71 (Table.leaf (SupportEdge.mk 31 107 Bool.false)) (Table.node 72 (Table.leaf (SupportEdge.mk 31 109 Bool.true)) (Table.leaf (SupportEdge.mk 47 82 Bool.false)))) (Table.node 75 (Table.node 74 (Table.leaf (SupportEdge.mk 47 112 Bool.false)) (Table.leaf (SupportEdge.mk 47 121 Bool.false))) (Table.node 76 (Table.leaf (SupportEdge.mk 47 123 Bool.true)) (Table.leaf (SupportEdge.mk 172 207 Bool.false))))) (Table.node 80 (Table.node 78 (Table.leaf (SupportEdge.mk 172 232 Bool.true)) (Table.node 79 (Table.leaf (SupportEdge.mk 172 241 Bool.true)) (Table.leaf (SupportEdge.mk 172 243 Bool.false)))) (Table.node 82 (Table.node 81 (Table.leaf (SupportEdge.mk 33 68 Bool.false)) (Table.leaf (SupportEdge.mk 33 98 Bool.true))) (Table.node 83 (Table.leaf (SupportEdge.mk 33 104 Bool.true)) (Table.leaf (SupportEdge.mk 33 107 Bool.true))))))) (Table.node 98 (Table.node 91 (Table.node 87 (Table.node 85 (Table.leaf (SupportEdge.mk 33 110 Bool.true)) (Table.node 86 (Table.leaf (SupportEdge.mk 36 71 Bool.false)) (Table.leaf (SupportEdge.mk 36 91 Bool.false)))) (Table.node 89 (Table.node 88 (Table.leaf (SupportEdge.mk 36 112 Bool.true)) (Table.leaf (SupportEdge.mk 36 113 Bool.true))) (Table.node 90 (Table.leaf (SupportEdge.mk 37 72 Bool.false)) (Table.leaf (SupportEdge.mk 37 92 Bool.false))))) (Table.node 94 (Table.node 92 (Table.leaf (SupportEdge.mk 37 114 Bool.true)) (Table.node 93 (Table.leaf (SupportEdge.mk 37 115 Bool.true)) (Table.leaf (SupportEdge.mk 40 75 Bool.false)))) (Table.node 96 (Table.node 95 (Table.leaf (SupportEdge.mk 40 95 Bool.false)) (Table.leaf (SupportEdge.mk 40 117 Bool.true))) (Table.node 97 (Table.leaf (SupportEdge.mk 40 118 Bool.true)) (Table.leaf (SupportEdge.mk 46 81 Bool.false)))))) (Table.node 105 (Table.node 101 (Table.node 99 (Table.leaf (SupportEdge.mk 46 101 Bool.false)) (Table.node 100 (Table.leaf (SupportEdge.mk 46 121 Bool.true)) (Table.leaf (SupportEdge.mk 46 122 Bool.true)))) (Table.node 103 (Table.node 102 (Table.leaf (SupportEdge.mk 181 216 Bool.false)) (Table.leaf (SupportEdge.mk 181 231 Bool.false))) (Table.node 104 (Table.leaf (SupportEdge.mk 181 246 Bool.false)) (Table.leaf (SupportEdge.mk 181 247 Bool.false))))) (Table.node 108 (Table.node 106 (Table.leaf (SupportEdge.mk 3 128 Bool.true)) (Table.node 107 (Table.leaf (SupportEdge.mk 3 132 Bool.true)) (Table.leaf (SupportEdge.mk 3 135 Bool.true)))) (Table.node 110 (Table.node 109 (Table.leaf (SupportEdge.mk 3 139 Bool.false)) (Table.leaf (SupportEdge.mk 4 129 Bool.true))) (Table.node 111 (Table.leaf (SupportEdge.mk 4 133 Bool.true)) (Table.leaf (SupportEdge.mk 4 136 Bool.true))))))))) (Table.node 168 (Table.node 140 (Table.node 126 (Table.node 119 (Table.node 115 (Table.node 113 (Table.leaf (SupportEdge.mk 4 140 Bool.false)) (Table.node 114 (Table.leaf (SupportEdge.mk 18 148 Bool.false)) (Table.leaf (SupportEdge.mk 18 154 Bool.false)))) (Table.node 117 (Table.node 116 (Table.leaf (SupportEdge.mk 18 157 Bool.false)) (Table.leaf (SupportEdge.mk 18 160 Bool.false))) (Table.node 118 (Table.leaf (SupportEdge.mk 33 168 Bool.false)) (Table.leaf (SupportEdge.mk 33 174 Bool.false))))) (Table.node 122 (Table.node 120 (Table.leaf (SupportEdge.mk 33 177 Bool.false)) (Table.node 121 (Table.leaf (SupportEdge.mk 33 180 Bool.false)) (Table.leaf (SupportEdge.mk 68 203 Bool.false)))) (Table.node 124 (Table.node 123 (Table.leaf (SupportEdge.mk 68 209 Bool.false)) (Table.leaf (SupportEdge.mk 68 212 Bool.false))) (Table.node 125 (Table.leaf (SupportEdge.mk 68 215 Bool.false)) (Table.leaf (SupportEdge.mk 12 132 Bool.false)))))) (Table.node 133 (Table.node 129 (Table.node 127 (Table.leaf (SupportEdge.mk 12 142 Bool.false)) (Table.node 128 (Table.leaf (SupportEdge.mk 12 151 Bool.true)) (Table.leaf (SupportEdge.mk 12 154 Bool.false)))) (Table.node 131 (Table.node 130 (Table.leaf (SupportEdge.mk 14 134 Bool.false)) (Table.leaf (SupportEdge.mk 14 144 Bool.false))) (Table.node 132 (Table.leaf (SupportEdge.mk 14 153 Bool.true)) (Table.leaf (SupportEdge.mk 14 156 Bool.true))))) (Table.node 136 (Table.node 134 (Table.leaf (SupportEdge.mk 19 139 Bool.false)) (Table.node 135 (Table.leaf (SupportEdge.mk 19 149 Bool.false)) (Table.leaf (SupportEdge.mk 19 158 Bool.false)))) (Table.node 138 (Table.node 137 (Table.leaf (SupportEdge.mk 19 160 Bool.true)) (Table.leaf (SupportEdge.mk 50 175 Bool.true))) (Table.node 139 (Table.leaf (SupportEdge.mk 50 185 Bool.true)) (Table.leaf (SupportEdge.mk 50 192 Bool.false))))))) (Table.node 154 (Table.node 147 (Table.node 143 (Table.node 141 (Table.leaf (SupportEdge.mk 50 194 Bool.true)) (Table.node 142 (Table.leaf (SupportEdge.mk 85 210 Bool.true)) (Table.leaf (SupportEdge.mk 85 220 Bool.true)))) (Table.node 145 (Table.node 144 (Table.leaf (SupportEdge.mk 85 227 Bool.false)) (Table.leaf (SupportEdge.mk 85 229 Bool.true))) (Table.node 146 (Table.leaf (SupportEdge.mk 16 136 Bool.false)) (Table.leaf (SupportEdge.mk 16 146 Bool.false))))) (Table.node 150 (Table.node 148 (Table.leaf (SupportEdge.mk 16 152 Bool.false)) (Table.node 149 (Table.leaf (SupportEdge.mk 16 157 Bool.true)) (Table.leaf (SupportEdge.mk 17 137 Bool.false)))) (Table.node 152 (Table.node 151 (Table.leaf (SupportEdge.mk 17 147 Bool.false)) (Table.leaf (SupportEdge.mk 17 153 Bool.false))) (Table.node 153 (Table.leaf (SupportEdge.mk 17 158 Bool.true)) (Table.leaf (SupportEdge.mk 20 140 Bool.false)))))) (Table.node 161 (Table.node 157 (Table.node 155 (Table.leaf (SupportEdge.mk 20 150 Bool.false)) (Table.node 156 (Table.leaf (SupportEdge.mk 20 156 Bool.false)) (Table.leaf (SupportEdge.mk 20 160 Bool.false)))) (Table.node 159 (Table.node 158 (Table.leaf (SupportEdge.mk 54 179 Bool.true)) (Table.leaf (SupportEdge.mk 54 189 Bool.true))) (Table.node 160 (Table.leaf (SupportEdge.mk 54 193 Bool.true)) (Table.leaf (SupportEdge.mk 54 195 Bool.false))))) (Table.node 164 (Table.node 162 (Table.leaf (SupportEdge.mk 89 214 Bool.true)) (Table.node 163 (Table.leaf (SupportEdge.mk 89 224 Bool.true)) (Table.leaf (SupportEdge.mk 89 228 Bool.true)))) (Table.node 166 (Table.node 165 (Table.leaf (SupportEdge.mk 89 230 Bool.false)) (Table.leaf (SupportEdge.mk 24 129 Bool.true))) (Table.node 167 (Table.leaf (SupportEdge.mk 24 163 Bool.true)) (Table.leaf (SupportEdge.mk 24 166 Bool.true)))))))) (Table.node 196 (Table.node 182 (Table.node 175 (Table.node 171 (Table.node 169 (Table.leaf (SupportEdge.mk 24 168 Bool.true)) (Table.node 170 (Table.leaf (SupportEdge.mk 25 130 Bool.true)) (Table.leaf (SupportEdge.mk 25 164 Bool.true)))) (Table.node 173 (Table.node 172 (Table.leaf (SupportEdge.mk 25 167 Bool.true)) (Table.leaf (SupportEdge.mk 25 169 Bool.true))) (Table.node 174 (Table.leaf (SupportEdge.mk 35 140 Bool.true)) (Table.leaf (SupportEdge.mk 35 176 Bool.false))))) (Table.node 178 (Table.node 176 (Table.leaf (SupportEdge.mk 35 179 Bool.false)) (Table.node 177 (Table.leaf (SupportEdge.mk 35 180 Bool.false)) (Table.leaf (SupportEdge.mk 45 150 Bool.true)))) (Table.node 180 (Table.node 179 (Table.leaf (SupportEdge.mk 45 186 Bool.false)) (Table.leaf (SupportEdge.mk 45 189 Bool.false))) (Table.node 181 (Table.leaf (SupportEdge.mk 45 190 Bool.false)) (Table.leaf (SupportEdge.mk 100 205 Bool.false)))))) (Table.node 189 (Table.node 185 (Table.node 183 (Table.leaf (SupportEdge.mk 100 236 Bool.false)) (Table.node 184 (Table.leaf (SupportEdge.mk 100 239 Bool.false)) (Table.leaf (SupportEdge.mk 100 240 Bool.false)))) (Table.node 187 (Table.node 186 (Table.leaf (SupportEdge.mk 44 149 Bool.true)) (Table.leaf (SupportEdge.mk 44 169 Bool.true))) (Table.node 188 (Table.leaf (SupportEdge.mk 44 185 Bool.false)) (Table.leaf (SupportEdge.mk 44 188 Bool.false))))) (Table.node 192 (Table.node 190 (Table.leaf (SupportEdge.mk 44 190 Bool.true)) (Table.node 191 (Table.leaf (SupportEdge.mk 71 141 Bool.false)) (Table.leaf (SupportEdge.mk 71 196 Bool.true)))) (Table.node 194 (Table.node 193 (Table.leaf (SupportEdge.mk 71 216 Bool.false)) (Table.leaf (SupportEdge.mk 71 217 Bool.false))) (Table.node 195 (Table.leaf (SupportEdge.mk 74 144 Bool.false)) (Table.leaf (SupportEdge.mk 74 199 Bool.true))))))) (Table.node 210 (Table.node 203 (Table.node 199 (Table.node 197 (Table.leaf (SupportEdge.mk 74 220 Bool.true)) (Table.node 198 (Table.leaf (SupportEdge.mk 74 221 Bool.true)) (Table.leaf (SupportEdge.mk 77 147 Bool.false)))) (Table.node 201 (Table.node 200 (Table.leaf (SupportEdge.mk 77 202 Bool.true)) (Table.leaf (SupportEdge.mk 77 223 Bool.true))) (Table.node 202 (Table.leaf (SupportEdge.mk 77 224 Bool.true)) (Table.leaf (SupportEdge.mk 83 153 Bool.false))))) (Table.node 206 (Table.node 204 (Table.leaf (SupportEdge.mk 83 208 Bool.true)) (Table.node 205 (Table.leaf (SupportEdge.mk 83 227 Bool.true)) (Table.leaf (SupportEdge.mk 83 228 Bool.true)))) (Table.node 208 (Table.node 207 (Table.leaf (SupportEdge.mk 113 183 Bool.false)) (Table.leaf (SupportEdge.mk 113 233 Bool.false))) (Table.node 209 (Table.leaf (SupportEdge.mk 113 247 Bool.true)) (Table.leaf (SupportEdge.mk 113 248 Bool.true)))))) (Table.node 217 (Table.node 213 (Table.node 211 (Table.leaf (SupportEdge.mk 82 152 Bool.false)) (Table.node 212 (Table.leaf (SupportEdge.mk 82 207 Bool.true)) (Table.leaf (SupportEdge.mk 82 217 Bool.true)))) (Table.node 215 (Table.node 214 (Table.leaf (SupportEdge.mk 82 226 Bool.true)) (Table.leaf (SupportEdge.mk 82 228 Bool.false))) (Table.node 216 (Table.leaf (SupportEdge.mk 109 179 Bool.false)) (Table.leaf (SupportEdge.mk 109 214 Bool.false))))) (Table.node 221 (Table.node 219 (Table.node 218 (Table.leaf (SupportEdge.mk 109 239 Bool.true)) (Table.leaf (SupportEdge.mk 109 243 Bool.true))) (Table.node 220 (Table.leaf (SupportEdge.mk 109 245 Bool.false)) (Table.leaf (SupportEdge.mk 115 185 Bool.false)))) (Table.node 223 (Table.node 222 (Table.leaf (SupportEdge.mk 115 220 Bool.false)) (Table.leaf (SupportEdge.mk 115 235 Bool.false))) (Table.node 224 (Table.leaf (SupportEdge.mk 115 247 Bool.false)) (Table.leaf (SupportEdge.mk 115 249 Bool.true))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 5 (Table.node 2 (Table.node 1 (Table.leaf 23) (Table.leaf 84)) (Table.node 3 (Table.leaf 97) (Table.node 4 (Table.leaf 102) (Table.leaf 111)))) (Table.node 7 (Table.node 6 (Table.leaf 138) (Table.leaf 155)) (Table.node 8 (Table.leaf 159) (Table.node 9 (Table.leaf 170) (Table.leaf 218)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 225 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 10 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C035.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode21 : Eq (assignment 21) Sign.positive :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode22 : Eq (assignment 22) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode24 : Eq (assignment 24) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode25 : Eq (assignment 25) Sign.positive :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode57 : Eq (assignment 57) Sign.positive :=
    Eq.trans (h_support 40 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode60 : Eq (assignment 60) Sign.positive :=
    Eq.trans (h_support 44 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode91 : Eq (assignment 91) Sign.positive :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode94 : Eq (assignment 94) Sign.positive :=
    Eq.trans (h_support 45 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode95 : Eq (assignment 95) Sign.negative :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode96 : Eq (assignment 96) Sign.negative :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode99 : Eq (assignment 99) Sign.positive :=
    Eq.trans (h_support 46 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode100 : Eq (assignment 100) Sign.positive :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode129 : Eq (assignment 129) Sign.negative :=
    Eq.trans (h_support 165 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode130 : Eq (assignment 130) Sign.negative :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode25)
  let hnode163 : Eq (assignment 163) Sign.negative :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode164 : Eq (assignment 164) Sign.negative :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode25)
  let hnode166 : Eq (assignment 166) Sign.negative :=
    Eq.trans (h_support 167 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode167 : Eq (assignment 167) Sign.negative :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode25)
  let hnode168 : Eq (assignment 168) Sign.negative :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode169 : Eq (assignment 169) Sign.negative :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode25)
  let hnode4 : Eq (assignment 4) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 109 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode129)
  let hnode26 : Eq (assignment 26) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 61 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode91)
  let hnode31 : Eq (assignment 31) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 69 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode96)
  let hnode33 : Eq (assignment 33) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 117 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode168)
  let hnode36 : Eq (assignment 36) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 86 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode40 : Eq (assignment 40) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 94 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode44 : Eq (assignment 44) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 186 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode169)
  let hnode58 : Eq (assignment 58) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 13 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode128 : Eq (assignment 128) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 18 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode168)
  let hnode202 : Eq (assignment 202) Sign.negative :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode167)
  let hnode205 : Eq (assignment 205) Sign.positive :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode100)
  let hnode233 : Eq (assignment 233) Sign.negative :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode167)
  let hnode236 : Eq (assignment 236) Sign.positive :=
    Eq.trans (h_support 182 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode100)
  let hnode238 : Eq (assignment 238) Sign.positive :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode167)
  let hnode239 : Eq (assignment 239) Sign.positive :=
    Eq.trans (h_support 183 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode100)
  let hnode240 : Eq (assignment 240) Sign.positive :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode100)
  let hnode3 : Eq (assignment 3) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 105 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode128)
  let hnode8 : Eq (assignment 8) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 9 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode61 : Eq (assignment 61) Sign.negative :=
    Eq.trans (h_support 60 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode66 : Eq (assignment 66) Sign.positive :=
    Eq.trans (h_support 68 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode68 : Eq (assignment 68) Sign.negative :=
    Eq.trans (h_support 80 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode71 : Eq (assignment 71) Sign.positive :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode75 : Eq (assignment 75) Sign.negative :=
    Eq.trans (h_support 93 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode77 : Eq (assignment 77) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 199 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode202)
  let hnode92 : Eq (assignment 92) Sign.negative :=
    Eq.trans (h_support 12 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode98 : Eq (assignment 98) Sign.positive :=
    Eq.trans (h_support 14 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode58)
  let hnode101 : Eq (assignment 101) Sign.positive :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode103 : Eq (assignment 103) Sign.positive :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode104 : Eq (assignment 104) Sign.positive :=
    Eq.trans (h_support 82 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode107 : Eq (assignment 107) Sign.positive :=
    Eq.trans (h_support 70 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode109 : Eq (assignment 109) Sign.negative :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode31)
  let hnode110 : Eq (assignment 110) Sign.positive :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode112 : Eq (assignment 112) Sign.negative :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode36)
  let hnode113 : Eq (assignment 113) Sign.negative :=
    Eq.trans (h_support 88 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode36)
  let hnode117 : Eq (assignment 117) Sign.positive :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode118 : Eq (assignment 118) Sign.positive :=
    Eq.trans (h_support 96 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode133 : Eq (assignment 133) Sign.negative :=
    Eq.trans (h_support 110 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode136 : Eq (assignment 136) Sign.negative :=
    Eq.trans (h_support 111 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode140 : Eq (assignment 140) Sign.positive :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode149 : Eq (assignment 149) Sign.negative :=
    Eq.trans (h_support 185 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode162 : Eq (assignment 162) Sign.positive :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode128)
  let hnode165 : Eq (assignment 165) Sign.positive :=
    Eq.trans (h_support 17 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode128)
  let hnode174 : Eq (assignment 174) Sign.negative :=
    Eq.trans (h_support 118 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode177 : Eq (assignment 177) Sign.negative :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode180 : Eq (assignment 180) Sign.negative :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode185 : Eq (assignment 185) Sign.positive :=
    Eq.trans (h_support 187 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode188 : Eq (assignment 188) Sign.positive :=
    Eq.trans (h_support 188 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode190 : Eq (assignment 190) Sign.negative :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode16 : Eq (assignment 16) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 145 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode136)
  let hnode18 : Eq (assignment 18) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 28 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode68)
  let hnode19 : Eq (assignment 19) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 134 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode149)
  let hnode20 : Eq (assignment 20) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 153 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode140)
  let hnode27 : Eq (assignment 27) Sign.positive :=
    Eq.trans (h_support 4 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode28 : Eq (assignment 28) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 66 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode30 : Eq (assignment 30) Sign.positive :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode32 : Eq (assignment 32) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 49 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode103)
  let hnode34 : Eq (assignment 34) Sign.negative :=
    Eq.trans (h_support 7 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode35 : Eq (assignment 35) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 173 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode140)
  let hnode37 : Eq (assignment 37) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 90 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode42 : Eq (assignment 42) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 53 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode113)
  let hnode43 : Eq (assignment 43) Sign.positive :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode45 : Eq (assignment 45) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 180 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode190)
  let hnode46 : Eq (assignment 46) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 98 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode101)
  let hnode47 : Eq (assignment 47) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 73 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode49 : Eq (assignment 49) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 32 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode50 : Eq (assignment 50) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 138 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode185)
  let hnode115 : Eq (assignment 115) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 220 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode185)
  let hnode132 : Eq (assignment 132) Sign.positive :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode135 : Eq (assignment 135) Sign.positive :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode139 : Eq (assignment 139) Sign.negative :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode141 : Eq (assignment 141) Sign.positive :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode147 : Eq (assignment 147) Sign.positive :=
    Eq.trans (h_support 198 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode77)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 215 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode109)
  let hnode183 : Eq (assignment 183) Sign.negative :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode113)
  let hnode196 : Eq (assignment 196) Sign.negative :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode71)
  let hnode203 : Eq (assignment 203) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode209 : Eq (assignment 209) Sign.negative :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode212 : Eq (assignment 212) Sign.negative :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode214 : Eq (assignment 214) Sign.negative :=
    Eq.trans (h_support 216 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode109)
  let hnode215 : Eq (assignment 215) Sign.negative :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode216 : Eq (assignment 216) Sign.positive :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode217 : Eq (assignment 217) Sign.positive :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode223 : Eq (assignment 223) Sign.negative :=
    Eq.trans (h_support 200 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode77)
  let hnode224 : Eq (assignment 224) Sign.negative :=
    Eq.trans (h_support 201 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode77)
  let hnode243 : Eq (assignment 243) Sign.positive :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode109)
  let hnode245 : Eq (assignment 245) Sign.negative :=
    Eq.trans (h_support 219 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode109)
  let hnode247 : Eq (assignment 247) Sign.positive :=
    Eq.trans (h_support 208 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode113)
  let hnode248 : Eq (assignment 248) Sign.positive :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode113)
  let hnode12 : Eq (assignment 12) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 125 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode132)
  let hnode17 : Eq (assignment 17) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 150 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode147)
  let hnode54 : Eq (assignment 54) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 157 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode179)
  let hnode63 : Eq (assignment 63) Sign.positive :=
    Eq.trans (h_support 64 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode67 : Eq (assignment 67) Sign.negative :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode72 : Eq (assignment 72) Sign.negative :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode78 : Eq (assignment 78) Sign.negative :=
    Eq.trans (h_support 29 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode81 : Eq (assignment 81) Sign.positive :=
    Eq.trans (h_support 97 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode82 : Eq (assignment 82) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 212 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode217)
  let hnode87 : Eq (assignment 87) Sign.negative :=
    Eq.trans (h_support 30 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode89 : Eq (assignment 89) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 161 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode214)
  let hnode90 : Eq (assignment 90) Sign.negative :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode93 : Eq (assignment 93) Sign.negative :=
    Eq.trans (h_support 65 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode106 : Eq (assignment 106) Sign.negative :=
    Eq.trans (h_support 67 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode108 : Eq (assignment 108) Sign.negative :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode114 : Eq (assignment 114) Sign.positive :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode37)
  let hnode119 : Eq (assignment 119) Sign.positive :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode42)
  let hnode121 : Eq (assignment 121) Sign.negative :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode46)
  let hnode122 : Eq (assignment 122) Sign.negative :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode46)
  let hnode123 : Eq (assignment 123) Sign.positive :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode124 : Eq (assignment 124) Sign.negative :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode49)
  let hnode146 : Eq (assignment 146) Sign.negative :=
    Eq.trans (h_support 146 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode148 : Eq (assignment 148) Sign.positive :=
    Eq.trans (h_support 113 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode18)
  let hnode150 : Eq (assignment 150) Sign.positive :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode152 : Eq (assignment 152) Sign.negative :=
    Eq.trans (h_support 147 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode154 : Eq (assignment 154) Sign.positive :=
    Eq.trans (h_support 114 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode18)
  let hnode156 : Eq (assignment 156) Sign.positive :=
    Eq.trans (h_support 155 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode157 : Eq (assignment 157) Sign.positive :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode16)
  let hnode158 : Eq (assignment 158) Sign.negative :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode160 : Eq (assignment 160) Sign.positive :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode172 : Eq (assignment 172) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 79 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode243)
  let hnode175 : Eq (assignment 175) Sign.positive :=
    Eq.trans (h_support 137 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode50)
  let hnode176 : Eq (assignment 176) Sign.negative :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode181 : Eq (assignment 181) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 101 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode216)
  let hnode186 : Eq (assignment 186) Sign.negative :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode189 : Eq (assignment 189) Sign.negative :=
    Eq.trans (h_support 179 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode192 : Eq (assignment 192) Sign.negative :=
    Eq.trans (h_support 139 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode50)
  let hnode194 : Eq (assignment 194) Sign.positive :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode50)
  let hnode220 : Eq (assignment 220) Sign.positive :=
    Eq.trans (h_support 221 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode115)
  let hnode235 : Eq (assignment 235) Sign.positive :=
    Eq.trans (h_support 222 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode115)
  let hnode249 : Eq (assignment 249) Sign.negative :=
    Eq.trans (h_support 224 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode115)
  let hnode13 : Eq (assignment 13) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 26 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode82)
  let hnode14 : Eq (assignment 14) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 132 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode156)
  let hnode62 : Eq (assignment 62) Sign.negative :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode12)
  let hnode74 : Eq (assignment 74) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 196 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode220)
  let hnode85 : Eq (assignment 85) Sign.negative :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode12)
  let hnode137 : Eq (assignment 137) Sign.positive :=
    Eq.trans (h_support 149 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode142 : Eq (assignment 142) Sign.positive :=
    Eq.trans (h_support 126 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode151 : Eq (assignment 151) Sign.negative :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode12)
  let hnode153 : Eq (assignment 153) Sign.positive :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode193 : Eq (assignment 193) Sign.negative :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode195 : Eq (assignment 195) Sign.positive :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode54)
  let hnode207 : Eq (assignment 207) Sign.positive :=
    Eq.trans (h_support 211 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode82)
  let hnode219 : Eq (assignment 219) Sign.negative :=
    Eq.trans (h_support 37 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode154)
  let hnode226 : Eq (assignment 226) Sign.positive :=
    Eq.trans (h_support 213 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode82)
  let hnode228 : Eq (assignment 228) Sign.negative :=
    Eq.trans (h_support 214 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode82)
  let hnode229 : Eq (assignment 229) Sign.positive :=
    Eq.trans (h_support 39 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode154)
  let hnode230 : Eq (assignment 230) Sign.positive :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode89)
  let hnode231 : Eq (assignment 231) Sign.positive :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode181)
  let hnode232 : Eq (assignment 232) Sign.negative :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode172)
  let hnode241 : Eq (assignment 241) Sign.negative :=
    Eq.trans (h_support 78 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode172)
  let hnode246 : Eq (assignment 246) Sign.positive :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode181)
  let hnode73 : Eq (assignment 73) Sign.positive :=
    Eq.trans (h_support 25 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode83 : Eq (assignment 83) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 205 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode228)
  let hnode86 : Eq (assignment 86) Sign.positive :=
    Eq.trans (h_support 27 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode134 : Eq (assignment 134) Sign.negative :=
    Eq.trans (h_support 129 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode144 : Eq (assignment 144) Sign.negative :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode199 : Eq (assignment 199) Sign.positive :=
    Eq.trans (h_support 195 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode210 : Eq (assignment 210) Sign.positive :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode85)
  let hnode221 : Eq (assignment 221) Sign.positive :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode227 : Eq (assignment 227) Sign.negative :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode85)
  let hnode208 : Eq (assignment 208) Sign.negative :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C035.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (domain_from_eq (domain := Cases.C035.initial 0) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded2 := below_succ bounded1 (top_allows (Sign.withNegation globalNegation (assignment 1)))
  let bounded3 := below_succ bounded2 (top_allows (Sign.withNegation globalNegation (assignment 2)))
  let bounded4 := below_succ bounded3 (domain_from_eq (domain := Cases.C035.initial 3) (congrArg (Sign.withNegation globalNegation) hnode3) (Eq.refl Bool.true))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C035.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (top_allows (Sign.withNegation globalNegation (assignment 5)))
  let bounded7 := below_succ bounded6 (top_allows (Sign.withNegation globalNegation (assignment 6)))
  let bounded8 := below_succ bounded7 (top_allows (Sign.withNegation globalNegation (assignment 7)))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C035.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (top_allows (Sign.withNegation globalNegation (assignment 9)))
  let bounded11 := below_succ bounded10 (top_allows (Sign.withNegation globalNegation (assignment 10)))
  let bounded12 := below_succ bounded11 (top_allows (Sign.withNegation globalNegation (assignment 11)))
  let bounded13 := below_succ bounded12 (domain_from_eq (domain := Cases.C035.initial 12) (congrArg (Sign.withNegation globalNegation) hnode12) (Eq.refl Bool.true))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C035.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C035.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (top_allows (Sign.withNegation globalNegation (assignment 15)))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Cases.C035.initial 16) (congrArg (Sign.withNegation globalNegation) hnode16) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C035.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (domain_from_eq (domain := Cases.C035.initial 18) (congrArg (Sign.withNegation globalNegation) hnode18) (Eq.refl Bool.true))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C035.initial 19) (congrArg (Sign.withNegation globalNegation) hnode19) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Cases.C035.initial 20) (congrArg (Sign.withNegation globalNegation) hnode20) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C035.initial 21) (congrArg (Sign.withNegation globalNegation) hnode21) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (domain_from_eq (domain := Cases.C035.initial 22) (congrArg (Sign.withNegation globalNegation) hnode22) (Eq.refl Bool.true))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C035.initial 23) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C035.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C035.initial 25) (congrArg (Sign.withNegation globalNegation) hnode25) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Cases.C035.initial 26) (congrArg (Sign.withNegation globalNegation) hnode26) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C035.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C035.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (top_allows (Sign.withNegation globalNegation (assignment 29)))
  let bounded31 := below_succ bounded30 (domain_from_eq (domain := Cases.C035.initial 30) (congrArg (Sign.withNegation globalNegation) hnode30) (Eq.refl Bool.true))
  let bounded32 := below_succ bounded31 (domain_from_eq (domain := Cases.C035.initial 31) (congrArg (Sign.withNegation globalNegation) hnode31) (Eq.refl Bool.true))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C035.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C035.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C035.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (domain_from_eq (domain := Cases.C035.initial 35) (congrArg (Sign.withNegation globalNegation) hnode35) (Eq.refl Bool.true))
  let bounded37 := below_succ bounded36 (domain_from_eq (domain := Cases.C035.initial 36) (congrArg (Sign.withNegation globalNegation) hnode36) (Eq.refl Bool.true))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C035.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (top_allows (Sign.withNegation globalNegation (assignment 38)))
  let bounded40 := below_succ bounded39 (top_allows (Sign.withNegation globalNegation (assignment 39)))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Cases.C035.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (top_allows (Sign.withNegation globalNegation (assignment 41)))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C035.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (domain_from_eq (domain := Cases.C035.initial 43) (congrArg (Sign.withNegation globalNegation) hnode43) (Eq.refl Bool.true))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Cases.C035.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C035.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (domain_from_eq (domain := Cases.C035.initial 46) (congrArg (Sign.withNegation globalNegation) hnode46) (Eq.refl Bool.true))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C035.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (top_allows (Sign.withNegation globalNegation (assignment 48)))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C035.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (domain_from_eq (domain := Cases.C035.initial 50) (congrArg (Sign.withNegation globalNegation) hnode50) (Eq.refl Bool.true))
  let bounded52 := below_succ bounded51 (top_allows (Sign.withNegation globalNegation (assignment 51)))
  let bounded53 := below_succ bounded52 (top_allows (Sign.withNegation globalNegation (assignment 52)))
  let bounded54 := below_succ bounded53 (top_allows (Sign.withNegation globalNegation (assignment 53)))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Cases.C035.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (top_allows (Sign.withNegation globalNegation (assignment 55)))
  let bounded57 := below_succ bounded56 (top_allows (Sign.withNegation globalNegation (assignment 56)))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C035.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C035.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (top_allows (Sign.withNegation globalNegation (assignment 59)))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C035.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Cases.C035.initial 61) (congrArg (Sign.withNegation globalNegation) hnode61) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C035.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C035.initial 63) (congrArg (Sign.withNegation globalNegation) hnode63) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (top_allows (Sign.withNegation globalNegation (assignment 64)))
  let bounded66 := below_succ bounded65 (top_allows (Sign.withNegation globalNegation (assignment 65)))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C035.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (domain_from_eq (domain := Cases.C035.initial 67) (congrArg (Sign.withNegation globalNegation) hnode67) (Eq.refl Bool.true))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C035.initial 68) (congrArg (Sign.withNegation globalNegation) hnode68) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (top_allows (Sign.withNegation globalNegation (assignment 69)))
  let bounded71 := below_succ bounded70 (top_allows (Sign.withNegation globalNegation (assignment 70)))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C035.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C035.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C035.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C035.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Cases.C035.initial 75) (congrArg (Sign.withNegation globalNegation) hnode75) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (top_allows (Sign.withNegation globalNegation (assignment 76)))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C035.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C035.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (top_allows (Sign.withNegation globalNegation (assignment 79)))
  let bounded81 := below_succ bounded80 (top_allows (Sign.withNegation globalNegation (assignment 80)))
  let bounded82 := below_succ bounded81 (domain_from_eq (domain := Cases.C035.initial 81) (congrArg (Sign.withNegation globalNegation) hnode81) (Eq.refl Bool.true))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Cases.C035.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C035.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (domain_from_eq (domain := Cases.C035.initial 84) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C035.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C035.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C035.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (top_allows (Sign.withNegation globalNegation (assignment 88)))
  let bounded90 := below_succ bounded89 (domain_from_eq (domain := Cases.C035.initial 89) (congrArg (Sign.withNegation globalNegation) hnode89) (Eq.refl Bool.true))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C035.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C035.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C035.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C035.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C035.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C035.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C035.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (domain_from_eq (domain := Cases.C035.initial 97) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C035.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C035.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C035.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C035.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C035.initial 102) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C035.initial 103) (congrArg (Sign.withNegation globalNegation) hnode103) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C035.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (top_allows (Sign.withNegation globalNegation (assignment 105)))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C035.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C035.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C035.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C035.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C035.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C035.initial 111) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C035.initial 112) (congrArg (Sign.withNegation globalNegation) hnode112) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C035.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C035.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C035.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (top_allows (Sign.withNegation globalNegation (assignment 116)))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C035.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C035.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C035.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (top_allows (Sign.withNegation globalNegation (assignment 120)))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C035.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C035.initial 122) (congrArg (Sign.withNegation globalNegation) hnode122) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C035.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C035.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (top_allows (Sign.withNegation globalNegation (assignment 125)))
  let bounded127 := below_succ bounded126 (top_allows (Sign.withNegation globalNegation (assignment 126)))
  let bounded128 := below_succ bounded127 (top_allows (Sign.withNegation globalNegation (assignment 127)))
  let bounded129 := below_succ bounded128 (domain_from_eq (domain := Cases.C035.initial 128) (congrArg (Sign.withNegation globalNegation) hnode128) (Eq.refl Bool.true))
  let bounded130 := below_succ bounded129 (domain_from_eq (domain := Cases.C035.initial 129) (congrArg (Sign.withNegation globalNegation) hnode129) (Eq.refl Bool.true))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C035.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (top_allows (Sign.withNegation globalNegation (assignment 131)))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C035.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C035.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C035.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C035.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C035.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C035.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C035.initial 138) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C035.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C035.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C035.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C035.initial 142) (congrArg (Sign.withNegation globalNegation) hnode142) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (top_allows (Sign.withNegation globalNegation (assignment 143)))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C035.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (top_allows (Sign.withNegation globalNegation (assignment 145)))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C035.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C035.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C035.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C035.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C035.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C035.initial 151) (congrArg (Sign.withNegation globalNegation) hnode151) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C035.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C035.initial 153) (congrArg (Sign.withNegation globalNegation) hnode153) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (domain_from_eq (domain := Cases.C035.initial 154) (congrArg (Sign.withNegation globalNegation) hnode154) (Eq.refl Bool.true))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C035.initial 155) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C035.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C035.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C035.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C035.initial 159) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C035.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (top_allows (Sign.withNegation globalNegation (assignment 161)))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Cases.C035.initial 162) (congrArg (Sign.withNegation globalNegation) hnode162) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C035.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C035.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C035.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C035.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C035.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (domain_from_eq (domain := Cases.C035.initial 168) (congrArg (Sign.withNegation globalNegation) hnode168) (Eq.refl Bool.true))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C035.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C035.initial 170) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (top_allows (Sign.withNegation globalNegation (assignment 171)))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C035.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (top_allows (Sign.withNegation globalNegation (assignment 173)))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C035.initial 174) (congrArg (Sign.withNegation globalNegation) hnode174) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C035.initial 175) (congrArg (Sign.withNegation globalNegation) hnode175) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C035.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Cases.C035.initial 177) (congrArg (Sign.withNegation globalNegation) hnode177) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (top_allows (Sign.withNegation globalNegation (assignment 178)))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C035.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C035.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C035.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (top_allows (Sign.withNegation globalNegation (assignment 182)))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C035.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (top_allows (Sign.withNegation globalNegation (assignment 184)))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C035.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Cases.C035.initial 186) (congrArg (Sign.withNegation globalNegation) hnode186) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (top_allows (Sign.withNegation globalNegation (assignment 187)))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C035.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C035.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C035.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (top_allows (Sign.withNegation globalNegation (assignment 191)))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C035.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C035.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Cases.C035.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C035.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (domain_from_eq (domain := Cases.C035.initial 196) (congrArg (Sign.withNegation globalNegation) hnode196) (Eq.refl Bool.true))
  let bounded198 := below_succ bounded197 (top_allows (Sign.withNegation globalNegation (assignment 197)))
  let bounded199 := below_succ bounded198 (top_allows (Sign.withNegation globalNegation (assignment 198)))
  let bounded200 := below_succ bounded199 (domain_from_eq (domain := Cases.C035.initial 199) (congrArg (Sign.withNegation globalNegation) hnode199) (Eq.refl Bool.true))
  let bounded201 := below_succ bounded200 (top_allows (Sign.withNegation globalNegation (assignment 200)))
  let bounded202 := below_succ bounded201 (top_allows (Sign.withNegation globalNegation (assignment 201)))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C035.initial 202) (congrArg (Sign.withNegation globalNegation) hnode202) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (domain_from_eq (domain := Cases.C035.initial 203) (congrArg (Sign.withNegation globalNegation) hnode203) (Eq.refl Bool.true))
  let bounded205 := below_succ bounded204 (top_allows (Sign.withNegation globalNegation (assignment 204)))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C035.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (top_allows (Sign.withNegation globalNegation (assignment 206)))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Cases.C035.initial 207) (congrArg (Sign.withNegation globalNegation) hnode207) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C035.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C035.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C035.initial 210) (congrArg (Sign.withNegation globalNegation) hnode210) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (top_allows (Sign.withNegation globalNegation (assignment 211)))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C035.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (top_allows (Sign.withNegation globalNegation (assignment 213)))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C035.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (domain_from_eq (domain := Cases.C035.initial 215) (congrArg (Sign.withNegation globalNegation) hnode215) (Eq.refl Bool.true))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C035.initial 216) (congrArg (Sign.withNegation globalNegation) hnode216) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C035.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C035.initial 218) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Cases.C035.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C035.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (domain_from_eq (domain := Cases.C035.initial 221) (congrArg (Sign.withNegation globalNegation) hnode221) (Eq.refl Bool.true))
  let bounded223 := below_succ bounded222 (top_allows (Sign.withNegation globalNegation (assignment 222)))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C035.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C035.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (top_allows (Sign.withNegation globalNegation (assignment 225)))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C035.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C035.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C035.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Cases.C035.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C035.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (domain_from_eq (domain := Cases.C035.initial 231) (congrArg (Sign.withNegation globalNegation) hnode231) (Eq.refl Bool.true))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C035.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (domain_from_eq (domain := Cases.C035.initial 233) (congrArg (Sign.withNegation globalNegation) hnode233) (Eq.refl Bool.true))
  let bounded235 := below_succ bounded234 (top_allows (Sign.withNegation globalNegation (assignment 234)))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C035.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (domain_from_eq (domain := Cases.C035.initial 236) (congrArg (Sign.withNegation globalNegation) hnode236) (Eq.refl Bool.true))
  let bounded238 := below_succ bounded237 (top_allows (Sign.withNegation globalNegation (assignment 237)))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C035.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Cases.C035.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (domain_from_eq (domain := Cases.C035.initial 240) (congrArg (Sign.withNegation globalNegation) hnode240) (Eq.refl Bool.true))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C035.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (top_allows (Sign.withNegation globalNegation (assignment 242)))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C035.initial 243) (congrArg (Sign.withNegation globalNegation) hnode243) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (top_allows (Sign.withNegation globalNegation (assignment 244)))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C035.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C035.initial 246) (congrArg (Sign.withNegation globalNegation) hnode246) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C035.initial 247) (congrArg (Sign.withNegation globalNegation) hnode247) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C035.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (domain_from_eq (domain := Cases.C035.initial 249) (congrArg (Sign.withNegation globalNegation) hnode249) (Eq.refl Bool.true))
  let bounded251 := below_succ bounded250 (top_allows (Sign.withNegation globalNegation (assignment 250)))
  let bounded252 := below_succ bounded251 (top_allows (Sign.withNegation globalNegation (assignment 251)))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C035.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C035
#print axioms Papers.RationalityTen.PureGP.Initializers.C035.support_sign_contradiction
