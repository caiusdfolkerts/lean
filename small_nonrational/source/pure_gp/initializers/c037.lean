module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C037

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C037
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 0
def globalNegation : Bool := Bool.true
def edgeTable : Table SupportEdge := (Table.node 112 (Table.node 56 (Table.node 28 (Table.node 14 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 4 9 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 4 13 Bool.false)) (Table.leaf (SupportEdge.mk 4 16 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 4 18 Bool.false)) (Table.leaf (SupportEdge.mk 5 10 Bool.false))) (Table.node 6 (Table.leaf (SupportEdge.mk 5 14 Bool.false)) (Table.leaf (SupportEdge.mk 5 17 Bool.false))))) (Table.node 10 (Table.node 8 (Table.leaf (SupportEdge.mk 5 19 Bool.false)) (Table.node 9 (Table.leaf (SupportEdge.mk 35 45 Bool.false)) (Table.leaf (SupportEdge.mk 35 51 Bool.false)))) (Table.node 12 (Table.node 11 (Table.leaf (SupportEdge.mk 35 54 Bool.false)) (Table.leaf (SupportEdge.mk 35 55 Bool.false))) (Table.node 13 (Table.leaf (SupportEdge.mk 70 80 Bool.false)) (Table.leaf (SupportEdge.mk 70 86 Bool.false)))))) (Table.node 21 (Table.node 17 (Table.node 15 (Table.leaf (SupportEdge.mk 70 89 Bool.false)) (Table.node 16 (Table.leaf (SupportEdge.mk 70 90 Bool.false)) (Table.leaf (SupportEdge.mk 140 150 Bool.false)))) (Table.node 19 (Table.node 18 (Table.leaf (SupportEdge.mk 140 156 Bool.false)) (Table.leaf (SupportEdge.mk 140 159 Bool.false))) (Table.node 20 (Table.leaf (SupportEdge.mk 140 160 Bool.false)) (Table.leaf (SupportEdge.mk 0 57 Bool.true))))) (Table.node 24 (Table.node 22 (Table.leaf (SupportEdge.mk 0 58 Bool.true)) (Table.node 23 (Table.leaf (SupportEdge.mk 0 59 Bool.true)) (Table.leaf (SupportEdge.mk 0 60 Bool.true)))) (Table.node 26 (Table.node 25 (Table.leaf (SupportEdge.mk 1 61 Bool.true)) (Table.leaf (SupportEdge.mk 1 62 Bool.true))) (Table.node 27 (Table.leaf (SupportEdge.mk 1 63 Bool.true)) (Table.leaf (SupportEdge.mk 1 64 Bool.true))))))) (Table.node 42 (Table.node 35 (Table.node 31 (Table.node 29 (Table.leaf (SupportEdge.mk 6 71 Bool.true)) (Table.node 30 (Table.leaf (SupportEdge.mk 6 72 Bool.true)) (Table.leaf (SupportEdge.mk 6 73 Bool.true)))) (Table.node 33 (Table.node 32 (Table.leaf (SupportEdge.mk 6 74 Bool.true)) (Table.leaf (SupportEdge.mk 21 91 Bool.true))) (Table.node 34 (Table.leaf (SupportEdge.mk 21 92 Bool.true)) (Table.leaf (SupportEdge.mk 21 93 Bool.true))))) (Table.node 38 (Table.node 36 (Table.leaf (SupportEdge.mk 21 94 Bool.true)) (Table.node 37 (Table.leaf (SupportEdge.mk 126 196 Bool.false)) (Table.leaf (SupportEdge.mk 126 197 Bool.false)))) (Table.node 40 (Table.node 39 (Table.leaf (SupportEdge.mk 126 198 Bool.false)) (Table.leaf (SupportEdge.mk 126 199 Bool.false))) (Table.node 41 (Table.leaf (SupportEdge.mk 3 58 Bool.false)) (Table.leaf (SupportEdge.mk 3 62 Bool.false)))))) (Table.node 49 (Table.node 45 (Table.node 43 (Table.leaf (SupportEdge.mk 3 65 Bool.false)) (Table.node 44 (Table.leaf (SupportEdge.mk 3 69 Bool.true)) (Table.leaf (SupportEdge.mk 4 59 Bool.false)))) (Table.node 47 (Table.node 46 (Table.leaf (SupportEdge.mk 4 63 Bool.false)) (Table.leaf (SupportEdge.mk 4 66 Bool.false))) (Table.node 48 (Table.leaf (SupportEdge.mk 4 70 Bool.true)) (Table.leaf (SupportEdge.mk 18 78 Bool.true))))) (Table.node 52 (Table.node 50 (Table.leaf (SupportEdge.mk 18 84 Bool.true)) (Table.node 51 (Table.leaf (SupportEdge.mk 18 87 Bool.true)) (Table.leaf (SupportEdge.mk 18 90 Bool.true)))) (Table.node 54 (Table.node 53 (Table.leaf (SupportEdge.mk 33 98 Bool.true)) (Table.leaf (SupportEdge.mk 33 104 Bool.true))) (Table.node 55 (Table.leaf (SupportEdge.mk 33 107 Bool.true)) (Table.leaf (SupportEdge.mk 33 110 Bool.true)))))))) (Table.node 84 (Table.node 70 (Table.node 63 (Table.node 59 (Table.node 57 (Table.leaf (SupportEdge.mk 138 203 Bool.false)) (Table.node 58 (Table.leaf (SupportEdge.mk 138 209 Bool.false)) (Table.leaf (SupportEdge.mk 138 212 Bool.false)))) (Table.node 61 (Table.node 60 (Table.leaf (SupportEdge.mk 138 215 Bool.false)) (Table.leaf (SupportEdge.mk 10 60 Bool.true))) (Table.node 62 (Table.leaf (SupportEdge.mk 10 74 Bool.false)) (Table.leaf (SupportEdge.mk 10 77 Bool.false))))) (Table.node 66 (Table.node 64 (Table.leaf (SupportEdge.mk 10 79 Bool.false)) (Table.node 65 (Table.leaf (SupportEdge.mk 10 80 Bool.false)) (Table.leaf (SupportEdge.mk 22 57 Bool.false)))) (Table.node 68 (Table.node 67 (Table.leaf (SupportEdge.mk 22 91 Bool.false)) (Table.leaf (SupportEdge.mk 22 96 Bool.true))) (Table.node 69 (Table.leaf (SupportEdge.mk 22 97 Bool.true)) (Table.leaf (SupportEdge.mk 23 58 Bool.false)))))) (Table.node 77 (Table.node 73 (Table.node 71 (Table.leaf (SupportEdge.mk 23 92 Bool.false)) (Table.node 72 (Table.leaf (SupportEdge.mk 23 98 Bool.true)) (Table.leaf (SupportEdge.mk 23 99 Bool.true)))) (Table.node 75 (Table.node 74 (Table.leaf (SupportEdge.mk 30 65 Bool.false)) (Table.leaf (SupportEdge.mk 30 101 Bool.true))) (Table.node 76 (Table.leaf (SupportEdge.mk 30 107 Bool.true)) (Table.leaf (SupportEdge.mk 30 108 Bool.true))))) (Table.node 80 (Table.node 78 (Table.leaf (SupportEdge.mk 40 75 Bool.false)) (Table.node 79 (Table.leaf (SupportEdge.mk 40 111 Bool.true)) (Table.leaf (SupportEdge.mk 40 117 Bool.true)))) (Table.node 82 (Table.node 81 (Table.leaf (SupportEdge.mk 40 118 Bool.true)) (Table.leaf (SupportEdge.mk 165 200 Bool.false))) (Table.node 83 (Table.leaf (SupportEdge.mk 165 231 Bool.false)) (Table.leaf (SupportEdge.mk 165 237 Bool.false))))))) (Table.node 98 (Table.node 91 (Table.node 87 (Table.node 85 (Table.leaf (SupportEdge.mk 165 238 Bool.false)) (Table.node 86 (Table.leaf (SupportEdge.mk 43 78 Bool.false)) (Table.leaf (SupportEdge.mk 43 98 Bool.false)))) (Table.node 89 (Table.node 88 (Table.leaf (SupportEdge.mk 43 114 Bool.true)) (Table.leaf (SupportEdge.mk 43 117 Bool.true))) (Table.node 90 (Table.leaf (SupportEdge.mk 44 79 Bool.false)) (Table.leaf (SupportEdge.mk 44 99 Bool.false))))) (Table.node 94 (Table.node 92 (Table.leaf (SupportEdge.mk 44 115 Bool.true)) (Table.node 93 (Table.leaf (SupportEdge.mk 44 118 Bool.true)) (Table.leaf (SupportEdge.mk 45 80 Bool.false)))) (Table.node 96 (Table.node 95 (Table.leaf (SupportEdge.mk 45 100 Bool.false)) (Table.leaf (SupportEdge.mk 45 116 Bool.true))) (Table.node 97 (Table.leaf (SupportEdge.mk 45 119 Bool.true)) (Table.leaf (SupportEdge.mk 55 90 Bool.false)))))) (Table.node 105 (Table.node 101 (Table.node 99 (Table.leaf (SupportEdge.mk 55 110 Bool.false)) (Table.node 100 (Table.leaf (SupportEdge.mk 55 124 Bool.false)) (Table.leaf (SupportEdge.mk 55 125 Bool.false)))) (Table.node 103 (Table.node 102 (Table.leaf (SupportEdge.mk 190 225 Bool.false)) (Table.leaf (SupportEdge.mk 190 240 Bool.false))) (Table.node 104 (Table.leaf (SupportEdge.mk 190 249 Bool.true)) (Table.leaf (SupportEdge.mk 190 250 Bool.true))))) (Table.node 108 (Table.node 106 (Table.leaf (SupportEdge.mk 1 126 Bool.true)) (Table.node 107 (Table.leaf (SupportEdge.mk 1 131 Bool.false)) (Table.leaf (SupportEdge.mk 1 132 Bool.false)))) (Table.node 110 (Table.node 109 (Table.leaf (SupportEdge.mk 1 134 Bool.false)) (Table.leaf (SupportEdge.mk 4 129 Bool.true))) (Table.node 111 (Table.leaf (SupportEdge.mk 4 136 Bool.true)) (Table.leaf (SupportEdge.mk 4 138 Bool.true))))))))) (Table.node 168 (Table.node 140 (Table.node 126 (Table.node 119 (Table.node 115 (Table.node 113 (Table.leaf (SupportEdge.mk 4 140 Bool.false)) (Table.node 114 (Table.leaf (SupportEdge.mk 13 143 Bool.false)) (Table.leaf (SupportEdge.mk 13 152 Bool.true)))) (Table.node 117 (Table.node 116 (Table.leaf (SupportEdge.mk 13 154 Bool.true)) (Table.leaf (SupportEdge.mk 13 156 Bool.false))) (Table.node 118 (Table.leaf (SupportEdge.mk 28 163 Bool.false)) (Table.leaf (SupportEdge.mk 28 172 Bool.true))))) (Table.node 122 (Table.node 120 (Table.leaf (SupportEdge.mk 28 174 Bool.true)) (Table.node 121 (Table.leaf (SupportEdge.mk 28 176 Bool.false)) (Table.leaf (SupportEdge.mk 63 198 Bool.false)))) (Table.node 124 (Table.node 123 (Table.leaf (SupportEdge.mk 63 207 Bool.true)) (Table.leaf (SupportEdge.mk 63 209 Bool.true))) (Table.node 125 (Table.leaf (SupportEdge.mk 63 211 Bool.false)) (Table.leaf (SupportEdge.mk 11 131 Bool.false)))))) (Table.node 133 (Table.node 129 (Table.node 127 (Table.leaf (SupportEdge.mk 11 141 Bool.false)) (Table.node 128 (Table.leaf (SupportEdge.mk 11 151 Bool.false)) (Table.leaf (SupportEdge.mk 11 152 Bool.false)))) (Table.node 131 (Table.node 130 (Table.leaf (SupportEdge.mk 14 134 Bool.false)) (Table.leaf (SupportEdge.mk 14 144 Bool.false))) (Table.node 132 (Table.leaf (SupportEdge.mk 14 155 Bool.true)) (Table.leaf (SupportEdge.mk 14 156 Bool.true))))) (Table.node 136 (Table.node 134 (Table.leaf (SupportEdge.mk 17 137 Bool.false)) (Table.node 135 (Table.leaf (SupportEdge.mk 17 147 Bool.false)) (Table.leaf (SupportEdge.mk 17 158 Bool.true)))) (Table.node 138 (Table.node 137 (Table.leaf (SupportEdge.mk 17 159 Bool.true)) (Table.leaf (SupportEdge.mk 48 173 Bool.true))) (Table.node 139 (Table.leaf (SupportEdge.mk 48 183 Bool.true)) (Table.leaf (SupportEdge.mk 48 192 Bool.true))))))) (Table.node 154 (Table.node 147 (Table.node 143 (Table.node 141 (Table.leaf (SupportEdge.mk 48 193 Bool.true)) (Table.node 142 (Table.leaf (SupportEdge.mk 83 208 Bool.true)) (Table.leaf (SupportEdge.mk 83 218 Bool.true)))) (Table.node 145 (Table.node 144 (Table.leaf (SupportEdge.mk 83 227 Bool.true)) (Table.leaf (SupportEdge.mk 83 228 Bool.true))) (Table.node 146 (Table.leaf (SupportEdge.mk 40 145 Bool.true)) (Table.leaf (SupportEdge.mk 40 165 Bool.true))))) (Table.node 150 (Table.node 148 (Table.leaf (SupportEdge.mk 40 181 Bool.false)) (Table.node 149 (Table.leaf (SupportEdge.mk 40 187 Bool.false)) (Table.leaf (SupportEdge.mk 42 147 Bool.true)))) (Table.node 152 (Table.node 151 (Table.leaf (SupportEdge.mk 42 167 Bool.true)) (Table.leaf (SupportEdge.mk 42 183 Bool.false))) (Table.node 153 (Table.leaf (SupportEdge.mk 42 189 Bool.true)) (Table.leaf (SupportEdge.mk 44 149 Bool.true)))))) (Table.node 161 (Table.node 157 (Table.node 155 (Table.leaf (SupportEdge.mk 44 169 Bool.true)) (Table.node 156 (Table.leaf (SupportEdge.mk 44 185 Bool.false)) (Table.leaf (SupportEdge.mk 44 190 Bool.true)))) (Table.node 159 (Table.node 158 (Table.leaf (SupportEdge.mk 53 158 Bool.true)) (Table.leaf (SupportEdge.mk 53 178 Bool.true))) (Table.node 160 (Table.leaf (SupportEdge.mk 53 192 Bool.true)) (Table.leaf (SupportEdge.mk 53 195 Bool.true))))) (Table.node 164 (Table.node 162 (Table.leaf (SupportEdge.mk 118 223 Bool.false)) (Table.node 163 (Table.leaf (SupportEdge.mk 118 238 Bool.false)) (Table.leaf (SupportEdge.mk 118 247 Bool.true)))) (Table.node 166 (Table.node 165 (Table.leaf (SupportEdge.mk 118 250 Bool.true)) (Table.leaf (SupportEdge.mk 46 151 Bool.true))) (Table.node 167 (Table.leaf (SupportEdge.mk 46 171 Bool.true)) (Table.leaf (SupportEdge.mk 46 181 Bool.true)))))))) (Table.node 196 (Table.node 182 (Table.node 175 (Table.node 171 (Table.node 169 (Table.leaf (SupportEdge.mk 46 192 Bool.false)) (Table.node 170 (Table.leaf (SupportEdge.mk 47 152 Bool.true)) (Table.leaf (SupportEdge.mk 47 172 Bool.true)))) (Table.node 173 (Table.node 172 (Table.leaf (SupportEdge.mk 47 182 Bool.true)) (Table.leaf (SupportEdge.mk 47 193 Bool.false))) (Table.node 174 (Table.leaf (SupportEdge.mk 49 154 Bool.true)) (Table.leaf (SupportEdge.mk 49 174 Bool.true))))) (Table.node 178 (Table.node 176 (Table.leaf (SupportEdge.mk 49 184 Bool.true)) (Table.node 177 (Table.leaf (SupportEdge.mk 49 194 Bool.false)) (Table.leaf (SupportEdge.mk 52 157 Bool.true)))) (Table.node 180 (Table.node 179 (Table.leaf (SupportEdge.mk 52 177 Bool.true)) (Table.leaf (SupportEdge.mk 52 187 Bool.true))) (Table.node 181 (Table.leaf (SupportEdge.mk 52 195 Bool.false)) (Table.leaf (SupportEdge.mk 121 226 Bool.false)))))) (Table.node 189 (Table.node 185 (Table.node 183 (Table.leaf (SupportEdge.mk 121 241 Bool.false)) (Table.node 184 (Table.leaf (SupportEdge.mk 121 246 Bool.false)) (Table.leaf (SupportEdge.mk 121 251 Bool.false)))) (Table.node 187 (Table.node 186 (Table.leaf (SupportEdge.mk 55 160 Bool.true)) (Table.leaf (SupportEdge.mk 55 180 Bool.true))) (Table.node 188 (Table.leaf (SupportEdge.mk 55 190 Bool.true)) (Table.leaf (SupportEdge.mk 55 194 Bool.true))))) (Table.node 192 (Table.node 190 (Table.leaf (SupportEdge.mk 55 195 Bool.true)) (Table.node 191 (Table.leaf (SupportEdge.mk 74 144 Bool.false)) (Table.leaf (SupportEdge.mk 74 199 Bool.true)))) (Table.node 194 (Table.node 193 (Table.leaf (SupportEdge.mk 74 218 Bool.true)) (Table.leaf (SupportEdge.mk 74 220 Bool.true))) (Table.node 195 (Table.leaf (SupportEdge.mk 74 221 Bool.true)) (Table.leaf (SupportEdge.mk 91 161 Bool.false))))))) (Table.node 210 (Table.node 203 (Table.node 199 (Table.node 197 (Table.leaf (SupportEdge.mk 91 196 Bool.false)) (Table.node 198 (Table.leaf (SupportEdge.mk 91 231 Bool.false)) (Table.leaf (SupportEdge.mk 91 232 Bool.false)))) (Table.node 201 (Table.node 200 (Table.leaf (SupportEdge.mk 94 164 Bool.false)) (Table.leaf (SupportEdge.mk 94 199 Bool.false))) (Table.node 202 (Table.leaf (SupportEdge.mk 94 235 Bool.true)) (Table.leaf (SupportEdge.mk 94 236 Bool.true))))) (Table.node 206 (Table.node 204 (Table.leaf (SupportEdge.mk 97 167 Bool.false)) (Table.node 205 (Table.leaf (SupportEdge.mk 97 202 Bool.false)) (Table.leaf (SupportEdge.mk 97 238 Bool.true)))) (Table.node 208 (Table.node 207 (Table.leaf (SupportEdge.mk 97 239 Bool.true)) (Table.leaf (SupportEdge.mk 103 173 Bool.false))) (Table.node 209 (Table.leaf (SupportEdge.mk 103 208 Bool.false)) (Table.leaf (SupportEdge.mk 103 242 Bool.true)))))) (Table.node 217 (Table.node 213 (Table.node 211 (Table.leaf (SupportEdge.mk 103 243 Bool.true)) (Table.node 212 (Table.leaf (SupportEdge.mk 113 183 Bool.false)) (Table.leaf (SupportEdge.mk 113 218 Bool.false)))) (Table.node 215 (Table.node 214 (Table.leaf (SupportEdge.mk 113 247 Bool.true)) (Table.leaf (SupportEdge.mk 113 248 Bool.true))) (Table.node 216 (Table.leaf (SupportEdge.mk 102 172 Bool.false)) (Table.leaf (SupportEdge.mk 102 207 Bool.false))))) (Table.node 221 (Table.node 219 (Table.node 218 (Table.leaf (SupportEdge.mk 102 232 Bool.true)) (Table.leaf (SupportEdge.mk 102 241 Bool.true))) (Table.node 220 (Table.leaf (SupportEdge.mk 102 243 Bool.false)) (Table.leaf (SupportEdge.mk 107 177 Bool.false)))) (Table.node 223 (Table.node 222 (Table.leaf (SupportEdge.mk 107 212 Bool.false)) (Table.leaf (SupportEdge.mk 107 237 Bool.true))) (Table.node 224 (Table.leaf (SupportEdge.mk 107 241 Bool.true)) (Table.leaf (SupportEdge.mk 107 245 Bool.false))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 5 (Table.node 2 (Table.node 1 (Table.leaf 20) (Table.leaf 56)) (Table.node 3 (Table.leaf 68) (Table.node 4 (Table.leaf 95) (Table.leaf 120)))) (Table.node 7 (Table.node 6 (Table.leaf 133) (Table.leaf 153)) (Table.node 8 (Table.leaf 188) (Table.node 9 (Table.leaf 191) (Table.leaf 233)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 225 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 10 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C037.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode57 : Eq (assignment 57) Sign.negative :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode58 : Eq (assignment 58) Sign.negative :=
    Eq.trans (h_support 21 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode59 : Eq (assignment 59) Sign.negative :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode60 : Eq (assignment 60) Sign.negative :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode3 : Eq (assignment 3) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 40 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode4 : Eq (assignment 4) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 44 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode59)
  let hnode10 : Eq (assignment 10) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 60 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode60)
  let hnode22 : Eq (assignment 22) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 65 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode57)
  let hnode23 : Eq (assignment 23) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 69 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode5 : Eq (assignment 5) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 4 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode9 : Eq (assignment 9) Sign.negative :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode13 : Eq (assignment 13) Sign.negative :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode16 : Eq (assignment 16) Sign.negative :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode18 : Eq (assignment 18) Sign.negative :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode62 : Eq (assignment 62) Sign.negative :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode63 : Eq (assignment 63) Sign.negative :=
    Eq.trans (h_support 45 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode65 : Eq (assignment 65) Sign.negative :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode3)
  let hnode66 : Eq (assignment 66) Sign.negative :=
    Eq.trans (h_support 46 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode69 : Eq (assignment 69) Sign.positive :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode3)
  let hnode70 : Eq (assignment 70) Sign.positive :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode74 : Eq (assignment 74) Sign.positive :=
    Eq.trans (h_support 61 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode77 : Eq (assignment 77) Sign.positive :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode79 : Eq (assignment 79) Sign.positive :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode80 : Eq (assignment 80) Sign.positive :=
    Eq.trans (h_support 64 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode91 : Eq (assignment 91) Sign.negative :=
    Eq.trans (h_support 66 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode92 : Eq (assignment 92) Sign.negative :=
    Eq.trans (h_support 70 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode96 : Eq (assignment 96) Sign.positive :=
    Eq.trans (h_support 67 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode97 : Eq (assignment 97) Sign.positive :=
    Eq.trans (h_support 68 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode98 : Eq (assignment 98) Sign.positive :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode99 : Eq (assignment 99) Sign.positive :=
    Eq.trans (h_support 72 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode129 : Eq (assignment 129) Sign.positive :=
    Eq.trans (h_support 109 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode136 : Eq (assignment 136) Sign.positive :=
    Eq.trans (h_support 110 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode138 : Eq (assignment 138) Sign.positive :=
    Eq.trans (h_support 111 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode140 : Eq (assignment 140) Sign.negative :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode1 : Eq (assignment 1) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 25 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode62)
  let hnode6 : Eq (assignment 6) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 31 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode14 : Eq (assignment 14) Sign.positive :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode17 : Eq (assignment 17) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode19 : Eq (assignment 19) Sign.positive :=
    Eq.trans (h_support 7 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode21 : Eq (assignment 21) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 32 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode91)
  let hnode30 : Eq (assignment 30) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 73 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode65)
  let hnode33 : Eq (assignment 33) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 52 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode98)
  let hnode43 : Eq (assignment 43) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 86 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode98)
  let hnode44 : Eq (assignment 44) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 90 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode99)
  let hnode45 : Eq (assignment 45) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 93 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode78 : Eq (assignment 78) Sign.positive :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode84 : Eq (assignment 84) Sign.positive :=
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode86 : Eq (assignment 86) Sign.positive :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode87 : Eq (assignment 87) Sign.positive :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode89 : Eq (assignment 89) Sign.positive :=
    Eq.trans (h_support 14 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode90 : Eq (assignment 90) Sign.positive :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode143 : Eq (assignment 143) Sign.negative :=
    Eq.trans (h_support 113 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode144 : Eq (assignment 144) Sign.positive :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode74)
  let hnode150 : Eq (assignment 150) Sign.negative :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode140)
  let hnode152 : Eq (assignment 152) Sign.positive :=
    Eq.trans (h_support 114 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode154 : Eq (assignment 154) Sign.positive :=
    Eq.trans (h_support 115 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode13)
  let hnode156 : Eq (assignment 156) Sign.negative :=
    Eq.trans (h_support 116 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode159 : Eq (assignment 159) Sign.negative :=
    Eq.trans (h_support 18 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode140)
  let hnode160 : Eq (assignment 160) Sign.negative :=
    Eq.trans (h_support 19 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode140)
  let hnode161 : Eq (assignment 161) Sign.negative :=
    Eq.trans (h_support 195 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode167 : Eq (assignment 167) Sign.positive :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode97)
  let hnode196 : Eq (assignment 196) Sign.negative :=
    Eq.trans (h_support 196 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode198 : Eq (assignment 198) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode63)
  let hnode199 : Eq (assignment 199) Sign.negative :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode202 : Eq (assignment 202) Sign.positive :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode97)
  let hnode203 : Eq (assignment 203) Sign.positive :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode138)
  let hnode207 : Eq (assignment 207) Sign.positive :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode209 : Eq (assignment 209) Sign.positive :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode211 : Eq (assignment 211) Sign.negative :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode63)
  let hnode212 : Eq (assignment 212) Sign.positive :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode138)
  let hnode215 : Eq (assignment 215) Sign.positive :=
    Eq.trans (h_support 59 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode138)
  let hnode218 : Eq (assignment 218) Sign.negative :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode220 : Eq (assignment 220) Sign.negative :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode221 : Eq (assignment 221) Sign.negative :=
    Eq.trans (h_support 194 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode74)
  let hnode231 : Eq (assignment 231) Sign.negative :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode232 : Eq (assignment 232) Sign.negative :=
    Eq.trans (h_support 198 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode91)
  let hnode238 : Eq (assignment 238) Sign.negative :=
    Eq.trans (h_support 205 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode97)
  let hnode239 : Eq (assignment 239) Sign.negative :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode97)
  let hnode11 : Eq (assignment 11) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 128 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode152)
  let hnode35 : Eq (assignment 35) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 8 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode42 : Eq (assignment 42) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 150 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode167)
  let hnode47 : Eq (assignment 47) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 169 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode152)
  let hnode49 : Eq (assignment 49) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 173 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode154)
  let hnode55 : Eq (assignment 55) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 97 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode90)
  let hnode61 : Eq (assignment 61) Sign.negative :=
    Eq.trans (h_support 24 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode1)
  let hnode64 : Eq (assignment 64) Sign.negative :=
    Eq.trans (h_support 27 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode1)
  let hnode71 : Eq (assignment 71) Sign.positive :=
    Eq.trans (h_support 28 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode72 : Eq (assignment 72) Sign.positive :=
    Eq.trans (h_support 29 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode73 : Eq (assignment 73) Sign.positive :=
    Eq.trans (h_support 30 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode83 : Eq (assignment 83) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 142 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode218)
  let hnode93 : Eq (assignment 93) Sign.negative :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode94 : Eq (assignment 94) Sign.negative :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode100 : Eq (assignment 100) Sign.positive :=
    Eq.trans (h_support 94 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode101 : Eq (assignment 101) Sign.positive :=
    Eq.trans (h_support 74 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode102 : Eq (assignment 102) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 217 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode232)
  let hnode104 : Eq (assignment 104) Sign.positive :=
    Eq.trans (h_support 53 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode107 : Eq (assignment 107) Sign.positive :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode108 : Eq (assignment 108) Sign.positive :=
    Eq.trans (h_support 76 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode110 : Eq (assignment 110) Sign.positive :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode113 : Eq (assignment 113) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 212 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode218)
  let hnode114 : Eq (assignment 114) Sign.negative :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode115 : Eq (assignment 115) Sign.negative :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode116 : Eq (assignment 116) Sign.negative :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode117 : Eq (assignment 117) Sign.negative :=
    Eq.trans (h_support 88 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode118 : Eq (assignment 118) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 162 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode238)
  let hnode119 : Eq (assignment 119) Sign.negative :=
    Eq.trans (h_support 96 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode126 : Eq (assignment 126) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 36 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode196)
  let hnode131 : Eq (assignment 131) Sign.positive :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode1)
  let hnode132 : Eq (assignment 132) Sign.positive :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode1)
  let hnode134 : Eq (assignment 134) Sign.positive :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode1)
  let hnode137 : Eq (assignment 137) Sign.positive :=
    Eq.trans (h_support 133 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode147 : Eq (assignment 147) Sign.positive :=
    Eq.trans (h_support 134 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode149 : Eq (assignment 149) Sign.negative :=
    Eq.trans (h_support 153 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode155 : Eq (assignment 155) Sign.negative :=
    Eq.trans (h_support 131 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode158 : Eq (assignment 158) Sign.negative :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode165 : Eq (assignment 165) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 82 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode231)
  let hnode169 : Eq (assignment 169) Sign.negative :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode185 : Eq (assignment 185) Sign.positive :=
    Eq.trans (h_support 155 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode190 : Eq (assignment 190) Sign.negative :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode40 : Eq (assignment 40) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 146 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode165)
  let hnode51 : Eq (assignment 51) Sign.positive :=
    Eq.trans (h_support 9 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode53 : Eq (assignment 53) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 157 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode158)
  let hnode54 : Eq (assignment 54) Sign.positive :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode124 : Eq (assignment 124) Sign.positive :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode125 : Eq (assignment 125) Sign.positive :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode55)
  let hnode141 : Eq (assignment 141) Sign.positive :=
    Eq.trans (h_support 126 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode151 : Eq (assignment 151) Sign.positive :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode164 : Eq (assignment 164) Sign.negative :=
    Eq.trans (h_support 199 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode94)
  let hnode172 : Eq (assignment 172) Sign.positive :=
    Eq.trans (h_support 215 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode102)
  let hnode174 : Eq (assignment 174) Sign.positive :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode49)
  let hnode177 : Eq (assignment 177) Sign.positive :=
    Eq.trans (h_support 220 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode107)
  let hnode180 : Eq (assignment 180) Sign.negative :=
    Eq.trans (h_support 186 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode55)
  let hnode182 : Eq (assignment 182) Sign.positive :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode183 : Eq (assignment 183) Sign.negative :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode42)
  let hnode184 : Eq (assignment 184) Sign.positive :=
    Eq.trans (h_support 175 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode49)
  let hnode189 : Eq (assignment 189) Sign.positive :=
    Eq.trans (h_support 152 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode42)
  let hnode193 : Eq (assignment 193) Sign.negative :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode194 : Eq (assignment 194) Sign.negative :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode49)
  let hnode195 : Eq (assignment 195) Sign.negative :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode55)
  let hnode197 : Eq (assignment 197) Sign.negative :=
    Eq.trans (h_support 37 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode126)
  let hnode200 : Eq (assignment 200) Sign.negative :=
    Eq.trans (h_support 81 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode165)
  let hnode208 : Eq (assignment 208) Sign.negative :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode223 : Eq (assignment 223) Sign.negative :=
    Eq.trans (h_support 161 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode118)
  let hnode225 : Eq (assignment 225) Sign.negative :=
    Eq.trans (h_support 101 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode190)
  let hnode227 : Eq (assignment 227) Sign.negative :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode228 : Eq (assignment 228) Sign.negative :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode235 : Eq (assignment 235) Sign.positive :=
    Eq.trans (h_support 201 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode94)
  let hnode236 : Eq (assignment 236) Sign.positive :=
    Eq.trans (h_support 202 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode94)
  let hnode237 : Eq (assignment 237) Sign.negative :=
    Eq.trans (h_support 83 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode165)
  let hnode240 : Eq (assignment 240) Sign.negative :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode190)
  let hnode241 : Eq (assignment 241) Sign.negative :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode102)
  let hnode243 : Eq (assignment 243) Sign.positive :=
    Eq.trans (h_support 219 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode102)
  let hnode245 : Eq (assignment 245) Sign.positive :=
    Eq.trans (h_support 224 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode107)
  let hnode247 : Eq (assignment 247) Sign.positive :=
    Eq.trans (h_support 163 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode118)
  let hnode248 : Eq (assignment 248) Sign.positive :=
    Eq.trans (h_support 214 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode113)
  let hnode249 : Eq (assignment 249) Sign.positive :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode190)
  let hnode250 : Eq (assignment 250) Sign.positive :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode118)
  let hnode28 : Eq (assignment 28) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 118 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode172)
  let hnode46 : Eq (assignment 46) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 165 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode151)
  let hnode48 : Eq (assignment 48) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 138 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode183)
  let hnode52 : Eq (assignment 52) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 178 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode177)
  let hnode75 : Eq (assignment 75) Sign.positive :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode103 : Eq (assignment 103) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 210 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode243)
  let hnode111 : Eq (assignment 111) Sign.negative :=
    Eq.trans (h_support 78 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode121 : Eq (assignment 121) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 182 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode241)
  let hnode145 : Eq (assignment 145) Sign.negative :=
    Eq.trans (h_support 145 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode178 : Eq (assignment 178) Sign.negative :=
    Eq.trans (h_support 158 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode181 : Eq (assignment 181) Sign.positive :=
    Eq.trans (h_support 147 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode187 : Eq (assignment 187) Sign.positive :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode192 : Eq (assignment 192) Sign.negative :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode157 : Eq (assignment 157) Sign.positive :=
    Eq.trans (h_support 177 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode52)
  let hnode163 : Eq (assignment 163) Sign.negative :=
    Eq.trans (h_support 117 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode171 : Eq (assignment 171) Sign.positive :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode46)
  let hnode173 : Eq (assignment 173) Sign.negative :=
    Eq.trans (h_support 207 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode103)
  let hnode176 : Eq (assignment 176) Sign.negative :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode226 : Eq (assignment 226) Sign.negative :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode242 : Eq (assignment 242) Sign.positive :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode103)
  let hnode246 : Eq (assignment 246) Sign.negative :=
    Eq.trans (h_support 183 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode251 : Eq (assignment 251) Sign.negative :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C037.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (domain_from_eq (domain := Cases.C037.initial 0) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded2 := below_succ bounded1 (domain_from_eq (domain := Cases.C037.initial 1) (congrArg (Sign.withNegation globalNegation) hnode1) (Eq.refl Bool.true))
  let bounded3 := below_succ bounded2 (top_allows (Sign.withNegation globalNegation (assignment 2)))
  let bounded4 := below_succ bounded3 (domain_from_eq (domain := Cases.C037.initial 3) (congrArg (Sign.withNegation globalNegation) hnode3) (Eq.refl Bool.true))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C037.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Cases.C037.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Cases.C037.initial 6) (congrArg (Sign.withNegation globalNegation) hnode6) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (top_allows (Sign.withNegation globalNegation (assignment 7)))
  let bounded9 := below_succ bounded8 (top_allows (Sign.withNegation globalNegation (assignment 8)))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Cases.C037.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C037.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (domain_from_eq (domain := Cases.C037.initial 11) (congrArg (Sign.withNegation globalNegation) hnode11) (Eq.refl Bool.true))
  let bounded13 := below_succ bounded12 (top_allows (Sign.withNegation globalNegation (assignment 12)))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C037.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C037.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (top_allows (Sign.withNegation globalNegation (assignment 15)))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Cases.C037.initial 16) (congrArg (Sign.withNegation globalNegation) hnode16) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C037.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (domain_from_eq (domain := Cases.C037.initial 18) (congrArg (Sign.withNegation globalNegation) hnode18) (Eq.refl Bool.true))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C037.initial 19) (congrArg (Sign.withNegation globalNegation) hnode19) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Cases.C037.initial 20) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C037.initial 21) (congrArg (Sign.withNegation globalNegation) hnode21) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (domain_from_eq (domain := Cases.C037.initial 22) (congrArg (Sign.withNegation globalNegation) hnode22) (Eq.refl Bool.true))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C037.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (top_allows (Sign.withNegation globalNegation (assignment 24)))
  let bounded26 := below_succ bounded25 (top_allows (Sign.withNegation globalNegation (assignment 25)))
  let bounded27 := below_succ bounded26 (top_allows (Sign.withNegation globalNegation (assignment 26)))
  let bounded28 := below_succ bounded27 (top_allows (Sign.withNegation globalNegation (assignment 27)))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C037.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (top_allows (Sign.withNegation globalNegation (assignment 29)))
  let bounded31 := below_succ bounded30 (domain_from_eq (domain := Cases.C037.initial 30) (congrArg (Sign.withNegation globalNegation) hnode30) (Eq.refl Bool.true))
  let bounded32 := below_succ bounded31 (top_allows (Sign.withNegation globalNegation (assignment 31)))
  let bounded33 := below_succ bounded32 (top_allows (Sign.withNegation globalNegation (assignment 32)))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C037.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (top_allows (Sign.withNegation globalNegation (assignment 34)))
  let bounded36 := below_succ bounded35 (domain_from_eq (domain := Cases.C037.initial 35) (congrArg (Sign.withNegation globalNegation) hnode35) (Eq.refl Bool.true))
  let bounded37 := below_succ bounded36 (top_allows (Sign.withNegation globalNegation (assignment 36)))
  let bounded38 := below_succ bounded37 (top_allows (Sign.withNegation globalNegation (assignment 37)))
  let bounded39 := below_succ bounded38 (top_allows (Sign.withNegation globalNegation (assignment 38)))
  let bounded40 := below_succ bounded39 (top_allows (Sign.withNegation globalNegation (assignment 39)))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Cases.C037.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (top_allows (Sign.withNegation globalNegation (assignment 41)))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C037.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (domain_from_eq (domain := Cases.C037.initial 43) (congrArg (Sign.withNegation globalNegation) hnode43) (Eq.refl Bool.true))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Cases.C037.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C037.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (domain_from_eq (domain := Cases.C037.initial 46) (congrArg (Sign.withNegation globalNegation) hnode46) (Eq.refl Bool.true))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C037.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (domain_from_eq (domain := Cases.C037.initial 48) (congrArg (Sign.withNegation globalNegation) hnode48) (Eq.refl Bool.true))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C037.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (top_allows (Sign.withNegation globalNegation (assignment 50)))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C037.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (domain_from_eq (domain := Cases.C037.initial 52) (congrArg (Sign.withNegation globalNegation) hnode52) (Eq.refl Bool.true))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Cases.C037.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Cases.C037.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (domain_from_eq (domain := Cases.C037.initial 55) (congrArg (Sign.withNegation globalNegation) hnode55) (Eq.refl Bool.true))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C037.initial 56) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C037.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C037.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C037.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C037.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Cases.C037.initial 61) (congrArg (Sign.withNegation globalNegation) hnode61) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C037.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C037.initial 63) (congrArg (Sign.withNegation globalNegation) hnode63) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C037.initial 64) (congrArg (Sign.withNegation globalNegation) hnode64) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (domain_from_eq (domain := Cases.C037.initial 65) (congrArg (Sign.withNegation globalNegation) hnode65) (Eq.refl Bool.true))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C037.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (top_allows (Sign.withNegation globalNegation (assignment 67)))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C037.initial 68) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C037.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C037.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C037.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C037.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C037.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C037.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Cases.C037.initial 75) (congrArg (Sign.withNegation globalNegation) hnode75) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (top_allows (Sign.withNegation globalNegation (assignment 76)))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C037.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C037.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C037.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (domain_from_eq (domain := Cases.C037.initial 80) (congrArg (Sign.withNegation globalNegation) hnode80) (Eq.refl Bool.true))
  let bounded82 := below_succ bounded81 (top_allows (Sign.withNegation globalNegation (assignment 81)))
  let bounded83 := below_succ bounded82 (top_allows (Sign.withNegation globalNegation (assignment 82)))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C037.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (domain_from_eq (domain := Cases.C037.initial 84) (congrArg (Sign.withNegation globalNegation) hnode84) (Eq.refl Bool.true))
  let bounded86 := below_succ bounded85 (top_allows (Sign.withNegation globalNegation (assignment 85)))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C037.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C037.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (top_allows (Sign.withNegation globalNegation (assignment 88)))
  let bounded90 := below_succ bounded89 (domain_from_eq (domain := Cases.C037.initial 89) (congrArg (Sign.withNegation globalNegation) hnode89) (Eq.refl Bool.true))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C037.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C037.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C037.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C037.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C037.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C037.initial 95) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C037.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (domain_from_eq (domain := Cases.C037.initial 97) (congrArg (Sign.withNegation globalNegation) hnode97) (Eq.refl Bool.true))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C037.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C037.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C037.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C037.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C037.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C037.initial 103) (congrArg (Sign.withNegation globalNegation) hnode103) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C037.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (top_allows (Sign.withNegation globalNegation (assignment 105)))
  let bounded107 := below_succ bounded106 (top_allows (Sign.withNegation globalNegation (assignment 106)))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C037.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C037.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (top_allows (Sign.withNegation globalNegation (assignment 109)))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C037.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C037.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (top_allows (Sign.withNegation globalNegation (assignment 112)))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C037.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C037.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C037.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C037.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C037.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C037.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C037.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C037.initial 120) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C037.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (top_allows (Sign.withNegation globalNegation (assignment 122)))
  let bounded124 := below_succ bounded123 (top_allows (Sign.withNegation globalNegation (assignment 123)))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C037.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Cases.C037.initial 125) (congrArg (Sign.withNegation globalNegation) hnode125) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (domain_from_eq (domain := Cases.C037.initial 126) (congrArg (Sign.withNegation globalNegation) hnode126) (Eq.refl Bool.true))
  let bounded128 := below_succ bounded127 (top_allows (Sign.withNegation globalNegation (assignment 127)))
  let bounded129 := below_succ bounded128 (top_allows (Sign.withNegation globalNegation (assignment 128)))
  let bounded130 := below_succ bounded129 (domain_from_eq (domain := Cases.C037.initial 129) (congrArg (Sign.withNegation globalNegation) hnode129) (Eq.refl Bool.true))
  let bounded131 := below_succ bounded130 (top_allows (Sign.withNegation globalNegation (assignment 130)))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C037.initial 131) (congrArg (Sign.withNegation globalNegation) hnode131) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C037.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C037.initial 133) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C037.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (top_allows (Sign.withNegation globalNegation (assignment 135)))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C037.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C037.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C037.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (top_allows (Sign.withNegation globalNegation (assignment 139)))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C037.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C037.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (top_allows (Sign.withNegation globalNegation (assignment 142)))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C037.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C037.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C037.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (top_allows (Sign.withNegation globalNegation (assignment 146)))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C037.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (top_allows (Sign.withNegation globalNegation (assignment 148)))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C037.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C037.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C037.initial 151) (congrArg (Sign.withNegation globalNegation) hnode151) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C037.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C037.initial 153) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (domain_from_eq (domain := Cases.C037.initial 154) (congrArg (Sign.withNegation globalNegation) hnode154) (Eq.refl Bool.true))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C037.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C037.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C037.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C037.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C037.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C037.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (domain_from_eq (domain := Cases.C037.initial 161) (congrArg (Sign.withNegation globalNegation) hnode161) (Eq.refl Bool.true))
  let bounded163 := below_succ bounded162 (top_allows (Sign.withNegation globalNegation (assignment 162)))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C037.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C037.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C037.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (top_allows (Sign.withNegation globalNegation (assignment 166)))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C037.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (top_allows (Sign.withNegation globalNegation (assignment 168)))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C037.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (top_allows (Sign.withNegation globalNegation (assignment 170)))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C037.initial 171) (congrArg (Sign.withNegation globalNegation) hnode171) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C037.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C037.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C037.initial 174) (congrArg (Sign.withNegation globalNegation) hnode174) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (top_allows (Sign.withNegation globalNegation (assignment 175)))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C037.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Cases.C037.initial 177) (congrArg (Sign.withNegation globalNegation) hnode177) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C037.initial 178) (congrArg (Sign.withNegation globalNegation) hnode178) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (top_allows (Sign.withNegation globalNegation (assignment 179)))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C037.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C037.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C037.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C037.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Cases.C037.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C037.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (top_allows (Sign.withNegation globalNegation (assignment 186)))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C037.initial 187) (congrArg (Sign.withNegation globalNegation) hnode187) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C037.initial 188) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C037.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C037.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C037.initial 191) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C037.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C037.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Cases.C037.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C037.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (domain_from_eq (domain := Cases.C037.initial 196) (congrArg (Sign.withNegation globalNegation) hnode196) (Eq.refl Bool.true))
  let bounded198 := below_succ bounded197 (domain_from_eq (domain := Cases.C037.initial 197) (congrArg (Sign.withNegation globalNegation) hnode197) (Eq.refl Bool.true))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Cases.C037.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (domain_from_eq (domain := Cases.C037.initial 199) (congrArg (Sign.withNegation globalNegation) hnode199) (Eq.refl Bool.true))
  let bounded201 := below_succ bounded200 (domain_from_eq (domain := Cases.C037.initial 200) (congrArg (Sign.withNegation globalNegation) hnode200) (Eq.refl Bool.true))
  let bounded202 := below_succ bounded201 (top_allows (Sign.withNegation globalNegation (assignment 201)))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C037.initial 202) (congrArg (Sign.withNegation globalNegation) hnode202) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (domain_from_eq (domain := Cases.C037.initial 203) (congrArg (Sign.withNegation globalNegation) hnode203) (Eq.refl Bool.true))
  let bounded205 := below_succ bounded204 (top_allows (Sign.withNegation globalNegation (assignment 204)))
  let bounded206 := below_succ bounded205 (top_allows (Sign.withNegation globalNegation (assignment 205)))
  let bounded207 := below_succ bounded206 (top_allows (Sign.withNegation globalNegation (assignment 206)))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Cases.C037.initial 207) (congrArg (Sign.withNegation globalNegation) hnode207) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C037.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C037.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (top_allows (Sign.withNegation globalNegation (assignment 210)))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C037.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C037.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (top_allows (Sign.withNegation globalNegation (assignment 213)))
  let bounded215 := below_succ bounded214 (top_allows (Sign.withNegation globalNegation (assignment 214)))
  let bounded216 := below_succ bounded215 (domain_from_eq (domain := Cases.C037.initial 215) (congrArg (Sign.withNegation globalNegation) hnode215) (Eq.refl Bool.true))
  let bounded217 := below_succ bounded216 (top_allows (Sign.withNegation globalNegation (assignment 216)))
  let bounded218 := below_succ bounded217 (top_allows (Sign.withNegation globalNegation (assignment 217)))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C037.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (top_allows (Sign.withNegation globalNegation (assignment 219)))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C037.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (domain_from_eq (domain := Cases.C037.initial 221) (congrArg (Sign.withNegation globalNegation) hnode221) (Eq.refl Bool.true))
  let bounded223 := below_succ bounded222 (top_allows (Sign.withNegation globalNegation (assignment 222)))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C037.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (top_allows (Sign.withNegation globalNegation (assignment 224)))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C037.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C037.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C037.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C037.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (top_allows (Sign.withNegation globalNegation (assignment 229)))
  let bounded231 := below_succ bounded230 (top_allows (Sign.withNegation globalNegation (assignment 230)))
  let bounded232 := below_succ bounded231 (domain_from_eq (domain := Cases.C037.initial 231) (congrArg (Sign.withNegation globalNegation) hnode231) (Eq.refl Bool.true))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C037.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (domain_from_eq (domain := Cases.C037.initial 233) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded235 := below_succ bounded234 (top_allows (Sign.withNegation globalNegation (assignment 234)))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C037.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (domain_from_eq (domain := Cases.C037.initial 236) (congrArg (Sign.withNegation globalNegation) hnode236) (Eq.refl Bool.true))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C037.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C037.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Cases.C037.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (domain_from_eq (domain := Cases.C037.initial 240) (congrArg (Sign.withNegation globalNegation) hnode240) (Eq.refl Bool.true))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C037.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C037.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C037.initial 243) (congrArg (Sign.withNegation globalNegation) hnode243) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (top_allows (Sign.withNegation globalNegation (assignment 244)))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C037.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C037.initial 246) (congrArg (Sign.withNegation globalNegation) hnode246) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C037.initial 247) (congrArg (Sign.withNegation globalNegation) hnode247) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C037.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (domain_from_eq (domain := Cases.C037.initial 249) (congrArg (Sign.withNegation globalNegation) hnode249) (Eq.refl Bool.true))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Cases.C037.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C037.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C037.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C037
#print axioms Papers.RationalityTen.PureGP.Initializers.C037.support_sign_contradiction
