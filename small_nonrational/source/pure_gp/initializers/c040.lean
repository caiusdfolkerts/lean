module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C040

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C040
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 3
def globalNegation : Bool := Bool.true
def edgeTable : Table SupportEdge := (Table.node 112 (Table.node 56 (Table.node 28 (Table.node 14 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 6 21 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 6 36 Bool.false)) (Table.leaf (SupportEdge.mk 6 37 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 6 38 Bool.false)) (Table.leaf (SupportEdge.mk 10 25 Bool.false))) (Table.node 6 (Table.leaf (SupportEdge.mk 10 42 Bool.true)) (Table.leaf (SupportEdge.mk 10 44 Bool.true))))) (Table.node 10 (Table.node 8 (Table.leaf (SupportEdge.mk 10 45 Bool.true)) (Table.node 9 (Table.leaf (SupportEdge.mk 14 29 Bool.false)) (Table.leaf (SupportEdge.mk 14 48 Bool.true)))) (Table.node 12 (Table.node 11 (Table.leaf (SupportEdge.mk 14 50 Bool.true)) (Table.leaf (SupportEdge.mk 14 51 Bool.true))) (Table.node 13 (Table.leaf (SupportEdge.mk 74 94 Bool.false)) (Table.leaf (SupportEdge.mk 74 113 Bool.false)))))) (Table.node 21 (Table.node 17 (Table.node 15 (Table.leaf (SupportEdge.mk 74 115 Bool.false)) (Table.node 16 (Table.leaf (SupportEdge.mk 74 116 Bool.false)) (Table.leaf (SupportEdge.mk 144 164 Bool.false)))) (Table.node 19 (Table.node 18 (Table.leaf (SupportEdge.mk 144 183 Bool.false)) (Table.leaf (SupportEdge.mk 144 185 Bool.false))) (Table.node 20 (Table.leaf (SupportEdge.mk 144 186 Bool.false)) (Table.leaf (SupportEdge.mk 3 58 Bool.false))))) (Table.node 24 (Table.node 22 (Table.leaf (SupportEdge.mk 3 62 Bool.false)) (Table.node 23 (Table.leaf (SupportEdge.mk 3 65 Bool.false)) (Table.leaf (SupportEdge.mk 3 69 Bool.true)))) (Table.node 26 (Table.node 25 (Table.leaf (SupportEdge.mk 4 59 Bool.false)) (Table.leaf (SupportEdge.mk 4 63 Bool.false))) (Table.node 27 (Table.leaf (SupportEdge.mk 4 66 Bool.false)) (Table.leaf (SupportEdge.mk 4 70 Bool.true))))))) (Table.node 42 (Table.node 35 (Table.node 31 (Table.node 29 (Table.leaf (SupportEdge.mk 18 78 Bool.true)) (Table.node 30 (Table.leaf (SupportEdge.mk 18 84 Bool.true)) (Table.leaf (SupportEdge.mk 18 87 Bool.true)))) (Table.node 33 (Table.node 32 (Table.leaf (SupportEdge.mk 18 90 Bool.true)) (Table.leaf (SupportEdge.mk 33 98 Bool.true))) (Table.node 34 (Table.leaf (SupportEdge.mk 33 104 Bool.true)) (Table.leaf (SupportEdge.mk 33 107 Bool.true))))) (Table.node 38 (Table.node 36 (Table.leaf (SupportEdge.mk 33 110 Bool.true)) (Table.node 37 (Table.leaf (SupportEdge.mk 138 203 Bool.false)) (Table.leaf (SupportEdge.mk 138 209 Bool.false)))) (Table.node 40 (Table.node 39 (Table.leaf (SupportEdge.mk 138 212 Bool.false)) (Table.leaf (SupportEdge.mk 138 215 Bool.false))) (Table.node 41 (Table.leaf (SupportEdge.mk 21 56 Bool.false)) (Table.leaf (SupportEdge.mk 21 91 Bool.true)))))) (Table.node 49 (Table.node 45 (Table.node 43 (Table.leaf (SupportEdge.mk 21 92 Bool.true)) (Table.node 44 (Table.leaf (SupportEdge.mk 21 94 Bool.true)) (Table.leaf (SupportEdge.mk 24 59 Bool.false)))) (Table.node 47 (Table.node 46 (Table.leaf (SupportEdge.mk 24 96 Bool.false)) (Table.leaf (SupportEdge.mk 24 98 Bool.false))) (Table.node 48 (Table.leaf (SupportEdge.mk 24 100 Bool.true)) (Table.leaf (SupportEdge.mk 28 63 Bool.false))))) (Table.node 52 (Table.node 50 (Table.leaf (SupportEdge.mk 28 102 Bool.false)) (Table.node 51 (Table.leaf (SupportEdge.mk 28 104 Bool.false)) (Table.leaf (SupportEdge.mk 28 106 Bool.true)))) (Table.node 54 (Table.node 53 (Table.leaf (SupportEdge.mk 38 73 Bool.false)) (Table.leaf (SupportEdge.mk 38 112 Bool.false))) (Table.node 55 (Table.leaf (SupportEdge.mk 38 114 Bool.false)) (Table.leaf (SupportEdge.mk 38 116 Bool.true)))))))) (Table.node 84 (Table.node 70 (Table.node 63 (Table.node 59 (Table.node 57 (Table.leaf (SupportEdge.mk 163 198 Bool.false)) (Table.node 58 (Table.leaf (SupportEdge.mk 163 232 Bool.true)) (Table.leaf (SupportEdge.mk 163 234 Bool.true)))) (Table.node 61 (Table.node 60 (Table.leaf (SupportEdge.mk 163 236 Bool.false)) (Table.leaf (SupportEdge.mk 27 62 Bool.false))) (Table.node 62 (Table.leaf (SupportEdge.mk 27 92 Bool.true)) (Table.leaf (SupportEdge.mk 27 101 Bool.false))))) (Table.node 66 (Table.node 64 (Table.leaf (SupportEdge.mk 27 104 Bool.true)) (Table.node 65 (Table.leaf (SupportEdge.mk 29 64 Bool.false)) (Table.leaf (SupportEdge.mk 29 94 Bool.true)))) (Table.node 68 (Table.node 67 (Table.leaf (SupportEdge.mk 29 103 Bool.false)) (Table.leaf (SupportEdge.mk 29 106 Bool.false))) (Table.node 69 (Table.leaf (SupportEdge.mk 34 69 Bool.false)) (Table.leaf (SupportEdge.mk 34 99 Bool.true)))))) (Table.node 77 (Table.node 73 (Table.node 71 (Table.leaf (SupportEdge.mk 34 108 Bool.true)) (Table.node 72 (Table.leaf (SupportEdge.mk 34 110 Bool.false)) (Table.leaf (SupportEdge.mk 50 85 Bool.false)))) (Table.node 75 (Table.node 74 (Table.leaf (SupportEdge.mk 50 115 Bool.false)) (Table.leaf (SupportEdge.mk 50 122 Bool.true))) (Table.node 76 (Table.leaf (SupportEdge.mk 50 124 Bool.false)) (Table.leaf (SupportEdge.mk 175 210 Bool.false))))) (Table.node 80 (Table.node 78 (Table.leaf (SupportEdge.mk 175 235 Bool.true)) (Table.node 79 (Table.leaf (SupportEdge.mk 175 242 Bool.false)) (Table.leaf (SupportEdge.mk 175 244 Bool.true)))) (Table.node 82 (Table.node 81 (Table.leaf (SupportEdge.mk 40 75 Bool.false)) (Table.leaf (SupportEdge.mk 40 95 Bool.false))) (Table.node 83 (Table.leaf (SupportEdge.mk 40 111 Bool.true)) (Table.leaf (SupportEdge.mk 40 118 Bool.true))))))) (Table.node 98 (Table.node 91 (Table.node 87 (Table.node 85 (Table.leaf (SupportEdge.mk 41 76 Bool.false)) (Table.node 86 (Table.leaf (SupportEdge.mk 41 96 Bool.false)) (Table.leaf (SupportEdge.mk 41 112 Bool.true)))) (Table.node 89 (Table.node 88 (Table.leaf (SupportEdge.mk 41 119 Bool.true)) (Table.leaf (SupportEdge.mk 43 78 Bool.false))) (Table.node 90 (Table.leaf (SupportEdge.mk 43 98 Bool.false)) (Table.leaf (SupportEdge.mk 43 114 Bool.true))))) (Table.node 94 (Table.node 92 (Table.leaf (SupportEdge.mk 43 120 Bool.true)) (Table.node 93 (Table.leaf (SupportEdge.mk 52 87 Bool.false)) (Table.leaf (SupportEdge.mk 52 107 Bool.false)))) (Table.node 96 (Table.node 95 (Table.leaf (SupportEdge.mk 52 121 Bool.false)) (Table.leaf (SupportEdge.mk 52 125 Bool.true))) (Table.node 97 (Table.leaf (SupportEdge.mk 187 222 Bool.false)) (Table.leaf (SupportEdge.mk 187 237 Bool.false)))))) (Table.node 105 (Table.node 101 (Table.node 99 (Table.leaf (SupportEdge.mk 187 246 Bool.true)) (Table.node 100 (Table.leaf (SupportEdge.mk 187 250 Bool.false)) (Table.leaf (SupportEdge.mk 44 79 Bool.false)))) (Table.node 103 (Table.node 102 (Table.leaf (SupportEdge.mk 44 99 Bool.false)) (Table.leaf (SupportEdge.mk 44 115 Bool.true))) (Table.node 104 (Table.leaf (SupportEdge.mk 44 118 Bool.true)) (Table.leaf (SupportEdge.mk 44 120 Bool.false))))) (Table.node 108 (Table.node 106 (Table.leaf (SupportEdge.mk 3 128 Bool.true)) (Table.node 107 (Table.leaf (SupportEdge.mk 3 132 Bool.true)) (Table.leaf (SupportEdge.mk 3 135 Bool.true)))) (Table.node 110 (Table.node 109 (Table.leaf (SupportEdge.mk 3 138 Bool.false)) (Table.leaf (SupportEdge.mk 5 130 Bool.true))) (Table.node 111 (Table.leaf (SupportEdge.mk 5 134 Bool.true)) (Table.leaf (SupportEdge.mk 5 137 Bool.true))))))))) (Table.node 168 (Table.node 140 (Table.node 126 (Table.node 119 (Table.node 115 (Table.node 113 (Table.leaf (SupportEdge.mk 5 140 Bool.true)) (Table.node 114 (Table.leaf (SupportEdge.mk 19 149 Bool.false)) (Table.leaf (SupportEdge.mk 19 155 Bool.false)))) (Table.node 117 (Table.node 116 (Table.leaf (SupportEdge.mk 19 158 Bool.false)) (Table.leaf (SupportEdge.mk 19 160 Bool.true))) (Table.node 118 (Table.leaf (SupportEdge.mk 34 169 Bool.false)) (Table.leaf (SupportEdge.mk 34 175 Bool.false))))) (Table.node 122 (Table.node 120 (Table.leaf (SupportEdge.mk 34 178 Bool.false)) (Table.node 121 (Table.leaf (SupportEdge.mk 34 180 Bool.true)) (Table.leaf (SupportEdge.mk 69 204 Bool.false)))) (Table.node 124 (Table.node 123 (Table.leaf (SupportEdge.mk 69 210 Bool.false)) (Table.leaf (SupportEdge.mk 69 213 Bool.false))) (Table.node 125 (Table.leaf (SupportEdge.mk 69 215 Bool.true)) (Table.leaf (SupportEdge.mk 7 127 Bool.false)))))) (Table.node 133 (Table.node 129 (Table.node 127 (Table.leaf (SupportEdge.mk 7 141 Bool.true)) (Table.node 128 (Table.leaf (SupportEdge.mk 7 146 Bool.false)) (Table.leaf (SupportEdge.mk 7 147 Bool.false)))) (Table.node 131 (Table.node 130 (Table.leaf (SupportEdge.mk 8 128 Bool.false)) (Table.leaf (SupportEdge.mk 8 142 Bool.true))) (Table.node 132 (Table.leaf (SupportEdge.mk 8 148 Bool.false)) (Table.leaf (SupportEdge.mk 8 149 Bool.false))))) (Table.node 136 (Table.node 134 (Table.leaf (SupportEdge.mk 15 135 Bool.false)) (Table.node 135 (Table.leaf (SupportEdge.mk 15 151 Bool.false)) (Table.leaf (SupportEdge.mk 15 157 Bool.false)))) (Table.node 138 (Table.node 137 (Table.leaf (SupportEdge.mk 15 158 Bool.false)) (Table.leaf (SupportEdge.mk 40 165 Bool.true))) (Table.node 139 (Table.leaf (SupportEdge.mk 40 181 Bool.false)) (Table.leaf (SupportEdge.mk 40 187 Bool.false))))))) (Table.node 154 (Table.node 147 (Table.node 143 (Table.node 141 (Table.leaf (SupportEdge.mk 40 188 Bool.false)) (Table.node 142 (Table.leaf (SupportEdge.mk 75 200 Bool.true)) (Table.leaf (SupportEdge.mk 75 216 Bool.false)))) (Table.node 145 (Table.node 144 (Table.leaf (SupportEdge.mk 75 222 Bool.false)) (Table.leaf (SupportEdge.mk 75 223 Bool.false))) (Table.node 146 (Table.leaf (SupportEdge.mk 11 131 Bool.false)) (Table.leaf (SupportEdge.mk 11 141 Bool.false))))) (Table.node 150 (Table.node 148 (Table.leaf (SupportEdge.mk 11 151 Bool.false)) (Table.node 149 (Table.leaf (SupportEdge.mk 11 152 Bool.false)) (Table.leaf (SupportEdge.mk 14 134 Bool.false)))) (Table.node 152 (Table.node 151 (Table.leaf (SupportEdge.mk 14 144 Bool.false)) (Table.leaf (SupportEdge.mk 14 155 Bool.true))) (Table.node 153 (Table.leaf (SupportEdge.mk 14 156 Bool.true)) (Table.leaf (SupportEdge.mk 17 137 Bool.false)))))) (Table.node 161 (Table.node 157 (Table.node 155 (Table.leaf (SupportEdge.mk 17 147 Bool.false)) (Table.node 156 (Table.leaf (SupportEdge.mk 17 158 Bool.true)) (Table.leaf (SupportEdge.mk 17 159 Bool.true)))) (Table.node 159 (Table.node 158 (Table.leaf (SupportEdge.mk 48 173 Bool.true)) (Table.leaf (SupportEdge.mk 48 183 Bool.true))) (Table.node 160 (Table.leaf (SupportEdge.mk 48 192 Bool.true)) (Table.leaf (SupportEdge.mk 48 193 Bool.true))))) (Table.node 164 (Table.node 162 (Table.leaf (SupportEdge.mk 83 208 Bool.true)) (Table.node 163 (Table.leaf (SupportEdge.mk 83 218 Bool.true)) (Table.leaf (SupportEdge.mk 83 227 Bool.true)))) (Table.node 166 (Table.node 165 (Table.leaf (SupportEdge.mk 83 228 Bool.true)) (Table.leaf (SupportEdge.mk 36 141 Bool.true))) (Table.node 167 (Table.leaf (SupportEdge.mk 36 161 Bool.true)) (Table.leaf (SupportEdge.mk 36 181 Bool.false)))))))) (Table.node 196 (Table.node 182 (Table.node 175 (Table.node 171 (Table.node 169 (Table.leaf (SupportEdge.mk 36 183 Bool.false)) (Table.node 170 (Table.leaf (SupportEdge.mk 38 143 Bool.true)) (Table.leaf (SupportEdge.mk 38 163 Bool.true)))) (Table.node 173 (Table.node 172 (Table.leaf (SupportEdge.mk 38 184 Bool.true)) (Table.leaf (SupportEdge.mk 38 186 Bool.false))) (Table.node 174 (Table.leaf (SupportEdge.mk 41 146 Bool.true)) (Table.leaf (SupportEdge.mk 41 166 Bool.true))))) (Table.node 178 (Table.node 176 (Table.leaf (SupportEdge.mk 41 187 Bool.true)) (Table.node 177 (Table.leaf (SupportEdge.mk 41 189 Bool.false)) (Table.leaf (SupportEdge.mk 47 152 Bool.true)))) (Table.node 180 (Table.node 179 (Table.leaf (SupportEdge.mk 47 172 Bool.true)) (Table.leaf (SupportEdge.mk 47 191 Bool.true))) (Table.node 181 (Table.leaf (SupportEdge.mk 47 193 Bool.false)) (Table.leaf (SupportEdge.mk 112 217 Bool.false)))))) (Table.node 189 (Table.node 185 (Table.node 183 (Table.leaf (SupportEdge.mk 112 232 Bool.false)) (Table.node 184 (Table.leaf (SupportEdge.mk 112 246 Bool.true)) (Table.leaf (SupportEdge.mk 112 248 Bool.false)))) (Table.node 187 (Table.node 186 (Table.leaf (SupportEdge.mk 44 149 Bool.true)) (Table.leaf (SupportEdge.mk 44 169 Bool.true))) (Table.node 188 (Table.leaf (SupportEdge.mk 44 185 Bool.false)) (Table.leaf (SupportEdge.mk 44 188 Bool.false))))) (Table.node 192 (Table.node 190 (Table.leaf (SupportEdge.mk 44 190 Bool.true)) (Table.node 191 (Table.leaf (SupportEdge.mk 66 136 Bool.false)) (Table.leaf (SupportEdge.mk 66 201 Bool.false)))) (Table.node 194 (Table.node 193 (Table.leaf (SupportEdge.mk 66 207 Bool.false)) (Table.leaf (SupportEdge.mk 66 212 Bool.true))) (Table.node 195 (Table.leaf (SupportEdge.mk 67 137 Bool.false)) (Table.leaf (SupportEdge.mk 67 202 Bool.false))))))) (Table.node 210 (Table.node 203 (Table.node 199 (Table.node 197 (Table.leaf (SupportEdge.mk 67 208 Bool.false)) (Table.node 198 (Table.leaf (SupportEdge.mk 67 213 Bool.true)) (Table.leaf (SupportEdge.mk 70 140 Bool.false)))) (Table.node 201 (Table.node 200 (Table.leaf (SupportEdge.mk 70 205 Bool.false)) (Table.leaf (SupportEdge.mk 70 211 Bool.false))) (Table.node 202 (Table.leaf (SupportEdge.mk 70 215 Bool.false)) (Table.leaf (SupportEdge.mk 89 159 Bool.false))))) (Table.node 206 (Table.node 204 (Table.leaf (SupportEdge.mk 89 224 Bool.true)) (Table.node 205 (Table.leaf (SupportEdge.mk 89 228 Bool.true)) (Table.leaf (SupportEdge.mk 89 230 Bool.false)))) (Table.node 208 (Table.node 207 (Table.leaf (SupportEdge.mk 109 179 Bool.false)) (Table.leaf (SupportEdge.mk 109 239 Bool.true))) (Table.node 209 (Table.leaf (SupportEdge.mk 109 243 Bool.true)) (Table.leaf (SupportEdge.mk 109 245 Bool.false)))))) (Table.node 217 (Table.node 213 (Table.node 211 (Table.leaf (SupportEdge.mk 87 157 Bool.false)) (Table.node 212 (Table.leaf (SupportEdge.mk 87 212 Bool.true)) (Table.leaf (SupportEdge.mk 87 222 Bool.true)))) (Table.node 215 (Table.node 214 (Table.leaf (SupportEdge.mk 87 226 Bool.true)) (Table.leaf (SupportEdge.mk 87 230 Bool.false))) (Table.node 216 (Table.leaf (SupportEdge.mk 106 176 Bool.false)) (Table.leaf (SupportEdge.mk 106 211 Bool.false))))) (Table.node 221 (Table.node 219 (Table.node 218 (Table.leaf (SupportEdge.mk 106 236 Bool.true)) (Table.leaf (SupportEdge.mk 106 243 Bool.false))) (Table.node 220 (Table.leaf (SupportEdge.mk 106 244 Bool.false)) (Table.leaf (SupportEdge.mk 123 193 Bool.false)))) (Table.node 223 (Table.node 222 (Table.leaf (SupportEdge.mk 123 228 Bool.false)) (Table.leaf (SupportEdge.mk 123 243 Bool.false))) (Table.node 224 (Table.leaf (SupportEdge.mk 123 248 Bool.false)) (Table.leaf (SupportEdge.mk 123 251 Bool.false))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 5 (Table.node 2 (Table.node 1 (Table.leaf 39) (Table.leaf 68)) (Table.node 3 (Table.leaf 93) (Table.node 4 (Table.leaf 105) (Table.leaf 117)))) (Table.node 7 (Table.node 6 (Table.leaf 139) (Table.leaf 145)) (Table.node 8 (Table.leaf 153) (Table.node 9 (Table.leaf 182) (Table.leaf 214)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 225 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 10 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C040.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode58 : Eq (assignment 58) Sign.positive :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode62 : Eq (assignment 62) Sign.positive :=
    Eq.trans (h_support 21 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode65 : Eq (assignment 65) Sign.positive :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode69 : Eq (assignment 69) Sign.negative :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode128 : Eq (assignment 128) Sign.negative :=
    Eq.trans (h_support 105 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode132 : Eq (assignment 132) Sign.negative :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode135 : Eq (assignment 135) Sign.negative :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode138 : Eq (assignment 138) Sign.positive :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode8 : Eq (assignment 8) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 129 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode128)
  let hnode15 : Eq (assignment 15) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 133 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode135)
  let hnode27 : Eq (assignment 27) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 60 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode62)
  let hnode34 : Eq (assignment 34) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 68 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode203 : Eq (assignment 203) Sign.positive :=
    Eq.trans (h_support 36 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode138)
  let hnode204 : Eq (assignment 204) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode209 : Eq (assignment 209) Sign.positive :=
    Eq.trans (h_support 37 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode138)
  let hnode210 : Eq (assignment 210) Sign.negative :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode212 : Eq (assignment 212) Sign.positive :=
    Eq.trans (h_support 38 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode138)
  let hnode213 : Eq (assignment 213) Sign.negative :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode215 : Eq (assignment 215) Sign.positive :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode69)
  let hnode66 : Eq (assignment 66) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 193 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode212)
  let hnode67 : Eq (assignment 67) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 197 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode213)
  let hnode70 : Eq (assignment 70) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 201 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode215)
  let hnode87 : Eq (assignment 87) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 211 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode212)
  let hnode92 : Eq (assignment 92) Sign.negative :=
    Eq.trans (h_support 61 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode99 : Eq (assignment 99) Sign.positive :=
    Eq.trans (h_support 69 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode101 : Eq (assignment 101) Sign.positive :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode104 : Eq (assignment 104) Sign.negative :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode108 : Eq (assignment 108) Sign.positive :=
    Eq.trans (h_support 70 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode110 : Eq (assignment 110) Sign.negative :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode142 : Eq (assignment 142) Sign.positive :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode148 : Eq (assignment 148) Sign.negative :=
    Eq.trans (h_support 131 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode149 : Eq (assignment 149) Sign.negative :=
    Eq.trans (h_support 132 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode151 : Eq (assignment 151) Sign.negative :=
    Eq.trans (h_support 134 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode157 : Eq (assignment 157) Sign.negative :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode158 : Eq (assignment 158) Sign.negative :=
    Eq.trans (h_support 136 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode169 : Eq (assignment 169) Sign.negative :=
    Eq.trans (h_support 117 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode175 : Eq (assignment 175) Sign.negative :=
    Eq.trans (h_support 118 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode178 : Eq (assignment 178) Sign.negative :=
    Eq.trans (h_support 119 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode180 : Eq (assignment 180) Sign.positive :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode4 : Eq (assignment 4) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 27 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode70)
  let hnode11 : Eq (assignment 11) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 147 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode151)
  let hnode17 : Eq (assignment 17) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 155 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode158)
  let hnode18 : Eq (assignment 18) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 30 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode87)
  let hnode19 : Eq (assignment 19) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 113 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode149)
  let hnode21 : Eq (assignment 21) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 42 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode92)
  let hnode28 : Eq (assignment 28) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 50 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode33 : Eq (assignment 33) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 33 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode104)
  let hnode44 : Eq (assignment 44) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 101 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode99)
  let hnode52 : Eq (assignment 52) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 92 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode87)
  let hnode136 : Eq (assignment 136) Sign.negative :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode137 : Eq (assignment 137) Sign.positive :=
    Eq.trans (h_support 194 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode67)
  let hnode140 : Eq (assignment 140) Sign.positive :=
    Eq.trans (h_support 198 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode201 : Eq (assignment 201) Sign.negative :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode202 : Eq (assignment 202) Sign.positive :=
    Eq.trans (h_support 195 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode67)
  let hnode205 : Eq (assignment 205) Sign.positive :=
    Eq.trans (h_support 199 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode207 : Eq (assignment 207) Sign.negative :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode208 : Eq (assignment 208) Sign.positive :=
    Eq.trans (h_support 196 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode67)
  let hnode211 : Eq (assignment 211) Sign.positive :=
    Eq.trans (h_support 200 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode222 : Eq (assignment 222) Sign.positive :=
    Eq.trans (h_support 212 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode87)
  let hnode226 : Eq (assignment 226) Sign.positive :=
    Eq.trans (h_support 213 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode87)
  let hnode230 : Eq (assignment 230) Sign.negative :=
    Eq.trans (h_support 214 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode87)
  let hnode235 : Eq (assignment 235) Sign.positive :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode175)
  let hnode242 : Eq (assignment 242) Sign.negative :=
    Eq.trans (h_support 78 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode175)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 79 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode175)
  let hnode5 : Eq (assignment 5) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 111 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode137)
  let hnode6 : Eq (assignment 6) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 0 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode21)
  let hnode10 : Eq (assignment 10) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 6 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode56 : Eq (assignment 56) Sign.positive :=
    Eq.trans (h_support 40 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode21)
  let hnode59 : Eq (assignment 59) Sign.negative :=
    Eq.trans (h_support 24 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode4)
  let hnode63 : Eq (assignment 63) Sign.negative :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode75 : Eq (assignment 75) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 143 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode222)
  let hnode78 : Eq (assignment 78) Sign.negative :=
    Eq.trans (h_support 28 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode79 : Eq (assignment 79) Sign.positive :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode83 : Eq (assignment 83) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 161 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode208)
  let hnode84 : Eq (assignment 84) Sign.negative :=
    Eq.trans (h_support 29 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode89 : Eq (assignment 89) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 205 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode230)
  let hnode90 : Eq (assignment 90) Sign.negative :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode18)
  let hnode91 : Eq (assignment 91) Sign.negative :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode94 : Eq (assignment 94) Sign.negative :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode98 : Eq (assignment 98) Sign.negative :=
    Eq.trans (h_support 32 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode102 : Eq (assignment 102) Sign.negative :=
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode106 : Eq (assignment 106) Sign.positive :=
    Eq.trans (h_support 51 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode107 : Eq (assignment 107) Sign.negative :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode115 : Eq (assignment 115) Sign.negative :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode118 : Eq (assignment 118) Sign.negative :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode120 : Eq (assignment 120) Sign.positive :=
    Eq.trans (h_support 104 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode121 : Eq (assignment 121) Sign.negative :=
    Eq.trans (h_support 94 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode52)
  let hnode125 : Eq (assignment 125) Sign.positive :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode52)
  let hnode131 : Eq (assignment 131) Sign.negative :=
    Eq.trans (h_support 145 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode141 : Eq (assignment 141) Sign.negative :=
    Eq.trans (h_support 146 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode147 : Eq (assignment 147) Sign.positive :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode152 : Eq (assignment 152) Sign.negative :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode155 : Eq (assignment 155) Sign.negative :=
    Eq.trans (h_support 114 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode159 : Eq (assignment 159) Sign.negative :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode160 : Eq (assignment 160) Sign.positive :=
    Eq.trans (h_support 116 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode19)
  let hnode185 : Eq (assignment 185) Sign.positive :=
    Eq.trans (h_support 187 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode187 : Eq (assignment 187) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 96 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode222)
  let hnode188 : Eq (assignment 188) Sign.positive :=
    Eq.trans (h_support 188 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode190 : Eq (assignment 190) Sign.negative :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode7 : Eq (assignment 7) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 126 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode141)
  let hnode14 : Eq (assignment 14) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 151 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode155)
  let hnode24 : Eq (assignment 24) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 46 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode98)
  let hnode25 : Eq (assignment 25) Sign.negative :=
    Eq.trans (h_support 4 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode29 : Eq (assignment 29) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 65 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode94)
  let hnode36 : Eq (assignment 36) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode6)
  let hnode37 : Eq (assignment 37) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode6)
  let hnode38 : Eq (assignment 38) Sign.positive :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode6)
  let hnode40 : Eq (assignment 40) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 83 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode118)
  let hnode41 : Eq (assignment 41) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 175 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode187)
  let hnode42 : Eq (assignment 42) Sign.positive :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode43 : Eq (assignment 43) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 89 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode98)
  let hnode45 : Eq (assignment 45) Sign.positive :=
    Eq.trans (h_support 7 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode47 : Eq (assignment 47) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 177 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode152)
  let hnode50 : Eq (assignment 50) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 73 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode115)
  let hnode74 : Eq (assignment 74) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 12 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode94)
  let hnode130 : Eq (assignment 130) Sign.positive :=
    Eq.trans (h_support 109 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode134 : Eq (assignment 134) Sign.positive :=
    Eq.trans (h_support 110 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode5)
  let hnode144 : Eq (assignment 144) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 18 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode185)
  let hnode176 : Eq (assignment 176) Sign.positive :=
    Eq.trans (h_support 215 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode106)
  let hnode200 : Eq (assignment 200) Sign.negative :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode75)
  let hnode216 : Eq (assignment 216) Sign.positive :=
    Eq.trans (h_support 142 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode75)
  let hnode218 : Eq (assignment 218) Sign.positive :=
    Eq.trans (h_support 162 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode223 : Eq (assignment 223) Sign.positive :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode75)
  let hnode224 : Eq (assignment 224) Sign.positive :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode89)
  let hnode227 : Eq (assignment 227) Sign.positive :=
    Eq.trans (h_support 163 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode228 : Eq (assignment 228) Sign.positive :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode236 : Eq (assignment 236) Sign.negative :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode106)
  let hnode237 : Eq (assignment 237) Sign.positive :=
    Eq.trans (h_support 97 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode187)
  let hnode243 : Eq (assignment 243) Sign.positive :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode106)
  let hnode246 : Eq (assignment 246) Sign.negative :=
    Eq.trans (h_support 98 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode187)
  let hnode250 : Eq (assignment 250) Sign.positive :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode187)
  let hnode48 : Eq (assignment 48) Sign.negative :=
    Eq.trans (h_support 9 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode51 : Eq (assignment 51) Sign.negative :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode64 : Eq (assignment 64) Sign.positive :=
    Eq.trans (h_support 64 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode73 : Eq (assignment 73) Sign.positive :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode76 : Eq (assignment 76) Sign.negative :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode85 : Eq (assignment 85) Sign.negative :=
    Eq.trans (h_support 72 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode50)
  let hnode95 : Eq (assignment 95) Sign.positive :=
    Eq.trans (h_support 81 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode40)
  let hnode96 : Eq (assignment 96) Sign.negative :=
    Eq.trans (h_support 45 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode24)
  let hnode100 : Eq (assignment 100) Sign.positive :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode103 : Eq (assignment 103) Sign.positive :=
    Eq.trans (h_support 66 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode109 : Eq (assignment 109) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 208 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode243)
  let hnode111 : Eq (assignment 111) Sign.negative :=
    Eq.trans (h_support 82 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode112 : Eq (assignment 112) Sign.positive :=
    Eq.trans (h_support 53 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode113 : Eq (assignment 113) Sign.negative :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode74)
  let hnode114 : Eq (assignment 114) Sign.positive :=
    Eq.trans (h_support 54 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode116 : Eq (assignment 116) Sign.negative :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode119 : Eq (assignment 119) Sign.positive :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode122 : Eq (assignment 122) Sign.positive :=
    Eq.trans (h_support 74 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode50)
  let hnode123 : Eq (assignment 123) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 222 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode243)
  let hnode124 : Eq (assignment 124) Sign.negative :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode50)
  let hnode127 : Eq (assignment 127) Sign.positive :=
    Eq.trans (h_support 125 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode7)
  let hnode143 : Eq (assignment 143) Sign.negative :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode146 : Eq (assignment 146) Sign.positive :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode7)
  let hnode156 : Eq (assignment 156) Sign.negative :=
    Eq.trans (h_support 152 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode161 : Eq (assignment 161) Sign.negative :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode36)
  let hnode163 : Eq (assignment 163) Sign.negative :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode164 : Eq (assignment 164) Sign.positive :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode144)
  let hnode165 : Eq (assignment 165) Sign.negative :=
    Eq.trans (h_support 137 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode40)
  let hnode166 : Eq (assignment 166) Sign.positive :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode172 : Eq (assignment 172) Sign.negative :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode181 : Eq (assignment 181) Sign.positive :=
    Eq.trans (h_support 167 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode183 : Eq (assignment 183) Sign.positive :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode184 : Eq (assignment 184) Sign.negative :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode186 : Eq (assignment 186) Sign.positive :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode189 : Eq (assignment 189) Sign.negative :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode191 : Eq (assignment 191) Sign.negative :=
    Eq.trans (h_support 179 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode193 : Eq (assignment 193) Sign.positive :=
    Eq.trans (h_support 180 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode173 : Eq (assignment 173) Sign.positive :=
    Eq.trans (h_support 157 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode109)
  let hnode192 : Eq (assignment 192) Sign.positive :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode198 : Eq (assignment 198) Sign.negative :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode163)
  let hnode217 : Eq (assignment 217) Sign.positive :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode232 : Eq (assignment 232) Sign.positive :=
    Eq.trans (h_support 182 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode234 : Eq (assignment 234) Sign.positive :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode163)
  let hnode239 : Eq (assignment 239) Sign.positive :=
    Eq.trans (h_support 207 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode109)
  let hnode245 : Eq (assignment 245) Sign.negative :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode109)
  let hnode248 : Eq (assignment 248) Sign.positive :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode251 : Eq (assignment 251) Sign.positive :=
    Eq.trans (h_support 224 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode123)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C040.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (top_allows (Sign.withNegation globalNegation (assignment 0)))
  let bounded2 := below_succ bounded1 (top_allows (Sign.withNegation globalNegation (assignment 1)))
  let bounded3 := below_succ bounded2 (top_allows (Sign.withNegation globalNegation (assignment 2)))
  let bounded4 := below_succ bounded3 (domain_from_eq (domain := Cases.C040.initial 3) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C040.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Cases.C040.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Cases.C040.initial 6) (congrArg (Sign.withNegation globalNegation) hnode6) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Cases.C040.initial 7) (congrArg (Sign.withNegation globalNegation) hnode7) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C040.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (top_allows (Sign.withNegation globalNegation (assignment 9)))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C040.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (domain_from_eq (domain := Cases.C040.initial 11) (congrArg (Sign.withNegation globalNegation) hnode11) (Eq.refl Bool.true))
  let bounded13 := below_succ bounded12 (top_allows (Sign.withNegation globalNegation (assignment 12)))
  let bounded14 := below_succ bounded13 (top_allows (Sign.withNegation globalNegation (assignment 13)))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C040.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Cases.C040.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (top_allows (Sign.withNegation globalNegation (assignment 16)))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C040.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (domain_from_eq (domain := Cases.C040.initial 18) (congrArg (Sign.withNegation globalNegation) hnode18) (Eq.refl Bool.true))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C040.initial 19) (congrArg (Sign.withNegation globalNegation) hnode19) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (top_allows (Sign.withNegation globalNegation (assignment 20)))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C040.initial 21) (congrArg (Sign.withNegation globalNegation) hnode21) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (top_allows (Sign.withNegation globalNegation (assignment 22)))
  let bounded24 := below_succ bounded23 (top_allows (Sign.withNegation globalNegation (assignment 23)))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C040.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C040.initial 25) (congrArg (Sign.withNegation globalNegation) hnode25) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (top_allows (Sign.withNegation globalNegation (assignment 26)))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C040.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C040.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C040.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (top_allows (Sign.withNegation globalNegation (assignment 30)))
  let bounded32 := below_succ bounded31 (top_allows (Sign.withNegation globalNegation (assignment 31)))
  let bounded33 := below_succ bounded32 (top_allows (Sign.withNegation globalNegation (assignment 32)))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C040.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C040.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (top_allows (Sign.withNegation globalNegation (assignment 35)))
  let bounded37 := below_succ bounded36 (domain_from_eq (domain := Cases.C040.initial 36) (congrArg (Sign.withNegation globalNegation) hnode36) (Eq.refl Bool.true))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C040.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C040.initial 38) (congrArg (Sign.withNegation globalNegation) hnode38) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (domain_from_eq (domain := Cases.C040.initial 39) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded41 := below_succ bounded40 (domain_from_eq (domain := Cases.C040.initial 40) (congrArg (Sign.withNegation globalNegation) hnode40) (Eq.refl Bool.true))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C040.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C040.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (domain_from_eq (domain := Cases.C040.initial 43) (congrArg (Sign.withNegation globalNegation) hnode43) (Eq.refl Bool.true))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Cases.C040.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C040.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (top_allows (Sign.withNegation globalNegation (assignment 46)))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C040.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (domain_from_eq (domain := Cases.C040.initial 48) (congrArg (Sign.withNegation globalNegation) hnode48) (Eq.refl Bool.true))
  let bounded50 := below_succ bounded49 (top_allows (Sign.withNegation globalNegation (assignment 49)))
  let bounded51 := below_succ bounded50 (domain_from_eq (domain := Cases.C040.initial 50) (congrArg (Sign.withNegation globalNegation) hnode50) (Eq.refl Bool.true))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C040.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (domain_from_eq (domain := Cases.C040.initial 52) (congrArg (Sign.withNegation globalNegation) hnode52) (Eq.refl Bool.true))
  let bounded54 := below_succ bounded53 (top_allows (Sign.withNegation globalNegation (assignment 53)))
  let bounded55 := below_succ bounded54 (top_allows (Sign.withNegation globalNegation (assignment 54)))
  let bounded56 := below_succ bounded55 (top_allows (Sign.withNegation globalNegation (assignment 55)))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C040.initial 56) (congrArg (Sign.withNegation globalNegation) hnode56) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (top_allows (Sign.withNegation globalNegation (assignment 57)))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C040.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C040.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (top_allows (Sign.withNegation globalNegation (assignment 60)))
  let bounded62 := below_succ bounded61 (top_allows (Sign.withNegation globalNegation (assignment 61)))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C040.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C040.initial 63) (congrArg (Sign.withNegation globalNegation) hnode63) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C040.initial 64) (congrArg (Sign.withNegation globalNegation) hnode64) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (domain_from_eq (domain := Cases.C040.initial 65) (congrArg (Sign.withNegation globalNegation) hnode65) (Eq.refl Bool.true))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C040.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (domain_from_eq (domain := Cases.C040.initial 67) (congrArg (Sign.withNegation globalNegation) hnode67) (Eq.refl Bool.true))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C040.initial 68) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C040.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C040.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (top_allows (Sign.withNegation globalNegation (assignment 71)))
  let bounded73 := below_succ bounded72 (top_allows (Sign.withNegation globalNegation (assignment 72)))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C040.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C040.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Cases.C040.initial 75) (congrArg (Sign.withNegation globalNegation) hnode75) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Cases.C040.initial 76) (congrArg (Sign.withNegation globalNegation) hnode76) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (top_allows (Sign.withNegation globalNegation (assignment 77)))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C040.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C040.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (top_allows (Sign.withNegation globalNegation (assignment 80)))
  let bounded82 := below_succ bounded81 (top_allows (Sign.withNegation globalNegation (assignment 81)))
  let bounded83 := below_succ bounded82 (top_allows (Sign.withNegation globalNegation (assignment 82)))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C040.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (domain_from_eq (domain := Cases.C040.initial 84) (congrArg (Sign.withNegation globalNegation) hnode84) (Eq.refl Bool.true))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C040.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (top_allows (Sign.withNegation globalNegation (assignment 86)))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C040.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (top_allows (Sign.withNegation globalNegation (assignment 88)))
  let bounded90 := below_succ bounded89 (domain_from_eq (domain := Cases.C040.initial 89) (congrArg (Sign.withNegation globalNegation) hnode89) (Eq.refl Bool.true))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C040.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C040.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C040.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C040.initial 93) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C040.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C040.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C040.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (top_allows (Sign.withNegation globalNegation (assignment 97)))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C040.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C040.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C040.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C040.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C040.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C040.initial 103) (congrArg (Sign.withNegation globalNegation) hnode103) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C040.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C040.initial 105) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C040.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C040.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C040.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C040.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C040.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C040.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C040.initial 112) (congrArg (Sign.withNegation globalNegation) hnode112) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C040.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C040.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C040.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C040.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C040.initial 117) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C040.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C040.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C040.initial 120) (congrArg (Sign.withNegation globalNegation) hnode120) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C040.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C040.initial 122) (congrArg (Sign.withNegation globalNegation) hnode122) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C040.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C040.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Cases.C040.initial 125) (congrArg (Sign.withNegation globalNegation) hnode125) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (top_allows (Sign.withNegation globalNegation (assignment 126)))
  let bounded128 := below_succ bounded127 (domain_from_eq (domain := Cases.C040.initial 127) (congrArg (Sign.withNegation globalNegation) hnode127) (Eq.refl Bool.true))
  let bounded129 := below_succ bounded128 (domain_from_eq (domain := Cases.C040.initial 128) (congrArg (Sign.withNegation globalNegation) hnode128) (Eq.refl Bool.true))
  let bounded130 := below_succ bounded129 (top_allows (Sign.withNegation globalNegation (assignment 129)))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C040.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C040.initial 131) (congrArg (Sign.withNegation globalNegation) hnode131) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C040.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (top_allows (Sign.withNegation globalNegation (assignment 133)))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C040.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C040.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C040.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C040.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C040.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C040.initial 139) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C040.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C040.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C040.initial 142) (congrArg (Sign.withNegation globalNegation) hnode142) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C040.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C040.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C040.initial 145) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C040.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C040.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C040.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C040.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (top_allows (Sign.withNegation globalNegation (assignment 150)))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C040.initial 151) (congrArg (Sign.withNegation globalNegation) hnode151) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C040.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C040.initial 153) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (top_allows (Sign.withNegation globalNegation (assignment 154)))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C040.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C040.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C040.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C040.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C040.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C040.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (domain_from_eq (domain := Cases.C040.initial 161) (congrArg (Sign.withNegation globalNegation) hnode161) (Eq.refl Bool.true))
  let bounded163 := below_succ bounded162 (top_allows (Sign.withNegation globalNegation (assignment 162)))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C040.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C040.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C040.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C040.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (top_allows (Sign.withNegation globalNegation (assignment 167)))
  let bounded169 := below_succ bounded168 (top_allows (Sign.withNegation globalNegation (assignment 168)))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C040.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (top_allows (Sign.withNegation globalNegation (assignment 170)))
  let bounded172 := below_succ bounded171 (top_allows (Sign.withNegation globalNegation (assignment 171)))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C040.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C040.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (top_allows (Sign.withNegation globalNegation (assignment 174)))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C040.initial 175) (congrArg (Sign.withNegation globalNegation) hnode175) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C040.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (top_allows (Sign.withNegation globalNegation (assignment 177)))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C040.initial 178) (congrArg (Sign.withNegation globalNegation) hnode178) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C040.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C040.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C040.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C040.initial 182) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C040.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Cases.C040.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C040.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Cases.C040.initial 186) (congrArg (Sign.withNegation globalNegation) hnode186) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C040.initial 187) (congrArg (Sign.withNegation globalNegation) hnode187) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C040.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C040.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C040.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C040.initial 191) (congrArg (Sign.withNegation globalNegation) hnode191) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C040.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C040.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (top_allows (Sign.withNegation globalNegation (assignment 194)))
  let bounded196 := below_succ bounded195 (top_allows (Sign.withNegation globalNegation (assignment 195)))
  let bounded197 := below_succ bounded196 (top_allows (Sign.withNegation globalNegation (assignment 196)))
  let bounded198 := below_succ bounded197 (top_allows (Sign.withNegation globalNegation (assignment 197)))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Cases.C040.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (top_allows (Sign.withNegation globalNegation (assignment 199)))
  let bounded201 := below_succ bounded200 (domain_from_eq (domain := Cases.C040.initial 200) (congrArg (Sign.withNegation globalNegation) hnode200) (Eq.refl Bool.true))
  let bounded202 := below_succ bounded201 (domain_from_eq (domain := Cases.C040.initial 201) (congrArg (Sign.withNegation globalNegation) hnode201) (Eq.refl Bool.true))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C040.initial 202) (congrArg (Sign.withNegation globalNegation) hnode202) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (domain_from_eq (domain := Cases.C040.initial 203) (congrArg (Sign.withNegation globalNegation) hnode203) (Eq.refl Bool.true))
  let bounded205 := below_succ bounded204 (domain_from_eq (domain := Cases.C040.initial 204) (congrArg (Sign.withNegation globalNegation) hnode204) (Eq.refl Bool.true))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C040.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (top_allows (Sign.withNegation globalNegation (assignment 206)))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Cases.C040.initial 207) (congrArg (Sign.withNegation globalNegation) hnode207) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C040.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C040.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C040.initial 210) (congrArg (Sign.withNegation globalNegation) hnode210) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C040.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C040.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C040.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C040.initial 214) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (domain_from_eq (domain := Cases.C040.initial 215) (congrArg (Sign.withNegation globalNegation) hnode215) (Eq.refl Bool.true))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C040.initial 216) (congrArg (Sign.withNegation globalNegation) hnode216) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C040.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C040.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (top_allows (Sign.withNegation globalNegation (assignment 219)))
  let bounded221 := below_succ bounded220 (top_allows (Sign.withNegation globalNegation (assignment 220)))
  let bounded222 := below_succ bounded221 (top_allows (Sign.withNegation globalNegation (assignment 221)))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C040.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C040.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C040.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (top_allows (Sign.withNegation globalNegation (assignment 225)))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C040.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C040.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C040.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (top_allows (Sign.withNegation globalNegation (assignment 229)))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C040.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (top_allows (Sign.withNegation globalNegation (assignment 231)))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C040.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (top_allows (Sign.withNegation globalNegation (assignment 233)))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C040.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C040.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (domain_from_eq (domain := Cases.C040.initial 236) (congrArg (Sign.withNegation globalNegation) hnode236) (Eq.refl Bool.true))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C040.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (top_allows (Sign.withNegation globalNegation (assignment 238)))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Cases.C040.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (top_allows (Sign.withNegation globalNegation (assignment 240)))
  let bounded242 := below_succ bounded241 (top_allows (Sign.withNegation globalNegation (assignment 241)))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C040.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C040.initial 243) (congrArg (Sign.withNegation globalNegation) hnode243) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C040.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C040.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C040.initial 246) (congrArg (Sign.withNegation globalNegation) hnode246) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (top_allows (Sign.withNegation globalNegation (assignment 247)))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C040.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (top_allows (Sign.withNegation globalNegation (assignment 249)))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Cases.C040.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C040.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C040.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C040
#print axioms Papers.RationalityTen.PureGP.Initializers.C040.support_sign_contradiction
