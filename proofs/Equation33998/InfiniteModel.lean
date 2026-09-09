import JudgeProblem
import Mathlib.Logic.Relation
import Lean
namespace submission

@[reducible] def BaseEquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ («x» : G) («y» : G) («z» : G), «x» = («y» ◇ (((«y» ◇ «x») ◇ «x») ◇ («z» ◇ «z»)))

@[reducible] def BaseEquationRHS (G : Type _) [Magma G] : Prop :=
  ∀ («x» : G) («y» : G), «x» = «y»

abbrev BaseGoal : Prop :=
  ∃ (G : Type) (_ : Magma G), BaseEquationLHS G ∧ ¬ BaseEquationRHS G
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace base_model
inductive T where
 | lf : Nat → T
 | op : T → T → T
 | zz0 : T → T → T
 | zz1 : T → T → T → T
 | zz2 : T → T → T
 | zz3 : T
 | zz4 : T → T → T
 | zz5 : T → T → T
open T
abbrev ct0 (v0 v1 : T) : T := (zz5 (zz4 v0 v1) v1)
abbrev ct1 (v0 : T) : T := (zz5 v0 (zz2 v0 v0))
abbrev ct2 (v0 v1 : T) : T := (zz5 v0 (zz2 v1 v0))
abbrev ct3 (v0 v1 : T) : T := (zz5 v0 (ct2 v0 v1))
abbrev ct4 (v0 : T) : T := (zz5 v0 (zz3 ))
abbrev ct5 (v0 : T) : T := (zz4 v0 (zz3 ))
abbrev ct6 (v0 v1 : T) : T := (zz2 v0 (zz4 v1 v0))
abbrev ct7 (v0 v1 : T) : T := (zz5 (zz4 v0 v1) (ct6 v1 v0))
abbrev ct8 (v0 v1 : T) : T := (zz2 (zz2 v0 v1) v1)
abbrev ct9 (v0 v1 : T) : T := (zz5 v0 (ct8 v1 v0))
abbrev ct10 (v0 v1 : T) : T := (zz2 v0 (zz4 v0 v1))
abbrev ct11 (v0 v1 : T) : T := (zz5 (zz4 v0 v1) (ct10 v0 v1))
abbrev ct12 (v0 : T) : T := (zz2 (zz3 ) v0)
abbrev ct13 (v0 : T) : T := (zz5 v0 (ct12 v0))
abbrev ct14 : T := (zz2 (zz3 ) (zz3 ))
abbrev ct15 (v0 v1 : T) : T := (zz2 (ct2 v0 v1) v0)
abbrev ct16 (v0 v1 : T) : T := (zz5 v0 (ct15 v0 v1))
abbrev ct17 (v0 : T) : T := (zz4 (zz3 ) v0)
abbrev ct18 (v0 : T) : T := (zz2 (ct17 v0) (ct17 v0))
abbrev ct19 (v0 : T) : T := (zz5 (zz3 ) v0)
abbrev ct20 (v0 : T) : T := (zz2 v0 (zz3 ))
abbrev ct21 (v0 : T) : T := (zz2 (ct20 v0) (zz3 ))
abbrev ct22 (v0 : T) : T := (zz2 (ct21 v0) (zz3 ))
abbrev ct23 (v0 v1 : T) : T := (zz2 (zz2 v0 v1) (zz3 ))
abbrev ct24 (v0 v1 : T) : T := (zz2 (ct23 v0 v1) (zz3 ))
abbrev ct25 (v0 v1 : T) : T := (zz5 (ct24 v0 v1) v1)
abbrev ct26 (v0 : T) : T := (zz5 (ct21 v0) (ct17 v0))
abbrev ct27 (v0 : T) : T := (zz4 (zz3 ) (ct20 v0))
abbrev ct28 (v0 : T) : T := (zz5 v0 (ct27 v0))
abbrev ct29 (v0 : T) : T := (zz2 (zz2 v0 v0) (zz3 ))
abbrev ct30 (v0 : T) : T := (zz2 (ct29 v0) (zz3 ))
abbrev ct31 (v0 : T) : T := (zz2 v0 (ct30 v0))
abbrev ct32 (v0 : T) : T := (zz2 (ct17 v0) (ct21 v0))
abbrev ct33 (v0 : T) : T := (zz2 (ct27 v0) v0)
abbrev ct34 (v0 : T) : T := (zz5 (ct21 v0) (ct30 v0))
abbrev ct35 (v0 v1 : T) : T := (zz2 v0 (ct24 v0 v1))
abbrev ct36 (v0 v1 : T) : T := (zz5 (ct24 v0 v1) (ct35 v0 v1))
abbrev ct37 (v0 : T) : T := (zz2 (ct20 v0) (ct20 v0))
abbrev ct38 (v0 : T) : T := (zz2 (ct37 v0) (zz3 ))
abbrev ct39 (v0 : T) : T := (zz2 (ct38 v0) (zz3 ))
abbrev ct40 (v0 : T) : T := (zz5 v0 (ct39 v0))
abbrev ct41 (v0 : T) : T := (zz2 (ct12 v0) (zz3 ))
abbrev ct42 (v0 : T) : T := (zz2 (ct41 v0) (zz3 ))
abbrev ct43 (v0 : T) : T := (zz2 (ct42 v0) (ct42 v0))
abbrev ct44 (v0 : T) : T := (zz2 (ct17 v0) (zz3 ))
abbrev ct45 (v0 : T) : T := (zz2 (ct44 v0) (zz3 ))
abbrev ct46 (v0 : T) : T := (zz5 (ct45 v0) (ct21 v0))
abbrev ct47 (v0 : T) : T := (zz2 (ct27 v0) (zz3 ))
abbrev ct48 (v0 : T) : T := (zz2 (ct47 v0) (zz3 ))
abbrev ct49 (v0 : T) : T := (zz5 (ct48 v0) v0)
abbrev ct50 (v0 : T) : T := (zz2 v0 (ct21 v0))
abbrev ct51 (v0 : T) : T := (zz5 (ct21 v0) (ct50 v0))
abbrev ct52 (v0 : T) : T := (zz2 (ct20 v0) v0)
abbrev ct53 (v0 : T) : T := (zz5 v0 (ct52 v0))
abbrev ct54 (v0 : T) : T := (zz2 (ct39 v0) v0)
abbrev ct55 (v0 : T) : T := (zz5 v0 (ct54 v0))
abbrev ct56 (v0 : T) : T := (zz5 (ct41 v0) (ct21 v0))
abbrev ct57 (v0 : T) : T := (zz2 (zz3 ) (ct20 v0))
abbrev ct58 (v0 : T) : T := (zz2 (ct57 v0) (zz3 ))
abbrev ct59 (v0 : T) : T := (zz5 (ct58 v0) v0)
abbrev ct60 (v0 : T) : T := (zz5 (ct21 v0) (ct42 v0))
abbrev ct61 (v0 : T) : T := (zz2 (ct42 v0) (ct21 v0))
abbrev ct62 (v0 : T) : T := (zz2 (ct58 v0) (zz3 ))
abbrev ct63 (v0 : T) : T := (zz5 v0 (ct62 v0))
abbrev ct64 (v0 : T) : T := (zz2 (ct62 v0) v0)
abbrev ct65 (v0 v1 : T) : T := (zz2 v0 (ct24 v1 v0))
abbrev ct66 (v0 v1 : T) : T := (zz5 (ct24 v0 v1) (ct65 v1 v0))
abbrev ct67 (v0 : T) : T := (zz2 (ct30 v0) (ct21 v0))
abbrev ct68 (v0 : T) : T := (zz5 (ct21 v0) (ct67 v0))
abbrev ct69 (v0 : T) : T := (zz2 (ct21 v0) (ct41 v0))
abbrev ct70 (v0 : T) : T := (zz5 (ct41 v0) (ct69 v0))
abbrev ct71 (v0 : T) : T := (zz2 (ct21 v0) (ct45 v0))
abbrev ct72 (v0 : T) : T := (zz5 (ct45 v0) (ct71 v0))
abbrev ct73 (v0 : T) : T := (zz2 v0 (ct58 v0))
abbrev ct74 (v0 : T) : T := (zz5 (ct58 v0) (ct73 v0))
abbrev ct75 (v0 : T) : T := (zz2 v0 (ct48 v0))
abbrev ct76 (v0 : T) : T := (zz5 (ct48 v0) (ct75 v0))
abbrev ct77 (v0 : T) : T := (zz2 (ct42 v0) (ct41 v0))
abbrev ct78 (v0 : T) : T := (zz2 (ct17 v0) (ct45 v0))
abbrev ct79 (v0 : T) : T := (zz2 (ct62 v0) (ct58 v0))
abbrev ct80 (v0 : T) : T := (zz2 (ct27 v0) (ct48 v0))
abbrev ct81 (v0 v1 v2 : T) : T := (zz5 (zz4 v0 v1) v2)
abbrev ct82 (v0 v1 : T) : T := (zz5 v0 (zz2 v1 v1))
abbrev ct83 (v0 v1 : T) : T := (zz5 v0 (zz2 v0 v1))
abbrev ct84 (v0 v1 v2 : T) : T := (zz5 v0 (ct2 v1 v2))
abbrev ct85 (v0 v1 v2 : T) : T := (zz5 v0 (zz2 v1 v2))
abbrev ct86 (v0 v1 v2 : T) : T := (zz5 v0 (ct85 v1 v2 v0))
abbrev ct87 (v0 v1 v2 : T) : T := (zz5 v0 (ct85 v0 v1 v2))
abbrev ct88 (v0 v1 v2 : T) : T := (zz5 (zz4 v0 v1) (ct6 v1 v2))
abbrev ct89 (v0 v1 v2 : T) : T := (zz5 (zz4 v0 v1) (ct6 v2 v0))
abbrev ct90 (v0 v1 v2 : T) : T := (zz2 v0 (zz4 v1 v2))
abbrev ct91 (v0 v1 v2 : T) : T := (zz5 (zz4 v0 v1) (ct90 v2 v0 v1))
abbrev ct92 (v0 v1 v2 : T) : T := (zz5 (zz4 v0 v1) (ct90 v1 v0 v2))
abbrev ct93 (v0 v1 v2 : T) : T := (zz5 v0 (ct8 v1 v2))
abbrev ct94 (v0 v1 v2 : T) : T := (zz2 (zz2 v0 v1) v2)
abbrev ct95 (v0 v1 v2 : T) : T := (zz5 v0 (ct94 v1 v2 v0))
abbrev ct96 (v0 v1 v2 : T) : T := (zz5 v0 (ct94 v1 v0 v2))
abbrev ct97 (v0 v1 v2 : T) : T := (zz5 (zz4 v0 v1) (ct10 v2 v1))
abbrev ct98 (v0 v1 v2 : T) : T := (zz5 (zz4 v0 v1) (ct10 v0 v2))
abbrev ct99 (v0 v1 v2 : T) : T := (zz5 (zz4 v0 v1) (ct90 v0 v2 v1))
abbrev ct100 (v0 v1 : T) : T := (zz5 v0 (ct12 v1))
abbrev ct101 (v0 v1 v2 : T) : T := (zz5 v0 (ct15 v1 v2))
abbrev ct102 (v0 v1 v2 : T) : T := (zz2 (ct85 v0 v1 v2) v2)
abbrev ct103 (v0 v1 v2 : T) : T := (zz2 (ct2 v0 v1) v2)
abbrev ct104 (v0 v1 v2 : T) : T := (zz5 v0 (ct102 v1 v2 v0))
abbrev ct105 (v0 v1 v2 : T) : T := (zz2 (ct85 v0 v1 v2) v0)
abbrev ct106 (v0 v1 v2 : T) : T := (zz5 v0 (ct105 v0 v1 v2))
abbrev ct107 (v0 v1 v2 : T) : T := (zz5 v0 (ct103 v0 v1 v2))
abbrev ct108 (v0 v1 : T) : T := (zz2 (ct17 v0) (ct17 v1))
abbrev ct109 (v0 v1 v2 : T) : T := (zz5 (ct24 v0 v1) v2)
abbrev ct110 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct17 v1))
abbrev ct111 (v0 v1 : T) : T := (zz5 v0 (ct27 v1))
abbrev ct112 (v0 v1 : T) : T := (zz2 v0 (ct30 v1))
abbrev ct113 (v0 v1 : T) : T := (zz2 (ct17 v0) (ct21 v1))
abbrev ct114 (v0 v1 : T) : T := (zz2 (ct27 v0) v1)
abbrev ct115 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct30 v1))
abbrev ct116 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct24 v1 v0))
abbrev ct117 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct24 v0 v1))
abbrev ct118 (v0 v1 v2 : T) : T := (zz5 (ct24 v0 v1) (ct35 v2 v1))
abbrev ct119 (v0 v1 v2 : T) : T := (zz2 v0 (ct24 v1 v2))
abbrev ct120 (v0 v1 v2 : T) : T := (zz5 (ct24 v0 v1) (ct35 v0 v2))
abbrev ct121 (v0 v1 v2 : T) : T := (zz5 (ct24 v0 v1) (ct119 v2 v0 v1))
abbrev ct122 (v0 v1 v2 : T) : T := (zz5 (ct24 v0 v1) (ct119 v0 v2 v1))
abbrev ct123 (v0 v1 : T) : T := (zz5 v0 (ct39 v1))
abbrev ct124 (v0 v1 : T) : T := (zz2 (ct20 v0) (ct20 v1))
abbrev ct125 (v0 v1 : T) : T := (zz2 (ct124 v0 v1) (zz3 ))
abbrev ct126 (v0 v1 : T) : T := (zz2 (ct125 v0 v1) (zz3 ))
abbrev ct127 (v0 v1 : T) : T := (zz5 v0 (ct126 v1 v0))
abbrev ct128 (v0 v1 : T) : T := (zz5 v0 (ct126 v0 v1))
abbrev ct129 (v0 v1 : T) : T := (zz2 (ct42 v0) (ct42 v1))
abbrev ct130 (v0 v1 : T) : T := (zz5 (ct45 v0) (ct21 v1))
abbrev ct131 (v0 v1 : T) : T := (zz5 (ct48 v0) v1)
abbrev ct132 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct50 v1))
abbrev ct133 (v0 v1 : T) : T := (zz2 v0 (ct21 v1))
abbrev ct134 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct133 v1 v0))
abbrev ct135 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct133 v0 v1))
abbrev ct136 (v0 v1 : T) : T := (zz5 v0 (ct52 v1))
abbrev ct137 (v0 v1 : T) : T := (zz2 (ct20 v0) v1)
abbrev ct138 (v0 v1 : T) : T := (zz5 v0 (ct137 v1 v0))
abbrev ct139 (v0 v1 : T) : T := (zz5 v0 (ct137 v0 v1))
abbrev ct140 (v0 v1 : T) : T := (zz5 v0 (ct54 v1))
abbrev ct141 (v0 v1 : T) : T := (zz2 (ct126 v0 v1) v1)
abbrev ct142 (v0 v1 : T) : T := (zz2 (ct39 v0) v1)
abbrev ct143 (v0 v1 : T) : T := (zz5 v0 (ct141 v1 v0))
abbrev ct144 (v0 v1 : T) : T := (zz2 (ct126 v0 v1) v0)
abbrev ct145 (v0 v1 : T) : T := (zz5 v0 (ct144 v0 v1))
abbrev ct146 (v0 v1 : T) : T := (zz5 v0 (ct142 v0 v1))
abbrev ct147 (v0 v1 : T) : T := (zz5 (ct41 v0) (ct21 v1))
abbrev ct148 (v0 v1 : T) : T := (zz5 (ct58 v0) v1)
abbrev ct149 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct42 v1))
abbrev ct150 (v0 v1 : T) : T := (zz2 (ct42 v0) (ct21 v1))
abbrev ct151 (v0 v1 : T) : T := (zz5 v0 (ct62 v1))
abbrev ct152 (v0 v1 : T) : T := (zz2 (ct62 v0) v1)
abbrev ct153 (v0 v1 v2 : T) : T := (zz5 (ct24 v0 v1) (ct65 v1 v2))
abbrev ct154 (v0 v1 v2 : T) : T := (zz5 (ct24 v0 v1) (ct65 v2 v0))
abbrev ct155 (v0 v1 v2 : T) : T := (zz5 (ct24 v0 v1) (ct119 v1 v0 v2))
abbrev ct156 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct67 v1))
abbrev ct157 (v0 v1 : T) : T := (zz2 (ct24 v0 v1) (ct21 v1))
abbrev ct158 (v0 v1 : T) : T := (zz2 (ct30 v0) (ct21 v1))
abbrev ct159 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct157 v1 v0))
abbrev ct160 (v0 v1 : T) : T := (zz2 (ct24 v0 v1) (ct21 v0))
abbrev ct161 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct160 v0 v1))
abbrev ct162 (v0 v1 : T) : T := (zz5 (ct21 v0) (ct158 v0 v1))
abbrev ct163 (v0 v1 : T) : T := (zz5 (ct41 v0) (ct69 v1))
abbrev ct164 (v0 v1 : T) : T := (zz2 (ct21 v0) (ct41 v1))
abbrev ct165 (v0 v1 : T) : T := (zz5 (ct41 v0) (ct164 v1 v0))
abbrev ct166 (v0 v1 : T) : T := (zz5 (ct41 v0) (ct164 v0 v1))
abbrev ct167 (v0 v1 : T) : T := (zz5 (ct45 v0) (ct71 v1))
abbrev ct168 (v0 v1 : T) : T := (zz2 (ct21 v0) (ct45 v1))
abbrev ct169 (v0 v1 : T) : T := (zz5 (ct45 v0) (ct168 v1 v0))
abbrev ct170 (v0 v1 : T) : T := (zz5 (ct45 v0) (ct168 v0 v1))
abbrev ct171 (v0 v1 : T) : T := (zz5 (ct58 v0) (ct73 v1))
abbrev ct172 (v0 v1 : T) : T := (zz2 v0 (ct58 v1))
abbrev ct173 (v0 v1 : T) : T := (zz5 (ct58 v0) (ct172 v1 v0))
abbrev ct174 (v0 v1 : T) : T := (zz5 (ct58 v0) (ct172 v0 v1))
abbrev ct175 (v0 v1 : T) : T := (zz5 (ct48 v0) (ct75 v1))
abbrev ct176 (v0 v1 : T) : T := (zz2 v0 (ct48 v1))
abbrev ct177 (v0 v1 : T) : T := (zz5 (ct48 v0) (ct176 v1 v0))
abbrev ct178 (v0 v1 : T) : T := (zz5 (ct48 v0) (ct176 v0 v1))
abbrev ct179 (v0 : T) : T := (zz5 (zz3 ) (ct20 v0))
abbrev ct180 : T := (zz2 (ct14 ) (ct14 ))
abbrev ct181 : T := (zz2 (zz3 ) (ct14 ))
abbrev ct182 : T := (zz2 (ct181 ) (zz3 ))
abbrev ct183 : T := (zz5 (zz3 ) (ct182 ))
abbrev ct184 (v0 : T) : T := (zz2 (ct43 v0) (zz3 ))
abbrev ct185 (v0 : T) : T := (zz2 (ct18 v0) (zz3 ))
abbrev ct186 (v0 : T) : T := (zz2 (ct62 v0) (ct62 v0))
abbrev ct187 (v0 : T) : T := (zz2 (ct186 v0) (zz3 ))
abbrev ct188 (v0 : T) : T := (zz2 (ct27 v0) (ct27 v0))
abbrev ct189 (v0 : T) : T := (zz2 (ct188 v0) (zz3 ))
abbrev ct190 : T := (zz5 (zz3 ) (zz3 ))
abbrev ct191 (v0 : T) : T := (zz5 (ct17 v0) v0)
abbrev ct192 (v0 : T) : T := (zz5 (ct30 v0) v0)
abbrev ct193 (v0 : T) : T := (zz5 (ct42 v0) v0)
abbrev ct194 : T := (zz4 (zz3 ) (ct14 ))
abbrev ct195 : T := (zz2 (ct194 ) (zz3 ))
abbrev ct196 (v0 : T) : T := (zz2 (zz3 ) (ct5 v0))
abbrev ct197 (v0 : T) : T := (zz2 v0 (zz4 v0 v0))
abbrev ct198 : T := (zz2 (ct180 ) (zz3 ))
abbrev ct199 : T := (zz5 (zz3 ) (ct198 ))
abbrev ct200 : T := (zz5 (zz3 ) (ct14 ))
abbrev ct201 : T := (zz2 (ct198 ) (zz3 ))
abbrev ct202 : T := (zz5 (zz3 ) (ct201 ))
abbrev ct203 : T := (zz2 (ct199 ) (zz3 ))
abbrev ct204 (v0 : T) : T := (zz5 (zz3 ) (ct21 v0))
abbrev ct205 (v0 : T) : T := (zz2 (ct179 v0) (zz3 ))
abbrev ct206 : T := (zz2 (ct182 ) (zz3 ))
abbrev ct207 : T := (zz5 (zz3 ) (ct206 ))
abbrev ct208 : T := (zz2 (ct183 ) (zz3 ))
abbrev ct209 (v0 : T) : T := (zz2 (zz3 ) (ct17 v0))
abbrev ct210 (v0 : T) : T := (zz5 (ct17 v0) (ct18 v0))
abbrev ct211 (v0 : T) : T := (zz5 (zz3 ) (ct22 v0))
abbrev ct212 (v0 : T) : T := (zz2 (ct204 v0) (zz3 ))
abbrev ct213 (v0 : T) : T := (zz5 (ct30 v0) (ct31 v0))
abbrev ct214 (v0 : T) : T := (zz5 (ct21 v0) (ct32 v0))
abbrev ct215 (v0 : T) : T := (zz5 v0 (ct33 v0))
abbrev ct216 (v0 : T) : T := (zz2 (zz3 ) (ct42 v0))
abbrev ct217 (v0 : T) : T := (zz5 (ct42 v0) (ct43 v0))
abbrev ct218 (v0 : T) : T := (zz5 (ct21 v0) (ct61 v0))
abbrev ct219 (v0 : T) : T := (zz5 v0 (ct64 v0))
abbrev ct220 (v0 : T) : T := (zz2 v0 (ct5 v0))
abbrev ct221 : T := (zz2 (ct14 ) (zz3 ))
abbrev ct222 : T := (zz2 (ct221 ) (zz3 ))
abbrev ct223 : T := (zz2 (ct195 ) (zz3 ))
abbrev ct224 : T := (zz4 (zz3 ) (zz3 ))
abbrev ct225 (v0 : T) : T := (zz5 (ct41 v0) (ct77 v0))
abbrev ct226 (v0 : T) : T := (zz2 (ct184 v0) (zz3 ))
abbrev ct227 (v0 : T) : T := (zz5 (ct45 v0) (ct78 v0))
abbrev ct228 (v0 : T) : T := (zz2 (ct185 v0) (zz3 ))
abbrev ct229 (v0 : T) : T := (zz5 (ct58 v0) (ct79 v0))
abbrev ct230 (v0 : T) : T := (zz2 (ct187 v0) (zz3 ))
abbrev ct231 (v0 : T) : T := (zz5 (ct48 v0) (ct80 v0))
abbrev ct232 (v0 : T) : T := (zz2 (ct189 v0) (zz3 ))
abbrev ct233 : T := (zz2 (ct190 ) (zz3 ))
abbrev ct234 (v0 : T) : T := (zz2 (ct191 v0) (ct17 v0))
abbrev ct235 (v0 : T) : T := (zz2 (ct19 v0) (zz3 ))
abbrev ct236 (v0 : T) : T := (zz2 (ct192 v0) (ct30 v0))
abbrev ct237 (v0 : T) : T := (zz2 (ct26 v0) (ct21 v0))
abbrev ct238 (v0 : T) : T := (zz2 (ct28 v0) v0)
abbrev ct239 (v0 : T) : T := (zz2 (ct193 v0) (ct42 v0))
abbrev ct240 (v0 : T) : T := (zz2 (ct60 v0) (ct21 v0))
abbrev ct241 (v0 : T) : T := (zz2 (ct63 v0) v0)
abbrev ct242 : T := (zz2 (ct206 ) (zz3 ))
abbrev ct243 (v0 : T) : T := (zz2 (ct42 v0) (zz3 ))
abbrev ct244 (v0 : T) : T := (zz2 (ct243 v0) (zz3 ))
abbrev ct245 (v0 : T) : T := (zz2 (ct62 v0) (zz3 ))
abbrev ct246 (v0 : T) : T := (zz2 (ct245 v0) (zz3 ))
abbrev ct247 : T := (zz4 (zz3 ) (ct182 ))
abbrev ct248 : T := (zz4 (zz3 ) (ct221 ))
abbrev ct249 (v0 : T) : T := (zz4 (zz3 ) (ct21 v0))
abbrev ct250 : T := (zz4 (zz3 ) (ct194 ))
abbrev ct251 : T := (zz4 (zz3 ) (ct224 ))
abbrev ct252 : T := (zz4 (zz3 ) (ct206 ))
abbrev ct253 : T := (zz4 (zz3 ) (ct222 ))
abbrev ct254 : T := (zz2 (ct182 ) (ct182 ))
abbrev ct255 : T := (zz2 (ct254 ) (zz3 ))
abbrev ct256 : T := (zz2 (ct255 ) (zz3 ))
abbrev ct257 : T := (zz5 (zz3 ) (ct255 ))
abbrev ct258 : T := (zz5 (zz3 ) (ct221 ))
abbrev ct259 : T := (zz2 (ct200 ) (zz3 ))
abbrev ct260 : T := (zz2 (ct194 ) (ct194 ))
abbrev ct261 : T := (zz2 (ct260 ) (zz3 ))
abbrev ct262 : T := (zz2 (ct261 ) (zz3 ))
abbrev ct263 : T := (zz5 (zz3 ) (ct261 ))
abbrev ct264 : T := (zz2 (ct206 ) (ct206 ))
abbrev ct265 : T := (zz2 (ct264 ) (zz3 ))
abbrev ct266 : T := (zz2 (ct265 ) (zz3 ))
abbrev ct267 : T := (zz5 (zz3 ) (ct265 ))
abbrev ct268 (v0 : T) : T := (zz2 v0 (ct22 v0))
abbrev ct269 : T := (zz2 (ct181 ) (ct242 ))
abbrev ct270 : T := (zz2 (ct14 ) (ct242 ))
abbrev ct271 : T := (zz2 (zz3 ) (ct242 ))
abbrev ct272 : T := (zz2 (zz3 ) (ct181 ))
abbrev ct273 (v0 : T) : T := (zz2 (ct22 v0) (zz3 ))
abbrev ct274 (v0 : T) : T := (zz2 (ct20 v0) (ct273 v0))
abbrev ct275 : T := (zz2 (ct242 ) (zz3 ))
abbrev ct276 : T := (zz2 (ct182 ) (ct275 ))
abbrev ct277 : T := (zz2 (ct221 ) (ct275 ))
abbrev ct278 : T := (zz2 (ct14 ) (ct275 ))
abbrev ct279 : T := (zz2 (zz3 ) (ct275 ))
abbrev ct280 : T := (zz2 (zz3 ) (ct182 ))
abbrev ct281 : T := (zz2 (zz3 ) (ct221 ))
abbrev ct282 : T := (zz2 (zz3 ) (ct222 ))
abbrev ct283 (v0 : T) : T := (zz2 (ct17 v0) (ct228 v0))
abbrev ct284 (v0 : T) : T := (zz2 (ct273 v0) (zz3 ))
abbrev ct285 (v0 : T) : T := (zz2 (ct21 v0) (ct284 v0))
abbrev ct286 (v0 : T) : T := (zz2 (ct31 v0) (zz3 ))
abbrev ct287 (v0 : T) : T := (zz2 (ct286 v0) (zz3 ))
abbrev ct288 (v0 : T) : T := (zz2 v0 (ct287 v0))
abbrev ct289 (v0 : T) : T := (zz2 (ct32 v0) (zz3 ))
abbrev ct290 (v0 : T) : T := (zz2 (ct289 v0) (zz3 ))
abbrev ct291 (v0 : T) : T := (zz2 (ct17 v0) (ct290 v0))
abbrev ct292 (v0 : T) : T := (zz2 (ct33 v0) (zz3 ))
abbrev ct293 (v0 : T) : T := (zz2 (ct292 v0) (zz3 ))
abbrev ct294 (v0 : T) : T := (zz2 (ct27 v0) (ct293 v0))
abbrev ct295 (v0 : T) : T := (zz2 (ct42 v0) (ct226 v0))
abbrev ct296 (v0 : T) : T := (zz2 (ct61 v0) (zz3 ))
abbrev ct297 (v0 : T) : T := (zz2 (ct296 v0) (zz3 ))
abbrev ct298 (v0 : T) : T := (zz2 (ct42 v0) (ct297 v0))
abbrev ct299 (v0 : T) : T := (zz2 (ct42 v0) (ct244 v0))
abbrev ct300 (v0 : T) : T := (zz2 (ct64 v0) (zz3 ))
abbrev ct301 (v0 : T) : T := (zz2 (ct300 v0) (zz3 ))
abbrev ct302 (v0 : T) : T := (zz2 (ct62 v0) (ct301 v0))
abbrev ct303 (v0 : T) : T := (zz2 (ct62 v0) (ct246 v0))
abbrev ct304 : T := (zz2 (ct181 ) (ct206 ))
abbrev ct305 : T := (zz2 (ct14 ) (ct206 ))
abbrev ct306 : T := (zz2 (zz3 ) (ct206 ))
abbrev ct307 : T := (zz2 (ct182 ) (ct242 ))
abbrev ct308 : T := (zz2 (ct221 ) (ct242 ))
abbrev ct309 (v0 : T) : T := (zz2 (ct21 v0) (ct21 v0))
abbrev ct310 (v0 : T) : T := (zz2 (ct268 v0) (zz3 ))
abbrev ct311 (v0 : T) : T := (zz2 (ct310 v0) (zz3 ))
abbrev ct312 : T := (zz2 (ct194 ) (ct195 ))
abbrev ct313 : T := (zz2 (ct312 ) (zz3 ))
abbrev ct314 : T := (zz2 (ct313 ) (zz3 ))
abbrev ct315 : T := (zz5 (zz3 ) (ct313 ))
abbrev ct316 : T := (zz2 (ct206 ) (ct242 ))
abbrev ct317 : T := (zz2 (ct316 ) (zz3 ))
abbrev ct318 : T := (zz2 (ct317 ) (zz3 ))
abbrev ct319 : T := (zz5 (zz3 ) (ct317 ))
abbrev ct320 : T := (zz5 (zz3 ) (ct222 ))
abbrev ct321 : T := (zz2 (ct258 ) (zz3 ))
abbrev ct322 (v0 : T) : T := (zz2 (ct22 v0) v0)
abbrev ct323 (v0 : T) : T := (zz2 (ct322 v0) (zz3 ))
abbrev ct324 (v0 : T) : T := (zz2 (ct323 v0) (zz3 ))
abbrev ct325 : T := (zz2 (ct195 ) (ct194 ))
abbrev ct326 : T := (zz2 (ct325 ) (zz3 ))
abbrev ct327 : T := (zz2 (ct326 ) (zz3 ))
abbrev ct328 : T := (zz5 (zz3 ) (ct326 ))
abbrev ct329 : T := (zz2 (ct242 ) (ct206 ))
abbrev ct330 : T := (zz2 (ct329 ) (zz3 ))
abbrev ct331 : T := (zz2 (ct330 ) (zz3 ))
abbrev ct332 : T := (zz5 (zz3 ) (ct330 ))
abbrev ct333 : T := (zz2 (ct282 ) (zz3 ))
abbrev ct334 : T := (zz2 (ct333 ) (zz3 ))
abbrev ct335 : T := (zz2 (ct222 ) (zz3 ))
abbrev ct336 : T := (zz2 (ct335 ) (zz3 ))
abbrev ct337 : T := (zz2 (ct247 ) (zz3 ))
abbrev ct338 : T := (zz2 (ct337 ) (zz3 ))
abbrev ct339 : T := (zz2 (ct248 ) (zz3 ))
abbrev ct340 : T := (zz2 (ct339 ) (zz3 ))
abbrev ct341 : T := (zz2 (ct224 ) (zz3 ))
abbrev ct342 : T := (zz2 (ct341 ) (zz3 ))
abbrev ct343 : T := (zz2 (ct250 ) (zz3 ))
abbrev ct344 : T := (zz2 (ct343 ) (zz3 ))
abbrev ct345 : T := (zz2 (ct251 ) (zz3 ))
abbrev ct346 : T := (zz2 (ct345 ) (zz3 ))
abbrev ct347 : T := (zz2 (ct252 ) (zz3 ))
abbrev ct348 : T := (zz2 (ct347 ) (zz3 ))
abbrev ct349 : T := (zz2 (ct253 ) (zz3 ))
abbrev ct350 : T := (zz2 (ct349 ) (zz3 ))
abbrev ct351 (v0 : T) : T := (zz2 (ct20 v0) (ct22 v0))
abbrev ct352 : T := (zz2 (ct221 ) (ct182 ))
abbrev ct353 : T := (zz2 (ct352 ) (zz3 ))
abbrev ct354 : T := (zz2 (ct14 ) (ct182 ))
abbrev ct355 : T := (zz2 (ct354 ) (zz3 ))
abbrev ct356 : T := (zz2 (ct280 ) (zz3 ))
abbrev ct357 : T := (zz2 (ct281 ) (zz3 ))
abbrev ct358 (v0 : T) : T := (zz2 (ct309 v0) (zz3 ))
abbrev ct359 (v0 : T) : T := (zz2 (ct358 v0) (zz3 ))
abbrev ct360 (v0 : T) : T := (zz2 (ct21 v0) (ct273 v0))
abbrev ct361 : T := (zz2 (ct194 ) (ct223 ))
abbrev ct362 : T := (zz2 (ct224 ) (ct223 ))
abbrev ct363 : T := (zz2 (zz3 ) (ct223 ))
abbrev ct364 : T := (zz2 (zz3 ) (ct195 ))
abbrev ct365 : T := (zz2 (zz3 ) (ct194 ))
abbrev ct366 : T := (zz2 (zz3 ) (ct224 ))
abbrev ct367 : T := (zz2 (ct206 ) (ct275 ))
abbrev ct368 : T := (zz2 (ct222 ) (ct275 ))
abbrev ct369 : T := (zz2 (ct182 ) (ct206 ))
abbrev ct370 : T := (zz2 (ct221 ) (ct206 ))
abbrev ct371 (v0 : T) : T := (zz2 (ct21 v0) (ct20 v0))
abbrev ct372 : T := (zz2 (ct224 ) (ct195 ))
abbrev ct373 : T := (zz2 (ct222 ) (ct242 ))
abbrev ct374 : T := (zz2 (ct222 ) (ct222 ))
abbrev ct375 : T := (zz2 (ct374 ) (zz3 ))
abbrev ct376 (v0 : T) : T := (zz2 (ct22 v0) (ct22 v0))
abbrev ct377 (v0 : T) : T := (zz2 (ct376 v0) (zz3 ))
abbrev ct378 : T := (zz2 (ct195 ) (ct195 ))
abbrev ct379 : T := (zz2 (ct378 ) (zz3 ))
abbrev ct380 : T := (zz2 (ct372 ) (zz3 ))
abbrev ct381 : T := (zz2 (ct364 ) (zz3 ))
abbrev ct382 : T := (zz2 (ct365 ) (zz3 ))
abbrev ct383 : T := (zz2 (ct366 ) (zz3 ))
abbrev ct384 : T := (zz2 (ct242 ) (ct242 ))
abbrev ct385 : T := (zz2 (ct384 ) (zz3 ))
abbrev ct386 : T := (zz2 (ct269 ) (zz3 ))
abbrev ct387 : T := (zz2 (ct270 ) (zz3 ))
abbrev ct388 : T := (zz2 (ct271 ) (zz3 ))
abbrev ct389 : T := (zz2 (ct272 ) (zz3 ))
abbrev ct390 (v0 : T) : T := (zz2 (ct311 v0) (ct21 v0))
abbrev ct391 : T := (zz2 (ct314 ) (ct194 ))
abbrev ct392 : T := (zz2 (ct380 ) (zz3 ))
abbrev ct393 : T := (zz2 (ct392 ) (ct194 ))
abbrev ct394 : T := (zz2 (ct381 ) (zz3 ))
abbrev ct395 : T := (zz2 (ct394 ) (ct194 ))
abbrev ct396 : T := (zz2 (ct318 ) (ct206 ))
abbrev ct397 : T := (zz2 (ct373 ) (zz3 ))
abbrev ct398 : T := (zz2 (ct397 ) (zz3 ))
abbrev ct399 : T := (zz2 (ct398 ) (ct206 ))
abbrev ct400 : T := (zz2 (ct388 ) (zz3 ))
abbrev ct401 : T := (zz2 (ct400 ) (ct206 ))
abbrev ct402 : T := (zz5 (zz3 ) (ct335 ))
abbrev ct403 : T := (zz2 (ct320 ) (zz3 ))
abbrev ct404 (v0 : T) : T := (zz2 (ct324 v0) (ct21 v0))
abbrev ct405 : T := (zz2 (ct327 ) (ct194 ))
abbrev ct406 : T := (zz2 (ct262 ) (ct194 ))
abbrev ct407 : T := (zz2 (ct222 ) (ct194 ))
abbrev ct408 : T := (zz2 (ct331 ) (ct206 ))
abbrev ct409 : T := (zz2 (ct304 ) (zz3 ))
abbrev ct410 : T := (zz2 (ct409 ) (zz3 ))
abbrev ct411 : T := (zz2 (ct410 ) (ct206 ))
abbrev ct412 : T := (zz2 (ct305 ) (zz3 ))
abbrev ct413 : T := (zz2 (ct412 ) (zz3 ))
abbrev ct414 : T := (zz2 (ct413 ) (ct206 ))
abbrev ct415 : T := (zz2 (ct306 ) (zz3 ))
abbrev ct416 : T := (zz2 (ct415 ) (zz3 ))
abbrev ct417 : T := (zz2 (ct416 ) (ct206 ))
abbrev ct418 : T := (zz2 (ct334 ) (ct206 ))
abbrev ct419 (v0 : T) : T := (zz2 (zz3 ) (ct21 v0))
abbrev ct420 (v0 : T) : T := (zz2 (ct419 v0) (zz3 ))
abbrev ct421 (v0 : T) : T := (zz2 (ct420 v0) (zz3 ))
abbrev ct422 (v0 : T) : T := (zz2 (zz3 ) (ct22 v0))
abbrev ct423 (v0 : T) : T := (zz2 (ct422 v0) (zz3 ))
abbrev ct424 : T := (zz2 (ct356 ) (zz3 ))
abbrev ct425 : T := (zz5 (zz3 ) (ct356 ))
abbrev ct426 : T := (zz2 (ct382 ) (zz3 ))
abbrev ct427 : T := (zz5 (zz3 ) (ct382 ))
abbrev ct428 : T := (zz5 (zz3 ) (ct415 ))
abbrev ct429 : T := (zz2 (ct357 ) (zz3 ))
abbrev ct430 : T := (zz2 (ct383 ) (zz3 ))
abbrev ct431 (v0 : T) : T := (zz2 (zz3 ) (ct273 v0))
abbrev ct432 (v0 : T) : T := (zz2 (zz3 ) (ct284 v0))
abbrev ct433 (v0 : T) : T := (zz2 (ct30 v0) (ct287 v0))
abbrev ct434 (v0 : T) : T := (zz2 (ct21 v0) (ct290 v0))
abbrev ct435 (v0 : T) : T := (zz2 v0 (ct293 v0))
abbrev ct436 (v0 : T) : T := (zz2 (ct21 v0) (ct297 v0))
abbrev ct437 (v0 : T) : T := (zz2 (ct21 v0) (ct244 v0))
abbrev ct438 (v0 : T) : T := (zz2 v0 (ct301 v0))
abbrev ct439 (v0 : T) : T := (zz2 v0 (ct246 v0))
abbrev ct440 (v0 : T) : T := (zz2 (ct39 v0) (ct22 v0))
abbrev ct441 : T := (zz2 (ct256 ) (ct242 ))
abbrev ct442 : T := (zz2 (ct353 ) (zz3 ))
abbrev ct443 : T := (zz2 (ct442 ) (ct242 ))
abbrev ct444 : T := (zz2 (ct355 ) (zz3 ))
abbrev ct445 : T := (zz2 (ct444 ) (ct242 ))
abbrev ct446 : T := (zz2 (ct424 ) (ct242 ))
abbrev ct447 : T := (zz2 (ct222 ) (ct221 ))
abbrev ct448 (v0 : T) : T := (zz2 (ct359 v0) (ct273 v0))
abbrev ct449 : T := (zz2 (ct262 ) (ct223 ))
abbrev ct450 : T := (zz2 (ct222 ) (ct223 ))
abbrev ct451 : T := (zz2 (ct266 ) (ct275 ))
abbrev ct452 : T := (zz2 (ct256 ) (ct206 ))
abbrev ct453 : T := (zz2 (ct442 ) (ct206 ))
abbrev ct454 : T := (zz2 (ct444 ) (ct206 ))
abbrev ct455 : T := (zz2 (ct424 ) (ct206 ))
abbrev ct456 : T := (zz2 (ct429 ) (ct206 ))
abbrev ct457 : T := (zz2 (ct222 ) (ct14 ))
abbrev ct458 (v0 : T) : T := (zz2 (ct359 v0) (ct20 v0))
abbrev ct459 : T := (zz2 (ct262 ) (ct195 ))
abbrev ct460 : T := (zz2 (ct222 ) (ct195 ))
abbrev ct461 : T := (zz2 (ct266 ) (ct242 ))
abbrev ct462 : T := (zz2 (ct221 ) (ct221 ))
abbrev ct463 : T := (zz2 (ct14 ) (ct221 ))
abbrev ct464 : T := (zz2 (ct336 ) (ct333 ))
abbrev ct465 : T := (zz2 (ct221 ) (ct333 ))
abbrev ct466 : T := (zz2 (ct14 ) (ct333 ))
abbrev ct467 : T := (zz2 (zz3 ) (ct333 ))
abbrev ct468 : T := (zz2 (ct206 ) (ct356 ))
abbrev ct469 : T := (zz2 (ct222 ) (ct356 ))
abbrev ct470 : T := (zz2 (zz3 ) (ct356 ))
abbrev ct471 : T := (zz2 (zz3 ) (ct357 ))
abbrev ct472 (v0 : T) : T := (zz2 (ct421 v0) (ct420 v0))
abbrev ct473 : T := (zz2 (ct195 ) (ct382 ))
abbrev ct474 : T := (zz2 (ct194 ) (ct382 ))
abbrev ct475 : T := (zz2 (ct224 ) (ct382 ))
abbrev ct476 : T := (zz2 (zz3 ) (ct382 ))
abbrev ct477 : T := (zz2 (zz3 ) (ct383 ))
abbrev ct478 : T := (zz2 (ct242 ) (ct415 ))
abbrev ct479 : T := (zz2 (ct181 ) (ct415 ))
abbrev ct480 : T := (zz2 (ct14 ) (ct415 ))
abbrev ct481 : T := (zz2 (zz3 ) (ct415 ))
abbrev ct482 : T := (zz2 (ct221 ) (ct14 ))
abbrev ct483 : T := (zz2 (ct462 ) (zz3 ))
abbrev ct484 : T := (zz2 (ct463 ) (zz3 ))
abbrev ct485 : T := (zz2 (ct336 ) (ct14 ))
abbrev ct486 : T := (zz2 (ct221 ) (ct342 ))
abbrev ct487 : T := (zz2 (ct14 ) (ct342 ))
abbrev ct488 : T := (zz2 (zz3 ) (ct342 ))
abbrev ct489 : T := (zz2 (ct206 ) (ct338 ))
abbrev ct490 : T := (zz2 (ct222 ) (ct338 ))
abbrev ct491 : T := (zz2 (zz3 ) (ct338 ))
abbrev ct492 : T := (zz2 (zz3 ) (ct340 ))
abbrev ct493 (v0 : T) : T := (zz2 (ct249 v0) (zz3 ))
abbrev ct494 (v0 : T) : T := (zz2 (ct493 v0) (zz3 ))
abbrev ct495 (v0 : T) : T := (zz2 (ct249 v0) (ct494 v0))
abbrev ct496 : T := (zz2 (ct195 ) (ct344 ))
abbrev ct497 : T := (zz2 (ct194 ) (ct344 ))
abbrev ct498 : T := (zz2 (ct224 ) (ct344 ))
abbrev ct499 : T := (zz2 (zz3 ) (ct344 ))
abbrev ct500 : T := (zz2 (zz3 ) (ct346 ))
abbrev ct501 : T := (zz2 (ct242 ) (ct348 ))
abbrev ct502 : T := (zz2 (ct181 ) (ct348 ))
abbrev ct503 : T := (zz2 (ct14 ) (ct348 ))
abbrev ct504 : T := (zz2 (zz3 ) (ct348 ))
abbrev ct505 : T := (zz2 (zz3 ) (ct350 ))
abbrev ct506 : T := (zz2 (ct221 ) (ct336 ))
abbrev ct507 : T := (zz2 (ct14 ) (ct336 ))
abbrev ct508 : T := (zz2 (zz3 ) (ct336 ))
abbrev ct509 (v0 : T) : T := (zz2 (ct423 v0) (zz3 ))
abbrev ct510 (v0 : T) : T := (zz2 (ct21 v0) (ct423 v0))
abbrev ct511 : T := (zz2 (ct194 ) (ct381 ))
abbrev ct512 : T := (zz2 (ct224 ) (ct381 ))
abbrev ct513 : T := (zz2 (zz3 ) (ct381 ))
abbrev ct514 : T := (zz2 (ct389 ) (zz3 ))
abbrev ct515 : T := (zz2 (ct206 ) (ct388 ))
abbrev ct516 : T := (zz2 (ct222 ) (ct388 ))
abbrev ct517 : T := (zz2 (zz3 ) (ct388 ))
abbrev ct518 : T := (zz2 (zz3 ) (ct389 ))
abbrev ct519 : T := (zz2 (ct206 ) (ct415 ))
abbrev ct520 : T := (zz2 (ct222 ) (ct415 ))
abbrev ct521 (v0 : T) : T := (zz4 (zz3 ) (ct22 v0))
abbrev ct522 (v0 : T) : T := (zz2 (ct521 v0) (zz3 ))
abbrev ct523 (v0 : T) : T := (zz2 (ct522 v0) (zz3 ))
abbrev ct524 (v0 : T) : T := (zz2 (ct21 v0) (ct523 v0))
abbrev ct525 : T := (zz4 (zz3 ) (ct195 ))
abbrev ct526 : T := (zz2 (ct525 ) (zz3 ))
abbrev ct527 : T := (zz2 (ct526 ) (zz3 ))
abbrev ct528 : T := (zz2 (ct194 ) (ct527 ))
abbrev ct529 : T := (zz2 (ct224 ) (ct527 ))
abbrev ct530 : T := (zz2 (zz3 ) (ct527 ))
abbrev ct531 : T := (zz4 (zz3 ) (ct242 ))
abbrev ct532 : T := (zz2 (ct531 ) (zz3 ))
abbrev ct533 : T := (zz2 (ct532 ) (zz3 ))
abbrev ct534 : T := (zz4 (zz3 ) (ct181 ))
abbrev ct535 : T := (zz2 (ct534 ) (zz3 ))
abbrev ct536 : T := (zz2 (ct535 ) (zz3 ))
abbrev ct537 : T := (zz2 (ct206 ) (ct533 ))
abbrev ct538 : T := (zz2 (ct222 ) (ct533 ))
abbrev ct539 : T := (zz2 (zz3 ) (ct533 ))
abbrev ct540 : T := (zz2 (zz3 ) (ct536 ))
abbrev ct541 : T := (zz2 (ct206 ) (ct348 ))
abbrev ct542 : T := (zz2 (ct222 ) (ct348 ))
abbrev ct543 (v0 v1 : T) : T := (op (op v0 v1) v1)
abbrev ct544 (v0 v1 v2 : T) : T := (op (ct543 v0 v1) (op v2 v2))
abbrev ct545 (v0 v1 v2 : T) : T := (op v0 (ct544 v0 v1 v2))
abbrev ct546 (v0 v1 v2 : T) : T := (zz2 v0 (ct544 v0 v1 v2))
abbrev ct547 (v0 v1 v2 : T) : T := (zz2 (ct543 v0 v1) (op v2 v2))
abbrev ct548 (v0 v1 v2 : T) : T := (zz5 (op v0 v0) (ct547 v1 v2 v0))
abbrev ct549 (v0 v1 v2 : T) : T := (zz5 (ct1 v0) (ct547 v1 v2 v0))
abbrev ct550 (v0 v1 v2 : T) : T := (zz5 (zz3 ) (ct547 v0 v1 v2))
abbrev ct551 (v0 v1 v2 : T) : T := (zz2 (ct547 v0 v1 v2) (zz3 ))
abbrev ct552 (v0 v1 : T) : T := (zz2 (op v0 v1) v1)
abbrev ct553 (v0 v1 : T) : T := (zz5 v0 (ct552 v1 v0))
abbrev ct554 (v0 v1 v2 : T) : T := (zz2 (ct553 v0 v1) (op v2 v2))
abbrev ct555 (v0 v1 v2 : T) : T := (zz2 (ct554 v0 v1 v2) (zz3 ))
abbrev ct556 (v0 v1 v2 : T) : T := (zz2 (ct16 v0 v1) (op v2 v2))
abbrev ct557 (v0 v1 v2 : T) : T := (zz2 (ct556 v0 v1 v2) (zz3 ))
abbrev ct558 (v0 v1 v2 : T) : T := (zz2 (zz2 v0 v1) (op v2 v2))
abbrev ct559 (v0 v1 v2 : T) : T := (zz2 (ct558 v0 v1 v2) (zz3 ))
abbrev ct560 (v0 v1 v2 : T) : T := (zz2 (zz2 v0 v1) (ct1 v2))
abbrev ct561 (v0 v1 v2 : T) : T := (zz2 (ct560 v0 v1 v2) (zz3 ))
abbrev ct562 (v0 v1 v2 : T) : T := (zz2 v0 (ct548 v1 v0 v2))
abbrev ct563 (v0 v1 v2 : T) : T := (zz2 v0 (ct549 v1 v0 v2))
abbrev ct564 (v0 v1 v2 : T) : T := (zz2 v0 (ct550 v0 v1 v2))
abbrev ct565 (v0 v1 v2 : T) : T := (zz2 v0 (ct551 v0 v1 v2))
abbrev ct566 (v0 v1 v2 : T) : T := (zz2 v0 (ct555 v1 v0 v2))
abbrev ct567 (v0 v1 v2 : T) : T := (zz2 v0 (ct557 v1 v0 v2))
abbrev ct568 (v0 v1 v2 : T) : T := (zz2 v0 (ct559 v0 v1 v2))
abbrev ct569 (v0 v1 v2 : T) : T := (zz2 v0 (ct561 v0 v1 v2))
def sz : T → Nat
 | .lf _ => 1
 | .op x0 x1 => 8 * sz x0 + 9 * sz x1 + 20
 | .zz0 x0 x1 => 1 * sz x0 + 1 * sz x1 + 2
 | .zz1 x0 x1 x2 => 2 * sz x0 + 2 * sz x1 + 2 * sz x2 + 40
 | .zz2 x0 x1 => 1 * sz x0 + 1 * sz x1 + 1
 | .zz3  => 1
 | .zz4 x0 x1 => 1 * sz x0 + 1 * sz x1 + 16
 | .zz5 x0 x1 => 1 * sz x0 + 8 * sz x1 + 8
theorem sz_pos (a : T) : 0 < sz a := by
 cases a <;> simp only [sz] <;> omega
inductive Rule where
 | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15 | r16 | r17 | r18 | r19 | r20 | r21 | r22 | r23 | r24 | r25 | r26 | r27 | r28 | r29 | r30 | r31 | r32 | r33 | r34 | r35 | r36 | r37 | r38 | r39 | r40 | r41 | r42 | r43 | r44
def L : Rule → T → T → T → T
 | .r0, v0, v1, v2 => (zz0 v0 v1)
 | .r1, v0, v1, v2 => (ct0 v0 v1)
 | .r2, v0, v1, v2 => (ct1 v0)
 | .r3, v0, v1, v2 => (op v0 v1)
 | .r4, v0, v1, v2 => (ct3 v0 v1)
 | .r5, v0, v1, v2 => (ct4 v0)
 | .r6, v0, v1, v2 => (ct5 v0)
 | .r7, v0, v1, v2 => (ct7 v0 v1)
 | .r8, v0, v1, v2 => (ct9 v0 v1)
 | .r9, v0, v1, v2 => (ct11 v0 v1)
 | .r10, v0, v1, v2 => (ct13 v0)
 | .r11, v0, v1, v2 => (ct14 )
 | .r12, v0, v1, v2 => (zz1 v0 v1 v2)
 | .r13, v0, v1, v2 => (ct16 v0 v1)
 | .r14, v0, v1, v2 => (ct18 v0)
 | .r15, v0, v1, v2 => (ct19 v0)
 | .r16, v0, v1, v2 => (ct22 v0)
 | .r17, v0, v1, v2 => (ct25 v0 v1)
 | .r18, v0, v1, v2 => (ct26 v0)
 | .r19, v0, v1, v2 => (ct28 v0)
 | .r20, v0, v1, v2 => (zz4 v0 v0)
 | .r21, v0, v1, v2 => (ct31 v0)
 | .r22, v0, v1, v2 => (ct32 v0)
 | .r23, v0, v1, v2 => (ct33 v0)
 | .r24, v0, v1, v2 => (ct34 v0)
 | .r25, v0, v1, v2 => (ct36 v0 v1)
 | .r26, v0, v1, v2 => (ct40 v0)
 | .r27, v0, v1, v2 => (ct43 v0)
 | .r28, v0, v1, v2 => (ct46 v0)
 | .r29, v0, v1, v2 => (ct49 v0)
 | .r30, v0, v1, v2 => (ct51 v0)
 | .r31, v0, v1, v2 => (ct53 v0)
 | .r32, v0, v1, v2 => (ct55 v0)
 | .r33, v0, v1, v2 => (ct56 v0)
 | .r34, v0, v1, v2 => (ct59 v0)
 | .r35, v0, v1, v2 => (ct60 v0)
 | .r36, v0, v1, v2 => (ct61 v0)
 | .r37, v0, v1, v2 => (ct63 v0)
 | .r38, v0, v1, v2 => (ct64 v0)
 | .r39, v0, v1, v2 => (ct66 v0 v1)
 | .r40, v0, v1, v2 => (ct68 v0)
 | .r41, v0, v1, v2 => (ct70 v0)
 | .r42, v0, v1, v2 => (ct72 v0)
 | .r43, v0, v1, v2 => (ct74 v0)
 | .r44, v0, v1, v2 => (ct76 v0)
def R : Rule → T → T → T → T
 | .r0, v0, v1, v2 => (zz2 v0 v1)
 | .r1, v0, v1, v2 => v0
 | .r2, v0, v1, v2 => (zz3 )
 | .r3, v0, v1, v2 => (ct2 v1 v0)
 | .r4, v0, v1, v2 => v1
 | .r5, v0, v1, v2 => v0
 | .r6, v0, v1, v2 => v0
 | .r7, v0, v1, v2 => (ct10 v0 v1)
 | .r8, v0, v1, v2 => (ct15 v0 v1)
 | .r9, v0, v1, v2 => v1
 | .r10, v0, v1, v2 => (zz2 v0 v0)
 | .r11, v0, v1, v2 => (zz3 )
 | .r12, v0, v1, v2 => (ct24 v0 v1)
 | .r13, v0, v1, v2 => (zz2 v1 v0)
 | .r14, v0, v1, v2 => v0
 | .r15, v0, v1, v2 => (ct20 v0)
 | .r16, v0, v1, v2 => v0
 | .r17, v0, v1, v2 => v0
 | .r18, v0, v1, v2 => (ct17 v0)
 | .r19, v0, v1, v2 => (ct27 v0)
 | .r20, v0, v1, v2 => (ct30 v0)
 | .r21, v0, v1, v2 => v0
 | .r22, v0, v1, v2 => (ct17 v0)
 | .r23, v0, v1, v2 => (ct27 v0)
 | .r24, v0, v1, v2 => v0
 | .r25, v0, v1, v2 => v1
 | .r26, v0, v1, v2 => (ct20 v0)
 | .r27, v0, v1, v2 => v0
 | .r28, v0, v1, v2 => (ct17 v0)
 | .r29, v0, v1, v2 => (ct27 v0)
 | .r30, v0, v1, v2 => (ct30 v0)
 | .r31, v0, v1, v2 => (ct39 v0)
 | .r32, v0, v1, v2 => (ct52 v0)
 | .r33, v0, v1, v2 => (ct42 v0)
 | .r34, v0, v1, v2 => (ct62 v0)
 | .r35, v0, v1, v2 => (ct42 v0)
 | .r36, v0, v1, v2 => (ct42 v0)
 | .r37, v0, v1, v2 => (ct62 v0)
 | .r38, v0, v1, v2 => (ct62 v0)
 | .r39, v0, v1, v2 => (ct35 v0 v1)
 | .r40, v0, v1, v2 => (ct50 v0)
 | .r41, v0, v1, v2 => (ct77 v0)
 | .r42, v0, v1, v2 => (ct78 v0)
 | .r43, v0, v1, v2 => (ct79 v0)
 | .r44, v0, v1, v2 => (ct80 v0)
def Root (t u : T) : Prop :=
 ∃ k v0 v1 v2, t = L k v0 v1 v2 ∧ u = R k v0 v1 v2
inductive Step : T → T → Prop where
 | root {a b : T} : Root a b → Step a b
 | cQ0 {a b : T} (x2 : T) : Step a b → Step (op a x2) (op b x2)
 | cQ1 {a b : T} (x1 : T) : Step a b → Step (op x1 a) (op x1 b)
 | cQ2 {a b : T} (x2 : T) : Step a b → Step (zz0 a x2) (zz0 b x2)
 | cQ3 {a b : T} (x1 : T) : Step a b → Step (zz0 x1 a) (zz0 x1 b)
 | cQ4 {a b : T} (x2 x3 : T) : Step a b → Step (zz1 a x2 x3) (zz1 b x2 x3)
 | cQ5 {a b : T} (x1 x3 : T) : Step a b → Step (zz1 x1 a x3) (zz1 x1 b x3)
 | cQ6 {a b : T} (x1 x2 : T) : Step a b → Step (zz1 x1 x2 a) (zz1 x1 x2 b)
 | cQ7 {a b : T} (x2 : T) : Step a b → Step (zz2 a x2) (zz2 b x2)
 | cQ8 {a b : T} (x1 : T) : Step a b → Step (zz2 x1 a) (zz2 x1 b)
 | cQ9 {a b : T} (x2 : T) : Step a b → Step (zz4 a x2) (zz4 b x2)
 | cQ10 {a b : T} (x1 : T) : Step a b → Step (zz4 x1 a) (zz4 x1 b)
 | cQ11 {a b : T} (x2 : T) : Step a b → Step (zz5 a x2) (zz5 b x2)
 | cQ12 {a b : T} (x1 : T) : Step a b → Step (zz5 x1 a) (zz5 x1 b)
abbrev Reach := Relation.ReflTransGen Step
theorem rr {a : T} : Reach a a := .refl
def Join (a b : T) : Prop := ∃ c, Reach a c ∧ Reach b c
theorem rs (k : Rule) (v0 v1 v2 : T) : Step (L k v0 v1 v2) (R k v0 v1 v2) :=
 .root ⟨k, v0, v1, v2, rfl, rfl⟩
theorem root_decrease {a b : T} (h : Root a b) : sz b < sz a := by
 rcases h with ⟨k, v0, v1, v2, hl, hr⟩
 rw [hl, hr]
 have hp_v0 := sz_pos v0
 have hp_v1 := sz_pos v1
 have hp_v2 := sz_pos v2
 cases k <;> simp only [L, R, sz] <;> omega
theorem step_decrease {a b : T} (h : Step a b) : sz b < sz a := by
 induction h with
 | root h => exact root_decrease h
 | cQ0 x2 h ih => simp only [sz]; omega
 | cQ1 x1 h ih => simp only [sz]; omega
 | cQ2 x2 h ih => simp only [sz]; omega
 | cQ3 x1 h ih => simp only [sz]; omega
 | cQ4 x2 x3 h ih => simp only [sz]; omega
 | cQ5 x1 x3 h ih => simp only [sz]; omega
 | cQ6 x1 x2 h ih => simp only [sz]; omega
 | cQ7 x2 h ih => simp only [sz]; omega
 | cQ8 x1 h ih => simp only [sz]; omega
 | cQ9 x2 h ih => simp only [sz]; omega
 | cQ10 x1 h ih => simp only [sz]; omega
 | cQ11 x2 h ih => simp only [sz]; omega
 | cQ12 x1 h ih => simp only [sz]; omega
theorem reach_size {a b : T} (h : Reach a b) : sz b ≤ sz a := by
 induction h with
 | refl => exact Nat.le_refl _
 | tail h hs ih => have hd := step_decrease hs; omega
theorem join_symm {a b : T} (h : Join a b) : Join b a := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨c, h2, h1⟩
theorem reach_op_1 {a b : T} (x2 : T) (h : Reach a b) : Reach (op a x2) (op b x2) :=
 h.lift (fun a => (op a x2)) (fun _ _ h => (Step.cQ0 x2 h))
theorem join_op_1 {a b : T} (x2 : T) (h : Join a b) : Join (op a x2) (op b x2) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(op c x2), reach_op_1 x2 h1, reach_op_1 x2 h2⟩
theorem reach_op_2 {a b : T} (x1 : T) (h : Reach a b) : Reach (op x1 a) (op x1 b) :=
 h.lift (fun a => (op x1 a)) (fun _ _ h => (Step.cQ1 x1 h))
theorem join_op_2 {a b : T} (x1 : T) (h : Join a b) : Join (op x1 a) (op x1 b) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(op x1 c), reach_op_2 x1 h1, reach_op_2 x1 h2⟩
theorem step_op_cases {x1 x2 u : T} (h : Step (op x1 x2) u) :
  Root (op x1 x2) u ∨ (∃ v, u = (op v x2) ∧ Step x1 v) ∨ (∃ v, u = (op x1 v) ∧ Step x2 v) := by
 cases h with
 | root h => exact Or.inl h
 | cQ0 _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
 | cQ1 _ h => exact (Or.inr (Or.inr ⟨_, rfl, h⟩))
theorem reach_zz0_1 {a b : T} (x2 : T) (h : Reach a b) : Reach (zz0 a x2) (zz0 b x2) :=
 h.lift (fun a => (zz0 a x2)) (fun _ _ h => (Step.cQ2 x2 h))
theorem join_zz0_1 {a b : T} (x2 : T) (h : Join a b) : Join (zz0 a x2) (zz0 b x2) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz0 c x2), reach_zz0_1 x2 h1, reach_zz0_1 x2 h2⟩
theorem reach_zz0_2 {a b : T} (x1 : T) (h : Reach a b) : Reach (zz0 x1 a) (zz0 x1 b) :=
 h.lift (fun a => (zz0 x1 a)) (fun _ _ h => (Step.cQ3 x1 h))
theorem join_zz0_2 {a b : T} (x1 : T) (h : Join a b) : Join (zz0 x1 a) (zz0 x1 b) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz0 x1 c), reach_zz0_2 x1 h1, reach_zz0_2 x1 h2⟩
theorem step_zz0_cases {x1 x2 u : T} (h : Step (zz0 x1 x2) u) :
  Root (zz0 x1 x2) u ∨ (∃ v, u = (zz0 v x2) ∧ Step x1 v) ∨ (∃ v, u = (zz0 x1 v) ∧ Step x2 v) := by
 cases h with
 | root h => exact Or.inl h
 | cQ2 _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
 | cQ3 _ h => exact (Or.inr (Or.inr ⟨_, rfl, h⟩))
theorem reach_zz1_1 {a b : T} (x2 x3 : T) (h : Reach a b) : Reach (zz1 a x2 x3) (zz1 b x2 x3) :=
 h.lift (fun a => (zz1 a x2 x3)) (fun _ _ h => (Step.cQ4 x2 x3 h))
theorem join_zz1_1 {a b : T} (x2 x3 : T) (h : Join a b) : Join (zz1 a x2 x3) (zz1 b x2 x3) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz1 c x2 x3), reach_zz1_1 x2 x3 h1, reach_zz1_1 x2 x3 h2⟩
theorem reach_zz1_2 {a b : T} (x1 x3 : T) (h : Reach a b) : Reach (zz1 x1 a x3) (zz1 x1 b x3) :=
 h.lift (fun a => (zz1 x1 a x3)) (fun _ _ h => (Step.cQ5 x1 x3 h))
theorem join_zz1_2 {a b : T} (x1 x3 : T) (h : Join a b) : Join (zz1 x1 a x3) (zz1 x1 b x3) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz1 x1 c x3), reach_zz1_2 x1 x3 h1, reach_zz1_2 x1 x3 h2⟩
theorem reach_zz1_3 {a b : T} (x1 x2 : T) (h : Reach a b) : Reach (zz1 x1 x2 a) (zz1 x1 x2 b) :=
 h.lift (fun a => (zz1 x1 x2 a)) (fun _ _ h => (Step.cQ6 x1 x2 h))
theorem join_zz1_3 {a b : T} (x1 x2 : T) (h : Join a b) : Join (zz1 x1 x2 a) (zz1 x1 x2 b) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz1 x1 x2 c), reach_zz1_3 x1 x2 h1, reach_zz1_3 x1 x2 h2⟩
theorem step_zz1_cases {x1 x2 x3 u : T} (h : Step (zz1 x1 x2 x3) u) :
  Root (zz1 x1 x2 x3) u ∨ (∃ v, u = (zz1 v x2 x3) ∧ Step x1 v) ∨ (∃ v, u = (zz1 x1 v x3) ∧ Step x2 v) ∨ (∃ v, u = (zz1 x1 x2 v) ∧ Step x3 v) := by
 cases h with
 | root h => exact Or.inl h
 | cQ4 _ _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
 | cQ5 _ _ h => exact (Or.inr (Or.inr (Or.inl ⟨_, rfl, h⟩)))
 | cQ6 _ _ h => exact (Or.inr (Or.inr (Or.inr ⟨_, rfl, h⟩)))
theorem reach_zz2_1 {a b : T} (x2 : T) (h : Reach a b) : Reach (zz2 a x2) (zz2 b x2) :=
 h.lift (fun a => (zz2 a x2)) (fun _ _ h => (Step.cQ7 x2 h))
theorem join_zz2_1 {a b : T} (x2 : T) (h : Join a b) : Join (zz2 a x2) (zz2 b x2) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz2 c x2), reach_zz2_1 x2 h1, reach_zz2_1 x2 h2⟩
theorem reach_zz2_2 {a b : T} (x1 : T) (h : Reach a b) : Reach (zz2 x1 a) (zz2 x1 b) :=
 h.lift (fun a => (zz2 x1 a)) (fun _ _ h => (Step.cQ8 x1 h))
theorem join_zz2_2 {a b : T} (x1 : T) (h : Join a b) : Join (zz2 x1 a) (zz2 x1 b) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz2 x1 c), reach_zz2_2 x1 h1, reach_zz2_2 x1 h2⟩
theorem step_zz2_cases {x1 x2 u : T} (h : Step (zz2 x1 x2) u) :
  Root (zz2 x1 x2) u ∨ (∃ v, u = (zz2 v x2) ∧ Step x1 v) ∨ (∃ v, u = (zz2 x1 v) ∧ Step x2 v) := by
 cases h with
 | root h => exact Or.inl h
 | cQ7 _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
 | cQ8 _ h => exact (Or.inr (Or.inr ⟨_, rfl, h⟩))
theorem step_zz3_cases { u : T} (h : Step (zz3 ) u) :
  Root (zz3 ) u := by
 cases h with
 | root h => exact h
theorem reach_zz4_1 {a b : T} (x2 : T) (h : Reach a b) : Reach (zz4 a x2) (zz4 b x2) :=
 h.lift (fun a => (zz4 a x2)) (fun _ _ h => (Step.cQ9 x2 h))
theorem join_zz4_1 {a b : T} (x2 : T) (h : Join a b) : Join (zz4 a x2) (zz4 b x2) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz4 c x2), reach_zz4_1 x2 h1, reach_zz4_1 x2 h2⟩
theorem reach_zz4_2 {a b : T} (x1 : T) (h : Reach a b) : Reach (zz4 x1 a) (zz4 x1 b) :=
 h.lift (fun a => (zz4 x1 a)) (fun _ _ h => (Step.cQ10 x1 h))
theorem join_zz4_2 {a b : T} (x1 : T) (h : Join a b) : Join (zz4 x1 a) (zz4 x1 b) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz4 x1 c), reach_zz4_2 x1 h1, reach_zz4_2 x1 h2⟩
theorem step_zz4_cases {x1 x2 u : T} (h : Step (zz4 x1 x2) u) :
  Root (zz4 x1 x2) u ∨ (∃ v, u = (zz4 v x2) ∧ Step x1 v) ∨ (∃ v, u = (zz4 x1 v) ∧ Step x2 v) := by
 cases h with
 | root h => exact Or.inl h
 | cQ9 _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
 | cQ10 _ h => exact (Or.inr (Or.inr ⟨_, rfl, h⟩))
theorem reach_zz5_1 {a b : T} (x2 : T) (h : Reach a b) : Reach (zz5 a x2) (zz5 b x2) :=
 h.lift (fun a => (zz5 a x2)) (fun _ _ h => (Step.cQ11 x2 h))
theorem join_zz5_1 {a b : T} (x2 : T) (h : Join a b) : Join (zz5 a x2) (zz5 b x2) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz5 c x2), reach_zz5_1 x2 h1, reach_zz5_1 x2 h2⟩
theorem reach_zz5_2 {a b : T} (x1 : T) (h : Reach a b) : Reach (zz5 x1 a) (zz5 x1 b) :=
 h.lift (fun a => (zz5 x1 a)) (fun _ _ h => (Step.cQ12 x1 h))
theorem join_zz5_2 {a b : T} (x1 : T) (h : Join a b) : Join (zz5 x1 a) (zz5 x1 b) := by
 rcases h with ⟨c, h1, h2⟩
 exact ⟨(zz5 x1 c), reach_zz5_2 x1 h1, reach_zz5_2 x1 h2⟩
theorem step_zz5_cases {x1 x2 u : T} (h : Step (zz5 x1 x2) u) :
  Root (zz5 x1 x2) u ∨ (∃ v, u = (zz5 v x2) ∧ Step x1 v) ∨ (∃ v, u = (zz5 x1 v) ∧ Step x2 v) := by
 cases h with
 | root h => exact Or.inl h
 | cQ11 _ h => exact (Or.inr (Or.inl ⟨_, rfl, h⟩))
 | cQ12 _ h => exact (Or.inr (Or.inr ⟨_, rfl, h⟩))
theorem vP0 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (zz2 a0 a1) (zz0 v a1) := by
 exact ⟨(zz2 v a1), (rr.tail (Step.cQ7 a1 hv)), (rr.tail (rs .r0 v a1 a2))⟩
theorem vP1 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (zz2 a0 a1) (zz0 a0 v) := by
 exact ⟨(zz2 a0 v), (rr.tail (Step.cQ8 a0 hv)), (rr.tail (rs .r0 a0 v a2))⟩
theorem vP23 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct0 v a1) := by
 exact ⟨v, (rr.tail hv), (rr.tail (rs .r1 v a1 a2))⟩
theorem vP24 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join a0 (ct81 a0 v a1) := by
 exact ⟨a0, rr, ((rr.tail (Step.cQ12 (zz4 a0 v) hv)).tail (rs .r1 a0 v a2))⟩
theorem vP25 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join a0 (ct81 a0 a1 v) := by
 exact ⟨a0, rr, ((rr.tail (Step.cQ11 v (Step.cQ10 a0 hv))).tail (rs .r1 a0 v a2))⟩
theorem vP52 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (zz3 ) (ct82 v a0) := by
 exact ⟨(zz3 ), rr, (((rr.tail (Step.cQ12 v (Step.cQ7 a0 hv))).tail (Step.cQ12 v (Step.cQ8 v hv))).tail (rs .r2 v a1 a2))⟩
theorem vP53 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (zz3 ) (ct2 a0 v) := by
 exact ⟨(zz3 ), rr, (((rr.tail (Step.cQ11 (zz2 v a0) hv)).tail (Step.cQ12 v (Step.cQ8 v hv))).tail (rs .r2 v a1 a2))⟩
theorem vP54 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (zz3 ) (ct83 a0 v) := by
 exact ⟨(zz3 ), rr, (((rr.tail (Step.cQ11 (zz2 a0 v) hv)).tail (Step.cQ12 v (Step.cQ7 v hv))).tail (rs .r2 v a1 a2))⟩
theorem vP82 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct2 a1 a0) (op v a1) := by
 exact ⟨(ct2 a1 v), (rr.tail (Step.cQ12 a1 (Step.cQ7 a1 hv))), (rr.tail (rs .r3 v a1 a2))⟩
theorem vP83 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (ct2 a1 a0) (op a0 v) := by
 exact ⟨(ct2 v a0), ((rr.tail (Step.cQ11 (zz2 a0 a1) hv)).tail (Step.cQ12 v (Step.cQ8 a0 hv))), (rr.tail (rs .r3 a0 v a2))⟩
theorem vP100 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a1 (ct84 v a0 a1) := by
 exact ⟨a1, rr, (((rr.tail (Step.cQ12 v (Step.cQ11 (zz2 a1 a0) hv))).tail (Step.cQ12 v (Step.cQ12 v (Step.cQ8 a1 hv)))).tail (rs .r4 v a1 a2))⟩
theorem vP101 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a1 (ct86 a0 v a1) := by
 exact ⟨a1, rr, (((rr.tail (Step.cQ11 (ct85 v a1 a0) hv)).tail (Step.cQ12 v (Step.cQ12 v (Step.cQ8 a1 hv)))).tail (rs .r4 v a1 a2))⟩
theorem vP102 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join a1 (ct3 a0 v) := by
 exact ⟨v, (rr.tail hv), (rr.tail (rs .r4 a0 v a2))⟩
theorem vP103 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a1 (ct87 a0 a1 v) := by
 exact ⟨a1, rr, (((rr.tail (Step.cQ11 (ct85 a0 a1 v) hv)).tail (Step.cQ12 v (Step.cQ11 (zz2 a1 v) hv))).tail (rs .r4 v a1 a2))⟩
theorem vP104 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct4 v) := by
 exact ⟨v, (rr.tail hv), (rr.tail (rs .r5 v a1 a2))⟩
theorem vP105 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct5 v) := by
 exact ⟨v, (rr.tail hv), (rr.tail (rs .r6 v a1 a2))⟩
theorem vP106 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct10 a0 a1) (ct88 v a1 a0) := by
 exact ⟨(ct10 v a1), ((rr.tail (Step.cQ7 (zz4 a0 a1) hv)).tail (Step.cQ8 v (Step.cQ9 a1 hv))), ((rr.tail (Step.cQ12 (zz4 v a1) (Step.cQ8 a1 (Step.cQ9 a1 hv)))).tail (rs .r7 v a1 a2))⟩
theorem vP107 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (ct10 a0 a1) (ct89 a0 v a1) := by
 exact ⟨(ct10 a0 v), (rr.tail (Step.cQ8 a0 (Step.cQ10 a0 hv))), (((rr.tail (Step.cQ12 (zz4 a0 v) (Step.cQ7 (zz4 a0 a1) hv))).tail (Step.cQ12 (zz4 a0 v) (Step.cQ8 v (Step.cQ10 a0 hv)))).tail (rs .r7 a0 v a2))⟩
theorem vP108 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (ct10 a0 a1) (ct91 a0 a1 v) := by
 exact ⟨(ct10 a0 v), (rr.tail (Step.cQ8 a0 (Step.cQ10 a0 hv))), (((rr.tail (Step.cQ11 (ct90 v a0 a1) (Step.cQ10 a0 hv))).tail (Step.cQ12 (zz4 a0 v) (Step.cQ8 v (Step.cQ10 a0 hv)))).tail (rs .r7 a0 v a2))⟩
theorem vP109 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct10 a0 a1) (ct88 a0 a1 v) := by
 exact ⟨(ct10 v a1), ((rr.tail (Step.cQ7 (zz4 a0 a1) hv)).tail (Step.cQ8 v (Step.cQ9 a1 hv))), ((rr.tail (Step.cQ11 (ct6 a1 v) (Step.cQ9 a1 hv))).tail (rs .r7 v a1 a2))⟩
theorem vP110 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (ct10 a0 a1) (ct92 a0 a1 v) := by
 exact ⟨(ct10 a0 v), (rr.tail (Step.cQ8 a0 (Step.cQ10 a0 hv))), (((rr.tail (Step.cQ11 (ct90 a1 a0 v) (Step.cQ10 a0 hv))).tail (Step.cQ12 (zz4 a0 v) (Step.cQ7 (zz4 a0 v) hv))).tail (rs .r7 a0 v a2))⟩
theorem vP111 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct15 a0 a1) (ct93 v a1 a0) := by
 exact ⟨(ct15 v a1), (((rr.tail (Step.cQ7 a0 (Step.cQ11 (zz2 a1 a0) hv))).tail (Step.cQ7 a0 (Step.cQ12 v (Step.cQ8 a1 hv)))).tail (Step.cQ8 (ct2 v a1) hv)), (((rr.tail (Step.cQ12 v (Step.cQ7 a0 (Step.cQ8 a1 hv)))).tail (Step.cQ12 v (Step.cQ8 (zz2 a1 v) hv))).tail (rs .r8 v a1 a2))⟩
theorem vP112 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (ct15 a0 a1) (ct9 a0 v) := by
 exact ⟨(ct15 a0 v), (rr.tail (Step.cQ7 a0 (Step.cQ12 a0 (Step.cQ7 a0 hv)))), (rr.tail (rs .r8 a0 v a2))⟩
theorem vP113 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct15 a0 a1) (ct95 a0 a1 v) := by
 exact ⟨(ct15 v a1), (((rr.tail (Step.cQ7 a0 (Step.cQ11 (zz2 a1 a0) hv))).tail (Step.cQ7 a0 (Step.cQ12 v (Step.cQ8 a1 hv)))).tail (Step.cQ8 (ct2 v a1) hv)), (((rr.tail (Step.cQ11 (ct94 a1 v a0) hv)).tail (Step.cQ12 v (Step.cQ8 (zz2 a1 v) hv))).tail (rs .r8 v a1 a2))⟩
theorem vP114 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct15 a0 a1) (ct96 a0 a1 v) := by
 exact ⟨(ct15 v a1), (((rr.tail (Step.cQ7 a0 (Step.cQ11 (zz2 a1 a0) hv))).tail (Step.cQ7 a0 (Step.cQ12 v (Step.cQ8 a1 hv)))).tail (Step.cQ8 (ct2 v a1) hv)), (((rr.tail (Step.cQ11 (ct94 a1 a0 v) hv)).tail (Step.cQ12 v (Step.cQ7 v (Step.cQ8 a1 hv)))).tail (rs .r8 v a1 a2))⟩
theorem vP115 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a1 (ct97 v a1 a0) := by
 exact ⟨a1, rr, (((rr.tail (Step.cQ12 (zz4 v a1) (Step.cQ7 (zz4 a0 a1) hv))).tail (Step.cQ12 (zz4 v a1) (Step.cQ8 v (Step.cQ9 a1 hv)))).tail (rs .r9 v a1 a2))⟩
theorem vP116 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join a1 (ct98 a0 v a1) := by
 exact ⟨v, (rr.tail hv), ((rr.tail (Step.cQ12 (zz4 a0 v) (Step.cQ8 a0 (Step.cQ10 a0 hv)))).tail (rs .r9 a0 v a2))⟩
theorem vP117 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a1 (ct91 a0 a1 v) := by
 exact ⟨a1, rr, (((rr.tail (Step.cQ11 (ct90 v a0 a1) (Step.cQ9 a1 hv))).tail (Step.cQ12 (zz4 v a1) (Step.cQ8 v (Step.cQ9 a1 hv)))).tail (rs .r9 v a1 a2))⟩
theorem vP118 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a1 (ct99 a0 a1 v) := by
 exact ⟨a1, rr, (((rr.tail (Step.cQ11 (ct90 a0 v a1) (Step.cQ9 a1 hv))).tail (Step.cQ12 (zz4 v a1) (Step.cQ7 (zz4 v a1) hv))).tail (rs .r9 v a1 a2))⟩
theorem vP119 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join a1 (ct98 a0 a1 v) := by
 exact ⟨v, (rr.tail hv), ((rr.tail (Step.cQ11 (ct10 a0 v) (Step.cQ10 a0 hv))).tail (rs .r9 a0 v a2))⟩
theorem vP2 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (zz2 a0 a0) (ct100 v a0) := by
 exact ⟨(zz2 v v), ((rr.tail (Step.cQ7 a0 hv)).tail (Step.cQ8 v hv)), ((rr.tail (Step.cQ12 v (Step.cQ8 (zz3 ) hv))).tail (rs .r10 v a1 a2))⟩
theorem vP3 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (zz2 a0 a0) (ct100 a0 v) := by
 exact ⟨(zz2 v v), ((rr.tail (Step.cQ7 a0 hv)).tail (Step.cQ8 v hv)), ((rr.tail (Step.cQ11 (ct12 v) hv)).tail (rs .r10 v a1 a2))⟩
theorem vP4 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct24 a0 a1) (zz1 v a1 a2) := by
 exact ⟨(ct24 v a1), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a1 hv)))), (rr.tail (rs .r12 v a1 a2))⟩
theorem vP5 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (ct24 a0 a1) (zz1 a0 v a2) := by
 exact ⟨(ct24 a0 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv)))), (rr.tail (rs .r12 a0 v a2))⟩
theorem vP6 (a0 a1 a2 v : T) (hv : Step a2 v) :
  Join (ct24 a0 a1) (zz1 a0 a1 v) := by
 exact ⟨(ct24 a0 a1), rr, (rr.tail (rs .r12 a0 a1 v))⟩
theorem vP7 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (zz2 a1 a0) (ct101 v a0 a1) := by
 exact ⟨(zz2 a1 v), (rr.tail (Step.cQ8 a1 hv)), ((((rr.tail (Step.cQ12 v (Step.cQ7 a0 (Step.cQ11 (zz2 a1 a0) hv)))).tail (Step.cQ12 v (Step.cQ7 a0 (Step.cQ12 v (Step.cQ8 a1 hv))))).tail (Step.cQ12 v (Step.cQ8 (ct2 v a1) hv))).tail (rs .r13 v a1 a2))⟩
theorem vP8 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (zz2 a1 a0) (ct104 a0 v a1) := by
 exact ⟨(zz2 a1 v), (rr.tail (Step.cQ8 a1 hv)), ((((rr.tail (Step.cQ11 (ct102 v a1 a0) hv)).tail (Step.cQ12 v (Step.cQ7 a0 (Step.cQ12 v (Step.cQ8 a1 hv))))).tail (Step.cQ12 v (Step.cQ8 (ct2 v a1) hv))).tail (rs .r13 v a1 a2))⟩
theorem vP9 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (zz2 a1 a0) (ct16 a0 v) := by
 exact ⟨(zz2 v a0), (rr.tail (Step.cQ7 a0 hv)), (rr.tail (rs .r13 a0 v a2))⟩
theorem vP10 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (zz2 a1 a0) (ct106 a0 a1 v) := by
 exact ⟨(zz2 a1 v), (rr.tail (Step.cQ8 a1 hv)), ((((rr.tail (Step.cQ11 (ct105 a0 a1 v) hv)).tail (Step.cQ12 v (Step.cQ7 a0 (Step.cQ11 (zz2 a1 v) hv)))).tail (Step.cQ12 v (Step.cQ8 (ct2 v a1) hv))).tail (rs .r13 v a1 a2))⟩
theorem vP11 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (zz2 a1 a0) (ct107 a0 a1 v) := by
 exact ⟨(zz2 a1 v), (rr.tail (Step.cQ8 a1 hv)), ((((rr.tail (Step.cQ11 (ct103 a0 a1 v) hv)).tail (Step.cQ12 v (Step.cQ7 v (Step.cQ11 (zz2 a1 a0) hv)))).tail (Step.cQ12 v (Step.cQ7 v (Step.cQ12 v (Step.cQ8 a1 hv))))).tail (rs .r13 v a1 a2))⟩
theorem vP12 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct108 v a0) := by
 exact ⟨v, (rr.tail hv), ((rr.tail (Step.cQ8 (ct17 v) (Step.cQ10 (zz3 ) hv))).tail (rs .r14 v a1 a2))⟩
theorem vP13 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct108 a0 v) := by
 exact ⟨v, (rr.tail hv), ((rr.tail (Step.cQ7 (ct17 v) (Step.cQ10 (zz3 ) hv))).tail (rs .r14 v a1 a2))⟩
theorem vP14 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct20 a0) (ct19 v) := by
 exact ⟨(ct20 v), (rr.tail (Step.cQ7 (zz3 ) hv)), (rr.tail (rs .r15 v a1 a2))⟩
theorem vP15 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct22 v) := by
 exact ⟨v, (rr.tail hv), (rr.tail (rs .r16 v a1 a2))⟩
theorem vP16 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct25 v a1) := by
 exact ⟨v, (rr.tail hv), (rr.tail (rs .r17 v a1 a2))⟩
theorem vP17 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join a0 (ct109 a0 v a1) := by
 exact ⟨a0, rr, ((rr.tail (Step.cQ12 (ct24 a0 v) hv)).tail (rs .r17 a0 v a2))⟩
theorem vP18 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join a0 (ct109 a0 a1 v) := by
 exact ⟨a0, rr, ((rr.tail (Step.cQ11 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv))))).tail (rs .r17 a0 v a2))⟩
theorem vP19 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct17 a0) (ct110 v a0) := by
 exact ⟨(ct17 v), (rr.tail (Step.cQ10 (zz3 ) hv)), ((rr.tail (Step.cQ12 (ct21 v) (Step.cQ10 (zz3 ) hv))).tail (rs .r18 v a1 a2))⟩
theorem vP20 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct17 a0) (ct110 a0 v) := by
 exact ⟨(ct17 v), (rr.tail (Step.cQ10 (zz3 ) hv)), ((rr.tail (Step.cQ11 (ct17 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (rs .r18 v a1 a2))⟩
theorem vP21 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct27 a0) (ct111 v a0) := by
 exact ⟨(ct27 v), (rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv))), ((rr.tail (Step.cQ12 v (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (rs .r19 v a1 a2))⟩
theorem vP22 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct27 a0) (ct111 a0 v) := by
 exact ⟨(ct27 v), (rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv))), ((rr.tail (Step.cQ11 (ct27 v) hv)).tail (rs .r19 v a1 a2))⟩
theorem vP26 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct30 a0) (zz4 v a0) := by
 exact ⟨(ct30 v), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a0 hv)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv)))), ((rr.tail (Step.cQ10 v hv)).tail (rs .r20 v a1 a2))⟩
theorem vP27 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct30 a0) (zz4 a0 v) := by
 exact ⟨(ct30 v), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a0 hv)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv)))), ((rr.tail (Step.cQ9 v hv)).tail (rs .r20 v a1 a2))⟩
theorem vP28 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct112 v a0) := by
 exact ⟨v, (rr.tail hv), (((rr.tail (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a0 hv))))).tail (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv))))).tail (rs .r21 v a1 a2))⟩
theorem vP29 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct65 a0 v) := by
 exact ⟨v, (rr.tail hv), (((rr.tail (Step.cQ7 (ct24 v a0) hv)).tail (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv))))).tail (rs .r21 v a1 a2))⟩
theorem vP30 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct35 a0 v) := by
 exact ⟨v, (rr.tail hv), (((rr.tail (Step.cQ7 (ct24 a0 v) hv)).tail (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 v hv))))).tail (rs .r21 v a1 a2))⟩
theorem vP31 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct17 a0) (ct113 v a0) := by
 exact ⟨(ct17 v), (rr.tail (Step.cQ10 (zz3 ) hv)), ((rr.tail (Step.cQ8 (ct17 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (rs .r22 v a1 a2))⟩
theorem vP32 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct17 a0) (ct113 a0 v) := by
 exact ⟨(ct17 v), (rr.tail (Step.cQ10 (zz3 ) hv)), ((rr.tail (Step.cQ7 (ct21 v) (Step.cQ10 (zz3 ) hv))).tail (rs .r22 v a1 a2))⟩
theorem vP33 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct27 a0) (ct114 v a0) := by
 exact ⟨(ct27 v), (rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv))), ((rr.tail (Step.cQ8 (ct27 v) hv)).tail (rs .r23 v a1 a2))⟩
theorem vP34 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct27 a0) (ct114 a0 v) := by
 exact ⟨(ct27 v), (rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv))), ((rr.tail (Step.cQ7 v (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (rs .r23 v a1 a2))⟩
theorem vP35 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct115 v a0) := by
 exact ⟨v, (rr.tail hv), (((rr.tail (Step.cQ12 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a0 hv))))).tail (Step.cQ12 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv))))).tail (rs .r24 v a1 a2))⟩
theorem vP36 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct116 a0 v) := by
 exact ⟨v, (rr.tail hv), (((rr.tail (Step.cQ11 (ct24 v a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ12 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv))))).tail (rs .r24 v a1 a2))⟩
theorem vP37 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct117 a0 v) := by
 exact ⟨v, (rr.tail hv), (((rr.tail (Step.cQ11 (ct24 a0 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ12 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 v hv))))).tail (rs .r24 v a1 a2))⟩
theorem vP38 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a1 (ct118 v a1 a0) := by
 exact ⟨a1, rr, (((rr.tail (Step.cQ12 (ct24 v a1) (Step.cQ7 (ct24 a0 a1) hv))).tail (Step.cQ12 (ct24 v a1) (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a1 hv)))))).tail (rs .r25 v a1 a2))⟩
theorem vP39 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join a1 (ct120 a0 v a1) := by
 exact ⟨v, (rr.tail hv), ((rr.tail (Step.cQ12 (ct24 a0 v) (Step.cQ8 a0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv)))))).tail (rs .r25 a0 v a2))⟩
theorem vP40 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a1 (ct121 a0 a1 v) := by
 exact ⟨a1, rr, (((rr.tail (Step.cQ11 (ct119 v a0 a1) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a1 hv))))).tail (Step.cQ12 (ct24 v a1) (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a1 hv)))))).tail (rs .r25 v a1 a2))⟩
theorem vP41 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a1 (ct122 a0 a1 v) := by
 exact ⟨a1, rr, (((rr.tail (Step.cQ11 (ct119 a0 v a1) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a1 hv))))).tail (Step.cQ12 (ct24 v a1) (Step.cQ7 (ct24 v a1) hv))).tail (rs .r25 v a1 a2))⟩
theorem vP42 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join a1 (ct120 a0 a1 v) := by
 exact ⟨v, (rr.tail hv), ((rr.tail (Step.cQ11 (ct35 a0 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv))))).tail (rs .r25 a0 v a2))⟩
theorem vP43 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct20 a0) (ct123 v a0) := by
 exact ⟨(ct20 v), (rr.tail (Step.cQ7 (zz3 ) hv)), (((rr.tail (Step.cQ12 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct20 a0) (Step.cQ7 (zz3 ) hv)))))).tail (Step.cQ12 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (ct20 v) (Step.cQ7 (zz3 ) hv)))))).tail (rs .r26 v a1 a2))⟩
theorem vP44 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct20 a0) (ct127 a0 v) := by
 exact ⟨(ct20 v), (rr.tail (Step.cQ7 (zz3 ) hv)), (((rr.tail (Step.cQ11 (ct126 v a0) hv)).tail (Step.cQ12 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (ct20 v) (Step.cQ7 (zz3 ) hv)))))).tail (rs .r26 v a1 a2))⟩
theorem vP45 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct20 a0) (ct128 a0 v) := by
 exact ⟨(ct20 v), (rr.tail (Step.cQ7 (zz3 ) hv)), (((rr.tail (Step.cQ11 (ct126 a0 v) hv)).tail (Step.cQ12 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct20 v) (Step.cQ7 (zz3 ) hv)))))).tail (rs .r26 v a1 a2))⟩
theorem vP46 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct129 v a0) := by
 exact ⟨v, (rr.tail hv), ((rr.tail (Step.cQ8 (ct42 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv))))).tail (rs .r27 v a1 a2))⟩
theorem vP47 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join a0 (ct129 a0 v) := by
 exact ⟨v, (rr.tail hv), ((rr.tail (Step.cQ7 (ct42 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv))))).tail (rs .r27 v a1 a2))⟩
theorem vP48 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct17 a0) (ct130 v a0) := by
 exact ⟨(ct17 v), (rr.tail (Step.cQ10 (zz3 ) hv)), ((rr.tail (Step.cQ12 (ct45 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (rs .r28 v a1 a2))⟩
theorem vP49 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct17 a0) (ct130 a0 v) := by
 exact ⟨(ct17 v), (rr.tail (Step.cQ10 (zz3 ) hv)), ((rr.tail (Step.cQ11 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) hv))))).tail (rs .r28 v a1 a2))⟩
theorem vP50 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct27 a0) (ct131 v a0) := by
 exact ⟨(ct27 v), (rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv))), ((rr.tail (Step.cQ12 (ct48 v) hv)).tail (rs .r29 v a1 a2))⟩
theorem vP51 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct27 a0) (ct131 a0 v) := by
 exact ⟨(ct27 v), (rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv))), ((rr.tail (Step.cQ11 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))))).tail (rs .r29 v a1 a2))⟩
theorem vP55 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct30 a0) (ct132 v a0) := by
 exact ⟨(ct30 v), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a0 hv)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv)))), (((rr.tail (Step.cQ12 (ct21 v) (Step.cQ7 (ct21 a0) hv))).tail (Step.cQ12 (ct21 v) (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (rs .r30 v a1 a2))⟩
theorem vP56 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct30 a0) (ct134 a0 v) := by
 exact ⟨(ct30 v), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a0 hv)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv)))), (((rr.tail (Step.cQ11 (ct133 v a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ12 (ct21 v) (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (rs .r30 v a1 a2))⟩
theorem vP57 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct30 a0) (ct135 a0 v) := by
 exact ⟨(ct30 v), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a0 hv)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv)))), (((rr.tail (Step.cQ11 (ct133 a0 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ12 (ct21 v) (Step.cQ7 (ct21 v) hv))).tail (rs .r30 v a1 a2))⟩
theorem vP58 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct39 a0) (ct136 v a0) := by
 exact ⟨(ct39 v), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct20 a0) (Step.cQ7 (zz3 ) hv))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (ct20 v) (Step.cQ7 (zz3 ) hv))))), (((rr.tail (Step.cQ12 v (Step.cQ7 a0 (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ12 v (Step.cQ8 (ct20 v) hv))).tail (rs .r31 v a1 a2))⟩
theorem vP59 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct39 a0) (ct138 a0 v) := by
 exact ⟨(ct39 v), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct20 a0) (Step.cQ7 (zz3 ) hv))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (ct20 v) (Step.cQ7 (zz3 ) hv))))), (((rr.tail (Step.cQ11 (ct137 v a0) hv)).tail (Step.cQ12 v (Step.cQ8 (ct20 v) hv))).tail (rs .r31 v a1 a2))⟩
theorem vP60 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct39 a0) (ct139 a0 v) := by
 exact ⟨(ct39 v), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct20 a0) (Step.cQ7 (zz3 ) hv))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (ct20 v) (Step.cQ7 (zz3 ) hv))))), (((rr.tail (Step.cQ11 (ct137 a0 v) hv)).tail (Step.cQ12 v (Step.cQ7 v (Step.cQ7 (zz3 ) hv)))).tail (rs .r31 v a1 a2))⟩
theorem vP61 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct52 a0) (ct140 v a0) := by
 exact ⟨(ct52 v), ((rr.tail (Step.cQ7 a0 (Step.cQ7 (zz3 ) hv))).tail (Step.cQ8 (ct20 v) hv)), ((((rr.tail (Step.cQ12 v (Step.cQ7 a0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct20 a0) (Step.cQ7 (zz3 ) hv))))))).tail (Step.cQ12 v (Step.cQ7 a0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (ct20 v) (Step.cQ7 (zz3 ) hv))))))).tail (Step.cQ12 v (Step.cQ8 (ct39 v) hv))).tail (rs .r32 v a1 a2))⟩
theorem vP62 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct52 a0) (ct143 a0 v) := by
 exact ⟨(ct52 v), ((rr.tail (Step.cQ7 a0 (Step.cQ7 (zz3 ) hv))).tail (Step.cQ8 (ct20 v) hv)), ((((rr.tail (Step.cQ11 (ct141 v a0) hv)).tail (Step.cQ12 v (Step.cQ7 a0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (ct20 v) (Step.cQ7 (zz3 ) hv))))))).tail (Step.cQ12 v (Step.cQ8 (ct39 v) hv))).tail (rs .r32 v a1 a2))⟩
theorem vP63 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct52 a0) (ct145 a0 v) := by
 exact ⟨(ct52 v), ((rr.tail (Step.cQ7 a0 (Step.cQ7 (zz3 ) hv))).tail (Step.cQ8 (ct20 v) hv)), ((((rr.tail (Step.cQ11 (ct144 a0 v) hv)).tail (Step.cQ12 v (Step.cQ7 a0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct20 v) (Step.cQ7 (zz3 ) hv))))))).tail (Step.cQ12 v (Step.cQ8 (ct39 v) hv))).tail (rs .r32 v a1 a2))⟩
theorem vP64 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct52 a0) (ct146 a0 v) := by
 exact ⟨(ct52 v), ((rr.tail (Step.cQ7 a0 (Step.cQ7 (zz3 ) hv))).tail (Step.cQ8 (ct20 v) hv)), ((((rr.tail (Step.cQ11 (ct142 a0 v) hv)).tail (Step.cQ12 v (Step.cQ7 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct20 a0) (Step.cQ7 (zz3 ) hv))))))).tail (Step.cQ12 v (Step.cQ7 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (ct20 v) (Step.cQ7 (zz3 ) hv))))))).tail (rs .r32 v a1 a2))⟩
theorem vP65 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct42 a0) (ct147 v a0) := by
 exact ⟨(ct42 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))), ((rr.tail (Step.cQ12 (ct41 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (rs .r33 v a1 a2))⟩
theorem vP66 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct42 a0) (ct147 a0 v) := by
 exact ⟨(ct42 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))), ((rr.tail (Step.cQ11 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))).tail (rs .r33 v a1 a2))⟩
theorem vP67 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct62 a0) (ct148 v a0) := by
 exact ⟨(ct62 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))), ((rr.tail (Step.cQ12 (ct58 v) hv)).tail (rs .r34 v a1 a2))⟩
theorem vP68 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct62 a0) (ct148 a0 v) := by
 exact ⟨(ct62 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))), ((rr.tail (Step.cQ11 v (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (rs .r34 v a1 a2))⟩
theorem vP69 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct42 a0) (ct149 v a0) := by
 exact ⟨(ct42 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))), ((rr.tail (Step.cQ12 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv))))).tail (rs .r35 v a1 a2))⟩
theorem vP70 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct42 a0) (ct149 a0 v) := by
 exact ⟨(ct42 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))), ((rr.tail (Step.cQ11 (ct42 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (rs .r35 v a1 a2))⟩
theorem vP71 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct42 a0) (ct150 v a0) := by
 exact ⟨(ct42 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))), ((rr.tail (Step.cQ8 (ct42 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (rs .r36 v a1 a2))⟩
theorem vP72 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct42 a0) (ct150 a0 v) := by
 exact ⟨(ct42 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))), ((rr.tail (Step.cQ7 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv))))).tail (rs .r36 v a1 a2))⟩
theorem vP73 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct62 a0) (ct151 v a0) := by
 exact ⟨(ct62 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))), ((rr.tail (Step.cQ12 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv)))))).tail (rs .r37 v a1 a2))⟩
theorem vP74 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct62 a0) (ct151 a0 v) := by
 exact ⟨(ct62 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))), ((rr.tail (Step.cQ11 (ct62 v) hv)).tail (rs .r37 v a1 a2))⟩
theorem vP75 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct62 a0) (ct152 v a0) := by
 exact ⟨(ct62 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))), ((rr.tail (Step.cQ8 (ct62 v) hv)).tail (rs .r38 v a1 a2))⟩
theorem vP76 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct62 a0) (ct152 a0 v) := by
 exact ⟨(ct62 v), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))), ((rr.tail (Step.cQ7 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv)))))).tail (rs .r38 v a1 a2))⟩
theorem vP77 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct35 a0 a1) (ct153 v a1 a0) := by
 exact ⟨(ct35 v a1), ((rr.tail (Step.cQ7 (ct24 a0 a1) hv)).tail (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a1 hv))))), ((rr.tail (Step.cQ12 (ct24 v a1) (Step.cQ8 a1 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a1 hv)))))).tail (rs .r39 v a1 a2))⟩
theorem vP78 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (ct35 a0 a1) (ct154 a0 v a1) := by
 exact ⟨(ct35 a0 v), (rr.tail (Step.cQ8 a0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv))))), (((rr.tail (Step.cQ12 (ct24 a0 v) (Step.cQ7 (ct24 a0 a1) hv))).tail (Step.cQ12 (ct24 a0 v) (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv)))))).tail (rs .r39 a0 v a2))⟩
theorem vP79 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (ct35 a0 a1) (ct121 a0 a1 v) := by
 exact ⟨(ct35 a0 v), (rr.tail (Step.cQ8 a0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv))))), (((rr.tail (Step.cQ11 (ct119 v a0 a1) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv))))).tail (Step.cQ12 (ct24 a0 v) (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv)))))).tail (rs .r39 a0 v a2))⟩
theorem vP80 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct35 a0 a1) (ct153 a0 a1 v) := by
 exact ⟨(ct35 v a1), ((rr.tail (Step.cQ7 (ct24 a0 a1) hv)).tail (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a1 hv))))), ((rr.tail (Step.cQ11 (ct65 a1 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a1 hv))))).tail (rs .r39 v a1 a2))⟩
theorem vP81 (a0 a1 a2 v : T) (hv : Step a1 v) :
  Join (ct35 a0 a1) (ct155 a0 a1 v) := by
 exact ⟨(ct35 a0 v), (rr.tail (Step.cQ8 a0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv))))), (((rr.tail (Step.cQ11 (ct119 a1 a0 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 a0 hv))))).tail (Step.cQ12 (ct24 a0 v) (Step.cQ7 (ct24 a0 v) hv))).tail (rs .r39 a0 v a2))⟩
theorem vP84 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct50 a0) (ct156 v a0) := by
 exact ⟨(ct50 v), ((rr.tail (Step.cQ7 (ct21 a0) hv)).tail (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))), ((((rr.tail (Step.cQ12 (ct21 v) (Step.cQ7 (ct21 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a0 hv)))))).tail (Step.cQ12 (ct21 v) (Step.cQ7 (ct21 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv)))))).tail (Step.cQ12 (ct21 v) (Step.cQ8 (ct30 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (rs .r40 v a1 a2))⟩
theorem vP85 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct50 a0) (ct159 a0 v) := by
 exact ⟨(ct50 v), ((rr.tail (Step.cQ7 (ct21 a0) hv)).tail (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))), ((((rr.tail (Step.cQ11 (ct157 v a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ12 (ct21 v) (Step.cQ7 (ct21 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv)))))).tail (Step.cQ12 (ct21 v) (Step.cQ8 (ct30 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (rs .r40 v a1 a2))⟩
theorem vP86 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct50 a0) (ct161 a0 v) := by
 exact ⟨(ct50 v), ((rr.tail (Step.cQ7 (ct21 a0) hv)).tail (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))), ((((rr.tail (Step.cQ11 (ct160 a0 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ12 (ct21 v) (Step.cQ7 (ct21 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 v hv)))))).tail (Step.cQ12 (ct21 v) (Step.cQ8 (ct30 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (rs .r40 v a1 a2))⟩
theorem vP87 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct50 a0) (ct162 a0 v) := by
 exact ⟨(ct50 v), ((rr.tail (Step.cQ7 (ct21 a0) hv)).tail (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))), ((((rr.tail (Step.cQ11 (ct158 a0 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ12 (ct21 v) (Step.cQ7 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 a0 hv)))))).tail (Step.cQ12 (ct21 v) (Step.cQ7 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 v hv)))))).tail (rs .r40 v a1 a2))⟩
theorem vP88 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct77 a0) (ct163 v a0) := by
 exact ⟨(ct77 v), ((rr.tail (Step.cQ7 (ct41 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv))))).tail (Step.cQ8 (ct42 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))), (((rr.tail (Step.cQ12 (ct41 v) (Step.cQ7 (ct41 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (Step.cQ12 (ct41 v) (Step.cQ8 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv))))).tail (rs .r41 v a1 a2))⟩
theorem vP89 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct77 a0) (ct165 a0 v) := by
 exact ⟨(ct77 v), ((rr.tail (Step.cQ7 (ct41 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv))))).tail (Step.cQ8 (ct42 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))), (((rr.tail (Step.cQ11 (ct164 v a0) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))).tail (Step.cQ12 (ct41 v) (Step.cQ8 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv))))).tail (rs .r41 v a1 a2))⟩
theorem vP90 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct77 a0) (ct166 a0 v) := by
 exact ⟨(ct77 v), ((rr.tail (Step.cQ7 (ct41 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv))))).tail (Step.cQ8 (ct42 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))), (((rr.tail (Step.cQ11 (ct164 a0 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) hv)))).tail (Step.cQ12 (ct41 v) (Step.cQ7 (ct41 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (rs .r41 v a1 a2))⟩
theorem vP91 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct78 a0) (ct167 v a0) := by
 exact ⟨(ct78 v), ((rr.tail (Step.cQ7 (ct45 a0) (Step.cQ10 (zz3 ) hv))).tail (Step.cQ8 (ct17 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) hv))))), (((rr.tail (Step.cQ12 (ct45 v) (Step.cQ7 (ct45 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (Step.cQ12 (ct45 v) (Step.cQ8 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) hv)))))).tail (rs .r42 v a1 a2))⟩
theorem vP92 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct78 a0) (ct169 a0 v) := by
 exact ⟨(ct78 v), ((rr.tail (Step.cQ7 (ct45 a0) (Step.cQ10 (zz3 ) hv))).tail (Step.cQ8 (ct17 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) hv))))), (((rr.tail (Step.cQ11 (ct168 v a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) hv))))).tail (Step.cQ12 (ct45 v) (Step.cQ8 (ct21 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) hv)))))).tail (rs .r42 v a1 a2))⟩
theorem vP93 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct78 a0) (ct170 a0 v) := by
 exact ⟨(ct78 v), ((rr.tail (Step.cQ7 (ct45 a0) (Step.cQ10 (zz3 ) hv))).tail (Step.cQ8 (ct17 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) hv))))), (((rr.tail (Step.cQ11 (ct168 a0 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) hv))))).tail (Step.cQ12 (ct45 v) (Step.cQ7 (ct45 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (rs .r42 v a1 a2))⟩
theorem vP94 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct79 a0) (ct171 v a0) := by
 exact ⟨(ct79 v), ((rr.tail (Step.cQ7 (ct58 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv)))))).tail (Step.cQ8 (ct62 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))), (((rr.tail (Step.cQ12 (ct58 v) (Step.cQ7 (ct58 a0) hv))).tail (Step.cQ12 (ct58 v) (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv)))))).tail (rs .r43 v a1 a2))⟩
theorem vP95 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct79 a0) (ct173 a0 v) := by
 exact ⟨(ct79 v), ((rr.tail (Step.cQ7 (ct58 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv)))))).tail (Step.cQ8 (ct62 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))), (((rr.tail (Step.cQ11 (ct172 v a0) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (Step.cQ12 (ct58 v) (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv)))))).tail (rs .r43 v a1 a2))⟩
theorem vP96 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct79 a0) (ct174 a0 v) := by
 exact ⟨(ct79 v), ((rr.tail (Step.cQ7 (ct58 a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv)))))).tail (Step.cQ8 (ct62 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))), (((rr.tail (Step.cQ11 (ct172 a0 v) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) hv))))).tail (Step.cQ12 (ct58 v) (Step.cQ7 (ct58 v) hv))).tail (rs .r43 v a1 a2))⟩
theorem vP97 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct80 a0) (ct175 v a0) := by
 exact ⟨(ct80 v), ((rr.tail (Step.cQ7 (ct48 a0) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ8 (ct27 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))))), (((rr.tail (Step.cQ12 (ct48 v) (Step.cQ7 (ct48 a0) hv))).tail (Step.cQ12 (ct48 v) (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv))))))).tail (rs .r44 v a1 a2))⟩
theorem vP98 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct80 a0) (ct177 a0 v) := by
 exact ⟨(ct80 v), ((rr.tail (Step.cQ7 (ct48 a0) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ8 (ct27 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))))), (((rr.tail (Step.cQ11 (ct176 v a0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))))).tail (Step.cQ12 (ct48 v) (Step.cQ8 v (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv))))))).tail (rs .r44 v a1 a2))⟩
theorem vP99 (a0 a1 a2 v : T) (hv : Step a0 v) :
  Join (ct80 a0) (ct178 a0 v) := by
 exact ⟨(ct80 v), ((rr.tail (Step.cQ7 (ct48 a0) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))).tail (Step.cQ8 (ct27 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))))), (((rr.tail (Step.cQ11 (ct176 a0 v) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) hv)))))).tail (Step.cQ12 (ct48 v) (Step.cQ7 (ct48 v) hv))).tail (rs .r44 v a1 a2))⟩
theorem peak_0 (a0 a1 a2 : T) {u : T} (h : Step (zz0 a0 a1) u) :
  Join (zz2 a0 a1) u := by
 rcases step_zz0_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 =>
   rcases T.zz0.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   subst a0
   exact ⟨(zz2 b0 b1), rr, rr⟩
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 => cases hE
  | r12 => cases hE
  | r13 => cases hE
  | r14 => cases hE
  | r15 => cases hE
  | r16 => cases hE
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 => cases hE
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 => cases hE
  | r37 => cases hE
  | r38 => cases hE
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  exact vP0 a0 a1 a2 u0 h0
 ·
  exact vP1 a0 a1 a2 u0 h0
theorem peak_1 (a0 a1 a2 : T) {u : T} (h : Step (ct0 a0 a1) u) :
  Join a0 u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz4.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   subst a0
   exact ⟨b0, rr, rr⟩
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   subst b0
   exact ⟨a0, rr, (rr.tail (rs .r6 a0 (lf 0) (lf 0)))⟩
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz4.inj he0 with ⟨he2, he3⟩
   clear he0
   have hsize := congrArg sz he3
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz4.inj he0 with ⟨he2, he3⟩
   clear he0
   have hsize := congrArg sz he3
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
 ·
  rcases step_zz4_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a1
    intro he0
    subst a0
    exact ⟨b0, rr, (rr.tail (rs .r5 b0 (lf 0) (lf 0)))⟩
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a1
    intro he0
    subst a0
    exact ⟨b0, rr, (rr.tail (rs .r17 b0 b0 (lf 0)))⟩
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP23 a0 a1 a2 u1 h1
  ·
   exact vP24 a0 a1 a2 u1 h1
 ·
  exact vP25 a0 a1 a2 u0 h0
theorem peak_2 (a0 a1 a2 : T) {u : T} (h : Step (ct1 a0) u) :
  Join (zz3 ) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨(zz3 ), rr, rr⟩
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨(zz3 ), rr, (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst b0
   intro he0 he6
   clear he6
   clear he0
   exact ⟨(zz3 ), rr, ((rr.tail (rs .r36 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
 ·
  exact vP52 a0 a1 a2 u0 h0
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    clear he0
    exact ⟨(zz3 ), rr, (rr.tail (rs .r5 (zz3 ) (lf 0) (lf 0)))⟩
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    clear he0
    exact ⟨(zz3 ), rr, (rr.tail (rs .r1 (zz3 ) b0 (lf 0)))⟩
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    clear he0
    exact ⟨(zz3 ), rr, (rr.tail (rs .r17 (zz3 ) b0 (lf 0)))⟩
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    have hsize := congrArg sz he4
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP53 a0 a1 a2 u1 h1
  ·
   exact vP54 a0 a1 a2 u1 h1
theorem peak_3 (a0 a1 a2 : T) {u : T} (h : Step (op a0 a1) u) :
  Join (ct2 a1 a0) u := by
 rcases step_op_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 =>
   rcases T.op.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   subst a0
   exact ⟨(ct2 b1 b0), rr, rr⟩
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 => cases hE
  | r12 => cases hE
  | r13 => cases hE
  | r14 => cases hE
  | r15 => cases hE
  | r16 => cases hE
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 => cases hE
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 => cases hE
  | r37 => cases hE
  | r38 => cases hE
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  exact vP82 a0 a1 a2 u0 h0
 ·
  exact vP83 a0 a1 a2 u0 h0
theorem peak_4 (a0 a1 a2 : T) {u : T} (h : Step (ct3 a0 a1) u) :
  Join a1 u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz5.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   revert he0 he2 he4
   subst a0
   intro he0 he2 he4
   revert he0 he2
   subst a1
   intro he0 he2
   clear he2
   clear he0
   exact ⟨b1, rr, rr⟩
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨a1, rr, ((rr.tail (Step.cQ7 (zz3 ) (rs .r15 (ct20 a1) (lf 0) (lf 0)))).tail (rs .r16 a1 (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
 ·
  exact vP100 a0 a1 a2 u0 h0
 ·
  rcases step_zz5_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b1
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r2 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨b0, rr, (rr.tail (rs .r5 b0 (lf 0) (lf 0)))⟩
   | r3 => cases hE
   | r4 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r5 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r6 => cases hE
   | r7 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨b1, rr, (rr.tail (rs .r9 b0 b1 (lf 0)))⟩
   | r8 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨(zz2 b1 b0), rr, (rr.tail (rs .r13 b0 b1 (lf 0)))⟩
   | r9 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨b0, rr, (rr.tail (rs .r1 b0 b1 (lf 0)))⟩
   | r10 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨(zz3 ), rr, (rr.tail (rs .r2 b0 (lf 0) (lf 0)))⟩
   | r11 => cases hE
   | r12 => cases hE
   | r13 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨(ct2 b0 b1), rr, rr⟩
   | r14 => cases hE
   | r15 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    subst a0
    exact ⟨a1, rr, (((rr.tail (rs .r8 (zz3 ) a1 (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct20 a1) (lf 0) (lf 0)))).tail (rs .r16 a1 (lf 0) (lf 0)))⟩
   | r16 => cases hE
   | r17 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b1
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r18 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r19 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r20 => cases hE
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    cases he0
   | r25 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨b0, rr, (rr.tail (rs .r17 b0 b1 (lf 0)))⟩
   | r26 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    subst b0
    exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (rr.tail (rs .r2 (zz3 ) (lf 0) (lf 0)))⟩
   | r27 => cases hE
   | r28 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    cases he0
   | r29 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r30 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨b0, rr, (rr.tail (rs .r24 b0 (lf 0) (lf 0)))⟩
   | r31 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨(ct20 b0), rr, (rr.tail (rs .r26 b0 (lf 0) (lf 0)))⟩
   | r32 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨(ct39 b0), rr, (rr.tail (rs .r31 b0 (lf 0) (lf 0)))⟩
   | r33 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    cases he0
   | r34 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r35 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    cases he0
   | r36 => cases hE
   | r37 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    subst b0
    exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((rr.tail (rs .r8 (zz3 ) (ct181 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0)))).tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r38 => cases hE
   | r39 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨b1, rr, (rr.tail (rs .r25 b0 b1 (lf 0)))⟩
   | r40 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨(ct30 b0), rr, (rr.tail (rs .r30 b0 (lf 0) (lf 0)))⟩
   | r41 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨(ct21 b0), rr, ((rr.tail (rs .r31 (ct41 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 b0 (lf 0) (lf 0)))))⟩
   | r42 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨(ct21 b0), rr, ((rr.tail (rs .r30 (ct17 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 b0 (lf 0) (lf 0)))))⟩
   | r43 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨b0, rr, (((rr.tail (rs .r31 (ct58 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r16 b0 (lf 0) (lf 0)))⟩
   | r44 =>
    rcases T.zz5.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a0
    intro he0 he2
    revert he0
    subst a1
    intro he0
    clear he0
    exact ⟨b0, rr, (((rr.tail (rs .r30 (ct27 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r16 b0 (lf 0) (lf 0)))⟩
  ·
   exact vP101 a0 a1 a2 u1 h1
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(zz3 ), rr, (((rr.tail (rs .r15 (ct190 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r5 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct17 b0), rr, ((rr.tail (Step.cQ12 (ct17 b0) (rs .r1 (zz3 ) b0 (lf 0)))).tail (rs .r5 (ct17 b0) (lf 0) (lf 0)))⟩
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct21 b0), rr, ((rr.tail (rs .r15 (ct19 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 b0 (lf 0) (lf 0))))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨b0, rr, ((rr.tail (Step.cQ12 (ct30 b0) (rs .r17 b0 b0 (lf 0)))).tail (rs .r17 b0 b0 (lf 0)))⟩
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct17 b0), rr, ((rr.tail (Step.cQ12 (ct21 b0) (rs .r18 b0 (lf 0) (lf 0)))).tail (rs .r18 b0 (lf 0) (lf 0)))⟩
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct27 b0), rr, ((rr.tail (Step.cQ12 b0 (rs .r19 b0 (lf 0) (lf 0)))).tail (rs .r19 b0 (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct42 b0), rr, ((rr.tail (Step.cQ12 (ct42 b0) (rs .r17 (zz3 ) b0 (lf 0)))).tail (rs .r5 (ct42 b0) (lf 0) (lf 0)))⟩
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct42 b0), rr, ((rr.tail (Step.cQ12 (ct21 b0) (rs .r35 b0 (lf 0) (lf 0)))).tail (rs .r35 b0 (lf 0) (lf 0)))⟩
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct62 b0), rr, ((rr.tail (Step.cQ12 b0 (rs .r37 b0 (lf 0) (lf 0)))).tail (rs .r37 b0 (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP102 a0 a1 a2 u2 h2
   ·
    exact vP103 a0 a1 a2 u2 h2
theorem peak_5 (a0 a1 a2 : T) {u : T} (h : Step (ct4 a0) u) :
  Join a0 u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   subst a0
   exact ⟨b0, (rr.tail (rs .r6 b0 (lf 0) (lf 0))), rr⟩
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   clear he1
   subst a0
   exact ⟨b0, rr, rr⟩
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), rr, (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   subst a0
   exact ⟨b0, (rr.tail (rs .r16 b0 (lf 0) (lf 0))), rr⟩
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
 ·
  exact vP104 a0 a1 a2 u0 h0
 ·
  rcases step_zz3_cases h0 with hr
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
theorem peak_6 (a0 a1 a2 : T) {u : T} (h : Step (ct5 a0) u) :
  Join a0 u := by
 rcases step_zz4_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 =>
   rcases T.zz4.inj hE with ⟨he0, he1⟩
   clear hE
   clear he1
   subst a0
   exact ⟨b0, rr, rr⟩
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 => cases hE
  | r12 => cases hE
  | r13 => cases hE
  | r14 => cases hE
  | r15 => cases hE
  | r16 => cases hE
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 =>
   rcases T.zz4.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), rr, (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 => cases hE
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 => cases hE
  | r37 => cases hE
  | r38 => cases hE
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  exact vP105 a0 a1 a2 u0 h0
 ·
  rcases step_zz3_cases h0 with hr
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
theorem peak_7 (a0 a1 a2 : T) {u : T} (h : Step (ct7 a0 a1) u) :
  Join (ct10 a0 a1) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz4.inj he0 with ⟨he2, he3⟩
   clear he0
   have hsize := congrArg sz he3
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz4.inj he3 with ⟨he4, he5⟩
   clear he3
   revert he0 he2 he4
   subst a1
   intro he0 he2 he4
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨(ct10 b0 b1), rr, rr⟩
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz4.inj he3 with ⟨he4, he5⟩
   clear he3
   revert he0 he2 he4
   subst a1
   intro he0 he2 he4
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b1
   intro he0
   clear he0
   exact ⟨b0, ((rr.tail (Step.cQ8 b0 (rs .r20 b0 (lf 0) (lf 0)))).tail (rs .r21 b0 (lf 0) (lf 0))), rr⟩
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   revert he0
   subst a1
   intro he0
   clear he0
   exact ⟨(zz2 a0 a0), (rr.tail (Step.cQ8 a0 (rs .r6 a0 (lf 0) (lf 0)))), ((rr.tail (Step.cQ7 (ct5 a0) (rs .r6 a0 (lf 0) (lf 0)))).tail (Step.cQ8 a0 (rs .r6 a0 (lf 0) (lf 0))))⟩
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
 ·
  rcases step_zz4_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a1
    intro he0
    subst a0
    exact ⟨(zz2 b0 b0), (rr.tail (Step.cQ8 b0 (rs .r6 b0 (lf 0) (lf 0)))), ((rr.tail (Step.cQ12 b0 (Step.cQ8 (zz3 ) (rs .r6 b0 (lf 0) (lf 0))))).tail (rs .r10 b0 (lf 0) (lf 0)))⟩
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a1
    intro he0
    subst a0
    exact ⟨b0, ((rr.tail (Step.cQ8 b0 (rs .r20 b0 (lf 0) (lf 0)))).tail (rs .r21 b0 (lf 0) (lf 0))), ((rr.tail (Step.cQ12 (ct30 b0) (Step.cQ8 b0 (rs .r20 b0 (lf 0) (lf 0))))).tail (rs .r25 b0 b0 (lf 0)))⟩
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP106 a0 a1 a2 u1 h1
  ·
   exact vP107 a0 a1 a2 u1 h1
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz4.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a1
    intro he0 he2
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP108 a0 a1 a2 u1 h1
  ·
   rcases step_zz4_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 =>
     rcases T.zz4.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a1
     intro he0
     subst a0
     exact ⟨(zz2 b0 b0), (rr.tail (Step.cQ8 b0 (rs .r6 b0 (lf 0) (lf 0)))), ((rr.tail (Step.cQ11 (ct12 b0) (rs .r6 b0 (lf 0) (lf 0)))).tail (rs .r10 b0 (lf 0) (lf 0)))⟩
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 =>
     rcases T.zz4.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a1
     intro he0
     subst a0
     exact ⟨b0, ((rr.tail (Step.cQ8 b0 (rs .r20 b0 (lf 0) (lf 0)))).tail (rs .r21 b0 (lf 0) (lf 0))), ((rr.tail (Step.cQ11 (ct31 b0) (rs .r20 b0 (lf 0) (lf 0)))).tail (rs .r25 b0 b0 (lf 0)))⟩
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP109 a0 a1 a2 u2 h2
   ·
    exact vP110 a0 a1 a2 u2 h2
theorem peak_8 (a0 a1 a2 : T) {u : T} (h : Step (ct9 a0 a1) u) :
  Join (ct15 a0 a1) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a1
   intro he0
   clear he0
   exact ⟨(ct15 b0 b1), rr, rr⟩
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨a1, ((rr.tail (Step.cQ7 (zz3 ) (rs .r15 (ct20 a1) (lf 0) (lf 0)))).tail (rs .r16 a1 (lf 0) (lf 0))), (rr.tail (rs .r16 a1 (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a1
   intro he0
   cases he0
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a1
   intro he0
   subst b0
   exact ⟨(zz3 ), (((((rr.tail (Step.cQ7 (zz3 ) (rs .r15 (ct198 ) (lf 0) (lf 0)))).tail (rs .r16 (ct180 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a1
   intro he0
   cases he0
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he0 he4
   subst b0
   intro he0 he4
   revert he0
   subst a1
   intro he0
   clear he0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he0 he4
   subst b0
   intro he0 he4
   revert he0
   subst a1
   intro he0
   clear he0
   exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct180 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct198 ) (lf 0) (lf 0))))).tail (rs .r16 (ct198 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a1
   intro he0
   cases he0
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a1
   intro he0
   cases he0
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a1
   intro he0
   subst b0
   exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0)))).tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
 ·
  exact vP111 a0 a1 a2 u0 h0
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a1
    exact ⟨(ct20 b0), (((rr.tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) b0 (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r16 (ct20 b0) (lf 0) (lf 0))), (rr.tail (rs .r15 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_a1 := sz_pos a1
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    cases he3
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    cases he3
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    revert he2
    subst b0
    intro he2
    subst a1
    exact ⟨(zz3 ), ((((((rr.tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct181 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0))))).tail (rs .r16 (ct182 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((rr.tail (rs .r8 (zz3 ) (ct181 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0)))).tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (rr.tail (rs .r2 (zz3 ) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct209 b0), (rr.tail (Step.cQ7 (ct17 b0) (rs .r2 (ct17 b0) (lf 0) (lf 0)))), (rr.tail (rs .r7 (zz3 ) b0 (lf 0)))⟩
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct21 b0), ((((rr.tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct20 b0) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) b0 (lf 0))))).tail (rs .r16 (ct179 b0) (lf 0) (lf 0))).tail (rs .r15 (ct20 b0) (lf 0) (lf 0))), (rr.tail (rs .r15 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨b0, ((rr.tail (Step.cQ7 (ct30 b0) (rs .r25 b0 b0 (lf 0)))).tail (rs .r21 b0 (lf 0) (lf 0))), (rr.tail (rs .r25 b0 b0 (lf 0)))⟩
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct17 b0), (((rr.tail (Step.cQ7 (ct21 b0) (Step.cQ12 (ct21 b0) (rs .r22 b0 (lf 0) (lf 0))))).tail (Step.cQ7 (ct21 b0) (rs .r18 b0 (lf 0) (lf 0)))).tail (rs .r22 b0 (lf 0) (lf 0))), ((rr.tail (Step.cQ12 (ct21 b0) (rs .r22 b0 (lf 0) (lf 0)))).tail (rs .r18 b0 (lf 0) (lf 0)))⟩
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct27 b0), (((rr.tail (Step.cQ7 b0 (Step.cQ12 b0 (rs .r23 b0 (lf 0) (lf 0))))).tail (Step.cQ7 b0 (rs .r19 b0 (lf 0) (lf 0)))).tail (rs .r23 b0 (lf 0) (lf 0))), ((rr.tail (Step.cQ12 b0 (rs .r23 b0 (lf 0) (lf 0)))).tail (rs .r19 b0 (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct216 b0), (rr.tail (Step.cQ7 (ct42 b0) (rs .r2 (ct42 b0) (lf 0) (lf 0)))), (rr.tail (rs .r39 (zz3 ) b0 (lf 0)))⟩
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct42 b0), (((rr.tail (Step.cQ7 (ct21 b0) (Step.cQ12 (ct21 b0) (rs .r36 b0 (lf 0) (lf 0))))).tail (Step.cQ7 (ct21 b0) (rs .r35 b0 (lf 0) (lf 0)))).tail (rs .r36 b0 (lf 0) (lf 0))), ((rr.tail (Step.cQ12 (ct21 b0) (rs .r36 b0 (lf 0) (lf 0)))).tail (rs .r35 b0 (lf 0) (lf 0)))⟩
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst a1
     exact ⟨(ct62 b0), (((rr.tail (Step.cQ7 b0 (Step.cQ12 b0 (rs .r38 b0 (lf 0) (lf 0))))).tail (Step.cQ7 b0 (rs .r37 b0 (lf 0) (lf 0)))).tail (rs .r38 b0 (lf 0) (lf 0))), ((rr.tail (Step.cQ12 b0 (rs .r38 b0 (lf 0) (lf 0)))).tail (rs .r37 b0 (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP112 a0 a1 a2 u2 h2
   ·
    exact vP113 a0 a1 a2 u2 h2
  ·
   exact vP114 a0 a1 a2 u1 h1
theorem peak_9 (a0 a1 a2 : T) {u : T} (h : Step (ct11 a0 a1) u) :
  Join a1 u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz4.inj he0 with ⟨he2, he3⟩
   clear he0
   have hsize := congrArg sz he3
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz4.inj he3 with ⟨he4, he5⟩
   clear he3
   revert he0 he2 he4
   subst a1
   intro he0 he2 he4
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨b1, rr, ((rr.tail (Step.cQ8 b1 (rs .r20 b1 (lf 0) (lf 0)))).tail (rs .r21 b1 (lf 0) (lf 0)))⟩
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz4.inj he3 with ⟨he4, he5⟩
   clear he3
   revert he0 he2 he4
   subst a1
   intro he0 he2 he4
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨b1, rr, rr⟩
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨a1, rr, (rr.tail (rs .r14 a1 (lf 0) (lf 0)))⟩
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
 ·
  rcases step_zz4_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a1
    intro he0
    subst a0
    exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ12 b0 (Step.cQ8 b0 (rs .r6 b0 (lf 0) (lf 0))))).tail (rs .r2 b0 (lf 0) (lf 0)))⟩
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a1
    intro he0
    subst a0
    exact ⟨b0, rr, ((rr.tail (Step.cQ12 (ct30 b0) (Step.cQ8 b0 (rs .r20 b0 (lf 0) (lf 0))))).tail (rs .r25 b0 b0 (lf 0)))⟩
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP115 a0 a1 a2 u1 h1
  ·
   exact vP116 a0 a1 a2 u1 h1
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz4.inj he1 with ⟨he2, he3⟩
    clear he1
    revert he0 he2
    subst a1
    intro he0 he2
    revert he0
    subst a0
    intro he0
    cases he0
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP117 a0 a1 a2 u1 h1
  ·
   rcases step_zz4_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 =>
     rcases T.zz4.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a1
     intro he0
     subst a0
     exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ11 (zz2 b0 b0) (rs .r6 b0 (lf 0) (lf 0)))).tail (rs .r2 b0 (lf 0) (lf 0)))⟩
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 =>
     rcases T.zz4.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a1
     intro he0
     subst a0
     exact ⟨b0, rr, ((rr.tail (Step.cQ11 (ct31 b0) (rs .r20 b0 (lf 0) (lf 0)))).tail (rs .r25 b0 b0 (lf 0)))⟩
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP118 a0 a1 a2 u2 h2
   ·
    exact vP119 a0 a1 a2 u2 h2
theorem peak_10 (a0 a1 a2 : T) {u : T} (h : Step (ct13 a0) u) :
  Join (zz2 a0 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨(zz3 ), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0))), rr⟩
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b1
   intro he0
   clear he0
   exact ⟨(zz2 b0 b0), ((rr.tail (Step.cQ7 (ct5 b0) (rs .r6 b0 (lf 0) (lf 0)))).tail (Step.cQ8 b0 (rs .r6 b0 (lf 0) (lf 0)))), (rr.tail (Step.cQ8 b0 (rs .r6 b0 (lf 0) (lf 0))))⟩
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨b1, (rr.tail (rs .r14 b1 (lf 0) (lf 0))), rr⟩
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨(zz2 b0 b0), rr, rr⟩
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨b1, (rr.tail (rs .r27 b1 (lf 0) (lf 0))), rr⟩
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨(zz3 ), (((((rr.tail (Step.cQ7 (ct221 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b1
   intro he0
   clear he0
   exact ⟨(zz2 b0 b0), ((rr.tail (Step.cQ7 (ct22 b0) (rs .r16 b0 (lf 0) (lf 0)))).tail (Step.cQ8 b0 (rs .r16 b0 (lf 0) (lf 0)))), (rr.tail (Step.cQ8 b0 (rs .r16 b0 (lf 0) (lf 0))))⟩
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct182 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((rr.tail (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct182 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨(zz3 ), (((((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
 ·
  exact vP2 a0 a1 a2 u0 h0
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    clear he0
    exact ⟨(zz3 ), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0))), (rr.tail (rs .r5 (zz3 ) (lf 0) (lf 0)))⟩
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    subst b0
    exact ⟨(zz3 ), (rr.tail (rs .r27 (zz3 ) (lf 0) (lf 0))), ((rr.tail (rs .r5 (ct222 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
  ·
   exact vP3 a0 a1 a2 u1 h1
theorem peak_11 (a0 a1 a2 : T) {u : T} (h : Step (ct14 ) u) :
  Join (zz3 ) u := by
 rcases step_zz2_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 =>
   clear hE
   exact ⟨(zz3 ), rr, rr⟩
  | r12 => cases hE
  | r13 => cases hE
  | r14 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r15 => cases hE
  | r16 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   clear he1
   cases he0
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r22 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r23 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r37 => cases hE
  | r38 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  rcases step_zz3_cases h0 with hr
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
 ·
  rcases step_zz3_cases h0 with hr
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
theorem peak_12 (a0 a1 a2 : T) {u : T} (h : Step (zz1 a0 a1 a2) u) :
  Join (ct24 a0 a1) u := by
 rcases step_zz1_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 => cases hE
  | r12 =>
   rcases T.zz1.inj hE with ⟨he0, he1, he2⟩
   clear hE
   revert he0 he1
   subst a2
   intro he0 he1
   revert he0
   subst a1
   intro he0
   subst a0
   exact ⟨(ct24 b0 b1), rr, rr⟩
  | r13 => cases hE
  | r14 => cases hE
  | r15 => cases hE
  | r16 => cases hE
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 => cases hE
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 => cases hE
  | r37 => cases hE
  | r38 => cases hE
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  exact vP4 a0 a1 a2 u0 h0
 ·
  exact vP5 a0 a1 a2 u0 h0
 ·
  exact vP6 a0 a1 a2 u0 h0
theorem peak_13 (a0 a1 a2 : T) {u : T} (h : Step (ct16 a0 a1) u) :
  Join (zz2 a1 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz5.inj he2 with ⟨he4, he5⟩
   clear he2
   rcases T.zz2.inj he5 with ⟨he6, he7⟩
   clear he5
   clear he7
   revert he0 he4
   subst a1
   intro he0 he4
   clear he4
   clear he0
   exact ⟨(zz2 b1 b0), rr, rr⟩
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(ct20 a1), rr, ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct20 a1) (lf 0) (lf 0))))).tail (rs .r16 (ct20 a1) (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a1 := sz_pos a1
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
 ·
  exact vP7 a0 a1 a2 u0 h0
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_a1 := sz_pos a1
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz5_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b1
     intro he0
     have hsize := congrArg sz he0
     have hp_a0 := sz_pos a0
     have hp_a1 := sz_pos a1
     have hp_b0 := sz_pos b0
     simp only [sz] at hsize
     omega
    | r2 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(zz2 b0 b0), rr, (rr.tail (rs .r10 b0 (lf 0) (lf 0)))⟩
    | r3 => cases hE
    | r4 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r5 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r6 => cases hE
    | r7 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct6 b1 b0), rr, ((rr.tail (rs .r8 (zz4 b0 b1) b0 (lf 0))).tail (Step.cQ7 (zz4 b0 b1) (rs .r9 b0 b1 (lf 0))))⟩
    | r8 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct8 b1 b0), rr, ((rr.tail (rs .r8 b0 (ct2 b0 b1) (lf 0))).tail (Step.cQ7 b0 (rs .r13 b0 b1 (lf 0))))⟩
    | r9 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct10 b0 b1), rr, (rr.tail (rs .r7 b0 b1 (lf 0)))⟩
    | r10 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct12 b0), rr, ((rr.tail (rs .r8 b0 b0 (lf 0))).tail (Step.cQ7 b0 (rs .r2 b0 (lf 0) (lf 0))))⟩
    | r11 => cases hE
    | r12 => cases hE
    | r13 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct15 b0 b1), rr, (rr.tail (rs .r8 b0 b1 (lf 0)))⟩
    | r14 => cases hE
    | r15 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(ct20 a1), rr, ((((rr.tail (rs .r8 (zz3 ) (ct20 a1) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) a1 (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct20 a1) (lf 0) (lf 0))))).tail (rs .r16 (ct20 a1) (lf 0) (lf 0)))⟩
    | r16 => cases hE
    | r17 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b1
     intro he0
     have hsize := congrArg sz he0
     have hp_a0 := sz_pos a0
     have hp_a1 := sz_pos a1
     have hp_b0 := sz_pos b0
     simp only [sz] at hsize
     omega
    | r18 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r19 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     cases he0
    | r25 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct35 b0 b1), rr, (rr.tail (rs .r39 b0 b1 (lf 0)))⟩
    | r26 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     subst b0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((rr.tail (rs .r8 (zz3 ) (zz3 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r27 => cases hE
    | r28 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     cases he0
    | r29 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     have hsize := congrArg sz he0
     have hp_a0 := sz_pos a0
     have hp_a1 := sz_pos a1
     simp only [sz] at hsize
     omega
    | r30 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct50 b0), rr, (rr.tail (rs .r40 b0 (lf 0) (lf 0)))⟩
    | r31 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct52 b0), rr, (rr.tail (rs .r32 b0 (lf 0) (lf 0)))⟩
    | r32 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct54 b0), rr, ((rr.tail (rs .r8 b0 (ct20 b0) (lf 0))).tail (Step.cQ7 b0 (rs .r31 b0 (lf 0) (lf 0))))⟩
    | r33 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     cases he0
    | r34 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     have hsize := congrArg sz he0
     have hp_a0 := sz_pos a0
     have hp_a1 := sz_pos a1
     simp only [sz] at hsize
     omega
    | r35 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     cases he0
    | r36 => cases hE
    | r37 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     subst b0
     exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((((rr.tail (rs .r8 (zz3 ) (ct182 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct181 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0))))).tail (rs .r16 (ct182 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r38 => cases hE
    | r39 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct65 b1 b0), rr, ((rr.tail (rs .r8 (ct24 b0 b1) b0 (lf 0))).tail (Step.cQ7 (ct24 b0 b1) (rs .r25 b0 b1 (lf 0))))⟩
    | r40 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct67 b0), rr, ((rr.tail (rs .r8 (ct21 b0) b0 (lf 0))).tail (Step.cQ7 (ct21 b0) (rs .r30 b0 (lf 0) (lf 0))))⟩
    | r41 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct69 b0), rr, (((rr.tail (rs .r8 (ct41 b0) (ct42 b0) (lf 0))).tail (Step.cQ7 (ct41 b0) (rs .r31 (ct41 b0) (lf 0) (lf 0)))).tail (Step.cQ7 (ct41 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 b0 (lf 0) (lf 0))))))⟩
    | r42 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct71 b0), rr, (((rr.tail (rs .r8 (ct45 b0) (ct17 b0) (lf 0))).tail (Step.cQ7 (ct45 b0) (rs .r30 (ct17 b0) (lf 0) (lf 0)))).tail (Step.cQ7 (ct45 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 b0 (lf 0) (lf 0))))))⟩
    | r43 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct73 b0), rr, ((((rr.tail (rs .r8 (ct58 b0) (ct62 b0) (lf 0))).tail (Step.cQ7 (ct58 b0) (rs .r31 (ct58 b0) (lf 0) (lf 0)))).tail (Step.cQ7 (ct58 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (ct20 b0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct58 b0) (rs .r16 b0 (lf 0) (lf 0))))⟩
    | r44 =>
     rcases T.zz5.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     revert he0 he2
     subst a0
     intro he0 he2
     revert he0
     subst a1
     intro he0
     clear he0
     exact ⟨(ct75 b0), rr, ((((rr.tail (rs .r8 (ct48 b0) (ct27 b0) (lf 0))).tail (Step.cQ7 (ct48 b0) (rs .r30 (ct27 b0) (lf 0) (lf 0)))).tail (Step.cQ7 (ct48 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 (ct20 b0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct48 b0) (rs .r16 b0 (lf 0) (lf 0))))⟩
   ·
    exact vP8 a0 a1 a2 u2 h2
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst a1
      exact ⟨(zz3 ), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((rr.tail (rs .r15 (ct233 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r5 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst a1
      exact ⟨b0, (rr.tail (rs .r14 b0 (lf 0) (lf 0))), ((rr.tail (Step.cQ12 (ct17 b0) (Step.cQ7 (ct17 b0) (rs .r1 (zz3 ) b0 (lf 0))))).tail (rs .r9 (zz3 ) b0 (lf 0)))⟩
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst a1
      exact ⟨b0, (rr.tail (rs .r16 b0 (lf 0) (lf 0))), (((rr.tail (rs .r15 (ct235 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 b0 (lf 0) (lf 0))))).tail (rs .r16 b0 (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst a1
      exact ⟨b0, (rr.tail (rs .r21 b0 (lf 0) (lf 0))), ((rr.tail (Step.cQ12 (ct30 b0) (Step.cQ7 (ct30 b0) (rs .r17 b0 b0 (lf 0))))).tail (rs .r25 b0 b0 (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst a1
      exact ⟨(ct17 b0), (rr.tail (rs .r22 b0 (lf 0) (lf 0))), (((rr.tail (Step.cQ12 (ct21 b0) (Step.cQ7 (ct21 b0) (rs .r18 b0 (lf 0) (lf 0))))).tail (Step.cQ12 (ct21 b0) (rs .r22 b0 (lf 0) (lf 0)))).tail (rs .r18 b0 (lf 0) (lf 0)))⟩
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst a1
      exact ⟨(ct27 b0), (rr.tail (rs .r23 b0 (lf 0) (lf 0))), (((rr.tail (Step.cQ12 b0 (Step.cQ7 b0 (rs .r19 b0 (lf 0) (lf 0))))).tail (Step.cQ12 b0 (rs .r23 b0 (lf 0) (lf 0)))).tail (rs .r19 b0 (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst a1
      exact ⟨b0, (rr.tail (rs .r27 b0 (lf 0) (lf 0))), (((rr.tail (Step.cQ12 (ct42 b0) (Step.cQ7 (ct42 b0) (rs .r17 (zz3 ) b0 (lf 0))))).tail (rs .r10 (ct42 b0) (lf 0) (lf 0))).tail (rs .r27 b0 (lf 0) (lf 0)))⟩
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst a1
      exact ⟨(ct42 b0), (rr.tail (rs .r36 b0 (lf 0) (lf 0))), (((rr.tail (Step.cQ12 (ct21 b0) (Step.cQ7 (ct21 b0) (rs .r35 b0 (lf 0) (lf 0))))).tail (Step.cQ12 (ct21 b0) (rs .r36 b0 (lf 0) (lf 0)))).tail (rs .r35 b0 (lf 0) (lf 0)))⟩
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst a1
      exact ⟨(ct62 b0), (rr.tail (rs .r38 b0 (lf 0) (lf 0))), (((rr.tail (Step.cQ12 b0 (Step.cQ7 b0 (rs .r37 b0 (lf 0) (lf 0))))).tail (Step.cQ12 b0 (rs .r38 b0 (lf 0) (lf 0)))).tail (rs .r37 b0 (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP9 a0 a1 a2 u3 h3
    ·
     exact vP10 a0 a1 a2 u3 h3
  ·
   exact vP11 a0 a1 a2 u1 h1
theorem peak_14 (a0 a1 a2 : T) {u : T} (h : Step (ct18 a0) u) :
  Join a0 u := by
 rcases step_zz2_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r12 => cases hE
  | r13 => cases hE
  | r14 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz4.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨b0, rr, rr⟩
  | r15 => cases hE
  | r16 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r22 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r23 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz4.inj he0 with ⟨he2, he3⟩
   clear he0
   have hsize := congrArg sz he3
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r37 => cases hE
  | r38 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  rcases step_zz4_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    subst b0
    exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    subst b0
    exact ⟨(zz3 ), rr, (((rr.tail (Step.cQ7 (ct224 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
  ·
   exact vP12 a0 a1 a2 u1 h1
 ·
  rcases step_zz4_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    subst b0
    exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    subst b0
    exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ7 (ct222 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r21 (zz3 ) (lf 0) (lf 0)))⟩
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
  ·
   exact vP13 a0 a1 a2 u1 h1
theorem peak_15 (a0 a1 a2 : T) {u : T} (h : Step (ct19 a0) u) :
  Join (ct20 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), rr⟩
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨b1, ((rr.tail (Step.cQ7 (zz3 ) (rs .r15 (ct20 b1) (lf 0) (lf 0)))).tail (rs .r16 b1 (lf 0) (lf 0))), rr⟩
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0))), rr⟩
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨b1, (rr.tail (rs .r16 b1 (lf 0) (lf 0))), ((rr.tail (Step.cQ7 (zz3 ) (rs .r15 (ct20 b1) (lf 0) (lf 0)))).tail (rs .r16 b1 (lf 0) (lf 0)))⟩
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(ct20 b1), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct20 b1) (lf 0) (lf 0))))).tail (rs .r16 (ct20 b1) (lf 0) (lf 0))), rr⟩
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(ct20 b0), rr, rr⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), (((rr.tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), ((((rr.tail (rs .r16 (ct180 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), (((((rr.tail (rs .r16 (ct198 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), (((rr.tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
 ·
  rcases step_zz3_cases h0 with hr
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
 ·
  exact vP14 a0 a1 a2 u0 h0
theorem peak_16 (a0 a1 a2 : T) {u : T} (h : Step (ct22 a0) u) :
  Join a0 u := by
 rcases step_zz2_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   clear he1
   cases he0
  | r12 => cases hE
  | r13 => cases hE
  | r14 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r15 => cases hE
  | r16 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   clear he1
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   subst a0
   exact ⟨b0, rr, rr⟩
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r22 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r23 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r37 => cases hE
  | r38 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   subst a0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(ct20 b0), rr, rr⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((rr.tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct21 b0), rr, rr⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (rs .r16 (ct182 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP15 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz3_cases h0 with hr
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
theorem peak_17 (a0 a1 a2 : T) {u : T} (h : Step (ct25 a0 a1) u) :
  Join a0 u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   subst b0
   exact ⟨a0, rr, (rr.tail (rs .r16 a0 (lf 0) (lf 0)))⟩
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   subst a0
   exact ⟨b0, rr, rr⟩
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he4
   subst b0
   intro he4
   cases he4
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he4
   subst b0
   intro he4
   cases he4
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a1
    intro he4
    subst a0
    exact ⟨b0, rr, (rr.tail (rs .r5 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a1
    intro he4
    subst a0
    exact ⟨(zz3 ), ((rr.tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((rr.tail (rs .r5 (ct206 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a1
     intro he2
     subst a0
     exact ⟨(ct20 b0), rr, (rr.tail (rs .r5 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a1
     intro he2
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((rr.tail (rs .r5 (ct242 ) (lf 0) (lf 0))).tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(zz3 ), rr, (((rr.tail (rs .r5 (ct221 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct17 b0), rr, (rr.tail (rs .r18 b0 (lf 0) (lf 0)))⟩
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct21 b0), rr, (rr.tail (rs .r5 (ct21 b0) (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨b0, rr, (rr.tail (rs .r24 b0 (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct17 b0), rr, (rr.tail (rs .r28 b0 (lf 0) (lf 0)))⟩
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct27 b0), rr, (rr.tail (rs .r29 b0 (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct42 b0), rr, (rr.tail (rs .r35 b0 (lf 0) (lf 0)))⟩
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct42 b0), rr, ((rr.tail (Step.cQ11 (ct21 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0)))).tail (rs .r33 b0 (lf 0) (lf 0)))⟩
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct62 b0), rr, ((rr.tail (Step.cQ11 b0 (rs .r16 (ct58 b0) (lf 0) (lf 0)))).tail (rs .r34 b0 (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP16 a0 a1 a2 u3 h3
    ·
     exact vP17 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  exact vP18 a0 a1 a2 u0 h0
theorem peak_18 (a0 a1 a2 : T) {u : T} (h : Step (ct26 a0) u) :
  Join (ct17 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz4.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨(ct17 b0), rr, rr⟩
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz4.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(ct27 b0), rr, (rr.tail (rs .r19 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(zz3 ), ((((rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct247 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct247 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct247 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), (rr.tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (Step.cQ11 (ct224 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct224 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct249 b0), rr, (rr.tail (rs .r19 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct250 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct250 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct250 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct250 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct252 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct252 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct252 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct252 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP19 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz4_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    subst b0
    exact ⟨(zz3 ), (rr.tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((rr.tail (rs .r5 (ct221 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    subst b0
    exact ⟨(zz3 ), (rr.tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (rr.tail (rs .r24 (zz3 ) (lf 0) (lf 0)))⟩
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
  ·
   exact vP20 a0 a1 a2 u1 h1
theorem peak_19 (a0 a1 a2 : T) {u : T} (h : Step (ct28 a0) u) :
  Join (ct27 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((rr.tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz4.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   clear he2
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz4.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨(ct27 b0), rr, rr⟩
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
 ·
  exact vP21 a0 a1 a2 u0 h0
 ·
  rcases step_zz4_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((rr.tail (rs .r15 (ct224 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct17 b0), (rr.tail (Step.cQ10 (zz3 ) (rs .r16 b0 (lf 0) (lf 0)))), (rr.tail (rs .r18 b0 (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((((rr.tail (Step.cQ10 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ11 (ct250 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct250 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct250 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((((rr.tail (Step.cQ10 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ10 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ11 (ct252 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct252 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct252 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP22 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
theorem peak_20 (a0 a1 a2 : T) {u : T} (h : Step (zz4 a0 a0) u) :
  Join (ct30 a0) u := by
 rcases step_zz4_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 =>
   rcases T.zz4.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), rr⟩
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 => cases hE
  | r12 => cases hE
  | r13 => cases hE
  | r14 => cases hE
  | r15 => cases hE
  | r16 => cases hE
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 =>
   rcases T.zz4.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(ct30 b0), rr, rr⟩
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 => cases hE
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 => cases hE
  | r37 => cases hE
  | r38 => cases hE
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  exact vP26 a0 a1 a2 u0 h0
 ·
  exact vP27 a0 a1 a2 u0 h0
theorem peak_21 (a0 a1 a2 : T) {u : T} (h : Step (ct31 a0) u) :
  Join a0 u := by
 rcases step_zz2_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r12 => cases hE
  | r13 => cases hE
  | r14 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r15 => cases hE
  | r16 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   clear he6
   clear he0
   exact ⟨b0, rr, rr⟩
  | r22 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r23 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   revert he0
   subst b0
   intro he0
   cases he0
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r37 => cases hE
  | r38 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  exact vP28 a0 a1 a2 u0 h0
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    subst b0
    exact ⟨(zz3 ), rr, (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    cases he4
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(zz3 ), rr, (((rr.tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(ct17 b0), rr, (rr.tail (rs .r22 b0 (lf 0) (lf 0)))⟩
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      have hsize := congrArg sz he0
      have hp_b0 := sz_pos b0
      simp only [sz] at hsize
      omega
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      have hsize := congrArg sz he0
      have hp_b0 := sz_pos b0
      simp only [sz] at hsize
      omega
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(ct42 b0), rr, (rr.tail (rs .r36 b0 (lf 0) (lf 0)))⟩
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      clear he3
      rcases T.zz2.inj he2 with ⟨he4, he5⟩
      clear he2
      clear he5
      have hsize := congrArg sz he4
      have hp_b0 := sz_pos b0
      simp only [sz] at hsize
      omega
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      have hsize := congrArg sz he0
      have hp_b0 := sz_pos b0
      simp only [sz] at hsize
      omega
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP29 a0 a1 a2 u3 h3
    ·
     exact vP30 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
theorem peak_22 (a0 a1 a2 : T) {u : T} (h : Step (ct32 a0) u) :
  Join (ct17 a0) u := by
 rcases step_zz2_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r12 => cases hE
  | r13 => cases hE
  | r14 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r15 => cases hE
  | r16 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r22 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(ct17 b0), rr, rr⟩
  | r23 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz4.inj he0 with ⟨he2, he3⟩
   clear he0
   have hsize := congrArg sz he3
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   cases he0
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   cases he0
  | r37 => cases hE
  | r38 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  rcases step_zz4_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    subst b0
    exact ⟨(zz3 ), (rr.tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((rr.tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    subst b0
    exact ⟨(zz3 ), (rr.tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((rr.tail (rs .r36 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
  ·
   exact vP31 a0 a1 a2 u1 h1
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(ct27 b0), rr, (rr.tail (rs .r23 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(zz3 ), ((((rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((rr.tail (Step.cQ7 (ct206 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct206 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct206 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct206 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (rs .r21 (zz3 ) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), (rr.tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((rr.tail (Step.cQ7 (ct14 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct249 b0), rr, (rr.tail (rs .r23 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ7 (ct195 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct195 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct195 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ7 (ct242 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct242 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct242 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP32 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
theorem peak_23 (a0 a1 a2 : T) {u : T} (h : Step (ct33 a0) u) :
  Join (ct27 a0) u := by
 rcases step_zz2_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r12 => cases hE
  | r13 => cases hE
  | r14 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz4.inj he0 with ⟨he2, he3⟩
   clear he0
   have hsize := congrArg sz he3
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r15 => cases hE
  | r16 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r22 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz4.inj he0 with ⟨he2, he3⟩
   clear he0
   have hsize := congrArg sz he3
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r23 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(ct27 b0), rr, rr⟩
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r37 => cases hE
  | r38 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  rcases step_zz4_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 => cases hE
   | r12 => cases hE
   | r13 => cases hE
   | r14 => cases hE
   | r15 => cases hE
   | r16 => cases hE
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 =>
    rcases T.zz4.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r21 => cases hE
   | r22 => cases hE
   | r23 => cases hE
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 => cases hE
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 => cases hE
   | r37 => cases hE
   | r38 => cases hE
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((rr.tail (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct17 b0), (rr.tail (Step.cQ10 (zz3 ) (rs .r16 b0 (lf 0) (lf 0)))), (rr.tail (rs .r22 b0 (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((((rr.tail (Step.cQ10 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((rr.tail (Step.cQ7 (ct194 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct194 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct194 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((((rr.tail (Step.cQ10 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ10 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((((rr.tail (Step.cQ7 (ct206 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct206 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct206 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (rs .r21 (zz3 ) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP33 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
 ·
  exact vP34 a0 a1 a2 u0 h0
theorem peak_24 (a0 a1 a2 : T) {u : T} (h : Step (ct34 a0) u) :
  Join a0 u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b1
   intro he0
   cases he0
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   clear he6
   clear he0
   exact ⟨b0, rr, rr⟩
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   clear he6
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   clear he9
   have hsize := congrArg sz he8
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   cases he6
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   cases he9
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨(zz3 ), rr, (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   cases he6
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(ct20 b0), rr, (rr.tail (rs .r26 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct256 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct256 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct254 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct255 ) (lf 0) (lf 0)))).tail (rs .r16 (ct254 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct182 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), rr, ((((((rr.tail (Step.cQ11 (ct222 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct14 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (zz3 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct21 b0), rr, (rr.tail (rs .r26 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct262 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct262 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct262 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct260 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct261 ) (lf 0) (lf 0)))).tail (rs .r16 (ct260 ) (lf 0) (lf 0))).tail (rs .r14 (ct14 ) (lf 0) (lf 0))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct266 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct266 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct266 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct264 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct265 ) (lf 0) (lf 0)))).tail (rs .r16 (ct264 ) (lf 0) (lf 0))).tail (rs .r27 (ct14 ) (lf 0) (lf 0))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP35 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    subst b0
    exact ⟨(zz3 ), rr, (((rr.tail (rs .r5 (ct221 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    cases he4
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(zz3 ), rr, ((rr.tail (rs .r33 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(ct17 b0), rr, (rr.tail (rs .r28 b0 (lf 0) (lf 0)))⟩
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      have hsize := congrArg sz he0
      have hp_b0 := sz_pos b0
      simp only [sz] at hsize
      omega
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      have hsize := congrArg sz he0
      have hp_b0 := sz_pos b0
      simp only [sz] at hsize
      omega
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(ct42 b0), rr, ((rr.tail (Step.cQ11 (ct21 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0)))).tail (rs .r33 b0 (lf 0) (lf 0)))⟩
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      clear he3
      rcases T.zz2.inj he2 with ⟨he4, he5⟩
      clear he2
      clear he5
      have hsize := congrArg sz he4
      have hp_b0 := sz_pos b0
      simp only [sz] at hsize
      omega
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      have hsize := congrArg sz he0
      have hp_b0 := sz_pos b0
      simp only [sz] at hsize
      omega
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP36 a0 a1 a2 u3 h3
    ·
     exact vP37 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
theorem peak_25 (a0 a1 a2 : T) {u : T} (h : Step (ct36 a0 a1) u) :
  Join a1 u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨a1, rr, (rr.tail (rs .r27 a1 (lf 0) (lf 0)))⟩
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he0 he2 he8
   subst a1
   intro he0 he2 he8
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨b1, rr, rr⟩
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he0 he2 he8
   subst a1
   intro he0 he2 he8
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨b1, rr, (rr.tail (rs .r21 b1 (lf 0) (lf 0)))⟩
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst b0
   intro he0 he2 he6
   cases he6
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   cases he6
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   cases he6
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a1
    intro he4
    subst a0
    exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ12 b0 (Step.cQ8 b0 (rs .r16 b0 (lf 0) (lf 0))))).tail (rs .r2 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a1
    intro he4
    subst a0
    exact ⟨(zz3 ), rr, ((((((((((rr.tail (Step.cQ11 (ct269 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct269 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct269 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a1
     intro he2
     subst a0
     exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ12 (ct20 b0) (Step.cQ8 (ct20 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r2 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a1
     intro he2
     subst a0
     exact ⟨(zz3 ), rr, (((((((((((((rr.tail (Step.cQ11 (ct276 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct276 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct276 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct276 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct275 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct275 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct275 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct182 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(zz3 ), rr, (((((rr.tail (Step.cQ11 (ct282 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct282 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct282 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct17 b0), rr, ((rr.tail (Step.cQ12 (ct21 b0) (rs .r21 (ct17 b0) (lf 0) (lf 0)))).tail (rs .r18 b0 (lf 0) (lf 0)))⟩
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ12 (ct21 b0) (Step.cQ8 (ct21 b0) (rs .r16 (ct21 b0) (lf 0) (lf 0))))).tail (rs .r2 (ct21 b0) (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct30 b0), rr, ((rr.tail (Step.cQ12 (ct21 b0) (Step.cQ8 b0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 b0 (lf 0) (lf 0))))))).tail (rs .r30 b0 (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct21 b0), rr, (((rr.tail (Step.cQ12 (ct45 b0) (Step.cQ8 (ct17 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r22 b0 (lf 0) (lf 0))))))).tail (rs .r30 (ct17 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 b0 (lf 0) (lf 0)))))⟩
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨b0, rr, ((((rr.tail (Step.cQ12 (ct48 b0) (Step.cQ8 (ct27 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 b0 (lf 0) (lf 0))))))).tail (rs .r30 (ct27 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r16 b0 (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct42 b0), rr, ((rr.tail (Step.cQ12 (ct21 b0) (rs .r21 (ct42 b0) (lf 0) (lf 0)))).tail (rs .r35 b0 (lf 0) (lf 0)))⟩
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct21 b0), rr, (((((rr.tail (Step.cQ11 (ct298 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0)))).tail (Step.cQ12 (ct41 b0) (Step.cQ8 (ct42 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r36 b0 (lf 0) (lf 0))))))).tail (Step.cQ12 (ct41 b0) (Step.cQ8 (ct42 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0))))).tail (rs .r31 (ct41 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 b0 (lf 0) (lf 0)))))⟩
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨b0, rr, ((((((rr.tail (Step.cQ11 (ct302 b0) (rs .r16 (ct58 b0) (lf 0) (lf 0)))).tail (Step.cQ12 (ct58 b0) (Step.cQ8 (ct62 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r38 b0 (lf 0) (lf 0))))))).tail (Step.cQ12 (ct58 b0) (Step.cQ8 (ct62 b0) (rs .r16 (ct58 b0) (lf 0) (lf 0))))).tail (rs .r31 (ct58 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r16 b0 (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP38 a0 a1 a2 u3 h3
    ·
     exact vP39 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    rcases T.zz2.inj he4 with ⟨he6, he7⟩
    clear he4
    revert he0 he6
    subst a1
    intro he0 he6
    revert he0
    subst a0
    intro he0
    clear he0
    exact ⟨b0, rr, (rr.tail (rs .r17 b0 b0 (lf 0)))⟩
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    rcases T.zz2.inj he4 with ⟨he6, he7⟩
    clear he4
    revert he0 he6
    subst a1
    intro he0 he6
    revert he0
    subst a0
    intro he0
    cases he0
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP40 a0 a1 a2 u1 h1
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     rcases T.zz2.inj he2 with ⟨he4, he5⟩
     clear he2
     revert he4
     subst a1
     intro he4
     subst a0
     exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ11 (zz2 b0 b0) (rs .r16 b0 (lf 0) (lf 0)))).tail (rs .r2 b0 (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     rcases T.zz2.inj he2 with ⟨he4, he5⟩
     clear he2
     revert he4
     subst a1
     intro he4
     subst a0
     exact ⟨(zz3 ), rr, (((((((((rr.tail (Step.cQ11 (ct304 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct304 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct304 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct304 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      cases he0
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      revert he2
      subst a1
      intro he2
      subst a0
      exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ11 (ct37 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0)))).tail (rs .r2 (ct20 b0) (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      revert he2
      subst a1
      intro he2
      subst a0
      exact ⟨(zz3 ), rr, (((((((((((((rr.tail (Step.cQ11 (ct307 ) (rs .r16 (ct182 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct307 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct307 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct307 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct307 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(zz3 ), rr, ((((((rr.tail (Step.cQ11 (ct281 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct281 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct17 b0), rr, (((rr.tail (Step.cQ11 (ct32 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 b0 (lf 0) (lf 0)))))).tail (Step.cQ12 (ct21 b0) (rs .r22 b0 (lf 0) (lf 0)))).tail (rs .r18 b0 (lf 0) (lf 0)))⟩
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(zz3 ), rr, ((rr.tail (Step.cQ11 (ct309 b0) (rs .r16 (ct21 b0) (lf 0) (lf 0)))).tail (rs .r2 (ct21 b0) (lf 0) (lf 0)))⟩
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct30 b0), rr, ((rr.tail (Step.cQ11 (ct50 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 b0 (lf 0) (lf 0)))))).tail (rs .r30 b0 (lf 0) (lf 0)))⟩
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct21 b0), rr, (((rr.tail (Step.cQ11 (ct78 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r22 b0 (lf 0) (lf 0)))))).tail (rs .r30 (ct17 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 b0 (lf 0) (lf 0)))))⟩
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨b0, rr, ((((rr.tail (Step.cQ11 (ct80 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 b0 (lf 0) (lf 0)))))).tail (rs .r30 (ct27 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r16 b0 (lf 0) (lf 0)))⟩
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct42 b0), rr, (((rr.tail (Step.cQ11 (ct61 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 b0 (lf 0) (lf 0)))))).tail (Step.cQ12 (ct21 b0) (rs .r36 b0 (lf 0) (lf 0)))).tail (rs .r35 b0 (lf 0) (lf 0)))⟩
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct21 b0), rr, (((rr.tail (Step.cQ11 (ct299 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r36 b0 (lf 0) (lf 0)))))).tail (rs .r30 (ct42 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 b0 (lf 0) (lf 0)))))⟩
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨b0, rr, ((((rr.tail (Step.cQ11 (ct303 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r38 b0 (lf 0) (lf 0)))))).tail (rs .r30 (ct62 b0) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r16 b0 (lf 0) (lf 0)))⟩
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      exact vP41 a0 a1 a2 u4 h4
     ·
      exact vP42 a0 a1 a2 u4 h4
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
theorem peak_26 (a0 a1 a2 : T) {u : T} (h : Step (ct40 a0) u) :
  Join (ct20 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b1
   intro he0
   subst a0
   exact ⟨(zz3 ), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((rr.tail (Step.cQ7 (zz3 ) (rs .r15 (ct198 ) (lf 0) (lf 0)))).tail (rs .r16 (ct180 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((rr.tail (rs .r16 (ct180 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst b0
   intro he0 he6
   clear he6
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   rcases T.zz2.inj he7 with ⟨he8, he9⟩
   clear he7
   clear he9
   revert he0 he6
   subst a0
   intro he0 he6
   clear he6
   clear he0
   exact ⟨(ct20 b0), rr, rr⟩
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst b0
   intro he0 he6
   cases he6
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   rcases T.zz2.inj he7 with ⟨he8, he9⟩
   clear he7
   clear he9
   revert he0 he6
   subst a0
   intro he0 he6
   cases he6
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
 ·
  exact vP43 a0 a1 a2 u0 h0
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    cases he5
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    cases he5
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     cases he3
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     cases he3
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      have hsize := congrArg sz he0
      have hp_b0 := sz_pos b0
      simp only [sz] at hsize
      omega
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(ct42 b0), rr, (rr.tail (rs .r33 b0 (lf 0) (lf 0)))⟩
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      rcases T.zz2.inj he0 with ⟨he4, he5⟩
      clear he0
      clear he5
      rcases T.zz2.inj he4 with ⟨he6, he7⟩
      clear he4
      clear he7
      have hsize := congrArg sz he6
      have hp_b0 := sz_pos b0
      simp only [sz] at hsize
      omega
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      clear he3
      have hsize := congrArg sz he2
      have hp_a0 := sz_pos a0
      simp only [sz] at hsize
      omega
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(zz3 ), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((rr.tail (rs .r8 (zz3 ) (ct181 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0)))).tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨b0, (rr.tail (rs .r16 b0 (lf 0) (lf 0))), ((rr.tail (Step.cQ12 (ct21 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 b0 (rs .r16 b0 (lf 0) (lf 0))))))).tail (rs .r24 b0 (lf 0) (lf 0)))⟩
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), (((rr.tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((((((((((rr.tail (Step.cQ11 (ct314 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct314 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct312 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct313 ) (lf 0) (lf 0)))).tail (rs .r16 (ct312 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct195 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct195 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), (((rr.tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((((rr.tail (Step.cQ11 (ct318 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct318 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct316 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct317 ) (lf 0) (lf 0)))).tail (rs .r16 (ct316 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct242 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      exact vP44 a0 a1 a2 u4 h4
     ·
      rcases step_zz3_cases h4 with hr
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 => cases hE
       | r12 => cases hE
       | r13 => cases hE
       | r14 => cases hE
       | r15 => cases hE
       | r16 => cases hE
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 => cases hE
       | r22 => cases hE
       | r23 => cases hE
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 => cases hE
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 => cases hE
       | r37 => cases hE
       | r38 => cases hE
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(zz3 ), (rr.tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((rr.tail (rs .r8 (zz3 ) (ct221 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct14 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (zz3 ) (lf 0))))).tail (rs .r16 (ct200 ) (lf 0) (lf 0))).tail (rs .r2 (zz3 ) (lf 0) (lf 0)))⟩
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨b0, (rr.tail (rs .r16 b0 (lf 0) (lf 0))), ((rr.tail (Step.cQ12 (ct21 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 b0 (rs .r16 b0 (lf 0) (lf 0))))))).tail (rs .r24 b0 (lf 0) (lf 0)))⟩
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), (((rr.tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct327 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct327 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct325 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct326 ) (lf 0) (lf 0)))).tail (rs .r16 (ct325 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct194 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (rs .r14 (ct14 ) (lf 0) (lf 0))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), (((rr.tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct331 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct331 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct329 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct330 ) (lf 0) (lf 0)))).tail (rs .r16 (ct329 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct206 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ7 (ct206 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (rs .r21 (zz3 ) (lf 0) (lf 0)))⟩
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      exact vP45 a0 a1 a2 u4 h4
     ·
      rcases step_zz3_cases h4 with hr
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 => cases hE
       | r12 => cases hE
       | r13 => cases hE
       | r14 => cases hE
       | r15 => cases hE
       | r16 => cases hE
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 => cases hE
       | r22 => cases hE
       | r23 => cases hE
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 => cases hE
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 => cases hE
       | r37 => cases hE
       | r38 => cases hE
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
theorem peak_27 (a0 a1 a2 : T) {u : T} (h : Step (ct43 a0) u) :
  Join a0 u := by
 rcases step_zz2_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r12 => cases hE
  | r13 => cases hE
  | r14 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r15 => cases hE
  | r16 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   revert he0
   subst b0
   intro he0
   cases he0
  | r22 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   cases he0
  | r23 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   clear he6
   clear he0
   exact ⟨b0, rr, rr⟩
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   clear he9
   rcases T.zz2.inj he8 with ⟨he10, he11⟩
   clear he8
   have hsize := congrArg sz he11
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r37 => cases hE
  | r38 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    subst b0
    exact ⟨(zz3 ), rr, (rr.tail (rs .r21 (zz3 ) (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    cases he4
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(zz3 ), rr, (((rr.tail (Step.cQ7 (ct222 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct222 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r21 (zz3 ) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((rr.tail (Step.cQ7 (ct334 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct334 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     exact vP46 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    subst b0
    exact ⟨(zz3 ), rr, ((rr.tail (rs .r16 (ct14 ) (lf 0) (lf 0))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    cases he4
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(zz3 ), rr, ((rr.tail (rs .r36 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (rs .r38 (ct221 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     exact vP47 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
theorem peak_28 (a0 a1 a2 : T) {u : T} (h : Step (ct46 a0) u) :
  Join (ct17 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   cases he0
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   clear he9
   have hsize := congrArg sz he8
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(ct17 b0), rr, rr⟩
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz4.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   cases he0
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   cases he0
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he8
   subst b0
   intro he8
   cases he8
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   clear he9
   have hsize := congrArg sz he8
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    cases he2
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    cases he2
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz4.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     clear he2
     exact ⟨(zz3 ), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct222 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct222 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct222 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct14 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (zz3 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz4_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 =>
      rcases T.zz4.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), (rr.tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((rr.tail (rs .r33 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 =>
      rcases T.zz4.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), (rr.tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((rr.tail (Step.cQ11 (ct221 ) (rs .r16 (ct221 ) (lf 0) (lf 0)))).tail (rs .r33 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     exact vP48 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(ct27 b0), rr, (rr.tail (rs .r29 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(zz3 ), ((((rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((((((((((rr.tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct206 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct206 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct206 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct181 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0)))).tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), (rr.tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (Step.cQ11 (ct14 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct14 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r2 (zz3 ) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct249 b0), rr, (rr.tail (rs .r29 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct195 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ11 (ct195 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct195 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct195 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct195 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct195 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ11 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct242 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct182 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct181 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0))))).tail (rs .r16 (ct182 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP49 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
theorem peak_29 (a0 a1 a2 : T) {u : T} (h : Step (ct49 a0) u) :
  Join (ct27 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz4.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(ct27 b0), rr, rr⟩
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he4
   subst b0
   intro he4
   cases he4
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he4
   subst b0
   intro he4
   cases he4
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz4.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz4.inj he4 with ⟨he6, he7⟩
   clear he4
   rcases T.zz2.inj he7 with ⟨he8, he9⟩
   clear he7
   clear he9
   have hsize := congrArg sz he8
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    cases he2
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    cases he2
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz4.inj he0 with ⟨he2, he3⟩
     clear he0
     rcases T.zz2.inj he3 with ⟨he4, he5⟩
     clear he3
     clear he5
     revert he2
     subst a0
     intro he2
     clear he2
     exact ⟨(zz3 ), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (rs .r5 (ct195 ) (lf 0) (lf 0))).tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz4_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 =>
      rcases T.zz4.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 =>
      rcases T.zz4.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(zz3 ), ((rr.tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (rs .r5 (ct342 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(ct17 b0), (rr.tail (Step.cQ10 (zz3 ) (rs .r16 b0 (lf 0) (lf 0)))), (rr.tail (rs .r28 b0 (lf 0) (lf 0)))⟩
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), ((((rr.tail (Step.cQ10 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), (((((((((rr.tail (Step.cQ11 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ11 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct194 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct194 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct194 ) (lf 0) (lf 0))).tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), ((((rr.tail (Step.cQ10 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ10 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct181 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0)))).tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      exact vP50 a0 a1 a2 u4 h4
     ·
      rcases step_zz3_cases h4 with hr
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 => cases hE
       | r12 => cases hE
       | r13 => cases hE
       | r14 => cases hE
       | r15 => cases hE
       | r16 => cases hE
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 => cases hE
       | r22 => cases hE
       | r23 => cases hE
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 => cases hE
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 => cases hE
       | r37 => cases hE
       | r38 => cases hE
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  exact vP51 a0 a1 a2 u0 h0
theorem peak_30 (a0 a1 a2 : T) {u : T} (h : Step (ct51 a0) u) :
  Join (ct30 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((rr.tail (Step.cQ7 (ct221 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨(ct30 b0), rr, rr⟩
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst b0
   intro he0 he2 he6
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(ct39 b0), rr, ((rr.tail (Step.cQ12 b0 (Step.cQ8 (ct20 b0) (rs .r16 b0 (lf 0) (lf 0))))).tail (rs .r31 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((((((((rr.tail (Step.cQ11 (ct307 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct307 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct307 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((rr.tail (Step.cQ11 (ct281 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct281 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct359 b0), rr, ((rr.tail (Step.cQ12 (ct20 b0) (Step.cQ8 (ct21 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r31 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 (ct14 ) (lf 0) (lf 0))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct361 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct361 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct361 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct361 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (ct14 ) (lf 0) (lf 0))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct367 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct367 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct367 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct367 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct275 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct275 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct182 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP55 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he6, he7⟩
    clear he0
    revert he6
    subst b0
    intro he6
    cases he6
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP56 a0 a1 a2 u1 h1
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     subst a0
     exact ⟨(ct39 b0), rr, ((rr.tail (Step.cQ11 (ct52 b0) (rs .r16 b0 (lf 0) (lf 0)))).tail (rs .r31 b0 (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     subst a0
     exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct369 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct369 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct369 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct369 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((rr.tail (Step.cQ11 (ct181 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (rs .r10 (ct14 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(ct359 b0), rr, ((rr.tail (Step.cQ11 (ct371 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0)))).tail (rs .r31 (ct20 b0) (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 (ct14 ) (lf 0) (lf 0))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct312 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct312 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct312 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct312 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct312 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct195 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct195 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (ct14 ) (lf 0) (lf 0))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct316 ) (rs .r16 (ct182 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct316 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct316 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct316 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct316 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP57 a0 a1 a2 u3 h3
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
theorem peak_31 (a0 a1 a2 : T) {u : T} (h : Step (ct53 a0) u) :
  Join (ct39 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he0 he4
   subst b0
   intro he0 he4
   revert he0
   subst b1
   intro he0
   clear he0
   exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((rr.tail (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   cases he0
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨(ct39 b0), rr, rr⟩
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   cases he0
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he0 he8
   subst b0
   intro he0 he8
   clear he8
   clear he0
   exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((rr.tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
 ·
  exact vP58 a0 a1 a2 u0 h0
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    cases he2
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    rcases T.zz2.inj he4 with ⟨he6, he7⟩
    clear he4
    revert he6
    subst b0
    intro he6
    cases he6
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    rcases T.zz2.inj he4 with ⟨he6, he7⟩
    clear he4
    revert he6
    subst b0
    intro he6
    clear he6
    exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (rr.tail (rs .r24 (zz3 ) (lf 0) (lf 0)))⟩
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    have hsize := congrArg sz he2
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (rr.tail (rs .r2 (zz3 ) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct30 b0), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct22 b0) (rs .r16 b0 (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 b0 (rs .r16 b0 (lf 0) (lf 0)))))), (rr.tail (rs .r30 b0 (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct195 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct195 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct195 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (rr.tail (rs .r2 (ct194 ) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (rr.tail (rs .r2 (ct206 ) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP59 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   exact vP60 a0 a1 a2 u1 h1
theorem peak_32 (a0 a1 a2 : T) {u : T} (h : Step (ct55 a0) u) :
  Join (ct52 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he0 he4
   subst b0
   intro he0 he4
   revert he0
   subst b1
   intro he0
   clear he0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct180 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct198 ) (lf 0) (lf 0))))).tail (rs .r16 (ct198 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((rr.tail (rs .r16 (ct198 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst b0
   intro he0 he6
   cases he6
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   cases he0
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨(ct52 b0), rr, rr⟩
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   cases he0
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst b0
   intro he0 he6
   cases he6
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   have hsize := congrArg sz he9
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
 ·
  exact vP61 a0 a1 a2 u0 h0
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    subst b0
    exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((rr.tail (rs .r15 (ct180 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    rcases T.zz2.inj he4 with ⟨he6, he7⟩
    clear he4
    have hsize := congrArg sz he7
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    rcases T.zz2.inj he4 with ⟨he6, he7⟩
    clear he4
    have hsize := congrArg sz he7
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    rcases T.zz2.inj he4 with ⟨he6, he7⟩
    clear he4
    clear he7
    cases he6
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     rcases T.zz2.inj he2 with ⟨he4, he5⟩
     clear he2
     cases he5
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     rcases T.zz2.inj he2 with ⟨he4, he5⟩
     clear he2
     cases he5
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      cases he0
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      cases he3
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      cases he3
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       rcases T.zz2.inj he1 with ⟨he2, he3⟩
       clear he1
       clear he3
       revert he0
       subst a0
       intro he0
       have hsize := congrArg sz he0
       have hp_b0 := sz_pos b0
       simp only [sz] at hsize
       omega
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       rcases T.zz2.inj he1 with ⟨he2, he3⟩
       clear he1
       clear he3
       revert he0
       subst a0
       intro he0
       cases he0
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       cases he0
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       rcases T.zz2.inj he1 with ⟨he2, he3⟩
       clear he1
       clear he3
       revert he0
       subst a0
       intro he0
       clear he0
       exact ⟨(ct77 b0), rr, (rr.tail (rs .r41 b0 (lf 0) (lf 0)))⟩
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       rcases T.zz2.inj he1 with ⟨he2, he3⟩
       clear he1
       clear he3
       revert he0
       subst a0
       intro he0
       rcases T.zz2.inj he0 with ⟨he4, he5⟩
       clear he0
       clear he5
       rcases T.zz2.inj he4 with ⟨he6, he7⟩
       clear he4
       clear he7
       have hsize := congrArg sz he6
       have hp_b0 := sz_pos b0
       simp only [sz] at hsize
       omega
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       rcases T.zz2.inj he0 with ⟨he2, he3⟩
       clear he0
       clear he3
       have hsize := congrArg sz he2
       have hp_a0 := sz_pos a0
       simp only [sz] at hsize
       omega
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      rcases step_zz2_cases h4 with hr | ⟨u5, rfl, h5⟩ | ⟨u5, rfl, h5⟩
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        clear he1
        subst a0
        exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((rr.tail (rs .r8 (zz3 ) (ct182 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct181 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0))))).tail (rs .r16 (ct182 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
       | r12 => cases hE
       | r13 => cases hE
       | r14 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r15 => cases hE
       | r16 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        clear he1
        subst a0
        exact ⟨(ct50 b0), (rr.tail (Step.cQ7 (ct21 b0) (rs .r16 b0 (lf 0) (lf 0)))), ((rr.tail (Step.cQ12 (ct21 b0) (Step.cQ7 (ct21 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 b0 (rs .r16 b0 (lf 0) (lf 0)))))))).tail (rs .r40 b0 (lf 0) (lf 0)))⟩
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r22 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r23 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        revert he0
        subst b0
        intro he0
        subst a0
        exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (ct194 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (rs .r14 (ct14 ) (lf 0) (lf 0))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((((rr.tail (Step.cQ11 (ct391 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct391 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct391 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct195 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct195 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (rs .r38 (ct194 ) (lf 0) (lf 0)))).tail (rs .r16 (ct364 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r37 => cases hE
       | r38 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        revert he0
        subst b0
        intro he0
        subst a0
        exact ⟨(zz3 ), (((((rr.tail (Step.cQ7 (ct206 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ7 (ct206 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (rs .r21 (zz3 ) (lf 0) (lf 0))), (((((((((((rr.tail (Step.cQ11 (ct396 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct396 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct396 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (rs .r38 (ct206 ) (lf 0) (lf 0)))).tail (rs .r16 (ct271 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
      ·
       exact vP62 a0 a1 a2 u5 h5
      ·
       rcases step_zz3_cases h5 with hr
       ·
        rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
        rw [hout]
        cases k with
        | r0 => cases hE
        | r1 => cases hE
        | r2 => cases hE
        | r3 => cases hE
        | r4 => cases hE
        | r5 => cases hE
        | r6 => cases hE
        | r7 => cases hE
        | r8 => cases hE
        | r9 => cases hE
        | r10 => cases hE
        | r11 => cases hE
        | r12 => cases hE
        | r13 => cases hE
        | r14 => cases hE
        | r15 => cases hE
        | r16 => cases hE
        | r17 => cases hE
        | r18 => cases hE
        | r19 => cases hE
        | r20 => cases hE
        | r21 => cases hE
        | r22 => cases hE
        | r23 => cases hE
        | r24 => cases hE
        | r25 => cases hE
        | r26 => cases hE
        | r27 => cases hE
        | r28 => cases hE
        | r29 => cases hE
        | r30 => cases hE
        | r31 => cases hE
        | r32 => cases hE
        | r33 => cases hE
        | r34 => cases hE
        | r35 => cases hE
        | r36 => cases hE
        | r37 => cases hE
        | r38 => cases hE
        | r39 => cases hE
        | r40 => cases hE
        | r41 => cases hE
        | r42 => cases hE
        | r43 => cases hE
        | r44 => cases hE
     ·
      rcases step_zz2_cases h4 with hr | ⟨u5, rfl, h5⟩ | ⟨u5, rfl, h5⟩
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        clear he1
        subst a0
        exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((rr.tail (rs .r8 (zz3 ) (ct222 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct221 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct14 ) (lf 0))))).tail (rs .r16 (ct258 ) (lf 0) (lf 0))).tail (rs .r8 (zz3 ) (zz3 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
       | r12 => cases hE
       | r13 => cases hE
       | r14 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r15 => cases hE
       | r16 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        clear he1
        subst a0
        exact ⟨(ct50 b0), (rr.tail (Step.cQ7 (ct21 b0) (rs .r16 b0 (lf 0) (lf 0)))), ((rr.tail (Step.cQ12 (ct21 b0) (Step.cQ7 (ct21 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 b0 (rs .r16 b0 (lf 0) (lf 0)))))))).tail (rs .r40 b0 (lf 0) (lf 0)))⟩
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r22 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r23 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        revert he0
        subst b0
        intro he0
        subst a0
        exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (ct194 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (rs .r14 (ct14 ) (lf 0) (lf 0))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct405 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct405 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct405 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct194 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 (ct14 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct194 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r37 => cases hE
       | r38 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        revert he0
        subst b0
        intro he0
        subst a0
        exact ⟨(zz3 ), (((((rr.tail (Step.cQ7 (ct206 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ7 (ct206 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (rs .r21 (zz3 ) (lf 0) (lf 0))), (((((((((((((rr.tail (Step.cQ11 (ct408 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct408 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct408 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
      ·
       exact vP63 a0 a1 a2 u5 h5
      ·
       rcases step_zz3_cases h5 with hr
       ·
        rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
        rw [hout]
        cases k with
        | r0 => cases hE
        | r1 => cases hE
        | r2 => cases hE
        | r3 => cases hE
        | r4 => cases hE
        | r5 => cases hE
        | r6 => cases hE
        | r7 => cases hE
        | r8 => cases hE
        | r9 => cases hE
        | r10 => cases hE
        | r11 => cases hE
        | r12 => cases hE
        | r13 => cases hE
        | r14 => cases hE
        | r15 => cases hE
        | r16 => cases hE
        | r17 => cases hE
        | r18 => cases hE
        | r19 => cases hE
        | r20 => cases hE
        | r21 => cases hE
        | r22 => cases hE
        | r23 => cases hE
        | r24 => cases hE
        | r25 => cases hE
        | r26 => cases hE
        | r27 => cases hE
        | r28 => cases hE
        | r29 => cases hE
        | r30 => cases hE
        | r31 => cases hE
        | r32 => cases hE
        | r33 => cases hE
        | r34 => cases hE
        | r35 => cases hE
        | r36 => cases hE
        | r37 => cases hE
        | r38 => cases hE
        | r39 => cases hE
        | r40 => cases hE
        | r41 => cases hE
        | r42 => cases hE
        | r43 => cases hE
        | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   exact vP64 a0 a1 a2 u1 h1
theorem peak_33 (a0 a1 a2 : T) {u : T} (h : Step (ct56 a0) u) :
  Join (ct42 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   cases he0
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he4
   subst a0
   intro he4
   cases he4
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   cases he9
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he8
   subst b0
   intro he8
   cases he8
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he4
   subst a0
   intro he4
   cases he4
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   cases he0
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   cases he0
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(ct42 b0), rr, rr⟩
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   have hsize := congrArg sz he5
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   cases he9
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    revert he2
    subst a0
    intro he2
    cases he2
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    revert he2
    subst a0
    intro he2
    cases he2
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     clear he0
     exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (Step.cQ11 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (zz3 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst b0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct336 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct222 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct221 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct14 ) (lf 0))))).tail (rs .r16 (ct258 ) (lf 0) (lf 0))).tail (rs .r8 (zz3 ) (zz3 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
   ·
    exact vP65 a0 a1 a2 u2 h2
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(ct62 b0), rr, (rr.tail (rs .r34 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct181 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0)))).tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((rr.tail (Step.cQ11 (ct14 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r2 (zz3 ) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct421 b0), rr, (rr.tail (rs .r34 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((((((rr.tail (Step.cQ11 (ct195 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct195 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct195 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct195 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct195 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ11 (ct242 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct182 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (ct181 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0))))).tail (rs .r16 (ct182 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP66 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
theorem peak_34 (a0 a1 a2 : T) {u : T} (h : Step (ct59 a0) u) :
  Join (ct62 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   subst b0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   have hsize := congrArg sz he5
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(ct62 b0), rr, rr⟩
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   have hsize := congrArg sz he5
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   rcases T.zz2.inj he5 with ⟨he6, he7⟩
   clear he5
   clear he7
   have hsize := congrArg sz he6
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    cases he3
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    cases he3
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     clear he3
     revert he0
     subst a0
     intro he0
     subst b0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((rr.tail (Step.cQ11 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (zz3 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     clear he3
     revert he0
     subst a0
     intro he0
     cases he0
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     clear he3
     revert he0
     subst a0
     intro he0
     cases he0
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     clear he3
     revert he0
     subst a0
     intro he0
     cases he0
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((rr.tail (rs .r5 (ct221 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(ct42 b0), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 b0 (lf 0) (lf 0)))))), (rr.tail (rs .r33 b0 (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct194 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct194 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct194 ) (lf 0) (lf 0))).tail (rs .r23 (zz3 ) (lf 0) (lf 0))).tail (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r6 (zz3 ) (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ11 (ct206 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct181 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0)))).tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP67 a0 a1 a2 u3 h3
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  exact vP68 a0 a1 a2 u0 h0
theorem peak_35 (a0 a1 a2 : T) {u : T} (h : Step (ct60 a0) u) :
  Join (ct42 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b1
   intro he0
   cases he0
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   revert he0
   subst b0
   intro he0
   clear he0
   exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), rr⟩
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   cases he6
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   clear he9
   have hsize := congrArg sz he8
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   cases he6
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   cases he9
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   clear he6
   clear he0
   exact ⟨(ct42 b0), rr, rr⟩
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   clear he6
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(ct62 b0), rr, (rr.tail (rs .r37 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((((((rr.tail (Step.cQ11 (ct424 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct424 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct280 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct356 ) (lf 0) (lf 0)))).tail (rs .r16 (ct280 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((rr.tail (Step.cQ11 (ct222 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct14 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (zz3 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct421 b0), rr, (rr.tail (rs .r37 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((((((rr.tail (Step.cQ11 (ct426 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct426 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct426 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct365 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct382 ) (lf 0) (lf 0)))).tail (rs .r16 (ct365 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct416 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct416 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct416 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct306 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct415 ) (lf 0) (lf 0)))).tail (rs .r16 (ct306 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (rs .r21 (zz3 ) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP69 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    subst b0
    exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((rr.tail (rs .r5 (ct221 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    cases he4
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((rr.tail (rs .r33 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((rr.tail (Step.cQ11 (ct221 ) (rs .r16 (ct221 ) (lf 0) (lf 0)))).tail (rs .r33 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     exact vP70 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
theorem peak_36 (a0 a1 a2 : T) {u : T} (h : Step (ct61 a0) u) :
  Join (ct42 a0) u := by
 rcases step_zz2_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r12 => cases hE
  | r13 => cases hE
  | r14 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r15 => cases hE
  | r16 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r22 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   cases he0
  | r23 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he6, he7⟩
   clear he0
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   clear he9
   rcases T.zz2.inj he8 with ⟨he10, he11⟩
   clear he8
   have hsize := congrArg sz he11
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(ct42 b0), rr, rr⟩
  | r37 => cases hE
  | r38 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    subst b0
    exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((rr.tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a0
    intro he4
    cases he4
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((rr.tail (Step.cQ7 (ct221 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((rr.tail (Step.cQ7 (ct336 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct336 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct221 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     exact vP71 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(ct62 b0), rr, (rr.tail (rs .r38 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (rs .r27 (ct14 ) (lf 0) (lf 0))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), (rr.tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((rr.tail (Step.cQ7 (ct14 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct421 b0), rr, (rr.tail (rs .r38 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ7 (ct195 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct195 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct195 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP72 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
theorem peak_37 (a0 a1 a2 : T) {u : T} (h : Step (ct63 a0) u) :
  Join (ct62 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b1
   intro he0
   subst a0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((rr.tail (Step.cQ7 (zz3 ) (rs .r15 (ct182 ) (lf 0) (lf 0)))).tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   subst a0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((rr.tail (rs .r16 (ct181 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst b0
   intro he0 he6
   cases he6
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   rcases T.zz2.inj he7 with ⟨he8, he9⟩
   clear he7
   clear he9
   revert he0 he6
   subst a0
   intro he0 he6
   cases he6
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst b0
   intro he0 he6
   clear he6
   have hsize := congrArg sz he0
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   rcases T.zz2.inj he7 with ⟨he8, he9⟩
   clear he7
   clear he9
   revert he0 he6
   subst a0
   intro he0 he6
   clear he6
   clear he0
   exact ⟨(ct62 b0), rr, rr⟩
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
 ·
  exact vP73 a0 a1 a2 u0 h0
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    cases he5
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    cases he5
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     cases he3
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     cases he3
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((rr.tail (rs .r33 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      cases he0
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      cases he0
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((rr.tail (rs .r8 (zz3 ) (ct14 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r8 (zz3 ) (zz3 ) (lf 0)))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r2 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(ct42 b0), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 b0 (lf 0) (lf 0)))))), (rr.tail (rs .r35 b0 (lf 0) (lf 0)))⟩
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct426 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct426 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct365 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct382 ) (lf 0) (lf 0)))).tail (rs .r16 (ct365 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ11 (ct416 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct416 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r8 (zz3 ) (ct306 ) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r15 (ct415 ) (lf 0) (lf 0)))).tail (rs .r16 (ct306 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (rs .r21 (zz3 ) (lf 0) (lf 0)))⟩
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      exact vP74 a0 a1 a2 u4 h4
     ·
      rcases step_zz3_cases h4 with hr
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 => cases hE
       | r12 => cases hE
       | r13 => cases hE
       | r14 => cases hE
       | r15 => cases hE
       | r16 => cases hE
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 => cases hE
       | r22 => cases hE
       | r23 => cases hE
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 => cases hE
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 => cases hE
       | r37 => cases hE
       | r38 => cases hE
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
theorem peak_38 (a0 a1 a2 : T) {u : T} (h : Step (ct64 a0) u) :
  Join (ct62 a0) u := by
 rcases step_zz2_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 => cases hE
  | r2 => cases hE
  | r3 => cases hE
  | r4 => cases hE
  | r5 => cases hE
  | r6 => cases hE
  | r7 => cases hE
  | r8 => cases hE
  | r9 => cases hE
  | r10 => cases hE
  | r11 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r12 => cases hE
  | r13 => cases hE
  | r14 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r15 => cases hE
  | r16 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   subst b0
   exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((rr.tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r17 => cases hE
  | r18 => cases hE
  | r19 => cases hE
  | r20 => cases hE
  | r21 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   have hsize := congrArg sz he0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r22 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r23 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   cases he0
  | r24 => cases hE
  | r25 => cases hE
  | r26 => cases hE
  | r27 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r28 => cases hE
  | r29 => cases hE
  | r30 => cases hE
  | r31 => cases hE
  | r32 => cases hE
  | r33 => cases hE
  | r34 => cases hE
  | r35 => cases hE
  | r36 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r37 => cases hE
  | r38 =>
   rcases T.zz2.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(ct62 b0), rr, rr⟩
  | r39 => cases hE
  | r40 => cases hE
  | r41 => cases hE
  | r42 => cases hE
  | r43 => cases hE
  | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    cases he5
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    cases he5
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     cases he3
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     cases he3
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((rr.tail (Step.cQ7 (ct221 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      cases he0
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      cases he0
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(zz3 ), ((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((rr.tail (rs .r16 (ct14 ) (lf 0) (lf 0))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(ct42 b0), (rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 b0 (lf 0) (lf 0)))))), (rr.tail (rs .r36 b0 (lf 0) (lf 0)))⟩
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((rr.tail (Step.cQ7 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct194 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct194 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), ((((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((rr.tail (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct206 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (rs .r21 (zz3 ) (lf 0) (lf 0)))⟩
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      exact vP75 a0 a1 a2 u4 h4
     ·
      rcases step_zz3_cases h4 with hr
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 => cases hE
       | r12 => cases hE
       | r13 => cases hE
       | r14 => cases hE
       | r15 => cases hE
       | r16 => cases hE
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 => cases hE
       | r22 => cases hE
       | r23 => cases hE
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 => cases hE
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 => cases hE
       | r37 => cases hE
       | r38 => cases hE
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  exact vP76 a0 a1 a2 u0 h0
theorem peak_39 (a0 a1 a2 : T) {u : T} (h : Step (ct66 a0 a1) u) :
  Join (ct35 a0 a1) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   revert he0
   subst a1
   intro he0
   clear he0
   exact ⟨(zz2 a0 a0), (rr.tail (Step.cQ8 a0 (rs .r16 a0 (lf 0) (lf 0)))), ((rr.tail (Step.cQ7 (ct22 a0) (rs .r16 a0 (lf 0) (lf 0)))).tail (Step.cQ8 a0 (rs .r16 a0 (lf 0) (lf 0))))⟩
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he0 he2 he8
   subst a1
   intro he0 he2 he8
   revert he0 he2
   subst a0
   intro he0 he2
   revert he0
   subst b1
   intro he0
   clear he0
   exact ⟨b0, (rr.tail (rs .r21 b0 (lf 0) (lf 0))), rr⟩
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he0 he2 he8
   subst a1
   intro he0 he2 he8
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨(ct35 b0 b1), rr, rr⟩
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_a1 := sz_pos a1
   simp only [sz] at hsize
   omega
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst b0
   intro he0 he2 he6
   cases he6
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   cases he6
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   cases he6
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a1
    intro he4
    subst a0
    exact ⟨(zz2 b0 b0), (rr.tail (Step.cQ8 b0 (rs .r16 b0 (lf 0) (lf 0)))), ((rr.tail (Step.cQ12 b0 (Step.cQ8 (zz3 ) (rs .r16 b0 (lf 0) (lf 0))))).tail (rs .r10 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he4
    subst a1
    intro he4
    subst a0
    exact ⟨(zz3 ), ((((((rr.tail (Step.cQ7 (ct242 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct271 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct271 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct271 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a1
     intro he2
     subst a0
     exact ⟨(ct37 b0), (rr.tail (Step.cQ8 (ct20 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0)))), ((rr.tail (Step.cQ12 (ct20 b0) (Step.cQ8 (zz3 ) (rs .r16 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r10 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a1
     intro he2
     subst a0
     exact ⟨(zz3 ), ((((((((rr.tail (Step.cQ7 (ct275 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct275 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct275 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct182 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct279 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct279 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct279 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct279 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct182 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(zz3 ), (rr.tail (rs .r21 (zz3 ) (lf 0) (lf 0))), (((((rr.tail (Step.cQ11 (ct282 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct282 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct282 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct17 b0), (rr.tail (rs .r21 (ct17 b0) (lf 0) (lf 0))), ((rr.tail (Step.cQ12 (ct21 b0) (rs .r21 (ct17 b0) (lf 0) (lf 0)))).tail (rs .r18 b0 (lf 0) (lf 0)))⟩
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct309 b0), (rr.tail (Step.cQ8 (ct21 b0) (rs .r16 (ct21 b0) (lf 0) (lf 0)))), ((rr.tail (Step.cQ12 (ct21 b0) (Step.cQ8 (zz3 ) (rs .r16 (ct21 b0) (lf 0) (lf 0))))).tail (rs .r10 (ct21 b0) (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct50 b0), (rr.tail (Step.cQ8 b0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 b0 (lf 0) (lf 0)))))), ((rr.tail (Step.cQ12 (ct21 b0) (Step.cQ8 (ct30 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 b0 (lf 0) (lf 0))))))).tail (rs .r40 b0 (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct78 b0), (rr.tail (Step.cQ8 (ct17 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r22 b0 (lf 0) (lf 0)))))), ((rr.tail (Step.cQ12 (ct45 b0) (Step.cQ8 (ct21 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r22 b0 (lf 0) (lf 0))))))).tail (rs .r42 b0 (lf 0) (lf 0)))⟩
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct80 b0), (rr.tail (Step.cQ8 (ct27 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 b0 (lf 0) (lf 0)))))), ((rr.tail (Step.cQ12 (ct48 b0) (Step.cQ8 b0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 b0 (lf 0) (lf 0))))))).tail (rs .r44 b0 (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct42 b0), (rr.tail (rs .r21 (ct42 b0) (lf 0) (lf 0))), ((rr.tail (Step.cQ12 (ct21 b0) (rs .r21 (ct42 b0) (lf 0) (lf 0)))).tail (rs .r35 b0 (lf 0) (lf 0)))⟩
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct77 b0), ((rr.tail (Step.cQ8 (ct42 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r36 b0 (lf 0) (lf 0)))))).tail (Step.cQ8 (ct42 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0)))), ((((rr.tail (Step.cQ11 (ct436 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0)))).tail (Step.cQ12 (ct41 b0) (Step.cQ8 (ct21 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r36 b0 (lf 0) (lf 0))))))).tail (Step.cQ12 (ct41 b0) (Step.cQ8 (ct21 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0))))).tail (rs .r41 b0 (lf 0) (lf 0)))⟩
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a1
      intro he0
      subst a0
      exact ⟨(ct79 b0), ((rr.tail (Step.cQ8 (ct62 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r38 b0 (lf 0) (lf 0)))))).tail (Step.cQ8 (ct62 b0) (rs .r16 (ct58 b0) (lf 0) (lf 0)))), ((((rr.tail (Step.cQ11 (ct438 b0) (rs .r16 (ct58 b0) (lf 0) (lf 0)))).tail (Step.cQ12 (ct58 b0) (Step.cQ8 b0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r38 b0 (lf 0) (lf 0))))))).tail (Step.cQ12 (ct58 b0) (Step.cQ8 b0 (rs .r16 (ct58 b0) (lf 0) (lf 0))))).tail (rs .r43 b0 (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP77 a0 a1 a2 u3 h3
    ·
     exact vP78 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    rcases T.zz2.inj he4 with ⟨he6, he7⟩
    clear he4
    revert he0 he6
    subst a1
    intro he0 he6
    revert he0
    subst a0
    intro he0
    clear he0
    exact ⟨b0, (rr.tail (rs .r21 b0 (lf 0) (lf 0))), (rr.tail (rs .r17 b0 b0 (lf 0)))⟩
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    rcases T.zz2.inj he4 with ⟨he6, he7⟩
    clear he4
    revert he0 he6
    subst a1
    intro he0 he6
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    have hp_a1 := sz_pos a1
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP79 a0 a1 a2 u1 h1
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     rcases T.zz2.inj he2 with ⟨he4, he5⟩
     clear he2
     revert he4
     subst a1
     intro he4
     subst a0
     exact ⟨(zz2 b0 b0), (rr.tail (Step.cQ8 b0 (rs .r16 b0 (lf 0) (lf 0)))), ((rr.tail (Step.cQ11 (ct12 b0) (rs .r16 b0 (lf 0) (lf 0)))).tail (rs .r10 b0 (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     rcases T.zz2.inj he2 with ⟨he4, he5⟩
     clear he2
     revert he4
     subst a1
     intro he4
     subst a0
     exact ⟨(zz3 ), ((((((rr.tail (Step.cQ7 (ct242 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ11 (ct306 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct306 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct306 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct306 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      cases he0
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      revert he2
      subst a1
      intro he2
      subst a0
      exact ⟨(ct37 b0), (rr.tail (Step.cQ8 (ct20 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0)))), ((rr.tail (Step.cQ11 (ct57 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0)))).tail (rs .r10 (ct20 b0) (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      revert he2
      subst a1
      intro he2
      subst a0
      exact ⟨(zz3 ), ((((((((rr.tail (Step.cQ7 (ct275 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct275 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct275 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct182 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct271 ) (rs .r16 (ct182 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct271 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct271 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct271 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct271 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(zz3 ), (rr.tail (rs .r21 (zz3 ) (lf 0) (lf 0))), ((((((rr.tail (Step.cQ11 (ct281 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct281 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct17 b0), (rr.tail (rs .r21 (ct17 b0) (lf 0) (lf 0))), (((rr.tail (Step.cQ11 (ct32 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 b0 (lf 0) (lf 0)))))).tail (Step.cQ12 (ct21 b0) (rs .r22 b0 (lf 0) (lf 0)))).tail (rs .r18 b0 (lf 0) (lf 0)))⟩
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct309 b0), (rr.tail (Step.cQ8 (ct21 b0) (rs .r16 (ct21 b0) (lf 0) (lf 0)))), ((rr.tail (Step.cQ11 (ct419 b0) (rs .r16 (ct21 b0) (lf 0) (lf 0)))).tail (rs .r10 (ct21 b0) (lf 0) (lf 0)))⟩
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct50 b0), (rr.tail (Step.cQ8 b0 (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 b0 (lf 0) (lf 0)))))), ((rr.tail (Step.cQ11 (ct67 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 b0 (lf 0) (lf 0)))))).tail (rs .r40 b0 (lf 0) (lf 0)))⟩
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct78 b0), (rr.tail (Step.cQ8 (ct17 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r22 b0 (lf 0) (lf 0)))))), ((rr.tail (Step.cQ11 (ct71 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r22 b0 (lf 0) (lf 0)))))).tail (rs .r42 b0 (lf 0) (lf 0)))⟩
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct80 b0), (rr.tail (Step.cQ8 (ct27 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 b0 (lf 0) (lf 0)))))), ((rr.tail (Step.cQ11 (ct75 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 b0 (lf 0) (lf 0)))))).tail (rs .r44 b0 (lf 0) (lf 0)))⟩
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct42 b0), (rr.tail (rs .r21 (ct42 b0) (lf 0) (lf 0))), (((rr.tail (Step.cQ11 (ct61 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 b0 (lf 0) (lf 0)))))).tail (Step.cQ12 (ct21 b0) (rs .r36 b0 (lf 0) (lf 0)))).tail (rs .r35 b0 (lf 0) (lf 0)))⟩
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct77 b0), ((rr.tail (Step.cQ8 (ct42 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r36 b0 (lf 0) (lf 0)))))).tail (Step.cQ8 (ct42 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0)))), ((((rr.tail (Step.cQ11 (ct437 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r36 b0 (lf 0) (lf 0)))))).tail (Step.cQ11 (ct437 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0)))).tail (Step.cQ12 (ct41 b0) (Step.cQ8 (ct21 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0))))).tail (rs .r41 b0 (lf 0) (lf 0)))⟩
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a1
       intro he0
       subst a0
       exact ⟨(ct79 b0), ((rr.tail (Step.cQ8 (ct62 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r38 b0 (lf 0) (lf 0)))))).tail (Step.cQ8 (ct62 b0) (rs .r16 (ct58 b0) (lf 0) (lf 0)))), ((((rr.tail (Step.cQ11 (ct439 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r38 b0 (lf 0) (lf 0)))))).tail (Step.cQ11 (ct439 b0) (rs .r16 (ct58 b0) (lf 0) (lf 0)))).tail (Step.cQ12 (ct58 b0) (Step.cQ8 b0 (rs .r16 (ct58 b0) (lf 0) (lf 0))))).tail (rs .r43 b0 (lf 0) (lf 0)))⟩
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      exact vP80 a0 a1 a2 u4 h4
     ·
      exact vP81 a0 a1 a2 u4 h4
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
theorem peak_40 (a0 a1 a2 : T) {u : T} (h : Step (ct68 a0) u) :
  Join (ct50 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   have hsize := congrArg sz he4
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he0 he8
   subst a0
   intro he0 he8
   clear he8
   clear he0
   exact ⟨(zz3 ), (((rr.tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((rr.tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz2.inj he6 with ⟨he8, he9⟩
   clear he6
   have hsize := congrArg sz he9
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   clear he2
   clear he0
   exact ⟨(ct50 b0), rr, rr⟩
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst b0
   intro he0 he2 he6
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he8, he9⟩
   clear he2
   clear he9
   rcases T.zz2.inj he8 with ⟨he10, he11⟩
   clear he8
   clear he11
   cases he10
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he8, he9⟩
   clear he2
   clear he9
   rcases T.zz2.inj he8 with ⟨he10, he11⟩
   clear he8
   clear he11
   have hsize := congrArg sz he10
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst a0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(ct52 b0), (rr.tail (Step.cQ8 (ct20 b0) (rs .r16 b0 (lf 0) (lf 0)))), ((rr.tail (Step.cQ12 b0 (Step.cQ8 (ct39 b0) (rs .r16 b0 (lf 0) (lf 0))))).tail (rs .r32 b0 (lf 0) (lf 0)))⟩
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    subst a0
    exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct441 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct441 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct441 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (rs .r36 (ct182 ) (lf 0) (lf 0)))).tail (rs .r16 (ct280 ) (lf 0) (lf 0))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((rr.tail (Step.cQ11 (ct447 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct447 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (rs .r36 (zz3 ) (lf 0) (lf 0)))).tail (rs .r16 (ct14 ) (lf 0) (lf 0))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     subst a0
     exact ⟨(ct371 b0), (rr.tail (Step.cQ8 (ct21 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0)))), ((rr.tail (Step.cQ12 (ct20 b0) (Step.cQ8 (ct359 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0))))).tail (rs .r32 (ct20 b0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct449 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct449 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct449 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct449 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct223 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 (ct14 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct223 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     subst a0
     exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct275 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct275 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct182 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct451 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct451 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct451 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct451 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct275 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (ct14 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct275 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct182 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    exact vP84 a0 a1 a2 u2 h2
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst a0
    intro he0
    have hsize := congrArg sz he0
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst a0
    intro he0
    cases he0
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he6, he7⟩
    clear he0
    clear he7
    rcases T.zz2.inj he6 with ⟨he8, he9⟩
    clear he6
    clear he9
    rcases T.zz2.inj he8 with ⟨he10, he11⟩
    clear he8
    have hsize := congrArg sz he11
    have hp_b0 := sz_pos b0
    simp only [sz] at hsize
    omega
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst a0
    intro he0
    rcases T.zz2.inj he0 with ⟨he6, he7⟩
    clear he0
    clear he7
    rcases T.zz2.inj he6 with ⟨he8, he9⟩
    clear he6
    clear he9
    rcases T.zz2.inj he8 with ⟨he10, he11⟩
    clear he8
    clear he11
    subst b0
    exact ⟨(zz3 ), (((rr.tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (rr.tail (rs .r24 (zz3 ) (lf 0) (lf 0)))⟩
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    rcases T.zz2.inj he4 with ⟨he6, he7⟩
    clear he4
    have hsize := congrArg sz he7
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     rcases T.zz2.inj he2 with ⟨he4, he5⟩
     clear he2
     revert he4
     subst a0
     intro he4
     subst b0
     exact ⟨(zz3 ), (((rr.tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((rr.tail (rs .r10 (ct221 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct221 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     rcases T.zz2.inj he2 with ⟨he4, he5⟩
     clear he2
     revert he4
     subst a0
     intro he4
     cases he4
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      cases he0
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      revert he2
      subst a0
      intro he2
      cases he2
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      rcases T.zz2.inj he0 with ⟨he2, he3⟩
      clear he0
      revert he2
      subst a0
      intro he2
      cases he2
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       clear he0
       exact ⟨(zz3 ), (((rr.tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (rr.tail (rs .r2 (ct221 ) (lf 0) (lf 0)))⟩
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       clear he0
       exact ⟨(ct78 b0), rr, (rr.tail (rs .r42 b0 (lf 0) (lf 0)))⟩
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       cases he0
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       have hsize := congrArg sz he0
       have hp_b0 := sz_pos b0
       simp only [sz] at hsize
       omega
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       cases he0
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       have hsize := congrArg sz he0
       have hp_b0 := sz_pos b0
       simp only [sz] at hsize
       omega
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       clear he0
       exact ⟨(ct77 b0), (rr.tail (Step.cQ8 (ct42 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0)))), (((rr.tail (Step.cQ11 (ct437 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0)))).tail (Step.cQ12 (ct41 b0) (Step.cQ8 (ct21 b0) (rs .r16 (ct41 b0) (lf 0) (lf 0))))).tail (rs .r41 b0 (lf 0) (lf 0)))⟩
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       rcases T.zz2.inj he0 with ⟨he2, he3⟩
       clear he0
       clear he3
       rcases T.zz2.inj he2 with ⟨he4, he5⟩
       clear he2
       clear he5
       have hsize := congrArg sz he4
       have hp_b0 := sz_pos b0
       simp only [sz] at hsize
       omega
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       have hsize := congrArg sz he0
       have hp_b0 := sz_pos b0
       simp only [sz] at hsize
       omega
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      exact vP85 a0 a1 a2 u4 h4
     ·
      exact vP86 a0 a1 a2 u4 h4
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     subst a0
     exact ⟨(ct52 b0), (rr.tail (Step.cQ8 (ct20 b0) (rs .r16 b0 (lf 0) (lf 0)))), ((rr.tail (Step.cQ11 (ct54 b0) (rs .r16 b0 (lf 0) (lf 0)))).tail (rs .r32 b0 (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     subst a0
     exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct242 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct452 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct452 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct452 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct452 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct182 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct206 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (rs .r27 (ct14 ) (lf 0) (lf 0)))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(zz3 ), (((rr.tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ11 (ct457 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct457 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct457 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(ct371 b0), (rr.tail (Step.cQ8 (ct21 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0)))), ((rr.tail (Step.cQ11 (ct458 b0) (rs .r16 (ct20 b0) (lf 0) (lf 0)))).tail (rs .r32 (ct20 b0) (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct459 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct459 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct459 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct459 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct459 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct195 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r14 (ct14 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct195 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct275 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct275 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r16 (ct182 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct461 ) (rs .r16 (ct182 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct461 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct461 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct461 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct461 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r27 (ct14 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct242 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP87 a0 a1 a2 u3 h3
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
theorem peak_41 (a0 a1 a2 : T) {u : T} (h : Step (ct70 a0) u) :
  Join (ct77 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he6
   subst a0
   intro he0 he6
   clear he6
   clear he0
   exact ⟨(zz3 ), ((rr.tail (rs .r36 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), rr⟩
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he4
   subst a0
   intro he4
   cases he4
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst a0
   intro he0 he2 he6
   cases he6
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   revert he4
   subst a0
   intro he4
   cases he4
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst a0
   intro he0 he2 he6
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   have hsize := congrArg sz he5
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst a0
   intro he0 he2 he6
   cases he6
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst a0
   intro he0 he2 he6
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he8, he9⟩
   clear he2
   clear he9
   rcases T.zz2.inj he8 with ⟨he10, he11⟩
   clear he8
   clear he11
   cases he10
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst a0
   intro he0 he2 he6
   clear he6
   clear he2
   clear he0
   exact ⟨(ct77 b0), rr, rr⟩
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst a0
   intro he0 he2 he6
   cases he6
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst a0
   intro he0 he2 he6
   clear he6
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst a0
   intro he0 he2 he6
   cases he6
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    revert he2
    subst a0
    intro he2
    cases he2
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    revert he2
    subst a0
    intro he2
    cases he2
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     clear he0
     exact ⟨(zz3 ), ((rr.tail (rs .r36 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct462 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct462 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct221 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     subst b0
     exact ⟨(zz3 ), ((((((rr.tail (Step.cQ7 (ct333 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct333 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct333 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((rr.tail (Step.cQ11 (ct464 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct464 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct333 ) (rs .r16 (ct221 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct333 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct333 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst a0
     intro he0
     cases he0
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
   ·
    exact vP88 a0 a1 a2 u2 h2
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he0 he4
    subst a0
    intro he0 he4
    cases he4
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he0 he4
    subst a0
    intro he0 he4
    revert he0
    subst b0
    intro he0
    cases he0
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he0 he4
    subst a0
    intro he0 he4
    cases he4
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    revert he0 he4
    subst a0
    intro he0 he4
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he6, he7⟩
    clear he0
    clear he7
    rcases T.zz2.inj he6 with ⟨he8, he9⟩
    clear he6
    clear he9
    cases he8
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    have hsize := congrArg sz he4
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     subst a0
     exact ⟨(ct79 b0), rr, (rr.tail (rs .r43 b0 (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     subst a0
     exact ⟨(zz3 ), ((((((((((rr.tail (Step.cQ7 (ct356 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (ct356 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct356 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct356 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((((((((rr.tail (Step.cQ11 (ct468 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ11 (ct468 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct468 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct468 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct468 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct468 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct356 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct356 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(zz3 ), ((rr.tail (rs .r36 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct463 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct463 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct463 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(ct472 b0), rr, (rr.tail (rs .r43 (ct20 b0) (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), ((((((((rr.tail (Step.cQ7 (ct382 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct382 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct382 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((((rr.tail (Step.cQ11 (ct473 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct473 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct473 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct473 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct473 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct382 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct382 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct382 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), ((((((((rr.tail (Step.cQ7 (ct415 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ7 (ct415 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct415 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct415 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((rr.tail (Step.cQ11 (ct478 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ11 (ct478 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct478 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct478 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct415 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct415 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct415 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP89 a0 a1 a2 u3 h3
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     cases he2
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      clear he0
      exact ⟨(zz3 ), ((rr.tail (rs .r36 (zz3 ) (lf 0) (lf 0))).tail (rs .r16 (zz3 ) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ11 (ct482 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (rs .r31 (ct14 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct221 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), ((((((rr.tail (Step.cQ7 (ct333 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct333 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct333 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((rr.tail (Step.cQ11 (ct485 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct485 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct485 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r16 (ct221 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct14 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      cases he0
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     exact vP90 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
theorem peak_42 (a0 a1 a2 : T) {u : T} (h : Step (ct72 a0) u) :
  Join (ct78 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   cases he6
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz4.inj he4 with ⟨he6, he7⟩
   clear he4
   have hsize := congrArg sz he7
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst b0
   intro he0 he2
   cases he2
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   have hsize := congrArg sz he6
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   cases he6
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst b0
   intro he0 he2
   rcases T.zz2.inj he2 with ⟨he8, he9⟩
   clear he2
   clear he9
   rcases T.zz2.inj he8 with ⟨he10, he11⟩
   clear he8
   clear he11
   have hsize := congrArg sz he10
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst b0
   intro he0 he2 he6
   cases he6
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz4.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he0 he2 he8
   subst a0
   intro he0 he2 he8
   clear he8
   clear he2
   clear he0
   exact ⟨(ct78 b0), rr, rr⟩
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz4.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he0 he2 he8
   subst a0
   intro he0 he2 he8
   clear he8
   have hsize := congrArg sz he2
   have hp_b0 := sz_pos b0
   simp only [sz] at hsize
   omega
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    cases he2
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    cases he2
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz4.inj he0 with ⟨he2, he3⟩
     clear he0
     revert he2
     subst a0
     intro he2
     clear he2
     exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((((rr.tail (Step.cQ11 (ct450 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct450 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct450 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct450 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct223 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz4_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 =>
      rcases T.zz4.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), (((((rr.tail (Step.cQ7 (ct342 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct486 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct486 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct486 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct342 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct342 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 =>
      rcases T.zz4.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), (((((rr.tail (Step.cQ7 (ct342 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((((rr.tail (Step.cQ11 (ct486 ) (rs .r16 (ct221 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct486 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct486 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct486 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct342 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct342 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     exact vP91 a0 a1 a2 u3 h3
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    cases he4
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst b0
    intro he0
    cases he0
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    cases he4
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he6, he7⟩
    clear he0
    clear he7
    rcases T.zz2.inj he6 with ⟨he8, he9⟩
    clear he6
    clear he9
    have hsize := congrArg sz he8
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    have hsize := congrArg sz he4
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     subst a0
     exact ⟨(ct80 b0), rr, (rr.tail (rs .r44 b0 (lf 0) (lf 0)))⟩
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     subst a0
     exact ⟨(zz3 ), (((((((((((rr.tail (Step.cQ7 (ct338 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct338 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct338 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct338 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((((((((((rr.tail (Step.cQ11 (ct489 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ11 (ct489 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ11 (ct489 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct489 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct489 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct489 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct489 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct338 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct338 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(zz3 ), (((((rr.tail (Step.cQ7 (ct342 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct487 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct487 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct487 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct487 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct342 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(ct495 b0), rr, (rr.tail (rs .r44 (ct20 b0) (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), (((((((((rr.tail (Step.cQ7 (ct344 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct344 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct344 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((((((rr.tail (Step.cQ11 (ct496 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ11 (ct496 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct496 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct496 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct496 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct496 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct344 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct344 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct344 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), (((((((((rr.tail (Step.cQ7 (ct348 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct348 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct348 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((((((rr.tail (Step.cQ11 (ct501 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ11 (ct501 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct501 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct501 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct501 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct501 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct348 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct348 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct348 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP92 a0 a1 a2 u3 h3
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     cases he2
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     cases he2
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      cases he0
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      cases he0
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      rcases T.zz4.inj he0 with ⟨he2, he3⟩
      clear he0
      revert he2
      subst a0
      intro he2
      clear he2
      exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((((rr.tail (Step.cQ11 (ct460 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct460 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct460 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct460 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct460 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct195 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz4_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 =>
       rcases T.zz4.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       subst b0
       exact ⟨(zz3 ), (((((rr.tail (Step.cQ7 (ct342 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((rr.tail (Step.cQ11 (ct462 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (rs .r2 (ct221 ) (lf 0) (lf 0)))⟩
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 =>
       rcases T.zz4.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst a0
       intro he0
       subst b0
       exact ⟨(zz3 ), (((((rr.tail (Step.cQ7 (ct342 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((((rr.tail (Step.cQ11 (ct506 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct506 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct506 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct506 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct336 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct336 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct221 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      rcases step_zz3_cases h4 with hr
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 => cases hE
       | r12 => cases hE
       | r13 => cases hE
       | r14 => cases hE
       | r15 => cases hE
       | r16 => cases hE
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 => cases hE
       | r22 => cases hE
       | r23 => cases hE
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 => cases hE
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 => cases hE
       | r37 => cases hE
       | r38 => cases hE
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
     ·
      exact vP93 a0 a1 a2 u4 h4
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
theorem peak_43 (a0 a1 a2 : T) {u : T} (h : Step (ct74 a0) u) :
  Join (ct79 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(zz3 ), ((((((rr.tail (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct182 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct182 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   rcases T.zz2.inj he5 with ⟨he6, he7⟩
   clear he5
   clear he7
   have hsize := congrArg sz he6
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst b0
   intro he0 he2 he6
   clear he6
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   rcases T.zz2.inj he7 with ⟨he8, he9⟩
   clear he7
   clear he9
   revert he0 he2 he6
   subst a0
   intro he0 he2 he6
   clear he6
   clear he2
   clear he0
   exact ⟨(ct79 b0), rr, rr⟩
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    cases he3
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    cases he3
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     clear he3
     revert he0
     subst a0
     intro he0
     subst b0
     exact ⟨(zz3 ), ((((((rr.tail (Step.cQ7 (ct333 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct333 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct333 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct465 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct465 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct333 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct333 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     clear he3
     revert he0
     subst a0
     intro he0
     cases he0
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     clear he3
     revert he0
     subst a0
     intro he0
     cases he0
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     rcases T.zz2.inj he1 with ⟨he2, he3⟩
     clear he1
     clear he3
     revert he0
     subst a0
     intro he0
     cases he0
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(zz3 ), ((((((rr.tail (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct182 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((rr.tail (Step.cQ11 (ct280 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct280 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct280 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      subst a0
      exact ⟨(ct77 b0), ((rr.tail (Step.cQ7 (ct423 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 b0 (lf 0) (lf 0))))))).tail (Step.cQ8 (ct42 b0) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 b0 (lf 0) (lf 0)))))), ((rr.tail (Step.cQ12 (ct41 b0) (Step.cQ8 (ct21 b0) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 b0 (lf 0) (lf 0))))))).tail (rs .r41 b0 (lf 0) (lf 0)))⟩
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), ((((((((((rr.tail (Step.cQ7 (ct381 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct381 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct381 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct381 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((((rr.tail (Step.cQ11 (ct511 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct511 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct511 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct511 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct511 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct381 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct381 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      subst a0
      exact ⟨(zz3 ), ((((((((((rr.tail (Step.cQ7 (ct388 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct388 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct388 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct388 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((((((rr.tail (Step.cQ11 (ct515 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ11 (ct515 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct515 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct515 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct388 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct388 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     exact vP94 a0 a1 a2 u3 h3
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    cases he5
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    cases he5
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    cases he5
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    cases he5
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP95 a0 a1 a2 u1 h1
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     cases he3
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     cases he3
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      subst b0
      exact ⟨(zz3 ), ((((((rr.tail (Step.cQ7 (ct333 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct333 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct333 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ11 (ct482 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0))))).tail (rs .r31 (ct14 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct221 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r16 (zz3 ) (lf 0) (lf 0)))⟩
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      cases he0
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      cases he0
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      rcases T.zz2.inj he1 with ⟨he2, he3⟩
      clear he1
      clear he3
      revert he0
      subst a0
      intro he0
      cases he0
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(zz3 ), ((((((rr.tail (Step.cQ7 (ct182 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct182 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((rr.tail (Step.cQ11 (ct281 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (rs .r10 (ct221 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct221 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct221 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(ct77 b0), ((rr.tail (Step.cQ7 (ct423 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 b0 (lf 0) (lf 0))))))).tail (Step.cQ8 (ct42 b0) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 b0 (lf 0) (lf 0)))))), ((rr.tail (Step.cQ11 (ct69 b0) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 b0 (lf 0) (lf 0)))))).tail (rs .r41 b0 (lf 0) (lf 0)))⟩
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), ((((((((((rr.tail (Step.cQ7 (ct381 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct381 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct381 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct381 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((((rr.tail (Step.cQ11 (ct474 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct474 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct474 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct474 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct474 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct474 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct382 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct382 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), ((((((((((rr.tail (Step.cQ7 (ct388 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct388 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (ct388 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ7 (ct388 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((((((rr.tail (Step.cQ11 (ct519 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct519 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct519 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct519 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct519 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct519 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct415 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct415 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r21 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      exact vP96 a0 a1 a2 u4 h4
     ·
      rcases step_zz3_cases h4 with hr
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 => cases hE
       | r12 => cases hE
       | r13 => cases hE
       | r14 => cases hE
       | r15 => cases hE
       | r16 => cases hE
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 => cases hE
       | r22 => cases hE
       | r23 => cases hE
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 => cases hE
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 => cases hE
       | r37 => cases hE
       | r38 => cases hE
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
theorem peak_44 (a0 a1 a2 : T) {u : T} (h : Step (ct76 a0) u) :
  Join (ct80 a0) u := by
 rcases step_zz5_cases h with hr | ⟨u0, rfl, h0⟩ | ⟨u0, rfl, h0⟩
 ·
  rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
  rw [hout]
  cases k with
  | r0 => cases hE
  | r1 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   cases he0
  | r2 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r3 => cases hE
  | r4 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r5 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r6 => cases hE
  | r7 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r8 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r9 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r10 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   revert he0
   subst a0
   intro he0
   clear he0
   exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
  | r11 => cases hE
  | r12 => cases hE
  | r13 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   have hp_b1 := sz_pos b1
   simp only [sz] at hsize
   omega
  | r14 => cases hE
  | r15 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   cases he0
  | r16 => cases hE
  | r17 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b1
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   cases he4
  | r18 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r19 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   cases he1
  | r20 => cases hE
  | r21 => cases hE
  | r22 => cases hE
  | r23 => cases hE
  | r24 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r25 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   cases he6
  | r26 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r27 => cases hE
  | r28 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r29 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   clear he5
   rcases T.zz4.inj he4 with ⟨he6, he7⟩
   clear he4
   rcases T.zz2.inj he7 with ⟨he8, he9⟩
   clear he7
   clear he9
   have hsize := congrArg sz he8
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r30 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r31 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r32 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r33 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r34 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   revert he0
   subst b0
   intro he0
   rcases T.zz2.inj he0 with ⟨he2, he3⟩
   clear he0
   clear he3
   rcases T.zz2.inj he2 with ⟨he4, he5⟩
   clear he2
   cases he5
  | r35 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r36 => cases hE
  | r37 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   cases he3
  | r38 => cases hE
  | r39 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   cases he6
  | r40 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   revert he0 he2
   subst b0
   intro he0 he2
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r41 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   revert he0 he2 he6
   subst b0
   intro he0 he2 he6
   cases he6
  | r42 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz4.inj he6 with ⟨he8, he9⟩
   clear he6
   revert he0 he2 he8
   subst b0
   intro he0 he2 he8
   clear he8
   have hsize := congrArg sz he2
   have hp_a0 := sz_pos a0
   simp only [sz] at hsize
   omega
  | r43 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   cases he7
  | r44 =>
   rcases T.zz5.inj hE with ⟨he0, he1⟩
   clear hE
   rcases T.zz2.inj he1 with ⟨he2, he3⟩
   clear he1
   rcases T.zz2.inj he3 with ⟨he4, he5⟩
   clear he3
   clear he5
   rcases T.zz2.inj he4 with ⟨he6, he7⟩
   clear he4
   clear he7
   rcases T.zz4.inj he6 with ⟨he8, he9⟩
   clear he6
   rcases T.zz2.inj he9 with ⟨he10, he11⟩
   clear he9
   clear he11
   revert he0 he2 he8
   subst a0
   intro he0 he2 he8
   clear he8
   clear he2
   clear he0
   exact ⟨(ct80 b0), rr, rr⟩
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    cases he0
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    clear he1
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    cases he2
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    cases he0
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    rcases T.zz2.inj he0 with ⟨he2, he3⟩
    clear he0
    clear he3
    cases he2
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz4.inj he0 with ⟨he2, he3⟩
     clear he0
     rcases T.zz2.inj he3 with ⟨he4, he5⟩
     clear he3
     clear he5
     revert he2
     subst a0
     intro he2
     clear he2
     exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct363 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct363 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct363 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct363 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz4_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 =>
      rcases T.zz4.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 =>
      rcases T.zz4.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
    ·
     rcases step_zz2_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct363 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct363 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct363 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct363 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r12 => cases hE
      | r13 => cases hE
      | r14 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r15 => cases hE
      | r16 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       clear he1
       subst a0
       exact ⟨(ct78 b0), ((rr.tail (Step.cQ7 (ct523 b0) (Step.cQ10 (zz3 ) (rs .r16 b0 (lf 0) (lf 0))))).tail (Step.cQ8 (ct17 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 b0 (lf 0) (lf 0))))))), ((rr.tail (Step.cQ12 (ct45 b0) (Step.cQ8 (ct21 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 b0 (lf 0) (lf 0)))))))).tail (rs .r42 b0 (lf 0) (lf 0)))⟩
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r22 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r23 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), (((((((((((rr.tail (Step.cQ7 (ct527 ) (Step.cQ10 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct527 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct527 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct527 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((((((rr.tail (Step.cQ11 (ct528 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ11 (ct528 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct528 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct528 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct528 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct528 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct527 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct527 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r37 => cases hE
      | r38 =>
       rcases T.zz2.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       subst a0
       exact ⟨(zz3 ), (((((((((((rr.tail (Step.cQ7 (ct533 ) (Step.cQ10 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct533 ) (Step.cQ10 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct533 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct533 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((((((rr.tail (Step.cQ11 (ct537 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))))).tail (Step.cQ11 (ct537 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct537 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct537 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct537 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct537 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct533 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct533 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      exact vP97 a0 a1 a2 u4 h4
     ·
      rcases step_zz3_cases h4 with hr
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 => cases hE
       | r12 => cases hE
       | r13 => cases hE
       | r14 => cases hE
       | r15 => cases hE
       | r16 => cases hE
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 => cases hE
       | r22 => cases hE
       | r23 => cases hE
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 => cases hE
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 => cases hE
       | r37 => cases hE
       | r38 => cases hE
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
  ·
   rcases step_zz3_cases h1 with hr
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 => cases hE
    | r12 => cases hE
    | r13 => cases hE
    | r14 => cases hE
    | r15 => cases hE
    | r16 => cases hE
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 => cases hE
    | r22 => cases hE
    | r23 => cases hE
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 => cases hE
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 => cases hE
    | r37 => cases hE
    | r38 => cases hE
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
 ·
  rcases step_zz2_cases h0 with hr | ⟨u1, rfl, h1⟩ | ⟨u1, rfl, h1⟩
  ·
   rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
   rw [hout]
   cases k with
   | r0 => cases hE
   | r1 => cases hE
   | r2 => cases hE
   | r3 => cases hE
   | r4 => cases hE
   | r5 => cases hE
   | r6 => cases hE
   | r7 => cases hE
   | r8 => cases hE
   | r9 => cases hE
   | r10 => cases hE
   | r11 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r12 => cases hE
   | r13 => cases hE
   | r14 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r15 => cases hE
   | r16 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    cases he1
   | r17 => cases hE
   | r18 => cases hE
   | r19 => cases hE
   | r20 => cases hE
   | r21 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    cases he4
   | r22 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r23 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r24 => cases hE
   | r25 => cases hE
   | r26 => cases hE
   | r27 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    cases he4
   | r28 => cases hE
   | r29 => cases hE
   | r30 => cases hE
   | r31 => cases hE
   | r32 => cases hE
   | r33 => cases hE
   | r34 => cases hE
   | r35 => cases hE
   | r36 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    rcases T.zz2.inj he1 with ⟨he2, he3⟩
    clear he1
    clear he3
    rcases T.zz2.inj he2 with ⟨he4, he5⟩
    clear he2
    clear he5
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r37 => cases hE
   | r38 =>
    rcases T.zz2.inj hE with ⟨he0, he1⟩
    clear hE
    revert he0
    subst b0
    intro he0
    have hsize := congrArg sz he0
    have hp_a0 := sz_pos a0
    simp only [sz] at hsize
    omega
   | r39 => cases hE
   | r40 => cases hE
   | r41 => cases hE
   | r42 => cases hE
   | r43 => cases hE
   | r44 => cases hE
  ·
   exact vP98 a0 a1 a2 u1 h1
  ·
   rcases step_zz2_cases h1 with hr | ⟨u2, rfl, h2⟩ | ⟨u2, rfl, h2⟩
   ·
    rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
    rw [hout]
    cases k with
    | r0 => cases hE
    | r1 => cases hE
    | r2 => cases hE
    | r3 => cases hE
    | r4 => cases hE
    | r5 => cases hE
    | r6 => cases hE
    | r7 => cases hE
    | r8 => cases hE
    | r9 => cases hE
    | r10 => cases hE
    | r11 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     cases he0
    | r12 => cases hE
    | r13 => cases hE
    | r14 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r15 => cases hE
    | r16 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     clear he1
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     cases he2
    | r17 => cases hE
    | r18 => cases hE
    | r19 => cases hE
    | r20 => cases hE
    | r21 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r22 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r23 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     cases he0
    | r24 => cases hE
    | r25 => cases hE
    | r26 => cases hE
    | r27 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r28 => cases hE
    | r29 => cases hE
    | r30 => cases hE
    | r31 => cases hE
    | r32 => cases hE
    | r33 => cases hE
    | r34 => cases hE
    | r35 => cases hE
    | r36 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     cases he1
    | r37 => cases hE
    | r38 =>
     rcases T.zz2.inj hE with ⟨he0, he1⟩
     clear hE
     revert he0
     subst b0
     intro he0
     rcases T.zz2.inj he0 with ⟨he2, he3⟩
     clear he0
     clear he3
     cases he2
    | r39 => cases hE
    | r40 => cases hE
    | r41 => cases hE
    | r42 => cases hE
    | r43 => cases hE
    | r44 => cases hE
   ·
    rcases step_zz2_cases h2 with hr | ⟨u3, rfl, h3⟩ | ⟨u3, rfl, h3⟩
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      cases he0
     | r12 => cases hE
     | r13 => cases hE
     | r14 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r15 => cases hE
     | r16 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      clear he1
      cases he0
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r22 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r23 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      rcases T.zz4.inj he0 with ⟨he2, he3⟩
      clear he0
      rcases T.zz2.inj he3 with ⟨he4, he5⟩
      clear he3
      clear he5
      revert he2
      subst a0
      intro he2
      clear he2
      exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), (((((((((rr.tail (Step.cQ11 (ct364 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (rs .r10 (ct195 ) (lf 0) (lf 0))).tail (Step.cQ7 (ct195 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ7 (ct195 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct195 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      cases he1
     | r37 => cases hE
     | r38 =>
      rcases T.zz2.inj hE with ⟨he0, he1⟩
      clear hE
      revert he0
      subst b0
      intro he0
      cases he0
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
    ·
     rcases step_zz4_cases h3 with hr | ⟨u4, rfl, h4⟩ | ⟨u4, rfl, h4⟩
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 =>
       rcases T.zz4.inj hE with ⟨he0, he1⟩
       clear hE
       cases he1
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 =>
       rcases T.zz4.inj hE with ⟨he0, he1⟩
       clear hE
       revert he0
       subst b0
       intro he0
       cases he0
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
     ·
      rcases step_zz3_cases h4 with hr
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 => cases hE
       | r12 => cases hE
       | r13 => cases hE
       | r14 => cases hE
       | r15 => cases hE
       | r16 => cases hE
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 => cases hE
       | r22 => cases hE
       | r23 => cases hE
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 => cases hE
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 => cases hE
       | r37 => cases hE
       | r38 => cases hE
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
     ·
      rcases step_zz2_cases h4 with hr | ⟨u5, rfl, h5⟩ | ⟨u5, rfl, h5⟩
      ·
       rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
       rw [hout]
       cases k with
       | r0 => cases hE
       | r1 => cases hE
       | r2 => cases hE
       | r3 => cases hE
       | r4 => cases hE
       | r5 => cases hE
       | r6 => cases hE
       | r7 => cases hE
       | r8 => cases hE
       | r9 => cases hE
       | r10 => cases hE
       | r11 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        clear he1
        subst a0
        exact ⟨(zz3 ), (((((((rr.tail (Step.cQ7 (ct223 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct223 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((rr.tail (Step.cQ11 (ct488 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct488 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct488 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct488 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct488 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
       | r12 => cases hE
       | r13 => cases hE
       | r14 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r15 => cases hE
       | r16 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        clear he1
        subst a0
        exact ⟨(ct78 b0), ((rr.tail (Step.cQ7 (ct523 b0) (Step.cQ10 (zz3 ) (rs .r16 b0 (lf 0) (lf 0))))).tail (Step.cQ8 (ct17 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 b0 (lf 0) (lf 0))))))), ((rr.tail (Step.cQ11 (ct71 b0) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 b0 (lf 0) (lf 0))))))).tail (rs .r42 b0 (lf 0) (lf 0)))⟩
       | r17 => cases hE
       | r18 => cases hE
       | r19 => cases hE
       | r20 => cases hE
       | r21 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r22 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r23 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        revert he0
        subst b0
        intro he0
        subst a0
        exact ⟨(zz3 ), (((((((((((rr.tail (Step.cQ7 (ct527 ) (Step.cQ10 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct527 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct527 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct527 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((((((rr.tail (Step.cQ11 (ct497 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct497 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ11 (ct497 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct497 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))).tail (Step.cQ11 (ct497 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct497 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r15 (ct497 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct344 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct344 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
       | r24 => cases hE
       | r25 => cases hE
       | r26 => cases hE
       | r27 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r28 => cases hE
       | r29 => cases hE
       | r30 => cases hE
       | r31 => cases hE
       | r32 => cases hE
       | r33 => cases hE
       | r34 => cases hE
       | r35 => cases hE
       | r36 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        cases he1
       | r37 => cases hE
       | r38 =>
        rcases T.zz2.inj hE with ⟨he0, he1⟩
        clear hE
        revert he0
        subst b0
        intro he0
        subst a0
        exact ⟨(zz3 ), (((((((((((rr.tail (Step.cQ7 (ct533 ) (Step.cQ10 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))).tail (Step.cQ7 (ct533 ) (Step.cQ10 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (ct533 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (ct533 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ8 (zz3 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ8 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0))), ((((((((((((((((rr.tail (Step.cQ11 (ct541 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (ct181 ) (lf 0) (lf 0))))))).tail (Step.cQ11 (ct541 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ11 (ct541 ) (Step.cQ7 (zz3 ) (rs .r23 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ11 (ct541 ) (rs .r23 (zz3 ) (lf 0) (lf 0)))).tail (Step.cQ11 (ct541 ) (Step.cQ10 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ11 (ct541 ) (rs .r6 (zz3 ) (lf 0) (lf 0)))).tail (rs .r15 (ct541 ) (lf 0) (lf 0))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct348 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ7 (ct348 ) (rs .r16 (zz3 ) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ10 (zz3 ) (rs .r16 (zz3 ) (lf 0) (lf 0)))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (Step.cQ7 (zz3 ) (rs .r6 (zz3 ) (lf 0) (lf 0))))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))))).tail (Step.cQ7 (zz3 ) (Step.cQ8 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0))))).tail (Step.cQ7 (zz3 ) (rs .r11 (lf 0) (lf 0) (lf 0)))).tail (rs .r11 (lf 0) (lf 0) (lf 0)))⟩
       | r39 => cases hE
       | r40 => cases hE
       | r41 => cases hE
       | r42 => cases hE
       | r43 => cases hE
       | r44 => cases hE
      ·
       exact vP99 a0 a1 a2 u5 h5
      ·
       rcases step_zz3_cases h5 with hr
       ·
        rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
        rw [hout]
        cases k with
        | r0 => cases hE
        | r1 => cases hE
        | r2 => cases hE
        | r3 => cases hE
        | r4 => cases hE
        | r5 => cases hE
        | r6 => cases hE
        | r7 => cases hE
        | r8 => cases hE
        | r9 => cases hE
        | r10 => cases hE
        | r11 => cases hE
        | r12 => cases hE
        | r13 => cases hE
        | r14 => cases hE
        | r15 => cases hE
        | r16 => cases hE
        | r17 => cases hE
        | r18 => cases hE
        | r19 => cases hE
        | r20 => cases hE
        | r21 => cases hE
        | r22 => cases hE
        | r23 => cases hE
        | r24 => cases hE
        | r25 => cases hE
        | r26 => cases hE
        | r27 => cases hE
        | r28 => cases hE
        | r29 => cases hE
        | r30 => cases hE
        | r31 => cases hE
        | r32 => cases hE
        | r33 => cases hE
        | r34 => cases hE
        | r35 => cases hE
        | r36 => cases hE
        | r37 => cases hE
        | r38 => cases hE
        | r39 => cases hE
        | r40 => cases hE
        | r41 => cases hE
        | r42 => cases hE
        | r43 => cases hE
        | r44 => cases hE
    ·
     rcases step_zz3_cases h3 with hr
     ·
      rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
      rw [hout]
      cases k with
      | r0 => cases hE
      | r1 => cases hE
      | r2 => cases hE
      | r3 => cases hE
      | r4 => cases hE
      | r5 => cases hE
      | r6 => cases hE
      | r7 => cases hE
      | r8 => cases hE
      | r9 => cases hE
      | r10 => cases hE
      | r11 => cases hE
      | r12 => cases hE
      | r13 => cases hE
      | r14 => cases hE
      | r15 => cases hE
      | r16 => cases hE
      | r17 => cases hE
      | r18 => cases hE
      | r19 => cases hE
      | r20 => cases hE
      | r21 => cases hE
      | r22 => cases hE
      | r23 => cases hE
      | r24 => cases hE
      | r25 => cases hE
      | r26 => cases hE
      | r27 => cases hE
      | r28 => cases hE
      | r29 => cases hE
      | r30 => cases hE
      | r31 => cases hE
      | r32 => cases hE
      | r33 => cases hE
      | r34 => cases hE
      | r35 => cases hE
      | r36 => cases hE
      | r37 => cases hE
      | r38 => cases hE
      | r39 => cases hE
      | r40 => cases hE
      | r41 => cases hE
      | r42 => cases hE
      | r43 => cases hE
      | r44 => cases hE
   ·
    rcases step_zz3_cases h2 with hr
    ·
     rcases hr with ⟨k, b0, b1, b2, hE, hout⟩
     rw [hout]
     cases k with
     | r0 => cases hE
     | r1 => cases hE
     | r2 => cases hE
     | r3 => cases hE
     | r4 => cases hE
     | r5 => cases hE
     | r6 => cases hE
     | r7 => cases hE
     | r8 => cases hE
     | r9 => cases hE
     | r10 => cases hE
     | r11 => cases hE
     | r12 => cases hE
     | r13 => cases hE
     | r14 => cases hE
     | r15 => cases hE
     | r16 => cases hE
     | r17 => cases hE
     | r18 => cases hE
     | r19 => cases hE
     | r20 => cases hE
     | r21 => cases hE
     | r22 => cases hE
     | r23 => cases hE
     | r24 => cases hE
     | r25 => cases hE
     | r26 => cases hE
     | r27 => cases hE
     | r28 => cases hE
     | r29 => cases hE
     | r30 => cases hE
     | r31 => cases hE
     | r32 => cases hE
     | r33 => cases hE
     | r34 => cases hE
     | r35 => cases hE
     | r36 => cases hE
     | r37 => cases hE
     | r38 => cases hE
     | r39 => cases hE
     | r40 => cases hE
     | r41 => cases hE
     | r42 => cases hE
     | r43 => cases hE
     | r44 => cases hE
theorem root_peak {a b c : T} (h : Root a b) (hs : Step a c) : Join b c := by
 rcases h with ⟨k, v0, v1, v2, hl, hr⟩
 rw [hl] at hs
 rw [hr]
 cases k with
 | r0 => exact peak_0 v0 v1 v2 hs
 | r1 => exact peak_1 v0 v1 v2 hs
 | r2 => exact peak_2 v0 v1 v2 hs
 | r3 => exact peak_3 v0 v1 v2 hs
 | r4 => exact peak_4 v0 v1 v2 hs
 | r5 => exact peak_5 v0 v1 v2 hs
 | r6 => exact peak_6 v0 v1 v2 hs
 | r7 => exact peak_7 v0 v1 v2 hs
 | r8 => exact peak_8 v0 v1 v2 hs
 | r9 => exact peak_9 v0 v1 v2 hs
 | r10 => exact peak_10 v0 v1 v2 hs
 | r11 => exact peak_11 v0 v1 v2 hs
 | r12 => exact peak_12 v0 v1 v2 hs
 | r13 => exact peak_13 v0 v1 v2 hs
 | r14 => exact peak_14 v0 v1 v2 hs
 | r15 => exact peak_15 v0 v1 v2 hs
 | r16 => exact peak_16 v0 v1 v2 hs
 | r17 => exact peak_17 v0 v1 v2 hs
 | r18 => exact peak_18 v0 v1 v2 hs
 | r19 => exact peak_19 v0 v1 v2 hs
 | r20 => exact peak_20 v0 v1 v2 hs
 | r21 => exact peak_21 v0 v1 v2 hs
 | r22 => exact peak_22 v0 v1 v2 hs
 | r23 => exact peak_23 v0 v1 v2 hs
 | r24 => exact peak_24 v0 v1 v2 hs
 | r25 => exact peak_25 v0 v1 v2 hs
 | r26 => exact peak_26 v0 v1 v2 hs
 | r27 => exact peak_27 v0 v1 v2 hs
 | r28 => exact peak_28 v0 v1 v2 hs
 | r29 => exact peak_29 v0 v1 v2 hs
 | r30 => exact peak_30 v0 v1 v2 hs
 | r31 => exact peak_31 v0 v1 v2 hs
 | r32 => exact peak_32 v0 v1 v2 hs
 | r33 => exact peak_33 v0 v1 v2 hs
 | r34 => exact peak_34 v0 v1 v2 hs
 | r35 => exact peak_35 v0 v1 v2 hs
 | r36 => exact peak_36 v0 v1 v2 hs
 | r37 => exact peak_37 v0 v1 v2 hs
 | r38 => exact peak_38 v0 v1 v2 hs
 | r39 => exact peak_39 v0 v1 v2 hs
 | r40 => exact peak_40 v0 v1 v2 hs
 | r41 => exact peak_41 v0 v1 v2 hs
 | r42 => exact peak_42 v0 v1 v2 hs
 | r43 => exact peak_43 v0 v1 v2 hs
 | r44 => exact peak_44 v0 v1 v2 hs
theorem local_confluence {a b c : T} (h : Step a b) (hs : Step a c) : Join b c := by
 induction h generalizing c with
 | root h => exact root_peak h hs
 | @cQ0 a b x2 h ih =>
  rcases step_op_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ0 x2 h))
  ·
   exact join_op_1 x2 (ih hv)
  ·
   exact ⟨(op b v), .single (Step.cQ1 b hv), .single (Step.cQ0 v h)⟩
 | @cQ1 a b x1 h ih =>
  rcases step_op_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ1 x1 h))
  ·
   exact ⟨(op v b), .single (Step.cQ0 b hv), .single (Step.cQ1 v h)⟩
  ·
   exact join_op_2 x1 (ih hv)
 | @cQ2 a b x2 h ih =>
  rcases step_zz0_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ2 x2 h))
  ·
   exact join_zz0_1 x2 (ih hv)
  ·
   exact ⟨(zz0 b v), .single (Step.cQ3 b hv), .single (Step.cQ2 v h)⟩
 | @cQ3 a b x1 h ih =>
  rcases step_zz0_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ3 x1 h))
  ·
   exact ⟨(zz0 v b), .single (Step.cQ2 b hv), .single (Step.cQ3 v h)⟩
  ·
   exact join_zz0_2 x1 (ih hv)
 | @cQ4 a b x2 x3 h ih =>
  rcases step_zz1_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ4 x2 x3 h))
  ·
   exact join_zz1_1 x2 x3 (ih hv)
  ·
   exact ⟨(zz1 b v x3), .single (Step.cQ5 b x3 hv), .single (Step.cQ4 v x3 h)⟩
  ·
   exact ⟨(zz1 b x2 v), .single (Step.cQ6 b x2 hv), .single (Step.cQ4 x2 v h)⟩
 | @cQ5 a b x1 x3 h ih =>
  rcases step_zz1_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ5 x1 x3 h))
  ·
   exact ⟨(zz1 v b x3), .single (Step.cQ4 b x3 hv), .single (Step.cQ5 v x3 h)⟩
  ·
   exact join_zz1_2 x1 x3 (ih hv)
  ·
   exact ⟨(zz1 x1 b v), .single (Step.cQ6 x1 b hv), .single (Step.cQ5 x1 v h)⟩
 | @cQ6 a b x1 x2 h ih =>
  rcases step_zz1_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ6 x1 x2 h))
  ·
   exact ⟨(zz1 v x2 b), .single (Step.cQ4 x2 b hv), .single (Step.cQ6 v x2 h)⟩
  ·
   exact ⟨(zz1 x1 v b), .single (Step.cQ5 x1 b hv), .single (Step.cQ6 x1 v h)⟩
  ·
   exact join_zz1_3 x1 x2 (ih hv)
 | @cQ7 a b x2 h ih =>
  rcases step_zz2_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ7 x2 h))
  ·
   exact join_zz2_1 x2 (ih hv)
  ·
   exact ⟨(zz2 b v), .single (Step.cQ8 b hv), .single (Step.cQ7 v h)⟩
 | @cQ8 a b x1 h ih =>
  rcases step_zz2_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ8 x1 h))
  ·
   exact ⟨(zz2 v b), .single (Step.cQ7 b hv), .single (Step.cQ8 v h)⟩
  ·
   exact join_zz2_2 x1 (ih hv)
 | @cQ9 a b x2 h ih =>
  rcases step_zz4_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ9 x2 h))
  ·
   exact join_zz4_1 x2 (ih hv)
  ·
   exact ⟨(zz4 b v), .single (Step.cQ10 b hv), .single (Step.cQ9 v h)⟩
 | @cQ10 a b x1 h ih =>
  rcases step_zz4_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ10 x1 h))
  ·
   exact ⟨(zz4 v b), .single (Step.cQ9 b hv), .single (Step.cQ10 v h)⟩
  ·
   exact join_zz4_2 x1 (ih hv)
 | @cQ11 a b x2 h ih =>
  rcases step_zz5_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ11 x2 h))
  ·
   exact join_zz5_1 x2 (ih hv)
  ·
   exact ⟨(zz5 b v), .single (Step.cQ12 b hv), .single (Step.cQ11 v h)⟩
 | @cQ12 a b x1 h ih =>
  rcases step_zz5_cases hs with hr | ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
  ·
   exact join_symm (root_peak hr (Step.cQ12 x1 h))
  ·
   exact ⟨(zz5 v b), .single (Step.cQ11 b hv), .single (Step.cQ12 v h)⟩
  ·
   exact join_zz5_2 x1 (ih hv)

theorem confluence (a : T) : ∀ {b c : T}, Reach a b → Reach a c → Join b c := by
 induction a using (measure sz).wf.induction with
 | h a ih =>
  intro b c hab hac
  rcases hab.cases_head with rfl | ⟨p, hap, hpb⟩
  ·
   exact ⟨c, hac, .refl⟩
  rcases hac.cases_head with rfl | ⟨q, haq, hqc⟩
  ·
   exact ⟨b, .refl, hab⟩
  rcases local_confluence hap haq with ⟨d, hpd, hqd⟩
  rcases ih p (step_decrease hap) hpb hpd with ⟨e, hbe, hde⟩
  rcases ih q (step_decrease haq) hqc hqd with ⟨f, hcf, hdf⟩
  have hd : sz d < sz a := Nat.lt_of_le_of_lt (reach_size hpd) (step_decrease hap)
  rcases ih d hd hde hdf with ⟨g, heg, hfg⟩
  exact ⟨g, hbe.trans heg, hcf.trans hfg⟩

theorem join_equivalence : Equivalence Join := by
 refine ⟨fun a => ⟨a, .refl, .refl⟩, fun h => join_symm h, ?_⟩
 intro a b c hab hbc
 rcases hab with ⟨x, hax, hbx⟩
 rcases hbc with ⟨y, hby, hcy⟩
 rcases confluence b hbx hby with ⟨z, hxz, hyz⟩
 exact ⟨z, hax.trans hxz, hcy.trans hyz⟩

def treeSetoid : Setoid T := ⟨Join, join_equivalence⟩
def Carrier := Quotient treeSetoid
def project : T → Carrier := Quotient.mk treeSetoid

def product : Carrier → Carrier → Carrier :=
 Quotient.lift₂ (fun a b => project (op a b)) (by
  intro a b c d hac hbd
  apply Quotient.sound
  exact join_equivalence.trans (join_op_1 b hac) (join_op_2 c hbd))

instance : Magma Carrier := ⟨product⟩
theorem project_op (a b : T) : project (op a b) = project a ◇ project b := rfl
theorem project_reach {a b : T} (h : Reach a b) : project a = project b :=
 Quotient.sound ⟨b, h, .refl⟩

theorem source : BaseEquationLHS Carrier := by
 intro q0 q1 q2
 refine Quotient.inductionOn q0 ?_
 intro a0
 refine Quotient.inductionOn q1 ?_
 intro a1
 refine Quotient.inductionOn q2 ?_
 intro a2
 change project a0 = project (ct545 a1 a0 a2)
 exact (project_reach rr).trans (project_reach ((((((((((((((((((((rr.tail (rs .r3 a1 (ct544 a1 a0 a2) (lf 0))).tail (Step.cQ11 (ct546 a1 a0 a2) (rs .r3 (ct543 a1 a0) (op a2 a2) (lf 0)))).tail (Step.cQ11 (ct546 a1 a0 a2) (Step.cQ11 (ct547 a1 a0 a2) (rs .r3 a2 a2 (lf 0))))).tail (Step.cQ11 (ct546 a1 a0 a2) (Step.cQ11 (ct547 a1 a0 a2) (rs .r2 a2 (lf 0) (lf 0))))).tail (Step.cQ11 (ct546 a1 a0 a2) (rs .r15 (ct547 a1 a0 a2) (lf 0) (lf 0)))).tail (Step.cQ11 (ct546 a1 a0 a2) (Step.cQ7 (zz3 ) (Step.cQ7 (op a2 a2) (rs .r3 (op a1 a0) a0 (lf 0)))))).tail (Step.cQ11 (ct546 a1 a0 a2) (Step.cQ7 (zz3 ) (Step.cQ7 (op a2 a2) (Step.cQ12 a0 (Step.cQ7 a0 (rs .r3 a1 a0 (lf 0)))))))).tail (Step.cQ11 (ct546 a1 a0 a2) (Step.cQ7 (zz3 ) (Step.cQ7 (op a2 a2) (rs .r13 a0 a1 (lf 0)))))).tail (Step.cQ11 (ct546 a1 a0 a2) (Step.cQ7 (zz3 ) (Step.cQ8 (zz2 a1 a0) (rs .r3 a2 a2 (lf 0)))))).tail (Step.cQ11 (ct546 a1 a0 a2) (Step.cQ7 (zz3 ) (Step.cQ8 (zz2 a1 a0) (rs .r2 a2 (lf 0) (lf 0)))))).tail (Step.cQ12 (ct24 a1 a0) (Step.cQ8 a1 (rs .r3 (ct543 a1 a0) (op a2 a2) (lf 0))))).tail (Step.cQ12 (ct24 a1 a0) (Step.cQ8 a1 (Step.cQ11 (ct547 a1 a0 a2) (rs .r3 a2 a2 (lf 0)))))).tail (Step.cQ12 (ct24 a1 a0) (Step.cQ8 a1 (Step.cQ11 (ct547 a1 a0 a2) (rs .r2 a2 (lf 0) (lf 0)))))).tail (Step.cQ12 (ct24 a1 a0) (Step.cQ8 a1 (rs .r15 (ct547 a1 a0 a2) (lf 0) (lf 0))))).tail (Step.cQ12 (ct24 a1 a0) (Step.cQ8 a1 (Step.cQ7 (zz3 ) (Step.cQ7 (op a2 a2) (rs .r3 (op a1 a0) a0 (lf 0))))))).tail (Step.cQ12 (ct24 a1 a0) (Step.cQ8 a1 (Step.cQ7 (zz3 ) (Step.cQ7 (op a2 a2) (Step.cQ12 a0 (Step.cQ7 a0 (rs .r3 a1 a0 (lf 0))))))))).tail (Step.cQ12 (ct24 a1 a0) (Step.cQ8 a1 (Step.cQ7 (zz3 ) (Step.cQ7 (op a2 a2) (rs .r13 a0 a1 (lf 0))))))).tail (Step.cQ12 (ct24 a1 a0) (Step.cQ8 a1 (Step.cQ7 (zz3 ) (Step.cQ8 (zz2 a1 a0) (rs .r3 a2 a2 (lf 0))))))).tail (Step.cQ12 (ct24 a1 a0) (Step.cQ8 a1 (Step.cQ7 (zz3 ) (Step.cQ8 (zz2 a1 a0) (rs .r2 a2 (lf 0) (lf 0))))))).tail (rs .r25 a1 a0 (lf 0)))).symm

theorem leaf_irreducible (n : Nat) {u : T} (h : Step (lf n) u) : False := by
 have hd := step_decrease h
 have hu := sz_pos u
 simp only [sz] at hd
 omega

theorem leaf_reach (n : Nat) {u : T} (h : Reach (lf n) u) : lf n = u := by
 rcases h.cases_head with he | ⟨v, hv, _⟩
 ·
  exact he
 ·
  exact False.elim (leaf_irreducible n hv)

theorem generators_injective : Function.Injective (fun n => project (lf n)) := by
 intro n m he
 rcases Quotient.exact he with ⟨u, hn, hm⟩
 exact T.lf.inj ((leaf_reach n hn).trans (leaf_reach m hm).symm)

theorem nontrivial : ¬ ∀ x y : Carrier, x = y := by
 intro h
 have he : (0 : Nat) = 1 := generators_injective (h (project (lf 0)) (project (lf 1)))
 omega

def result : BaseGoal := ⟨Carrier, inferInstance, source, nontrivial⟩
end base_model
def base_certificate : BaseGoal := base_model.result
def result : Goal := by
  rcases base_certificate with ⟨G, originalMagma, hs, ht⟩
  let oppositeMagma : Magma G := ⟨fun a b => @Magma.op G originalMagma b a⟩
  refine ⟨G, oppositeMagma, ?_, ?_⟩
  · intro «x» «y» «z»
    change «x» = (@Magma.op G originalMagma «z» (@Magma.op G originalMagma (@Magma.op G originalMagma (@Magma.op G originalMagma «z» «x») «x») (@Magma.op G originalMagma «y» «y»)))
    exact hs «x» «z» «y»
  · exact ht
end submission
def submission : Goal := submission.result
#print axioms submission
