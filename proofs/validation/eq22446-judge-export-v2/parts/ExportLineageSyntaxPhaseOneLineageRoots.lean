prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxCommonRootExclusion
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

mutual
theorem image_small_phase_one_common_root {p q : T} (h : Image p q) :
    ∀ u v, p = S (P u v) → nodes q < nodes p →
      ∃ r, Lineage r u ∧ Lineage r (S (S q)) :=
  match h with
  | .square p => by
      intro u v hp hs
      simp only [nodes_S] at hs
      exact False.elim (Nat.lt_irrefl _ hs)
  | .literal p z => by
      intro u v hp hs
      exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt
        (Nat.lt_trans (pair_left .zero _ _) (pair_left .zero _ _))) hs)
  | .transport hc hi => by
      intro u v hp hs
      obtain ⟨r,hr,hl⟩ := column_small_phase_one_common_root hc u v hp
        (Nat.lt_trans (pair_left .zero _ _) hs)
      exact ⟨r,hr,.step hl hi⟩
  | .inverseFollowup p => by intro u v hp hs; cases hp
  | .returnFollowup hi => by intro u v hp hs; cases hp
  | .cycleFollowup hs hi hj => by intro u v hp ht; cases hp
theorem column_small_phase_one_common_root {p a : T} (h : Column p a) :
    ∀ u v, a = S (P u v) → nodes p < nodes a →
      ∃ r, Lineage r u ∧ Lineage r p :=
  match h with
  | .ancestry hl => by
      intro u v ha hs
      cases hl with
      | refl =>
          simp only [nodes_S] at hs
          exact False.elim (Nat.lt_irrefl _ hs)
      | @step p x y hl hi =>
          simp only [cube] at ha
          have he := S_injective ha
          rw [(T.p.inj he).2.1] at hl
          exact ⟨p,hl,.refl p⟩
  | .literal p y => by intro u v ha hs; cases ha
  | .inverseImage hi => by
      intro u v ha hs
      obtain ⟨r,hr,hp⟩ := image_small_phase_one_common_root hi u v ha (by simpa only [nodes_S] using hs)
      exact ⟨r,hr,by simpa only [cube] using hp⟩
end

end submission.Equation22446Lineage
