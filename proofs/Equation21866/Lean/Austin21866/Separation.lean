import Austin21866.Basic
set_option autoImplicit false
set_option Elab.async false

namespace submission.Austin21866
open T

theorem row_ne {a b : T} (h : Row a b) : a ≠ b := by
  induction h with
  | direct a c => intro he; cases he
  | back x y z => intro he; cases he
  | cross x y z hr ih =>
    intro he
    exact ih (T.p.inj he).2
  | lift x y z hr hs ih ih' => intro he; cases he

theorem row_irrefl (a : T) : ¬ Row a a := fun h => row_ne h rfl

theorem row_not_right (a b : T) : ¬ Row (p a b) b := by
  intro h
  cases h

theorem row_not_right3 (a b c d : T) : ¬ Row (p a (p b (p c d))) c := by
  intro h
  cases h

theorem op_row_shape {a b : T} (h : Row a b) :
    ∃ c, op a b = p a c ∧ Row a c := by
  cases h
  · rename_i c
    refine ⟨p a c, ?_, Row.direct a c⟩
    exact op_miss a a c (fun hh => row_irrefl a hh.2)
  · rename_i x y
    refine ⟨b, ?_, Row.back x y b⟩
    cases b with
    | e => rfl
    | k t => rfl
    | p c d =>
      exact op_miss (p x (p y (p c d))) c d (fun hh => row_not_right3 x y c d hh.2)
  · rename_i x y z hr
    refine ⟨p y z, ?_, Row.cross x y z hr⟩
    exact op_miss _ y z (fun hh => row_not_right x y hh.2)
  · rename_i c v hr hs
    refine ⟨c, ?_, hr⟩
    exact op_hit a (p a c) v hs (Row.direct a c)

end submission.Austin21866
