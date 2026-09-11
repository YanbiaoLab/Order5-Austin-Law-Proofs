import Austin21866.Model
set_option Elab.async false

namespace submission.Austin21866

theorem equation24200 (x y z : T) :
    x = (dualOp (dualOp (dualOp y x) x) (dualOp (dualOp x z) z)) := equation21714 x z y

theorem equation24199 (x y z : T) :
    x = (dualOp (dualOp (dualOp y x) x) (dualOp (dualOp x z) y)) := equation21864 x y z

theorem equation24197 (x y z : T) :
    x = (dualOp (dualOp (dualOp y x) x) (dualOp (dualOp x y) z)) := equation21865 x z y

theorem equation24201 (x y z w : T) :
    x = (dualOp (dualOp (dualOp y x) x) (dualOp (dualOp x z) w)) := equation21866 x w z y

end submission.Austin21866
