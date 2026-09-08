import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root168 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r q1 q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root169 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d q0 q1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root170 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.c q0 q1 q2) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root171 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c q1 (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root172 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r q0 (T.m q1 q0)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root173 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.r q0 q1) q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root174 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root175 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.c q0 q1 q2) q1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root176 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c q0 (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root177 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d (T.c q0 q0 q1) q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root178 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root179 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d (T.d q0 q1) q2) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root180 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root181 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root182 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c q0 (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root183 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root184 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root185 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root186 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root187 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root188 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837
