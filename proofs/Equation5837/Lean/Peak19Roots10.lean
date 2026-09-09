import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root210 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r q1 q0) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root211 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d q0 q1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root212 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.c q0 q1 q2) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root213 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) q1 x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root214 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r q0 (T.m q1 q0)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root215 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.r q0 q1) q0) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root216 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root217 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.c q0 q1 q2) q1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root218 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) q0 x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root219 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d (T.c q0 q0 q1) q0) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root220 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r q0 (T.c q0 q0 q1)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root221 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d (T.d q0 q1) q2) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root222 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root223 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root224 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) q0 x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root225 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root226 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root227 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root228 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root229 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root230 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837
