import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root189 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r q1 q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root190 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d q0 q1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root191 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.c q0 q1 q2) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root192 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) q1 x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root193 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r q0 (T.m q1 q0)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root194 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.r q0 q1) q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root195 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.c (T.c q2 q0 q1) q0 q1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root196 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.c q0 q1 q2) q1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root197 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) q0 x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root198 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d (T.c q0 q0 q1) q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root199 {q0 q1 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r q0 (T.c q0 q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root200 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d (T.d q0 q1) q2) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root201 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root202 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.c (T.d q0 q1) (T.d q0 q1) q2) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root203 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) q0 x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root204 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root205 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root206 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root207 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root208 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

theorem peak20_root209 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) := by
  cases he

end submission.Austin5837
