import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root147 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r q1 q0) x0 x1)) := by
  cases he

theorem peak19_root148 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d q0 q1) x0 x1)) := by
  cases he

theorem peak19_root149 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.c q0 q1 q2) x0 x1)) := by
  cases he

theorem peak19_root150 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c q1 x0 x1)) := by
  cases he

theorem peak19_root151 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r q0 (T.m q1 q0)) x0 x1)) := by
  cases he

theorem peak19_root152 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.r q0 q1) q0) x0 x1)) := by
  cases he

theorem peak19_root153 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.c (T.c q2 q0 q1) q0 q1) x0 x1)) := by
  cases he

theorem peak19_root154 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.c q0 q1 q2) q1) x0 x1)) := by
  cases he

theorem peak19_root155 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c q0 x0 x1)) := by
  cases he

theorem peak19_root156 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c q0 q0 q1) q0) x0 x1)) := by
  cases he

theorem peak19_root157 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r q0 (T.c q0 q0 q1)) x0 x1)) := by
  cases he

theorem peak19_root158 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d q0 q1) q2) x0 x1)) := by
  cases he

theorem peak19_root159 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) x0 x1)) := by
  cases he

theorem peak19_root160 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) x0 x1)) := by
  cases he

theorem peak19_root161 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c q0 x0 x1)) := by
  cases he

theorem peak19_root162 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) x0 x1)) := by
  cases he

theorem peak19_root163 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x0 x1)) := by
  cases he

theorem peak19_root164 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) x0 x1)) := by
  cases he

theorem peak19_root165 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) x0 x1)) := by
  cases he

theorem peak19_root166 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) x0 x1)) := by
  cases he

theorem peak19_root167 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) x0 x1)) := by
  cases he

end submission.Austin5837
