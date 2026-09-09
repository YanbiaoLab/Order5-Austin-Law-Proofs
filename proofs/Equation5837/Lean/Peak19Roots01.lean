import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root21 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r q1 q0) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root22 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root23 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.c q0 q1 q2) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root24 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m q1 (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root25 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r q0 (T.m q1 q0)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root26 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.r q0 q1) q0) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root27 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.c (T.c q2 q0 q1) q0 q1) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root28 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.c q0 q1 q2) q1) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root29 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m q0 (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root30 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.c q0 q0 q1) q0) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root31 {q0 q1 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r q0 (T.c q0 q0 q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root32 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d q0 q1) q2) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root33 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root34 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root35 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m q0 (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root36 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root37 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root38 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root39 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root40 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root41 {q0 q1 q2 x0 x1 x2 : T} (he : (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837
