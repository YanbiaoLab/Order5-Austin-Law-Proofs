import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root126 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r q1 q0)) := by
  cases he

theorem peak19_root127 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d q0 q1)) := by
  cases he

theorem peak19_root128 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c q0 q1 q2)) := by
  cases he

theorem peak19_root129 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) q1) := by
  cases he

theorem peak19_root130 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r q0 (T.m q1 q0))) := by
  cases he

theorem peak19_root131 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.r q0 q1) q0)) := by
  cases he

theorem peak19_root132 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.c q2 q0 q1) q0 q1)) := by
  cases he

theorem peak19_root133 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.c q0 q1 q2) q1)) := by
  cases he

theorem peak19_root134 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) q0) := by
  cases he

theorem peak19_root135 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d (T.c q0 q0 q1) q0)) := by
  cases he

theorem peak19_root136 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r q0 (T.c q0 q0 q1))) := by
  cases he

theorem peak19_root137 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d (T.d q0 q1) q2)) := by
  cases he

theorem peak19_root138 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak19_root139 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  have cycle := congrArg size e1
  simp only [size] at cycle
  omega

theorem peak19_root140 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) q0) := by
  cases he

theorem peak19_root141 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1))) := by
  cases he

theorem peak19_root142 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) := by
  cases he

theorem peak19_root143 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2))) := by
  cases he

theorem peak19_root144 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1))) := by
  cases he

theorem peak19_root145 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0)) := by
  cases he

theorem peak19_root146 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) := by
  cases he

end submission.Austin5837
