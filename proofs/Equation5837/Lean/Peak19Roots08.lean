import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak19_root168 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r q1 q0) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root169 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d q0 q1) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root170 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c q0 q1 q2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root171 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d q1 (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root172 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r q0 (T.m q1 q0)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root173 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.r q0 q1) q0) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root174 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.c q2 q0 q1) q0 q1) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root175 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.c q0 q1 q2) q1) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root176 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d q0 (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root177 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.c q0 q0 q1) q0) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root178 {q0 q1 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r q0 (T.c q0 q0 q1)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root179 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.d q0 q1) q2) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root180 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d x0 x1)) x0 x1)) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  cases e0

theorem peak19_root181 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d x0 x1)) x0 x1)) := by
  have e0 := (T.c.inj he).1
  have e1 := (T.c.inj he).2.1
  have e2 := (T.c.inj he).2.2
  have e3 := e0.symm
  subst e3
  cases e1

theorem peak19_root182 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d q0 (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root183 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root184 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root185 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root186 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root187 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.d x0 x1)) x0 x1)) := by
  cases he

theorem peak19_root188 {q0 q1 q2 x0 x1 x2 : T} (he : (T.c (T.d x0 x1) (T.d x0 x1) x2) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0 x1) (T.d x0 x1)) (T.m (T.d (T.d x0 x1) (T.c (T.d x0 x1) (T.d x0 x1) x2)) (T.c (T.d (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) (T.d x0 x1)) x0 x1)) := by
  cases he

end submission.Austin5837
