import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak21_root0 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.m q0 q1) q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r q1 q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak21_root1 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d q0 q1) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  cases e1

theorem peak21_root2 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.d q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.c q0 q1 q2) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  cases e1

theorem peak21_root3 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) q1 := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  have e6 := e3.symm
  subst e6
  cases e4

theorem peak21_root4 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.r q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r q0 (T.m q1 q0)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak21_root5 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.r q0 q1) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  cases e1

theorem peak21_root6 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.r (T.d q0 q1) q2)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.c (T.c q2 q0 q1) q0 q1) := by
  cases he

theorem peak21_root7 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.c q0 q1 q2) q1) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  cases e3

theorem peak21_root8 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) q0 := by
  cases he

theorem peak21_root9 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d (T.c q0 q0 q1) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak21_root10 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r q0 (T.c q0 q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := e1.symm
  subst e4
  cases e2

theorem peak21_root11 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d (T.d q0 q1) q2) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := e2.symm
  subst e7
  have e8 := e3.symm
  subst e8
  have e9 := (T.c.inj e4).1
  have e10 := (T.c.inj e4).2.1
  have e11 := (T.c.inj e4).2.2
  cases e5

theorem peak21_root12 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) := by
  cases he

theorem peak21_root13 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.c (T.d q0 q1) (T.d q0 q1) q2) := by
  cases he

theorem peak21_root14 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) q0 := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak21_root15 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  have e9 := e3.symm
  subst e9
  have e10 := (T.c.inj e4).1
  have e11 := (T.c.inj e4).2.1
  have e12 := (T.c.inj e4).2.2
  have e13 := e5.symm
  subst e13
  have e14 := e6.symm
  subst e14
  have e15 := e10.symm
  have cycle := congrArg size e15
  simp only [size] at cycle
  omega

theorem peak21_root16 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  cases e3

theorem peak21_root17 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := e2.symm
  subst e7
  have e8 := e3.symm
  subst e8
  cases e4

theorem peak21_root18 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  subst e3
  cases e4

theorem peak21_root19 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  cases e2

theorem peak21_root20 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.r (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.d.inj e2).1
  have e8 := (T.d.inj e2).2
  have e9 := e3.symm
  subst e9
  have e10 := (T.c.inj e4).1
  have e11 := (T.c.inj e4).2.1
  have e12 := (T.c.inj e4).2.2
  have e13 := (T.c.inj e5).1
  have e14 := (T.c.inj e5).2.1
  have e15 := (T.c.inj e5).2.2
  have e16 := (T.d.inj e6).1
  have e17 := (T.d.inj e6).2
  have e18 := (T.c.inj e7).1
  have e19 := (T.c.inj e7).2.1
  have e20 := (T.c.inj e7).2.2
  have e21 := (T.d.inj e8).1
  have e22 := (T.d.inj e8).2
  have e23 := (T.d.inj e10).1
  have e24 := (T.d.inj e10).2
  have e25 := (T.d.inj e11).1
  have e26 := (T.d.inj e11).2
  have e27 := e12.symm
  subst e27
  have e28 := (T.d.inj e13).1
  have e29 := (T.d.inj e13).2
  have e30 := (T.d.inj e14).1
  have e31 := (T.d.inj e14).2
  have e32 := e17.symm
  subst e32
  exact ⟨(T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))), (Steps.refl _), (Steps.refl _)⟩

end submission.Austin5837
