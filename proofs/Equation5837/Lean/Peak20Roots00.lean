import Basic
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace submission.Austin5837
open T
theorem peak20_root0 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.m q0 q1) q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r q1 q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak20_root1 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d q0 q1) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  cases e1

theorem peak20_root2 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.d q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c q0 q1 q2) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  cases e1

theorem peak20_root3 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c q1 q0 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) q1 := by
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

theorem peak20_root4 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.r q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r q0 (T.m q1 q0)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak20_root5 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.r q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.r q0 q1) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  cases e1

theorem peak20_root6 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.r (T.d q0 q1) q2)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.c q2 q0 q1) q0 q1) := by
  cases he

theorem peak20_root7 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c q0 q1 q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c q0 q1 q2) q1) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  cases e3

theorem peak20_root8 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.r (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) q0 := by
  cases he

theorem peak20_root9 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.c q0 q0 q1) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.c q0 q0 q1) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak20_root10 {q0 q1 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.c q0 q0 q1) q0) q0)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r q0 (T.c q0 q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := e1.symm
  subst e4
  have e5 := (T.c.inj e2).1
  have e6 := (T.c.inj e2).2.1
  have e7 := (T.c.inj e2).2.2
  cases e3

theorem peak20_root11 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.d q0 q1) q2) := by
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
  have e12 := e9.symm
  subst e12
  cases e10

theorem peak20_root12 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) q0 q1)) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) := by
  cases he

theorem peak20_root13 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.c q0 (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.c (T.d q0 q1) (T.d q0 q1) q2) := by
  cases he

theorem peak20_root14 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) q0 := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  cases e0

theorem peak20_root15 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d q0 q1) q2) (T.c (T.c q2 q0 q1) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.c q2 q0 q1) q0 q1) (T.d q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  cases e2

theorem peak20_root16 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m q0 (T.c (T.d q0 q1) (T.d q0 q1) q2))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := e0.symm
  subst e2
  have e3 := (T.c.inj e1).1
  have e4 := (T.c.inj e1).2.1
  have e5 := (T.c.inj e1).2.2
  cases e3

theorem peak20_root17 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d q0 q1) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) := by
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

theorem peak20_root18 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d q0 q1) (T.c (T.d q0 q1) (T.d q0 q1) q2)) (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0 q1) (T.d q0 q1)) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  cases e2

theorem peak20_root19 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  have e7 := (T.c.inj e2).1
  have e8 := (T.c.inj e2).2.1
  have e9 := (T.c.inj e2).2.2
  have e10 := (T.d.inj e3).1
  have e11 := (T.d.inj e3).2
  have e12 := (T.c.inj e4).1
  have e13 := (T.c.inj e4).2.1
  have e14 := (T.c.inj e4).2.2
  have e15 := (T.c.inj e5).1
  have e16 := (T.c.inj e5).2.1
  have e17 := (T.c.inj e5).2.2
  have e18 := (T.d.inj e6).1
  have e19 := (T.d.inj e6).2
  have e20 := (T.d.inj e7).1
  have e21 := (T.d.inj e7).2
  have e22 := (T.d.inj e8).1
  have e23 := (T.d.inj e8).2
  have e24 := e9.symm
  subst e24
  have e25 := e10.symm
  subst e25
  have e26 := e11.symm
  subst e26
  exact ⟨(T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0), (Steps.refl _), (Steps.refl _)⟩

theorem peak20_root20 {q0 q1 q2 x0 x1 x2 : T} (he : (T.m (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) (T.c (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1))) = (T.m (T.d (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) q0) (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)))) :
    Join (T.d (T.d (T.c (T.d x0 x1) (T.d x0 x1) x2) (T.d x0 x1)) x0) (T.r (T.c (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1)) (T.d (T.c (T.d q0 q1) (T.d q0 q1) q2) (T.d q0 q1))) := by
  have e0 := (T.m.inj he).1
  have e1 := (T.m.inj he).2
  have e2 := (T.d.inj e0).1
  have e3 := (T.d.inj e0).2
  have e4 := (T.c.inj e1).1
  have e5 := (T.c.inj e1).2.1
  have e6 := (T.c.inj e1).2.2
  cases e2

end submission.Austin5837
