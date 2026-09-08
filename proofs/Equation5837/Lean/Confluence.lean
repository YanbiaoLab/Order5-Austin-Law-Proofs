import Peak1
import Peak2
import Peak3
import Peak4
import Peak5
import Peak6
import Peak7
import Peak8
import Peak9
import Peak10
import Peak11
import Peak12
import Peak13
import Peak14
import Peak15
import Peak16
import Peak17
import Peak18
import Peak19
import Peak20
import Peak21
set_option autoImplicit false
namespace submission.Austin5837
open T
theorem root_step {x y z : T} (h : Root x y) (k : Step x z) : Join y z := by
  cases h with
  | r1 => exact peak1 _ _ k
  | r2 => exact peak2 _ _ k
  | r3 => exact peak3 _ _ _ k
  | r4 => exact peak4 _ _ _ k
  | r5 => exact peak5 _ _ k
  | r6 => exact peak6 _ _ k
  | r7 => exact peak7 _ _ _ k
  | r8 => exact peak8 _ _ _ k
  | r9 => exact peak9 _ _ k
  | r10 => exact peak10 _ _ k
  | r11 => exact peak11 _ _ k
  | r12 => exact peak12 _ _ _ k
  | r13 => exact peak13 _ _ _ k
  | r14 => exact peak14 _ _ _ k
  | r15 => exact peak15 _ _ _ k
  | r16 => exact peak16 _ _ _ k
  | r17 => exact peak17 _ _ _ k
  | r18 => exact peak18 _ _ _ k
  | r19 => exact peak19 _ _ _ k
  | r20 => exact peak20 _ _ _ k
  | r21 => exact peak21 _ _ _ k
theorem local_join {x y z : T} (h : Step x y) (k : Step x z) : Join y z := by
  induction h generalizing z with
  | root hr => exact root_step hr k
  | underK h ih =>
    cases k with
    | root hr => exact (root_step hr (.underK h)).symm
    | underK k => exact (ih k).underK
  | underV h ih =>
    cases k with
    | root hr => exact (root_step hr (.underV h)).symm
    | underV k => exact (ih k).underV
  | underU h ih =>
    cases k with
    | root hr => exact (root_step hr (.underU h)).symm
    | underU k => exact (ih k).underU
  | left c h ih =>
    cases k with
    | root hr => exact (root_step hr (.left c h)).symm
    | left _ k => exact (ih k).left c
    | @right x _ z k =>
      exact ⟨m _ z, Steps.single (.right _ k), Steps.single (.left z h)⟩
  | right c h ih =>
    cases k with
    | root hr => exact (root_step hr (.right c h)).symm
    | @left x y _ k =>
      exact ⟨m y _, Steps.single (.left _ k), Steps.single (.right y h)⟩
    | right _ k => exact (ih k).right c
  | leftR c h ih =>
    cases k with
    | root hr => exact (root_step hr (.leftR c h)).symm
    | leftR _ k => exact (ih k).leftR c
    | @rightR x _ z k =>
      exact ⟨r _ z, Steps.single (.rightR _ k), Steps.single (.leftR z h)⟩
  | rightR c h ih =>
    cases k with
    | root hr => exact (root_step hr (.rightR c h)).symm
    | @leftR x y _ k =>
      exact ⟨r y _, Steps.single (.leftR _ k), Steps.single (.rightR y h)⟩
    | rightR _ k => exact (ih k).rightR c
  | leftD c h ih =>
    cases k with
    | root hr => exact (root_step hr (.leftD c h)).symm
    | leftD _ k => exact (ih k).leftD c
    | @rightD x _ z k =>
      exact ⟨d _ z, Steps.single (.rightD _ k), Steps.single (.leftD z h)⟩
  | rightD c h ih =>
    cases k with
    | root hr => exact (root_step hr (.rightD c h)).symm
    | @leftD x y _ k =>
      exact ⟨d y _, Steps.single (.leftD _ k), Steps.single (.rightD y h)⟩
    | rightD _ k => exact (ih k).rightD c
  | firstC b d h ih =>
    cases k with
    | root hr => exact (root_step hr (.firstC b d h)).symm
    | firstC _ _ k => exact (ih k).firstC b d
    | @secondC _ _ b2 _ k =>
      exact ⟨c _ b2 d, Steps.single (.secondC _ d k), Steps.single (.firstC b2 d h)⟩
    | @thirdC _ _ _ d2 k =>
      exact ⟨c _ b d2, Steps.single (.thirdC _ b k), Steps.single (.firstC b d2 h)⟩
  | secondC aa d h ih =>
    cases k with
    | root hr => exact (root_step hr (.secondC aa d h)).symm
    | @firstC _ a2 _ _ k =>
      exact ⟨c a2 _ d, Steps.single (.firstC _ d k), Steps.single (.secondC a2 d h)⟩
    | secondC _ _ k => exact (ih k).secondC aa d
    | @thirdC _ _ _ d2 k =>
      exact ⟨c aa _ d2, Steps.single (.thirdC aa _ k), Steps.single (.secondC aa d2 h)⟩
  | thirdC aa b h ih =>
    cases k with
    | root hr => exact (root_step hr (.thirdC aa b h)).symm
    | @firstC _ a2 _ _ k =>
      exact ⟨c a2 b _, Steps.single (.firstC b _ k), Steps.single (.thirdC a2 b h)⟩
    | @secondC _ _ b2 _ k =>
      exact ⟨c aa b2 _, Steps.single (.secondC aa _ k), Steps.single (.thirdC aa b2 h)⟩
    | thirdC _ _ k => exact (ih k).thirdC aa b
def Normal (x : T) : Prop := ∀ {y : T}, Step x y → False

theorem normal_exists (x : T) : ∃ y, Steps x y ∧ Normal y := by
  classical
  have aux : ∀ n x, size x = n → ∃ y, Steps x y ∧ Normal y := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hx
      by_cases h : ∃ y, Step x y
      · obtain ⟨y, hxy⟩ := h
        obtain ⟨z, hyz, hz⟩ := ih (size y) (hx ▸ step_decreases hxy) y rfl
        exact ⟨z, .cons hxy hyz, hz⟩
      · exact ⟨x, .refl x, fun k => h ⟨_, k⟩⟩
  exact aux (size x) x rfl

theorem normal_steps_eq {x y : T} (hx : Normal x) (h : Steps x y) : x = y := by
  cases h with
  | refl => rfl
  | cons h _ => exact False.elim (hx h)

/-- Newman's argument specialized to the strictly decreasing positive weighted tree size. -/
theorem normal_unique {x y z : T} (hy : Normal y) (hz : Normal z)
    (hxy : Steps x y) (hxz : Steps x z) : y = z := by
  have aux : ∀ n x, size x = n → ∀ y z, Normal y → Normal z →
      Steps x y → Steps x z → y = z := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hx y z hy hz hxy hxz
      cases hxy with
      | refl => exact normal_steps_eq hy hxz
      | @cons _ p _ hxp hpy =>
        cases hxz with
        | refl => exact (normal_steps_eq hz (.cons hxp hpy)).symm
        | @cons _ q _ hxq hqz =>
          obtain ⟨d, hpd, hqd⟩ := local_join hxp hxq
          obtain ⟨normalTarget, hde, he⟩ := normal_exists d
          have hye := ih (size p) (hx ▸ step_decreases hxp) p rfl y normalTarget
            hy he hpy (hpd.trans hde)
          have hze := ih (size q) (hx ▸ step_decreases hxq) q rfl z normalTarget
            hz he hqz (hqd.trans hde)
          exact hye.trans hze.symm
  exact aux (size x) x rfl y z hy hz hxy hxz

noncomputable def norm (x : T) : T := Classical.choose (normal_exists x)
theorem steps_norm (x : T) : Steps x (norm x) := (Classical.choose_spec (normal_exists x)).1
theorem norm_normal (x : T) : Normal (norm x) := (Classical.choose_spec (normal_exists x)).2

theorem norm_of_normal {x : T} (h : Normal x) : norm x = x :=
  (normal_steps_eq h (steps_norm x)).symm

theorem norm_steps {x y : T} (h : Steps x y) : norm x = norm y :=
  normal_unique (norm_normal x) (norm_normal y) (steps_norm x) (h.trans (steps_norm y))

theorem confluent {x y z : T} (hy : Steps x y) (hz : Steps x z) : Join y z := by
  have h : norm y = norm z := (norm_steps hy).symm.trans (norm_steps hz)
  exact ⟨norm y, steps_norm y, h ▸ steps_norm z⟩

theorem norm_m (x y : T) : norm (m (norm x) (norm y)) = norm (m x y) :=
  (norm_steps (Steps.both (steps_norm x) (steps_norm y))).symm

theorem norm_m_left (p q : T) : norm (m (norm p) q) = norm (m p q) :=
  (norm_steps (Steps.left q (steps_norm p))).symm
theorem norm_m_right (p q : T) : norm (m p (norm q)) = norm (m p q) :=
  (norm_steps (Steps.right p (steps_norm q))).symm
end submission.Austin5837
