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
set_option autoImplicit false
namespace Austin12857
open T

theorem root_step {x y z : T} (h : Root x y) (k : Step x z) : Join y z := by
  cases h with
  | r1 x => exact peak1 x k
  | r2 x y z => exact peak2 x y z k
  | r3 x y => exact peak3 x y k
  | r4 x y => exact peak4 x y k
  | r5 x y z => exact peak5 x y z k
  | r6 x y => exact peak6 x y k
  | r7 x => exact peak7 x k
  | r8 x y => exact peak8 x y k
  | r9 x y => exact peak9 x y k
  | r10 x y => exact peak10 x y k

theorem local_join {x y z : T} (h : Step x y) (k : Step x z) : Join y z := by
  induction h generalizing z with
  | root hr => exact root_step hr k
  | underS h ih =>
    cases k with
    | root hr => exact (root_step hr (.underS h)).symm
    | underS k => exact (ih k).underS
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

/-- Newman's argument specialized to the strictly decreasing node count. -/
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
          obtain ⟨e, hde, he⟩ := normal_exists d
          have hye := ih (size p) (hx ▸ step_decreases hxp) p rfl y e
            hy he hpy (hpd.trans hde)
          have hze := ih (size q) (hx ▸ step_decreases hxq) q rfl z e
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
end Austin12857
