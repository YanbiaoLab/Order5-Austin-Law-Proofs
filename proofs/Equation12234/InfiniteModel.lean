import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin12234

/- Relational square/Step construction; the source law is proved in NoMiddle. -/
inductive T where
  | e : T
  | k : T → T
  | p : T → T → T
  deriving DecidableEq
open T
def sz : T → Nat
  | e => 0
  | k a => sz a + 1
  | p a b => sz a + sz b + 2

mutual
inductive Code : T → T → T → Prop
  | rightRaw (x y z h a : T) (s₀ : Step z x h) (s₁ : Step h y a) :
      Code y (p a (p x y)) x
  | leftRaw (x y z h b : T) (s₀ : Step z x h) (s₁ : Step x y b) :
      Code y (p (p h y) b) x
  | rightSquare (y z h a : T) (s₀ : Step z y h) (s₁ : Step h y a) :
      Code y (p a (k y)) y
  | leftSquare (x y z b : T) (s₀ : Step z x y) (s₁ : Step x y b) :
      Code y (p (k y) b) x
inductive Step : T → T → T → Prop
  | raw (a b : T) : Step a b (p a b)
  | square (a : T) : Step a a (k a)
  | hit {a b o : T} (h : Code a b o) : Step a b o
end

theorem code_bounds {a b o : T} (h : Code a b o) : sz a < sz b ∧ sz o < sz b := by
  apply Code.rec (motive_1 := fun a b o _ => sz a < sz b ∧ sz o < sz b)
    (motive_2 := fun a b o _ => sz a ≤ max (sz b) (sz o))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro x y z h a s₀ s₁ ih₀ ih₁
    simp only [sz]; constructor <;> omega
  · intro x y z h b s₀ s₁ ih₀ ih₁
    simp only [sz]; constructor <;> omega
  · intro y z h a s₀ s₁ ih₀ ih₁
    simp only [sz]; constructor <;> omega
  · intro x y z b s₀ s₁ ih₀ ih₁
    simp only [sz]; constructor <;> omega
  · intro a b; simp only [sz]; omega
  · intro a; simp only [sz]; omega
  · intro a b o hc ih; omega

theorem step_bound {a b o : T} (h : Step a b o) : sz a ≤ max (sz b) (sz o) := by
  cases h with
  | raw => simp only [sz]; omega
  | square => simp only [sz]; omega
  | hit hc => have hb := (code_bounds hc).1; omega

theorem step_ne_second {a b : T} (h : Step a b b) : False := by
  cases h with
  | hit hc => have hb := (code_bounds hc).2; omega

theorem code_shape {a b o : T} (h : Code a b o) : ∃ l r, b = p l r := by
  cases h <;> exact ⟨_, _, rfl⟩

theorem code_steps {a b o : T} (h : Code a b o) :
    ∃ z t l r, Step z o t ∧ Step t a l ∧ Step o a r ∧ b = p l r := by
  cases h with
  | rightRaw _ _ z t l h₀ h₁ => exact ⟨z, t, l, p o a, h₀, h₁, Step.raw o a, rfl⟩
  | leftRaw _ _ z t r h₀ h₁ => exact ⟨z, t, p t a, r, h₀, Step.raw t a, h₁, rfl⟩
  | rightSquare _ z t l h₀ h₁ => exact ⟨z, t, l, k a, h₀, h₁, Step.square a, rfl⟩
  | leftSquare _ _ z r h₀ h₁ => exact ⟨z, a, k a, r, h₀, Step.square a, h₁, rfl⟩

end submission.Austin12234

set_option autoImplicit false
namespace submission.Austin12234
open T

theorem swap_raw_raw {a b c d x y : T}
    (s : Step a x (p c y)) (t : Step b y (p d x)) : x = y := by
  cases s with
  | raw => rfl
  | hit hs =>
    cases t with
    | raw => rfl
    | hit ht =>
      have hb := (code_bounds hs).2
      have hc := (code_bounds ht).2
      simp only [sz] at hb hc
      omega

theorem swap_raw_square {a b c x y : T}
    (s : Step a x (p c y)) (t : Step b y (k x)) : x = y := by
  cases s with
  | raw => rfl
  | hit hs =>
    cases t with
    | square => rfl
    | hit ht =>
      have hb := (code_bounds hs).2
      have hc := (code_bounds ht).2
      simp only [sz] at hb hc
      omega

theorem swap_square_square {a b x y : T}
    (s : Step a x (k y)) (t : Step b y (k x)) : x = y := by
  cases s with
  | square => rfl
  | hit hs =>
    cases t with
    | square => rfl
    | hit ht =>
      have hb := (code_bounds hs).2
      have hc := (code_bounds ht).2
      simp only [sz] at hb hc
      omega

theorem code_key_unique {a b o a' o' : T}
    (h : Code a b o) (h' : Code a' b o') : a = a' := by
  cases h <;> cases h'
  all_goals first
    | rfl
    | exact swap_raw_raw (by assumption) (by assumption)
    | exact swap_raw_square (by assumption) (by assumption)
    | exact (swap_raw_square (by assumption) (by assumption)).symm
    | exact swap_square_square (by assumption) (by assumption)

theorem step_first_unique {a b o a' : T}
    (h : Step a b o) (h' : Step a' b o) : a = a' := by
  cases h with
  | raw =>
    cases h' with
    | raw => rfl
    | hit hc => have hb := (code_bounds hc).2; simp only [sz] at hb; omega
  | square =>
    cases h' with
    | square => rfl
    | hit hc => have hb := (code_bounds hc).2; simp only [sz] at hb; omega
  | hit hc =>
    cases h' with
    | raw => have hb := (code_bounds hc).2; simp only [sz] at hb; omega
    | square => have hb := (code_bounds hc).2; simp only [sz] at hb; omega
    | hit hd => exact code_key_unique hc hd

theorem code_output_unique {a b o a' o' : T}
    (h : Code a b o) (h' : Code a' b o') : o = o' := by
  have ha := code_key_unique h h'
  subst a'
  obtain ⟨z, t, l, r, s₀, s₁, s₂, hb⟩ := code_steps h
  obtain ⟨z', t', l', r', s₀', s₁', s₂', hb'⟩ := code_steps h'
  have he := T.p.inj (hb.symm.trans hb')
  rw [he.2] at s₂
  exact step_first_unique s₂ s₂'

end submission.Austin12234

set_option autoImplicit false
namespace submission.Austin12234
open T

noncomputable def eval (a b : T) : T := by
  classical
  exact if a = b then k a
    else if h : ∃ o, Code a b o then Classical.choose h else p a b

theorem eval_square (a : T) : eval a a = k a := by simp [eval]
theorem eval_hit {a b o : T} (h : Code a b o) : eval a b = o := by
  have hab : a ≠ b := by
    intro he; have hb := (code_bounds h).1; rw [he] at hb; omega
  rw [eval, if_neg hab, dif_pos ⟨o, h⟩]
  exact code_output_unique (Classical.choose_spec ⟨o, h⟩) h
theorem eval_raw {a b : T} (hab : a ≠ b) (hc : ¬ ∃ o, Code a b o) :
    eval a b = p a b := by rw [eval, if_neg hab, dif_neg hc]
theorem eval_step (a b : T) : Step a b (eval a b) := by
  by_cases hab : a = b
  · subst b; rw [eval_square]; exact Step.square a
  · by_cases hc : ∃ o, Code a b o
    · obtain ⟨o, ho⟩ := hc; rw [eval_hit ho]; exact Step.hit ho
    · rw [eval_raw hab hc]; exact Step.raw a b
theorem eval_right_injective (a a' b : T) (h : eval a b = eval a' b) : a = a' := by
  have hs := eval_step a b
  rw [h] at hs
  exact step_first_unique hs (eval_step a' b)
theorem eval_ne_second (a b : T) : eval a b ≠ b := by
  intro h
  have hs := eval_step a b
  rw [h] at hs
  exact step_ne_second hs

theorem step_left_fixed {a b : T} (h : Step a b a) : Code a b a := by
  cases h with
  | hit hc => exact hc

theorem step_small {a b o : T} (h : Step a b o) (hb : sz o < sz b) : Code a b o := by
  cases h with
  | raw => simp only [sz] at hb; omega
  | square => simp only [sz] at hb; omega
  | hit hc => exact hc

theorem no_code_after_step {a b o q : T} (s : Step a b o) (c : Code b o q) : False := by
  cases s with
  | raw =>
    obtain ⟨z, t, l, r, s₀, s₁, s₂, he⟩ := code_steps c
    have hb := (T.p.inj he).2
    rw [← hb] at s₂
    exact step_ne_second s₂
  | square => obtain ⟨l, r, he⟩ := code_shape c; cases he
  | hit hc =>
    have h₁ := (code_bounds hc).2
    have h₂ := (code_bounds c).1
    omega

theorem left_fixed_shape {a b : T} (h : Code a b a) :
    ∃ l, b = p l (p a a) ∨ b = p l (k a) := by
  obtain ⟨z, t, l, r, s₀, s₁, s₂, he⟩ := code_steps h
  cases s₂ with
  | raw => exact ⟨l, Or.inl he⟩
  | square => exact ⟨l, Or.inr he⟩
  | hit hc => have hb := (code_bounds hc).1; omega

theorem no_middle_after_hit {x y z h a b o : T}
    (s₀ : Step z x h) (s₁ : Step h y a) (cb : Code x y b)
    (c : Code a b o) : False := by
  have hab := (code_bounds c).1
  have hby := (code_bounds cb).2
  have ha : sz a < sz y := by omega
  have ch := step_small s₁ ha
  have hh : h = x := code_key_unique ch cb
  rw [hh] at s₀
  exact step_ne_second s₀

/- Every possible middle hit has the right-hand source product in its raw
   branch. This reduction does not exclude that remaining branch. -/
theorem middle_hit_requires_raw {x y z h a b o : T}
    (s₀ : Step z x h) (s₁ : Step h y a) (s₂ : Step x y b)
    (c : Code a b o) : b = p x y := by
  cases s₂ with
  | raw => rfl
  | square => obtain ⟨l, r, he⟩ := code_shape c; cases he
  | hit cb => exact False.elim (no_middle_after_hit s₀ s₁ cb c)

def tower : Nat → T
  | 0 => e
  | n+1 => k (tower n)
theorem tower_size (n : Nat) : sz (tower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower, sz, ih]
theorem tower_injective (n j : Nat) (h : tower n = tower j) : n = j := by
  have hh := congrArg sz h
  simpa only [tower_size] using hh

end submission.Austin12234

set_option autoImplicit false
namespace submission.Austin12234
open T

theorem source_container_code {x y z h a b : T}
    (s₀ : Step z x h) (s₁ : Step h y a) (s₂ : Step x y b) : Code y (p a b) x := by
  cases s₂ with
  | raw => exact Code.rightRaw _ _ _ _ _ s₀ s₁
  | square => exact Code.rightSquare _ _ _ _ s₀ s₁
  | hit cb =>
    cases s₁ with
    | raw => exact Code.leftRaw _ _ _ _ _ s₀ (Step.hit cb)
    | square => exact Code.leftSquare _ _ _ _ s₀ (Step.hit cb)
    | hit ca =>
      have hh := code_key_unique ca cb
      rw [hh] at s₀
      exact False.elim (step_ne_second s₀)

/- The safety property used below is proved by rawSafety in NoMiddle. -/
def RawSafety : Prop := ∀ (x y z h a o : T),
  Step z x h → Step h y a → ¬ Code a (p x y) o

theorem no_middle_of_rawSafety (safe : RawSafety) {x y z h a b o : T}
    (s₀ : Step z x h) (s₁ : Step h y a) (s₂ : Step x y b)
    (c : Code a b o) : False := by
  have hb := middle_hit_requires_raw s₀ s₁ s₂ c
  rw [hb] at c
  exact safe x y z h a o s₀ s₁ c

theorem equation12234_of_rawSafety (safe : RawSafety) (x y z : T) :
    eval y (eval (eval (eval z x) y) (eval x y)) = x := by
  let h := eval z x
  let a := eval h y
  let b := eval x y
  have s₀ : Step z x h := eval_step z x
  have s₁ : Step h y a := eval_step h y
  have s₂ : Step x y b := eval_step x y
  have hab : a ≠ b := by
    intro he
    rw [he] at s₁
    have hh := step_first_unique s₁ s₂
    rw [hh] at s₀
    exact step_ne_second s₀
  have hc : ¬ ∃ o, Code a b o := by
    rintro ⟨o, ho⟩
    exact no_middle_of_rawSafety safe s₀ s₁ s₂ ho
  change eval y (eval a b) = x
  rw [eval_raw hab hc]
  exact eval_hit (source_container_code s₀ s₁ s₂)

/- The unconditional infinite_model theorem in Law supplies the proved rawSafety argument. -/
theorem infinite_model_of_rawSafety (safe : RawSafety) :
    ∃ (A : Type) (op : A → A → A) (f : Nat → A),
      (∀ x y z, op y (op (op (op z x) y) (op x y)) = x) ∧
      (∀ n j, f n = f j → n = j) :=
  ⟨T, eval, tower, equation12234_of_rawSafety safe, tower_injective⟩

end submission.Austin12234

set_option autoImplicit false
namespace submission.Austin12234
open T

def Plain (a b o : T) : Prop := o = p a b ∨ (a = b ∧ o = k b)
theorem step_plain_or_code {a b o : T} (s : Step a b o) : Plain a b o ∨ Code a b o := by
  cases s with
  | raw => exact Or.inl (Or.inl rfl)
  | square => exact Or.inl (Or.inr ⟨rfl, rfl⟩)
  | hit hc => exact Or.inr hc
theorem plain_growth {a b o : T} (h : Plain a b o) : sz a < sz o ∧ sz b < sz o := by
  rcases h with h | ⟨rfl, h⟩ <;> rw [h] <;> simp only [sz] <;> constructor <;> omega
theorem plain_right_unique {a b c d o : T} (s : Plain a b o) (t : Plain c d o) : b = d := by
  rcases s with rfl | ⟨rfl, rfl⟩ <;> rcases t with he | ⟨_, he⟩
  · exact (T.p.inj he).2
  · cases he
  · cases he
  · exact T.k.inj he
theorem plain_of_no_code {a b o : T} (s : Step a b o) (hn : ¬ Code a b o) : Plain a b o :=
  (step_plain_or_code s).resolve_right hn
theorem plain_of_other_key {a b o k v : T} (s : Step a b o) (hc : Code k b v)
    (hne : a ≠ k) : Plain a b o := by
  apply plain_of_no_code s
  intro hd
  exact hne (code_key_unique hd hc)
theorem plain_of_large_left {a b o : T} (s : Step a b o) (hn : sz b ≤ sz a) : Plain a b o := by
  apply plain_of_no_code s
  intro hc; have hb := (code_bounds hc).1; omega
theorem no_code_equal_pair {a k o : T} (c : Code k (p a a) o) : False := by
  obtain ⟨z, t, l, r, s₀, s₁, s₂, he⟩ := code_steps c
  have hh := T.p.inj he
  rw [← hh.1] at s₁
  rw [← hh.2] at s₂
  have ht := step_first_unique s₁ s₂
  rw [ht] at s₀
  exact step_ne_second s₀
theorem no_code_tag {a k o : T} {b : T} (hb : b = p a a ∨ b = T.k a)
    (c : Code k b o) : False := by
  rcases hb with rfl | rfl
  · exact no_code_equal_pair c
  · obtain ⟨l, r, he⟩ := code_shape c; cases he

theorem no_code_fixed_extension {a h v u o k t : T}
    (fixed : Code a h a) (s₀ : Step v a u) (s₁ : Step u h o)
    (c : Code k o t) : False := by
  have hau : u ≠ a := fun he => step_ne_second (he ▸ s₀)
  have po := plain_of_other_key s₁ fixed hau
  obtain ⟨l, shape⟩ := left_fixed_shape fixed
  obtain ⟨zz, r, ll, rr, q₀, q₁, q₂, he⟩ := code_steps c
  rcases po with po | ⟨_, po⟩
  · rw [po] at he
    have hs := T.p.inj he
    rw [← hs.1] at q₁
    rw [← hs.2] at q₂
    have ah := (code_bounds fixed).1
    rcases step_plain_or_code q₂ with pq | cq
    · rcases pq with pq | ⟨_, pq⟩
      · have tag : k = p a a ∨ k = T.k a := by
          rcases shape with shape | shape
          · exact Or.inl (T.p.inj (pq.symm.trans shape)).2
          · exact Or.inr (T.p.inj (pq.symm.trans shape)).2
        have p₁ := plain_of_no_code q₁ (no_code_tag tag)
        have gu := (plain_growth p₁).2
        have ak : sz a < sz k := by rcases tag with rfl | rfl <;> simp only [sz] <;> omega
        have p₀ : Plain v a u := plain_of_no_code s₀ (by
          intro hc; have hu := (code_bounds hc).2; omega)
        have hk := plain_right_unique p₀ p₁
        rw [hk] at ak; omega
      · obtain ⟨l', r', shape'⟩ := code_shape fixed
        rw [pq] at shape'; cases shape'
    · have hk := (code_bounds cq).2
      have p₁ := plain_of_other_key q₁ cq (fun hr => step_ne_second (hr ▸ q₀))
      have gu := (plain_growth p₁).2
      have p₀ : Plain v a u := plain_of_no_code s₀ (by
        intro hc; have hu := (code_bounds hc).2; omega)
      have ka := plain_right_unique p₀ p₁
      rw [ka] at ah; omega
  · obtain ⟨l', r', shape'⟩ := code_shape c
    rw [po] at shape'; cases shape'

end submission.Austin12234

set_option autoImplicit false
namespace submission.Austin12234
open T

theorem cycle_unpack {k l r : T} (c : Code k (p l r) r) :
    ∃ v u, Code r k r ∧ Step v r u ∧ Step u k l := by
  obtain ⟨v, u, ll, rr, s₀, s₁, s₂, he⟩ := code_steps c
  have hh := T.p.inj he
  rw [← hh.1] at s₁
  rw [← hh.2] at s₂
  exact ⟨v, u, step_left_fixed s₂, s₀, s₁⟩

theorem cycle_growing_impossible {z x h y a o t w : T}
    (s₀ : Step z x h) (s₁ : Step h y a) (s₂ : Step o a y)
    (s₃ : Step t a x) (s₄ : Step w o t) (ha : a = p h y) : False := by
  have gha : sz h < sz a ∧ sz y < sz a := by rw [ha]; simp only [sz]; constructor <;> omega
  have ca := step_small s₂ gha.2
  have ca' := ca
  rw [ha] at ca'
  obtain ⟨v, u, fixed, su, sh⟩ := cycle_unpack ca'
  have ny : ∀ k q, ¬ Code k h q := fun _ _ => no_code_fixed_extension fixed su sh
  have ph := plain_of_other_key sh fixed (fun hu => step_ne_second (hu ▸ su))
  have goh := (plain_growth ph).2
  have gyo := (code_bounds fixed).1
  have px := plain_of_other_key s₃ ca (fun he => step_ne_second (he ▸ s₄))
  have gax := (plain_growth px).2
  have cx := step_small s₀ (by omega)
  have hx : x = p t a := by
    rcases px with hx | ⟨_, hx⟩
    · exact hx
    · obtain ⟨l, r, he⟩ := code_shape cx; rw [hx] at he; cases he
  obtain ⟨v', r, ll, rr, q₀, q₁, q₂, he⟩ := code_steps cx
  rw [hx] at he
  have hp := T.p.inj he
  rw [← hp.1] at q₁
  rw [← hp.2] at q₂
  have pr := plain_of_no_code q₀ (ny _ _)
  have ghr := (plain_growth pr).2
  have finish (pq : Plain r z t) : False := by
    have grt := (plain_growth pq).1
    have pt : Plain w o t := plain_of_no_code s₄ (by
      intro ct
      have ht := code_output_unique ct fixed
      rw [ht] at grt
      omega)
    have hz := plain_right_unique pq pt
    rw [hz] at q₂
    have pa := plain_of_other_key q₂ fixed (by intro hh; rw [hh] at goh; omega)
    rcases pa with pa | ⟨_, pa⟩
    · have hy := (T.p.inj (ha.symm.trans pa)).2
      rw [hy] at gyo; omega
    · rw [ha] at pa; cases pa
  rcases step_plain_or_code q₂ with pa | cza
  · rcases pa with pa | ⟨_, pa⟩
    · have hz : y = z := (T.p.inj (ha.symm.trans pa)).2
      apply finish
      apply plain_of_large_left q₁
      rw [← hz]; omega
    · rw [ha] at pa; cases pa
  · apply finish
    exact plain_of_other_key q₁ cza (by intro hh; rw [hh] at ghr; omega)

theorem cycle_shrinking_impossible {z x h y a o t w : T}
    (s₀ : Step z x h) (s₁ : Step h y a) (s₂ : Step o a y)
    (s₃ : Step t a x) (s₄ : Step w o t) (hy : y = p o a) : False := by
  have gay : sz a < sz y := by rw [hy]; simp only [sz]; omega
  have cy := step_small s₁ gay
  have cy' := cy
  rw [hy] at cy'
  obtain ⟨v, u, fixed, su, so⟩ := cycle_unpack cy'
  have no : ∀ k q, ¬ Code k o q := fun _ _ => no_code_fixed_extension fixed su so
  have po := plain_of_other_key so fixed (fun hu => step_ne_second (hu ▸ su))
  have gho := (plain_growth po).2
  have gah := (code_bounds fixed).1
  have pt := plain_of_no_code s₄ (no _ _)
  have got := (plain_growth pt).2
  have px := plain_of_large_left s₃ (by omega)
  have gtx := (plain_growth px).1
  have cx := step_small s₀ (by omega)
  have hx : x = p t a := by
    rcases px with hx | ⟨_, hx⟩
    · exact hx
    · obtain ⟨l, r, he⟩ := code_shape cx; rw [hx] at he; cases he
  obtain ⟨v', r, ll, rr, q₀, q₁, q₂, he⟩ := code_steps cx
  rw [hx] at he
  have hp := T.p.inj he
  rw [← hp.1] at q₁
  rw [← hp.2] at q₂
  have cz : Code h z a := (step_plain_or_code q₂).elim (fun pq => by
    have ha := (plain_growth pq).1
    omega) id
  have pq := plain_of_no_code q₁ (by
    intro ct
    have ht := code_output_unique ct cz
    rw [ht] at got
    omega)
  have hz := plain_right_unique pq pt
  rw [hz] at cz
  exact no _ _ cz

theorem forbidden_pentagon {z x h y a o t w : T}
    (s₀ : Step z x h) (s₁ : Step h y a) (s₂ : Step o a y)
    (s₃ : Step t a x) (s₄ : Step w o t) : False := by
  rcases step_plain_or_code s₁ with p₁ | c₁
  · rcases p₁ with ha | ⟨_, ha⟩
    · exact cycle_growing_impossible s₀ s₁ s₂ s₃ s₄ ha
    · have gay : sz y < sz a := by rw [ha]; simp only [sz]; omega
      have c₂ := step_small s₂ gay
      obtain ⟨l, r, he⟩ := code_shape c₂
      rw [ha] at he; cases he
  · have gay := (code_bounds c₁).2
    have p₂ : Plain o a y := plain_of_no_code s₂ (by
      intro c₂; have gya := (code_bounds c₂).2; omega)
    rcases p₂ with hy | ⟨_, hy⟩
    · exact cycle_shrinking_impossible s₀ s₁ s₂ s₃ s₄ hy
    · obtain ⟨l, r, he⟩ := code_shape c₁
      rw [hy] at he; cases he

theorem rawSafety : RawSafety := by
  intro x y z h a o s₀ s₁ c
  obtain ⟨w, t, l, r, q₀, q₁, q₂, he⟩ := code_steps c
  have hh := T.p.inj he
  rw [← hh.1] at q₁
  rw [← hh.2] at q₂
  exact forbidden_pentagon s₀ s₁ q₂ q₁ q₀

theorem equation12234 (x y z : T) : eval y (eval (eval (eval z x) y) (eval x y)) = x :=
  equation12234_of_rawSafety rawSafety x y z

end submission.Austin12234

set_option autoImplicit false
namespace submission.Austin12234
abbrev Carrier := T
noncomputable def mul : Carrier → Carrier → Carrier := eval
noncomputable def opposite (a b : Carrier) : Carrier := mul b a
def embed : Nat → Carrier := tower
theorem embed_injective (n j : Nat) (h : embed n = embed j) : n = j := tower_injective n j h
theorem equation33883 (x y z : Carrier) :
    opposite (opposite (opposite y x) (opposite y (opposite x z))) y = x :=
  equation12234 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, op y (op (op (op z x) y) (op x y)) = x) ∧
    (∀ n j, f n = f j → n = j) := infinite_model_of_rawSafety rawSafety
end submission.Austin12234

namespace submission
abbrev CM := Austin12234.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin12234.embed n = Austin12234.embed j) : n = j :=
  Austin12234.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin12234.mul⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin12234.equation12234 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin12234.embed_injective 0 1
      (h (submission.Austin12234.embed 0) (submission.Austin12234.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

