import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin10218

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
      Code y (p (p x y) a) x
  | leftRaw (x y z h b : T) (s₀ : Step z x h) (s₁ : Step x y b) :
      Code y (p b (p h y)) x
  | rightSquare (y z h a : T) (s₀ : Step z y h) (s₁ : Step h y a) :
      Code y (p (k y) a) y
  | leftSquare (x y z b : T) (s₀ : Step z x y) (s₁ : Step x y b) :
      Code y (p b (k y)) x
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
    ∃ z t l r, Step z o t ∧ Step o a l ∧ Step t a r ∧ b = p l r := by
  cases h with
  | rightRaw _ _ z t l h₀ h₁ => exact ⟨z, t, p o a, l, h₀, Step.raw o a, h₁, rfl⟩
  | leftRaw _ _ z t r h₀ h₁ => exact ⟨z, t, r, p t a, h₀, h₁, Step.raw t a, rfl⟩
  | rightSquare _ z t l h₀ h₁ => exact ⟨z, t, k a, l, h₀, Step.square a, h₁, rfl⟩
  | leftSquare _ _ z r h₀ h₁ => exact ⟨z, a, r, k a, h₀, h₁, Step.square a, rfl⟩

end submission.Austin10218

set_option autoImplicit false
namespace submission.Austin10218
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
  rw [he.1] at s₁
  exact step_first_unique s₁ s₁'

end submission.Austin10218

set_option autoImplicit false
namespace submission.Austin10218
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
    ∃ r, b = p (p a a) r ∨ b = p (k a) r := by
  obtain ⟨z, t, l, r, s₀, s₁, s₂, he⟩ := code_steps h
  cases s₁ with
  | raw => exact ⟨r, Or.inl he⟩
  | square => exact ⟨r, Or.inr he⟩
  | hit hc => have hb := (code_bounds hc).1; omega

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

end submission.Austin10218

set_option autoImplicit false
namespace submission.Austin10218
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

theorem no_code_fixed_extension {a h v u o key out : T}
    (fixed : Code a h a) (s₀ : Step v a u) (s₁ : Step u h o)
    (c : Code key o out) : False := by
  have hau : u ≠ a := fun he => step_ne_second (he ▸ s₀)
  have po := plain_of_other_key s₁ fixed hau
  obtain ⟨zf, tf, tag, kf, sf₀, sf₁, sf₂, hf⟩ := code_steps fixed
  have ptag : Plain a a tag := plain_of_large_left sf₁ (by omega)
  have gat := (plain_growth ptag).2
  have ah := (code_bounds fixed).1
  obtain ⟨zz, r, ll, rr, q₀, q₁, q₂, he⟩ := code_steps c
  rcases po with po | ⟨_, po⟩
  · rw [po] at he
    have hs := T.p.inj he
    rw [← hs.1] at q₁
    rw [← hs.2] at q₂
    have pq₂ : Plain r key h := by
      apply plain_of_no_code q₂
      intro cq
      have hk := (code_bounds cq).2
      have pq₁ := plain_of_other_key q₁ cq (fun hr => step_ne_second (hr.symm ▸ q₀))
      have gu := (plain_growth pq₁).2
      have pv : Plain v a u := plain_of_no_code s₀ (by
        intro hc; have hu := (code_bounds hc).2; omega)
      have ka := plain_right_unique pv pq₁
      rw [ka] at ah; omega
    rcases pq₂ with hh | ⟨_, hh⟩
    · have eqs := T.p.inj (hh.symm.trans hf)
      rw [eqs.1] at q₀
      rw [eqs.2] at q₁
      rcases step_plain_or_code q₁ with pq | cq
      · have gou := (plain_growth pq).1
        have pv : Plain v a u := plain_of_no_code s₀ (by
          intro cv
          have gua := (code_bounds cv).2
          have pz : Plain zz out tag := plain_of_no_code q₀ (by
            intro cz; have gto := (code_bounds cz).2; omega)
          have hoa := plain_right_unique pz ptag
          rw [hoa] at gou; omega)
        have hak := plain_right_unique pv pq
        rw [← hak] at sf₂
        exact step_ne_second sf₂
      · rcases step_plain_or_code q₀ with pz | cz
        · have hoa := plain_right_unique pz ptag
          rw [hoa] at cq
          exact no_code_after_step sf₂ cq
        · have gto := (code_bounds cz).2
          have gok := (code_bounds cq).1
          have pk : Plain tf a kf := plain_of_no_code sf₂ (by
            intro ck; have gka := (code_bounds ck).2; omega)
          have hk : kf = p tf a := by
            rcases pk with hk | ⟨ht, _⟩
            · exact hk
            · exact False.elim (step_ne_second (ht ▸ sf₀))
          obtain ⟨zw, tw, lw, rw, w₀, w₁, w₂, hw⟩ := code_steps cq
          rw [hk] at hw
          have eqw := T.p.inj hw
          rw [← eqw.2] at w₂
          have cw := step_small w₂ (by omega)
          have bad := code_output_unique cw cz
          rw [bad] at gat; omega
    · rw [hh] at hf; cases hf
  · obtain ⟨l', r', shape'⟩ := code_shape c
    rw [po] at shape'; cases shape'

end submission.Austin10218

set_option autoImplicit false
namespace submission.Austin10218
open T

theorem forbidden_pentagon {z x h y a o t w : T}
    (s₀ : Step z x h) (s₁ : Step x y a) (s₂ : Step o a h)
    (s₃ : Step t a y) (s₄ : Step w o t) : False := by
  rcases step_plain_or_code s₁ with p₁ | c₁
  · have gx := (plain_growth p₁).1
    have gy := (plain_growth p₁).2
    have c₃ := step_small s₃ gy
    have p₂ := plain_of_other_key s₂ c₃ (fun he => step_ne_second (he.symm ▸ s₄))
    have gh := (plain_growth p₂).2
    have p₀ := plain_of_no_code s₀ (by intro hc; have hb := (code_bounds hc).2; omega)
    have he := plain_right_unique p₀ p₂
    rw [he] at gx; omega
  · have gay := (code_bounds c₁).2
    have p₃ := plain_of_no_code s₃ (by intro hc; have hb := (code_bounds hc).2; omega)
    have hy : y = p t a := by
      rcases p₃ with hy | ⟨_, hy⟩
      · exact hy
      · obtain ⟨l, r, he⟩ := code_shape c₁; rw [hy] at he; cases he
    obtain ⟨v, r, ll, rr, q₀, q₁, q₂, he⟩ := code_steps c₁
    rw [hy] at he
    have hh := T.p.inj he
    rw [← hh.1] at q₁
    rw [← hh.2] at q₂
    have pt : Plain a x t := by
      rcases step_plain_or_code q₂ with pq | cq
      · have gxa := (plain_growth pq).2
        exact plain_of_large_left q₁ (by omega)
      · exact plain_of_other_key q₁ cq (fun he => step_ne_second (he.symm ▸ q₀))
    have gxt := (plain_growth pt).2
    have gat := (plain_growth pt).1
    have finish (p₂ : Plain o a h) (gxh : sz x < sz h) : False := by
      have p₀ := plain_of_no_code s₀ (by intro hc; have hb := (code_bounds hc).2; omega)
      have hxa := plain_right_unique p₀ p₂
      rw [hxa] at q₂
      exact step_ne_second q₂
    rcases step_plain_or_code s₄ with p₄ | c₄
    · have hox := plain_right_unique p₄ pt
      have p₂ : Plain o a h := plain_of_no_code s₂ (by
        intro hc; rw [hox] at hc; exact no_code_after_step q₂ hc)
      apply finish p₂
      have goh := (plain_growth p₂).1
      rw [hox] at goh; exact goh
    · have gto := (code_bounds c₄).2
      have p₂ := plain_of_large_left s₂ (by omega)
      apply finish p₂
      have goh := (plain_growth p₂).1
      omega

theorem no_middle {z x h y a b o : T}
    (s₀ : Step z x h) (s₁ : Step x y a) (s₂ : Step h y b) (c : Code a b o) : False := by
  have hb : b = p h y := by
    cases s₂ with
    | raw => rfl
    | square => obtain ⟨l, r, he⟩ := code_shape c; cases he
    | hit cb =>
      have gab := (code_bounds c).1
      have gby := (code_bounds cb).2
      have ca := step_small s₁ (by omega)
      have hh := code_key_unique cb ca
      rw [hh] at s₀
      exact False.elim (step_ne_second s₀)
  obtain ⟨w, t, ll, rr, q₀, q₁, q₂, he⟩ := code_steps c
  rw [hb] at he
  have hp := T.p.inj he
  rw [← hp.1] at q₁
  rw [← hp.2] at q₂
  exact forbidden_pentagon s₀ s₁ q₁ q₂ q₀

theorem source_container_code {x y z h a b : T}
    (s₀ : Step z x h) (s₁ : Step x y a) (s₂ : Step h y b) : Code y (p a b) x := by
  cases s₁ with
  | raw => exact Code.rightRaw _ _ _ _ _ s₀ s₂
  | square => exact Code.rightSquare _ _ _ _ s₀ s₂
  | hit ca =>
    cases s₂ with
    | raw => exact Code.leftRaw _ _ _ _ _ s₀ (Step.hit ca)
    | square => exact Code.leftSquare _ _ _ _ s₀ (Step.hit ca)
    | hit cb =>
      have hh := code_key_unique cb ca
      rw [hh] at s₀
      exact False.elim (step_ne_second s₀)

theorem equation10218 (x y z : T) : eval y (eval (eval x y) (eval (eval z x) y)) = x := by
  let h := eval z x
  let a := eval x y
  let b := eval h y
  have s₀ : Step z x h := eval_step z x
  have s₁ : Step x y a := eval_step x y
  have s₂ : Step h y b := eval_step h y
  have hab : a ≠ b := by
    intro he
    rw [he] at s₁
    have hh := step_first_unique s₂ s₁
    rw [hh] at s₀
    exact step_ne_second s₀
  have hc : ¬ ∃ o, Code a b o := by
    rintro ⟨o, ho⟩
    exact no_middle s₀ s₁ s₂ ho
  change eval y (eval a b) = x
  rw [eval_raw hab hc]
  exact eval_hit (source_container_code s₀ s₁ s₂)

end submission.Austin10218

set_option autoImplicit false
namespace submission.Austin10218
abbrev Carrier := T
noncomputable def mul : Carrier → Carrier → Carrier := eval
noncomputable def opposite (a b : Carrier) : Carrier := mul b a
def embed : Nat → Carrier := tower
theorem embed_injective (n j : Nat) (h : embed n = embed j) : n = j := tower_injective n j h
theorem equation35685 (x y z : Carrier) :
    opposite (opposite (opposite y (opposite x z)) (opposite y x)) y = x :=
  equation10218 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, op y (op (op x y) (op (op z x) y)) = x) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation10218, embed_injective⟩
end submission.Austin10218

namespace submission
abbrev CM := Austin10218.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin10218.embed n = Austin10218.embed j) : n = j :=
  Austin10218.embed_injective n j h
end CM
noncomputable instance modelMagma : Magma CM := ⟨Austin10218.opposite⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin10218.equation35685 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin10218.embed_injective 0 1
      (h (submission.Austin10218.embed 0) (submission.Austin10218.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

