import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false

namespace submission.Austin6912

inductive Color where
  | c0 | c1 | c2 | c3 | c4
  deriving DecidableEq

def Color.next : Color → Color
  | .c0 => .c1 | .c1 => .c2 | .c2 => .c3 | .c3 => .c4 | .c4 => .c0

inductive Tree where
  | e : Tree
  | atom : Nat → Color → Tree
  | node : Tree → Tree → Color → Tree
  deriving DecidableEq

open Tree Color

def k : Tree → Tree
  | e => e
  | atom n c => atom n c.next
  | node a b c => node a b c.next

abbrev k2 (a : Tree) := k (k a)
abbrev k3 (a : Tree) := k (k (k a))
abbrev k4 (a : Tree) := k (k (k (k a)))
abbrev raw (a b : Tree) := node a b c0

def sz : Tree → Nat
  | e => 0
  | atom _ _ => 1
  | node a b _ => sz a + sz b + 2

@[simp] theorem k_e : k e = e := rfl
@[simp] theorem k_five (a : Tree) : k (k (k (k (k a)))) = a := by
  cases a with
  | e => rfl
  | atom n c => cases c <;> rfl
  | node a b c => cases c <;> rfl
@[simp] theorem sz_k (a : Tree) : sz (k a) = sz a := by cases a <;> rfl

theorem k_injective {a b : Tree} (h : k a = k b) : a = b := by
  have hh := congrArg k4 h
  simpa only [k4, k_five] using hh

@[simp] theorem k_eq_e (a : Tree) : k a = e ↔ a = e := by
  constructor
  · intro h
    exact k_injective h
  · intro h
    subst a
    rfl

theorem k_ne_self {a : Tree} (ha : a ≠ e) : k a ≠ a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, Color.next]
  | node a b c => cases c <;> simp [k, Color.next]

theorem k2_ne_self {a : Tree} (ha : a ≠ e) : k2 a ≠ a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k2, k, Color.next]
  | node a b c => cases c <;> simp [k2, k, Color.next]

theorem k3_ne_self {a : Tree} (ha : a ≠ e) : k3 a ≠ a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k3, k, Color.next]
  | node a b c => cases c <;> simp [k3, k, Color.next]

mutual
def f (a b : Tree) : Tree :=
  if a = e then k2 b
  else if b = e then k3 a
  else if a = b then e
  else if b = k2 a then k a
  else match a with
    | node t key c1 =>
      if key = b then
        match inverse key t with
        | some z => k4 z
        | none => raw a b
      else raw a b
    | _ => raw a b
termination_by sz a
decreasing_by all_goals simp_wf; simp [sz]; omega

def inverse (a out : Tree) : Option Tree :=
  if a = e then some (k3 out)
  else if out = e then some a
  else if out = k3 a then some e
  else if out = k a then some (k2 a)
  else
    let fallback := match a with
      | node t key c1 => if f key (k out) = t then some key else none
      | _ => none
    match out with
    | node a' b c0 => if a' = a then some b else fallback
    | _ => fallback
termination_by sz a
decreasing_by all_goals simp_wf; simp [sz]; omega
end

def NF : Tree → Prop
  | e => True
  | atom _ _ => True
  | node a b _ => NF a ∧ NF b ∧ f a b = raw a b

@[simp] theorem nf_k (a : Tree) : NF (k a) ↔ NF a := by cases a <;> rfl

theorem nf_node_left {a b : Tree} {c : Color} (h : NF (node a b c)) : NF a := h.1
theorem nf_node_right {a b : Tree} {c : Color} (h : NF (node a b c)) : NF b := h.2.1
theorem nf_node_raw {a b : Tree} {c : Color} (h : NF (node a b c)) : f a b = raw a b := h.2.2

@[simp] theorem f_e_left (b : Tree) : f e b = k2 b := by rw [f.eq_def]; simp
@[simp] theorem f_e_right (a : Tree) : f a e = k3 a := by
  rw [f.eq_def]
  split
  · subst a; rfl
  · simp

@[simp] theorem f_square (a : Tree) : f a a = e := by
  rw [f.eq_def]
  by_cases h : a = e
  · subst a; rfl
  · simp [h]

@[simp] theorem f_orbit (a : Tree) : f a (k2 a) = k a := by
  rw [f.eq_def]
  by_cases h : a = e
  · subst a; rfl
  · have hh := k2_ne_self h
    simp [h, hh, Ne.symm hh]

end submission.Austin6912

set_option autoImplicit false

namespace submission.Austin6912
open Tree Color

inductive FCases (a b out : Tree) : Prop where
  | left (h : a = e) (ho : out = k2 b)
  | right (h : b = e) (ho : out = k3 a)
  | square (h : a = b) (ho : out = e)
  | orbit (h : b = k2 a) (ho : out = k a)
  | code (t z : Tree) (ha : a = node t b c1)
      (hi : inverse b t = some z) (ho : out = k4 z)
  | raw (ho : out = raw a b)

theorem f_cases (a b : Tree) : FCases a b (f a b) := by
  rw [f.eq_def]
  split
  · exact .left ‹a = e› rfl
  · split
    · exact .right ‹b = e› rfl
    · split
      · exact .square ‹a = b› rfl
      · split
        · exact .orbit ‹b = k2 a› rfl
        · split
          · split
            · rename_i hk
              cases hk
              split
              · exact .code _ _ rfl (by assumption) rfl
              · exact .raw rfl
            · exact .raw rfl
          · exact .raw rfl

inductive InvCases (a out b : Tree) : Prop where
  | left (ha : a = e) (hb : b = k3 out)
  | square (ho : out = e) (hb : b = a)
  | right (ho : out = k3 a) (hb : b = e)
  | orbit (ho : out = k a) (hb : b = k2 a)
  | raw (ho : out = raw a b)
  | code (t : Tree) (ha : a = node t b c1) (hf : f b (k out) = t)

theorem inverse_fallback_cases {a out b : Tree}
    (h : (match a with
      | node t key c1 => if f key (k out) = t then some key else none
      | _ => none) = some b) : ∃ t, a = node t b c1 ∧ f b (k out) = t := by
  split at h
  · split at h
    · have hb := Option.some.inj h
      cases hb
      exact ⟨_, rfl, by first | assumption | rfl⟩
    · contradiction
  · contradiction

theorem inverse_cases {a out b : Tree} (h : inverse a out = some b) :
    InvCases a out b := by
  rw [inverse.eq_def] at h
  split at h
  · exact .left ‹a = e› (Option.some.inj h).symm
  · split at h
    · exact .square ‹out = e› (Option.some.inj h).symm
    · split at h
      · exact .right ‹out = k3 a› (Option.some.inj h).symm
      · split at h
        · exact .orbit ‹out = k a› (Option.some.inj h).symm
        · dsimp only at h
          split at h
          · split at h
            · rename_i ha
              have hb := Option.some.inj h
              cases ha
              cases hb
              exact .raw rfl
            · obtain ⟨t, ha, hf⟩ := inverse_fallback_cases h
              exact .code t ha hf
          · obtain ⟨t, ha, hf⟩ := inverse_fallback_cases h
            exact .code t ha hf

theorem inverse_size {a out b : Tree} (h : inverse a out = some b) :
    sz b ≤ max (sz a) (sz out) := by
  cases inverse_cases h with
  | left ha hb => subst a; subst b; simp [k3, sz]
  | square ho hb => subst out; subst b; simp [sz]
  | right ho hb => subst b; simp [sz]
  | orbit ho hb => subst b; simp only [k2, sz_k]; omega
  | raw ho => subst out; simp [raw, sz]; omega
  | code t ha hf => subst a; simp [sz]; omega

theorem code_output_size {a b t z : Tree}
    (ha : a = node t b c1) (hi : inverse b t = some z) : sz (k4 z) < sz a := by
  have h := inverse_size hi
  subst a
  simp only [k4, sz_k, sz]
  omega

theorem large_right (a b : Tree) (h : sz a < sz b) : sz b ≤ sz (f a b) := by
  cases f_cases a b with
  | left ha ho => rw [ho]; simp [k2]
  | right hb ho => subst b; simp [sz] at h
  | square hab ho => subst b; omega
  | orbit hb ho => subst b; simp [k2] at h
  | code t z ha hi ho => subst a; simp [sz] at h; omega
  | raw ho => rw [ho]; simp [raw, sz]; omega

theorem nf_raw_ne_e {a b : Tree} {c : Color} (h : NF (node a b c)) :
    a ≠ e ∧ b ≠ e := by
  have hh := nf_node_raw h
  constructor
  · intro he
    subst a
    have hs := congrArg sz hh
    simp [raw, sz, k2] at hs
  · intro he
    subst b
    have hs := congrArg sz hh
    simp [raw, sz, k3] at hs

theorem f_fixed {a b : Tree} (h : f a b = a) : a = e ∧ b = e := by
  cases f_cases a b with
  | left ha ho =>
    subst a
    have hb : b = e := by simpa only [h, k2, k_eq_e] using ho.symm
    exact ⟨rfl, hb⟩
  | right hb ho =>
    subst b
    by_cases ha : a = e
    · exact ⟨ha, rfl⟩
    · exact False.elim (k3_ne_self ha (ho.symm.trans h))
  | square hab ho =>
    have ha := h.symm.trans ho
    exact ⟨ha, hab.symm.trans ha⟩
  | orbit hb ho =>
    by_cases ha : a = e
    · subst a; exact ⟨rfl, by simpa only [k2, k_e] using hb⟩
    · exact False.elim (k_ne_self ha (ho.symm.trans h))
  | code t z ha hi ho =>
    have hs := code_output_size ha hi
    rw [← ho, h] at hs
    omega
  | raw ho =>
    have hs := congrArg sz (h.symm.trans ho)
    simp [raw, sz] at hs
    omega

end submission.Austin6912

set_option autoImplicit false

namespace submission.Austin6912
open Tree Color

@[simp] theorem inverse_e_left (out : Tree) : inverse e out = some (k3 out) := by
  rw [inverse.eq_def]; simp

@[simp] theorem inverse_e (a : Tree) : inverse a e = some a := by
  rw [inverse.eq_def]
  by_cases h : a = e
  · subst a; rfl
  · simp [h]

@[simp] theorem inverse_k3 (a : Tree) : inverse a (k3 a) = some e := by
  rw [inverse.eq_def]
  by_cases h : a = e
  · subst a; rfl
  · have hn : k3 a ≠ e := fun he => h (k_injective (k_injective (k_injective he)))
    simp only [h, hn, if_false, if_true]

@[simp] theorem inverse_k (a : Tree) : inverse a (k a) = some (k2 a) := by
  rw [inverse.eq_def]
  by_cases h : a = e
  · subst a; rfl
  · have hn : k a ≠ e := fun he => h (k_injective he)
    have h3 : k a ≠ k3 a := by
      intro he
      exact k2_ne_self h (k_injective he).symm
    simp only [h, hn, h3, if_false, if_true]

theorem inverse_raw {a b : Tree} (hf : f a b = raw a b) :
    inverse a (raw a b) = some b := by
  have ha : a ≠ e := by
    intro he
    subst a
    have hs := congrArg sz hf
    simp [k2, raw, sz] at hs
  have h3 : raw a b ≠ k3 a := by
    intro he
    have hs := congrArg sz he
    simp [k3, raw, sz] at hs
    omega
  have h1 : raw a b ≠ k a := by
    intro he
    have hs := congrArg sz he
    simp [raw, sz] at hs
    omega
  rw [inverse.eq_def]
  simp [ha, h3, h1, raw]

theorem nf_raw_not_orbit {a b : Tree} {c : Color} (h : NF (node a b c)) :
    b ≠ k2 a := by
  intro he
  have hh := nf_node_raw h
  subst b
  have hs := congrArg sz hh
  simp [k2, raw, sz] at hs
  omega

theorem f_code {t b z : Tree} (ha : NF (node t b c1))
    (hi : inverse b t = some z) : f (node t b c1) b = k4 z := by
  have hb : b ≠ e := (nf_raw_ne_e ha).2
  have hab : node t b c1 ≠ b := by
    intro he
    have hs := congrArg sz he
    simp [sz] at hs
    omega
  have horbit : b ≠ k2 (node t b c1) := by
    intro he
    have hs := congrArg sz he
    simp [k2, sz] at hs
    omega
  rw [f.eq_def]
  simp [hb, hab, horbit, hi]

theorem inverse_small {t key out : Tree} (ho : out ≠ e)
    (hs : sz out < sz (node t key c1)) (hf : f key (k out) = t) :
    inverse (node t key c1) out = some key := by
  have h3 : out ≠ k3 (node t key c1) := by
    intro he
    rw [he] at hs
    simp only [k3, sz_k] at hs
    omega
  have h1 : out ≠ k (node t key c1) := by
    intro he
    rw [he] at hs
    simp only [sz_k] at hs
    omega
  cases out with
  | e => exact False.elim (ho rfl)
  | atom n c =>
    rw [inverse.eq_def]
    simp [ho, h3, h1, hf]
  | node a b c =>
    have ha : a ≠ node t key c1 := by
      intro he
      rw [he] at hs
      simp only [sz] at hs
      omega
    cases c <;> rw [inverse.eq_def] <;> simp [ho, h3, h1, ha, hf]

end submission.Austin6912

set_option autoImplicit false

namespace submission.Austin6912
open Tree Color

def Correct (a : Tree) : Prop :=
  (∀ b, NF b → NF (f a b) ∧ inverse a (f a b) = some b) ∧
  (∀ out b, NF out → inverse a out = some b → NF b ∧ f a b = out)

theorem correct_bound (n : Nat) : ∀ a, sz a < n → NF a → Correct a := by
  induction n with
  | zero => intro a h; omega
  | succ n ih =>
    intro a hn hfa
    have small : ∀ b, sz b < sz a → NF b → Correct b := by
      intro b hb hfb
      exact ih b (by omega) hfb
    have sound : ∀ out b, NF out → inverse a out = some b → NF b ∧ f a b = out := by
      intro out b hout hi
      cases inverse_cases hi with
      | left ha hb =>
        subst a
        subst b
        constructor
        · simpa only [k3, nf_k] using hout
        · simp only [f_e_left, k2, k3, k_five]
      | square ho hb =>
        subst out
        subst b
        exact ⟨hfa, f_square a⟩
      | right ho hb =>
        subst b
        exact ⟨True.intro, (f_e_right a).trans ho.symm⟩
      | orbit ho hb =>
        subst b
        exact ⟨by simpa only [k2, nf_k] using hfa, (f_orbit a).trans ho.symm⟩
      | raw ho =>
        subst out
        exact ⟨nf_node_right hout, nf_node_raw hout⟩
      | code t ha hf =>
        subst a
        have hb := nf_node_right hfa
        have cb := small b (by simp [sz]; omega) hb
        have hk : NF (k out) := (nf_k out).2 hout
        have hrec : inverse b t = some (k out) := by
          rw [← hf]
          exact (cb.1 (k out) hk).2
        refine ⟨hb, ?_⟩
        rw [f_code hfa hrec]
        exact k_five out
    refine ⟨?_, sound⟩
    intro b hfb
    cases f_cases a b with
    | left ha ho =>
      subst a
      rw [ho]
      constructor
      · simpa only [k2, nf_k] using hfb
      · simp only [inverse_e_left, k3, k2, k_five]
    | right hb ho =>
      subst b
      rw [ho]
      exact ⟨by simpa only [k3, nf_k] using hfa, inverse_k3 a⟩
    | square hab ho =>
      subst b
      rw [ho]
      exact ⟨True.intro, inverse_e a⟩
    | orbit hb ho =>
      subst b
      rw [ho]
      exact ⟨(nf_k a).2 hfa, inverse_k a⟩
    | code t z ha hi ho =>
      subst a
      have ht := nf_node_left hfa
      have cb := small b (by simp [sz]; omega) hfb
      obtain ⟨hz, hf⟩ := cb.2 t z ht hi
      have hze : z ≠ e := by
        intro he
        subst z
        have ht' : t = k3 b := by simpa only [f_e_right] using hf.symm
        have hbad := nf_raw_not_orbit hfa
        apply hbad
        rw [ht']
        simp only [k2, k3, k_five]
      have hoe : k4 z ≠ e := by
        intro he
        exact hze (k_injective (k_injective (k_injective (k_injective he))))
      have hsize : sz (k4 z) < sz (node t b c1) := code_output_size rfl hi
      have hstep : f b (k (k4 z)) = t := by simpa only [k4, k_five] using hf
      rw [ho]
      exact ⟨by simpa only [k4, nf_k] using hz, inverse_small hoe hsize hstep⟩
    | raw ho =>
      rw [ho]
      exact ⟨⟨hfa, hfb, ho⟩, inverse_raw ho⟩

theorem correct {a : Tree} (ha : NF a) : Correct a :=
  correct_bound (sz a + 1) a (by omega) ha

theorem f_nf {a b : Tree} (ha : NF a) (hb : NF b) : NF (f a b) :=
  ((correct ha).1 b hb).1

theorem inverse_complete {a b : Tree} (ha : NF a) (hb : NF b) :
    inverse a (f a b) = some b := ((correct ha).1 b hb).2

theorem inverse_sound {a out b : Tree} (ha : NF a) (ho : NF out)
    (h : inverse a out = some b) : NF b ∧ f a b = out := (correct ha).2 out b ho h

theorem f_left_cancel {a b c : Tree} (ha : NF a) (hb : NF b) (hc : NF c)
    (h : f a b = f a c) : b = c := by
  have hi := congrArg (inverse a) h
  rw [inverse_complete ha hb, inverse_complete ha hc] at hi
  exact Option.some.inj hi


end submission.Austin6912

set_option autoImplicit false

namespace submission.Austin6912
open Tree Color

theorem f_reverse_orbit (a : Tree) : f (k3 a) a = k4 a := by
  have h := f_orbit (k3 a)
  simpa only [k2, k3, k4, k_five] using h

theorem f_not_code {x y t : Tree} (hy : NF y) : f x y ≠ node t x c1 := by
  intro he
  cases f_cases x y with
  | left hx ho =>
    subst x
    have hn : NF (k2 y) := by simpa only [k2, nf_k] using hy
    rw [ho.symm.trans he] at hn
    exact (nf_raw_ne_e hn).2 rfl
  | right hy0 ho =>
    have hs := congrArg sz (ho.symm.trans he)
    simp [k3, sz] at hs
    omega
  | square hxy ho => cases ho.symm.trans he
  | orbit hy2 ho =>
    have hs := congrArg sz (ho.symm.trans he)
    simp [sz] at hs
    omega
  | code u z hx hi ho =>
    have hs := code_output_size hx hi
    rw [← ho, he] at hs
    simp [sz] at hs
    omega
  | raw ho => cases ho.symm.trans he

theorem recovery {x y : Tree} (hx : NF x) (hy : NF y) :
    f (k (f (f x y) x)) x = k4 y := by
  by_cases hx0 : x = e
  · subst x
    simp only [f_e_left, f_e_right, k2, k3, k4, k_five]
  have hu : NF (f x y) := f_nf hx hy
  cases f_cases (f x y) x with
  | left he ho =>
    have hyx : y = x := f_left_cancel hx hy hx (he.trans (f_square x).symm)
    subst y
    rw [ho]
    exact f_reverse_orbit x
  | right he ho => exact False.elim (hx0 he)
  | square he ho => exact False.elim (hx0 (f_fixed he).1)
  | orbit he ho =>
    have hf : f x y = k3 x := by
      have hh := congrArg k3 he
      simpa only [k2, k3, k_five] using hh.symm
    have hye : y = e := f_left_cancel hx hy True.intro (hf.trans (f_e_right x).symm)
    rw [ho]
    change f (k2 (f x y)) x = k4 y
    rw [← he, f_square, hye]
    rfl
  | code t z he hi ho => exact False.elim (f_not_code hy he)
  | raw ho =>
    have hv := f_nf hu hx
    rw [ho] at hv
    rw [ho]
    exact f_code hv (inverse_complete hx hy)

def star (x y : Tree) : Tree := k (f y x)

theorem star_nf {x y : Tree} (hx : NF x) (hy : NF y) : NF (star x y) :=
  (nf_k (f y x)).2 (f_nf hy hx)

@[simp] theorem star_square (x : Tree) : star x x = e := by
  simp only [star, f_square, k_e]

theorem star_e_star (x y : Tree) : star e (star x y) = f y x := by
  simp only [star, f_e_right, k3, k_five]

theorem source {x y z : Tree} (hx : NF x) (hy : NF y) :
    star y (star y (star (star z z) (star x y))) = x := by
  rw [star_square, star_e_star]
  change k (f (k (f (f y x) y)) y) = x
  rw [recovery hy hx]
  exact k_five x

def Carrier := {t : Tree // NF t}
def op (x y : Carrier) : Carrier := ⟨star x.1 y.1, star_nf x.2 y.2⟩

theorem source_holds (x y z : Carrier) : op y (op y (op (op z z) (op x y))) = x := by
  apply Subtype.ext
  exact source x.2 y.2

def embed (n : Nat) : Carrier := ⟨atom n c0, True.intro⟩

theorem embed_injective (m n : Nat) (h : embed m = embed n) : m = n := by
  have hh := congrArg Subtype.val h
  exact (Tree.atom.inj hh).1

def opposite (x y : Carrier) : Carrier := op y x

theorem dual_holds (x y z : Carrier) :
    opposite (opposite (opposite (opposite y x) (opposite z z)) y) y = x :=
  source_holds x y z

/-- An explicit embedding of Nat, independently of the nontriviality Goal. -/
theorem infinite_model : ∃ i : Nat → Carrier, ∀ m n, i m = i n → m = n :=
  ⟨embed, embed_injective⟩


end submission.Austin6912

namespace submission
abbrev CM := Austin6912.Carrier
namespace CM
/-- This model contains an injective image of every natural number. -/
theorem tower_injective (m n : Nat)
    (h : Austin6912.embed m = Austin6912.embed n) : m = n :=
  Austin6912.embed_injective m n h
end CM
instance modelMagma : Magma CM := ⟨Austin6912.op⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin6912.source_holds x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin6912.embed_injective 0 1
      (h (submission.Austin6912.embed 0) (submission.Austin6912.embed 1))
    exact Nat.noConfusion bad

example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

