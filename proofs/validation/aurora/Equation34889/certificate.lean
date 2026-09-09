import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin11082

inductive Color where
  | c0 | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq
def Color.next : Color → Color
  | .c0 => .c1 | .c1 => .c2 | .c2 => .c3 | .c3 => .c4 | .c4 => .c5 | .c5 => .c0
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
abbrev k5 (a : Tree) := k (k (k (k (k a))))
abbrev raw (a b : Tree) := node a b c0
def sz : Tree → Nat
  | e => 0
  | atom _ _ => 1
  | node a b _ => sz a + sz b + 2
@[simp] theorem k_e : k e = e := rfl
@[simp] theorem k_six (a : Tree) : k (k (k (k (k (k a))))) = a := by
  cases a with
  | e => rfl
  | atom n c => cases c <;> rfl
  | node a b c => cases c <;> rfl
@[simp] theorem sz_k (a : Tree) : sz (k a) = sz a := by cases a <;> rfl
theorem sz_pos {a : Tree} (ha : a ≠ e) : 0 < sz a := by
  cases a <;> simp [sz] at * <;> omega
theorem k_injective {a b : Tree} (h : k a = k b) : a = b := by
  have hh := congrArg k5 h
  simpa only [k5, k_six] using hh

def q (a b : Tree) : Tree :=
  if a = e then k b
  else if b = e then k a
  else if b = a ∨ b = k3 a then e
  else if b = k a ∨ b = k4 a then k4 a
  else if b = k5 a then k3 a
  else match a with
    | node u x c1 => if q x b = u then x else raw a b
    | _ => raw a b
termination_by sz a
decreasing_by all_goals simp_wf; simp [sz]; omega

def NF : Tree → Prop
  | e => True
  | atom _ _ => True
  | node a b _ => NF a ∧ NF b ∧ q a b = raw a b
@[simp] theorem nf_k (a : Tree) : NF (k a) ↔ NF a := by cases a <;> rfl
@[simp] theorem q_e_left (b : Tree) : q e b = k b := by rw [q.eq_def]; simp
@[simp] theorem q_e_right (a : Tree) : q a e = k a := by
  rw [q.eq_def]
  split
  · subst a; rfl
  · simp
@[simp] theorem q_square (a : Tree) : q a a = e := by
  rw [q.eq_def]
  by_cases h : a = e
  · subst a; rfl
  · simp [h]

end submission.Austin11082

set_option autoImplicit false
namespace submission.Austin11082
open Tree Color

inductive QCase (a b out : Tree) : Prop where
  | left : a = e → out = k b → QCase a b out
  | right : b = e → out = k a → QCase a b out
  | zero : (b = a ∨ b = k3 a) → out = e → QCase a b out
  | orbit : (b = k a ∨ b = k4 a) → out = k4 a → QCase a b out
  | reverse : b = k5 a → out = k3 a → QCase a b out
  | code (u x : Tree) : a = node u x c1 → q x b = u → out = x → QCase a b out
  | raw : out = raw a b → QCase a b out

theorem q_cases (a b : Tree) : QCase a b (q a b) := by
  rw [q.eq_def]
  split
  · exact .left (by assumption) rfl
  · split
    · exact .right (by assumption) rfl
    · split
      · exact .zero (by assumption) rfl
      · split
        · exact .orbit (by assumption) rfl
        · split
          · exact .reverse (by assumption) rfl
          · split
            · split
              · exact .code _ _ rfl (by assumption) rfl
              · exact .raw rfl
            · exact .raw rfl

theorem large_right_bound (n : Nat) : ∀ a, sz a < n → ∀ b, sz a < sz b → sz b ≤ sz (q a b) := by
  induction n with
  | zero => intro a h; omega
  | succ n ih =>
    intro a hn b hab
    cases q_cases a b with
    | left ha ho => rw [ho, sz_k]
                    exact Nat.le_refl _
    | right hb ho => subst b; simp [sz] at hab
    | zero hb ho =>
      rcases hb with hb | hb
      · subst b; omega
      · rw [hb] at hab; simp only [k3, sz_k] at hab; omega
    | orbit hb ho =>
      rcases hb with hb | hb
      · rw [hb, sz_k] at hab; omega
      · rw [hb] at hab; simp only [k4, sz_k] at hab; omega
    | reverse hb ho => rw [hb] at hab; simp only [k5, sz_k] at hab; omega
    | code u x ha hx ho =>
      subst a
      have h := ih x (by simp [sz] at hn ⊢; omega) b (by simp [sz] at hab; omega)
      rw [hx] at h
      simp [sz] at hab
      omega
    | raw ho => rw [ho]; simp [sz]; omega

theorem large_right {a b : Tree} (h : sz a < sz b) : sz b ≤ sz (q a b) :=
  large_right_bound (sz a + 1) a (by omega) b h

theorem code_right_small {u x b : Tree} (h : q x b = u) :
    sz b < sz (node u x c1) := by
  by_cases hh : sz x < sz b
  · have hb := large_right hh
    rw [h] at hb
    simp [sz]; omega
  · simp [sz]; omega

theorem q_nf {a b : Tree} (ha : NF a) (hb : NF b) : NF (q a b) := by
  cases q_cases a b with
  | left he ho => rw [ho]; exact (nf_k b).2 hb
  | right he ho => rw [ho]; exact (nf_k a).2 ha
  | zero he ho => rw [ho]; exact True.intro
  | orbit he ho => rw [ho]; simpa only [k4, nf_k] using ha
  | reverse he ho => rw [ho]; simpa only [k3, nf_k] using ha
  | code u x he hq ho => subst a; rw [ho]; exact ha.2.1
  | raw ho => rw [ho]; exact ⟨ha, hb, ho⟩

theorem nf_right_ne_e {a b : Tree} {c : Color} (h : NF (node a b c)) : b ≠ e := by
  intro he
  subst b
  have hh := congrArg sz h.2.2
  simp only [q_e_right, sz_k, sz] at hh
  omega

end submission.Austin11082

set_option autoImplicit false
namespace submission.Austin11082
open Tree Color

theorem ne10 {a : Tree} (ha : a ≠ e) : k a ≠ a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne13 {a : Tree} (ha : a ≠ e) : k a ≠ k3 a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne40 {a : Tree} (ha : a ≠ e) : k4 a ≠ a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne43 {a : Tree} (ha : a ≠ e) : k4 a ≠ k3 a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne50 {a : Tree} (ha : a ≠ e) : k5 a ≠ a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne53 {a : Tree} (ha : a ≠ e) : k5 a ≠ k3 a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne51 {a : Tree} (ha : a ≠ e) : k5 a ≠ k a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne54 {a : Tree} (ha : a ≠ e) : k5 a ≠ k4 a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

@[simp] theorem k_eq_e (a : Tree) : k a = e ↔ a = e := by
  constructor
  · intro h; exact k_injective h
  · intro h; subst a; rfl

@[simp] theorem q_k1 (a : Tree) : q a (k a) = k4 a := by
  rw [q.eq_def]
  by_cases ha : a = e
  · subst a; rfl
  · have hne : k a ≠ e := by intro h; exact ha (k_injective h)
    simp only [ha, hne, if_false, ne10 ha, ne13 ha, or_true, or_false, true_or, false_or, if_true]

@[simp] theorem q_k3 (a : Tree) : q a (k3 a) = e := by
  rw [q.eq_def]
  by_cases ha : a = e
  · subst a; rfl
  · have hne : k3 a ≠ e := by intro h; exact ha (k_injective (k_injective (k_injective h)))
    simp only [ha, hne, if_false, or_true, or_false, true_or, false_or, if_true]

@[simp] theorem q_k4 (a : Tree) : q a (k4 a) = k4 a := by
  rw [q.eq_def]
  by_cases ha : a = e
  · subst a; rfl
  · have hne : k4 a ≠ e := by intro h; exact ha (k_injective (k_injective (k_injective (k_injective h))))
    simp only [ha, hne, if_false, ne40 ha, ne43 ha, or_true, or_false, true_or, false_or, if_true]

@[simp] theorem q_k5 (a : Tree) : q a (k5 a) = k3 a := by
  rw [q.eq_def]
  by_cases ha : a = e
  · subst a; rfl
  · have hne : k5 a ≠ e := by intro h; exact ha (k_injective (k_injective (k_injective (k_injective (k_injective h)))))
    simp only [ha, hne, if_false, ne50 ha, ne53 ha, ne51 ha, ne54 ha, or_true, or_false, true_or, false_or, if_true]

theorem q_reverse (a : Tree) : q (k a) a = k4 a := by
  have h := q_k5 (k a)
  simpa only [k3, k4, k5, k_six] using h

theorem ne30 {a : Tree} (ha : a ≠ e) : k3 a ≠ a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne21 {a : Tree} (ha : a ≠ e) : k2 a ≠ k a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne24 {a : Tree} (ha : a ≠ e) : k2 a ≠ k4 a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne23 {a : Tree} (ha : a ≠ e) : k2 a ≠ k3 a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

theorem ne41 {a : Tree} (ha : a ≠ e) : k4 a ≠ k a := by
  cases a with
  | e => exact False.elim (ha rfl)
  | atom n c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]
  | node u v c => cases c <;> simp [k, k2, k3, k4, k5, Color.next]

end submission.Austin11082

set_option autoImplicit false
namespace submission.Austin11082
open Tree Color

theorem output_same_size {a b : Tree} (ha : a ≠ e) (hs : sz (q a b) = sz a) :
    (b = e ∧ q a b = k a) ∨
    ((b = k a ∨ b = k4 a) ∧ q a b = k4 a) ∨
    (b = k5 a ∧ q a b = k3 a) := by
  cases q_cases a b with
  | left he ho => exact False.elim (ha he)
  | right he ho => exact .inl ⟨he, ho⟩
  | zero he ho => have hp := sz_pos ha; rw [ho] at hs; simp [sz] at hs; omega
  | orbit he ho => exact .inr (.inl ⟨he, ho⟩)
  | reverse he ho => exact .inr (.inr ⟨he, ho⟩)
  | code u x he hq ho => subst a; rw [ho] at hs; simp [sz] at hs; omega
  | raw ho => rw [ho] at hs; simp [sz] at hs; omega

theorem q_zero_nf {a b : Tree} (ha : NF a) (hne : a ≠ e) (h : q a b = e) :
    b = a ∨ b = k3 a := by
  cases q_cases a b with
  | left he ho => exact False.elim (hne he)
  | right he ho => exact False.elim (hne (k_injective (ho.symm.trans h)))
  | zero he ho => exact he
  | orbit he ho =>
    exact False.elim (hne (k_injective (k_injective (k_injective (k_injective (ho.symm.trans h))))))
  | reverse he ho =>
    exact False.elim (hne (k_injective (k_injective (k_injective (ho.symm.trans h)))))
  | code u x he hq ho =>
    subst a
    exact False.elim (nf_right_ne_e ha (ho.symm.trans h))
  | raw ho => cases ho.symm.trans h

theorem middle_code_impossible {x z u t : Tree} (hx : x ≠ e)
    (he : q x z = node u t c1) (hq : q t x = u) : False := by
  have hs := code_right_small hq
  rw [← he] at hs
  cases q_cases x z with
  | left h ho => exact hx h
  | right h ho => rw [ho, sz_k] at hs; omega
  | zero h ho => cases ho.symm.trans he
  | orbit h ho => rw [ho] at hs; simp only [k4, sz_k] at hs; omega
  | reverse h ho => rw [ho] at hs; simp only [k3, sz_k] at hs; omega
  | code v s h hq ho => subst x; rw [ho] at hs; simp [sz] at hs; omega
  | raw ho => cases ho.symm.trans he

theorem q_code {u x z : Tree} (hn : NF (node u x c1)) (hq : q x z = u) :
    q (node u x c1) z = x := by
  have hs : sz z < sz (node u x c1) := code_right_small hq
  have hz : z ≠ e := by
    intro he
    subst z
    have hu : u = k x := hq.symm.trans (q_e_right x)
    have hh := congrArg sz hn.2.2
    rw [hu, q_reverse] at hh
    simp only [k4, sz_k, sz] at hh
    omega
  have h0 : z ≠ node u x c1 := by
    intro he; have hh := congrArg sz he; omega
  have h1 : z ≠ k (node u x c1) := by
    intro he; have hh := congrArg sz he; simp only [sz_k] at hh; omega
  have h3 : z ≠ k3 (node u x c1) := by
    intro he; have hh := congrArg sz he; simp only [k3, sz_k] at hh; omega
  have h4 : z ≠ k4 (node u x c1) := by
    intro he; have hh := congrArg sz he; simp only [k4, sz_k] at hh; omega
  have h5 : z ≠ k5 (node u x c1) := by
    intro he; have hh := congrArg sz he; simp only [k5, sz_k] at hh; omega
  have he : node u x c1 ≠ e := by intro h; cases h
  rw [q.eq_def]
  simp only [he, hz, h0, h1, h3, h4, h5, hq,
    false_or, or_false, if_false, if_true]

theorem q_ne0 {a b : Tree} (ha : a ≠ e) : q a b ≠ a := by
  intro h
  obtain ⟨hz, ho⟩ | ⟨hz, ho⟩ | ⟨hz, ho⟩ := output_same_size ha
    (congrArg sz h)
  · exact (ne10 ha) (ho.symm.trans h)
  · exact (ne40 ha) (ho.symm.trans h)
  · exact (ne30 ha) (ho.symm.trans h)

theorem q_ne2 {a b : Tree} (ha : a ≠ e) : q a b ≠ k2 a := by
  intro h
  obtain ⟨hz, ho⟩ | ⟨hz, ho⟩ | ⟨hz, ho⟩ := output_same_size ha
    (by rw [h]; simp only [k2, k3, k4, k5, sz_k])
  · exact ((ne21 ha).symm) (ho.symm.trans h)
  · exact ((ne24 ha).symm) (ho.symm.trans h)
  · exact ((ne23 ha).symm) (ho.symm.trans h)

theorem q_ne5 {a b : Tree} (ha : a ≠ e) : q a b ≠ k5 a := by
  intro h
  obtain ⟨hz, ho⟩ | ⟨hz, ho⟩ | ⟨hz, ho⟩ := output_same_size ha
    (by rw [h]; simp only [k2, k3, k4, k5, sz_k])
  · exact ((ne51 ha).symm) (ho.symm.trans h)
  · exact ((ne54 ha).symm) (ho.symm.trans h)
  · exact ((ne53 ha).symm) (ho.symm.trans h)

theorem q_eq_k1 {a b : Tree} (ha : a ≠ e) (h : q a b = k a) : b = e := by
  obtain ⟨hz, ho⟩ | ⟨hz, ho⟩ | ⟨hz, ho⟩ := output_same_size ha
    (by rw [h]; simp only [k2, k3, k4, k5, sz_k])
  · exact hz
  · exact False.elim ((ne41 ha) (ho.symm.trans h))
  · exact False.elim (((ne13 ha).symm) (ho.symm.trans h))

theorem q_eq_k3 {a b : Tree} (ha : a ≠ e) (h : q a b = k3 a) : b = k5 a := by
  obtain ⟨hz, ho⟩ | ⟨hz, ho⟩ | ⟨hz, ho⟩ := output_same_size ha
    (by rw [h]; simp only [k2, k3, k4, k5, sz_k])
  · exact False.elim ((ne13 ha) (ho.symm.trans h))
  · exact False.elim ((ne43 ha) (ho.symm.trans h))
  · exact hz

end submission.Austin11082

set_option autoImplicit false
namespace submission.Austin11082
open Tree Color

theorem raw_recovery {x z : Tree} (hx : NF x) (hz : NF z)
    (h : q (q x z) x = raw (q x z) x) : q (k (q (q x z) x)) z = x := by
  have hn := q_nf (q_nf hx hz) hx
  rw [h] at hn ⊢
  exact q_code hn rfl

theorem recovery {x z : Tree} (hx : NF x) (hz : NF z) :
    q (k (q (q x z) x)) z = x := by
  by_cases hx0 : x = e
  · subst x
    rw [q_e_left, q_e_right]
    have h := q_k3 (k3 z)
    simpa only [k3, k_six] using h
  cases q_cases (q x z) x with
  | left he ho =>
    rcases q_zero_nf hx hx0 he with hz0 | hz3
    · rw [ho, hz0]
      have h := q_k4 (k2 x)
      simpa only [k2, k4, k_six] using h
    · rw [ho, hz3]
      have h := q_k1 (k2 x)
      simpa only [k2, k4, k_six] using h
  | right he ho => exact False.elim (hx0 he)
  | zero he ho =>
    rcases he with he | he
    · exact False.elim (q_ne0 hx0 he.symm)
    · have hu : q x z = k3 x := by
        have h := congrArg k3 he
        simpa only [k3, k_six] using h.symm
      have hzz := q_eq_k3 hx0 hu
      rw [ho, k_e, q_e_left, hzz]
      exact k_six x
  | orbit he ho =>
    rcases he with he | he
    · have hu : q x z = k5 x := by
        have h := congrArg k5 he
        simpa only [k5, k_six] using h.symm
      exact False.elim (q_ne5 hx0 hu)
    · have hu : q x z = k2 x := by
        have h := congrArg k2 he
        simpa only [k2, k4, k_six] using h.symm
      exact False.elim (q_ne2 hx0 hu)
  | reverse he ho =>
    have hu : q x z = k x := by
      have h := congrArg k he
      simpa only [k5, k_six] using h.symm
    have hzz := q_eq_k1 hx0 hu
    rw [ho, hzz, q_e_right]
    simpa only [hzz, k3, k5] using he.symm
  | code u t he hq ho => exact False.elim (middle_code_impossible hx0 he hq)
  | raw ho => exact raw_recovery hx hz ho

theorem dual_source {x y z : Tree} (hx : NF x) (hz : NF z) :
    q (q (q y y) (q (q x z) x)) z = x := by
  rw [q_square, q_e_left]
  exact recovery hx hz

def Carrier := {t : Tree // NF t}
def op (a b : Carrier) : Carrier := ⟨q a.1 b.1, q_nf a.2 b.2⟩
def opposite (a b : Carrier) : Carrier := op b a

theorem equation34889 (x y z : Carrier) : op (op (op y y) (op (op x z) x)) z = x := by
  apply Subtype.ext
  exact dual_source x.2 z.2

theorem equation11082 (x y z : Carrier) :
    opposite y (opposite (opposite x (opposite y x)) (opposite z z)) = x :=
  equation34889 x z y

def embed (n : Nat) : Carrier := ⟨atom n c0, True.intro⟩
theorem embed_injective (m n : Nat) (h : embed m = embed n) : m = n := by
  have hh := congrArg Subtype.val h
  exact (Tree.atom.inj hh).1
theorem infinite_model : ∃ i : Nat → Carrier, ∀ m n, i m = i n → m = n :=
  ⟨embed, embed_injective⟩

end submission.Austin11082

namespace submission
abbrev CM := Austin11082.Carrier
namespace CM
/-- This model contains an injective image of every natural number. -/
theorem tower_injective (m n : Nat)
    (h : Austin11082.embed m = Austin11082.embed n) : m = n :=
  Austin11082.embed_injective m n h
end CM
instance modelMagma : Magma CM := ⟨Austin11082.op⟩
end submission

theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin11082.equation34889 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin11082.embed_injective 0 1
      (h (submission.Austin11082.embed 0) (submission.Austin11082.embed 1))
    exact Nat.noConfusion bad

example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

