import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin12883
/- Total, size-recursive decoder. Law.lean proves E12883; Model.lean proves infinity. -/
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
abbrev Small (b : T) := {o : T // sz o < sz b}
abbrev Bounded (a b : T) := {o : T // sz o ≤ sz a + sz b + 2}
def raw (a b : T) : Bounded a b := ⟨p a b, Nat.le_refl _⟩

def evalWith (a b : T) (d : Option (Small b)) : Bounded a b :=
  if hab : a = b then ⟨k a, by subst b; simp only [sz]; omega⟩
  else match b, d with
    | p body key, some o =>
      if key = a then ⟨o.val, by have ho := o.property; simp only [sz] at ho ⊢; omega⟩
      else raw a (p body key)
    | b', _ => raw a b'

def fromCodeWith (b out : T) (d : Option (Small b)) : Option T :=
  match b, d with
  | p _ key, some o => if o.val = out then some key else none
  | _, _ => none
def inverseWith (b out : T) (d : Option (Small b)) : Option T :=
  if out = k b then some b
  else
    match out with
    | p a second =>
      if second = b ∧ (evalWith a b d).val = out then some a else fromCodeWith b out d
    | e => fromCodeWith b e d
    | k t => fromCodeWith b (k t) d

def combine {b : T} (first second : Option (Small b)) : Option (Small b) :=
  match first, second with
  | none, _ => second
  | _, none => first
  | some a, some c => if a.val = c.val then first else none

def decode (b : T) : Option (Small b) :=
  match b with
  | p body y =>
    let primary : Option (Small (p body y)) :=
      match body with
      | p x payload =>
        have hx : sz x < sz (p (p x payload) y) := by simp only [sz]; omega
        let h0 := evalWith y x (decode x)
        have hsmall : sz h0.val < sz (p (p x payload) y) := by
          have hh := h0.property; simp only [sz] at hh ⊢; omega
        if (inverseWith h0.val payload (decode h0.val)).isSome then some ⟨x, hx⟩ else none
      | k x =>
        have hx : sz x < sz (p (k x) y) := by simp only [sz]; omega
        let h0 := evalWith y x (decode x)
        have hsmall : sz h0.val < sz (p (k x) y) := by
          have hh := h0.property; simp only [sz] at hh ⊢; omega
        if (inverseWith h0.val x (decode h0.val)).isSome then some ⟨x, hx⟩ else none
      | e => none
    let extra : Option (Small (p body y)) :=
      match y with
      | p (p inner x) target =>
        have hi : sz (p inner x) < sz (p body (p (p inner x) target)) := by simp only [sz]; omega
        have hw : sz body < sz (p body (p (p inner x) target)) := by simp only [sz]; omega
        if sz body < sz (p inner x) ∧ (evalWith x (p inner x) (decode (p inner x))).val = body ∧
            (inverseWith body target (decode body)).isSome then
          some ⟨x, by simp only [sz]; omega⟩ else none
      | k (p inner x) =>
        have hi : sz (p inner x) < sz (p body (k (p inner x))) := by simp only [sz]; omega
        have hw : sz body < sz (p body (k (p inner x))) := by simp only [sz]; omega
        if sz body < sz (p inner x) ∧ (evalWith x (p inner x) (decode (p inner x))).val = body ∧
            (inverseWith body (p inner x) (decode body)).isSome then
          some ⟨x, by simp only [sz]; omega⟩ else none
      | _ => none
    combine primary extra
  | _ => none
termination_by sz b
decreasing_by all_goals assumption

def q (a b : T) : T := (evalWith a b (decode b)).val
def inv (b out : T) : Option T := inverseWith b out (decode b)
theorem q_size (a b : T) : sz (q a b) ≤ sz a + sz b + 2 :=
  (evalWith a b (decode b)).property
@[simp] theorem decode_e : decode e = none := by rw [decode.eq_def]
@[simp] theorem decode_k (a : T) : decode (k a) = none := by rw [decode.eq_def]
@[simp] theorem q_square (a : T) : q a a = k a := by simp [q, evalWith]
@[simp] theorem q_e_right (a : T) : q a e = if a = e then k a else p a e := by
  simp only [q,decode_e,evalWith]
  split <;> rfl
end submission.Austin12883

set_option autoImplicit false
namespace submission.Austin12883
open T

@[simp] theorem evalWith_square (a : T) (d : Option (Small a)) : (evalWith a a d).val = k a := by
  simp [evalWith]
theorem key_ne_pair (body key : T) : key ≠ p body key := by
  intro he
  have hh := congrArg sz he
  simp only [sz] at hh
  omega
theorem evalWith_hit (body key : T) (o : Small (p body key)) :
    (evalWith key (p body key) (some o)).val = o.val := by
  simp [evalWith, key_ne_pair]

theorem fromCodeWith_sound {b out a : T} {d : Option (Small b)}
    (h : fromCodeWith b out d = some a) : (evalWith a b d).val = out := by
  cases b with
  | e => simp [fromCodeWith] at h
  | k b => simp [fromCodeWith] at h
  | p body key =>
    cases d with
    | none => simp [fromCodeWith] at h
    | some o =>
      simp only [fromCodeWith] at h
      split at h
      · rename_i ho
        have ha := Option.some.inj h
        subst a
        exact (evalWith_hit body key o).trans ho
      · cases h

theorem inverseWith_sound {b out a : T} {d : Option (Small b)}
    (h : inverseWith b out d = some a) : (evalWith a b d).val = out := by
  unfold inverseWith at h
  split at h
  · rename_i he
    have ha := Option.some.inj h
    subst a
    exact (evalWith_square b d).trans he.symm
  · cases out with
    | e => exact fromCodeWith_sound h
    | k t => exact fromCodeWith_sound h
    | p left right =>
      change (if right = b ∧ (evalWith left b d).val = p left right then some left
        else fromCodeWith b (p left right) d) = some a at h
      split at h
      · rename_i hc
        have ha := Option.some.inj h
        subst a
        exact hc.2
      · exact fromCodeWith_sound h

theorem inverseWith_raw (a b : T) (d : Option (Small b))
    (he : (evalWith a b d).val = p a b) : inverseWith b (p a b) d = some a := by
  simp [inverseWith, he]

theorem inverseWith_small (b out : T) (d : Option (Small b)) (hs : sz out < sz b) :
    inverseWith b out d = fromCodeWith b out d := by
  have hn : out ≠ k b := by intro he; rw [he] at hs; simp only [sz] at hs; omega
  unfold inverseWith
  rw [if_neg hn]
  cases out with
  | e => rfl
  | k t => rfl
  | p left right =>
    have hr : right ≠ b := by
      intro he; rw [he] at hs; simp only [sz] at hs; omega
    change (if right = b ∧ (evalWith left b d).val = p left right then some left
      else fromCodeWith b (p left right) d) = fromCodeWith b (p left right) d
    simp only [hr, false_and, ↓reduceIte]

theorem inverseWith_complete (a b : T) (d : Option (Small b)) :
    inverseWith b (evalWith a b d).val d = some a := by
  by_cases hab : a = b
  · subst b
    rw [evalWith_square]
    simp [inverseWith]
  · have finish (he : (evalWith a b d).val = p a b) :
        inverseWith b (evalWith a b d).val d = some a := by
      rw [he]
      exact inverseWith_raw a b d he
    cases b with
    | e => apply finish; simp [evalWith, hab, raw]
    | k t => apply finish; simp [evalWith, hab, raw]
    | p body key =>
      cases d with
      | none => apply finish; simp [evalWith, hab, raw]
      | some o =>
        by_cases hka : key = a
        · subst key
          rw [evalWith_hit]
          rw [inverseWith_small _ _ _ o.property]
          simp [fromCodeWith]
        · apply finish; simp [evalWith, hab, hka, raw]

theorem inv_sound {b out a : T} (h : inv b out = some a) : q a b = out :=
  inverseWith_sound h
@[simp] theorem inv_complete (a b : T) : inv b (q a b) = some a :=
  inverseWith_complete a b (decode b)
theorem q_right_injective (a a' b : T) (he : q a b = q a' b) : a = a' := by
  have h := congrArg (inv b) he
  simpa only [inv_complete, Option.some.injEq] using h
end submission.Austin12883

set_option autoImplicit false
namespace submission.Austin12883
open T

def Code (b out : T) : Prop := ∃ h : sz out < sz b, decode b = some ⟨out, h⟩
def Hit (a b out : T) : Prop := ∃ body, b = p body a ∧ Code b out
def Plain (a b out : T) : Prop := out = p a b ∨ (a = b ∧ out = k b)
def Range (b out : T) : Prop := ∃ a, q a b = out

theorem range_iff (b out : T) : Range b out ↔ (inv b out).isSome = true := by
  constructor
  · rintro ⟨a, rfl⟩; simp only [inv_complete, Option.isSome_some]
  · intro h
    cases hi : inv b out with
    | none => simp [hi] at h
    | some a => exact ⟨a, inv_sound hi⟩

theorem code_small {b out : T} (h : Code b out) : sz out < sz b := h.choose
theorem hit_small {a b out : T} (h : Hit a b out) : sz a < sz b ∧ sz out < sz b := by
  obtain ⟨body, rfl, hc⟩ := h
  exact ⟨by simp only [sz]; omega, code_small hc⟩
theorem q_hit {a b out : T} (h : Hit a b out) : q a b = out := by
  obtain ⟨body, rfl, hs, hd⟩ := h
  change (evalWith a (p body a) (decode (p body a))).val = out
  rw [hd, evalWith_hit]
theorem q_cases (a b : T) : Plain a b (q a b) ∨ Hit a b (q a b) := by
  by_cases he : a = b
  · subst a; exact Or.inl (Or.inr ⟨rfl, q_square b⟩)
  · cases b with
    | e => left; left; simp [q, decode_e, evalWith, he, raw]
    | k t => left; left; simp [q, decode_k, evalWith, he, raw]
    | p body key =>
      cases hd : decode (p body key) with
      | none => left; left; simp [q, hd, evalWith, he, raw]
      | some o =>
        by_cases hk : key = a
        · subst key
          have hq : q a (p body a) = o.val := by simp [q, hd, evalWith_hit]
          right; refine ⟨body, rfl, ?_⟩
          rw [hq]; exact ⟨o.property, hd⟩
        · left; left; simp [q, hd, evalWith, he, hk, raw]
theorem plain_growth {a b out : T} (h : Plain a b out) :
    sz a < sz out ∧ sz b < sz out := by
  rcases h with rfl | ⟨rfl, rfl⟩ <;> simp only [sz] <;> constructor <;> omega
theorem q_ne_right (a b : T) : q a b ≠ b := by
  intro he
  rcases q_cases a b with hp | hh
  · have hs := (plain_growth hp).2; rw [he] at hs; omega
  · have hs := (hit_small hh).2; rw [he] at hs; omega
theorem no_range_self (b : T) : ¬ Range b b := by
  rintro ⟨a, h⟩; exact q_ne_right a b h
theorem hit_of_drop {a b : T} (hs : sz (q a b) < sz b) : Hit a b (q a b) := by
  rcases q_cases a b with hp | hh
  · have hb := (plain_growth hp).2; omega
  · exact hh
theorem plain_of_large_left {a b : T} (hs : sz b ≤ sz a) : Plain a b (q a b) := by
  rcases q_cases a b with hp | hh
  · exact hp
  · have hb := (hit_small hh).1; omega
theorem q_of_larger_left {a b : T} (hs : sz b < sz a) : q a b = p a b := by
  rcases plain_of_large_left (Nat.le_of_lt hs) with hp | ⟨he, _⟩
  · exact hp
  · rw [he] at hs; omega
theorem q_k_right (a b : T) : q a (k b) = if a = k b then k a else p a (k b) := by
  simp only [q, decode_k, evalWith]
  split <;> rfl
theorem range_k_lower {b out : T} (h : Range (k b) out) : sz b < sz out := by
  obtain ⟨a, rfl⟩ := h
  rw [q_k_right]
  split
  · rename_i he; rw [he]; simp only [sz]; omega
  · simp only [sz]; omega

end submission.Austin12883

set_option autoImplicit false
namespace submission.Austin12883
open T

def primary (body y : T) : Option (Small (p body y)) :=
  match body with
  | p x payload =>
    if (inv (q y x) payload).isSome then some ⟨x, by simp only [sz]; omega⟩ else none
  | k x =>
    if (inv (q y x) x).isSome then some ⟨x, by simp only [sz]; omega⟩ else none
  | e => none
def extra (body y : T) : Option (Small (p body y)) :=
  match y with
  | p (p inner x) target =>
    if sz body < sz (p inner x) ∧ q x (p inner x) = body ∧ (inv body target).isSome then
      some ⟨x, by simp only [sz]; omega⟩ else none
  | k (p inner x) =>
    if sz body < sz (p inner x) ∧ q x (p inner x) = body ∧ (inv body (p inner x)).isSome then
      some ⟨x, by simp only [sz]; omega⟩ else none
  | _ => none

theorem decode_pair (body y : T) : decode (p body y) = combine (primary body y) (extra body y) := by
  rw [decode.eq_def]
  rfl

def Primary (body y out : T) : Prop :=
  (∃ payload, body = p out payload ∧ Range (q y out) payload) ∨
  (body = k out ∧ Range (q y out) out)
def Extra (body y out : T) : Prop := ∃ inner,
  sz body < sz (p inner out) ∧ q out (p inner out) = body ∧
    ((∃ target, y = p (p inner out) target ∧ Range body target) ∨
      (y = k (p inner out) ∧ Range body (p inner out)))

theorem primary_sound {body y : T} {o : Small (p body y)} (h : primary body y = some o) :
    Primary body y o.val := by
  cases body with
  | e => simp [primary] at h
  | k x =>
    simp only [primary] at h
    split at h
    · rename_i hr
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [← ho]; exact Or.inr ⟨rfl, (range_iff _ _).mpr hr⟩
    · cases h
  | p x payload =>
    simp only [primary] at h
    split at h
    · rename_i hr
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [← ho]; exact Or.inl ⟨payload, rfl, (range_iff _ _).mpr hr⟩
    · cases h

theorem primary_complete {body y out : T} (h : Primary body y out) :
    ∃ hs : sz out < sz (p body y), primary body y = some ⟨out, hs⟩ := by
  rcases h with ⟨payload, rfl, hr⟩ | ⟨rfl, hr⟩
  · refine ⟨by simp only [sz]; omega, ?_⟩
    simp only [primary, (range_iff _ _).mp hr, ↓reduceIte]
  · refine ⟨by simp only [sz]; omega, ?_⟩
    simp only [primary, (range_iff _ _).mp hr, ↓reduceIte]

theorem extra_sound {body y : T} {o : Small (p body y)} (h : extra body y = some o) :
    Extra body y o.val := by
  unfold extra at h
  split at h
  · rename_i inner x target
    split at h
    · rename_i hc
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [← ho]
      exact ⟨inner, hc.1, hc.2.1, Or.inl ⟨target, rfl, (range_iff _ _).mpr hc.2.2⟩⟩
    · cases h
  · rename_i inner x
    split at h
    · rename_i hc
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [← ho]
      exact ⟨inner, hc.1, hc.2.1, Or.inr ⟨rfl, (range_iff _ _).mpr hc.2.2⟩⟩
    · cases h
  · cases h

theorem extra_complete {body y out : T} (h : Extra body y out) :
    ∃ hs : sz out < sz (p body y), extra body y = some ⟨out, hs⟩ := by
  obtain ⟨inner, hs, hq, ⟨target, rfl, hr⟩ | ⟨rfl, hr⟩⟩ := h
  · refine ⟨by simp only [sz]; omega, ?_⟩
    simp only [extra, hs, hq, (range_iff _ _).mp hr, and_self, ↓reduceIte]
  · refine ⟨by simp only [sz]; omega, ?_⟩
    simp only [extra, hs, hq, (range_iff _ _).mp hr, and_self, ↓reduceIte]

theorem combine_cases {b : T} {a c : Option (Small b)} {o : Small b}
    (h : combine a c = some o) : a = some o ∨ c = some o := by
  cases a <;> cases c <;> simp only [combine] at h ⊢
  · cases h
  · exact Or.inr h
  · exact Or.inl h
  · split at h
    · exact Or.inl h
    · cases h

theorem code_cases {body y out : T} (h : Code (p body y) out) :
    Primary body y out ∨ Extra body y out := by
  obtain ⟨hs, hd⟩ := h
  rw [decode_pair] at hd
  rcases combine_cases hd with hp | he
  · exact Or.inl (primary_sound hp)
  · exact Or.inr (extra_sound he)
theorem primary_output_lt_body {body y out : T} (h : Primary body y out) : sz out < sz body := by
  rcases h with ⟨payload, rfl, _⟩ | ⟨rfl, _⟩ <;> simp only [sz] <;> omega
theorem extra_output_lt_key {body y out : T} (h : Extra body y out) : sz out < sz y := by
  obtain ⟨inner, _, _, ⟨target, rfl, _⟩ | ⟨rfl, _⟩⟩ := h <;> simp only [sz] <;> omega
theorem extra_body_lt_key {body y out : T} (h : Extra body y out) : sz body < sz y := by
  obtain ⟨inner, hs, _, ⟨target, rfl, _⟩ | ⟨rfl, _⟩⟩ := h <;> simp only [sz] at hs ⊢ <;> omega

end submission.Austin12883

set_option autoImplicit false
namespace submission.Austin12883
open T

def Node (child tree : T) : Prop := (∃ right, tree = p child right) ∨ tree = k child
theorem node_growth {child tree : T} (h : Node child tree) : sz child < sz tree := by
  rcases h with ⟨right, rfl⟩ | rfl <;> simp only [sz] <;> omega
theorem primary_node {body key out : T} (h : Primary body key out) : Node out body := by
  rcases h with ⟨r, he, _⟩ | ⟨he, _⟩
  · exact Or.inl ⟨r, he⟩
  · exact Or.inr he
theorem node_unique {a b tree : T} (ha : Node a tree) (hb : Node b tree) : a = b := by
  rcases ha with ⟨r, rfl⟩ | rfl <;> rcases hb with ⟨s, he⟩ | he
  · exact (T.p.inj he).1
  · cases he
  · cases he
  · exact T.k.inj he
theorem range_node_pair_lower {inner key x target : T} (hn : Node inner key)
    (hs : sz x < sz inner) (hr : Range (p key x) target) : sz inner ≤ sz target := by
  obtain ⟨a, rfl⟩ := hr
  have hg := node_growth hn
  rcases q_cases a (p key x) with hp | hh
  · have h := (plain_growth hp).2; simp only [sz] at h; omega
  · obtain ⟨body, he, hc⟩ := hh
    rcases code_cases hc with hprimary | hextra
    · have hout := node_unique (primary_node hprimary) hn
      rw [hout]; exact Nat.le_refl _
    · have hb := extra_body_lt_key hextra; omega

theorem primary_extra_disjoint {body key a out : T} (hp : Primary body key a)
    (he : Extra body key out) : False := by
  obtain ⟨inner, hs, _, ht⟩ := he
  have hn : Node (p inner out) key := by
    rcases ht with ⟨target, hk, _⟩ | ⟨hk, _⟩
    · exact Or.inl ⟨target, hk⟩
    · exact Or.inr hk
  have hg := node_growth hn
  have ha := primary_output_lt_body hp
  have hq : q key a = p key a := q_of_larger_left (by omega)
  rcases hp with ⟨payload, hb, hr⟩ | ⟨hb, hr⟩
  · rw [hq] at hr
    have hl := range_node_pair_lower hn (by omega : sz a < sz (p inner out)) hr
    rw [hb] at hs; simp only [sz] at hs hl; omega
  · rw [hq] at hr
    have hl := range_node_pair_lower hn (by omega : sz a < sz (p inner out)) hr
    omega

theorem code_of_primary {body key out : T} (hp : Primary body key out) : Code (p body key) out := by
  obtain ⟨hs, hf⟩ := primary_complete hp
  have he : extra body key = none := by
    cases h : extra body key with
    | none => rfl
    | some o => exact False.elim (primary_extra_disjoint hp (extra_sound h))
  exact ⟨hs, by rw [decode_pair, hf, he]; rfl⟩
theorem code_of_extra {body key out : T} (he : Extra body key out) : Code (p body key) out := by
  obtain ⟨hs, hf⟩ := extra_complete he
  have hp : primary body key = none := by
    cases h : primary body key with
    | none => rfl
    | some o => exact False.elim (primary_extra_disjoint (primary_sound h) he)
  exact ⟨hs, by rw [decode_pair, hp, hf]; rfl⟩

end submission.Austin12883

set_option autoImplicit false
namespace submission.Austin12883
open T

theorem step_cases {a b out : T} (h : q a b = out) : Plain a b out ∨ Hit a b out := by
  rw [← h]; exact q_cases a b
theorem step_ne_right {a b out : T} (h : q a b = out) : out ≠ b := by
  rw [← h]; exact q_ne_right a b
theorem step_plain_of_output_large {a b out : T} (h : q a b = out) (hs : sz b ≤ sz out) :
    Plain a b out := by
  rcases step_cases h with hp | hh
  · exact hp
  · have ho := (hit_small hh).2; omega
theorem step_hit_of_output_small {a b out : T} (h : q a b = out) (hs : sz out < sz b) :
    Hit a b out := by
  rw [← h]; exact hit_of_drop (by rw [h]; exact hs)

theorem inner_hit_extra {x y z u v w : T} (hu : q y x = u) (hv : q z u = v)
    (hw : q x v = w) (hit : Hit x v w) : Extra w y x := by
  have ⟨hxv, hwv⟩ := hit_small hit
  obtain ⟨body, vshape, _⟩ := hit
  have uraw : u = p y x := by
    rcases step_cases hu with hp | hh
    · rcases hp with hr | ⟨hy, hu'⟩
      · exact hr
      · have vp : Plain z u v := by
          rcases step_cases hv with hpv | hhv
          · exact hpv
          · obtain ⟨b, hb, _⟩ := hhv; rw [hu'] at hb; cases hb
        rcases vp with vp | ⟨_, vp⟩
        · have eqs := T.p.inj (vp.symm.trans vshape)
          have hx := congrArg sz (eqs.2.symm.trans hu')
          simp only [sz] at hx; omega
        · rw [vp] at vshape; cases vshape
    · have hux := (hit_small hh).2
      have vp := step_plain_of_output_large hv (by omega)
      rcases vp with vp | ⟨_, vp⟩
      · have he := (T.p.inj (vp.symm.trans vshape)).2
        rw [he] at hux; omega
      · rw [vp] at vshape; cases vshape
  have vhit : Hit z u v := by
    rcases step_cases hv with hp | hh
    · rcases hp with hp | ⟨_, hp⟩
      · have he := (T.p.inj (hp.symm.trans vshape)).2
        have hs := congrArg sz (he.symm.trans uraw)
        simp only [sz] at hs; omega
      · rw [hp] at vshape; cases vshape
    · exact hh
  obtain ⟨vb, vkey, vc⟩ := vhit
  rw [uraw] at vc vkey
  have hz : z = x := (T.p.inj vkey).2.symm
  have vp : Primary y x v := by
    rcases code_cases vc with hp | he
    · exact hp
    · have hs := extra_output_lt_key he; omega
  refine ⟨body, ?_, ?_, ?_⟩
  · rw [← vshape]; exact hwv
  · rw [← vshape]; exact hw
  · rcases vp with ⟨target, hy, hr⟩ | ⟨hy, hr⟩
    · rw [hw] at hr
      exact Or.inl ⟨target, by rw [← vshape]; exact hy, hr⟩
    · rw [hw] at hr
      exact Or.inr ⟨by rw [← vshape]; exact hy, by rw [← vshape]; exact hr⟩

theorem extra_preceding_raw {w y x : T} (he : Extra w y x) : q w y = p w y := by
  have hwy := extra_body_lt_key he
  rcases q_cases w y with hp | hh
  · rcases hp with hp | ⟨hw, _⟩
    · exact hp
    · rw [hw] at hwy; omega
  · obtain ⟨body, hy, _⟩ := hh
    obtain ⟨inner, _, _, ⟨target, ht, hr⟩ | ⟨ht, _⟩⟩ := he
    · have hw := (T.p.inj (ht.symm.trans hy)).2
      rw [hw] at hr; exact False.elim (no_range_self w hr)
    · rw [ht] at hy; cases hy

end submission.Austin12883

set_option autoImplicit false
namespace submission.Austin12883
open T

theorem plain_inner_ne_key {x y z u v w : T} (hu : q y x = u) (hv : q z u = v)
    (hw : q x v = w) (hp : Plain x v w) : w ≠ y := by
  intro he
  have ⟨hxw, hvw⟩ := plain_growth hp
  have uraw : u = p y x := hu.symm.trans (q_of_larger_left (by rw [← he]; exact hxw))
  have hvu : sz v < sz u := by rw [uraw, ← he]; simp only [sz]; omega
  obtain ⟨body, shape, hc⟩ := step_hit_of_output_small hv hvu
  rw [uraw] at hc
  have hprimary : Primary y x v := by
    rcases code_cases hc with hpr | hex
    · exact hpr
    · have hs := extra_body_lt_key hex; rw [← he] at hs; omega
  have hn : Node x y := by
    rw [← he]
    rcases hp with hp | ⟨hx, hp⟩
    · exact Or.inl ⟨v, hp⟩
    · exact Or.inr (hp.trans (congrArg k hx.symm))
  have hvx := node_unique (primary_node hprimary) hn
  rw [hvx, q_square] at hw
  have hy : y = k x := he.symm.trans hw.symm
  rw [hy, hvx] at hprimary
  rcases hprimary with ⟨payload, bad, _⟩ | ⟨_, hr⟩
  · cases bad
  · rw [q_square] at hr
    have hs := range_k_lower hr; omega

theorem plain_inner_no_outer_hit {x y z u v w out : T} (hu : q y x = u) (hv : q z u = v)
    (hw : q x v = w) (hp : Plain x v w) (hh : Hit w y out) : False := by
  obtain ⟨body, hy, _⟩ := hh
  have hwy : sz w < sz y := by rw [hy]; simp only [sz]; omega
  have ⟨hxw, hvw⟩ := plain_growth hp
  have uraw : u = p y x := hu.symm.trans (q_of_larger_left (by omega))
  have hvu : sz v < sz u := by rw [uraw]; simp only [sz]; omega
  obtain ⟨vb, vshape, vc⟩ := step_hit_of_output_small hv hvu
  rw [uraw] at vc
  have vp : Primary y x v := by
    rcases code_cases vc with hpr | hex
    · exact hpr
    · have hs := extra_body_lt_key hex; omega
  rcases vp with ⟨target, ht, hr⟩ | ⟨ht, _⟩
  · have hw' := (T.p.inj (ht.symm.trans hy)).2
    rw [hw, hw'] at hr
    exact no_range_self w hr
  · rw [ht] at hy; cases hy

theorem preceding_raw {x y z u v w : T} (hu : q y x = u) (hv : q z u = v)
    (hw : q x v = w) : q w y = p w y := by
  rcases step_cases hw with hp | hh
  · rcases q_cases w y with ho | hh'
    · rcases ho with ho | ⟨he, _⟩
      · exact ho
      · exact False.elim (plain_inner_ne_key hu hv hw hp he)
    · exact False.elim (plain_inner_no_outer_hit hu hv hw hp hh')
  · exact extra_preceding_raw (inner_hit_extra hu hv hw hh)

theorem equation12883 (x y z : T) :
    x = q y (q (q x (q z (q y x))) y) := by
  let u := q y x
  let v := q z u
  let w := q x v
  have hu : q y x = u := rfl
  have hv : q z u = v := rfl
  have hw : q x v = w := rfl
  change x = q y (q w y)
  rw [preceding_raw hu hv hw]
  symm
  apply q_hit
  refine ⟨w, rfl, ?_⟩
  rcases step_cases hw with hp | hh
  · apply code_of_primary
    rcases hp with hr | ⟨he, hr⟩
    · exact Or.inl ⟨v, hr, ⟨z, hv⟩⟩
    · exact Or.inr ⟨hr.trans (congrArg k he.symm), ⟨z, hv.trans he.symm⟩⟩
  · exact code_of_extra (inner_hit_extra hu hv hw hh)

end submission.Austin12883

set_option autoImplicit false
namespace submission.Austin12883
abbrev Carrier := T
def mul : Carrier → Carrier → Carrier := q
def opposite (a b : Carrier) : Carrier := mul b a
def embed : Nat → Carrier
  | 0 => T.e
  | n + 1 => T.k (embed n)
@[simp] theorem embed_size (n : Nat) : sz (embed n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [embed, sz, ih]
theorem embed_injective (n j : Nat) (h : embed n = embed j) : n = j := by
  have hs := congrArg sz h
  simpa only [embed_size] using hs
theorem equation33020 (x y z : Carrier) :
    x = opposite (opposite y (opposite (opposite (opposite x y) z) x)) y :=
  equation12883 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op y (op (op x (op z (op y x))) y)) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation12883, embed_injective⟩
end submission.Austin12883

namespace submission
abbrev CM := Austin12883.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin12883.embed n = Austin12883.embed j) : n = j :=
  Austin12883.embed_injective n j h
end CM
instance modelMagma : Magma CM := ⟨Austin12883.opposite⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin12883.equation33020 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin12883.embed_injective 0 1
      (h (submission.Austin12883.embed 0) (submission.Austin12883.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

