import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin5947
/- Experimental E5947 primitives; no source law is asserted here. -/
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
    | p key body, some o =>
      if key = a then ⟨o.val, by have ho := o.property; simp only [sz] at ho ⊢; omega⟩
      else raw a (p key body)
    | b', _ => raw a b'

def fromCodeWith (b out : T) (d : Option (Small b)) : Option T :=
  match b, d with
  | p key _, some o => if o.val = out then some key else none
  | _, _ => none
def inverseWith (b out : T) (d : Option (Small b)) : Option T :=
  if out = k b then some b
  else
    match out with
    | p a second =>
      if second = b ∧ (evalWith a b d).val = out then some a else fromCodeWith b out d
    | e => fromCodeWith b e d
    | k t => fromCodeWith b (k t) d

end submission.Austin5947

set_option autoImplicit false
namespace submission.Austin5947
open T

@[simp] theorem evalWith_square (a : T) (d : Option (Small a)) : (evalWith a a d).val = k a := by
  simp [evalWith]
theorem key_ne_pair (body key : T) : key ≠ p key body := by
  intro he
  have hh := congrArg sz he
  simp only [sz] at hh
  omega
theorem evalWith_hit (body key : T) (o : Small (p key body)) :
    (evalWith key (p key body) (some o)).val = o.val := by
  simp [evalWith, key_ne_pair]

theorem fromCodeWith_sound {b out a : T} {d : Option (Small b)}
    (h : fromCodeWith b out d = some a) : (evalWith a b d).val = out := by
  cases b with
  | e => simp [fromCodeWith] at h
  | k b => simp [fromCodeWith] at h
  | p key body =>
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
    | p key body =>
      cases d with
      | none => apply finish; simp [evalWith, hab, raw]
      | some o =>
        by_cases hka : key = a
        · subst key
          rw [evalWith_hit]
          rw [inverseWith_small _ _ _ o.property]
          simp [fromCodeWith]
        · apply finish; simp [evalWith, hab, hka, raw]

theorem evalWith_left_bound (a b : T) (d : Option (Small b)) :
    sz a ≤ max (sz b) (sz (evalWith a b d).val) := by
  by_cases he : a = b
  · subst a; exact Nat.le_max_left _ _
  · cases b with
    | e => simp [evalWith, he, raw, sz] <;> omega
    | k t => simp [evalWith, he, raw, sz] <;> omega
    | p key body =>
      cases d with
      | none => simp [evalWith, he, raw, sz] <;> omega
      | some o =>
        by_cases hk : key = a
        · subst key; simp only [sz]; omega
        · simp [evalWith, he, hk, raw, sz] <;> omega
theorem inverseWith_bound {b out a : T} {d : Option (Small b)}
    (h : inverseWith b out d = some a) : sz a ≤ max (sz b) (sz out) := by
  have hs := evalWith_left_bound a b d
  rw [inverseWith_sound h] at hs
  exact hs
end submission.Austin5947

set_option autoImplicit false
namespace submission.Austin5947
open T

def mixedWith (first key out : T) (da : Option (Small first)) (db : Option (Small key)) : Bool :=
  match inverseWith key out db with
  | none => false
  | some h => (inverseWith first h da).isSome

def combine {b : T} (a c : Option (Small b)) : Option (Small b) :=
  match a,c with
  | none,_ => c
  | _,none => a
  | some x,some y => if x.val = y.val then a else none

def decode (b : T) : Option (Small b) :=
  match b with
  | p key body =>
    have hk : sz key < sz (p key body) := by simp only [sz]; omega
    let primary : Option (Small (p key body)) :=
      match body with
      | p x right =>
        have hx : sz x < sz (p key (p x right)) := by simp only [sz]; omega
        if mixedWith x key right (decode x) (decode key) then some ⟨x,hx⟩ else none
      | k right =>
        have hx : sz right < sz (p key (k right)) := by simp only [sz]; omega
        if mixedWith right key right (decode right) (decode key) then some ⟨right,hx⟩ else none
      | e => none
    let extra : Option (Small (p key body)) :=
      match key with
      | p h other =>
        match decode (p h other) with
        | none => none
        | some v =>
          have hv : sz v.val < sz (p (p h other) body) := by
            have hs := v.property; simp only [sz] at hs ⊢; omega
          match hshape : v.val with
          | p x rest =>
            have hx : sz x < sz (p (p h other) body) := by
              have hs := v.property; rw [hshape] at hs; simp only [sz] at hs ⊢; omega
            if (inverseWith x h (decode x)).isSome then
              match decode v.val with
              | none => none
              | some w => if w.val = body then some ⟨x,hx⟩ else none
            else none
          | _ => none
      | _ => none
    combine primary extra
  | _ => none
termination_by sz b
decreasing_by all_goals assumption

def q (a b : T) : T := (evalWith a b (decode b)).val
def inv (b out : T) : Option T := inverseWith b out (decode b)
theorem inv_sound {b out a : T} (h : inv b out = some a) : q a b = out := inverseWith_sound h
@[simp] theorem inv_complete (a b : T) : inv b (q a b) = some a := inverseWith_complete _ _ _
theorem q_right_injective (a a' b : T) (he : q a b = q a' b) : a = a' := by
  have h := congrArg (inv b) he
  simpa only [inv_complete,Option.some.injEq] using h
@[simp] theorem q_square (a : T) : q a a = k a := evalWith_square _ _
@[simp] theorem decode_e : decode e = none := by rw [decode.eq_def]
@[simp] theorem decode_k (a : T) : decode (k a) = none := by rw [decode.eq_def]
end submission.Austin5947

set_option autoImplicit false
namespace submission.Austin5947
open T

def Code (b out : T) : Prop := ∃ h : sz out < sz b, decode b = some ⟨out, h⟩
def Hit (a b out : T) : Prop := ∃ body, b = p a body ∧ Code b out
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
  change (evalWith a (p a body) (decode (p a body))).val = out
  rw [hd, evalWith_hit]
theorem q_cases (a b : T) : Plain a b (q a b) ∨ Hit a b (q a b) := by
  by_cases he : a = b
  · subst a; exact Or.inl (Or.inr ⟨rfl, q_square b⟩)
  · cases b with
    | e => left; left; simp [q, decode_e, evalWith, he, raw]
    | k t => left; left; simp [q, decode_k, evalWith, he, raw]
    | p key body =>
      cases hd : decode (p key body) with
      | none => left; left; simp [q, hd, evalWith, he, raw]
      | some o =>
        by_cases hk : key = a
        · subst key
          have hq : q a (p a body) = o.val := by simp [q, hd, evalWith_hit]
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

def MixedRange (first key out : T) : Prop := ∃ h, Range first h ∧ q h key = out

theorem mixed_range_iff (first key out : T) : MixedRange first key out ↔
    mixedWith first key out (decode first) (decode key) = true := by
  change MixedRange first key out ↔ (match inv key out with | none => false | some h => (inv first h).isSome) = true
  cases hi : inv key out with
  | none =>
    constructor
    · rintro ⟨h,_,hs⟩
      have he : inv key out = some h := by rw [←hs]; exact inv_complete h key
      rw [hi] at he; cases he
    · intro h; cases h
  | some h =>
    constructor
    · rintro ⟨a,hr,hs⟩
      have he : inv key out = some a := by rw [←hs]; exact inv_complete a key
      have ha := Option.some.inj (hi.symm.trans he)
      rw [ha]; exact (range_iff _ _).mp hr
    · intro hr
      exact ⟨h,(range_iff _ _).mpr hr,inv_sound hi⟩

theorem mixed_range_range {first key out : T} (h : MixedRange first key out) : Range key out := by
  obtain ⟨a,_,ha⟩ := h; exact ⟨a,ha⟩
end submission.Austin5947

set_option autoImplicit false
namespace submission.Austin5947
open T

def primary (key body : T) : Option (Small (p key body)) :=
  match body with
  | p x right => if mixedWith x key right (decode x) (decode key) then some ⟨x,by simp only [sz]; omega⟩ else none
  | k right => if mixedWith right key right (decode right) (decode key) then some ⟨right,by simp only [sz]; omega⟩ else none
  | e => none

def extra (key body : T) : Option (Small (p key body)) :=
  match key with
  | p h other =>
    match decode (p h other) with
    | none => none
    | some v =>
      match hshape : v.val with
      | p x rest =>
        if (inv x h).isSome then
          match decode v.val with
          | none => none
          | some w => if w.val = body then some ⟨x,by
              have hs := v.property; rw [hshape] at hs; simp only [sz] at hs ⊢; omega⟩ else none
        else none
      | _ => none
  | _ => none

theorem decode_pair (key body : T) : decode (p key body) = combine (primary key body) (extra key body) := by
  rw [decode.eq_def]
  cases key <;> cases body <;> rfl

def Primary (key body out : T) : Prop :=
  (∃ right, body = p out right ∧ MixedRange out key right) ∨ (body = k out ∧ MixedRange out key out)
def Extra (key body out : T) : Prop := ∃ h other v rest,
  key = p h other ∧ Code key v ∧ v = p out rest ∧ Range out h ∧ Code v body

theorem primary_sound {key body : T} {o : Small (p key body)}
    (h : primary key body = some o) : Primary key body o.val := by
  cases body with
  | e => cases h
  | k right =>
    simp only [primary] at h
    split at h
    · rename_i hr
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [←ho]; exact Or.inr ⟨rfl,(mixed_range_iff _ _ _).mpr hr⟩
    · cases h
  | p x right =>
    simp only [primary] at h
    split at h
    · rename_i hr
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [←ho]; exact Or.inl ⟨right,rfl,(mixed_range_iff _ _ _).mpr hr⟩
    · cases h

theorem primary_complete {key body out : T} (h : Primary key body out) :
    ∃ hs : sz out < sz (p key body), primary key body = some ⟨out,hs⟩ := by
  rcases h with ⟨right,rfl,hr⟩ | ⟨rfl,hr⟩
  all_goals refine ⟨by simp only [sz]; omega,?_⟩
  all_goals simp only [primary,if_pos ((mixed_range_iff _ _ _).mp hr)]

theorem extra_sound {key body : T} {o : Small (p key body)} (h : extra key body = some o) :
    Extra key body o.val := by
  cases key with
  | e => cases h
  | k a => cases h
  | p first other =>
    simp only [extra] at h
    split at h
    · cases h
    · rename_i v hv
      split at h
      · rename_i x rest hshape
        split at h
        · rename_i hr
          split at h
          · cases h
          · rename_i w hw
            split at h
            · rename_i he
              have ho := congrArg Subtype.val (Option.some.inj h)
              rw [←ho]
              refine ⟨first,other,v.val,rest,rfl,⟨v.property,hv⟩,hshape,(range_iff _ _).mpr hr,?_⟩
              rw [←he]; exact ⟨w.property,hw⟩
            · cases h
        · cases h
      · cases h

theorem extra_complete {key body out : T} (h : Extra key body out) :
    ∃ hs : sz out < sz (p key body), extra key body = some ⟨out,hs⟩ := by
  obtain ⟨first,other,v,rest,rfl,⟨hv,hd⟩,rfl,hr,⟨hw,hd'⟩⟩ := h
  refine ⟨by simp only [sz] at hv ⊢; omega,?_⟩
  simp only [extra,hd,if_pos ((range_iff _ _).mp hr),hd',↓reduceIte]

theorem combine_cases {b : T} {a c : Option (Small b)} {o : Small b}
    (h : combine a c = some o) : a = some o ∨ c = some o := by
  cases a <;> cases c <;> simp only [combine] at h ⊢
  · cases h
  · exact Or.inr h
  · exact Or.inl h
  · split at h
    · exact Or.inl h
    · cases h
theorem code_cases {key body out : T} (h : Code (p key body) out) : Primary key body out ∨ Extra key body out := by
  obtain ⟨hs,hd⟩ := h
  rw [decode_pair] at hd
  rcases combine_cases hd with hp | he
  · exact Or.inl (primary_sound hp)
  · exact Or.inr (extra_sound he)
end submission.Austin5947

set_option autoImplicit false
namespace submission.Austin5947
open T

def RightNode (child tree : T) : Prop := (∃ left, tree = p left child) ∨ tree = k child
theorem right_node_growth {child tree : T} (h : RightNode child tree) : sz child < sz tree := by
  rcases h with ⟨left,rfl⟩ | rfl <;> simp only [sz] <;> omega
theorem right_node_unique {a b tree : T} (ha : RightNode a tree) (hb : RightNode b tree) : a = b := by
  rcases ha with ⟨l,rfl⟩ | rfl <;> rcases hb with ⟨l',he⟩ | he
  · exact (T.p.inj he).2
  · cases he
  · cases he
  · exact T.k.inj he
theorem code_unique {b a c : T} (ha : Code b a) (hc : Code b c) : a = c := by
  obtain ⟨_,ha⟩ := ha; obtain ⟨_,hc⟩ := hc
  exact congrArg Subtype.val (Option.some.inj (ha.symm.trans hc))
theorem code_pair_q {key body out : T} (h : Code (p key body) out) : q key (p key body) = out :=
  q_hit ⟨body,rfl,h⟩
theorem step_cases {a b out : T} (h : q a b = out) : Plain a b out ∨ Hit a b out := by
  rw [←h]; exact q_cases a b
theorem step_hit_small {a b out : T} (h : q a b = out) (hs : sz out < sz b) : Hit a b out := by
  rw [←h]; apply hit_of_drop; rw [h]; exact hs
theorem range_small_code {b out : T} (hr : Range b out) (hs : sz out < sz b) : Code b out := by
  obtain ⟨a,ha⟩ := hr
  exact (step_hit_small ha hs).choose_spec.2
theorem range_small_eq {b out other : T} (hc : Code b out) (hr : Range b other)
    (hs : sz other < sz b) : other = out := code_unique (range_small_code hr hs) hc

theorem primary_image_node {key body out : T} (hp : Primary key body out) :
    ∃ right, RightNode right body ∧ Range key right := by
  rcases hp with ⟨right,hp,hr⟩ | ⟨hp,hr⟩
  · exact ⟨right,Or.inl ⟨out,hp⟩,mixed_range_range hr⟩
  · exact ⟨out,Or.inr hp,mixed_range_range hr⟩

theorem extra_body_small {key body out : T} (he : Extra key body out) : sz body < sz key := by
  obtain ⟨_,_,v,_,_,hcv,_,_,hcb⟩ := he
  have hs := code_small hcv
  have ht := code_small hcb
  omega

theorem primary_extra_disjoint {key body a out : T} (hp : Primary key body a) (he : Extra key body out) : False := by
  obtain ⟨_,_,v,_,_,hcv,_,_,hcb⟩ := he
  have hs := code_small hcv
  have ht := code_small hcb
  obtain ⟨right,hn,hr⟩ := primary_image_node hp
  have hb := right_node_growth hn
  have he := range_small_eq hcv hr (by omega)
  rw [he] at hb; omega

theorem code_of_primary {key body out : T} (hp : Primary key body out) : Code (p key body) out := by
  obtain ⟨hs,hd⟩ := primary_complete hp
  have he : extra key body = none := by
    cases h : extra key body with
    | none => rfl
    | some v => exact False.elim (primary_extra_disjoint hp (extra_sound h))
  exact ⟨hs,by rw [decode_pair,hd,he]; rfl⟩
theorem code_of_extra {key body out : T} (he : Extra key body out) : Code (p key body) out := by
  obtain ⟨hs,hd⟩ := extra_complete he
  have hp : primary key body = none := by
    cases h : primary key body with
    | none => rfl
    | some v => exact False.elim (primary_extra_disjoint (primary_sound h) he)
  exact ⟨hs,by rw [decode_pair,hp,hd]; rfl⟩

theorem no_code_range_extension {key body out : T} (hr : Range key body) : ¬Code (p key body) out := by
  intro hc
  rcases code_cases hc with hp | he
  · obtain ⟨right,hn,hrr⟩ := primary_image_node hp
    have hs := right_node_growth hn
    obtain ⟨a,ha⟩ := hr
    rcases step_cases ha with hp | hh
    · have hn' : RightNode key body := by
        rcases hp with hp | ⟨_,hp⟩
        · exact Or.inl ⟨a,hp⟩
        · exact Or.inr hp
      have he := right_node_unique hn hn'
      rw [he] at hrr; exact no_range_self key hrr
    · have hb := (hit_small hh).2
      have he := range_small_eq hh.choose_spec.2 hrr (by omega)
      rw [he] at hs; omega
  · obtain ⟨_,_,v,_,_,hcv,_,_,hcb⟩ := he
    have hv := code_small hcv
    have hb := code_small hcb
    have he := range_small_eq hcv hr (by omega)
    rw [he] at hb; omega
end submission.Austin5947

set_option autoImplicit false
namespace submission.Austin5947
open T

theorem inner_hit_completion {x y v w : T} (hr : MixedRange x y v) (hh : Hit x v w) : Extra y w x := by
  obtain ⟨h,hr,hv⟩ := hr
  obtain ⟨rest,hshape,hcv⟩ := hh
  rcases step_cases hv with hp | hh
  · rcases hp with hp | ⟨_,hp⟩
    · have he := (T.p.inj (hp.symm.trans hshape)).1
      rw [he] at hr; exact False.elim (no_range_self x hr)
    · rw [hp] at hshape; cases hshape
  · obtain ⟨other,hy,hcy⟩ := hh
    exact ⟨h,other,v,rest,hy,hcy,hshape,hr,hcv⟩

theorem plain_inner_ne_key {x y v w : T} (hr : MixedRange x y v) (hp : Plain x v w) : w ≠ y := by
  intro he
  rcases hp with hp | ⟨_,hp⟩
  · have hy : y = p x v := he.symm.trans hp
    have hs : sz v < sz y := by rw [hy]; simp only [sz]; omega
    obtain ⟨h,hr,hv⟩ := hr
    obtain ⟨other,hy',_⟩ := step_hit_small hv hs
    have hx := (T.p.inj (hy'.symm.trans hy)).1
    rw [hx] at hr; exact no_range_self x hr
  · have hy : y = k v := he.symm.trans hp
    have hs : sz v < sz y := by rw [hy]; simp only [sz]; omega
    have hc := range_small_code (mixed_range_range hr) hs
    rw [hy] at hc
    obtain ⟨_,hd⟩ := hc; rw [decode_k] at hd; cases hd

theorem plain_inner_preceding_raw {x y v w : T} (hr : MixedRange x y v) (hp : Plain x v w) : q y w = p y w := by
  have hwy := plain_inner_ne_key hr hp
  rcases q_cases y w with ho | hh
  · rcases ho with ho | ⟨he,_⟩
    · exact ho
    · exact False.elim (hwy he.symm)
  · obtain ⟨body,hs,hc⟩ := hh
    rcases hp with hp | ⟨_,hp⟩
    · have he := (T.p.inj (hp.symm.trans hs)).1
      have hv := mixed_range_range hr
      rw [hp,he] at hc
      exact False.elim (no_code_range_extension hv hc)
    · rw [hp] at hs; cases hs

theorem equation5947 (x y z : T) : x = q y (q y (q x (q (q z x) y))) := by
  let v := q (q z x) y
  let w := q x v
  have hr : MixedRange x y v := ⟨q z x,⟨z,rfl⟩,rfl⟩
  have hw : q x v = w := rfl
  have hc : Code (p y w) x ∧ q y w = p y w := by
    rcases step_cases hw with hp | hh
    · refine ⟨code_of_primary ?_,plain_inner_preceding_raw hr hp⟩
      rcases hp with hp | ⟨he,hp⟩
      · exact Or.inl ⟨v,hp,hr⟩
      · exact Or.inr ⟨by rw [he]; exact hp,by rw [←he] at hr; exact hr⟩
    · have he := inner_hit_completion hr hh
      exact ⟨code_of_extra he,q_of_larger_left (extra_body_small he)⟩
  change x = q y (q y w)
  rw [hc.2]
  exact (code_pair_q hc.1).symm
end submission.Austin5947

set_option autoImplicit false
namespace submission.Austin5947
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
theorem equation40057 (x y z : Carrier) :
    x = opposite (opposite (opposite (opposite y (opposite x z)) x) y) y :=
  equation5947 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op y (op y (op x (op (op z x) y)))) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation5947, embed_injective⟩
end submission.Austin5947

namespace submission
abbrev CM := Austin5947.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin5947.embed n = Austin5947.embed j) : n = j :=
  Austin5947.embed_injective n j h
end CM
instance modelMagma : Magma CM := ⟨Austin5947.opposite⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin5947.equation40057 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin5947.embed_injective 0 1
      (h (submission.Austin5947.embed 0) (submission.Austin5947.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

