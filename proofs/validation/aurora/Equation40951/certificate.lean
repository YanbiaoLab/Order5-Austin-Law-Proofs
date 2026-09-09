import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin5107
/- Experimental E5107 primitives; no source law is asserted here. -/
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

end submission.Austin5107

set_option autoImplicit false
namespace submission.Austin5107
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
end submission.Austin5107

set_option autoImplicit false
namespace submission.Austin5107
open T

def combine {b : T} (a c : Option (Small b)) : Option (Small b) :=
  match a,c with
  | none,_ => c
  | _,none => a
  | some x,some y => if x.val = y.val then a else none

def decode (b : T) : Option (Small b) :=
  match b with
  | p key (p repeated body) =>
    if he : repeated = key then
      have hk : sz key < sz (p key (p repeated body)) := by simp only [sz]; omega
      let primary : Option (Small (p key (p repeated body))) :=
        match body with
        | p left right =>
          match hi : inverseWith key right (decode key) with
          | none => none
          | some x => some ⟨x,by
              have hb := inverseWith_bound hi; simp only [sz]; omega⟩
        | k right =>
          match hi : inverseWith key right (decode key) with
          | none => none
          | some x => some ⟨x,by
              have hb := inverseWith_bound hi; simp only [sz]; omega⟩
        | e => none
      let rawExtra : Option (Small (p key (p repeated body))) :=
        match key with
        | p x other =>
          have hv : sz (p x (p x other)) < sz (p (p x other) (p repeated body)) := by
            have hs := congrArg sz he; simp only [sz] at hs ⊢; omega
          if (evalWith x (p x other) (decode (p x other))).val = p x (p x other) then
            match decode (p x (p x other)) with
            | none => none
            | some w => if w.val = body then some ⟨x,by simp only [sz]; omega⟩ else none
          else none
        | _ => none
      let hitExtra : Option (Small (p key (p repeated body))) :=
        match key with
        | p x other =>
          match decode (p x other) with
          | none => none
          | some v =>
            have hv : sz v.val < sz (p (p x other) (p repeated body)) := by
              have hs := v.property; simp only [sz] at hs ⊢; omega
            match decode v.val with
            | none => none
            | some w => if w.val = body then some ⟨x,by simp only [sz]; omega⟩ else none
        | _ => none
      combine primary (combine rawExtra hitExtra)
    else none
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
end submission.Austin5107

set_option autoImplicit false
namespace submission.Austin5107
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

end submission.Austin5107

set_option autoImplicit false
namespace submission.Austin5107
open T
abbrev Container (key body : T) := p key (p key body)

def primary (key body : T) : Option (Small (Container key body)) :=
  match body with
  | p left right =>
    match hi : inv key right with
    | none => none
    | some x => some ⟨x,by have hb := inverseWith_bound hi; simp only [Container,sz]; omega⟩
  | k right =>
    match hi : inv key right with
    | none => none
    | some x => some ⟨x,by have hb := inverseWith_bound hi; simp only [Container,sz]; omega⟩
  | e => none

def rawExtra (key body : T) : Option (Small (Container key body)) :=
  match key with
  | p x other =>
    if q x (p x other) = p x (p x other) then
      match decode (p x (p x other)) with
      | none => none
      | some w => if w.val = body then some ⟨x,by simp only [Container,sz]; omega⟩ else none
    else none
  | _ => none

def hitExtra (key body : T) : Option (Small (Container key body)) :=
  match key with
  | p x other =>
    match decode (p x other) with
    | none => none
    | some v =>
      match decode v.val with
      | none => none
      | some w => if w.val = body then some ⟨x,by simp only [Container,sz]; omega⟩ else none
  | _ => none

theorem decode_full (key body : T) : decode (Container key body) =
    combine (primary key body) (combine (rawExtra key body) (hitExtra key body)) := by
  rw [decode.eq_def]
  simp only [Container,dif_pos rfl]
  cases key <;> cases body <;> rfl

theorem code_shape {key rest out : T} (hc : Code (p key rest) out) : ∃ body, rest = p key body := by
  obtain ⟨_,hd⟩ := hc
  cases rest with
  | e => rw [decode.eq_def] at hd; cases hd
  | k a => rw [decode.eq_def] at hd; cases hd
  | p repeated body =>
    by_cases he : repeated = key
    · exact ⟨body,congrArg (fun t => p t body) he⟩
    · rw [decode.eq_def] at hd
      simp only [dif_neg he] at hd
      cases hd

def Primary (key body out : T) : Prop :=
  (∃ left, body = p left (q out key)) ∨ body = k (q out key)
def RawExtra (key body out : T) : Prop := ∃ other,
  key = p out other ∧ q out key = p out key ∧ Code (p out key) body
def HitExtra (key body out : T) : Prop := ∃ other v,
  key = p out other ∧ Code key v ∧ Code v body

theorem primary_sound {key body : T} {o : Small (Container key body)}
    (h : primary key body = some o) : Primary key body o.val := by
  cases body with
  | e => cases h
  | k right =>
    simp only [primary] at h
    split at h
    · cases h
    · rename_i x hi
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [←ho]
      exact Or.inr (congrArg k (inv_sound hi).symm)
  | p left right =>
    simp only [primary] at h
    split at h
    · cases h
    · rename_i x hi
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [←ho]
      exact Or.inl ⟨left,congrArg (p left) (inv_sound hi).symm⟩

theorem primary_complete {key body out : T} (h : Primary key body out) :
    ∃ hs : sz out < sz (Container key body), primary key body = some ⟨out,hs⟩ := by
  have hb := evalWith_left_bound out key (decode key)
  change sz out ≤ max (sz key) (sz (q out key)) at hb
  rcases h with ⟨left,rfl⟩ | rfl
  all_goals refine ⟨by simp only [Container,sz]; omega,?_⟩
  all_goals simp only [primary]
  all_goals split
  all_goals first
    | rename_i hi; rw [inv_complete] at hi; cases hi
    | rename_i x hi
      have he := Option.some.inj ((inv_complete out key).symm.trans hi)
      subst x
      rfl
  all_goals rfl

theorem rawExtra_sound {key body : T} {o : Small (Container key body)}
    (h : rawExtra key body = some o) : RawExtra key body o.val := by
  cases key with
  | e => cases h
  | k a => cases h
  | p x other =>
    simp only [rawExtra] at h
    split at h
    · rename_i hraw
      split at h
      · cases h
      · rename_i w hd
        split at h
        · rename_i hw
          have ho := congrArg Subtype.val (Option.some.inj h)
          rw [←ho]
          refine ⟨other,rfl,hraw,?_⟩
          rw [←hw]; exact ⟨w.property,hd⟩
        · cases h
    · cases h

theorem rawExtra_complete {key body out : T} (h : RawExtra key body out) :
    ∃ hs : sz out < sz (Container key body), rawExtra key body = some ⟨out,hs⟩ := by
  obtain ⟨other,rfl,hr,hc⟩ := h
  obtain ⟨hb,hd⟩ := hc
  refine ⟨by simp only [Container,sz]; omega,?_⟩
  simp only [rawExtra,if_pos hr,hd,↓reduceIte]

theorem hitExtra_sound {key body : T} {o : Small (Container key body)}
    (h : hitExtra key body = some o) : HitExtra key body o.val := by
  cases key with
  | e => cases h
  | k a => cases h
  | p x other =>
    simp only [hitExtra] at h
    split at h
    · cases h
    · rename_i v hd
      split at h
      · cases h
      · rename_i w hw
        split at h
        · rename_i ho
          have hx := congrArg Subtype.val (Option.some.inj h)
          rw [←hx]
          refine ⟨other,v.val,rfl,⟨v.property,hd⟩,?_⟩
          rw [←ho]; exact ⟨w.property,hw⟩
        · cases h

theorem hitExtra_complete {key body out : T} (h : HitExtra key body out) :
    ∃ hs : sz out < sz (Container key body), hitExtra key body = some ⟨out,hs⟩ := by
  obtain ⟨other,v,rfl,⟨hv,hd⟩,⟨hb,hw⟩⟩ := h
  refine ⟨by simp only [Container,sz]; omega,?_⟩
  simp only [hitExtra,hd,hw,↓reduceIte]

theorem combine_cases {b : T} {a c : Option (Small b)} {o : Small b}
    (h : combine a c = some o) : a = some o ∨ c = some o := by
  cases a <;> cases c <;> simp only [combine] at h ⊢
  · cases h
  · exact Or.inr h
  · exact Or.inl h
  · split at h
    · exact Or.inl h
    · cases h

theorem code_cases {key body out : T} (h : Code (Container key body) out) :
    Primary key body out ∨ RawExtra key body out ∨ HitExtra key body out := by
  obtain ⟨hs,hd⟩ := h
  rw [decode_full] at hd
  rcases combine_cases hd with hp | he
  · exact Or.inl (primary_sound hp)
  · rcases combine_cases he with hr | hh
    · exact Or.inr (Or.inl (rawExtra_sound hr))
    · exact Or.inr (Or.inr (hitExtra_sound hh))
end submission.Austin5107

set_option autoImplicit false
namespace submission.Austin5107
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
  rcases hp with ⟨left,hp⟩ | hp
  · exact ⟨q out key,Or.inl ⟨left,hp⟩,⟨out,rfl⟩⟩
  · exact ⟨q out key,Or.inr hp,⟨out,rfl⟩⟩

theorem code_body_bound {key rest out : T} (hc : Code (p key rest) out) : sz out < sz rest := by
  obtain ⟨body,rfl⟩ := code_shape hc
  rcases code_cases hc with hp | hr | hh
  · have hb := evalWith_left_bound out key (decode key)
    change sz out ≤ max (sz key) (sz (q out key)) at hb
    rcases hp with ⟨left,rfl⟩ | rfl <;> simp only [sz] <;> omega
  · obtain ⟨other,rfl,_⟩ := hr; simp only [sz]; omega
  · obtain ⟨other,v,rfl,_,_⟩ := hh
    simp only [sz]; omega

theorem raw_extra_body_small {key body out : T} (hr : RawExtra key body out) : sz body < sz key := by
  obtain ⟨_,_,_,hc⟩ := hr
  exact code_body_bound hc

theorem raw_extra_no_code {key body out v : T} (hr : RawExtra key body out) : ¬Code key v := by
  obtain ⟨other,hkey,hraw,_⟩ := hr
  intro hc
  have hs := code_small hc
  have hq : q out key = v := by rw [hkey] at hc ⊢; exact code_pair_q hc
  rw [hraw] at hq
  rw [←hq] at hs; simp only [sz] at hs; omega

theorem hit_extra_body_small {key body out : T} (hh : HitExtra key body out) : sz body < sz key := by
  obtain ⟨_,v,_,hc,hv⟩ := hh
  have hs := code_small hc
  have ht := code_small hv
  omega

theorem primary_raw_disjoint {key body a out : T} (hp : Primary key body a) (hr : RawExtra key body out) : False := by
  obtain ⟨right,hn,him⟩ := primary_image_node hp
  have hs := right_node_growth hn
  have hb := raw_extra_body_small hr
  exact raw_extra_no_code hr (range_small_code him (by omega))

theorem primary_hit_disjoint {key body a out : T} (hp : Primary key body a) (hh : HitExtra key body out) : False := by
  obtain ⟨_,v,_,hcv,hcb⟩ := hh
  have hv := code_small hcv
  have hb := code_small hcb
  obtain ⟨right,hn,hr⟩ := primary_image_node hp
  have hs := right_node_growth hn
  have he := range_small_eq hcv hr (by omega)
  rw [he] at hs; omega

theorem raw_hit_disjoint {key body a out : T} (hr : RawExtra key body a) (hh : HitExtra key body out) : False := by
  exact raw_extra_no_code hr hh.choose_spec.choose_spec.2.1

theorem code_of_primary {key body out : T} (hp : Primary key body out) : Code (Container key body) out := by
  obtain ⟨hs,hd⟩ := primary_complete hp
  have hr : rawExtra key body = none := by
    cases h : rawExtra key body with
    | none => rfl
    | some v => exact False.elim (primary_raw_disjoint hp (rawExtra_sound h))
  have hh : hitExtra key body = none := by
    cases h : hitExtra key body with
    | none => rfl
    | some v => exact False.elim (primary_hit_disjoint hp (hitExtra_sound h))
  exact ⟨hs,by rw [decode_full,hd,hr,hh]; rfl⟩

theorem code_of_raw {key body out : T} (hr : RawExtra key body out) : Code (Container key body) out := by
  obtain ⟨hs,hd⟩ := rawExtra_complete hr
  have hp : primary key body = none := by
    cases h : primary key body with
    | none => rfl
    | some v => exact False.elim (primary_raw_disjoint (primary_sound h) hr)
  have hh : hitExtra key body = none := by
    cases h : hitExtra key body with
    | none => rfl
    | some v => exact False.elim (raw_hit_disjoint hr (hitExtra_sound h))
  exact ⟨hs,by rw [decode_full,hp,hd,hh]; rfl⟩

theorem code_of_hit {key body out : T} (hh : HitExtra key body out) : Code (Container key body) out := by
  obtain ⟨hs,hd⟩ := hitExtra_complete hh
  have hp : primary key body = none := by
    cases h : primary key body with
    | none => rfl
    | some v => exact False.elim (primary_hit_disjoint (primary_sound h) hh)
  have hr : rawExtra key body = none := by
    cases h : rawExtra key body with
    | none => rfl
    | some v => exact False.elim (raw_hit_disjoint (rawExtra_sound h) hh)
  exact ⟨hs,by rw [decode_full,hp,hr,hd]; rfl⟩

end submission.Austin5107

set_option autoImplicit false
namespace submission.Austin5107
open T

theorem no_code_range_extension {key rest out : T} (hr : Range key rest) : ¬Code (p key rest) out := by
  intro hc
  obtain ⟨body,hrest⟩ := code_shape hc
  have hg : sz key < sz rest := by rw [hrest]; simp only [sz]; omega
  obtain ⟨a,ha⟩ := hr
  rcases step_cases ha with hp | hh
  · rcases hp with hp | ⟨_,hp⟩
    · have he := (T.p.inj (hp.symm.trans hrest)).1
      rw [he,q_square] at ha
      rw [hrest] at ha; cases ha
    · rw [hp] at hrest; cases hrest
  · have hs := (hit_small hh).2; omega

theorem no_code_full_image {key body out : T} (hr : Range key body) : ¬Code (Container key body) out := by
  intro hc
  rcases code_cases hc with hp | he | he
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
  · have hb := raw_extra_body_small he
    exact raw_extra_no_code he (range_small_code hr hb)
  · obtain ⟨_,v,_,hcv,hcb⟩ := he
    have hv := code_small hcv
    have hb := code_small hcb
    have he := range_small_eq hcv hr (by omega)
    rw [he] at hb; omega

theorem inner_hit_completion {x y z v w : T} (hv : q x y = v) (hh : Hit z v w) :
    RawExtra y w x ∨ HitExtra y w x := by
  obtain ⟨rest,hshape,hc⟩ := hh
  rcases step_cases hv with hp | hh
  · rcases hp with hp | ⟨_,hp⟩
    · have hc' : Code (p x y) w := by rw [←hp]; exact hc
      obtain ⟨other,hy⟩ := code_shape hc'
      exact Or.inl ⟨other,hy,hv.trans hp,hc'⟩
    · rw [hp] at hshape; cases hshape
  · obtain ⟨other,hy,hcy⟩ := hh
    exact Or.inr ⟨other,v,hy,hcy,hc⟩

theorem outer_two_small {y w : T} (hw : sz w < sz y) : q y (q y w) = Container y w := by
  rw [q_of_larger_left hw]
  rcases q_cases y (p y w) with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · exact hp
    · have hs := congrArg sz he; simp only [sz] at hs; omega
  · obtain ⟨body,he,hc⟩ := hh
    obtain ⟨rest,hr⟩ := code_shape hc
    rw [hr] at hw; simp only [sz] at hw; omega

theorem plain_inner_ne_key {x y v w : T} (hr : Range y v) (hp : Plain x v w) : w ≠ y := by
  intro he
  rcases hp with hp | ⟨_,hp⟩
  · have hy : y = p x v := he.symm.trans hp
    have hs : sz v < sz y := by rw [hy]; simp only [sz]; omega
    have hc := range_small_code hr hs
    rw [hy] at hc
    have hh := code_body_bound hc; omega
  · have hy : y = k v := he.symm.trans hp
    have hs : sz v < sz y := by rw [hy]; simp only [sz]; omega
    have hc := range_small_code hr hs
    rw [hy] at hc
    obtain ⟨_,hd⟩ := hc; rw [decode_k] at hd; cases hd

theorem plain_inner_first_raw {x y v w : T} (hr : Range y v) (hp : Plain x v w) : q y w = p y w := by
  have hwy := plain_inner_ne_key hr hp
  rcases q_cases y w with ho | hh
  · rcases ho with ho | ⟨he,_⟩
    · exact ho
    · exact False.elim (hwy he.symm)
  · obtain ⟨body,hs,hc⟩ := hh
    rcases hp with hp | ⟨_,hp⟩
    · have he := (T.p.inj (hp.symm.trans hs)).1
      rw [hp,he] at hc
      exact False.elim (no_code_range_extension hr hc)
    · rw [hp] at hs; cases hs

theorem plain_inner_second_raw {x y v w : T} (hr : Range y v) (hp : Plain x v w) :
    q y (p y w) = Container y w := by
  rcases q_cases y (p y w) with ho | hh
  · rcases ho with ho | ⟨he,_⟩
    · exact ho
    · exact False.elim (key_ne_pair w y he)
  · obtain ⟨body,hs,hc⟩ := hh
    obtain ⟨rest,hw⟩ := code_shape hc
    rcases hp with hp | ⟨_,hp⟩
    · have he := T.p.inj (hp.symm.trans hw)
      have hc' := hc
      rw [hp,he.1] at hc'
      exact False.elim (no_code_full_image hr hc')
    · rw [hp] at hw; cases hw

theorem equation5107 (x y z : T) : x = q y (q y (q y (q z (q x y)))) := by
  let v := q x y
  let w := q z v
  have hv : q x y = v := rfl
  have hw : q z v = w := rfl
  have hc : Code (Container y w) x ∧ q y (q y w) = Container y w := by
    rcases step_cases hw with hp | hh
    · refine ⟨code_of_primary ?_,?_⟩
      · rcases hp with hp | ⟨he,hp⟩
        · exact Or.inl ⟨z,by rw [hv]; exact hp⟩
        · exact Or.inr (by rw [hv]; exact hp)
      · rw [plain_inner_first_raw ⟨x,hv⟩ hp]
        exact plain_inner_second_raw ⟨x,hv⟩ hp
    · rcases inner_hit_completion hv hh with hr | hh
      · exact ⟨code_of_raw hr,outer_two_small (raw_extra_body_small hr)⟩
      · exact ⟨code_of_hit hh,outer_two_small (hit_extra_body_small hh)⟩
  change x = q y (q y (q y w))
  rw [hc.2]
  exact (code_pair_q hc.1).symm
end submission.Austin5107

set_option autoImplicit false
namespace submission.Austin5107
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
theorem equation40951 (x y z : Carrier) :
    x = opposite (opposite (opposite (opposite (opposite y x) z) y) y) y :=
  equation5107 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op y (op y (op y (op z (op x y))))) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation5107, embed_injective⟩
end submission.Austin5107

namespace submission
abbrev CM := Austin5107.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin5107.embed n = Austin5107.embed j) : n = j :=
  Austin5107.embed_injective n j h
end CM
instance modelMagma : Magma CM := ⟨Austin5107.opposite⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin5107.equation40951 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin5107.embed_injective 0 1
      (h (submission.Austin5107.embed 0) (submission.Austin5107.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

