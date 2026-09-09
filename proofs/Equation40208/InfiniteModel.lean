import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin5951
/- Experimental E5951 primitives; no source law is asserted here. -/
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

end submission.Austin5951

set_option autoImplicit false
namespace submission.Austin5951
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
end submission.Austin5951

set_option autoImplicit false
namespace submission.Austin5951
open T

def twiceWith (key out : T) (d : Option (Small key)) : Bool :=
  match inverseWith key out d with
  | none => false
  | some h => (inverseWith key h d).isSome

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
      | p x right => if twiceWith key right (decode key) then some ⟨x,by simp only [sz]; omega⟩ else none
      | k right => if twiceWith key right (decode key) then some ⟨right,by simp only [sz]; omega⟩ else none
      | e => none
    let fixed : Option (Small (p key body)) :=
      match key with
      | p (p x rest) other =>
        have hh : sz (p x rest) < sz (p (p (p x rest) other) body) := by simp only [sz]; omega
        match decode (p (p x rest) other) with
        | none => none
        | some v => if v.val = p x rest then
            match decode (p x rest) with
            | none => none
            | some w => if w.val = body then some ⟨x,by simp only [sz]; omega⟩ else none
          else none
      | _ => none
    let reentry : Option (Small (p key body)) :=
      match key with
      | p label other =>
        if label = body then
          match decode (p label other) with
          | none => none
          | some x =>
            have hx : sz x.val < sz (p (p label other) body) := by
              have hs := x.property; simp only [sz] at hs ⊢; omega
            if x.val ≠ body ∧ twiceWith x.val other (decode x.val) then some ⟨x.val,hx⟩ else none
        else none
      | _ => none
    combine primary (combine fixed reentry)
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
end submission.Austin5951

set_option autoImplicit false
namespace submission.Austin5951
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

def DoubleRange (key out : T) : Prop := ∃ h, Range key h ∧ q h key = out

theorem double_range_iff (key out : T) : DoubleRange key out ↔ twiceWith key out (decode key) = true := by
  change DoubleRange key out ↔ (match inv key out with | none => false | some h => (inv key h).isSome) = true
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

theorem double_range_range {key out : T} (h : DoubleRange key out) : Range key out := by
  obtain ⟨a,_,ha⟩ := h; exact ⟨a,ha⟩
end submission.Austin5951

set_option autoImplicit false
namespace submission.Austin5951
open T

def primary (key body : T) : Option (Small (p key body)) :=
  match body with
  | p x right => if twiceWith key right (decode key) then some ⟨x,by simp only [sz]; omega⟩ else none
  | k right => if twiceWith key right (decode key) then some ⟨right,by simp only [sz]; omega⟩ else none
  | e => none

def fixed (key body : T) : Option (Small (p key body)) :=
  match key with
  | p (p x rest) other =>
    match decode (p (p x rest) other) with
    | none => none
    | some v => if v.val = p x rest then
        match decode (p x rest) with
        | none => none
        | some w => if w.val = body then some ⟨x,by simp only [sz]; omega⟩ else none
      else none
  | _ => none

def reentry (key body : T) : Option (Small (p key body)) :=
  match key with
  | p label other =>
    if label = body then
      match decode (p label other) with
      | none => none
      | some x =>
        if x.val ≠ body ∧ twiceWith x.val other (decode x.val) then some ⟨x.val,by
            have hs := x.property; simp only [sz] at hs ⊢; omega⟩ else none
    else none
  | _ => none

theorem decode_pair (key body : T) : decode (p key body) =
    combine (primary key body) (combine (fixed key body) (reentry key body)) := by
  rw [decode.eq_def]
  cases key with
  | e => cases body <;> rfl
  | k a => cases body <;> rfl
  | p a b => cases a <;> cases body <;> rfl

def Primary (key body out : T) : Prop :=
  (∃ right, body = p out right ∧ DoubleRange key right) ∨ (body = k out ∧ DoubleRange key out)
def Fixed (key body out : T) : Prop := ∃ rest other,
  key = p (p out rest) other ∧ Code key (p out rest) ∧ Code (p out rest) body
def Reentry (key body out : T) : Prop := ∃ other,
  key = p body other ∧ Code key out ∧ out ≠ body ∧ DoubleRange out other

theorem primary_sound {key body : T} {o : Small (p key body)}
    (h : primary key body = some o) : Primary key body o.val := by
  cases body with
  | e => cases h
  | k right =>
    simp only [primary] at h
    split at h
    · rename_i hr
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [←ho]; exact Or.inr ⟨rfl,(double_range_iff _ _).mpr hr⟩
    · cases h
  | p x right =>
    simp only [primary] at h
    split at h
    · rename_i hr
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [←ho]; exact Or.inl ⟨right,rfl,(double_range_iff _ _).mpr hr⟩
    · cases h

theorem primary_complete {key body out : T} (h : Primary key body out) :
    ∃ hs : sz out < sz (p key body), primary key body = some ⟨out,hs⟩ := by
  rcases h with ⟨right,rfl,hr⟩ | ⟨rfl,hr⟩
  all_goals refine ⟨by simp only [sz]; omega,?_⟩
  all_goals simp only [primary,if_pos ((double_range_iff _ _).mp hr)]

theorem fixed_sound {key body : T} {o : Small (p key body)} (h : fixed key body = some o) :
    Fixed key body o.val := by
  unfold fixed at h
  split at h
  · rename_i x rest other
    split at h
    · cases h
    · rename_i v hv
      split at h
      · rename_i he
        split at h
        · cases h
        · rename_i w hw
          split at h
          · rename_i hew
            have ho := congrArg Subtype.val (Option.some.inj h)
            rw [←ho]
            refine ⟨rest,other,rfl,?_,?_⟩
            · have hc : Code (p (p x rest) other) v.val := ⟨v.property,hv⟩
              rw [he] at hc; exact hc
            · rw [←hew]; exact ⟨w.property,hw⟩
          · cases h
      · cases h
  · cases h

theorem fixed_complete {key body out : T} (h : Fixed key body out) :
    ∃ hs : sz out < sz (p key body), fixed key body = some ⟨out,hs⟩ := by
  obtain ⟨rest,other,rfl,⟨hv,hd⟩,⟨hw,hd'⟩⟩ := h
  refine ⟨by simp only [sz]; omega,?_⟩
  simp only [fixed,hd,hd',↓reduceIte]

theorem reentry_sound {key body : T} {o : Small (p key body)} (h : reentry key body = some o) :
    Reentry key body o.val := by
  cases key with
  | e => cases h
  | k a => cases h
  | p label other =>
    simp only [reentry] at h
    split at h
    · rename_i hl
      split at h
      · cases h
      · rename_i x hx
        split at h
        · rename_i hg
          have ho := congrArg Subtype.val (Option.some.inj h)
          rw [←ho]
          exact ⟨other,by rw [hl],⟨x.property,hx⟩,hg.1,(double_range_iff _ _).mpr hg.2⟩
        · cases h
    · cases h

theorem reentry_complete {key body out : T} (h : Reentry key body out) :
    ∃ hs : sz out < sz (p key body), reentry key body = some ⟨out,hs⟩ := by
  obtain ⟨other,rfl,⟨hx,hd⟩,hne,hr⟩ := h
  refine ⟨by simp only [sz] at hx ⊢; omega,?_⟩
  simp only [reentry,↓reduceIte,hd]
  rw [if_pos ⟨hne,(double_range_iff _ _).mp hr⟩]

theorem combine_cases {b : T} {a c : Option (Small b)} {o : Small b}
    (h : combine a c = some o) : a = some o ∨ c = some o := by
  cases a <;> cases c <;> simp only [combine] at h ⊢
  · cases h
  · exact Or.inr h
  · exact Or.inl h
  · split at h
    · exact Or.inl h
    · cases h

theorem code_cases {key body out : T} (h : Code (p key body) out) :
    Primary key body out ∨ Fixed key body out ∨ Reentry key body out := by
  obtain ⟨hs,hd⟩ := h
  rw [decode_pair] at hd
  rcases combine_cases hd with hp | he
  · exact Or.inl (primary_sound hp)
  · rcases combine_cases he with hf | hr
    · exact Or.inr (Or.inl (fixed_sound hf))
    · exact Or.inr (Or.inr (reentry_sound hr))
end submission.Austin5951

set_option autoImplicit false
namespace submission.Austin5951
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
    ∃ right, RightNode right body ∧ DoubleRange key right := by
  rcases hp with ⟨right,hp,hr⟩ | ⟨hp,hr⟩
  · exact ⟨right,Or.inl ⟨out,hp⟩,hr⟩
  · exact ⟨out,Or.inr hp,hr⟩

theorem fixed_out_small {key body out : T} (hf : Fixed key body out) : sz out < sz key := by
  obtain ⟨rest,other,rfl,_⟩ := hf; simp only [sz]; omega

theorem fixed_body_small {key body out : T} (hf : Fixed key body out) : sz body < sz key := by
  obtain ⟨rest,other,_,hk,hb⟩ := hf
  have hs := code_small hk
  have ht := code_small hb
  omega

theorem reentry_out_small {key body out : T} (hr : Reentry key body out) : sz out < sz key :=
  code_small hr.choose_spec.2.1

theorem reentry_body_small {key body out : T} (hr : Reentry key body out) : sz body < sz key := by
  obtain ⟨other,rfl,_⟩ := hr; simp only [sz]; omega

theorem code_max_bound {key body out : T} (hc : Code (p key body) out) : sz out < max (sz key) (sz body) := by
  rcases code_cases hc with hp | hf | hr
  · rcases hp with ⟨right,rfl,_⟩ | ⟨rfl,_⟩ <;> simp only [sz] <;> omega
  · have hs := fixed_out_small hf; omega
  · have hs := reentry_out_small hr; omega

theorem code_key_primary {key body : T} (hc : Code (p key body) key) : Primary key body key := by
  rcases code_cases hc with hp | hf | hr
  · exact hp
  · have hs := fixed_out_small hf; omega
  · have hs := reentry_out_small hr; omega

theorem double_range_small_fixed {key out : T} (hr : DoubleRange key out) (hs : sz out < sz key) : q out key = out := by
  obtain ⟨h,hr,hh⟩ := hr
  have hhit := step_hit_small hh hs
  have hhk := (hit_small hhit).1
  have hc := range_small_code hr hhk
  have he := code_unique hc hhit.choose_spec.2
  rw [he] at hh; exact hh

theorem fixed_point_hit {a b : T} (h : q a b = a) : Hit a b a := by
  rcases step_cases h with hp | hh
  · have hs := (plain_growth hp).1; omega
  · exact hh

theorem no_range_pair_self_left {key other : T} : ¬Range key (p key other) := by
  rintro ⟨a,ha⟩
  rcases step_cases ha with hp | hh
  · rcases hp with hp | ⟨_,hp⟩
    · have he := (T.p.inj hp).1
      rw [←he,q_square] at ha; cases ha
    · cases hp
  · have hs := (hit_small hh).2; simp only [sz] at hs; omega

theorem primary_fixed_disjoint {key body a out : T} (hp : Primary key body a) (hf : Fixed key body out) : False := by
  obtain ⟨rest,other,_,hck,hcb⟩ := hf
  have hbk := code_small hck
  have hbb := code_small hcb
  obtain ⟨right,hn,hr⟩ := primary_image_node hp
  have hs := right_node_growth hn
  have he := range_small_eq hck (double_range_range hr) (by omega)
  rw [he] at hs; omega

theorem primary_reentry_disjoint {key body a out : T} (hp : Primary key body a) (hr : Reentry key body out) : False := by
  have hb := reentry_body_small hr
  obtain ⟨other,hkey,_⟩ := hr
  obtain ⟨right,hn,hr⟩ := primary_image_node hp
  have hs := right_node_growth hn
  have hf := double_range_small_fixed hr (by omega)
  obtain ⟨rest,hshape,_⟩ := fixed_point_hit hf
  have he := (T.p.inj (hkey.symm.trans hshape)).1
  rw [he] at hs; omega

theorem fixed_reentry_disjoint {key body a out : T} (hf : Fixed key body a) (hr : Reentry key body out) : False := by
  obtain ⟨rest,other,hkey,hck,_⟩ := hf
  obtain ⟨other',hkey',hc,hne,_⟩ := hr
  have he := (T.p.inj (hkey'.symm.trans hkey)).1
  have ho := code_unique hc hck
  exact hne (ho.trans he.symm)

theorem code_of_primary {key body out : T} (hp : Primary key body out) : Code (p key body) out := by
  obtain ⟨hs,hd⟩ := primary_complete hp
  have hr : fixed key body = none := by
    cases h : fixed key body with
    | none => rfl
    | some v => exact False.elim (primary_fixed_disjoint hp (fixed_sound h))
  have hh : reentry key body = none := by
    cases h : reentry key body with
    | none => rfl
    | some v => exact False.elim (primary_reentry_disjoint hp (reentry_sound h))
  exact ⟨hs,by rw [decode_pair,hd,hr,hh]; rfl⟩

theorem code_of_fixed {key body out : T} (hr : Fixed key body out) : Code (p key body) out := by
  obtain ⟨hs,hd⟩ := fixed_complete hr
  have hp : primary key body = none := by
    cases h : primary key body with
    | none => rfl
    | some v => exact False.elim (primary_fixed_disjoint (primary_sound h) hr)
  have hh : reentry key body = none := by
    cases h : reentry key body with
    | none => rfl
    | some v => exact False.elim (fixed_reentry_disjoint hr (reentry_sound h))
  exact ⟨hs,by rw [decode_pair,hp,hd,hh]; rfl⟩

theorem code_of_reentry {key body out : T} (hh : Reentry key body out) : Code (p key body) out := by
  obtain ⟨hs,hd⟩ := reentry_complete hh
  have hp : primary key body = none := by
    cases h : primary key body with
    | none => rfl
    | some v => exact False.elim (primary_reentry_disjoint (primary_sound h) hh)
  have hr : fixed key body = none := by
    cases h : fixed key body with
    | none => rfl
    | some v => exact False.elim (fixed_reentry_disjoint (fixed_sound h) hh)
  exact ⟨hs,by rw [decode_pair,hp,hr,hd]; rfl⟩

end submission.Austin5951

set_option autoImplicit false
namespace submission.Austin5951
open T

theorem primary_body_growth {key body out : T} (hp : Primary key body out) : sz out < sz body := by
  rcases hp with ⟨right,rfl,_⟩ | ⟨rfl,_⟩ <;> simp only [sz] <;> omega

theorem code_key_right_node_impossible {key body : T} (hc : Code (p key body) key)
    (hn : RightNode key body) : False := by
  have hp := code_key_primary hc
  rcases hp with ⟨right,hy,hr⟩ | ⟨_,hr⟩
  · have he := right_node_unique (show RightNode right body from Or.inl ⟨key,hy⟩) hn
    rw [he] at hr
    exact no_range_self key (double_range_range hr)
  · exact no_range_self key (double_range_range hr)

theorem primary_on_plain_image_impossible {x y z w : T} (hp : Primary x y w)
    (hx : Plain z y x) : False := by
  have hyx := (plain_growth hx).2
  obtain ⟨right,hn,hr⟩ := primary_image_node hp
  have hry := right_node_growth hn
  have hf := double_range_small_fixed hr (by omega)
  obtain ⟨rest,hshape,hc⟩ := fixed_point_hit hf
  rcases hx with hx | ⟨_,hx⟩
  · have he := (T.p.inj (hshape.symm.trans hx)).2
    rw [hshape,he] at hc
    exact code_key_right_node_impossible hc hn
  · rw [hx] at hshape; cases hshape

theorem fixed_on_image_impossible {x y w : T} (hr : Range y x) (hf : Fixed x y w) : False := by
  obtain ⟨rest,other,hx,hcx,hcy⟩ := hf
  have hyh := code_small hcy
  have hhx : sz (p w rest) < sz x := by rw [hx]; simp only [sz]; omega
  obtain ⟨z,hz⟩ := hr
  have hp : Plain z y x := by
    rcases step_cases hz with hp | hh
    · exact hp
    · have hs := (hit_small hh).2; omega
  rcases hp with hp | ⟨_,hp⟩
  · have he := (T.p.inj (hx.symm.trans hp)).2
    rw [hx,he] at hcx
    have hs := primary_body_growth (code_key_primary hcx)
    omega
  · rw [hp] at hx; cases hx

theorem raw_inner_completion {x y w : T} (hr : Range y x) (hraw : q x y = p x y)
    (hc : Code (p x y) w) : Reentry y w x := by
  have hp : Primary x y w := by
    rcases code_cases hc with hp | hf | hre
    · exact hp
    · exact False.elim (fixed_on_image_impossible hr hf)
    · obtain ⟨other,hx,_⟩ := hre
      rw [hx] at hr; exact False.elim (no_range_pair_self_left hr)
  obtain ⟨z,hz⟩ := hr
  have hh : Hit z y x := by
    rcases step_cases hz with hpz | hh
    · exact False.elim (primary_on_plain_image_impossible hp hpz)
    · exact hh
  obtain ⟨other,hy,hcy⟩ := hh
  rcases hp with ⟨right,hp,hd⟩ | ⟨hp,_⟩
  · have he := T.p.inj (hp.symm.trans hy)
    have hne : x ≠ w := by
      intro hxw
      have hfix : q w y = x := by rw [he.1]; exact hz
      rw [←hxw,hraw] at hfix
      have hs := congrArg sz hfix; simp only [sz] at hs; omega
    exact ⟨right,hp,hcy,hne,hd⟩
  · rw [hp] at hy; cases hy

theorem inner_hit_completion {x y v w : T} (hr : DoubleRange y v) (hh : Hit x v w) :
    Fixed y w x ∨ Reentry y w x := by
  obtain ⟨h,hr,hv⟩ := hr
  obtain ⟨rest,hshape,hcv⟩ := hh
  rcases step_cases hv with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · have hhx := (T.p.inj (hp.symm.trans hshape)).1
      have hv' : q x y = p x y := by rw [←hhx]; exact hv.trans hp
      have hr' : Range y x := by rw [←hhx]; exact hr
      have hc' : Code (p x y) w := by rw [←hhx,←hp]; exact hcv
      exact Or.inr (raw_inner_completion hr' hv' hc')
    · rw [he] at hr; exact False.elim (no_range_self y hr)
  · have hs := (hit_small hh).1
    have hch := range_small_code hr hs
    have he := code_unique hch hh.choose_spec.2
    obtain ⟨other,hy,hcy⟩ := hh
    refine Or.inl ⟨rest,other,?_,?_,?_⟩
    · rw [he,hshape] at hy; exact hy
    · rw [hshape] at hcy; exact hcy
    · rw [hshape] at hcv; exact hcv
end submission.Austin5951

set_option autoImplicit false
namespace submission.Austin5951
open T

theorem no_code_double_extension {key body out : T} (hr : DoubleRange key body) : ¬Code (p key body) out := by
  intro hc
  rcases code_cases hc with hp | hf | hre
  · obtain ⟨right,hn,hrr⟩ := primary_image_node hp
    have hs := right_node_growth hn
    obtain ⟨a,_,ha⟩ := hr
    rcases step_cases ha with hp | hh
    · have hn' : RightNode key body := by
        rcases hp with hp | ⟨_,hp⟩
        · exact Or.inl ⟨a,hp⟩
        · exact Or.inr hp
      have he := right_node_unique hn hn'
      rw [he] at hrr
      exact no_range_self key (double_range_range hrr)
    · have hb := (hit_small hh).2
      have he := range_small_eq hh.choose_spec.2 (double_range_range hrr) (by omega)
      rw [he] at hs; omega
  · have hb := fixed_body_small hf
    obtain ⟨rest,other,_,hck,hcb⟩ := hf
    have he := range_small_eq hck (double_range_range hr) hb
    have hs := code_small hcb
    rw [he] at hs; omega
  · have hb := reentry_body_small hre
    obtain ⟨other,_,hck,hne,_⟩ := hre
    exact hne (range_small_eq hck (double_range_range hr) hb).symm

theorem plain_inner_ne_key {x y v w : T} (hr : DoubleRange y v) (hp : Plain x v w) : w ≠ y := by
  intro he
  rcases hp with hp | ⟨_,hp⟩
  · have hy : y = p x v := he.symm.trans hp
    have hs : sz v < sz y := by rw [hy]; simp only [sz]; omega
    have hf := double_range_small_fixed hr hs
    obtain ⟨other,hy',hc⟩ := fixed_point_hit hf
    have hx := (T.p.inj (hy.symm.trans hy')).1
    rw [hy,hx] at hc
    have hb := code_max_bound hc
    simp only [Nat.max_self] at hb; omega
  · have hy : y = k v := he.symm.trans hp
    have hs : sz v < sz y := by rw [hy]; simp only [sz]; omega
    have hc := range_small_code (double_range_range hr) hs
    rw [hy] at hc
    obtain ⟨_,hd⟩ := hc; rw [decode_k] at hd; cases hd

theorem plain_inner_preceding_raw {x y v w : T} (hr : DoubleRange y v) (hp : Plain x v w) : q y w = p y w := by
  have hwy := plain_inner_ne_key hr hp
  rcases q_cases y w with ho | hh
  · rcases ho with ho | ⟨he,_⟩
    · exact ho
    · exact False.elim (hwy he.symm)
  · obtain ⟨body,hs,hc⟩ := hh
    rcases hp with hp | ⟨_,hp⟩
    · have he := (T.p.inj (hp.symm.trans hs)).1
      rw [hp,he] at hc
      exact False.elim (no_code_double_extension hr hc)
    · rw [hp] at hs; cases hs

theorem equation5951 (x y z : T) : x = q y (q y (q x (q (q z y) y))) := by
  let v := q (q z y) y
  let w := q x v
  have hr : DoubleRange y v := ⟨q z y,⟨z,rfl⟩,rfl⟩
  have hw : q x v = w := rfl
  have hc : Code (p y w) x ∧ q y w = p y w := by
    rcases step_cases hw with hp | hh
    · refine ⟨code_of_primary ?_,plain_inner_preceding_raw hr hp⟩
      rcases hp with hp | ⟨he,hp⟩
      · exact Or.inl ⟨v,hp,hr⟩
      · exact Or.inr ⟨by rw [he]; exact hp,by rw [he]; exact hr⟩
    · rcases inner_hit_completion hr hh with hf | hre
      · exact ⟨code_of_fixed hf,q_of_larger_left (fixed_body_small hf)⟩
      · exact ⟨code_of_reentry hre,q_of_larger_left (reentry_body_small hre)⟩
  change x = q y (q y w)
  rw [hc.2]
  exact (code_pair_q hc.1).symm
end submission.Austin5951

set_option autoImplicit false
namespace submission.Austin5951
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
theorem equation40208 (x y z : Carrier) :
    x = opposite (opposite (opposite (opposite y (opposite y z)) x) y) y :=
  equation5951 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op y (op y (op x (op (op z y) y)))) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation5951, embed_injective⟩
end submission.Austin5951

namespace submission
abbrev CM := Austin5951.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin5951.embed n = Austin5951.embed j) : n = j :=
  Austin5951.embed_injective n j h
end CM
instance modelMagma : Magma CM := ⟨Austin5951.opposite⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin5951.equation40208 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin5951.embed_injective 0 1
      (h (submission.Austin5951.embed 0) (submission.Austin5951.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

