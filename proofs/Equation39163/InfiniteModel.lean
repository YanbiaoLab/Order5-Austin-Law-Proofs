import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin6895
/- Experimental E6895 primitives; no source law is asserted here. -/
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
abbrev Small (b : T) := {o : T // sz o ≤ sz b}
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

end submission.Austin6895

set_option autoImplicit false
namespace submission.Austin6895
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

theorem inverseWith_small (b out : T) (d : Option (Small b)) (hs : sz out ≤ sz b) :
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
end submission.Austin6895

set_option autoImplicit false
namespace submission.Austin6895
open T

def diagonal : T → Option T
  | k d => some d
  | p a b => if a = b then some a else none
  | e => none

def combine {b : T} (first second : Option (Small b)) : Option (Small b) :=
  match first,second with
  | none,_ => second
  | _,none => first
  | some a,some c => if a.val = c.val then first else none

def decode (b : T) : Option (Small b) :=
  match b with
  | p key body =>
    have hk : sz key < sz (p key body) := by simp only [sz]; omega
    let primary : Option (Small (p key body)) :=
      match body with
      | p left right =>
        match hi : inverseWith key right (decode key) with
        | none => none
        | some x =>
          have hx : sz x < sz (p key (p left right)) := by
            have h := inverseWith_bound hi; simp only [sz]; omega
          if (inverseWith key left (decode key)).isSome then some ⟨x,Nat.le_of_lt hx⟩ else none
      | k child =>
        match hi : inverseWith key child (decode key) with
        | none => none
        | some x =>
          have hx : sz x < sz (p key (k child)) := by
            have h := inverseWith_bound hi; simp only [sz]; omega
          if (inverseWith key child (decode key)).isSome then some ⟨x,Nat.le_of_lt hx⟩ else none
      | e => none
    let extra : Option (Small (p key body)) :=
      match diagonal key with
      | none => none
      | some d =>
        if key ≠ body ∧ (evalWith d body (decode body)).val = d then
          some ⟨p body key,by simp only [sz]; omega⟩
        else none

    combine primary extra
  | _ => none
termination_by sz b
decreasing_by all_goals first | assumption | simp only [sz]; omega

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
end submission.Austin6895

set_option autoImplicit false
namespace submission.Austin6895
open T

def Code (b out : T) : Prop := ∃ h : sz out ≤ sz b, decode b = some ⟨out, h⟩
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

theorem code_small {b out : T} (h : Code b out) : sz out ≤ sz b := h.choose
theorem hit_small {a b out : T} (h : Hit a b out) : sz a < sz b ∧ sz out ≤ sz b := by
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

end submission.Austin6895

set_option autoImplicit false
namespace submission.Austin6895
open T

def primary (key body : T) : Option (Small (p key body)) :=
  match body with
  | p left right =>
    match hi : inv key right with
    | none => none
    | some x =>
      if (inv key left).isSome then
        some ⟨x,by have h := inverseWith_bound hi; simp only [sz]; omega⟩ else none
  | k child =>
    match hi : inv key child with
    | none => none
    | some x =>
      if (inv key child).isSome then
        some ⟨x,by have h := inverseWith_bound hi; simp only [sz]; omega⟩ else none
  | e => none
def extra (key body : T) : Option (Small (p key body)) :=
  match diagonal key with
  | none => none
  | some d => if key ≠ body ∧ q d body = d then
      some ⟨p body key,by simp only [sz]; omega⟩ else none
theorem decode_pair (key body : T) : decode (p key body) = combine (primary key body) (extra key body) := by
  rw [decode.eq_def]
  cases key <;> cases body <;> rfl

def Primary (key body out : T) : Prop :=
  (∃ left, body = p left (q out key) ∧ Range key left) ∨
  (body = k (q out key) ∧ Range key (q out key))
def Extra (key body out : T) : Prop := ∃ d,
  diagonal key = some d ∧ key ≠ body ∧ q d body = d ∧ out = p body key

theorem primary_sound {key body : T} {o : Small (p key body)} (h : primary key body = some o) :
    Primary key body o.val := by
  cases body with
  | e => simp [primary] at h
  | p left right =>
    simp only [primary] at h
    split at h
    · cases h
    · rename_i x hi
      split at h
      · rename_i hr
        have ho := congrArg Subtype.val (Option.some.inj h)
        rw [←ho]
        exact Or.inl ⟨left,by rw [inv_sound hi],(range_iff _ _).mpr hr⟩
      · cases h
  | k child =>
    simp only [primary] at h
    split at h
    · cases h
    · rename_i x hi
      split at h
      · rename_i hr
        have ho := congrArg Subtype.val (Option.some.inj h)
        rw [←ho]
        exact Or.inr ⟨congrArg k (inv_sound hi).symm,by rw [inv_sound hi]; exact (range_iff _ _).mpr hr⟩
      · cases h

theorem primary_complete {key body out : T} (h : Primary key body out) :
    ∃ hs : sz out ≤ sz (p key body), primary key body = some ⟨out,hs⟩ := by
  have hbound := evalWith_left_bound out key (decode key)
  change sz out ≤ max (sz key) (sz (q out key)) at hbound
  rcases h with ⟨left,rfl,hr⟩ | ⟨rfl,hr⟩
  all_goals refine ⟨by simp only [sz]; omega,?_⟩
  all_goals simp only [primary]
  all_goals split
  all_goals first
    | rename_i hi; rw [inv_complete] at hi; cases hi
    | rename_i x hi
      have he := Option.some.inj ((inv_complete out key).symm.trans hi)
      subst x
      rw [if_pos ((range_iff _ _).mp hr)]
  all_goals rw [if_pos ((range_iff _ _).mp hr)]

theorem extra_sound {key body : T} {o : Small (p key body)} (h : extra key body = some o) :
    Extra key body o.val := by
  unfold extra at h
  split at h
  · cases h
  · rename_i d hd
    split at h
    · rename_i hf
      have ho := congrArg Subtype.val (Option.some.inj h)
      exact ⟨d,hd,hf.1,hf.2,ho.symm⟩
    · cases h

theorem extra_complete {key body out : T} (h : Extra key body out) :
    ∃ hs : sz out ≤ sz (p key body), extra key body = some ⟨out,hs⟩ := by
  obtain ⟨d,hd,hne,hq,rfl⟩ := h
  refine ⟨by simp only [sz]; omega,?_⟩
  simp only [extra,hd]
  rw [if_pos ⟨hne,hq⟩]

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
end submission.Austin6895

set_option autoImplicit false
namespace submission.Austin6895
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
theorem primary_right_node {key body out : T} (h : Primary key body out) : RightNode (q out key) body := by
  rcases h with ⟨left,he,_⟩ | ⟨he,_⟩
  · exact Or.inl ⟨left,he⟩
  · exact Or.inr he
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

theorem primary_small {key body out : T} (hp : Primary key body out) : sz out < sz (p key body) := by
  have hs := right_node_growth (primary_right_node hp)
  have hb := evalWith_left_bound out key (decode key)
  change sz out ≤ max (sz key) (sz (q out key)) at hb
  simp only [sz]; omega

theorem code_ne_self {b : T} : ¬Code b b := by
  intro hc
  cases b with
  | e => obtain ⟨_,hd⟩ := hc; rw [decode_e] at hd; cases hd
  | k a => obtain ⟨_,hd⟩ := hc; rw [decode_k] at hd; cases hd
  | p key body =>
    rcases code_cases hc with hp | he
    · have hs := primary_small hp; omega
    · obtain ⟨_,_,hne,_,ho⟩ := he
      exact hne (T.p.inj ho).1

theorem q_ne_right (a b : T) : q a b ≠ b := by
  intro he
  rcases step_cases he with hp | hh
  · have hs := (plain_growth hp).2; omega
  · exact code_ne_self hh.choose_spec.2

theorem no_range_self (b : T) : ¬Range b b := by
  rintro ⟨a,h⟩; exact q_ne_right a b h

theorem no_fixed_diagonal (a : T) : ¬Code (p a a) a := by
  intro hc
  rcases code_cases hc with hp | he
  · have hs := right_node_growth (primary_right_node hp)
    rw [q_square] at hs; simp only [sz] at hs; omega
  · exact he.choose_spec.2.1 rfl

theorem no_code_diagonal (a out : T) : ¬Code (p a a) out := by
  intro hc
  have hp : Primary a a out := by
    rcases code_cases hc with hp | he
    · exact hp
    · exact False.elim (he.choose_spec.2.1 rfl)
  unfold Primary at hp
  generalize hu : q out a = u at hp
  rcases hp with ⟨left,ha,hr⟩ | ⟨ha,_⟩
  · have hsmall : sz u < sz a := by rw [ha]; simp only [sz]; omega
    have hl : sz left < sz a := by rw [ha]; simp only [sz]; omega
    have cc := range_small_code ⟨out,hu⟩ hsmall
    have he := range_small_eq cc hr hl
    rw [he] at ha
    rw [ha] at cc
    exact no_fixed_diagonal _ cc
  · have hsmall : sz u < sz a := by rw [ha]; simp only [sz]; omega
    have cc := range_small_code ⟨out,hu⟩ hsmall
    rw [ha] at cc
    obtain ⟨_,hd⟩ := cc; rw [decode_k] at hd; cases hd

theorem diagonal_cases {key d : T} (h : diagonal key = some d) : key = k d ∨ key = p d d := by
  cases key with
  | e => cases h
  | k a => exact Or.inl (congrArg k (Option.some.inj h))
  | p a b =>
    simp only [diagonal] at h
    split at h
    · rename_i he
      have ha := Option.some.inj h
      subst a; subst b; exact Or.inr rfl
    · cases h

theorem diagonal_no_code {key d out : T} (hd : diagonal key = some d) : ¬Code key out := by
  rcases diagonal_cases hd with rfl | rfl
  · rintro ⟨_,h⟩; rw [decode_k] at h; cases h
  · exact no_code_diagonal d out

theorem diagonal_growth {key d : T} (hd : diagonal key = some d) : sz d < sz key := by
  rcases diagonal_cases hd with rfl | rfl <;> simp only [sz] <;> omega

theorem fixed_point_hit {a b : T} (h : q a b = a) : Hit a b a := by
  rcases step_cases h with hp | hh
  · have hs := (plain_growth hp).1; omega
  · exact hh

theorem primary_extra_disjoint {key body a x : T} (hp : Primary key body a) (he : Extra key body x) : False := by
  obtain ⟨d,hd,_,hf,_⟩ := he
  obtain ⟨other,hbody,_⟩ := fixed_point_hit hf
  have hr : Range key d := by
    rcases hp with ⟨left,hp,hr⟩ | ⟨hp,_⟩
    · have he := (T.p.inj (hp.symm.trans hbody)).1
      rw [←he]; exact hr
    · rw [hp] at hbody; cases hbody
  exact diagonal_no_code hd (range_small_code hr (diagonal_growth hd))

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

end submission.Austin6895

set_option autoImplicit false
namespace submission.Austin6895
open T

theorem plain_of_output_large {a b out : T} (h : q a b = out) (hs : sz b < sz out) : Plain a b out := by
  rcases step_cases h with hp | hh
  · exact hp
  · have ho := (hit_small hh).2; omega

theorem range_reverse_no_hit {a b out : T} (hr : Range a b) : ¬Hit a b out := by
  intro hh
  have hs := (hit_small hh).1
  obtain ⟨r,hb,hc⟩ := hh
  obtain ⟨z,hz⟩ := hr
  rcases plain_of_output_large hz hs with hp | ⟨_,hp⟩
  · have he := (T.p.inj (hp.symm.trans hb)).2
    rw [←he] at hb
    rw [hb] at hc
    exact no_code_diagonal a out hc
  · rw [hp] at hb; cases hb

theorem range_reverse_raw {a b : T} (hr : Range a b) : q a b = p a b := by
  rcases q_cases a b with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · exact hp
    · rw [he] at hr; exact False.elim (no_range_self b hr)
  · exact False.elim (range_reverse_no_hit hr hh)

theorem no_code_paired_ranges {key body out : T} (hc : Code (p key body) out)
    (hk : Range out key) (hb : Range out body) : False := by
  rcases code_cases hc with hp | he
  · have hn := primary_right_node hp
    have hq := range_reverse_raw hk
    rw [hq] at hn
    have hs := right_node_growth hn
    have hsmall : sz out < sz body := by simp only [sz] at hs; omega
    obtain ⟨a,ha⟩ := hb
    have hn' : RightNode out body := by
      rcases plain_of_output_large ha hsmall with hp | ⟨_,hp⟩
      · exact Or.inl ⟨a,hp⟩
      · exact Or.inr hp
    have he := congrArg sz (right_node_unique hn hn')
    simp only [sz] at he; omega
  · obtain ⟨_,_,hne,_,ho⟩ := he
    have hk' : sz key < sz out := by rw [ho]; simp only [sz]; omega
    have hb' : sz body < sz out := by rw [ho]; simp only [sz]; omega
    exact hne (code_unique (range_small_code hk hk') (range_small_code hb hb'))

theorem inner_hit_structure {x y z u v w : T} (hu : q z y = u) (hv : q x y = v)
    (hh : Hit u v w) : u = x ∧ v = p x y ∧ Code (p x y) w := by
  have huv := (hit_small hh).1
  obtain ⟨body,hshape,hcv⟩ := hh
  have hp : Plain x y v := by
    rcases step_cases hv with hp | hh
    · exact hp
    · have hvy := (hit_small hh).2
      have hcu := range_small_code ⟨z,hu⟩ (by omega)
      have he := code_unique hcu hh.choose_spec.2
      rw [he] at huv; omega
  rcases hp with hp | ⟨_,hp⟩
  · have he := (T.p.inj (hp.symm.trans hshape)).1
    refine ⟨he.symm,hp,?_⟩
    rw [←hp]; exact hcv
  · rw [hp] at hshape; cases hshape

theorem extra_on_image_impossible {x y w : T} (hr : Range y x) (he : Extra x y w) : False := by
  obtain ⟨d,hd,_,hf,_⟩ := he
  have hh := fixed_point_hit hf
  have hdb := (hit_small hh).1
  have hdx := diagonal_growth hd
  obtain ⟨z,hz⟩ := hr
  have hp : Plain z y x := by
    rcases step_cases hz with hp | hh'
    · exact hp
    · have h := code_unique hh'.choose_spec.2 hh.choose_spec.2
      rw [h] at hdx; omega
  rcases diagonal_cases hd with hd | hd
  · rcases hp with hp | ⟨_,hp⟩
    · rw [hd] at hp; cases hp
    · have he := T.k.inj (hd.symm.trans hp)
      rw [he] at hdb; omega
  · rcases hp with hp | ⟨_,hp⟩
    · have he := (T.p.inj (hd.symm.trans hp)).2
      rw [he] at hdb; omega
    · rw [hd] at hp; cases hp

theorem inner_code_primary {x y w : T} (hr : Range y x) (hc : Code (p x y) w) : Primary x y w := by
  rcases code_cases hc with hp | he
  · exact hp
  · exact False.elim (extra_on_image_impossible hr he)

theorem image_inner_primary_raw {x y z w : T} (hx : q z y = x) (hp : Primary x y w) : x = p z y := by
  have hplain : Plain z y x := by
    rcases step_cases hx with hplain | hh
    · exact hplain
    · obtain ⟨other,hy,hc⟩ := hh
      rcases hp with ⟨left,hp,hr⟩ | ⟨hp,_⟩
      · have he := T.p.inj (hp.symm.trans hy)
        apply False.elim (no_code_paired_ranges (by rw [←hy]; exact hc) ?_ ?_)
        · rw [←he.1]; exact hr
        · rw [←he.2]; exact ⟨w,rfl⟩
      · rw [hp] at hy; cases hy
  rcases hplain with hplain | ⟨_,hs⟩
  · exact hplain
  · have hn := primary_right_node hp
    have hty := right_node_growth hn
    have hh : Hit w x (q w x) := by
      apply hit_of_drop
      have hxy : sz y < sz x := by rw [hs]; simp only [sz]; omega
      omega
    obtain ⟨body,hshape,_⟩ := hh
    rw [hs] at hshape; cases hshape

theorem inner_hit_completion {x y z u v w : T} (hu : q z y = u) (hv : q x y = v)
    (hh : Hit u v w) : Extra y w x := by
  obtain ⟨hux,_,hc⟩ := inner_hit_structure hu hv hh
  have hx : q z y = x := hu.trans hux
  have hp := inner_code_primary ⟨z,hx⟩ hc
  have hraw := image_inner_primary_raw hx hp
  unfold Primary at hp
  generalize ht : q w x = t at hp
  have hn : RightNode t y := by
    rcases hp with ⟨left,hy,_⟩ | ⟨hy,_⟩
    · exact Or.inl ⟨left,hy⟩
    · exact Or.inr hy
  have hty := right_node_growth hn
  have hhit : Hit w x t := step_hit_small ht (by rw [hraw]; simp only [sz]; omega)
  obtain ⟨r,hshape,hct⟩ := hhit
  have hw : w = z := (T.p.inj (hshape.symm.trans hraw)).1
  have hd : diagonal y = some t := by
    rcases hp with ⟨left,hy,hr⟩ | ⟨hy,_⟩
    · have hleft : sz left < sz x := by
        have hs : sz left < sz y := by rw [hy]; simp only [sz]; omega
        rw [hraw]; simp only [sz]; omega
      have he := range_small_eq hct hr hleft
      rw [hy,he]; simp [diagonal]
    · rw [hy]; rfl
  have hpt : Primary z y t := by
    rw [hraw] at hct
    rcases code_cases hct with hp | he
    · exact hp
    · obtain ⟨_,_,_,_,he⟩ := he
      rw [he] at hty; simp only [sz] at hty; omega
  have hft : q t z = t := right_node_unique (primary_right_node hpt) hn
  have hyz : y ≠ z := by
    intro he
    have hc := (fixed_point_hit hft).choose_spec.2
    rw [←he] at hc
    exact diagonal_no_code hd hc
  exact ⟨t,hd,by rw [hw]; exact hyz,by rw [hw]; exact hft,by rw [hw]; exact hraw⟩

end submission.Austin6895

set_option autoImplicit false
namespace submission.Austin6895
open T

theorem diagonal_right_node {key d : T} (hd : diagonal key = some d) : RightNode d key := by
  rcases diagonal_cases hd with hd | hd
  · exact Or.inr hd
  · exact Or.inl ⟨d,hd⟩

theorem diagonal_outer_no_return {key d : T} (hd : diagonal key = some d) : ¬Code (p d key) d := by
  intro hc
  rcases code_cases hc with hp | he
  · have he := right_node_unique (primary_right_node hp) (diagonal_right_node hd)
    rw [q_square] at he
    have hs := congrArg sz he; simp only [sz] at hs; omega
  · have hs := congrArg sz he.choose_spec.2.2.2
    simp only [sz] at hs; omega

theorem no_code_range_extension {key body out : T} (hr : Range key body) : ¬Code (p key body) out := by
  intro hc
  rcases code_cases hc with hp | he
  · have hn := primary_right_node hp
    have hs := right_node_growth hn
    obtain ⟨a,ha⟩ := hr
    rcases step_cases ha with hb | hh
    · have hn' : RightNode key body := by
        rcases hb with hb | ⟨_,hb⟩
        · exact Or.inl ⟨a,hb⟩
        · exact Or.inr hb
      exact q_ne_right out key (right_node_unique hn hn')
    · have hbk := (hit_small hh).2
      have heq := range_small_eq hh.choose_spec.2 (show Range key (q out key) from ⟨out,rfl⟩) (by omega)
      rw [heq] at hs; omega
  · obtain ⟨d,hd,_,hf,_⟩ := he
    obtain ⟨other,hbody,hcb⟩ := fixed_point_hit hf
    obtain ⟨a,ha⟩ := hr
    have hp : Plain a key body := by
      rcases step_cases ha with hp | hh
      · exact hp
      · exact False.elim (diagonal_no_code hd hh.choose_spec.2)
    rcases hp with hp | ⟨_,hp⟩
    · have he := (T.p.inj (hbody.symm.trans hp)).2
      rw [hbody,he] at hcb
      exact diagonal_outer_no_return hd hcb
    · rw [hp] at hbody; cases hbody

theorem plain_inner_preceding_raw {x y u v w : T} (hv : q x y = v)
    (hp : Plain u v w) (hc : Code (p y w) x) : q y w = p y w := by
  have hwy : w ≠ y := by
    intro he; rw [he] at hc; exact no_code_diagonal y x hc
  rcases q_cases y w with ho | hh
  · rcases ho with ho | ⟨he,_⟩
    · exact ho
    · exact False.elim (hwy he.symm)
  · obtain ⟨body,hs,hc⟩ := hh
    rcases hp with hp | ⟨_,hp⟩
    · have hshape := (T.p.inj (hp.symm.trans hs)).1
      rw [hp,hshape] at hc
      exact False.elim (no_code_range_extension ⟨x,hv⟩ hc)
    · rw [hp] at hs; cases hs

theorem extra_preceding_raw {y w x : T} (he : Extra y w x) : q y w = p y w := by
  obtain ⟨d,hd,hyw,hf,_⟩ := he
  obtain ⟨other,hw,_⟩ := fixed_point_hit hf
  have hdy := diagonal_growth hd
  rcases q_cases y w with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · exact hp
    · exact False.elim (hyw he)
  · obtain ⟨body,hw',_⟩ := hh
    have he := (T.p.inj (hw.symm.trans hw')).1
    rw [he] at hdy; omega

theorem equation6895 (x y z : T) : x = q y (q y (q (q z y) (q x y))) := by
  let u := q z y
  let v := q x y
  let w := q u v
  have hu : q z y = u := rfl
  have hv : q x y = v := rfl
  have hw : q u v = w := rfl
  have hc : Code (p y w) x ∧ q y w = p y w := by
    rcases step_cases hw with hp | hh
    · have hc : Code (p y w) x := by
        apply code_of_primary
        rcases hp with hp | ⟨he,hp⟩
        · exact Or.inl ⟨u,by rw [hv]; exact hp,⟨z,hu⟩⟩
        · exact Or.inr ⟨by rw [hv]; exact hp,⟨x,rfl⟩⟩
      exact ⟨hc,plain_inner_preceding_raw hv hp hc⟩
    · have he := inner_hit_completion hu hv hh
      exact ⟨code_of_extra he,extra_preceding_raw he⟩
  change x = q y (q y w)
  rw [hc.2]
  exact (code_pair_q hc.1).symm
end submission.Austin6895

set_option autoImplicit false
namespace submission.Austin6895
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
theorem equation39163 (x y z : Carrier) :
    x = opposite (opposite (opposite (opposite y x) (opposite y z)) y) y :=
  equation6895 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op y (op y (op (op z y) (op x y)))) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation6895, embed_injective⟩
end submission.Austin6895

namespace submission
abbrev CM := Austin6895.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin6895.embed n = Austin6895.embed j) : n = j :=
  Austin6895.embed_injective n j h
end CM
instance modelMagma : Magma CM := ⟨Austin6895.opposite⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin6895.equation39163 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin6895.embed_injective 0 1
      (h (submission.Austin6895.embed 0) (submission.Austin6895.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

