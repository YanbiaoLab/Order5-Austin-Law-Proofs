import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin6820
/- Total, size-recursive decoder. Law.lean proves E6820; Model.lean proves infinity. -/
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

end submission.Austin6820

set_option autoImplicit false
namespace submission.Austin6820
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
end submission.Austin6820

set_option autoImplicit false
namespace submission.Austin6820
open T

def agrees {b : T} (out : T) : Option (Small b) → Bool
  | none => true
  | some a => a.val == out
def combine {b : T} (first second : Option (Small b)) : Option (Small b) :=
  match first with
  | none => second
  | some a => if agrees a.val second then first else none
def merge3 {b : T} (first second third : Option (Small b)) : Option (Small b) :=
  match first with
  | none => combine second third
  | some a => if agrees a.val second ∧ agrees a.val third then first else none

def decode (b : T) : Option (Small b) :=
  match b with
  | p key body =>
    have hkey : sz key < sz (p key body) := by simp only [sz]; omega
    have hbody : sz body < sz (p key body) := by simp only [sz]; omega
    let primary : Option (Small (p key body)) :=
      match body with
      | p left right =>
        match hi : inverseWith key left (decode key) with
        | none => none
        | some x =>
          if (inverseWith key right (decode key)).isSome then
            some ⟨x, by have hs := inverseWith_bound hi; simp only [sz]; omega⟩
          else none
      | k child =>
        match hi : inverseWith key child (decode key) with
        | none => none
        | some x => some ⟨x, by have hs := inverseWith_bound hi; simp only [sz]; omega⟩
      | e => none
    let fixed : Option (Small (p key body)) :=
      match key with
      | p target other =>
        if p target other ≠ body ∧ (evalWith target body (decode body)).val = target ∧
            (inverseWith body other (decode body)).isSome then
          some ⟨body, by simp only [sz]; omega⟩ else none
      | k target =>
        if k target ≠ body ∧ (evalWith target body (decode body)).val = target ∧
            (inverseWith body target (decode body)).isSome then
          some ⟨body, by simp only [sz]; omega⟩ else none
      | e => none
    let extra : Option (Small (p key body)) :=
      match key with
      | p x other =>
        if hs : sz body < sz (p x other) then
          match decode (p x other) with
          | none => none
          | some u =>
            have hu : sz u.val < sz (p (p x other) body) := by
              have h := u.property; simp only [sz] at h ⊢; omega
            if u.val ≠ x ∧ (evalWith body u.val (decode u.val)).val = x ∧
                (inverseWith u.val other (decode u.val)).isSome then
              some ⟨x, by simp only [sz]; omega⟩ else none
        else none
      | _ => none
    merge3 primary fixed extra
  | _ => none
termination_by sz b
decreasing_by all_goals assumption

def q (a b : T) : T := (evalWith a b (decode b)).val
def inv (b out : T) : Option T := inverseWith b out (decode b)
theorem inv_sound {b out a : T} (h : inv b out = some a) : q a b = out := inverseWith_sound h
@[simp] theorem inv_complete (a b : T) : inv b (q a b) = some a := inverseWith_complete _ _ _
theorem q_right_injective (a a' b : T) (he : q a b = q a' b) : a = a' := by
  have h := congrArg (inv b) he
  simpa only [inv_complete, Option.some.injEq] using h
@[simp] theorem q_square (a : T) : q a a = k a := evalWith_square _ _
@[simp] theorem decode_e : decode e = none := by rw [decode.eq_def]
@[simp] theorem decode_k (a : T) : decode (k a) = none := by rw [decode.eq_def]

end submission.Austin6820

set_option autoImplicit false
namespace submission.Austin6820
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

end submission.Austin6820

set_option autoImplicit false
namespace submission.Austin6820
open T

def primary (key body : T) : Option (Small (p key body)) :=
  match body with
  | p left right =>
    match hi : inv key left with
    | none => none
    | some x =>
      if (inv key right).isSome then
        some ⟨x, by have hs := inverseWith_bound hi; simp only [sz]; omega⟩ else none
  | k child =>
    match hi : inv key child with
    | none => none
    | some x => some ⟨x, by have hs := inverseWith_bound hi; simp only [sz]; omega⟩
  | e => none
def fixed (key body : T) : Option (Small (p key body)) :=
  match key with
  | p target other =>
    if p target other ≠ body ∧ q target body = target ∧ (inv body other).isSome then
      some ⟨body, by simp only [sz]; omega⟩ else none
  | k target =>
    if k target ≠ body ∧ q target body = target ∧ (inv body target).isSome then
      some ⟨body, by simp only [sz]; omega⟩ else none
  | e => none
def extra (key body : T) : Option (Small (p key body)) :=
  match key with
  | p x other =>
    if sz body < sz (p x other) then
      match decode (p x other) with
      | none => none
      | some u =>
        if u.val ≠ x ∧ q body u.val = x ∧ (inv u.val other).isSome then
          some ⟨x, by simp only [sz]; omega⟩ else none
    else none
  | _ => none
theorem decode_pair (key body : T) :
    decode (p key body) = merge3 (primary key body) (fixed key body) (extra key body) := by
  rw [decode.eq_def]
  cases key <;> cases body <;> rfl

def Primary (key body out : T) : Prop :=
  (∃ right, body = p (q out key) right ∧ Range key right) ∨ body = k (q out key)
def Fixed (key body out : T) : Prop := out = body ∧ key ≠ body ∧
  ((∃ target other, key = p target other ∧ q target body = target ∧ Range body other) ∨
   (∃ target, key = k target ∧ q target body = target ∧ Range body target))
def Extra (key body out : T) : Prop := ∃ other u,
  key = p out other ∧ sz body < sz key ∧ Code key u ∧ u ≠ out ∧ q body u = out ∧ Range u other

theorem primary_sound {key body : T} {o : Small (p key body)} (h : primary key body = some o) :
    Primary key body o.val := by
  cases body with
  | e => simp [primary] at h
  | k child =>
    simp only [primary] at h
    split at h
    · cases h
    · rename_i x hi
      have ho := congrArg Subtype.val (Option.some.inj h)
      rw [← ho]; exact Or.inr (congrArg k (inv_sound hi).symm)
  | p left right =>
    simp only [primary] at h
    split at h
    · cases h
    · rename_i x hi
      split at h
      · rename_i hr
        have ho := congrArg Subtype.val (Option.some.inj h)
        rw [← ho]
        exact Or.inl ⟨right, by rw [inv_sound hi], (range_iff _ _).mpr hr⟩
      · cases h

theorem primary_complete {key body out : T} (h : Primary key body out) :
    ∃ hs : sz out < sz (p key body), primary key body = some ⟨out, hs⟩ := by
  rcases h with ⟨right, rfl, hr⟩ | rfl
  · have hs := evalWith_left_bound out key (decode key)
    change sz out ≤ max (sz key) (sz (q out key)) at hs
    refine ⟨by simp only [sz]; omega, ?_⟩
    simp only [primary]
    split
    · rename_i hi; rw [inv_complete] at hi; cases hi
    · rename_i x hi
      have he := (Option.some.inj ((inv_complete out key).symm.trans hi))
      subst x
      rw [if_pos ((range_iff _ _).mp hr)]
  · have hs := evalWith_left_bound out key (decode key)
    change sz out ≤ max (sz key) (sz (q out key)) at hs
    refine ⟨by simp only [sz]; omega, ?_⟩
    simp only [primary]
    split
    · rename_i hi; rw [inv_complete] at hi; cases hi
    · rename_i x hi
      have he := (Option.some.inj ((inv_complete out key).symm.trans hi))
      subst x
      rfl

theorem fixed_sound {key body : T} {o : Small (p key body)} (h : fixed key body = some o) :
    Fixed key body o.val := by
  cases key with
  | e => simp [fixed] at h
  | p target other =>
    simp only [fixed] at h
    split at h
    · rename_i hc
      have ho := congrArg Subtype.val (Option.some.inj h)
      exact ⟨ho.symm, hc.1, Or.inl ⟨target, other, rfl, hc.2.1, (range_iff _ _).mpr hc.2.2⟩⟩
    · cases h
  | k target =>
    simp only [fixed] at h
    split at h
    · rename_i hc
      have ho := congrArg Subtype.val (Option.some.inj h)
      exact ⟨ho.symm, hc.1, Or.inr ⟨target, rfl, hc.2.1, (range_iff _ _).mpr hc.2.2⟩⟩
    · cases h
theorem fixed_complete {key body out : T} (h : Fixed key body out) :
    ∃ hs : sz out < sz (p key body), fixed key body = some ⟨out, hs⟩ := by
  obtain ⟨rfl, hn, ⟨target,other,rfl,hq,hr⟩ | ⟨target,rfl,hq,hr⟩⟩ := h
  all_goals refine ⟨by simp only [sz]; omega, ?_⟩
  all_goals simp only [fixed]; rw [if_pos ⟨hn,hq,(range_iff _ _).mp hr⟩]

theorem extra_sound {key body : T} {o : Small (p key body)} (h : extra key body = some o) :
    Extra key body o.val := by
  cases key with
  | e => simp [extra] at h
  | k t => simp [extra] at h
  | p x other =>
    simp only [extra] at h
    split at h
    · rename_i hs
      split at h
      · cases h
      · rename_i u hd
        split at h
        · rename_i hc
          have ho := congrArg Subtype.val (Option.some.inj h)
          rw [← ho]
          exact ⟨other,u.val,rfl,hs,⟨u.property,hd⟩,hc.1,hc.2.1,(range_iff _ _).mpr hc.2.2⟩
        · cases h
    · cases h
theorem extra_complete {key body out : T} (h : Extra key body out) :
    ∃ hs : sz out < sz (p key body), extra key body = some ⟨out, hs⟩ := by
  obtain ⟨other,u,rfl,hs,⟨hu,hd⟩,hne,hq,hr⟩ := h
  refine ⟨by simp only [sz]; omega, ?_⟩
  simp only [extra,hs,hd,↓reduceIte]
  rw [if_pos ⟨hne,hq,(range_iff _ _).mp hr⟩]

theorem combine_cases {b : T} {a c : Option (Small b)} {o : Small b}
    (h : combine a c = some o) : a = some o ∨ c = some o := by
  cases a with
  | none => exact Or.inr h
  | some a =>
    simp only [combine] at h
    split at h
    · exact Or.inl h
    · cases h
theorem merge3_cases {b : T} {a c d : Option (Small b)} {o : Small b}
    (h : merge3 a c d = some o) : a = some o ∨ c = some o ∨ d = some o := by
  cases a with
  | none => exact Or.inr (combine_cases h)
  | some a =>
    simp only [merge3] at h
    split at h
    · exact Or.inl h
    · cases h
theorem code_cases {key body out : T} (h : Code (p key body) out) :
    Primary key body out ∨ Fixed key body out ∨ Extra key body out := by
  obtain ⟨hs,hd⟩ := h
  rw [decode_pair] at hd
  rcases merge3_cases hd with hp | hf | he
  · exact Or.inl (primary_sound hp)
  · exact Or.inr (Or.inl (fixed_sound hf))
  · exact Or.inr (Or.inr (extra_sound he))

end submission.Austin6820

set_option autoImplicit false
namespace submission.Austin6820
open T

def Node (child tree : T) : Prop := (∃ right, tree = p child right) ∨ tree = k child
theorem node_growth {child tree : T} (h : Node child tree) : sz child < sz tree := by
  rcases h with ⟨right,rfl⟩ | rfl <;> simp only [sz] <;> omega
theorem node_unique {a b tree : T} (ha : Node a tree) (hb : Node b tree) : a = b := by
  rcases ha with ⟨r,rfl⟩ | rfl <;> rcases hb with ⟨s,he⟩ | he
  · exact (T.p.inj he).1
  · cases he
  · cases he
  · exact T.k.inj he
theorem primary_node {key body out : T} (h : Primary key body out) : Node (q out key) body := by
  rcases h with ⟨r,he,_⟩ | he
  · exact Or.inl ⟨r,he⟩
  · exact Or.inr he
theorem code_unique {b a c : T} (ha : Code b a) (hc : Code b c) : a = c := by
  obtain ⟨_,ha⟩ := ha; obtain ⟨_,hc⟩ := hc
  exact congrArg Subtype.val (Option.some.inj (ha.symm.trans hc))
theorem code_pair_q {key body out : T} (hc : Code (p key body) out) : q key (p key body) = out :=
  q_hit ⟨body,rfl,hc⟩
theorem step_cases {a b out : T} (h : q a b = out) : Plain a b out ∨ Hit a b out := by
  rw [← h]; exact q_cases a b
theorem step_hit_small {a b out : T} (h : q a b = out) (hs : sz out < sz b) : Hit a b out := by
  rw [← h]; apply hit_of_drop; rw [h]; exact hs
theorem range_small_code {b out : T} (hr : Range b out) (hs : sz out < sz b) : Code b out := by
  obtain ⟨a,ha⟩ := hr
  exact (step_hit_small ha hs).choose_spec.2
theorem range_small_eq {b out other : T} (hc : Code b out) (hr : Range b other)
    (hs : sz other < sz b) : other = out := code_unique (range_small_code hr hs) hc
theorem plain_of_no_hit {a b out : T} (h : q a b = out) (hn : ¬Hit a b out) : Plain a b out :=
  (step_cases h).resolve_right hn
theorem q_other_key {key body a : T} (ha : a ≠ key) (hb : a ≠ p key body) :
    q a (p key body) = p a (p key body) := by
  rcases q_cases a (p key body) with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · exact hp
    · exact False.elim (hb he)
  · obtain ⟨right,he,_⟩ := hh
    exact False.elim (ha (T.p.inj he).1.symm)
theorem no_fixed_diagonal (a : T) : ¬Code (p a a) a := by
  intro hc
  rcases code_cases hc with hp | hf | he
  · have hs := node_growth (primary_node hp)
    rw [q_square] at hs; simp only [sz] at hs; omega
  · exact hf.2.1 rfl
  · obtain ⟨_,_,_,hs,_⟩ := he; omega
theorem no_code_diagonal (a out : T) : ¬Code (p a a) out := by
  intro hc
  have hp : Primary a a out := by
    rcases code_cases hc with hp | hf | he
    · exact hp
    · exact False.elim (hf.2.1 rfl)
    · obtain ⟨_,_,_,hs,_⟩ := he; omega
  unfold Primary at hp
  generalize hu : q out a = u at hp
  rcases hp with ⟨right,ha,hr⟩ | ha
  · have hl : sz u < sz a := by rw [ha]; simp only [sz]; omega
    have hr' : sz right < sz a := by rw [ha]; simp only [sz]; omega
    have cc := range_small_code ⟨out,hu⟩ hl
    have he := range_small_eq cc hr hr'
    rw [he] at ha
    rw [ha] at cc
    exact no_fixed_diagonal _ cc
  · have hl : sz u < sz a := by rw [ha]; simp only [sz]; omega
    have cc := range_small_code ⟨out,hu⟩ hl
    rw [ha] at cc
    obtain ⟨_,hd⟩ := cc
    rw [decode_k] at hd
    cases hd

theorem fixed_point_small {a b : T} (h : q a b = a) : sz a < sz b := by
  rcases step_cases h with hp | hh
  · have hs := (plain_growth hp).1; omega
  · exact (hit_small hh).1
theorem fixed_point_code {a b : T} (h : q a b = a) : Code b a :=
  (step_hit_small h (fixed_point_small h)).choose_spec.2
theorem fixed_point_node_forbidden {a b c : T} (hf : q a b = a) (hn : Node a c)
    (hr : Range b c) : False := by
  obtain ⟨x,hx⟩ := hr
  have hac := node_growth hn
  have hb := fixed_point_small hf
  have hc := fixed_point_code hf
  have hp : Plain x b c := plain_of_no_hit hx (by
    intro hh; have he := code_unique hh.choose_spec.2 hc; rw [he] at hac; omega)
  rcases hp with hp | ⟨he,hp⟩
  · have hn' : Node x c := Or.inl ⟨b,hp⟩
    have hax := node_unique hn hn'
    rw [← hax,hf] at hx
    rw [hx] at hac; omega
  · have hn' : Node b c := Or.inr hp
    have hab := node_unique hn hn'
    rw [hab] at hb; omega

theorem range_successor {r y x : T} (hr : Range r y) (hx : q y r = x) (hne : x ≠ y) :
    x = p y r := by
  have hyr : y ≠ r := by intro he; rw [he] at hr; exact no_range_self r hr
  rcases step_cases hx with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · exact hp
    · exact False.elim (hyr he)
  · have hxr := (hit_small hh).2
    have hyr' := (hit_small hh).1
    have hc := range_small_code hr hyr'
    exact False.elim (hne (code_unique hh.choose_spec.2 hc))

end submission.Austin6820

set_option autoImplicit false
namespace submission.Austin6820
open T

theorem primary_unique {key body a b : T} (ha : Primary key body a) (hb : Primary key body b) : a = b :=
  q_right_injective a b key (node_unique (primary_node ha) (primary_node hb))
theorem primary_fixed_disjoint {key body a f : T} (hp : Primary key body a) (hf : Fixed key body f) : False := by
  obtain ⟨_,_,⟨target,other,hkey,hfix,hr⟩ | ⟨target,hkey,hfix,hr⟩⟩ := hf
  · obtain ⟨r,hbody,hcb⟩ := step_hit_small hfix (fixed_point_small hfix)
    have hqa := node_unique (primary_node hp) (Or.inl ⟨r,hbody⟩)
    have hrt : Range key r := by
      rcases hp with ⟨right,hp,hright⟩ | hp
      · have he := (T.p.inj (hp.symm.trans hbody)).2
        rw [← he]; exact hright
      · rw [hp] at hbody; cases hbody
    have htk : sz target < sz key := by rw [hkey]; simp only [sz]; omega
    have hck := range_small_code ⟨a,hqa⟩ htk
    by_cases hs : sz r < sz key
    · have he := range_small_eq hck hrt hs
      rw [he] at hbody
      rw [hbody] at hcb
      exact no_fixed_diagonal target hcb
    · have hot : sz other < sz body := by
        have hok : sz other < sz key := by rw [hkey]; simp only [sz]; omega
        have hrb : sz r < sz body := by rw [hbody]; simp only [sz]; omega
        omega
      have he := range_small_eq hcb hr hot
      rw [he] at hkey
      rw [hkey] at hck
      exact no_fixed_diagonal target hck
  · have hn : Node target key := Or.inr hkey
    obtain ⟨r,hbody,_⟩ := step_hit_small hfix (fixed_point_small hfix)
    have hqa := node_unique (primary_node hp) (Or.inl ⟨r,hbody⟩)
    have hrr : Range (k target) target := by rw [← hkey]; exact ⟨a,hqa⟩
    have hs := range_k_lower hrr; omega

theorem primary_extra_equal {key body a x : T} (hp : Primary key body a) (he : Extra key body x) : a = x := by
  obtain ⟨other,u,hkey,hs,hc,_,_,_⟩ := he
  have hqa := range_small_eq hc (show Range key (q a key) from ⟨a,rfl⟩)
    (by have hn := node_growth (primary_node hp); omega)
  have hqx : q x key = u := by rw [hkey] at hc ⊢; exact code_pair_q hc
  exact q_right_injective a x key (hqa.trans hqx.symm)

theorem plain_right_unique {a b c d out : T} (ha : Plain a b out) (hc : Plain c d out) : b = d := by
  rcases ha with rfl | ⟨rfl,rfl⟩ <;> rcases hc with he | ⟨_,he⟩
  · exact (T.p.inj he).2
  · cases he
  · cases he
  · exact T.k.inj he
theorem plain_of_output_large {a b out : T} (h : q a b = out) (hs : sz b ≤ sz out) : Plain a b out :=
  plain_of_no_hit h (by intro hh; have ho := (hit_small hh).2; omega)

theorem fixed_extra_disjoint {key body f x : T} (hf : Fixed key body f) (he : Extra key body x) : False := by
  obtain ⟨other,u,hkey,hs,hcu,hne,hq,hr⟩ := he
  have hfix : q x body = x ∧ Range body other := by
    obtain ⟨_,_,⟨target,other',hk,hfix,hr'⟩ | ⟨target,hk,_,_⟩⟩ := hf
    · have hh := T.p.inj (hk.symm.trans hkey)
      rw [hh.1] at hfix
      rw [hh.2] at hr'
      exact ⟨hfix,hr'⟩
    · rw [hk] at hkey; cases hkey
  have hxb := fixed_point_small hfix.1
  have hcb := fixed_point_code hfix.1
  have hhit : Hit body u x := by
    rcases step_cases hq with hp | hh
    · have hx := (plain_growth hp).1; omega
    · exact hh
  obtain ⟨r,hu,hc⟩ := hhit
  have hbu : sz body < sz u := by rw [hu]; simp only [sz]; omega
  have heq : other = x := by
    by_cases ho : sz other < sz u
    · exact range_small_eq hc hr ho
    · obtain ⟨a,ha⟩ := hr
      obtain ⟨b,hb⟩ := hfix.2
      have hp := plain_of_output_large ha (by omega)
      have hp' := plain_of_output_large hb (by omega)
      have he := plain_right_unique hp hp'
      rw [he] at hbu; omega
  rw [heq] at hkey
  rw [hkey] at hcu
  exact no_code_diagonal x u hcu

theorem extra_unique {key body a b : T} (ha : Extra key body a) (hb : Extra key body b) : a = b := by
  obtain ⟨other,_,he,_⟩ := ha
  obtain ⟨other',_,he',_⟩ := hb
  exact (T.p.inj (he.symm.trans he')).1
def Candidate (key body out : T) : Prop := Primary key body out ∨ Fixed key body out ∨ Extra key body out
theorem candidate_unique {key body a b : T} (ha : Candidate key body a) (hb : Candidate key body b) : a = b := by
  rcases ha with hp | hf | he <;> rcases hb with hp' | hf' | he'
  · exact primary_unique hp hp'
  · exact False.elim (primary_fixed_disjoint hp hf')
  · exact primary_extra_equal hp he'
  · exact False.elim (primary_fixed_disjoint hp' hf)
  · exact hf.1.trans hf'.1.symm
  · exact False.elim (fixed_extra_disjoint hf he')
  · exact (primary_extra_equal hp' he).symm
  · exact False.elim (fixed_extra_disjoint hf' he)
  · exact extra_unique he he'

theorem merge3_complete {b : T} {a c d : Option (Small b)} {o : Small b}
    (hp : a = some o ∨ c = some o ∨ d = some o)
    (hc : ∀ v, a = some v ∨ c = some v ∨ d = some v → v.val = o.val) : merge3 a c d = some o := by
  have ha : a = none ∨ a = some o := by
    cases ha : a with
    | none => exact Or.inl rfl
    | some v => have he := Subtype.ext (hc v (Or.inl ha)); rw [he]; exact Or.inr rfl
  have hb : c = none ∨ c = some o := by
    cases hb : c with
    | none => exact Or.inl rfl
    | some v => have he := Subtype.ext (hc v (Or.inr (Or.inl hb))); rw [he]; exact Or.inr rfl
  have hd : d = none ∨ d = some o := by
    cases hd : d with
    | none => exact Or.inl rfl
    | some v => have he := Subtype.ext (hc v (Or.inr (Or.inr hd))); rw [he]; exact Or.inr rfl
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hd with rfl | rfl
  all_goals simp_all [merge3,combine,agrees]

theorem code_of_candidate {key body out : T} (h : Candidate key body out) : Code (p key body) out := by
  have present : ∃ hs : sz out < sz (p key body),
      primary key body = some ⟨out,hs⟩ ∨ fixed key body = some ⟨out,hs⟩ ∨ extra key body = some ⟨out,hs⟩ := by
    rcases h with hp | hf | he
    · obtain ⟨hs,hp⟩ := primary_complete hp; exact ⟨hs,Or.inl hp⟩
    · obtain ⟨hs,hf⟩ := fixed_complete hf; exact ⟨hs,Or.inr (Or.inl hf)⟩
    · obtain ⟨hs,he⟩ := extra_complete he; exact ⟨hs,Or.inr (Or.inr he)⟩
  obtain ⟨hs,hp⟩ := present
  refine ⟨hs,?_⟩
  rw [decode_pair]
  apply merge3_complete hp
  intro v hv
  apply candidate_unique (b := out) ?_ h
  rcases hv with hp | hf | he
  · exact Or.inl (primary_sound hp)
  · exact Or.inr (Or.inl (fixed_sound hf))
  · exact Or.inr (Or.inr (extra_sound he))

end submission.Austin6820

set_option autoImplicit false
namespace submission.Austin6820
open T

theorem primary_reentry_range {key body out : T} (hp : Primary key body out)
    (hr : Range out body) (hs : sz key < sz out) : Range key out := by
  have hq := q_of_larger_left hs
  change q out key = p out key at hq
  rcases hp with ⟨right,hbody,hrr⟩ | hbody
  · rw [hq] at hbody
    obtain ⟨a,ha⟩ := hr
    have hsz : sz out < sz body := by rw [hbody]; simp only [sz]; omega
    have hp := plain_of_output_large ha (Nat.le_of_lt hsz)
    rcases hp with hp | ⟨_,hp⟩
    · have he := (T.p.inj (hbody.symm.trans hp)).2
      rw [he] at hrr; exact hrr
    · rw [hp] at hbody; cases hbody
  · rw [hq] at hbody
    obtain ⟨a,ha⟩ := hr
    have hsz : sz out < sz body := by rw [hbody]; simp only [sz]; omega
    have hp := plain_of_output_large ha (Nat.le_of_lt hsz)
    rcases hp with hp | ⟨_,hp⟩
    · rw [hp] at hbody; cases hbody
    · have he := T.k.inj (hbody.symm.trans hp)
      have hh := congrArg sz he; simp only [sz] at hh; omega
theorem code_reentry_range {key body out : T} (hc : Code (p key body) out)
    (hr : Range out body) (hs : sz key < sz out) : Range key out := by
  rcases code_cases hc with hp | hf | he
  · exact primary_reentry_range hp hr hs
  · rw [← hf.1] at hr; exact False.elim (no_range_self out hr)
  · obtain ⟨other,_,hk,_⟩ := he
    have hh := congrArg sz hk; simp only [sz] at hh; omega

def Tag (a b : T) : Prop := b = p a a ∨ b = k a
theorem tag_node {a b : T} (h : Tag a b) : Node a b := by
  rcases h with h | h
  · exact Or.inl ⟨a,h⟩
  · exact Or.inr h
theorem tag_no_code {a b out : T} (h : Tag a b) : ¬Code b out := by
  rcases h with rfl | rfl
  · exact no_code_diagonal a out
  · rintro ⟨_,hd⟩; rw [decode_k] at hd; cases hd
theorem tag_q (a b : T) (h : Tag a b) : q a b = p a b := by
  have hs := node_growth (tag_node h)
  rcases q_cases a b with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · exact hp
    · rw [he] at hs; omega
  · exact False.elim (tag_no_code h hh.choose_spec.2)
theorem tag_outer_no_return {a b : T} (h : Tag a b) : ¬Code (p b a) a := by
  intro hc
  rcases code_cases hc with hp | hf | he
  · have hs := node_growth (primary_node hp)
    rw [tag_q a b h] at hs; simp only [sz] at hs; omega
  · obtain ⟨_,_,⟨target,other,hb,hq,_⟩ | ⟨target,hb,hq,_⟩⟩ := hf
    · have ht := node_unique (tag_node h) (Or.inl ⟨other,hb⟩)
      rw [← ht,q_square] at hq
      have hs := congrArg sz hq; simp only [sz] at hs; omega
    · have ht := node_unique (tag_node h) (Or.inr hb)
      rw [← ht,q_square] at hq
      have hs := congrArg sz hq; simp only [sz] at hs; omega
  · obtain ⟨_,u,_,_,hcu,_⟩ := he
    exact tag_no_code h hcu

theorem extra_with_tag_impossible {key body out : T} (he : Extra key body out)
    (ht : Tag out body) : False := by
  obtain ⟨other,u,hkey,_,hcu,_,hq,hr⟩ := he
  have htb := node_growth (tag_node ht)
  have hhit : Hit body u out := by
    rcases step_cases hq with hp | hh
    · have hs := (plain_growth hp).1; omega
    · exact hh
  obtain ⟨r,hu,hc⟩ := hhit
  have hbu : sz body < sz u := by rw [hu]; simp only [sz]; omega
  rw [hkey] at hcu
  have hru := code_reentry_range hcu hr (by omega)
  obtain ⟨a,ha⟩ := hru
  have hp := plain_of_output_large ha (by omega)
  have hu' : u = p body out := by
    rcases hp with hp | ⟨_,hp⟩
    · have hh := T.p.inj (hu.symm.trans hp)
      rw [hh.2] at hu; exact hu
    · rw [hp] at hu; cases hu
  rw [hu'] at hc
  exact tag_outer_no_return ht hc

theorem returned_node_is_tag {key body out other : T} (hc : Code (p key body) out)
    (hb : body = p out other) (hr : Range (p key body) other) : Tag out body := by
  have hs : sz other < sz (p key body) := by rw [hb]; simp only [sz]; omega
  have he := range_small_eq hc hr hs
  exact Or.inl (by rw [hb,he])

theorem primary_from_tag_code {key body out : T} (hc : Code (p key body) out)
    (ht : Tag out body) : Primary key body out := by
  rcases code_cases hc with hp | hf | he
  · exact hp
  · have hs := node_growth (tag_node ht); rw [hf.1] at hs; omega
  · exact False.elim (extra_with_tag_impossible he ht)

end submission.Austin6820

set_option autoImplicit false
namespace submission.Austin6820
open T

theorem inner_hit_raw_right {x y z u v w : T} (hu : q x y = u) (hv : q z y = v)
    (hh : Hit u v w) : v = p u y := by
  have ⟨huv,_⟩ := hit_small hh
  obtain ⟨body,hshape,_⟩ := hh
  rcases step_cases hv with hp | hh
  · rcases hp with hp | ⟨_,hp⟩
    · have he := T.p.inj (hp.symm.trans hshape)
      rw [← he.1]; exact hp
    · rw [hp] at hshape; cases hshape
  · have hvy := (hit_small hh).2
    have hhu := step_hit_small hu (by omega)
    have he := code_unique hhu.choose_spec.2 hh.choose_spec.2
    rw [he] at huv; omega

theorem inner_hit_key_ne_input {x y z u v w : T} (hu : q x y = u) (hv : q z y = v)
    (hh : Hit u v w) : u ≠ x := by
  have hvraw := inner_hit_raw_right hu hv hh
  have hvy : sz y < sz v := by rw [hvraw]; simp only [sz]; omega
  have hz : z = u := by
    rcases plain_of_output_large hv (Nat.le_of_lt hvy) with hp | ⟨_,hp⟩
    · exact (T.p.inj (hp.symm.trans hvraw)).1
    · rw [hp] at hvraw; cases hvraw
  intro he
  have hv' : q x y = v := by rw [hz,he] at hv; exact hv
  have heq := hu.symm.trans hv'
  have hs := (hit_small hh).1
  rw [heq] at hs; omega

theorem extra_on_image_impossible {x y u w : T} (hu : q x y = u) (he : Extra u y w) : False := by
  obtain ⟨other,r,hshape,hs,hc,_,hq,hr⟩ := he
  have uraw : u = p x y := by
    rcases plain_of_output_large hu (Nat.le_of_lt hs) with hp | ⟨_,hp⟩
    · exact hp
    · rw [hp] at hshape; cases hshape
  have hh := T.p.inj (hshape.symm.trans uraw)
  rw [hh.1] at hq
  rw [hh.2] at hr
  have hxy : x ≠ y := by
    intro hxy
    rw [hxy,q_square] at hu
    rw [hxy] at uraw
    have bad := hu.trans uraw; cases bad
  have hx := range_successor hr hq hxy
  have hry : r ≠ y := by intro he; rw [he] at hr; exact no_range_self y hr
  have hrx : r ≠ x := by intro he; have h := congrArg sz (he.trans hx); simp only [sz] at h; omega
  have hqr : q r x = p r x := by rw [hx]; exact q_other_key hry (by rw [← hx]; exact hrx)
  rw [uraw] at hc
  rcases code_cases hc with hp | hf | he
  · have hn := node_growth (primary_node hp)
    rw [hqr] at hn
    have hxy' : sz y < sz x := by rw [hx]; simp only [sz]; omega
    simp only [sz] at hn; omega
  · rw [hf.1] at hr; exact no_range_self y hr
  · obtain ⟨other',_,hx',_⟩ := he
    have he := (T.p.inj (hx.symm.trans hx')).1
    rw [← he] at hr; exact no_range_self y hr

theorem inner_hit_primary {x y z u v w : T} (hu : q x y = u) (hv : q z y = v)
    (hh : Hit u v w) : Primary u y w := by
  have hvraw := inner_hit_raw_right hu hv hh
  obtain ⟨_,_,hc⟩ := hh
  rw [hvraw] at hc
  rcases code_cases hc with hp | hf | he
  · exact hp
  · obtain ⟨_,_,⟨target,other,hshape,hq,_⟩ | ⟨target,hshape,hq,_⟩⟩ := hf
    · exact False.elim (fixed_point_node_forbidden hq (Or.inl ⟨other,hshape⟩) ⟨x,hu⟩)
    · exact False.elim (fixed_point_node_forbidden hq (Or.inr hshape) ⟨x,hu⟩)
  · exact False.elim (extra_on_image_impossible hu he)

theorem raw_first_fixed_completion {x y u w target : T}
    (hu : u = p x y) (hh : Hit w u target) (hp : Primary u y w)
    (hq : q w u = target) : Fixed y w x := by
  obtain ⟨body,hshape,hc⟩ := hh
  rw [hu] at hshape hc
  have hw : w = x := (T.p.inj hshape).1.symm
  have ht : Tag target y := by
    rcases hp with ⟨other,hy,hr⟩ | hy
    · rw [hq] at hy
      rw [hu] at hr
      exact returned_node_is_tag hc hy hr
    · exact Or.inr (by rw [hq] at hy; exact hy)
  have hprim := primary_from_tag_code hc ht
  have hfixed : q target x = target := node_unique (primary_node hprim) (tag_node ht)
  have hyx : y ≠ x := by
    intro he
    have hnode := node_growth (tag_node ht)
    have hfx := fixed_point_code hfixed
    rw [← he] at hfx
    exact tag_no_code ht hfx
  refine ⟨hw.symm, ?_, ?_⟩
  · rw [hw]; exact hyx
  · rw [hw]
    rcases ht with hy | hy
    · exact Or.inl ⟨target,target,hy,hfixed,⟨target,hfixed⟩⟩
    · exact Or.inr ⟨target,hy,hfixed,⟨target,hfixed⟩⟩

theorem inner_hit_completion {x y z u v w : T} (hu : q x y = u) (hv : q z y = v)
    (hh : Hit u v w) : Fixed y w x ∨ Extra y w x := by
  have hp := inner_hit_primary hu hv hh
  have hvraw := inner_hit_raw_right hu hv hh
  have hux := inner_hit_key_ne_input hu hv hh
  unfold Primary at hp
  generalize ht : q w u = target at hp
  have hnode : Node target y := by
    rcases hp with ⟨other,hy,_⟩ | hy
    · exact Or.inl ⟨other,hy⟩
    · exact Or.inr hy
  have hty := node_growth hnode
  rcases step_cases ht with hplain | hhit
  · have ⟨hwt,hut⟩ := plain_growth hplain
    have hhu := step_hit_small hu (by omega)
    obtain ⟨other,hy,hc⟩ := hhu
    have hxt := node_unique (Or.inl ⟨other,hy⟩) hnode
    refine Or.inr ⟨other,u,hy,by omega,hc,hux,?_,?_⟩
    · exact ht.trans hxt.symm
    · rcases hp with ⟨other',hy',hr⟩ | hy'
      · have he := (T.p.inj (hy'.symm.trans hy)).2
        rw [← he]; exact hr
      · rw [hy'] at hy; cases hy
  · have hp' : Primary u y w := by simpa only [Primary,ht] using hp
    rcases step_cases hu with hup | huh
    · rcases hup with hur | ⟨_,hus⟩
      · exact Or.inl (raw_first_fixed_completion hur hhit hp' ht)
      · obtain ⟨b,he,_⟩ := hhit; rw [hus] at he; cases he
    · have huy := (hit_small huh).2
      obtain ⟨other,hy,hcy⟩ := huh
      have hxt := node_unique (Or.inl ⟨other,hy⟩) hnode
      have hwt : sz w < sz u := (hit_small hhit).1
      refine Or.inr ⟨other,u,hy,by omega,hcy,hux,ht.trans hxt.symm,?_⟩
      rcases hp with ⟨other',hy',hr⟩ | hy'
      · have he := (T.p.inj (hy'.symm.trans hy)).2
        rw [← he]; exact hr
      · rw [hy'] at hy; cases hy

theorem inner_hit_candidate {x y z u v w : T} (hu : q x y = u) (hv : q z y = v)
    (hh : Hit u v w) : Candidate y w x := Or.inr (inner_hit_completion hu hv hh)
end submission.Austin6820

set_option autoImplicit false
namespace submission.Austin6820
open T

theorem fixed_preceding_raw {y w x : T} (hf : Fixed y w x) : q y w = p y w := by
  have hyw := hf.2.1
  have hn : ∃ target, Node target y ∧ q target w = target := by
    obtain ⟨_,_,⟨target,other,hy,hq,_⟩ | ⟨target,hy,hq,_⟩⟩ := hf
    · exact ⟨target,Or.inl ⟨other,hy⟩,hq⟩
    · exact ⟨target,Or.inr hy,hq⟩
  obtain ⟨target,hnode,hfixed⟩ := hn
  have hty := node_growth hnode
  obtain ⟨r,hw,_⟩ := step_hit_small hfixed (fixed_point_small hfixed)
  rcases q_cases y w with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · exact hp
    · exact False.elim (hyw he)
  · obtain ⟨s,hw',_⟩ := hh
    have he := (T.p.inj (hw.symm.trans hw')).1
    rw [he] at hty; omega

theorem plain_inner_preceding_raw {x y z u v w : T} (hu : q x y = u) (hv : q z y = v)
    (hw : q u v = w) (hp : Plain u v w) : q y w = p y w := by
  have ⟨huw,hvw⟩ := plain_growth hp
  have hwy : w ≠ y := by
    intro he
    have cu := range_small_code ⟨x,hu⟩ (by rw [← he]; exact huw)
    have cv := range_small_code ⟨z,hv⟩ (by rw [← he]; exact hvw)
    have huv := code_unique cu cv
    rw [← huv,q_square] at hw
    have hy : y = k u := he.symm.trans hw.symm
    rw [hy] at cu
    obtain ⟨_,hd⟩ := cu; rw [decode_k] at hd; cases hd
  rcases q_cases y w with ho | hh
  · rcases ho with ho | ⟨he,_⟩
    · exact ho
    · exact False.elim (hwy he.symm)
  · obtain ⟨body,hs,_⟩ := hh
    rcases hp with hp | ⟨_,hp⟩
    · have hey := (T.p.inj (hp.symm.trans hs)).1
      have bad : q x y = y := hu.trans hey
      exact False.elim (q_ne_right x y bad)
    · rw [hp] at hs; cases hs

theorem extra_preceding_raw {y w x : T} (he : Extra y w x) : q y w = p y w := by
  obtain ⟨_,_,_,hs,_⟩ := he
  exact q_of_larger_left hs

theorem equation6820 (x y z : T) : x = q y (q y (q (q x y) (q z y))) := by
  let u := q x y
  let v := q z y
  let w := q u v
  have hu : q x y = u := rfl
  have hv : q z y = v := rfl
  have hw : q u v = w := rfl
  have hc : Candidate y w x ∧ q y w = p y w := by
    rcases step_cases hw with hp | hh
    · refine ⟨Or.inl ?_,plain_inner_preceding_raw hu hv hw hp⟩
      rcases hp with hp | ⟨he,hp⟩
      · exact Or.inl ⟨v,by rw [hu]; exact hp,⟨z,hv⟩⟩
      · exact Or.inr (by rw [hu,he]; exact hp)
    · have hc := inner_hit_completion hu hv hh
      refine ⟨Or.inr hc,?_⟩
      rcases hc with hf | he
      · exact fixed_preceding_raw hf
      · exact extra_preceding_raw he
  change x = q y (q y w)
  rw [hc.2]
  exact (code_pair_q (code_of_candidate hc.1)).symm

end submission.Austin6820

set_option autoImplicit false
namespace submission.Austin6820
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
theorem equation39485 (x y z : Carrier) :
    x = opposite (opposite (opposite (opposite y z) (opposite y x)) y) y :=
  equation6820 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op y (op y (op (op x y) (op z y)))) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier, mul, embed, equation6820, embed_injective⟩
end submission.Austin6820

namespace submission
abbrev CM := Austin6820.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin6820.embed n = Austin6820.embed j) : n = j :=
  Austin6820.embed_injective n j h
end CM
instance modelMagma : Magma CM := ⟨Austin6820.mul⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin6820.equation6820 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin6820.embed_injective 0 1
      (h (submission.Austin6820.embed 0) (submission.Austin6820.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

