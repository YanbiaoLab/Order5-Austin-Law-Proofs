import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin9337
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

def rootSize : T → Nat
  | e => 0
  | k a => sz a
  | p a b => max (sz a) (sz b)

theorem rootSize_le (a : T) : rootSize a ≤ sz a := by
  cases a <;> simp only [rootSize,sz] <;> omega

structure Answer (b : T) where
  key : T
  value : T
  key_ne : key ≠ b
  key_bound : rootSize key ≤ sz b
  value_bound : rootSize value < sz b

theorem Answer.ext {b : T} {a c : Answer b} (hk : a.key = c.key) (hv : a.value = c.value) : a = c := by
  cases a; cases c; simp_all

def evalWith (a b : T) (d : Option (Answer b)) : T :=
  if a = b then k b else
    match d with
    | none => p a b
    | some r => if a = r.key then r.value else p a b

def fromCodeWith (b out : T) (d : Option (Answer b)) : Option T :=
  match d with
  | none => none
  | some r => if r.value = out then some r.key else none

def inverseWith (b out : T) (d : Option (Answer b)) : Option T :=
  if out = k b then some b else
    match out with
    | p a second => if second = b ∧ evalWith a b d = out then some a else fromCodeWith b out d
    | _ => fromCodeWith b out d
end submission.Austin9337

set_option autoImplicit false
namespace submission.Austin9337
open T

@[simp] theorem evalWith_square (a : T) (d : Option (Answer a)) : evalWith a a d = k a := by simp [evalWith]
@[simp] theorem evalWith_hit {b : T} (r : Answer b) : evalWith r.key b (some r) = r.value := by
  simp [evalWith,r.key_ne]

theorem fromCodeWith_sound {b out a : T} {d : Option (Answer b)}
    (h : fromCodeWith b out d = some a) : evalWith a b d = out := by
  cases d with
  | none => cases h
  | some r =>
    simp only [fromCodeWith] at h
    split at h
    · rename_i he
      have ha := Option.some.inj h
      rw [←ha,evalWith_hit]; exact he
    · cases h

theorem inverseWith_sound {b out a : T} {d : Option (Answer b)}
    (h : inverseWith b out d = some a) : evalWith a b d = out := by
  unfold inverseWith at h
  split at h
  · rename_i he
    have ha := Option.some.inj h
    rw [←ha,evalWith_square]; exact he.symm
  · cases out with
    | e => exact fromCodeWith_sound h
    | k t => exact fromCodeWith_sound h
    | p left right =>
      change (if right = b ∧ evalWith left b d = p left right then some left
        else fromCodeWith b (p left right) d) = some a at h
      split at h
      · rename_i hc
        have ha := Option.some.inj h
        rw [←ha]; exact hc.2
      · exact fromCodeWith_sound h

theorem inverseWith_root_small (b out : T) (d : Option (Answer b)) (hs : rootSize out < sz b) :
    inverseWith b out d = fromCodeWith b out d := by
  have hn : out ≠ k b := by intro he; rw [he] at hs; simp only [rootSize] at hs; omega
  unfold inverseWith
  rw [if_neg hn]
  cases out with
  | e => rfl
  | k t => rfl
  | p left right =>
    have hr : right ≠ b := by intro he; rw [he] at hs; simp only [rootSize] at hs; omega
    change (if right = b ∧ evalWith left b d = p left right then some left
      else fromCodeWith b (p left right) d) = fromCodeWith b (p left right) d
    simp only [hr,false_and,↓reduceIte]

theorem inverseWith_complete (a b : T) (d : Option (Answer b)) : inverseWith b (evalWith a b d) d = some a := by
  by_cases hab : a = b
  · subst a; rw [evalWith_square]; simp [inverseWith]
  · have finish (he : evalWith a b d = p a b) : inverseWith b (evalWith a b d) d = some a := by
      rw [he]; simp [inverseWith,he]
    cases d with
    | none => apply finish; simp [evalWith,hab]
    | some r =>
      by_cases hk : a = r.key
      · subst a
        rw [evalWith_hit,inverseWith_root_small _ _ _ r.value_bound]
        simp [fromCodeWith]
      · apply finish; simp [evalWith,hab,hk]

theorem evalWith_left_root_bound (a b : T) (d : Option (Answer b)) :
    rootSize a ≤ max (sz b) (rootSize (evalWith a b d)) := by
  by_cases hab : a = b
  · subst a; have hs := rootSize_le b; omega
  · cases d with
    | none => simp only [evalWith,if_neg hab,rootSize]; have hs := rootSize_le a; simp only [rootSize] at hs; omega
    | some r =>
      by_cases hk : a = r.key
      · subst a; have hs := r.key_bound; omega
      · simp only [evalWith,if_neg hab,if_neg hk,rootSize]; have hs := rootSize_le a; simp only [rootSize] at hs; omega

theorem inverseWith_root_bound {b out a : T} {d : Option (Answer b)}
    (h : inverseWith b out d = some a) : rootSize a ≤ max (sz b) (rootSize out) := by
  have hs := evalWith_left_root_bound a b d
  rw [inverseWith_sound h] at hs
  exact hs
end submission.Austin9337

set_option autoImplicit false
namespace submission.Austin9337
open T

def combine {b : T} (a c : Option (Answer b)) : Option (Answer b) :=
  match a,c with
  | none,_ => c
  | _,none => a
  | some x,some y => if x.key = y.key ∧ x.value = y.value then a else none

def decode (b : T) : Option (Answer b) :=
  match b with
  | p u second =>
    have hu : sz u < sz (p u second) := by simp only [sz]; omega
    let primary : Option (Answer (p u second)) :=
      match second with
      | p y v =>
        have hy : sz y < sz (p u (p y v)) := by simp only [sz]; omega
        match hi : inverseWith y u (decode y) with
        | none => none
        | some x =>
          if (inverseWith y v (decode y)).isSome then
            some {
              key := y
              value := x
              key_ne := by
                intro he
                have hs := congrArg sz he
                simp only [sz] at hs
                omega
              key_bound := by
                have hs := rootSize_le y
                simp only [sz]
                omega
              value_bound := by
                have hs := inverseWith_root_bound hi
                have ht := rootSize_le u
                simp only [sz]
                omega }
          else none
      | _ => none
    let extra : Option (Answer (p u second)) :=
      match u with
      | p x v =>
        have hx : sz x < sz (p (p x v) second) := by simp only [sz]; omega
        have hu' : sz (p x v) < sz (p (p x v) second) := by simp only [sz]; omega
        if x = second ∧ (inverseWith x v (decode x)).isSome ∧
            evalWith (p x v) x (decode x) = p (p x v) second ∧
            evalWith (p (p x v) second) (p x v) (decode (p x v)) = p (p (p x v) second) (p x v) then
          some {
            key := p (p (p x v) second) (p x v)
            value := x
            key_ne := by
              intro he
              have hs := congrArg sz he
              simp only [sz] at hs
              omega
            key_bound := by simp only [rootSize,sz]; omega
            value_bound := by
              have hs := rootSize_le x
              simp only [sz]
              omega }
        else none
      | _ => none
    combine primary extra
  | _ => none
termination_by sz b
decreasing_by all_goals assumption

def q (a b : T) : T := evalWith a b (decode b)
def inv (b out : T) : Option T := inverseWith b out (decode b)
theorem inv_sound {b out a : T} (h : inv b out = some a) : q a b = out := inverseWith_sound h
@[simp] theorem inv_complete (a b : T) : inv b (q a b) = some a := inverseWith_complete _ _ _
theorem q_right_injective (a a' b : T) (he : q a b = q a' b) : a = a' := by
  have h := congrArg (inv b) he
  simpa only [inv_complete,Option.some.injEq] using h
@[simp] theorem q_square (a : T) : q a a = k a := evalWith_square _ _
@[simp] theorem decode_e : decode e = none := by rw [decode.eq_def]
@[simp] theorem decode_k (a : T) : decode (k a) = none := by rw [decode.eq_def]
end submission.Austin9337

set_option autoImplicit false
namespace submission.Austin9337
open T

def Code (b key out : T) : Prop := ∃ r : Answer b, decode b = some r ∧ r.key = key ∧ r.value = out
def Hit (a b out : T) : Prop := Code b a out
def Plain (a b out : T) : Prop := out = p a b ∨ (a = b ∧ out = k b)
def Range (b out : T) : Prop := ∃ a, q a b = out

theorem range_iff (b out : T) : Range b out ↔ (inv b out).isSome = true := by
  constructor
  · rintro ⟨a,rfl⟩; simp only [inv_complete,Option.isSome_some]
  · intro h
    cases hi : inv b out with
    | none => simp [hi] at h
    | some a => exact ⟨a,inv_sound hi⟩

theorem code_out_root {b key out : T} (h : Code b key out) : rootSize out < sz b := by
  obtain ⟨r,_,_,he⟩ := h
  rw [←he]; exact r.value_bound

theorem code_key_root {b key out : T} (h : Code b key out) : rootSize key ≤ sz b := by
  obtain ⟨r,_,he,_⟩ := h
  rw [←he]; exact r.key_bound

theorem code_key_ne {b key out : T} (h : Code b key out) : key ≠ b := by
  obtain ⟨r,_,he,_⟩ := h
  rw [←he]; exact r.key_ne

theorem q_hit {a b out : T} (h : Hit a b out) : q a b = out := by
  obtain ⟨r,hd,hk,ho⟩ := h
  rw [←hk,←ho]
  change evalWith r.key b (decode b) = r.value
  rw [hd,evalWith_hit]

theorem q_cases (a b : T) : Plain a b (q a b) ∨ Hit a b (q a b) := by
  by_cases he : a = b
  · subst a; exact Or.inl (Or.inr ⟨rfl,q_square b⟩)
  · cases hd : decode b with
    | none => left; left; simp [q,hd,evalWith,he]
    | some r =>
      by_cases hk : a = r.key
      · have hq : q a b = r.value := by rw [hk]; simp [q,hd,evalWith_hit]
        right
        exact ⟨r,hd,hk.symm,hq.symm⟩
      · left; left; simp [q,hd,evalWith,he,hk]

theorem plain_growth {a b out : T} (h : Plain a b out) : sz a < sz out ∧ sz b < sz out := by
  rcases h with rfl | ⟨rfl,rfl⟩ <;> simp only [sz] <;> constructor <;> omega

theorem code_unique {b a c out other : T} (h : Code b a out) (h' : Code b c other) : a = c ∧ out = other := by
  obtain ⟨r,hd,hk,ho⟩ := h
  obtain ⟨s,hd',hk',ho'⟩ := h'
  have he := Option.some.inj (hd.symm.trans hd')
  rw [←he] at hk' ho'
  exact ⟨hk.symm.trans hk',ho.symm.trans ho'⟩
end submission.Austin9337

set_option autoImplicit false
namespace submission.Austin9337
open T

def primary (u second : T) : Option (Answer (p u second)) :=
  match second with
  | p y v =>
    have hy : sz y < sz (p u (p y v)) := by simp only [sz]; omega
    match hi : inverseWith y u (decode y) with
    | none => none
    | some x =>
      if (inverseWith y v (decode y)).isSome then
        some {
          key := y
          value := x
          key_ne := by
            intro he
            have hs := congrArg sz he
            simp only [sz] at hs
            omega
          key_bound := by
            have hs := rootSize_le y
            simp only [sz]
            omega
          value_bound := by
            have hs := inverseWith_root_bound hi
            have ht := rootSize_le u
            simp only [sz]
            omega }
      else none
  | _ => none

def extra (u second : T) : Option (Answer (p u second)) :=
  match u with
  | p x v =>
    have hx : sz x < sz (p (p x v) second) := by simp only [sz]; omega
    have hu' : sz (p x v) < sz (p (p x v) second) := by simp only [sz]; omega
    if x = second ∧ (inverseWith x v (decode x)).isSome ∧
        evalWith (p x v) x (decode x) = p (p x v) second ∧
        evalWith (p (p x v) second) (p x v) (decode (p x v)) = p (p (p x v) second) (p x v) then
      some {
        key := p (p (p x v) second) (p x v)
        value := x
        key_ne := by
          intro he
          have hs := congrArg sz he
          simp only [sz] at hs
          omega
        key_bound := by simp only [rootSize,sz]; omega
        value_bound := by
          have hs := rootSize_le x
          simp only [sz]
          omega }
    else none
  | _ => none

theorem decode_pair (u second : T) : decode (p u second) = combine (primary u second) (extra u second) := by
  rw [decode.eq_def]
  cases u <;> cases second <;> rfl

def Primary (u second key out : T) : Prop := ∃ v,
  second = p key v ∧ q out key = u ∧ Range key v

def Extra (u second key out : T) : Prop := ∃ v,
  u = p out v ∧ out = second ∧ Range out v ∧ q u out = p u second ∧
  key = p (p u second) u ∧ q (p u second) u = key

theorem primary_sound {u second : T} {r : Answer (p u second)}
    (h : primary u second = some r) : Primary u second r.key r.value := by
  cases second with
  | e => cases h
  | k a => cases h
  | p y v =>
    simp only [primary] at h
    split at h
    · cases h
    · rename_i x hi
      split at h
      · rename_i hr
        have he := Option.some.inj h
        have hk := congrArg Answer.key he
        have hv := congrArg Answer.value he
        simp only at hk hv
        rw [←hk,←hv]
        exact ⟨v,rfl,inv_sound hi,(range_iff _ _).mpr hr⟩
      · cases h

theorem primary_complete {u second key out : T} (h : Primary u second key out) :
    ∃ r : Answer (p u second), primary u second = some r ∧ r.key = key ∧ r.value = out := by
  obtain ⟨v,rfl,hq,hr⟩ := h
  have hi : inverseWith key u (decode key) = some out := by
    change inv key u = some out
    rw [←hq,inv_complete]
  have hv := (range_iff _ _).mp hr
  unfold inv at hv
  let r : Answer (p u (p key v)) := ⟨key,out,by
      intro he
      have hs := congrArg sz he
      simp only [sz] at hs
      omega,by
      have hs := rootSize_le key
      simp only [sz]
      omega,by
      have hs := inverseWith_root_bound hi
      have ht := rootSize_le u
      simp only [sz]
      omega⟩
  refine ⟨r,?_,rfl,rfl⟩
  simp only [primary]
  split
  · rename_i hn
    rw [hi] at hn
    cases hn
  · rename_i x hx
    have he := Option.some.inj (hx.symm.trans hi)
    subst x
    simp only [if_pos hv]
    rfl

theorem extra_sound {u second : T} {r : Answer (p u second)}
    (h : extra u second = some r) : Extra u second r.key r.value := by
  cases u with
  | e => cases h
  | k a => cases h
  | p x v =>
    simp only [extra] at h
    split at h
    · rename_i hc
      have he := Option.some.inj h
      have hk := congrArg Answer.key he
      have hv := congrArg Answer.value he
      simp only at hk hv
      rw [←hk,←hv]
      exact ⟨v,rfl,hc.1,(range_iff _ _).mpr hc.2.1,hc.2.2.1,rfl,hc.2.2.2⟩
    · cases h

theorem extra_complete {u second key out : T} (h : Extra u second key out) :
    ∃ r : Answer (p u second), extra u second = some r ∧ r.key = key ∧ r.value = out := by
  obtain ⟨v,rfl,rfl,hr,hq,rfl,hq'⟩ := h
  have hv := (range_iff _ _).mp hr
  unfold inv at hv
  unfold q at hq hq'
  simp only [extra,hv,hq,hq',and_self,↓reduceIte]
  exact ⟨_,rfl,rfl,rfl⟩

theorem combine_cases {b : T} {a c : Option (Answer b)} {o : Answer b}
    (h : combine a c = some o) : a = some o ∨ c = some o := by
  cases a <;> cases c <;> simp only [combine] at h ⊢
  · cases h
  · exact Or.inr h
  · exact Or.inl h
  · split at h
    · exact Or.inl h
    · cases h

theorem code_pair_cases {u second key out : T} (h : Code (p u second) key out) :
    Primary u second key out ∨ Extra u second key out := by
  obtain ⟨r,hd,hk,hv⟩ := h
  rw [decode_pair] at hd
  rw [←hk,←hv]
  rcases combine_cases hd with hp | he
  · exact Or.inl (primary_sound hp)
  · exact Or.inr (extra_sound he)

theorem code_shape {b key out : T} (h : Code b key out) :
    ∃ u second, b = p u second ∧ (Primary u second key out ∨ Extra u second key out) := by
  cases b with
  | e => obtain ⟨r,hd,_,_⟩ := h; simp at hd
  | k a => obtain ⟨r,hd,_,_⟩ := h; simp at hd
  | p u second => exact ⟨u,second,rfl,code_pair_cases h⟩

end submission.Austin9337

set_option autoImplicit false
namespace submission.Austin9337
open T

theorem candidates_disjoint {u second a out key value : T}
    (ih : ∀ l r k x, sz (p l r) < sz (p u second) →
      Extra l r k x → Code (p l r) k x)
    (hp : Primary u second a out) (he : Extra u second key value) : False := by
  obtain ⟨w,rfl,hq,hr⟩ := hp
  obtain ⟨v,hu,hx,hr',hq',hk,hq''⟩ := he
  subst value
  rw [hu] at hq hq' hk hq'' ih
  have hv : v = a := by
    rcases q_cases out a with hp | hh
    · rcases hp with hp | ⟨_,hp⟩
      · rw [hq] at hp
        exact (T.p.inj hp).2
      · rw [hq] at hp
        cases hp
    · have hs := code_out_root hh
      rw [hq] at hs
      simp only [rootSize,sz] at hs
      omega
  subst v
  have hsmall : sz (p (p a w) a) < sz (p (p (p a w) a) (p a w)) := by
    simp only [sz]; omega
  have hex : Extra (p a w) a (p (p (p a w) a) (p a w)) a := by
    refine ⟨w,rfl,rfl,hr,?_,rfl,hq'⟩
    rcases q_cases out a with hp | hh
    · rcases hp with hp | ⟨_,hp⟩
      · rw [hq] at hp
        have hx := (T.p.inj hp).1
        rw [←hx] at hq
        exact hq
      · rw [hq] at hp; cases hp
    · have hs := code_out_root hh
      rw [hq] at hs
      simp only [rootSize,sz] at hs
      omega
  have hc := ih (p a w) a _ a hsmall hex
  have hqsmall := q_hit hc
  rw [hqsmall, hk] at hq''
  have hs := congrArg sz hq''
  simp only [sz] at hs
  omega

theorem candidate_complete_at (n : Nat) : ∀ u second key out,
    sz (p u second) = n → (Primary u second key out ∨ Extra u second key out) →
    Code (p u second) key out := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro u second key out hn hc
    have lower : ∀ l r k x, sz (p l r) < sz (p u second) → Extra l r k x → Code (p l r) k x := by
      intro l r k x hs he
      exact ih (sz (p l r)) (by omega) l r k x rfl (Or.inr he)
    have disjoint : ∀ a x k y, Primary u second a x → Extra u second k y → False := by
      intro a x k y hp he
      exact candidates_disjoint lower hp he
    rcases hc with hp | he
    · obtain ⟨r,hp',hk,hv⟩ := primary_complete hp
      have hn' : extra u second = none := by
        cases hh : extra u second with
        | none => rfl
        | some s => exact False.elim (disjoint key out s.key s.value hp (extra_sound hh))
      exact ⟨r,by rw [decode_pair,hp',hn']; rfl,hk,hv⟩
    · obtain ⟨r,he',hk,hv⟩ := extra_complete he
      have hn' : primary u second = none := by
        cases hh : primary u second with
        | none => rfl
        | some s => exact False.elim (disjoint s.key s.value key out (primary_sound hh) he)
      exact ⟨r,by rw [decode_pair,hn',he']; rfl,hk,hv⟩

theorem code_of_primary {u second key out : T} (h : Primary u second key out) :
    Code (p u second) key out := candidate_complete_at _ _ _ _ _ rfl (Or.inl h)
theorem code_of_extra {u second key out : T} (h : Extra u second key out) :
    Code (p u second) key out := candidate_complete_at _ _ _ _ _ rfl (Or.inr h)

end submission.Austin9337

set_option autoImplicit false
namespace submission.Austin9337
open T

theorem q_ne_right (a b : T) : q a b ≠ b := by
  intro he
  rcases q_cases a b with hp | hh
  · have hs := (plain_growth hp).2
    rw [he] at hs
    omega
  · rw [he] at hh
    obtain ⟨u,second,rfl,hc⟩ := code_shape hh
    rcases hc with ⟨v,hs,hq,hr⟩ | ⟨v,hu,hs,hr,hq,hk,hq'⟩
    · subst second
      rcases q_cases (p u (p a v)) a with hp | hh
      · have hg := (plain_growth hp).1
        rw [hq] at hg
        simp only [sz] at hg
        omega
      · have hg := code_key_root hh
        simp only [rootSize,sz] at hg
        omega
    · have hg := congrArg sz hs
      simp only [sz] at hg
      omega

theorem range_ne {a b : T} (h : Range a b) : b ≠ a := by
  obtain ⟨x,hx⟩ := h
  rw [←hx]
  exact q_ne_right x a

theorem range_small_hit {a b : T} (hr : Range a b) (hs : sz b ≤ sz a) : ∃ x, Code a x b := by
  obtain ⟨x,hx⟩ := hr
  rcases q_cases x a with hp | hh
  · have hg := (plain_growth hp).2
    rw [hx] at hg
    omega
  · rw [hx] at hh
    exact ⟨x,hh⟩

theorem fixed_left_root {a b : T} (h : q a b = a) : rootSize a ≤ sz b := by
  rcases q_cases a b with hp | hh
  · have hs := (plain_growth hp).1
    rw [h] at hs
    omega
  · exact code_key_root hh

theorem reverse_raw {a b : T} (hr : Range a b) : q a b = p a b := by
  rcases q_cases a b with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · exact hp
    · exact False.elim (range_ne hr he.symm)
  · obtain ⟨l,r,hb,hc⟩ := code_shape hh
    rcases hc with ⟨v,hs,hq,hv⟩ | ⟨v,hl,ho,hv,hq,hkey,hq'⟩
    · rw [hs] at hb
      obtain ⟨z,hz⟩ := hr
      rcases q_cases z a with hp | hc
      · rcases hp with hp | ⟨_,hp⟩
        · rw [hz,hb] at hp
          have hg := congrArg sz (T.p.inj hp).2
          simp only [sz] at hg
          omega
        · rw [hz,hb] at hp
          cases hp
      · have hg := code_out_root hc
        rw [hz,hb] at hg
        simp only [rootSize,sz] at hg
        omega
    · have hsmall : sz b ≤ sz a := by rw [hkey,←hb]; simp only [sz]; omega
      obtain ⟨z,hz⟩ := range_small_hit hr hsmall
      rw [hkey] at hz
      rcases code_pair_cases hz with hp | he
      · obtain ⟨t,ht,hz',_⟩ := hp
        rw [hl,ho] at ht
        have hkr := (T.p.inj ht).1
        rw [←hkr,←hb] at hz'
        have hg := fixed_left_root hz'
        rw [hb,hl,ho] at hg
        simp only [rootSize,sz] at hg
        omega
      · obtain ⟨t,ht,ho',_,_,_,_⟩ := he
        have hg := congrArg sz ho'
        rw [hb] at hg
        simp only [sz] at hg
        omega

theorem sandwich_raw {a b : T} (hr : Range a b) : q (p a b) a = p (p a b) a := by
  rcases q_cases (p a b) a with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · exact hp
    · have hs := congrArg sz he
      simp only [sz] at hs
      omega
  · obtain ⟨l,r,ha,hc⟩ := code_shape hh
    rcases hc with ⟨v,hshape,_,_⟩ | ⟨v,hl,ho,hv,hq,hkey,hq'⟩
    · have hs := congrArg sz hshape
      rw [ha] at hs
      simp only [sz] at hs
      omega
    · have hb : b = l := (T.p.inj hkey).2
      have hsmall : sz b ≤ sz a := by rw [hb,ha]; simp only [sz]; omega
      obtain ⟨z,hz⟩ := range_small_hit hr hsmall
      have hout := (code_unique hh hz).2
      have hs := congrArg sz hl
      rw [hout,hb] at hs
      simp only [sz] at hs
      omega

end submission.Austin9337

set_option autoImplicit false
namespace submission.Austin9337
open T

theorem primary_cycle {x u t l b : T} (hu : q u x = l) (hr : Range x b)
    (ht : q t u = p l (p x b)) : q (p l (p x b)) t = x := by
  rcases q_cases t u with hp | hh
  · rcases hp with hp | ⟨_,hp⟩
    · rw [ht] at hp
      have hl := (T.p.inj hp).1
      have hu' := (T.p.inj hp).2
      have hraw := sandwich_raw hr
      rw [hu'] at hraw
      have hl' : l = p u x := hu.symm.trans hraw
      have hlu : q l u = p l u := by
        calc
          q l u = q t u := by rw [hl]
          _ = p l (p x b) := ht
          _ = p l u := by rw [hu']
      have hc : Extra u x (p l u) x := by
        refine ⟨b,hu'.symm,rfl,hr,?_,?_,?_⟩
        · exact hraw
        · rw [hl']
        · rw [←hl']
          exact hlu
      have hc' := code_of_extra hc
      rw [←hl'] at hc'
      have hg := q_hit hc'
      rw [hu',←hl]
      exact hg
    · rw [ht] at hp
      cases hp
  · have hbound := code_out_root hh
    rw [ht] at hbound
    rcases q_cases u x with hp | hc
    · have hg := (plain_growth hp).1
      rw [hu] at hg
      simp only [rootSize] at hbound
      omega
    · obtain ⟨c,d,hx,hcases⟩ := code_shape hc
      rcases hcases with ⟨v,hd,_,_⟩ | ⟨v,hcshape,ho,_,_,hukey,_⟩
      · rw [hd] at hx
        rw [hx] at hbound
        simp only [rootSize,sz] at hbound
        omega
      · rw [ht,hukey] at hh
        rcases code_pair_cases hh with hp | he
        · obtain ⟨v,_,hq,_⟩ := hp
          rw [←hx] at hq
          exact hq
        · obtain ⟨v,_,he,_,_,_,_⟩ := he
          have hs := congrArg sz he
          rw [hx] at hs
          simp only [sz] at hs
          omega

theorem cycle (x y t : T) (ht : q t (q x y) = y) : q y t = x := by
  rcases q_cases x y with hp | hh
  · rcases hp with hp | ⟨he,hp⟩
    · rw [hp] at ht
      rcases q_cases t (p x y) with hp' | hh'
      · have hg := (plain_growth hp').2
        rw [ht] at hg
        simp only [sz] at hg
        omega
      · rw [ht] at hh'
        rcases code_pair_cases hh' with hp' | he'
        · obtain ⟨v,_,hq,_⟩ := hp'
          exact hq
        · obtain ⟨v,hx,_,hr,hq,hkey,_⟩ := he'
          have hc : Primary (p x y) x y x := ⟨v,hx,hq,hr⟩
          have hg := q_hit (code_of_primary hc)
          rw [hkey]
          exact hg
    · rw [hp] at ht
      rcases q_cases t (k y) with hp' | hh'
      · have hg := (plain_growth hp').2
        rw [ht] at hg
        simp only [sz] at hg
        omega
      · obtain ⟨r,hd,_,_⟩ := hh'
        simp only [decode_k] at hd
        cases hd
  · obtain ⟨l,second,hy,hc⟩ := code_shape hh
    rcases hc with ⟨b,hs,hu,hr⟩ | ⟨b,hl,ho,hr,hq,hkey,hq'⟩
    · rw [hs] at hy
      rw [hy]
      apply primary_cycle hu hr
      exact ht.trans hy
    · have hq0 : q l (q x y) = y := hq.trans hy.symm
      have htl : t = l := q_right_injective _ _ _ (ht.trans hq0.symm)
      rw [htl,hy]
      exact hq'

end submission.Austin9337

set_option autoImplicit false
namespace submission.Austin9337
open T

theorem range_prefixed {a b : T} (hr : Range a (p a b)) : b = a := by
  obtain ⟨x,hx⟩ := hr
  rcases q_cases x a with hp | hh
  · rcases hp with hp | ⟨_,hp⟩
    · rw [hx] at hp
      exact (T.p.inj hp).2
    · rw [hx] at hp
      cases hp
  · have hs := code_out_root hh
    rw [hx] at hs
    simp only [rootSize] at hs
    omega

theorem source (x y z : T) : q y (q (q x y) (q y (q z y))) = x := by
  have hr : Range y (q z y) := ⟨z,rfl⟩
  have hw := reverse_raw hr
  rw [hw]
  rcases q_cases (q x y) (p y (q z y)) with hp | hh
  · rcases hp with hp | ⟨he,_⟩
    · rw [hp]
      apply q_hit
      apply code_of_primary
      exact ⟨q z y,rfl,rfl,hr⟩
    · have hne := range_prefixed (show Range y (p y (q z y)) from ⟨x,he⟩)
      exact False.elim (q_ne_right z y hne)
  · rcases code_pair_cases hh with hp | he
    · obtain ⟨v,_,hq,_⟩ := hp
      exact cycle x y _ hq
    · obtain ⟨v,_,ho,_,_,_,hq⟩ := he
      have hx : x = p y (q z y) := q_right_injective _ _ _ hq.symm
      rw [ho,hw,hx]

end submission.Austin9337

set_option autoImplicit false
namespace submission.Austin9337
abbrev Carrier := T
def mul : Carrier → Carrier → Carrier := q
def opposite (a b : Carrier) : Carrier := mul b a
def embed : Nat → Carrier
  | 0 => T.e
  | n + 1 => T.k (embed n)
@[simp] theorem embed_size (n : Nat) : sz (embed n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [embed,sz,ih]
theorem embed_injective (n j : Nat) (h : embed n = embed j) : n = j := by
  have hs := congrArg sz h
  simpa only [embed_size] using hs

theorem equation9337 (x y z : Carrier) :
    x = mul y (mul (mul x y) (mul y (mul z y))) := (source x y z).symm
theorem equation36867 (x y z : Carrier) :
    x = opposite (opposite (opposite (opposite y z) y) (opposite y x)) y :=
  equation9337 x y z
theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op y (op (op x y) (op y (op z y)))) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨Carrier,mul,embed,equation9337,embed_injective⟩
end submission.Austin9337

namespace submission
abbrev CM := Austin9337.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin9337.embed n = Austin9337.embed j) : n = j :=
  Austin9337.embed_injective n j h
end CM
instance modelMagma : Magma CM := ⟨Austin9337.mul⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin9337.equation9337 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin9337.embed_injective 0 1
      (h (submission.Austin9337.embed 0) (submission.Austin9337.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

