import Lean.Elab.Tactic.Omega
import JudgeProblem
set_option Elab.async false


set_option autoImplicit false
namespace submission.Austin8485Base

inductive T where
  | e : T
  | k : T → T
  | p : T → T → T
  deriving DecidableEq
open T

def sz : T → Nat
  | e => 0
  | k x => sz x + 1
  | p x y => sz x + sz y + 2
def drop : T → T
  | e => e
  | k x => x
  | p x _ => x

theorem drop_size_le (a : T) : sz (drop a) ≤ sz a := by
  cases a <;> simp only [drop,sz] <;> omega

def possibleRight (a v : T) : Bool :=
  decide (v = k a) || (match v with | p _ second => decide (second = a) | _ => false) ||
    decide (v = drop a)

def admissible (a b : T) : Bool :=
  match b with
  | p _ v => decide (v ≠ a) && possibleRight a v
  | _ => false

theorem possibleRight_lower {a v : T} (h : possibleRight a v = true) : sz (drop a) ≤ sz v := by
  have hd := drop_size_le a
  unfold possibleRight at h
  simp only [Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with (hk | hp) | he
  · rw [hk]; simp only [sz]; omega
  · cases v with
    | e => cases hp
    | k x => cases hp
    | p x y =>
      have he : y = a := of_decide_eq_true hp
      rw [he]; simp only [sz]; omega
  · rw [he]; omega

theorem admissible_bound {a b : T} (h : admissible a b = true) : sz (drop a) < sz b := by
  cases b with
  | e => cases h
  | k x => cases h
  | p x v =>
    simp only [admissible,Bool.and_eq_true,decide_eq_true_eq] at h
    have hs := possibleRight_lower h.2
    simp only [sz]; omega

def selfTree (t : T) : T := p t (p (p (k t) t) t)

theorem selfTree_ne (t : T) : t ≠ selfTree t := by
  intro he
  have hs := congrArg sz he
  simp only [selfTree,sz] at hs; omega

def tower : Nat → T
  | 0 => e
  | n+1 => k (tower n)
@[simp] theorem tower_size (n : Nat) : sz (tower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower,sz,ih]
theorem tower_injective (i j : Nat) (h : tower i = tower j) : i = j := by
  have hs := congrArg sz h
  simpa only [tower_size] using hs

def protectedPair (a b : T) : Bool :=
  match a with
  | p u v => decide (v = b) || (match b with
      | p x y => decide (u = y ∧ v = x)
      | _ => false)
  | _ => false

theorem protected_size {a b : T} (h : protectedPair a b = true) : sz b ≤ sz a := by
  cases a with
  | e => cases h
  | k x => cases h
  | p u v =>
    cases b with
    | e => simp only [sz]; omega
    | k x =>
      simp only [protectedPair, Bool.or_false, decide_eq_true_eq] at h
      rw [h]
      simp only [sz]; omega
    | p x y =>
      simp only [protectedPair, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with hv | ⟨hu,hv⟩
      · rw [hv]; simp only [sz]; omega
      · rw [hu,hv]; simp only [sz]; omega

end submission.Austin8485Base

set_option autoImplicit false

namespace submission.Austin8485
open submission.Austin8485Base
open T

inductive Query where
  | mul : T → T → Query
  | image : T → T → Query
  | selfTail : T → T → Query
  | intersection : T → T → Query
  | bridge : T → T → Query

def rank : Query → Nat
  | .mul a b | .image a b | .intersection a b => 3 * (sz a + sz b) + 2
  | .bridge a b => 3 * (sz a + sz b) + 1
  | .selfTail a b => 3 * max (sz a) (sz b)

abbrev Reply : Query → Type
  | .mul _ _ => T
  | _ => Bool

def fallback : (task : Query) → Reply task
  | .mul a b => p a b
  | .image _ _ | .selfTail _ _ | .intersection _ _ | .bridge _ _ => false

abbrev Look (n : Nat) := (task : Query) → rank task < n → Reply task

def ask {n : Nat} (look : Look n) (task : Query) : Reply task :=
  if h : rank task < n then look task h else fallback task

def shape (a v : T) : Bool :=
  (match v with | p _ s => decide (s = a) | _ => false) ||
  (match a with | p s _ => decide (s = v) | _ => false)

def raw {n : Nat} (look : Look n) (a b : T) : Bool :=
  if a = b then false else
  match b with
  | p x v =>
    if v = a ∨ protectedPair a b = true then true else
    if shape a v
    then decide (ask look (.mul a b) = p a b)
    else true
  | _ => true

def smallCode {n : Nat} (look : Look n) (a b : T) : Bool :=
  match b with
  | p x (p u last) =>
    decide (last = a) && raw look x (p u last) &&
      ((match u with
        | p w second => decide (second = a) && raw look w a && ask look (.image x w)
        | _ => false) ||
       (decide (u = k a) && ask look (.image x a)) ||
       (decide (u = drop a) && raw look u a && ask look (.intersection x a)))
  | _ => false

def bigCode {n : Nat} (look : Look n) (a b : T) : Bool :=
  match a,b with
  | p first s,p x v => decide (first = v) && ask look (.selfTail v s) &&
      raw look x v && ask look (.bridge x v)
  | _,_ => false

def decode {n : Nat} (look : Look n) (a b : T) : Bool :=
  if a = b then false else
  match b with
  | p _ v => if v = a ∨ protectedPair a b = true then false
      else smallCode look a b || bigCode look a b
  | _ => false

def hasDecoder {n : Nat} (look : Look n) (b : T) : Bool :=
  match b with
  | p x v => (match v with
      | p _ a => smallCode look a b
      | _ => false) || (raw look x v && ask look (.bridge x v))
  | _ => false

def imageBody {n : Nat} (look : Look n) (b out : T) : Bool :=
  decide (out = k b) ||
  (match out with
    | p a second => decide (second = b) && raw look a b
    | _ => false) ||
  (match b with
    | p x _ => decide (out = x) && hasDecoder look b
    | _ => false)

def selfBody {n : Nat} (look : Look n) (t v : T) : Bool :=
  (match v with
    | p (p w second) last => decide (second = t ∧ last = t) &&
        raw look w t && ask look (.image t w)
    | _ => false) ||
  (match t with
    | p first s => decide (first = v) && ask look (.selfTail v s)
    | _ => false)

def intersectionBody {n : Nat} (look : Look n) (x a : T) : Bool :=
  match a with
  | p u t =>
    decode look (k x) a ||
    (match x with
      | p w _ => decode look w a && hasDecoder look x
      | _ => false) ||
    (match t with
      | p _ (p z second) => decide (second = x) && raw look z x && smallCode look (p z second) a
      | _ => false) ||
    (raw look t x && ask look (.selfTail t x) && raw look u t &&
      ask look (.bridge u t) && decide (p t x ≠ a ∧ x ≠ a ∧ x ≠ u))
  | _ => false

def bridgeBody {n : Nat} (look : Look n) (x v : T) : Bool :=
  imageBody look x v ||
  (match x with
    | p _ t => ask look (.selfTail v t) && ask look (.selfTail t x) && raw look t x
    | _ => false) ||
  (match v with
    | p t _ => ask look (.selfTail v t) && ask look (.selfTail t x) && raw look t x
    | _ => false) ||
  (match x with
    | p (p t s) _ => ask look (.selfTail v t) && ask look (.selfTail t s) && hasDecoder look x
    | _ => false)

def evaluate {n : Nat} (look : Look n) : (task : Query) → Reply task
  | .mul a b => if a = b then k b else if decode look a b then drop b else p a b
  | .image b out => imageBody look b out
  | .selfTail t v => selfBody look t v
  | .intersection x a => intersectionBody look x a
  | .bridge x v => bridgeBody look x v

def run (task : Query) : Reply task :=
  evaluate (n:=rank task) (fun smaller _ => run smaller) task
termination_by rank task

def mul (a b : T) : T := run (.mul a b)
def image (b out : T) : Bool := run (.image b out)
def selfTail (t v : T) : Bool := run (.selfTail t v)
def intersection (x a : T) : Bool := run (.intersection x a)
def bridge (x v : T) : Bool := run (.bridge x v)

abbrev scope (n : Nat) : Look n := fun task _ => run task

theorem run_eq (task : Query) : run task = evaluate (scope (rank task)) task := by
  rw [run.eq_def]

theorem ask_eq_run {n : Nat} {task : Query} (h : rank task < n) :
    ask (scope n) task = run task := by simp only [ask,h,↓reduceDIte]

@[simp] theorem mul_square (a : T) : mul a a = k a := by
  unfold mul
  rw [run_eq]
  simp only [evaluate,↓reduceIte]

theorem mul_cases (a b : T) : mul a b = p a b ∨
    (a = b ∧ mul a b = k b) ∨
    (a ≠ b ∧ decode (scope (rank (.mul a b))) a b = true ∧ mul a b = drop b) := by
  unfold mul
  rw [run_eq]
  by_cases he : a = b
  · simp only [evaluate,he,↓reduceIte,or_true,true_or,and_self]
  · simp only [evaluate,he,↓reduceIte]
    cases hd : decode (scope (rank (.mul a b))) a b <;>
      simp only [hd,Bool.false_eq_true,↓reduceIte,and_self,or_true,true_or,
        he,not_false_eq_true,and_true,true_and,false_and,false_or]
    exact Or.inr he

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem shape_possibleRight {a v : T} (h : shape a v = true) : possibleRight a v = true := by
  simp only [shape,Bool.or_eq_true] at h
  rcases h with hv | ha
  · cases v with
    | e => cases hv
    | k t => cases hv
    | p u s =>
      have he : s = a := of_decide_eq_true hv
      subst s
      simp only [possibleRight,decide_true,Bool.or_true,Bool.true_or]
  · cases a with
    | e => cases ha
    | k t => cases ha
    | p s u =>
      have he : s = v := of_decide_eq_true ha
      subst s
      simp only [possibleRight,drop,decide_true,Bool.or_true]

theorem raw_drop_large {n : Nat} (look : Look n) {a b : T}
    (hne : a ≠ b) (hs : sz b ≤ sz (drop a)) : raw look a b = true := by
  cases b with
  | e => simp only [raw,hne,↓reduceIte]
  | k t => simp only [raw,hne,↓reduceIte]
  | p x v =>
    have hshape : shape a v = false := by
      cases he : shape a v with
      | false => rfl
      | true =>
        have hl := possibleRight_lower (shape_possibleRight he)
        simp only [sz] at hs
        omega
    simp only [raw,hne,↓reduceIte,hshape,Bool.false_eq_true,ite_self]

theorem raw_square_right {n : Nat} (look : Look n) (t : T) : raw look (k t) t = true := by
  apply raw_drop_large look
  · intro he
    have := congrArg sz he; simp only [sz] at this; omega
  · simp only [drop]; omega

theorem raw_right_child {n : Nat} (look : Look n) (x t : T) : raw look t (p x t) = true := by
  have hne : t ≠ p x t := by
    intro he
    have := congrArg sz he; simp only [sz] at this; omega
  simp only [raw,hne,↓reduceIte,true_or]

@[simp] theorem image_square (b : T) : image b (k b) = true := by
  unfold image
  rw [run_eq]
  simp only [evaluate,imageBody,decide_true,Bool.true_or]

theorem concrete_canonical_self_point (t : T) : mul t (selfTree t) = t := by
  let look := scope (rank (.mul t (selfTree t)))
  have hi : ask look (.image t (k t)) = true := by
    rw [ask_eq_run (by simp only [rank,selfTree,sz]; omega)]
    exact image_square t
  have hr1 := raw_square_right look t
  have hr2 := raw_right_child look (p (k t) t) t
  have hc : smallCode look t (selfTree t) = true := by
    change (decide (t = t) && raw look t (p (p (k t) t) t) &&
      ((decide (t = t) && raw look (k t) t && ask look (.image t (k t))) ||
       (decide (p (k t) t = k t) && ask look (.image t t)) ||
       (decide (p (k t) t = drop t) && raw look (p (k t) t) t &&
        ask look (.intersection t t)))) = true
    simp only [decide_true,Bool.true_and,hr1,hr2,hi,
      Bool.and_self,Bool.true_or]
  have hp : protectedPair t (selfTree t) = false := by
    cases he : protectedPair t (selfTree t) with
    | false => rfl
    | true =>
      have hs := protected_size he
      simp only [selfTree,sz] at hs; omega
  have hn := selfTree_ne t
  have hv : p (p (k t) t) t ≠ t := by
    intro he
    have hs := congrArg sz he; simp only [sz] at hs; omega
  have hd : decode look t (selfTree t) = true := by
    change (if t = selfTree t then false else
      if p (p (k t) t) t = t ∨ protectedPair t (selfTree t) = true then false
      else smallCode look t (selfTree t) || bigCode look t (selfTree t)) = true
    simp only [hn,↓reduceIte,hp,hv,Bool.false_eq_true,
      or_self,not_false_eq_true,hc,Bool.true_or]
  unfold mul
  rw [run_eq]
  change (if t = selfTree t then k (selfTree t)
    else if decode look t (selfTree t) then drop (selfTree t) else p t (selfTree t)) = t
  rw [if_neg hn,if_pos hd]
  rfl

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem smallCode_shape {n : Nat} {look : Look n} {a x v : T}
    (h : smallCode look a (p x v) = true) : shape a v = true := by
  cases v with
  | e => cases h
  | k t => cases h
  | p u last =>
    simp only [smallCode,Bool.and_eq_true,decide_eq_true_eq] at h
    have he := h.1.1
    subst last
    simp only [shape,decide_true,Bool.true_or]

theorem bigCode_shape {n : Nat} {look : Look n} {a x v : T}
    (h : bigCode look a (p x v) = true) : shape a v = true := by
  cases a with
  | e => cases h
  | k t => cases h
  | p first s =>
    simp only [bigCode,Bool.and_eq_true,decide_eq_true_eq] at h
    have he := h.1.1.1
    subst first
    simp only [shape,decide_true,Bool.or_true]

theorem decode_shape {n : Nat} {look : Look n} {a x v : T}
    (h : decode look a (p x v) = true) : shape a v = true := by
  simp only [decode] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Bool.or_eq_true] at h
      exact h.elim smallCode_shape bigCode_shape

theorem decode_admissible {n : Nat} {look : Look n} {a b : T}
    (h : decode look a b = true) : admissible a b = true := by
  by_cases he : a = b
  · simp only [decode,he,↓reduceIte,Bool.false_eq_true] at h
  · cases b with
    | e => simp only [decode,he,↓reduceIte,Bool.false_eq_true] at h
    | k t => simp only [decode,he,↓reduceIte,Bool.false_eq_true] at h
    | p x v =>
      have hs := shape_possibleRight (decode_shape h)
      have hv : v ≠ a := by
        intro hv
        simp only [decode,hv,true_or,↓reduceIte,ite_self,Bool.false_eq_true] at h
      simp only [admissible,hs,Bool.and_true]
      exact decide_eq_true hv

theorem mul_false_decode {a b : T} (hne : a ≠ b)
    (hd : decode (scope (rank (.mul a b))) a b = false) : mul a b = p a b := by
  unfold mul
  rw [run_eq]
  simp only [evaluate,hne,↓reduceIte,hd,Bool.false_eq_true]

theorem mul_shape_false {a x v : T} (hne : a ≠ p x v) (hs : shape a v = false) :
    mul a (p x v) = p a (p x v) := by
  apply mul_false_decode hne
  cases he : decode (scope (rank (.mul a (p x v)))) a (p x v) with
  | false => rfl
  | true => have ht := decode_shape he; rw [hs] at ht; cases ht

theorem mul_guard_raw {a x v : T} (hne : a ≠ p x v)
    (hg : v = a ∨ protectedPair a (p x v) = true) : mul a (p x v) = p a (p x v) := by
  apply mul_false_decode hne
  simp only [decode,hne,↓reduceIte,hg]

theorem raw_spec {n : Nat} {a b : T} (hr : rank (.mul a b) < n) :
    raw (scope n) a b = true ↔ mul a b = p a b := by
  by_cases he : a = b
  · subst a
    simp only [raw,↓reduceIte,mul_square,reduceCtorEq,Bool.false_eq_true]
  · cases b with
    | e =>
      have hm : mul a e = p a e := mul_false_decode he (by simp only [decode,he,↓reduceIte])
      simp only [raw,he,↓reduceIte,hm]
    | k t =>
      have hm : mul a (k t) = p a (k t) := mul_false_decode he (by simp only [decode,he,↓reduceIte])
      simp only [raw,he,↓reduceIte,hm]
    | p x v =>
      by_cases hg : v = a ∨ protectedPair a (p x v) = true
      · have hm := mul_guard_raw he hg
        simp only [raw,he,↓reduceIte,hg,hm]
      · cases hs : shape a v with
        | false =>
          have hm := mul_shape_false he hs
          simp only [raw,he,↓reduceIte,hg,hs,Bool.false_eq_true,hm]
        | true =>
          simp only [raw,he,↓reduceIte,hg,hs]
          rw [ask_eq_run hr]
          exact decide_eq_true_iff

theorem mul_structural_cases (a b : T) : mul a b = p a b ∨
    (a = b ∧ mul a b = k b) ∨ (admissible a b = true ∧ mul a b = drop b) := by
  rcases mul_cases a b with hp | hs | ⟨_,hc,hd⟩
  · exact Or.inl hp
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr ⟨decode_admissible hc,hd⟩)

theorem mul_ne_right (a b : T) : mul a b ≠ b := by
  intro he
  rcases mul_structural_cases a b with hp | ⟨_,hk⟩ | ⟨ha,hd⟩
  · rw [he] at hp
    have hs := congrArg sz hp; simp only [sz] at hs; omega
  · rw [he] at hk
    have hs := congrArg sz hk; simp only [sz] at hs; omega
  · cases b with
    | e => cases ha
    | k x => cases ha
    | p x v =>
      rw [he] at hd
      have hs := congrArg sz hd; simp only [sz,drop] at hs; omega

theorem mul_drop_large {a b : T} (hne : a ≠ b) (hs : sz b ≤ sz (drop a)) :
    mul a b = p a b := by
  exact (raw_spec (n:=rank (.mul a b)+1) (by omega)).mp (raw_drop_large _ hne hs)

theorem mul_square_right (t : T) : mul (k t) t = p (k t) t := by
  exact (raw_spec (n:=rank (.mul (k t) t)+1) (by omega)).mp (raw_square_right _ t)

theorem mul_right_child (x t : T) : mul t (p x t) = p t (p x t) := by
  exact (raw_spec (n:=rank (.mul t (p x t))+1) (by omega)).mp (raw_right_child _ x t)

theorem mul_protected_raw {a b : T} (hne : a ≠ b) (hp : protectedPair a b = true) :
    mul a b = p a b := by
  apply mul_false_decode hne
  cases b with
  | e => simp only [decode,hne,↓reduceIte]
  | k t => simp only [decode,hne,↓reduceIte]
  | p x v => simp only [decode,hne,↓reduceIte,hp,or_true]

theorem mul_pair_right (w y : T) : mul (p w y) y = p (p w y) y := by
  apply mul_protected_raw
  · intro he
    have := congrArg sz he; simp only [sz] at this; omega
  · simp only [protectedPair,decide_true,Bool.true_or]

theorem mul_swap_pair {x y : T} (hne : x ≠ y) :
    mul (p y x) (p x y) = p (p y x) (p x y) := by
  apply mul_protected_raw
  · intro he; cases he; exact hne rfl
  · simp only [protectedPair,and_self,decide_true,Bool.or_true]

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

def rawValue (a b : T) : Bool := decide (mul a b = p a b)

theorem raw_scope {n : Nat} {a b : T} (h : rank (.mul a b) < n) :
    raw (scope n) a b = rawValue a b := by
  by_cases hp : mul a b = p a b
  · have hr := (raw_spec h).mpr hp
    simp only [hr,rawValue,hp,decide_true]
  · have hr : raw (scope n) a b = false := by
      cases he : raw (scope n) a b with
      | false => rfl
      | true => exact False.elim (hp ((raw_spec h).mp he))
    rw [hr]
    exact (decide_eq_false hp).symm

def smallValue (a b : T) : Bool :=
  match b with
  | p x (p u last) =>
    decide (last = a) && rawValue x (p u last) &&
      ((match u with
        | p w second => decide (second = a) && rawValue w a && image x w
        | _ => false) ||
       (decide (u = k a) && image x a) ||
       (decide (u = drop a) && rawValue u a && intersection x a))
  | _ => false

def bigValue (a b : T) : Bool :=
  match a,b with
  | p first s,p x v => decide (first = v) && selfTail v s && rawValue x v && bridge x v
  | _,_ => false

def decodeValue (a b : T) : Bool :=
  if a = b then false else
  match b with
  | p _ v => if v = a ∨ protectedPair a b = true then false
      else smallValue a b || bigValue a b
  | _ => false

def hasDecoderValue (b : T) : Bool :=
  match b with
  | p x v => (match v with | p _ a => smallValue a b | _ => false) ||
      (rawValue x v && bridge x v)
  | _ => false

theorem smallCode_scope {n : Nat} {a b : T} (hs : 3 * sz b ≤ n) :
    smallCode (scope n) a b = smallValue a b := by
  cases b with
  | e => rfl
  | k t => rfl
  | p x v =>
    cases v with
    | e => rfl
    | k t => rfl
    | p u last =>
      by_cases he : last = a
      · subst last
        have hr0 := raw_scope (a:=x) (b:=p u a) (n:=n)
          (by simp only [rank,sz]; simp only [sz] at hs; omega)
        have hr1 := raw_scope (a:=u) (b:=a) (n:=n)
          (by simp only [rank]; simp only [sz] at hs; omega)
        have hi : ask (scope n) (.image x a) = image x a :=
          ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
        have hj : ask (scope n) (.intersection x a) = intersection x a :=
          ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
        cases u with
        | e => simp only [smallCode,smallValue,hr0,hr1,hi,hj]
        | k t => simp only [smallCode,smallValue,hr0,hr1,hi,hj]
        | p w second =>
          have hrw := raw_scope (a:=w) (b:=a) (n:=n)
            (by simp only [rank]; simp only [sz] at hs; omega)
          have hiw : ask (scope n) (.image x w) = image x w :=
            ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
          simp only [smallCode,smallValue,hr0,hr1,hi,hj,hrw,hiw]
      · simp only [smallCode,smallValue,he,decide_false,Bool.false_and]

theorem bigCode_scope {n : Nat} {a b : T} (hs : 3 * max (sz a) (sz b) ≤ n) :
    bigCode (scope n) a b = bigValue a b := by
  cases a <;> cases b <;> try rfl
  case p.p first s x v =>
    have hr := raw_scope (a:=x) (b:=v) (n:=n)
      (by simp only [rank]; simp only [sz] at hs; omega)
    have hself : ask (scope n) (.selfTail v s) = selfTail v s :=
      ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
    have hb : ask (scope n) (.bridge x v) = bridge x v :=
      ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
    simp only [bigCode,bigValue,hr,hself,hb]

theorem decode_scope {n : Nat} {a b : T} (hs : 3 * max (sz a) (sz b) ≤ n) :
    decode (scope n) a b = decodeValue a b := by
  have hb : 3 * sz b ≤ n := by omega
  have hsmall := smallCode_scope (a:=a) hb
  have hbig := bigCode_scope hs
  unfold decode decodeValue
  split
  · rfl
  · cases b <;> simp only [hsmall,hbig]

theorem hasDecoder_scope {n : Nat} {b : T} (hs : 3 * sz b ≤ n) :
    hasDecoder (scope n) b = hasDecoderValue b := by
  cases b with
  | e => rfl
  | k t => rfl
  | p x v =>
    have hr := raw_scope (a:=x) (b:=v) (n:=n)
      (by simp only [rank]; simp only [sz] at hs; omega)
    have hb : ask (scope n) (.bridge x v) = bridge x v :=
      ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
    cases v with
    | e => simp only [hasDecoder,hasDecoderValue,hr,hb]
    | k t => simp only [hasDecoder,hasDecoderValue,hr,hb]
    | p u a =>
      have hc := smallCode_scope (a:=a) hs
      simp only [hasDecoder,hasDecoderValue,hr,hb,hc]

theorem mul_equation (a b : T) : mul a b =
    if a = b then k b else if decodeValue a b then drop b else p a b := by
  unfold mul
  rw [run_eq]
  simp only [evaluate]
  rw [decode_scope (by simp only [rank]; omega)]

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfTail_shape {t v : T} (h : selfTail t v = true) :
    (∃ w, v = p (p w t) t) ∨ (∃ s, t = p v s) := by
  unfold selfTail at h
  rw [run_eq] at h
  simp only [evaluate,selfBody,Bool.or_eq_true] at h
  rcases h with h | h
  · cases v with
    | e => cases h
    | k u => cases h
    | p u last =>
      cases u with
      | e => cases h
      | k u => cases h
      | p w second =>
        simp only [Bool.and_eq_true,decide_eq_true_eq] at h
        rcases h.1.1 with ⟨rfl,rfl⟩
        exact Or.inl ⟨w,rfl⟩
  · cases t with
    | e => cases h
    | k u => cases h
    | p first s =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h
      rcases h with ⟨rfl,_⟩
      exact Or.inr ⟨s,rfl⟩

theorem selfTail_ne {t v : T} (h : selfTail t v = true) : t ≠ v := by
  intro he
  rcases selfTail_shape h with ⟨w,hv⟩ | ⟨s,ht⟩
  · rw [←he] at hv
    have := congrArg sz hv; simp only [sz] at this; omega
  · rw [he] at ht
    have := congrArg sz ht; simp only [sz] at this; omega

theorem selfTail_raw {n : Nat} (look : Look n) {t v : T} (h : selfTail t v = true) :
    raw look t v = true := by
  rcases selfTail_shape h with ⟨w,rfl⟩ | ⟨s,rfl⟩
  · exact raw_right_child look (p w t) t
  · apply raw_drop_large look
    · intro he
      have := congrArg sz he; simp only [sz] at this; omega
    · simp only [drop]; omega

theorem selfTail_raw_value {t v : T} (h : selfTail t v = true) : rawValue t v = true := by
  rw [←raw_scope (n:=rank (.mul t v)+1) (by omega)]
  exact selfTail_raw _ h

theorem selfTail_raw_gate {n : Nat} (look : Look n) (v t x : T) :
    (selfTail v t && selfTail t x && raw look t x) =
    (selfTail v t && selfTail t x && rawValue t x) := by
  cases hs : selfTail t x with
  | false => simp only [hs,Bool.and_false,Bool.false_and]
  | true => simp only [hs,selfTail_raw look hs,selfTail_raw_value hs]

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

private theorem bool_or_congr {a b c d : Bool} (h : a = b) (g : c = d) :
    (a || c) = (b || d) := by rw [h,g]

def imageValue (b out : T) : Bool :=
  decide (out = k b) ||
  (match out with | p a second => decide (second = b) && rawValue a b | _ => false) ||
  (match b with | p x _ => decide (out = x) && hasDecoderValue b | _ => false)

def selfValue (t v : T) : Bool :=
  (match v with
    | p (p w second) last => decide (second = t ∧ last = t) && rawValue w t && image t w
    | _ => false) ||
  (match t with | p first s => decide (first = v) && selfTail v s | _ => false)

def intersectionValue (x a : T) : Bool :=
  match a with
  | p u t =>
    decodeValue (k x) a ||
    (match x with | p w _ => decodeValue w a && hasDecoderValue x | _ => false) ||
    (match t with
      | p _ (p z second) => decide (second = x) && rawValue z x && smallValue (p z second) a
      | _ => false) ||
    (rawValue t x && selfTail t x && rawValue u t && bridge u t &&
      decide (p t x ≠ a ∧ x ≠ a ∧ x ≠ u))
  | _ => false

def bridgeValue (x v : T) : Bool :=
  imageValue x v ||
  (match x with | p _ t => selfTail v t && selfTail t x && rawValue t x | _ => false) ||
  (match v with | p t _ => selfTail v t && selfTail t x && rawValue t x | _ => false) ||
  (match x with | p (p t s) _ => selfTail v t && selfTail t s && hasDecoderValue x | _ => false)

theorem imageBody_scope {n : Nat} {b out : T} (hs : 3 * max (sz b) (sz out) ≤ n) :
    imageBody (scope n) b out = imageValue b out := by
  have hd := hasDecoder_scope (b:=b) (n:=n) (by omega)
  cases out with
  | e => cases b <;> simp only [imageBody,imageValue,hd]
  | k t => cases b <;> simp only [imageBody,imageValue,hd]
  | p a second =>
    by_cases he : second = b
    · subst second
      have hr := raw_scope (a:=a) (b:=b) (n:=n)
        (by simp only [rank]; simp only [sz] at hs; omega)
      cases b <;> simp only [imageBody,imageValue,hd,hr]
    · cases b <;> simp only [imageBody,imageValue,hd,he,decide_false,Bool.false_and]

theorem selfBody_scope {n : Nat} {t v : T} (hs : 3 * max (sz t) (sz v) ≤ n) :
    selfBody (scope n) t v = selfValue t v := by
  unfold selfBody selfValue
  apply bool_or_congr
  · cases v with
    | e => rfl
    | k u => rfl
    | p u last =>
      cases u with
      | e => rfl
      | k u => rfl
      | p w second =>
        by_cases he : second = t ∧ last = t
        · rcases he with ⟨hsecond,hlast⟩
          subst second
          subst last
          have hr := raw_scope (a:=w) (b:=t) (n:=n)
            (by simp only [rank]; simp only [sz] at hs; omega)
          have hi : ask (scope n) (.image t w) = image t w :=
            ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
          simp only [hr,hi]
        · simp only [he,decide_false,Bool.false_and]
  · cases t with
    | e => rfl
    | k u => rfl
    | p first s =>
      by_cases he : first = v
      · subst first
        have hself : ask (scope n) (.selfTail v s) = selfTail v s :=
          ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
        simp only [hself]
      · simp only [he,decide_false,Bool.false_and]

theorem intersectionBody_scope {n : Nat} {x a : T} (hs : 3 * (sz x + sz a) ≤ n) :
    intersectionBody (scope n) x a = intersectionValue x a := by
  cases a with
  | e => rfl
  | k v => rfl
  | p u t =>
    unfold intersectionBody intersectionValue
    apply bool_or_congr
    · apply bool_or_congr
      · apply bool_or_congr
        · exact decode_scope (by simp only [sz] at hs ⊢; omega)
        · cases x with
          | e => rfl
          | k s => rfl
          | p w s =>
            change (decode (scope n) w (p u t) && hasDecoder (scope n) (p w s)) =
              (decodeValue w (p u t) && hasDecoderValue (p w s))
            have hc := decode_scope (a:=w) (b:=p u t) (n:=n)
              (by simp only [sz] at hs ⊢; omega)
            have hd := hasDecoder_scope (b:=p w s) (n:=n) (by omega)
            simp only [hc,hd]
      · cases t with
        | e => rfl
        | k s => rfl
        | p v w =>
          cases w with
          | e => rfl
          | k s => rfl
          | p z second =>
            have hr := raw_scope (a:=z) (b:=x) (n:=n)
              (by simp only [rank]; simp only [sz] at hs; omega)
            have hc := smallCode_scope (a:=p z second) (b:=p u (p v (p z second))) (n:=n)
              (by omega)
            simp only [hr,hc]
    · have hr1 := raw_scope (a:=t) (b:=x) (n:=n)
        (by simp only [rank]; simp only [sz] at hs; omega)
      have hr2 := raw_scope (a:=u) (b:=t) (n:=n)
        (by simp only [rank]; simp only [sz] at hs; omega)
      have hself : ask (scope n) (.selfTail t x) = selfTail t x :=
        ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
      have hb : ask (scope n) (.bridge u t) = bridge u t :=
        ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
      simp only [hr1,hr2,hself,hb]

theorem bridgeBody_scope {n : Nat} {x v : T} (hs : 3 * (sz x + sz v) + 1 ≤ n) :
    bridgeBody (scope n) x v = bridgeValue x v := by
  unfold bridgeBody bridgeValue
  apply bool_or_congr
  · apply bool_or_congr
    · apply bool_or_congr
      · exact imageBody_scope (by omega)
      · cases x with
        | e => rfl
        | k s => rfl
        | p s t =>
          have h1 : ask (scope n) (.selfTail v t) = selfTail v t :=
            ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
          have h2 : ask (scope n) (.selfTail t (p s t)) = selfTail t (p s t) :=
            ask_eq_run (by simp only [rank,sz]; simp only [sz] at hs; omega)
          simp only [h1,h2]
          exact selfTail_raw_gate _ v t (p s t)
    · cases v with
      | e => rfl
      | k s => rfl
      | p t s =>
        have h1 : ask (scope n) (.selfTail (p t s) t) = selfTail (p t s) t :=
          ask_eq_run (by simp only [rank,sz]; simp only [sz] at hs; omega)
        have h2 : ask (scope n) (.selfTail t x) = selfTail t x :=
          ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
        simp only [h1,h2]
        exact selfTail_raw_gate _ (p t s) t x
  · cases x with
    | e => rfl
    | k s => rfl
    | p w u =>
      cases w with
      | e => rfl
      | k s => rfl
      | p t s =>
        have h1 : ask (scope n) (.selfTail v t) = selfTail v t :=
          ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
        have h2 : ask (scope n) (.selfTail t s) = selfTail t s :=
          ask_eq_run (by simp only [rank]; simp only [sz] at hs; omega)
        have hd := hasDecoder_scope (b:=p (p t s) u) (n:=n) (by omega)
        simp only [h1,h2,hd]

theorem image_equation (b out : T) : image b out = imageValue b out := by
  unfold image
  rw [run_eq]
  exact imageBody_scope (by simp only [rank]; omega)

theorem selfTail_equation (t v : T) : selfTail t v = selfValue t v := by
  unfold selfTail
  rw [run_eq]
  exact selfBody_scope (by simp only [rank]; omega)

theorem intersection_equation (x a : T) : intersection x a = intersectionValue x a := by
  unfold intersection
  rw [run_eq]
  exact intersectionBody_scope (by simp only [rank]; omega)

theorem bridge_equation (x v : T) : bridge x v = bridgeValue x v := by
  unfold bridge
  rw [run_eq]
  exact bridgeBody_scope (by simp only [rank]; omega)

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem smallValue_hasDecoder {a x v : T} (h : smallValue a (p x v) = true) :
    hasDecoderValue (p x v) = true := by
  cases v with
  | e => cases h
  | k t => cases h
  | p u last =>
    have hc := h
    simp only [smallValue,Bool.and_eq_true,decide_eq_true_eq] at h
    have he := h.1.1
    subst last
    simp only [hasDecoderValue,hc,Bool.true_or]

theorem bigValue_hasDecoder {a x v : T} (h : bigValue a (p x v) = true) :
    hasDecoderValue (p x v) = true := by
  cases a with
  | e => cases h
  | k t => cases h
  | p first s =>
    simp only [bigValue,Bool.and_eq_true] at h
    simp only [hasDecoderValue,h.1.2,h.2,Bool.and_self,Bool.or_true]

theorem decodeValue_hasDecoder {a b : T} (h : decodeValue a b = true) :
    hasDecoderValue b = true := by
  by_cases he : a = b
  · simp only [decodeValue,he,↓reduceIte,Bool.false_eq_true] at h
  · cases b with
    | e => simp only [decodeValue,he,↓reduceIte,Bool.false_eq_true] at h
    | k t => simp only [decodeValue,he,↓reduceIte,Bool.false_eq_true] at h
    | p x v =>
      by_cases hg : v = a ∨ protectedPair a (p x v) = true
      · simp only [decodeValue,he,hg,↓reduceIte,Bool.false_eq_true] at h
      · simp only [decodeValue,he,hg,↓reduceIte,Bool.or_eq_true] at h
        exact h.elim smallValue_hasDecoder bigValue_hasDecoder

theorem image_contains_product (a b : T) : image b (mul a b) = true := by
  rcases mul_cases a b with hp | ⟨_,hk⟩ | ⟨_,hc,hd⟩
  · have hr : rawValue a b = true := decide_eq_true hp
    rw [hp,image_equation]
    simp only [imageValue,decide_true,Bool.true_and,hr,Bool.or_true,Bool.true_or]
  · rw [hk]
    exact image_square b
  · have hcv : decodeValue a b = true :=
      (decode_scope (n:=rank (.mul a b)) (by simp only [rank]; omega)).symm.trans hc
    have hh := decodeValue_hasDecoder hcv
    cases b with
    | e => cases hh
    | k t => cases hh
    | p x v =>
      rw [hd,image_equation]
      simp only [imageValue,drop,decide_true,hh,Bool.and_self,Bool.or_true]

theorem image_shape {b out : T} (h : image b out = true) :
    out = k b ∨ (∃ a, out = p a b ∧ mul a b = out) ∨ (∃ v, b = p out v) := by
  rw [image_equation] at h
  simp only [imageValue,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with (hk | hp) | hd
  · exact Or.inl hk
  · cases out with
    | e => cases hp
    | k t => cases hp
    | p a second =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hp
      rcases hp with ⟨rfl,hr⟩
      exact Or.inr (Or.inl ⟨a,rfl,of_decide_eq_true hr⟩)
  · cases b with
    | e => cases hd
    | k t => cases hd
    | p x v =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hd
      rcases hd with ⟨rfl,_⟩
      exact Or.inr (Or.inr ⟨v,rfl⟩)

theorem image_small_output {b out : T} (h : image b out = true) (hs : sz out < sz b) :
    ∃ v, b = p out v := by
  rcases image_shape h with hk | ⟨a,hp,_⟩ | hd
  · rw [hk] at hs; simp only [sz] at hs; omega
  · rw [hp] at hs; simp only [sz] at hs; omega
  · exact hd

theorem image_self_false (b : T) : image b b = false := by
  cases h : image b b with
  | false => rfl
  | true =>
    rcases image_shape h with hk | ⟨a,hp,_⟩ | ⟨v,hd⟩
    · have := congrArg sz hk; simp only [sz] at this; omega
    · have := congrArg sz hp; simp only [sz] at this; omega
    · have := congrArg sz hd; simp only [sz] at this; omega

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfTail_self_false (t : T) : selfTail t t = false := by
  cases h : selfTail t t with
  | false => rfl
  | true => exact False.elim (selfTail_ne h rfl)

theorem selfTail_square_false (t : T) : selfTail t (k t) = false := by
  cases h : selfTail t (k t) with
  | false => rfl
  | true =>
    rcases selfTail_shape h with ⟨w,hv⟩ | ⟨s,ht⟩
    · cases hv
    · have := congrArg sz ht; simp only [sz] at this; omega

theorem selfTail_back_false {v t : T} (s : T) (hs : sz t ≤ sz v)
    (h : selfTail v t = true) : selfTail t (p s v) = false := by
  cases hb : selfTail t (p s v) with
  | false => rfl
  | true =>
    rcases selfTail_shape hb with ⟨w,hp⟩ | ⟨u,ht⟩
    · have he : v = t := by cases hp; rfl
      exact False.elim (selfTail_ne h he)
    · have := congrArg sz ht; simp only [sz] at this; omega

theorem image_pair_tail_false {s v : T} (hne : s ≠ v) : image (p s v) v = false := by
  cases h : image (p s v) v with
  | false => rfl
  | true =>
    rcases image_small_output h (by simp only [sz]; omega) with ⟨u,hp⟩
    have he : s = v := by cases hp; rfl
    exact False.elim (hne he)

theorem bridge_tail_equation (s v : T) : bridge (p s v) v =
    (imageValue (p s v) v || (match s with
      | p t u => selfTail v t && selfTail t u && hasDecoderValue (p s v)
      | _ => false)) := by
  rw [bridge_equation]
  cases v with
  | e =>
    simp only [bridgeValue,selfTail_self_false,Bool.false_and,Bool.or_false]
    cases s <;> rfl
  | k t =>
    simp only [bridgeValue,selfTail_self_false,Bool.false_and,Bool.or_false]
    cases s <;> rfl
  | p t u =>
    cases h : selfTail (p t u) t with
    | false =>
      simp only [bridgeValue,selfTail_self_false,h,Bool.false_and,Bool.or_false]
      cases s <;> rfl
    | true =>
      have hb := selfTail_back_false s (by simp only [sz]; omega) h
      simp only [bridgeValue,selfTail_self_false,h,hb,Bool.false_and,Bool.and_false,Bool.or_false]
      cases s <;> rfl

theorem bridge_square_pair_false (v : T) : bridge (p (k v) v) v = false := by
  rw [bridge_tail_equation,←image_equation]
  have hi : image (p (k v) v) v = false := image_pair_tail_false (by
    intro he; have := congrArg sz he; simp only [sz] at this; omega)
  simp only [hi,Bool.or_self]

theorem bridge_double_pair_false (v : T) : bridge (p (p (k v) v) v) v = false := by
  rw [bridge_tail_equation,←image_equation]
  have hi : image (p (p (k v) v) v) v = false := image_pair_tail_false (by
    intro he; have := congrArg sz he; simp only [sz] at this; omega)
  simp only [hi,selfTail_square_false,Bool.false_and,Bool.or_self]

theorem selfTail_canonical (v : T) : selfTail v (p (p (k v) v) v) = true := by
  rw [selfTail_equation]
  have hr : rawValue (k v) v = true := decide_eq_true (mul_square_right v)
  simp only [selfValue,and_self,decide_true,Bool.true_and,hr,image_square,Bool.and_self,Bool.true_or]

theorem bridge_canonical_not_protected {x v : T} (hb : bridge x v = true) :
    protectedPair (selfTree v) (p x v) = false := by
  cases hp : protectedPair (selfTree v) (p x v) with
  | false => rfl
  | true =>
    simp only [selfTree,protectedPair,Bool.or_eq_true,decide_eq_true_eq] at hp
    rcases hp with he | ⟨_,he⟩
    · have hx : x = p (k v) v := by cases he; rfl
      rw [hx,bridge_square_pair_false] at hb
      cases hb
    · rw [←he,bridge_double_pair_false] at hb
      cases hb

theorem bridge_decodes_canonical {x v : T} (hr : rawValue x v = true)
    (hb : bridge x v = true) : mul (selfTree v) (p x v) = x := by
  have hne : selfTree v ≠ p x v := by
    intro he
    have hv : p (p (k v) v) v = v := by cases he
    have := congrArg sz hv; simp only [sz] at this; omega
  have hv : v ≠ selfTree v := selfTree_ne v
  have hp := bridge_canonical_not_protected hb
  have hbig : bigValue (selfTree v) (p x v) = true := by
    simp only [bigValue,selfTree,decide_true,Bool.true_and,selfTail_canonical,hr,hb,Bool.and_self]
  have hd : decodeValue (selfTree v) (p x v) = true := by
    simp only [decodeValue,hne,↓reduceIte,hv,hp,Bool.false_eq_true,or_self,hbig,Bool.or_true]
  rw [mul_equation,if_neg hne,if_pos hd]
  rfl

theorem smallValue_decodes {a x u : T} (hc : smallValue a (p x (p u a)) = true) :
    mul a (p x (p u a)) = x := by
  have hne : a ≠ p x (p u a) := by
    intro he; have := congrArg sz he; simp only [sz] at this; omega
  have hv : p u a ≠ a := by
    intro he; have := congrArg sz he; simp only [sz] at this; omega
  have hp : protectedPair a (p x (p u a)) = false := by
    cases h : protectedPair a (p x (p u a)) with
    | false => rfl
    | true => have hs := protected_size h; simp only [sz] at hs; omega
  have hd : decodeValue a (p x (p u a)) = true := by
    simp only [decodeValue,hne,↓reduceIte,hv,hp,Bool.false_eq_true,or_self,hc,Bool.true_or]
  rw [mul_equation,if_neg hne,if_pos hd]
  rfl

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem hasDecoder_sound {b : T} (h : hasDecoderValue b = true) :
    ∃ a, mul a b = drop b := by
  cases b with
  | e => cases h
  | k t => cases h
  | p x v =>
    simp only [hasDecoderValue,Bool.or_eq_true] at h
    rcases h with hsmall | hbig
    · cases v with
      | e => cases hsmall
      | k t => cases hsmall
      | p u a => exact ⟨a,smallValue_decodes hsmall⟩
    · simp only [Bool.and_eq_true] at hbig
      exact ⟨selfTree v,bridge_decodes_canonical hbig.1 hbig.2⟩

theorem image_sound {b out : T} (h : image b out = true) : ∃ a, mul a b = out := by
  rw [image_equation] at h
  simp only [imageValue,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with (hk | hp) | hd
  · exact ⟨b,by rw [hk,mul_square]⟩
  · cases out with
    | e => cases hp
    | k t => cases hp
    | p a second =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hp
      rcases hp with ⟨rfl,hr⟩
      exact ⟨a,of_decide_eq_true hr⟩
  · cases b with
    | e => cases hd
    | k t => cases hd
    | p x v =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hd
      rcases hd with ⟨rfl,hh⟩
      exact hasDecoder_sound hh

theorem image_spec (b out : T) : image b out = true ↔ ∃ a, mul a b = out := by
  constructor
  · exact image_sound
  · rintro ⟨a,rfl⟩
    exact image_contains_product a b

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem image_implies_bridge {x v : T} (h : image x v = true) : bridge x v = true := by
  rw [bridge_equation]
  unfold bridgeValue
  rw [←image_equation,h]
  simp only [Bool.true_or]

theorem decodeValue_raw_false {a b : T} (h : rawValue a b = true) : decodeValue a b = false := by
  have hm : mul a b = p a b := of_decide_eq_true h
  by_cases he : a = b
  · subst a
    rw [mul_square] at hm
    cases hm
  · cases hd : decodeValue a b with
    | false => rfl
    | true =>
      rw [mul_equation,if_neg he,if_pos hd] at hm
      have hs := drop_size_le b
      rw [hm] at hs
      simp only [sz] at hs; omega

theorem intersection_self_raw_false (t : T) (h : rawValue (drop t) t = true) :
    intersection t t = false := by
  rw [intersection_equation]
  cases t with
  | e => rfl
  | k s => rfl
  | p u s =>
    have h1 : decodeValue (k (p u s)) (p u s) = false :=
      decodeValue_raw_false (decide_eq_true (mul_square_right (p u s)))
    have h2 : decodeValue u (p u s) = false := decodeValue_raw_false h
    simp only [intersectionValue,h1,h2,ne_eq,not_true_eq_false,false_and,and_false,
      decide_false,Bool.and_false,Bool.false_and,Bool.false_or,Bool.or_false]
    cases s with
    | e => rfl
    | k v => rfl
    | p v w =>
      cases w with
      | e => rfl
      | k z => rfl
      | p z second =>
        have hn : second ≠ p u (p v (p z second)) := by
          intro he; have := congrArg sz he; simp only [sz] at this; omega
        simp only [hn,decide_false,Bool.false_and]

theorem selfTail_sound (t v : T) (h : selfTail t v = true) : mul t (p t v) = t := by
  have h0 := h
  rw [selfTail_equation] at h
  simp only [selfValue,Bool.or_eq_true] at h
  rcases h with h | h
  · cases v with
    | e => cases h
    | k u => cases h
    | p u last =>
      cases u with
      | e => cases h
      | k w => cases h
      | p w second =>
        simp only [Bool.and_eq_true,decide_eq_true_eq] at h
        rcases h with ⟨⟨⟨hs,hl⟩,hr⟩,hi⟩
        subst second
        subst last
        have hr0 : rawValue t (p (p w t) t) = true :=
          decide_eq_true (mul_right_child (p w t) t)
        apply smallValue_decodes
        simp only [smallValue,decide_true,Bool.true_and,hr0,hr,hi,Bool.and_self,Bool.true_or]
  · cases ht : t with
    | e => simp only [ht] at h; cases h
    | k u => simp only [ht] at h; cases h
    | p first s =>
      simp only [ht] at h h0 ⊢
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h
      rcases h with ⟨he,hh⟩
      subst first
      have himage : image (p v s) v = true :=
        (image_spec (p v s) v).mpr ⟨v,selfTail_sound v s hh⟩
      have hb := image_implies_bridge himage
      have hr := selfTail_raw_value h0
      have hne : p v s ≠ p (p v s) v := by
        intro he; have := congrArg sz he; simp only [sz] at this; omega
      have hv : v ≠ p v s := by
        intro he; have := congrArg sz he; simp only [sz] at this; omega
      have hp : protectedPair (p v s) (p (p v s) v) = false := by
        cases he : protectedPair (p v s) (p (p v s) v) with
        | false => rfl
        | true => have hs := protected_size he; simp only [sz] at hs; omega
      have hbig : bigValue (p v s) (p (p v s) v) = true := by
        simp only [bigValue,decide_true,Bool.true_and,hh,hr,hb,Bool.and_self]
      have hd : decodeValue (p v s) (p (p v s) v) = true := by
        simp only [decodeValue,hne,↓reduceIte,hv,hp,Bool.false_eq_true,or_self,hbig,Bool.or_true]
      rw [mul_equation,if_neg hne,if_pos hd]
      rfl
termination_by sz t + sz v
decreasing_by simp_wf; simp_all only [sz]; omega

theorem selfTail_complete {t v : T} (hm : mul t (p t v) = t) : selfTail t v = true := by
  have hc : decodeValue t (p t v) = true := by
    rcases mul_cases t (p t v) with hp | ⟨he,_⟩ | ⟨_,hd,_⟩
    · rw [hm] at hp
      have := congrArg sz hp; simp only [sz] at this; omega
    · have := congrArg sz he; simp only [sz] at this; omega
    · exact (decode_scope (n:=rank (.mul t (p t v))) (by simp only [rank]; omega)).symm.trans hd
  have hne : t ≠ p t v := by
    intro he; have := congrArg sz he; simp only [sz] at this; omega
  by_cases hg : v = t ∨ protectedPair t (p t v) = true
  · simp only [decodeValue,hne,hg,↓reduceIte,Bool.false_eq_true] at hc
  · simp only [decodeValue,hne,hg,↓reduceIte,Bool.or_eq_true] at hc
    rcases hc with hs | hb
    · cases v with
      | e => cases hs
      | k u => cases hs
      | p u last =>
        simp only [smallValue,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true] at hs
        rcases hs with ⟨⟨hl,_⟩,hb⟩
        subst last
        rcases hb with (hrr | hsq) | hdec
        · cases u with
          | e => cases hrr
          | k w => cases hrr
          | p w second =>
            simp only [Bool.and_eq_true,decide_eq_true_eq] at hrr
            rcases hrr with ⟨⟨he,hr⟩,hi⟩
            subst second
            rw [selfTail_equation]
            simp only [selfValue,and_self,decide_true,Bool.true_and,hr,hi,Bool.and_self,Bool.true_or]
        · simp only [image_self_false,Bool.and_eq_true,Bool.false_eq_true,and_false] at hsq
        · rcases hdec with ⟨⟨he,hr⟩,hj⟩
          rw [he] at hr
          rw [intersection_self_raw_false t hr] at hj
          cases hj
    · cases t with
      | e => cases hb
      | k u => cases hb
      | p first s =>
        simp only [bigValue,Bool.and_eq_true,decide_eq_true_eq] at hb
        have he := hb.1.1.1
        have hh := hb.1.1.2
        subst first
        rw [selfTail_equation]
        simp only [selfValue,decide_true,hh,Bool.and_self,Bool.or_true]

theorem selfTail_spec (t v : T) : selfTail t v = true ↔ mul t (p t v) = t :=
  ⟨selfTail_sound t v,selfTail_complete⟩

theorem image_reverse_raw {x v : T} (h : image x v = true) : mul x v = p x v := by
  rcases image_shape h with hk | ⟨a,hp,_⟩ | ⟨s,hx⟩
  · rw [hk]
    have hn : x ≠ k x := by
      intro he; have := congrArg sz he; simp only [sz] at this; omega
    exact mul_false_decode hn (by simp only [decode,hn,↓reduceIte])
  · rw [hp]
    exact mul_right_child a x
  · rw [hx]
    apply mul_drop_large
    · intro he; have := congrArg sz he; simp only [sz] at this; omega
    · simp only [drop]; omega

theorem canonical_decoder_from_image {x v : T} (h : image x v = true) :
    mul (selfTree v) (mul x v) = x := by
  have hr := image_reverse_raw h
  rw [hr]
  exact bridge_decodes_canonical (decide_eq_true hr) (image_implies_bridge h)

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem decodeValue_parts {a u t : T} (h : decodeValue a (p u t) = true) :
    a ≠ p u t ∧ t ≠ a ∧ protectedPair a (p u t) = false ∧
      (smallValue a (p u t) = true ∨ bigValue a (p u t) = true) := by
  by_cases he : a = p u t
  · simp only [decodeValue,he,↓reduceIte,Bool.false_eq_true] at h
  · by_cases hg : t = a ∨ protectedPair a (p u t) = true
    · simp only [decodeValue,he,hg,↓reduceIte,Bool.false_eq_true] at h
    · have ht : t ≠ a := fun ht => hg (Or.inl ht)
      have hp : protectedPair a (p u t) = false := by
        cases hp : protectedPair a (p u t) with
        | false => rfl
        | true => exact False.elim (hg (Or.inr hp))
      simp only [decodeValue,he,hg,↓reduceIte,Bool.or_eq_true] at h
      exact ⟨he,ht,hp,h⟩

theorem decodeValue_pair_spec (a u t : T) :
    decodeValue a (p u t) = true ↔ mul a (p u t) = u := by
  constructor
  · intro hd
    have hn := (decodeValue_parts hd).1
    rw [mul_equation,if_neg hn,if_pos hd]
    rfl
  · intro hm
    rcases mul_cases a (p u t) with hr | ⟨_,hk⟩ | ⟨_,hd,_⟩
    · rw [hm] at hr
      have := congrArg sz hr; simp only [sz] at this; omega
    · rw [hm] at hk
      have := congrArg sz hk; simp only [sz] at this; omega
    · exact (decode_scope (n:=rank (.mul a (p u t))) (by simp only [rank]; omega)).symm.trans hd

theorem smallValue_tail {a u t : T} (h : smallValue a (p u t) = true) : ∃ r, t = p r a := by
  cases t with
  | e => cases h
  | k v => cases h
  | p r last =>
    simp only [smallValue,Bool.and_eq_true,decide_eq_true_eq] at h
    have he := h.1.1
    exact ⟨r,by rw [he]⟩

theorem bigValue_tail_false {a u t : T} (hs : sz a ≤ sz t) : bigValue a (p u t) = false := by
  cases a with
  | e => rfl
  | k v => rfl
  | p first s =>
    have hn : first ≠ t := by
      intro he
      rw [he] at hs
      simp only [sz] at hs; omega
    simp only [bigValue,hn,decide_false,Bool.false_and]

theorem smallValue_pair_spec (a x u : T) :
    smallValue a (p x (p u a)) = true ↔ mul a (p x (p u a)) = x := by
  constructor
  · exact smallValue_decodes
  · intro hm
    have hd := (decodeValue_pair_spec a x (p u a)).mpr hm
    rcases (decodeValue_parts hd).2.2.2 with hs | hb
    · exact hs
    · rw [bigValue_tail_false (by simp only [sz]; omega)] at hb
      cases hb

theorem bigValue_decodes {a u t : T} (hne : a ≠ p u t) (ht : t ≠ a)
    (hp : protectedPair a (p u t) = false) (hb : bigValue a (p u t) = true) :
    mul a (p u t) = u := by
  apply (decodeValue_pair_spec a u t).mp
  simp only [decodeValue,hne,↓reduceIte,ht,hp,Bool.false_eq_true,or_self,hb,Bool.or_true]

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem intersection_sound {x u t : T} (h : intersection x (p u t) = true) :
    ∃ z, mul (mul z x) (p u t) = u := by
  rw [intersection_equation] at h
  simp only [intersectionValue,Bool.or_eq_true] at h
  rcases h with ((hsq | hdrop) | hsmall) | hbig
  · refine ⟨x,?_⟩
    rw [mul_square]
    exact (decodeValue_pair_spec (k x) u t).mp hsq
  · cases x with
    | e => cases hdrop
    | k v => cases hdrop
    | p w s =>
      simp only [Bool.and_eq_true] at hdrop
      rcases hasDecoder_sound hdrop.2 with ⟨z,hz⟩
      refine ⟨z,?_⟩
      rw [hz]
      exact (decodeValue_pair_spec w u t).mp hdrop.1
  · cases t with
    | e => cases hsmall
    | k v => cases hsmall
    | p r w =>
      cases w with
      | e => cases hsmall
      | k v => cases hsmall
      | p z second =>
        simp only [Bool.and_eq_true,decide_eq_true_eq] at hsmall
        rcases hsmall with ⟨⟨he,hr⟩,hc⟩
        subst second
        refine ⟨z,?_⟩
        rw [of_decide_eq_true hr]
        exact smallValue_decodes hc
  · simp only [Bool.and_eq_true,decide_eq_true_eq] at hbig
    rcases hbig with ⟨⟨⟨⟨hr,hself⟩,hu⟩,hb⟩,hne,hxa,hxu⟩
    refine ⟨t,?_⟩
    rw [of_decide_eq_true hr]
    apply bigValue_decodes hne
    · intro he
      have := congrArg sz he; simp only [sz] at this; omega
    · simp only [protectedPair,hxa,hxu,decide_false,and_false,Bool.or_self]
    · simp only [bigValue,decide_true,Bool.true_and,hself,hu,hb,Bool.and_self]

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem intersection_complete {x u t z : T} (hm : mul (mul z x) (p u t) = u) :
    intersection x (p u t) = true := by
  rcases mul_cases z x with hr | ⟨_,hk⟩ | ⟨_,hc,hd⟩
  · rw [hr] at hm
    have hc := (decodeValue_pair_spec (p z x) u t).mpr hm
    rcases decodeValue_parts hc with ⟨hne,ht,hp,hs | hb⟩
    · rcases smallValue_tail hs with ⟨r,he⟩
      subst t
      have hraw : rawValue z x = true := decide_eq_true hr
      rw [intersection_equation]
      simp only [intersectionValue,decide_true,Bool.true_and,hraw,hs,
        Bool.and_self,Bool.or_true,Bool.true_or]
    · simp only [bigValue,Bool.and_eq_true,decide_eq_true_eq] at hb
      rcases hb with ⟨⟨⟨he,hself⟩,hu⟩,hb⟩
      subst z
      have hxa : x ≠ p u t := by
        intro he
        have hh : protectedPair (p t x) (p u t) = true := by
          simp only [protectedPair,he,decide_true,Bool.true_or]
        rw [hp] at hh
        cases hh
      have hxu : x ≠ u := by
        intro he
        have hh : protectedPair (p t x) (p u t) = true := by
          simp only [protectedPair,he,and_self,decide_true,Bool.or_true]
        rw [hp] at hh
        cases hh
      have hguard : decide (p t x ≠ p u t ∧ x ≠ p u t ∧ x ≠ u) = true :=
        decide_eq_true ⟨hne,hxa,hxu⟩
      have hraw : rawValue t x = true := decide_eq_true hr
      rw [intersection_equation]
      simp only [intersectionValue,hraw,hself,hu,hb,hguard,Bool.and_self,Bool.or_true]
  · rw [hk] at hm
    have hc := (decodeValue_pair_spec (k x) u t).mpr hm
    rw [intersection_equation]
    simp only [intersectionValue,hc,Bool.true_or]
  · have hcv : decodeValue z x = true :=
      (decode_scope (n:=rank (.mul z x)) (by simp only [rank]; omega)).symm.trans hc
    have hh := decodeValue_hasDecoder hcv
    cases x with
    | e => cases hh
    | k v => cases hh
    | p w s =>
      rw [hd] at hm
      change mul w (p u t) = u at hm
      have hc := (decodeValue_pair_spec w u t).mpr hm
      rw [intersection_equation]
      simp only [intersectionValue,hc,hh,Bool.and_self,Bool.or_true,Bool.true_or]

theorem intersection_pair_spec (x u t : T) :
    intersection x (p u t) = true ↔ ∃ z, mul (mul z x) (p u t) = u := by
  constructor
  · exact intersection_sound
  · rintro ⟨z,hz⟩
    exact intersection_complete hz

theorem intersection_spec (x a : T) : intersection x a = true ↔
    (∃ u t, a = p u t) ∧ ∃ z, mul (mul z x) a = drop a := by
  cases a with
  | e =>
    rw [intersection_equation]
    simp only [intersectionValue,Bool.false_eq_true,reduceCtorEq,exists_false,false_and]
  | k v =>
    rw [intersection_equation]
    simp only [intersectionValue,Bool.false_eq_true,reduceCtorEq,exists_false,false_and]
  | p u t =>
    rw [intersection_pair_spec]
    constructor
    · intro h
      exact ⟨⟨u,t,rfl⟩,h⟩
    · rintro ⟨_,h⟩
      exact h

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem image_lower_bound {x w : T} (h : image x w = true) : sz (drop x) ≤ sz w := by
  have hd := drop_size_le x
  rcases image_shape h with hk | ⟨z,hr,_⟩ | ⟨s,hx⟩
  · rw [hk]; simp only [sz]; omega
  · rw [hr]; simp only [sz]; omega
  · rw [hx]; simp only [drop]; omega

theorem selfTail_pair_tail_false (w z : T) : selfTail (p w z) z = false := by
  cases h : selfTail (p w z) z with
  | false => rfl
  | true =>
    rw [selfTail_equation] at h
    simp only [selfValue,selfTail_self_false,Bool.and_false,Bool.or_false] at h
    cases z with
    | e => cases h
    | k s => cases h
    | p a b =>
      cases a with
      | e => cases h
      | k s => cases h
      | p q second =>
        simp only [Bool.and_eq_true,decide_eq_true_eq] at h
        have he := h.1.1.2
        have := congrArg sz he; simp only [sz] at this; omega

theorem selfTail_incoming_large {s u z : T} (hs : selfTail s u = true)
    (hz : selfTail z (p s u) = true) : sz (p s u) < sz z := by
  rcases selfTail_shape hz with ⟨w,he⟩ | ⟨a,hz⟩
  · have hu : u = z := by cases he; rfl
    have hs' : s = p w z := by cases he; rfl
    rw [hu,hs',selfTail_pair_tail_false] at hs
    cases hs
  · rw [hz]; simp only [sz]; omega

theorem selfTail_reverse {s u : T} (h : selfTail (p s u) s = true) : selfTail s u = true := by
  rw [selfTail_equation] at h
  simp only [selfValue,decide_true,Bool.true_and,Bool.or_eq_true] at h
  rcases h with hsmall | h
  · cases s with
    | e => cases hsmall
    | k t => cases hsmall
    | p a b =>
      cases a with
      | e => cases hsmall
      | k t => cases hsmall
      | p w second =>
        simp only [Bool.and_eq_true,decide_eq_true_eq] at hsmall
        have he := hsmall.1.1.2
        have := congrArg sz he; simp only [sz] at this; omega
  · exact h

theorem selfColumn_child_raw (r a u w : T) (hs : selfTail (p r a) u = true)
    (hi : image (p (p r a) u) w = true) : mul w a = p w a := by
  rcases image_shape hi with hk | ⟨z,hr,_⟩ | ⟨s,hx⟩
  · rw [hk]
    apply mul_drop_large
    · intro he; have := congrArg sz he; simp only [sz] at this; omega
    · simp only [drop,sz]; omega
  · rw [hr]
    rcases mul_cases (p z (p (p r a) u)) a with hraw | ⟨he,_⟩ | ⟨_,hc,_⟩
    · exact hraw
    · have := congrArg sz he; simp only [sz] at this; omega
    · have ha := decode_admissible hc
      have hcv : decodeValue (p z (p (p r a) u)) a = true :=
        (decode_scope (n:=rank (.mul (p z (p (p r a) u)) a)) (by simp only [rank]; omega)).symm.trans hc
      cases a with
      | e => cases ha
      | k v => cases ha
      | p b t =>
        rcases (decodeValue_parts hcv).2.2.2 with hsmall | hbig
        · rcases smallValue_tail hsmall with ⟨v,he⟩
          have := congrArg sz he; simp only [sz] at this; omega
        · simp only [bigValue,Bool.and_eq_true,decide_eq_true_eq] at hbig
          have hz := hbig.1.1.1
          have hself := hbig.1.1.2
          have hlarge := selfTail_incoming_large hs hself
          simp only [sz] at hlarge; omega
  · have hw : w = p r a := by cases hx; rfl
    rw [hw]
    exact mul_pair_right r a

theorem intersection_self_child_false (r a u : T) (hs : selfTail (p r a) u = true) :
    intersection (p (p r a) u) a = false := by
  cases h : intersection (p (p r a) u) a with
  | false => rfl
  | true =>
    rcases (intersection_spec _ _).mp h with ⟨_,⟨z,hz⟩⟩
    have hi := image_contains_product z (p (p r a) u)
    have hr := selfColumn_child_raw r a u _ hs hi
    rw [hr] at hz
    have hl := drop_size_le a
    have he := congrArg sz hz
    simp only [sz] at he; omega

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfColumn_small_key {t s a : T} (hs : selfTail t s = true)
    (hc : smallValue a (p t s) = true) : a = t := by
  rcases smallValue_tail hc with ⟨r,he⟩
  subst s
  rcases selfTail_shape hs with ⟨w,he⟩ | ⟨u,ht⟩
  · exact T.p.inj he |>.2
  · subst t
    have hs' := selfTail_reverse hs
    simp only [smallValue,decide_true,Bool.true_and,Bool.and_eq_true,Bool.or_eq_true] at hc
    rcases hc.2 with (hraw | hk) | hd
    · cases r with
      | e => cases hraw
      | k q => cases hraw
      | p w second =>
        simp only [Bool.and_eq_true,decide_eq_true_eq] at hraw
        have hl := image_lower_bound hraw.2
        simp only [drop,sz] at hl
        omega
    · simp only [Bool.and_eq_true,decide_eq_true_eq] at hk
      have hl := image_lower_bound hk.2
      simp only [drop,sz] at hl
      omega
    · rw [intersection_self_child_false r a u hs'] at hd
      cases hd.2

theorem selfTail_chain_shape {v s x : T} (hvs : selfTail v s = true)
    (hsx : selfTail s x = true) : (∃ w, x = p w s) ∨ (∃ u, v = p s u) := by
  rcases selfTail_shape hsx with ⟨w,hx⟩ | ⟨u,hs⟩
  · exact Or.inl ⟨p w s,hx⟩
  · rcases selfTail_shape hvs with ⟨w,hs'⟩ | hv
    · have hu : u = v := by rw [hs] at hs'; exact T.p.inj hs' |>.2
      have hx : x = p w v := by rw [hs] at hs'; exact T.p.inj hs' |>.1
      rw [hs] at hsx
      have hr := selfTail_reverse hsx
      rw [hu,hx,selfTail_pair_tail_false] at hr
      cases hr
    · exact Or.inr hv

theorem selfTail_chain_bridge {v s x : T} (hvs : selfTail v s = true)
    (hsx : selfTail s x = true) : bridge x v = true := by
  have hr := selfTail_raw_value hsx
  rw [bridge_equation]
  rcases selfTail_chain_shape hvs hsx with ⟨w,hx⟩ | ⟨u,hv⟩
  · subst x
    simp only [bridgeValue,hvs,hsx,hr,Bool.and_self,Bool.or_true,Bool.true_or]
  · subst v
    simp only [bridgeValue,hvs,hsx,hr,Bool.and_self,Bool.or_true,Bool.true_or]

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfColumn_decode_bridge {x v s w : T} (hs : selfTail v s = true)
    (hi : image x w = true) (hm : mul w (p v s) = v) : bridge x v = true := by
  have hc := (decodeValue_pair_spec w v s).mpr hm
  rcases (decodeValue_parts hc).2.2.2 with hsmall | hbig
  · have hw := selfColumn_small_key hs hsmall
    subst w
    exact image_implies_bridge hi
  · cases w with
    | e => cases hbig
    | k a => cases hbig
    | p first a =>
      simp only [bigValue,Bool.and_eq_true,decide_eq_true_eq] at hbig
      have he := hbig.1.1.1
      subst first
      have hsa := hbig.1.1.2
      rcases image_shape hi with hk | ⟨z,hr,_⟩ | ⟨b,hx⟩
      · cases hk
      · have ha := T.p.inj hr |>.2
        subst a
        exact selfTail_chain_bridge hs hsa
      · subst x
        have hh : hasDecoderValue (p (p s a) b) = true := by
          rw [image_equation] at hi
          simp only [imageValue,T.noConfusion,decide_false,decide_true,Bool.false_or,
            Bool.true_and,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at hi
          rcases hi with (he | ⟨he,_⟩) | hd
          · cases he
          · have hh := congrArg sz he; simp only [sz] at hh; omega
          · exact hd
        rw [bridge_equation]
        simp only [bridgeValue,hs,hsa,hh,Bool.and_self,Bool.or_true]

theorem selfColumn_bridge {x v s : T} (hs : selfTail v s = true)
    (hi : intersection x (p v s) = true) : bridge x v = true := by
  rcases intersection_sound hi with ⟨z,hz⟩
  exact selfColumn_decode_bridge hs (image_contains_product z x) hz

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfTail_head_false (t u : T) : selfTail t (p t u) = false := by
  cases h : selfTail t (p t u) with
  | false => rfl
  | true =>
    rcases selfTail_shape h with ⟨w,he⟩ | ⟨s,he⟩
    · have hh := congrArg sz (T.p.inj he).1
      simp only [sz] at hh; omega
    · have hh := congrArg sz he
      simp only [sz] at hh; omega

theorem selfTail_nested_false {t u a : T} (hu : selfTail t u = true)
    (ha : selfTail u a = true) : selfTail t (p u a) = false := by
  cases h : selfTail t (p u a) with
  | false => rfl
  | true =>
    have hl := selfTail_incoming_large ha h
    rcases selfTail_shape hu with ⟨w,he⟩ | ⟨s,ht⟩
    · rw [he] at hl; simp only [sz] at hl; omega
    · rcases selfTail_shape h with ⟨w,he⟩ | ⟨b,ht'⟩
      · have hh := congrArg sz he; simp only [sz] at hh hl; omega
      · rw [ht] at ht'
        have hh := congrArg sz (T.p.inj ht').1
        simp only [sz] at hh; omega

theorem selfTail_siblings_raw {t u x : T} (hu : selfTail t u = true)
    (hx : selfTail t x = true) : mul x (p t u) = p x (p t u) := by
  rcases mul_cases x (p t u) with hr | ⟨he,_⟩ | ⟨_,hd,_⟩
  · exact hr
  · rw [he,selfTail_head_false] at hx; cases hx
  · have hcv : decodeValue x (p t u) = true :=
      (decode_scope (n:=rank (.mul x (p t u))) (by simp only [rank]; omega)).symm.trans hd
    rcases (decodeValue_parts hcv).2.2.2 with hsmall | hbig
    · have he := selfColumn_small_key hu hsmall
      rw [he,selfTail_self_false] at hx; cases hx
    · cases x with
      | e => cases hbig
      | k a => cases hbig
      | p first a =>
        simp only [bigValue,Bool.and_eq_true,decide_eq_true_eq] at hbig
        have he := hbig.1.1.1
        subst first
        rw [selfTail_nested_false hu hbig.1.1.2] at hx
        cases hx

theorem selfTail_chain_raw {v s x : T} (hvs : selfTail v s = true)
    (hsx : selfTail s x = true) : mul x v = p x v := by
  rcases selfTail_shape hvs with ⟨w,hs⟩ | ⟨u,hv⟩
  · rcases selfTail_shape hsx with ⟨z,hx⟩ | ⟨a,hs'⟩
    · rw [hx,hs]
      apply mul_drop_large
      · intro he; have hh := congrArg sz he; simp only [sz] at hh; omega
      · simp only [drop,sz]; omega
    · have hx : x = p w v := by rw [hs] at hs'; exact (T.p.inj hs').1.symm
      have ha : a = v := by rw [hs] at hs'; exact (T.p.inj hs').2.symm
      rw [hs'] at hsx
      have hh := selfTail_reverse hsx
      rw [hx,ha,selfTail_pair_tail_false] at hh; cases hh
  · rw [hv] at hvs ⊢
    exact selfTail_siblings_raw (selfTail_reverse hvs) hsx

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfTail_double_head_raw {v t s : T} (ht : selfTail v t = true)
    (hs : selfTail t s = true) (a : T) : mul (p (p t s) a) v = p (p (p t s) a) v := by
  rcases selfTail_shape ht with ⟨w,he⟩ | ⟨u,hv⟩
  · rw [he]
    apply mul_drop_large
    · intro hh; have hh' := congrArg sz hh; simp only [sz] at hh'; omega
    · simp only [drop,sz]; omega
  · rw [hv] at ht ⊢
    have hu := selfTail_reverse ht
    rcases mul_cases (p (p t s) a) (p t u) with hr | ⟨he,_⟩ | ⟨_,hd,_⟩
    · exact hr
    · have hh := congrArg sz (T.p.inj he).1; simp only [sz] at hh; omega
    · have hcv : decodeValue (p (p t s) a) (p t u) = true :=
        (decode_scope (n:=rank (.mul (p (p t s) a) (p t u)))
          (by simp only [rank]; omega)).symm.trans hd
      rcases (decodeValue_parts hcv).2.2.2 with hsmall | hbig
      · have he := selfColumn_small_key hu hsmall
        have hh := congrArg sz he; simp only [sz] at hh; omega
      · simp only [bigValue,Bool.and_eq_true,decide_eq_true_eq] at hbig
        have he := hbig.1.1.1
        rw [←he,selfTail_head_false] at hu
        cases hu

theorem bridge_reverse_raw {x v : T} (hb : bridge x v = true) : mul x v = p x v := by
  rw [bridge_equation] at hb
  simp only [bridgeValue,Bool.or_eq_true] at hb
  rcases hb with ((hi | hr) | hl) | hd
  · exact image_reverse_raw ((image_equation x v).trans hi)
  · cases x with
    | e => cases hr
    | k a => cases hr
    | p a t =>
      simp only [Bool.and_eq_true] at hr
      exact selfTail_chain_raw hr.1.1 hr.1.2
  · cases v with
    | e => cases hl
    | k a => cases hl
    | p t a =>
      simp only [Bool.and_eq_true] at hl
      exact selfTail_chain_raw hl.1.1 hl.1.2
  · cases x with
    | e => cases hd
    | k a => cases hd
    | p b a =>
      cases b with
      | e => cases hd
      | k t => cases hd
      | p t s =>
        simp only [Bool.and_eq_true] at hd
        exact selfTail_double_head_raw hd.1.1 hd.1.2 a

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfTail_cycle_false {v t : T} (h : selfTail v t = true) : selfTail t v = false := by
  cases hh : selfTail t v with
  | false => rfl
  | true =>
    have hr := selfTail_chain_raw h hh
    rw [mul_square] at hr; cases hr

theorem selfTail_chain_skip_false {v t x : T} (ht : selfTail v t = true)
    (hx : selfTail t x = true) : selfTail v x = false := by
  cases hh : selfTail v x with
  | false => rfl
  | true =>
    rcases selfTail_shape ht with ⟨w,he⟩ | ⟨u,hv⟩
    · rcases selfTail_shape hx with ⟨z,hx'⟩ | ⟨a,ht'⟩
      · rcases selfTail_shape hh with ⟨b,hx''⟩ | ⟨b,hv'⟩
        · rw [hx'] at hx''
          have htv := (T.p.inj hx'').2
          rw [htv,selfTail_self_false] at ht; cases ht
        · rw [hx',he] at hv'
          have hsize := congrArg sz hv'; simp only [sz] at hsize; omega
      · have hx' : x = p w v := by rw [he] at ht'; exact (T.p.inj ht').1.symm
        have ha : a = v := by rw [he] at ht'; exact (T.p.inj ht').2.symm
        rw [ht'] at hx
        have hr := selfTail_reverse hx
        rw [hx',ha,selfTail_pair_tail_false] at hr; cases hr
    · rcases selfTail_shape hh with ⟨b,hx'⟩ | ⟨s,hv'⟩
      · rcases selfTail_shape hx with ⟨z,hx''⟩ | ⟨a,ht'⟩
        · rw [hx'] at hx''
          have he := (T.p.inj hx'').2
          rw [he,selfTail_self_false] at ht; cases ht
        · rw [hx',hv] at ht'
          have hsize := congrArg sz ht'; simp only [sz] at hsize; omega
      · rw [hv] at hv'
        have he := (T.p.inj hv').1
        rw [←he,selfTail_self_false] at hx; cases hx

theorem selfTail_double_head_tail_false (t u b : T) : selfTail (p (p t u) b) t = false := by
  cases h : selfTail (p (p t u) b) t with
  | false => rfl
  | true =>
    rcases selfTail_shape h with ⟨w,he⟩ | ⟨s,he⟩
    · have hh := congrArg sz he; simp only [sz] at hh; omega
    · have hh := congrArg sz (T.p.inj he).1; simp only [sz] at hh; omega

theorem selfTail_image_reverse_false {v x : T} (hx : selfTail v x = true) : image x v = false := by
  cases hi : image x v with
  | false => rfl
  | true =>
    have hl := image_lower_bound hi
    rcases selfTail_shape hx with ⟨w,he⟩ | ⟨t,hv⟩
    · rw [he] at hl; simp only [drop,sz] at hl; omega
    · rw [hv] at hi
      rcases image_shape hi with hk | ⟨a,hp,hr⟩ | ⟨b,he⟩
      · cases hk
      · have he := (T.p.inj hp).1
        have ht := (T.p.inj hp).2
        rw [←he,mul_square] at hr
        cases hr
      · have hh := congrArg sz he; simp only [sz] at hh; omega

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem bridge_selfTail_false {v x : T} (hs : selfTail v x = true) : bridge x v = false := by
  cases hb : bridge x v with
  | false => rfl
  | true =>
    rw [bridge_equation] at hb
    simp only [bridgeValue,Bool.or_eq_true] at hb
    rcases hb with ((hi | hr) | hl) | hd
    · rw [←image_equation,selfTail_image_reverse_false hs] at hi; cases hi
    · cases x with
      | e => cases hr
      | k a => cases hr
      | p a t =>
        simp only [Bool.and_eq_true] at hr
        rw [selfTail_chain_skip_false hr.1.1 hr.1.2] at hs; cases hs
    · cases v with
      | e => cases hl
      | k a => cases hl
      | p t a =>
        simp only [Bool.and_eq_true] at hl
        rw [selfTail_chain_skip_false hl.1.1 hl.1.2] at hs; cases hs
    · cases x with
      | e => cases hd
      | k a => cases hd
      | p b a =>
        cases b with
        | e => cases hd
        | k t => cases hd
        | p t s =>
          simp only [Bool.and_eq_true] at hd
          have hvt := hd.1.1
          have hts := hd.1.2
          rcases selfTail_shape hs with ⟨w,he⟩ | ⟨u,hv⟩
          · have hts' := (T.p.inj (T.p.inj he).1).2
            rw [hts',selfTail_cycle_false hvt] at hts; cases hts
          · rw [hv] at hvt
            rcases selfTail_shape hvt with ⟨w,he⟩ | ⟨b,he⟩
            · have hh := congrArg sz he; simp only [sz] at hh; omega
            · have hh := congrArg sz (T.p.inj he).1; simp only [sz] at hh; omega

theorem bridge_image_frame_false {w v : T} (hi : image v w = true) : bridge (p w v) v = false := by
  have hn : w ≠ v := by intro he; rw [he,image_self_false] at hi; cases hi
  rw [bridge_tail_equation,←image_equation,image_pair_tail_false hn,Bool.false_or]
  cases w with
  | e => rfl
  | k a => rfl
  | p t u =>
    cases hh : selfTail v t && selfTail t u && hasDecoderValue (p (p t u) v) with
    | false => exact hh
    | true =>
      simp only [Bool.and_eq_true] at hh
      rcases image_shape hi with hk | ⟨a,he,_⟩ | ⟨b,hv⟩
      · cases hk
      · have hu := (T.p.inj he).2
        have htv := hh.1.2
        rw [hu,selfTail_cycle_false hh.1.1] at htv; cases htv
      · have hvt := hh.1.1
        rw [hv,selfTail_double_head_tail_false] at hvt; cases hvt

theorem selfTail_small_shape {v x : T} (hs : selfTail v (p x v) = true) :
    ∃ w, x = p w v ∧ image v w = true := by
  rw [selfTail_equation] at hs
  simp only [selfValue,Bool.or_eq_true] at hs
  rcases hs with hr | hl
  · cases x with
    | e => cases hr
    | k a => cases hr
    | p w second =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hr
      have he := hr.1.1.1
      subst second
      exact ⟨w,rfl,hr.2⟩
  · cases v with
    | e => cases hl
    | k a => cases hl
    | p first s =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hl
      have hh := congrArg sz hl.1; simp only [sz] at hh; omega

theorem bridge_self_key_protected_false {x v s : T} (hs : selfTail v s = true)
    (hb : bridge x v = true) : protectedPair (p v s) (p x v) = false := by
  have h1 : s ≠ p x v := by
    intro he
    rw [he] at hs
    rcases selfTail_small_shape hs with ⟨w,hx,hi⟩
    rw [hx,bridge_image_frame_false hi] at hb; cases hb
  have h2 : s ≠ x := by
    intro he
    rw [he] at hs
    rw [bridge_selfTail_false hs] at hb; cases hb
  simp only [protectedPair,h1,h2,and_false,decide_false,Bool.or_self]

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem bridge_decodes_self {x v s : T} (hs : selfTail v s = true)
    (hb : bridge x v = true) : mul (p v s) (mul x v) = x := by
  have hr := bridge_reverse_raw hb
  rw [hr]
  apply bigValue_decodes
  · intro he
    have hs' := (T.p.inj he).2
    rw [hs',selfTail_self_false] at hs; cases hs
  · intro he; have hh := congrArg sz he; simp only [sz] at hh; omega
  · exact bridge_self_key_protected_false hs hb
  · simp only [bigValue,decide_true,Bool.true_and,hs,hb,rawValue,hr,Bool.and_self]

theorem source_self_branch {x y w : T} (hi : image x w = true)
    (hu : mul w y = drop y) (hv : mul (drop y) y = drop y) :
    mul y (mul x (mul (mul w y) y)) = x := by
  cases y with
  | e => exact False.elim (mul_ne_right e e hv)
  | k t =>
    have hm : mul t (k t) = p t (k t) := image_reverse_raw (image_square t)
    change mul t (k t) = t at hv
    rw [hm] at hv
    have hh := congrArg sz hv; simp only [sz] at hh; omega
  | p v s =>
    have hs := selfTail_complete hv
    have hb := selfColumn_decode_bridge hs hi hu
    rw [hu,hv]
    exact bridge_decodes_self hs hb

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem scalar_double_right_cases (w y : T) :
    (mul w y = p w y ∧ mul (mul w y) y = p (p w y) y) ∨
    (w = y ∧ mul (mul w y) y = p (k y) y) ∨
    (mul w y = drop y ∧
      (mul (mul w y) y = p (drop y) y ∨ mul (mul w y) y = drop y)) := by
  rcases mul_cases w y with hr | ⟨he,hk⟩ | ⟨_,_,hd⟩
  · exact Or.inl ⟨hr,by rw [hr]; exact mul_pair_right w y⟩
  · exact Or.inr (Or.inl ⟨he,by rw [hk]; exact mul_square_right y⟩)
  · apply Or.inr; apply Or.inr
    refine ⟨hd,?_⟩
    rcases mul_cases (mul w y) y with hr | ⟨he,_⟩ | ⟨_,_,hh⟩
    · exact Or.inl (by rw [hr,hd])
    · exact False.elim (mul_ne_right w y he)
    · exact Or.inr hh

theorem product_drop_pair {w y : T} (hm : mul w y = drop y) : ∃ u s, y = p u s := by
  rcases mul_cases w y with hr | ⟨_,hk⟩ | ⟨_,hc,_⟩
  · rw [hm] at hr
    have hl := drop_size_le y
    have hh := congrArg sz hr; simp only [sz] at hh; omega
  · rw [hm] at hk
    have hl := drop_size_le y
    have hh := congrArg sz hk; simp only [sz] at hh; omega
  · have ha := decode_admissible hc
    cases y with
    | e => cases ha
    | k t => cases ha
    | p u s => exact ⟨u,s,rfl⟩

-- The fourth-product hypothesis remains to be proved for the non-self branches.
theorem source_from_fourth_raw (x y w : T) (hi : image x w = true)
    (hr : mul x (mul (mul w y) y) = p x (mul (mul w y) y)) :
    mul y (mul x (mul (mul w y) y)) = x := by
  rcases scalar_double_right_cases w y with ⟨hu,hv⟩ | ⟨hw,hv⟩ | ⟨hu,hv⟩
  · rw [hr,hv]
    apply smallValue_decodes
    have hx : rawValue x (p (p w y) y) = true := by
      rw [hv] at hr; exact decide_eq_true hr
    have hw : rawValue w y = true := decide_eq_true hu
    simp only [smallValue,decide_true,Bool.true_and,hx,hw,hi,Bool.and_self,Bool.true_or]
  · rw [hr,hv]
    apply smallValue_decodes
    have hx : rawValue x (p (k y) y) = true := by
      rw [hv] at hr; exact decide_eq_true hr
    rw [hw] at hi
    simp only [smallValue,decide_true,Bool.true_and,hx,hi,Bool.false_or,Bool.true_or]
  · rcases hv with hv | hv
    · rw [hr,hv]
      apply smallValue_decodes
      have hx : rawValue x (p (drop y) y) = true := by
        rw [hv] at hr; exact decide_eq_true hr
      have hy : rawValue (drop y) y = true := by
        rw [hu] at hv; exact decide_eq_true hv
      rcases product_drop_pair hu with ⟨u,s,he⟩
      rcases image_sound hi with ⟨z,hz⟩
      have hj : intersection x y = true := by
        rw [he]
        apply intersection_complete (z:=z)
        rw [hz,←he,hu,he]; rfl
      simp only [smallValue,decide_true,Bool.true_and,hx,hy,hj,Bool.and_self,Bool.or_true]
    · have hv' : mul (drop y) y = drop y := by rw [hu] at hv; exact hv
      exact source_self_branch hi hu hv'

theorem equation8485_from_fourth_raw (x y z : T)
    (hr : mul x (mul (mul (mul z x) y) y) = p x (mul (mul (mul z x) y) y)) :
    mul y (mul x (mul (mul (mul z x) y) y)) = x :=
  source_from_fourth_raw x y (mul z x) (image_contains_product z x) hr

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfTail_square_lower {a t : T} (h : selfTail a (k t) = true) : sz (k t) < sz a := by
  rcases selfTail_shape h with ⟨w,he⟩ | ⟨u,he⟩
  · cases he
  · rw [he]; simp only [sz]; omega

theorem square_image_lower_raw {t a w : T} (hl : sz a < sz t)
    (hi : image (k t) w = true) : mul w a = p w a := by
  rcases image_shape hi with hk | ⟨z,he,_⟩ | ⟨b,he⟩
  · rw [hk]
    apply mul_drop_large
    · intro he; have hh := congrArg sz he; simp only [sz] at hh; omega
    · simp only [drop,sz]; omega
  · rw [he]
    rcases mul_cases (p z (k t)) a with hr | ⟨he,_⟩ | ⟨_,hd,_⟩
    · exact hr
    · have hh := congrArg sz he; simp only [sz] at hh; omega
    · have hcv : decodeValue (p z (k t)) a = true :=
        (decode_scope (n:=rank (.mul (p z (k t)) a)) (by simp only [rank]; omega)).symm.trans hd
      have ha := decode_admissible hd
      cases a with
      | e => cases ha
      | k b => cases ha
      | p u v =>
        rcases (decodeValue_parts hcv).2.2.2 with hsmall | hbig
        · rcases smallValue_tail hsmall with ⟨b,he⟩
          have hh := congrArg sz he; simp only [sz] at hh hl; omega
        · simp only [bigValue,Bool.and_eq_true,decide_eq_true_eq] at hbig
          have hself := hbig.1.1.2
          have hb := selfTail_square_lower hself
          simp only [sz] at hb hl; omega
  · cases he

theorem square_intersection_lower_false {t a : T} (hl : sz a < sz t) :
    intersection (k t) a = false := by
  cases h : intersection (k t) a with
  | false => rfl
  | true =>
    rcases (intersection_spec _ _).mp h with ⟨_,⟨z,hz⟩⟩
    have hr := square_image_lower_raw hl (image_contains_product z (k t))
    rw [hr] at hz
    have hd := drop_size_le a
    have hh := congrArg sz hz; simp only [sz] at hh; omega

theorem bridge_square_reverse_false (y : T) : bridge (k y) y = false := by
  rw [bridge_equation]
  have hi : imageValue (k y) y = false := by
    have hk : y ≠ k (k y) := by
      intro he; have hh := congrArg sz he; simp only [sz] at hh; omega
    simp only [imageValue,hk,decide_false,Bool.false_or,Bool.or_false]
    cases y with
    | e => rfl
    | k t => rfl
    | p t u =>
      have hn : u ≠ k (p t u) := by
        intro he; have hh := congrArg sz he; simp only [sz] at hh; omega
      simp only [hn,decide_false,Bool.false_and]
  simp only [bridgeValue,hi,Bool.false_or,Bool.or_false]
  cases y with
  | e => rfl
  | k a => rfl
  | p t u =>
    cases hs : selfTail t (k (p t u)) with
    | false => simp only [hs,Bool.and_false,Bool.false_and]
    | true =>
      have hl := selfTail_square_lower hs
      simp only [sz] at hl; omega

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem fourth_square_raw {x y : T} (hi : image x y = true) :
    mul x (p (k y) y) = p x (p (k y) y) := by
  rcases mul_cases x (p (k y) y) with hr | ⟨he,_⟩ | ⟨_,hd,_⟩
  · exact hr
  · have hl := image_lower_bound hi
    rw [he] at hl; simp only [drop,sz] at hl; omega
  · have hcv : decodeValue x (p (k y) y) = true :=
      (decode_scope (n:=rank (.mul x (p (k y) y))) (by simp only [rank]; omega)).symm.trans hd
    rcases (decodeValue_parts hcv).2.2.2 with hsmall | hbig
    · rcases smallValue_tail hsmall with ⟨r,hy⟩
      subst y
      simp only [smallValue,decide_true,Bool.true_and,Bool.and_eq_true,Bool.or_eq_true] at hsmall
      rcases hsmall.2 with (hrr | hk) | hj
      · cases r with
        | e => cases hrr
        | k t => cases hrr
        | p a second =>
          simp only [Bool.and_eq_true,decide_eq_true_eq] at hrr
          have hl := image_lower_bound hrr.2
          simp only [drop,sz] at hl; omega
      · have hl := image_lower_bound hk.2
        simp only [drop,sz] at hl; omega
      · have hh := hj.2
        rw [square_intersection_lower_false (by simp only [sz]; omega)] at hh
        cases hh
    · cases x with
      | e => cases hbig
      | k t => cases hbig
      | p first s =>
        simp only [bigValue,bridge_square_reverse_false,Bool.and_false,Bool.false_eq_true] at hbig

theorem source_square_branch {x y w : T} (hi : image x w = true) (hw : w = y) :
    mul y (mul x (mul (mul w y) y)) = x := by
  apply source_from_fourth_raw x y w hi
  rw [hw,mul_square,mul_square_right]
  rw [hw] at hi
  exact fourth_square_raw hi

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem rawValue_square_false (a : T) : rawValue a a = false := by
  simp only [rawValue,mul_square,reduceCtorEq,decide_false]

theorem smallValue_diagonal_false (a u : T) : smallValue a (p u (p a a)) = false := by
  have hk : a ≠ k a := by
    intro he; have hh := congrArg sz he; simp only [sz] at hh; omega
  have hd : (decide (a = drop a) && rawValue a a && intersection u a) = false := by
    rw [rawValue_square_false]; simp only [Bool.and_false,Bool.false_and]
  simp only [smallValue,hk,decide_false,Bool.false_and,hd,Bool.or_false]
  cases a with
  | e => simp only [Bool.and_false]
  | k t => simp only [Bool.and_false]
  | p w second =>
    have hn : second ≠ p w second := by
      intro he; have hh := congrArg sz he; simp only [sz] at hh; omega
    simp only [hn,decide_false,Bool.false_and,Bool.and_false]

theorem image_tail_decode_false {x w : T} (hi : image x w = true) (u : T) :
    decodeValue w (p u x) = false := by
  cases hc : decodeValue w (p u x) with
  | false => rfl
  | true =>
    rcases (decodeValue_parts hc).2.2.2 with hsmall | hbig
    · rcases smallValue_tail hsmall with ⟨r,he⟩
      rcases image_shape hi with hk | ⟨a,hp,_⟩ | ⟨s,hx⟩
      · rw [hk] at he
        have hh := congrArg sz he; simp only [sz] at hh; omega
      · rw [hp] at he
        have hh := congrArg sz he; simp only [sz] at hh; omega
      · rw [hx] at he
        have hs := (T.p.inj he).2
        rw [hx,hs,smallValue_diagonal_false] at hsmall
        cases hsmall
    · rcases image_shape hi with hk | ⟨a,hp,_⟩ | ⟨s,hx⟩
      · rw [hk] at hbig; cases hbig
      · rw [hp] at hbig
        simp only [bigValue,selfTail_self_false,Bool.and_false,Bool.false_and,Bool.false_eq_true] at hbig
      · rw [hx] at hbig
        rw [bigValue_tail_false (by simp only [sz]; omega)] at hbig
        cases hbig

theorem intersection_tail_false (x u : T) : intersection x (p u x) = false := by
  cases hi : intersection x (p u x) with
  | false => rfl
  | true =>
    rcases intersection_sound hi with ⟨z,hz⟩
    have hd := (decodeValue_pair_spec (mul z x) u x).mpr hz
    rw [image_tail_decode_false (image_contains_product z x) u] at hd
    cases hd

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfTail_below_head_false {u t : T} (hl : sz t < sz u) (s : T) :
    selfTail (p u s) t = false := by
  cases h : selfTail (p u s) t with
  | false => rfl
  | true =>
    rcases selfTail_shape h with ⟨w,he⟩ | ⟨a,he⟩
    · have hh := congrArg sz he; simp only [sz] at hh; omega
    · have hh := congrArg sz (T.p.inj he).1; omega

theorem image_head_false (u s : T) : image u (p u s) = false := by
  cases h : image u (p u s) with
  | false => rfl
  | true =>
    rcases image_shape h with hk | ⟨a,hp,hr⟩ | ⟨t,he⟩
    · cases hk
    · have he := (T.p.inj hp).1
      rw [←he,mul_square] at hr; cases hr
    · have hh := congrArg sz he; simp only [sz] at hh; omega

theorem bridge_head_false (u s : T) : bridge u (p u s) = false := by
  rw [bridge_equation]
  have hi : imageValue u (p u s) = false := (image_equation _ _).symm.trans (image_head_false u s)
  simp only [bridgeValue,hi,selfTail_self_false,Bool.and_false,Bool.false_and,
    Bool.false_or,Bool.or_false]
  cases u with
  | e => rfl
  | k a => rfl
  | p b a =>
    have h1 : selfTail (p (p b a) s) a = false :=
      selfTail_below_head_false (by simp only [sz]; omega) s
    simp only [h1,Bool.false_and,Bool.false_or]
    cases b with
    | e => rfl
    | k t => rfl
    | p t v =>
      have h2 : selfTail (p (p (p t v) a) s) t = false :=
        selfTail_below_head_false (by simp only [sz]; omega) s
      simp only [h2,Bool.false_and]

theorem selfTail_nested_tail_false (u s : T) : selfTail s (p u (p u s)) = false := by
  cases h : selfTail s (p u (p u s)) with
  | false => rfl
  | true =>
    rcases selfTail_shape h with ⟨w,he⟩ | ⟨a,he⟩
    · have hh := congrArg sz (T.p.inj he).2; simp only [sz] at hh; omega
    · have hh := congrArg sz he; simp only [sz] at hh; omega

theorem intersection_head_raw_false {u s : T} (hr : mul u (p u s) = p u (p u s)) :
    intersection (p u (p u s)) (p u s) = false := by
  cases hi : intersection (p u (p u s)) (p u s) with
  | false => rfl
  | true =>
    rcases intersection_sound hi with ⟨z,hz⟩
    have him := image_contains_product z (p u (p u s))
    rcases image_shape him with hk | ⟨w,hp,_⟩ | ⟨a,he⟩
    · rw [hk] at hz
      have hraw : mul (k (p u (p u s))) (p u s) = p (k (p u (p u s))) (p u s) := by
        apply mul_drop_large
        · intro he; have hh := congrArg sz he; simp only [sz] at hh; omega
        · simp only [drop,sz]; omega
      rw [hraw] at hz
      have hh := congrArg sz hz; simp only [sz] at hh; omega
    · rw [hp] at hz
      have hc := (decodeValue_pair_spec _ _ _).mpr hz
      rcases (decodeValue_parts hc).2.2.2 with hsmall | hbig
      · rcases smallValue_tail hsmall with ⟨a,he⟩
        have hh := congrArg sz he; simp only [sz] at hh; omega
      · simp only [bigValue,selfTail_nested_tail_false,Bool.and_false,Bool.false_and,Bool.false_eq_true] at hbig
    · have hu : mul z (p u (p u s)) = u := (T.p.inj he).1.symm
      rw [hu,hr] at hz
      have hh := congrArg sz hz; simp only [sz] at hh; omega

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem fourth_drop_pair_raw {x u s : T} (hi : intersection x (p u s) = true)
    (hr : mul u (p u s) = p u (p u s)) :
    mul x (p u (p u s)) = p x (p u (p u s)) := by
  rcases mul_cases x (p u (p u s)) with hraw | ⟨he,_⟩ | ⟨_,hd,_⟩
  · exact hraw
  · rw [he,intersection_head_raw_false hr] at hi; cases hi
  · have hcv : decodeValue x (p u (p u s)) = true :=
      (decode_scope (n:=rank (.mul x (p u (p u s)))) (by simp only [rank]; omega)).symm.trans hd
    rcases (decodeValue_parts hcv).2.2.2 with hsmall | hbig
    · rcases smallValue_tail hsmall with ⟨r,he⟩
      have hs := (T.p.inj he).2
      rw [hs,intersection_tail_false] at hi; cases hi
    · cases x with
      | e => cases hbig
      | k t => cases hbig
      | p first a =>
        simp only [bigValue,bridge_head_false,Bool.and_false,Bool.false_eq_true] at hbig

theorem fourth_drop_raw {x y w : T} (hi : image x w = true)
    (hu : mul w y = drop y) (hr : mul (drop y) y = p (drop y) y) :
    mul x (p (drop y) y) = p x (p (drop y) y) := by
  rcases product_drop_pair hu with ⟨u,s,hy⟩
  rcases image_sound hi with ⟨z,hz⟩
  have hj : intersection x (p u s) = true := by
    apply intersection_complete (z:=z)
    rw [hz,←hy,hu,hy]; rfl
  rw [hy] at hr ⊢
  exact fourth_drop_pair_raw hj hr

theorem source_drop_branch {x y w : T} (hi : image x w = true)
    (hu : mul w y = drop y) (hr : mul (drop y) y = p (drop y) y) :
    mul y (mul x (mul (mul w y) y)) = x := by
  apply source_from_fourth_raw x y w hi
  rw [hu,hr]
  exact fourth_drop_raw hi hu hr

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfTail_chain_into_selfpoint_false {y s t : T} (hs : selfTail y s = true)
    (ht : selfTail y t = true) : selfTail t (p y s) = false := by
  cases h : selfTail t (p y s) with
  | false => rfl
  | true =>
    have hl := selfTail_incoming_large hs h
    rcases selfTail_shape ht with ⟨w,he⟩ | ⟨a,hy⟩
    · rcases selfTail_shape h with ⟨z,hp⟩ | ⟨a,ht'⟩
      · have hh := congrArg sz hp; simp only [sz] at hh hl; omega
      · rw [he] at ht'
        have hys := (T.p.inj (T.p.inj ht').1).2
        rw [←hys,selfTail_self_false] at hs; cases hs
    · rw [hy] at hl; simp only [sz] at hl; omega

theorem bridge_raw_self_column_false {y s w : T} (hs : selfTail y s = true)
    (hi : image (p y s) w = true) (hr : mul w y = p w y) : bridge (p w y) y = false := by
  have hn : w ≠ y := by intro he; rw [he,mul_square] at hr; cases hr
  rw [bridge_tail_equation,←image_equation,image_pair_tail_false hn,Bool.false_or]
  cases w with
  | e => rfl
  | k a => rfl
  | p t a =>
    cases hh : selfTail y t && selfTail t a && hasDecoderValue (p (p t a) y) with
    | false => exact hh
    | true =>
      simp only [Bool.and_eq_true] at hh
      rcases image_shape hi with hk | ⟨z,hp,_⟩ | ⟨b,he⟩
      · cases hk
      · have ha := (T.p.inj hp).2
        have ht := hh.1.2
        rw [ha,selfTail_chain_into_selfpoint_false hs hh.1.1] at ht; cases ht
      · have hy := (T.p.inj he).1
        exact False.elim (hn hy.symm)

theorem bridge_double_tail_false {w x : T} (hn : w ≠ x) :
    bridge w (p (p w x) x) = false := by
  have hi : imageValue w (p (p w x) x) = false := by
    have hx : x ≠ w := Ne.symm hn
    simp only [imageValue,reduceCtorEq,decide_false,hx,Bool.false_and,Bool.false_or]
    cases w with
    | e => rfl
    | k a => rfl
    | p a b =>
      have hh : p (p (p a b) x) x ≠ a := by
        intro he; have hl := congrArg sz he; simp only [sz] at hl; omega
      simp only [hh,decide_false,Bool.false_and]
  have hself : selfTail (p (p w x) x) (p w x) = false := by
    cases h : selfTail (p (p w x) x) (p w x) with
    | false => rfl
    | true =>
      have hh := selfTail_reverse h
      rw [selfTail_pair_tail_false] at hh; cases hh
  rw [bridge_equation]
  simp only [bridgeValue,hi,hself,Bool.false_and,Bool.false_or,Bool.or_false]
  cases w with
  | e => rfl
  | k a => rfl
  | p a b =>
    have h1 : selfTail (p (p (p a b) x) x) b = false :=
      selfTail_below_head_false (by simp only [sz]; omega) x
    simp only [h1,Bool.false_and,Bool.false_or]
    cases a with
    | e => rfl
    | k t => rfl
    | p t s =>
      have h2 : selfTail (p (p (p (p t s) b) x) x) t = false :=
        selfTail_below_head_false (by simp only [sz]; omega) x
      simp only [h2,Bool.false_and]

theorem hasDecoder_double_frame_false {w x : T} (hn : w ≠ x) :
    hasDecoderValue (p w (p (p w x) x)) = false := by
  have hh : p w x ≠ drop x := by
    intro he; have hd := drop_size_le x
    rw [←he] at hd; simp only [sz] at hd; omega
  simp only [hasDecoderValue,bridge_double_tail_false hn,Bool.and_false,Bool.or_false,
    smallValue,image_self_false,Bool.and_false,reduceCtorEq,decide_false,Bool.false_and,
    hh,Bool.or_self]

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem selfTail_large_right_false {t y : T} (hl : sz t < sz y) (w : T) :
    selfTail t (p w y) = false := by
  cases h : selfTail t (p w y) with
  | false => rfl
  | true =>
    rcases selfTail_shape h with ⟨a,he⟩ | ⟨s,he⟩
    · have hh := congrArg sz (T.p.inj he).2; omega
    · have hh := congrArg sz he; simp only [sz] at hh; omega

theorem image_raw_column {x w : T} (hi : image x w = true)
    (hr : mul (drop x) x = p (drop x) x) : mul w x = p w x := by
  rcases image_shape hi with hk | ⟨a,hp,_⟩ | ⟨s,hx⟩
  · rw [hk]; exact mul_square_right x
  · rw [hp]; exact mul_pair_right a x
  · rw [hx] at hr ⊢; exact hr

theorem intersection_long_tail_false {a s w : T} (hi : image (p a s) w = true)
    (hr : mul a (p a s) = p a (p a s)) :
    intersection (p w (p a (p a s))) (p a s) = false := by
  cases hj : intersection (p w (p a (p a s))) (p a s) with
  | false => rfl
  | true =>
    rcases intersection_sound hj with ⟨z,hz⟩
    have him := image_contains_product z (p w (p a (p a s)))
    rcases image_shape him with hk | ⟨t,hp,_⟩ | ⟨b,he⟩
    · rw [hk] at hz
      have hraw : mul (k (p w (p a (p a s)))) (p a s) =
          p (k (p w (p a (p a s)))) (p a s) := by
        apply mul_drop_large
        · intro he; have hh := congrArg sz he; simp only [sz] at hh; omega
        · simp only [drop,sz]; omega
      rw [hraw] at hz
      have hh := congrArg sz hz; simp only [sz] at hh; omega
    · rw [hp] at hz
      have hc := (decodeValue_pair_spec _ _ _).mpr hz
      rcases (decodeValue_parts hc).2.2.2 with hsmall | hbig
      · rcases smallValue_tail hsmall with ⟨u,he⟩
        have hh := congrArg sz he; simp only [sz] at hh; omega
      · have hself : selfTail s (p w (p a (p a s))) = false :=
          selfTail_large_right_false (by simp only [sz]; omega) w
        simp only [bigValue,hself,Bool.and_false,Bool.false_and,Bool.false_eq_true] at hbig
    · have hw : mul z (p w (p a (p a s))) = w := (T.p.inj he).1.symm
      have hraw := image_raw_column hi hr
      rw [hw,hraw] at hz
      have hh := congrArg sz hz; simp only [sz] at hh; omega

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem image_left_hasDecoder {w y : T} (hi : image (p w y) w = true) :
    hasDecoderValue (p w y) = true := by
  rcases image_sound hi with ⟨z,hz⟩
  exact decodeValue_hasDecoder ((decodeValue_pair_spec z w y).mpr hz)

theorem fourth_ordinary_raw {x y w : T} (hi : image x w = true)
    (hr : mul w y = p w y) : mul x (p (p w y) y) = p x (p (p w y) y) := by
  rcases mul_cases x (p (p w y) y) with hraw | ⟨he,_⟩ | ⟨_,hd,_⟩
  · exact hraw
  · have hl := image_lower_bound hi
    rw [he] at hl; simp only [drop,sz] at hl; omega
  · have hcv : decodeValue x (p (p w y) y) = true :=
      (decode_scope (n:=rank (.mul x (p (p w y) y))) (by simp only [rank]; omega)).symm.trans hd
    rcases (decodeValue_parts hcv).2.2.2 with hsmall | hbig
    · rcases smallValue_tail hsmall with ⟨r,hy⟩
      subst y
      simp only [smallValue,decide_true,Bool.true_and,Bool.and_eq_true,Bool.or_eq_true] at hsmall
      rcases hsmall.2 with (hrr | hk) | hj
      · cases r with
        | e => cases hrr
        | k t => cases hrr
        | p a second =>
          simp only [Bool.and_eq_true,decide_eq_true_eq] at hrr
          have he := hrr.1.1
          subst second
          have him := hrr.2
          rcases image_small_output him (by simp only [sz]; omega) with ⟨s,he⟩
          have hw := (T.p.inj he).1
          subst a
          have hh := image_left_hasDecoder him
          have hn : w ≠ x := by intro he; rw [he,image_self_false] at hi; cases hi
          rw [hasDecoder_double_frame_false hn] at hh; cases hh
      · have him := hk.2
        rcases image_small_output him (by simp only [sz]; omega) with ⟨s,he⟩
        have hw := (T.p.inj he).1
        rw [hw,image_self_false] at hi; cases hi
      · have he : r = drop x := of_decide_eq_true hj.1.1
        have hrx := hj.1.2
        have hji := hj.2
        subst r
        cases x with
        | e =>
          have hrx' : rawValue e e = true := hrx
          rw [rawValue_square_false] at hrx'; cases hrx'
        | k t =>
          rw [intersection_equation] at hji
          cases hji
        | p a s =>
          have hrx' : mul a (p a s) = p a (p a s) := of_decide_eq_true hrx
          simp only [drop] at hji
          rw [intersection_long_tail_false hi hrx'] at hji; cases hji
    · cases x with
      | e => cases hbig
      | k t => cases hbig
      | p first s =>
        simp only [bigValue,Bool.and_eq_true,decide_eq_true_eq] at hbig
        have he := hbig.1.1.1
        subst first
        have hs := hbig.1.1.2
        have hb := hbig.2
        rw [bridge_raw_self_column_false hs hi hr] at hb; cases hb

theorem source_ordinary_branch {x y w : T} (hi : image x w = true)
    (hr : mul w y = p w y) : mul y (mul x (mul (mul w y) y)) = x := by
  apply source_from_fourth_raw x y w hi
  rw [hr,mul_pair_right]
  exact fourth_ordinary_raw hi hr

end submission.Austin8485

set_option autoImplicit false
namespace submission.Austin8485
open submission.Austin8485Base
open T

theorem source_from_image {x y w : T} (hi : image x w = true) :
    mul y (mul x (mul (mul w y) y)) = x := by
  rcases scalar_double_right_cases w y with ⟨hu,_⟩ | ⟨hw,_⟩ | ⟨hu,hv⟩
  · exact source_ordinary_branch hi hu
  · exact source_square_branch hi hw
  · rcases hv with hr | hs
    · rw [hu] at hr
      exact source_drop_branch hi hu hr
    · rw [hu] at hs
      exact source_self_branch hi hu hs

theorem equation8485 (x y z : T) : mul y (mul x (mul (mul (mul z x) y) y)) = x :=
  source_from_image (image_contains_product z x)

def dualMul (a b : T) : T := mul b a

theorem equation37519 (x y z : T) :
    dualMul (dualMul (dualMul y (dualMul y (dualMul x z))) x) y = x := by
  exact equation8485 x y z

theorem fourth_raw {x y w : T} (hi : image x w = true) :
    mul x (mul (mul w y) y) = p x (mul (mul w y) y) := by
  rcases scalar_double_right_cases w y with ⟨hu,hv⟩ | ⟨hw,hv⟩ | ⟨hu,hv⟩
  · rw [hv]; exact fourth_ordinary_raw hi hu
  · rw [hv]
    rw [hw] at hi
    exact fourth_square_raw hi
  · rcases hv with hr | hs
    · rw [hr]
      rw [hu] at hr
      exact fourth_drop_raw hi hu hr
    · rw [hs]
      rw [hu] at hs
      rcases product_drop_pair hu with ⟨v,s,hy⟩
      rw [hy] at hu hs ⊢
      exact bridge_reverse_raw (selfColumn_decode_bridge (selfTail_complete hs) hi hu)

abbrev Carrier := T
abbrev embed := submission.Austin8485Base.tower
theorem embed_injective (n j : Nat) (h : embed n = embed j) : n = j :=
  submission.Austin8485Base.tower_injective n j h

theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op y (op x (op (op (op z x) y) y))) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨T,mul,embed,(fun x y z => (equation8485 x y z).symm),embed_injective⟩

theorem dual_infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op (op (op y (op y (op x z))) x) y) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨T,dualMul,embed,(fun x y z => (equation37519 x y z).symm),embed_injective⟩

end submission.Austin8485

namespace submission
abbrev CM := Austin8485.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin8485.embed n = Austin8485.embed j) : n = j :=
  Austin8485.embed_injective n j h
end CM
instance modelMagma : Magma CM := ⟨Austin8485.mul⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact (submission.Austin8485.equation8485 x y z).symm
  · intro h
    have bad : 0 = 1 := submission.Austin8485.embed_injective 0 1
      (h (submission.Austin8485.embed 0) (submission.Austin8485.embed 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

