import Lean.Elab.Tactic.Omega
import JudgeProblem


set_option autoImplicit false
namespace submission.Austin7587

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

structure Keys (n : Nat) where
  terms : List T
  bounded : ∀ a, a ∈ terms → sz a < n

def Keys.empty (n : Nat) : Keys n := ⟨[],by simp⟩
def Keys.single {n : Nat} (a : T) (ha : sz a < n) : Keys n :=
  ⟨[a],by
    intro b hb
    have he : b = a := by simpa using hb
    simpa only [he] using ha⟩
def Keys.append {n : Nat} (a b : Keys n) : Keys n :=
  ⟨a.terms ++ b.terms,by
    intro t ht
    rcases List.mem_append.mp ht with ha | hb
    · exact a.bounded t ha
    · exact b.bounded t hb⟩

abbrev Answer (b : T) := Keys (sz b)

theorem key_ne_container {b a : T} (d : Answer b) (h : a ∈ d.terms) : a ≠ b := by
  intro he
  have hs := d.bounded a h
  rw [he] at hs
  omega

theorem drop_small_of_pos {b : T} (h : 0 < sz b) : sz (drop b) < sz b := by
  cases b <;> simp only [drop,sz] at * <;> omega

theorem drop_small_of_key {b a : T} (d : Answer b) (h : a ∈ d.terms) : sz (drop b) < sz b :=
  drop_small_of_pos (by have hs := d.bounded a h; omega)

def evalWith (a b : T) (d : Answer b) : T :=
  if a = b then k b else if a ∈ d.terms then drop b else p a b

def rightImageWith (b out : T) (d : Answer b) : Bool :=
  decide (out = k b) ||
    (match out with
      | p a second => decide (second = b ∧ evalWith a b d = out)
      | _ => false) ||
    (decide (out = drop b) && !d.terms.isEmpty)

@[simp] theorem evalWith_square (a : T) (d : Answer a) : evalWith a a d = k a := by simp [evalWith]
theorem evalWith_hit {a b : T} (d : Answer b) (h : a ∈ d.terms) : evalWith a b d = drop b := by
  simp only [evalWith,key_ne_container d h,↓reduceIte,h]

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

abbrev Scope (n : Nat) := (b : T) → sz b < n → Answer b

def evalTest {n : Nat} (look : Scope n) (a b out : T) : Bool :=
  if hb : sz b < n then decide (evalWith a b (look b hb) = out) else false

def rightImageTest {n : Nat} (look : Scope n) (b out : T) : Bool :=
  if hb : sz b < n then rightImageWith b out (look b hb) else false

def codeKeys {n : Nat} (look : Scope n) (b : T) : List T :=
  if hb : sz b < n then (look b hb).terms else []

def ordinaryImage {n : Nat} (look : Scope n) (x y u : T) : Bool :=
  let ordinary := match u with
    | p first w => decide (first = y) && rightImageTest look x w && evalTest look y w u
    | _ => false
  let square := decide (u = k y) && rightImageTest look x y
  let squareInput := evalTest look y (k x) u
  let decodedInput := !(codeKeys look x).isEmpty && evalTest look y (drop x) u
  let recoveredInput := evalTest look u x (p u x) && evalTest look y (p u x) u
  ordinary || square || squareInput || decodedInput || recoveredInput

def imageWithin {n : Nat} (look : Scope n) (x y u : T) : Bool :=
  ordinaryImage look x y u ||
    (evalTest look u x (p u x) &&
      match x with
      | p a c => if c = y then imageWithin look u y a else false
      | k c => if c = y then imageWithin look u y c else false
      | e => false)
termination_by sz x + sz u
decreasing_by all_goals simp_all [sz]; omega

def candidate {n : Nat} (key : T) (test : Bool) : Keys n :=
  if hk : sz key < n then if test then Keys.single key hk else Keys.empty n else Keys.empty n

def baseWithin {n : Nat} (look : Scope n) (b : T) : Keys n :=
  let test (x second : T) := match second with
    | p u y => candidate y (imageWithin look x y u)
    | k y => candidate y (imageWithin look x y y)
    | e => Keys.empty n
  match b with
  | p x second => test x second
  | k x => test x x
  | e => Keys.empty n

def extraTest {n : Nat} (look : Scope n) (x v y : T) : Keys n :=
  candidate y (decide (drop y = v) && (codeKeys look y).any (fun u => imageWithin look x y u))

def extraKeys {n : Nat} (look : Scope n) (x : T) : List T :=
  let rootKeys := match x with
    | p _ y => [y]
    | k y => [y]
    | e => []
  rootKeys ++ codeKeys look (k x) ++
    (if (codeKeys look x).isEmpty then [] else codeKeys look (drop x))

def collect {n : Nat} (ys : List T) (f : T → Keys n) : Keys n :=
  ys.foldr (fun y acc => (f y).append acc) (Keys.empty n)

def extraWithin {n : Nat} (look : Scope n) (b : T) : Keys n :=
  match b with
  | p x v => collect (extraKeys look x) (extraTest look x v)
  | k x => collect (extraKeys look x) (extraTest look x x)
  | e => Keys.empty n

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

def decode (b : T) : Answer b :=
  let look : Scope (sz b) := fun c hc => decode c
  (baseWithin look b).append (extraWithin look b)
termination_by sz b

def q (a b : T) : T := evalWith a b (decode b)
def rightImage (b out : T) : Bool := rightImageWith b out (decode b)
def Code (b key : T) : Prop := key ∈ (decode b).terms

abbrev scope (n : Nat) : Scope n := fun b _ => decode b
theorem decode_eq (b : T) : decode b =
    (baseWithin (scope (sz b)) b).append (extraWithin (scope (sz b)) b) := by rw [decode.eq_def]

@[simp] theorem q_square (a : T) : q a a = k a := evalWith_square _ _
theorem q_hit {a b : T} (h : Code b a) : q a b = drop b := evalWith_hit _ h
theorem code_key_bound {a b : T} (h : Code b a) : sz a < sz b := (decode b).bounded a h

theorem q_ne_right (a b : T) : q a b ≠ b := by
  intro he
  by_cases hab : a = b
  · subst a
    rw [q_square] at he
    have hs := congrArg sz he
    simp only [sz] at hs
    omega
  · by_cases hk : Code b a
    · rw [q_hit hk] at he
      have hs := drop_small_of_key (decode b) hk
      rw [he] at hs
      omega
    · have hq : q a b = p a b := by
        simp only [q,evalWith,hab,↓reduceIte,show ¬ a ∈ (decode b).terms from hk]
      rw [hq] at he
      have hs := congrArg sz he
      simp only [sz] at hs
      omega

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

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem rightImageWith_sound {b out : T} {d : Answer b}
    (h : rightImageWith b out d = true) : ∃ a, evalWith a b d = out := by
  unfold rightImageWith at h
  simp only [Bool.or_eq_true] at h
  rcases h with (hs | hp) | hc
  · have he : out = k b := of_decide_eq_true hs
    exact ⟨b,by rw [evalWith_square,he]⟩
  · cases out with
    | e => cases hp
    | k x => cases hp
    | p a second =>
      have he : second = b ∧ evalWith a b d = p a second := of_decide_eq_true hp
      exact ⟨a,he.2⟩
  · simp only [Bool.and_eq_true,decide_eq_true_eq] at hc
    cases hd : d.terms with
    | nil => simp only [hd,List.isEmpty_nil,Bool.not_true] at hc; cases hc.2
    | cons a rest =>
      have hm : a ∈ d.terms := by rw [hd]; simp
      exact ⟨a,(evalWith_hit d hm).trans hc.1.symm⟩

theorem rightImageWith_complete (a b : T) (d : Answer b) :
    rightImageWith b (evalWith a b d) d = true := by
  by_cases hab : a = b
  · subst a
    rw [evalWith_square]
    simp [rightImageWith]
  · by_cases hk : a ∈ d.terms
    · have he := evalWith_hit d hk
      have hn : d.terms.isEmpty = false := by
        cases hd : d.terms with
        | nil => rw [hd] at hk; cases hk
        | cons x xs => rfl
      rw [he]
      simp only [rightImageWith,decide_true,hn,Bool.not_false,Bool.and_self,Bool.or_true]
    · have he : evalWith a b d = p a b := by simp only [evalWith,hab,↓reduceIte,hk]
      rw [he]
      simp only [rightImageWith,he,and_self,decide_true,Bool.or_true,Bool.true_or]

theorem rightImage_sound {b out : T} (h : rightImage b out = true) : ∃ a, q a b = out :=
  rightImageWith_sound h
@[simp] theorem rightImage_complete (a b : T) : rightImage b (q a b) = true :=
  rightImageWith_complete a b (decode b)

theorem rightImage_iff (b out : T) : rightImage b out = true ↔ ∃ a, q a b = out := by
  constructor
  · exact rightImage_sound
  · rintro ⟨a,ha⟩
    rw [←ha]
    exact rightImage_complete a b

theorem q_cases (a b : T) : q a b = p a b ∨ (a = b ∧ q a b = k b) ∨
    (Code b a ∧ q a b = drop b) := by
  by_cases hab : a = b
  · exact Or.inr (Or.inl ⟨hab,by subst a; exact q_square b⟩)
  · by_cases hk : Code b a
    · exact Or.inr (Or.inr ⟨hk,q_hit hk⟩)
    · exact Or.inl (by simp only [q,evalWith,hab,↓reduceIte,show ¬ a ∈ (decode b).terms from hk])

theorem q_small_output {a b out : T} (hq : q a b = out) (hs : sz out < sz b) :
    Code b a ∧ out = drop b := by
  rcases q_cases a b with hp | ⟨_,hk⟩ | ⟨hc,hd⟩
  · rw [←hq,hp] at hs; simp only [sz] at hs; omega
  · rw [←hq,hk] at hs; simp only [sz] at hs; omega
  · exact ⟨hc,hq.symm.trans hd⟩

theorem q_left_size_bound (a b : T) : sz a ≤ max (sz b) (sz (q a b)) := by
  rcases q_cases a b with hp | ⟨hk,_⟩ | ⟨hc,_⟩
  · rw [hp]; simp only [sz]; omega
  · rw [hk]; omega
  · have hs := code_key_bound hc; omega

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem candidate_mem {n : Nat} (a key : T) (test : Bool) :
    a ∈ (candidate (n:=n) key test).terms ↔ a = key ∧ sz key < n ∧ test = true := by
  by_cases hk : sz key < n
  · cases ht : test <;> simp [candidate,hk,ht,Keys.single,Keys.empty]
  · simp [candidate,hk,Keys.empty]

theorem collect_mem {n : Nat} (a : T) (ys : List T) (f : T → Keys n) :
    a ∈ (collect ys f).terms ↔ ∃ y, y ∈ ys ∧ a ∈ (f y).terms := by
  induction ys with
  | nil => simp [collect,Keys.empty]
  | cons y ys ih =>
    simp only [collect,List.foldr_cons,Keys.append,List.mem_append] at *
    constructor
    · intro h
      rcases h with hy | ht
      · exact ⟨y,by simp,hy⟩
      · obtain ⟨z,hz,hza⟩ := ih.mp ht
        exact ⟨z,by simp [hz],hza⟩
    · rintro ⟨z,hz,hza⟩
      rcases List.mem_cons.mp hz with he | ht
      · subst z; exact Or.inl hza
      · exact Or.inr (ih.mpr ⟨z,ht,hza⟩)

theorem codeKeys_mem {n : Nat} (a b : T) :
    a ∈ codeKeys (scope n) b ↔ sz b < n ∧ Code b a := by
  by_cases hb : sz b < n <;> simp [codeKeys,hb,scope,Code]

theorem decode_mem (b a : T) : Code b a ↔
    a ∈ (baseWithin (scope (sz b)) b).terms ∨ a ∈ (extraWithin (scope (sz b)) b).terms := by
  unfold Code
  rw [decode_eq]
  exact List.mem_append

theorem base_pair {x y u : T}
    (h : imageWithin (scope (sz (p x (p u y)))) x y u = true) : Code (p x (p u y)) y := by
  apply (decode_mem _ _).mpr
  apply Or.inl
  change y ∈ (candidate y (imageWithin (scope (sz (p x (p u y)))) x y u)).terms
  exact (candidate_mem _ _ _).mpr ⟨rfl,by simp only [sz]; omega,h⟩

theorem base_square_right {x y : T}
    (h : imageWithin (scope (sz (p x (k y)))) x y y = true) : Code (p x (k y)) y := by
  apply (decode_mem _ _).mpr
  apply Or.inl
  change y ∈ (candidate y (imageWithin (scope (sz (p x (k y)))) x y y)).terms
  exact (candidate_mem _ _ _).mpr ⟨rfl,by simp only [sz]; omega,h⟩

theorem extraTest_mem {n : Nat} (a x v y : T) :
    a ∈ (extraTest (scope n) x v y).terms ↔
      a = y ∧ sz y < n ∧ drop y = v ∧
        ∃ u, u ∈ codeKeys (scope n) y ∧ imageWithin (scope n) x y u = true := by
  rw [extraTest,candidate_mem]
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true]

theorem extra_pair {x v y u : T}
    (hy : y ∈ extraKeys (scope (sz (p x v))) x)
    (hu : u ∈ codeKeys (scope (sz (p x v))) y)
    (hv : drop y = v) (hi : imageWithin (scope (sz (p x v))) x y u = true) : Code (p x v) y := by
  apply (decode_mem _ _).mpr
  apply Or.inr
  change y ∈ (collect (extraKeys (scope (sz (p x v))) x) (extraTest (scope (sz (p x v))) x v)).terms
  apply (collect_mem _ _ _).mpr
  refine ⟨y,hy,?_⟩
  apply (extraTest_mem _ _ _ _).mpr
  exact ⟨rfl,((codeKeys_mem u y).mp hu).1,hv,u,hu,hi⟩

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

def rootSize : T → Nat
  | e => 0
  | k x => sz x
  | p x y => max (sz x) (sz y)

theorem rootSize_le (x : T) : rootSize x ≤ sz x := by cases x <;> simp only [rootSize,sz] <;> omega
theorem drop_size_le (x : T) : sz (drop x) ≤ sz x := by cases x <;> simp only [drop,sz] <;> omega

theorem codeKeys_size {n : Nat} {look : Scope n} {b a : T}
    (h : a ∈ codeKeys look b) : sz a < sz b := by
  unfold codeKeys at h
  split at h
  · exact (look _ _).bounded a h
  · cases h

theorem codeKeys_root {n : Nat} {look : Scope n}
    (ih : ∀ b hb a, a ∈ (look b hb).terms → sz a < rootSize b)
    {b a : T} (h : a ∈ codeKeys look b) : sz a < rootSize b := by
  unfold codeKeys at h
  split at h
  · exact ih _ _ _ h
  · cases h

theorem extraKeys_bound {n : Nat} {look : Scope n}
    (ih : ∀ b hb a, a ∈ (look b hb).terms → sz a < rootSize b)
    {x a : T} (h : a ∈ extraKeys look x) : sz a < sz x := by
  unfold extraKeys at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with hr | hs
    · cases x with
      | e => cases hr
      | k y =>
        have he : a = y := by simpa using hr
        rw [he]; simp only [sz]; omega
      | p u y =>
        have he : a = y := by simpa using hr
        rw [he]; simp only [sz]; omega
    · exact codeKeys_root ih hs
  · split at h
    · cases h
    · have hs := codeKeys_size h
      have ht := drop_size_le x
      omega

theorem base_key_root {n : Nat} {look : Scope n} {b a : T}
    (h : a ∈ (baseWithin look b).terms) : sz a < rootSize b := by
  have bound (x second a : T)
      (h : a ∈ (match second with
        | p u y => candidate y (imageWithin look x y u)
        | k y => candidate y (imageWithin look x y y)
        | e => Keys.empty n).terms) : sz a < sz second := by
    cases second with
    | e => cases h
    | k y =>
      have he := ((candidate_mem a y _).mp h).1
      rw [he]; simp only [sz]; omega
    | p u y =>
      have he := ((candidate_mem a y _).mp h).1
      rw [he]; simp only [sz]; omega
  cases b with
  | e => cases h
  | k x => exact bound x x a h
  | p x v =>
    have hs := bound x v a h
    simp only [rootSize]; omega

theorem extraTest_key {n : Nat} {look : Scope n} {x v y a : T}
    (h : a ∈ (extraTest look x v y).terms) : a = y := ((candidate_mem a y _).mp h).1

theorem extra_key_root {n : Nat} {look : Scope n}
    (ih : ∀ b hb a, a ∈ (look b hb).terms → sz a < rootSize b)
    {b a : T} (h : a ∈ (extraWithin look b).terms) : sz a < rootSize b := by
  cases b with
  | e => cases h
  | k x =>
    obtain ⟨y,hy,ha⟩ := (collect_mem _ _ _).mp h
    rw [extraTest_key ha]
    exact extraKeys_bound ih hy
  | p x v =>
    obtain ⟨y,hy,ha⟩ := (collect_mem _ _ _).mp h
    have hs := extraKeys_bound ih hy
    rw [extraTest_key ha]; simp only [rootSize]; omega

theorem code_key_root_at (n : Nat) : ∀ b, sz b = n → ∀ a, Code b a → sz a < rootSize b := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro b hn a ha
    rcases (decode_mem b a).mp ha with hb | he
    · exact base_key_root hb
    · apply extra_key_root ?_ he
      intro c hc t ht
      exact ih (sz c) (by omega) c rfl t ht

theorem code_key_root {b a : T} (h : Code b a) : sz a < rootSize b :=
  code_key_root_at (sz b) b rfl a h

theorem q_left_root_bound (a b : T) : sz a < max (rootSize b) (sz (q a b)) := by
  rcases q_cases a b with hp | ⟨hk,hs⟩ | ⟨hc,_⟩
  · rw [hp]; simp only [sz]; omega
  · rw [hs,hk]; simp only [sz]; omega
  · have hs := code_key_root hc; omega

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem evalTest_sound {n : Nat} {a b out : T}
    (h : evalTest (scope n) a b out = true) : q a b = out := by
  unfold evalTest at h
  split at h
  · exact of_decide_eq_true h
  · cases h

theorem ordinaryImage_key_bound {n : Nat} {x y u : T}
    (h : ordinaryImage (scope n) x y u = true) : sz y < max (sz x) (sz u) := by
  unfold ordinaryImage at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((ho | hs) | hk) | hd) | hr
  · cases u with
    | e => cases ho
    | k t => cases ho
    | p first w =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at ho
      rw [ho.1.1]
      simp only [sz]; omega
  · simp only [Bool.and_eq_true,decide_eq_true_eq] at hs
    rw [hs.1]; simp only [sz]; omega
  · have hq := evalTest_sound hk
    have hb := q_left_root_bound y (k x)
    rw [hq] at hb
    exact hb
  · simp only [Bool.and_eq_true] at hd
    have hq := evalTest_sound hd.2
    have hb := q_left_root_bound y (drop x)
    rw [hq] at hb
    have ht := rootSize_le (drop x)
    have hs := drop_size_le x
    omega
  · simp only [Bool.and_eq_true] at hr
    have hq := evalTest_sound hr.2
    have hb := q_left_root_bound y (p u x)
    rw [hq] at hb
    simp only [rootSize] at hb
    omega

theorem image_key_bound_at (s : Nat) : ∀ {n : Nat} (x y u : T), sz x + sz u = s →
    imageWithin (scope n) x y u = true → sz y < max (sz x) (sz u) := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro n x y u hsize h
    rw [imageWithin.eq_def] at h
    simp only [Bool.or_eq_true] at h
    rcases h with hb | hr
    · exact ordinaryImage_key_bound hb
    · simp only [Bool.and_eq_true] at hr
      have ht := hr.2
      cases x with
      | e => cases ht
      | k c =>
        change (if c = y then imageWithin (scope n) u y c else false) = true at ht
        split at ht
        · have hb := ih (sz u + sz c) (by simp only [sz] at hsize; omega) u y c rfl ht
          simp only [sz]; omega
        · cases ht
      | p a c =>
        change (if c = y then imageWithin (scope n) u y a else false) = true at ht
        split at ht
        · have hb := ih (sz u + sz a) (by simp only [sz] at hsize; omega) u y a rfl ht
          simp only [sz]; omega
        · cases ht

theorem image_key_bound {n : Nat} {x y u : T}
    (h : imageWithin (scope n) x y u = true) : sz y < max (sz x) (sz u) :=
  image_key_bound_at _ x y u rfl h

theorem image_not_both_keys {n : Nat} {x y u : T}
    (h : imageWithin (scope n) x y u = true) (hx : Code y x) (hu : Code y u) : False := by
  have hy := image_key_bound h
  have hs := code_key_bound hx
  have ht := code_key_bound hu
  omega

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

def Image (x y u : T) : Prop := ∃ z, q y (q z x) = u

theorem q_small_drop {a b out : T} (hq : q a b = out) (hs : sz out < sz b) :
    out = drop b := (q_small_output hq hs).2

theorem rightImageTest_sound {n : Nat} {x w : T}
    (h : rightImageTest (scope n) x w = true) : ∃ z, q z x = w := by
  unfold rightImageTest at h
  split at h
  · exact rightImage_sound h
  · cases h

theorem codeKeys_nonempty {n : Nat} {x : T}
    (h : (!(codeKeys (scope n) x).isEmpty) = true) : ∃ a, Code x a := by
  cases hc : codeKeys (scope n) x with
  | nil => simp only [hc,List.isEmpty_nil,Bool.not_true] at h; cases h
  | cons a rest =>
    have hm : a ∈ codeKeys (scope n) x := by rw [hc]; simp
    exact ⟨a,((codeKeys_mem a x).mp hm).2⟩

theorem ordinaryImage_sound {n : Nat} {x y u : T}
    (h : ordinaryImage (scope n) x y u = true) : Image x y u := by
  unfold ordinaryImage at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((ho | hs) | hk) | hd) | hr
  · cases u with
    | e => cases ho
    | k t => cases ho
    | p first w =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at ho
      obtain ⟨z,hz⟩ := rightImageTest_sound ho.1.2
      exact ⟨z,by rw [hz]; exact evalTest_sound ho.2⟩
  · simp only [Bool.and_eq_true,decide_eq_true_eq] at hs
    obtain ⟨z,hz⟩ := rightImageTest_sound hs.2
    exact ⟨z,by rw [hz,q_square]; exact hs.1.symm⟩
  · exact ⟨x,by rw [q_square]; exact evalTest_sound hk⟩
  · simp only [Bool.and_eq_true] at hd
    obtain ⟨a,ha⟩ := codeKeys_nonempty hd.1
    exact ⟨a,by rw [q_hit ha]; exact evalTest_sound hd.2⟩
  · simp only [Bool.and_eq_true] at hr
    exact ⟨u,by rw [evalTest_sound hr.1]; exact evalTest_sound hr.2⟩

theorem image_self_sound {n : Nat} {x y : T}
    (h : imageWithin (scope n) x y x = true) : Image x y x := by
  rw [imageWithin.eq_def] at h
  simp only [Bool.or_eq_true] at h
  rcases h with ho | hr
  · exact ordinaryImage_sound ho
  · simp only [Bool.and_eq_true] at hr
    have he := evalTest_sound hr.1
    rw [q_square] at he
    cases he

theorem no_self_image_if_squares {x y : T}
    (hnext : ∀ a, ¬ Code (k x) a)
    (hself : ∀ t, x = k t → ∀ a, ¬ Code x a) : ¬ Image x y x := by
  rintro ⟨z,hz⟩
  rcases q_cases z x with hr | ⟨_,hk⟩ | ⟨hd,hv⟩
  · rw [hr] at hz
    have he : x = z := q_small_drop hz (by simp only [sz]; omega)
    subst z
    rw [q_square] at hr
    cases hr
  · rw [hk] at hz
    exact hnext y (q_small_output hz (by simp only [sz]; omega)).1
  · rw [hv] at hz
    have hw := drop_small_of_key (decode x) hd
    rcases q_cases y (drop x) with hp | ⟨_,hk⟩ | ⟨hc,hu⟩
    · have he : x = p y (drop x) := hz.symm.trans hp
      have hdrop : drop x = y := by rw [he]; rfl
      rw [hdrop,q_square] at hp
      cases hp
    · have he : x = k (drop x) := hz.symm.trans hk
      exact hself (drop x) he z hd
    · have hs := drop_small_of_key (decode (drop x)) hc
      have he : x = drop (drop x) := hz.symm.trans hu
      rw [←he] at hs
      omega

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem ordinary_drop_false {n : Nat} {x y u : T}
    (hu : u = drop x) (hs : sz u < sz x) (hn : n ≤ sz x + 1) :
    ¬ (ordinaryImage (scope n) x y u = true) := by
  intro h
  unfold ordinaryImage at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((ho | hsq) | hk) | hd) | hr
  · cases u with
    | e => cases ho
    | k t => cases ho
    | p first w =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at ho
      obtain ⟨z,hz⟩ := rightImageTest_sound ho.1.2
      have hw : sz w < sz x := by simp only [sz] at hs; omega
      have he := q_small_drop hz hw
      have he' : w = p first w := he.trans hu.symm
      have hb := congrArg sz he'
      simp only [sz] at hb; omega
  · simp only [Bool.and_eq_true,decide_eq_true_eq] at hsq
    obtain ⟨z,hz⟩ := rightImageTest_sound hsq.2
    have hy : sz y < sz x := by rw [hsq.1] at hs; simp only [sz] at hs; omega
    have he := q_small_drop hz hy
    have he' : y = k y := (he.trans hu.symm).trans hsq.1
    have hb := congrArg sz he'
    simp only [sz] at hb; omega
  · have hq := evalTest_sound hk
    have he := q_small_drop hq (by simp only [sz]; omega)
    change u = x at he
    rw [he] at hs; omega
  · simp only [Bool.and_eq_true] at hd
    have hq := evalTest_sound hd.2
    rw [←hu] at hq
    exact q_ne_right y u hq
  · simp only [Bool.and_eq_true] at hr
    have he := hr.2
    have hbad : ¬ sz (p u x) < n := by simp only [sz]; omega
    simp only [evalTest,hbad,↓reduceDIte] at he
    cases he

theorem image_drop_self {n : Nat} {x y u : T}
    (hu : u = drop x) (hs : sz u < sz x) (hn : n ≤ sz x + 1)
    (h : imageWithin (scope n) x y u = true) : Image u y u := by
  rw [imageWithin.eq_def] at h
  simp only [Bool.or_eq_true] at h
  rcases h with ho | hr
  · exact False.elim (ordinary_drop_false hu hs hn ho)
  · simp only [Bool.and_eq_true] at hr
    have ht := hr.2
    cases x with
    | e => cases ht
    | k c =>
      change (if c = y then imageWithin (scope n) u y c else false) = true at ht
      split at ht
      · have he : u = c := hu
        rw [←he] at ht
        exact image_self_sound ht
      · cases ht
    | p a c =>
      change (if c = y then imageWithin (scope n) u y a else false) = true at ht
      split at ht
      · have he : u = a := hu
        rw [←he] at ht
        exact image_self_sound ht
      · cases ht

theorem extra_square_false {n : Nat} {x a : T}
    (h : a ∈ (extraWithin (scope n) (k x)).terms) : False := by
  obtain ⟨y,hy,ha⟩ := (collect_mem _ _ _).mp h
  obtain ⟨he,_,hv,u,hu,_⟩ := (extraTest_mem _ _ _ _).mp ha
  have hc := ((codeKeys_mem u y).mp hu).2
  have hs := drop_small_of_key (decode y) hc
  have ht := extraKeys_bound (fun _ _ _ h => code_key_root h) hy
  rw [hv] at hs
  omega

theorem base_square_facts {n : Nat} {x a : T}
    (h : a ∈ (baseWithin (scope n) (k x)).terms) :
    ∃ y, imageWithin (scope n) x y (drop x) = true ∧ sz (drop x) < sz x := by
  cases x with
  | e => cases h
  | k y =>
    obtain ⟨_,_,hi⟩ := (candidate_mem _ _ _).mp h
    exact ⟨y,hi,by simp only [drop,sz]; omega⟩
  | p u y =>
    obtain ⟨_,_,hi⟩ := (candidate_mem _ _ _).mp h
    exact ⟨y,hi,by simp only [drop,sz]; omega⟩

theorem no_square_code_at (n : Nat) : ∀ x, sz (k x) = n → ∀ a, ¬ Code (k x) a := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x hn a ha
    rcases (decode_mem _ _).mp ha with hb | he
    · obtain ⟨y,hy,hsmall⟩ := base_square_facts hb
      have himage := image_drop_self rfl hsmall (by simp only [sz]; omega) hy
      have hnext : ∀ a, ¬ Code (k (drop x)) a :=
        ih (sz (k (drop x))) (by simp only [sz] at hn ⊢; omega) (drop x) rfl
      have hself : ∀ t, drop x = k t → ∀ a, ¬ Code (drop x) a := by
        intro t ht
        have hs := congrArg sz ht
        rw [ht]
        exact ih (sz (k t)) (by simp only [sz] at hn; omega) t rfl
      exact no_self_image_if_squares hnext hself himage
    · exact extra_square_false he

theorem no_square_code (x a : T) : ¬ Code (k x) a :=
  no_square_code_at (sz (k x)) x rfl a

theorem no_self_image (x y : T) : ¬ Image x y x :=
  no_self_image_if_squares (no_square_code x)
    (fun t ht => by rw [ht]; exact no_square_code t)

theorem no_self_image_test {n : Nat} (x y : T) : imageWithin (scope n) x y x = false := by
  cases h : imageWithin (scope n) x y x with
  | false => rfl
  | true => exact False.elim (no_self_image x y (image_self_sound h))

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem evalTest_complete {n : Nat} {a b out : T}
    (hb : sz b < n) (h : q a b = out) : evalTest (scope n) a b out = true := by
  simp only [evalTest,hb,↓reduceDIte]
  exact decide_eq_true h

theorem rightImageTest_complete {n : Nat} {b out : T}
    (hb : sz b < n) (h : ∃ a, q a b = out) : rightImageTest (scope n) b out = true := by
  simp only [rightImageTest,hb,↓reduceDIte]
  exact (rightImage_iff b out).mpr h

theorem codeKeys_nonempty_complete {n : Nat} {b a : T}
    (hb : sz b < n) (h : Code b a) : (!(codeKeys (scope n) b).isEmpty) = true := by
  have hm := (codeKeys_mem a b).mpr ⟨hb,h⟩
  cases ht : codeKeys (scope n) b with
  | nil => rw [ht] at hm; cases hm
  | cons t ts => rfl

theorem ordinaryImage_transfer {n m : Nat} {x y u : T}
    (hm : sz x + sz u + 2 < m) (h : ordinaryImage (scope n) x y u = true) :
    ordinaryImage (scope m) x y u = true := by
  unfold ordinaryImage at h ⊢
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with (((ho | hs) | hk) | hd) | hr
  · apply Or.inl; apply Or.inl; apply Or.inl; apply Or.inl
    cases u with
    | e => cases ho
    | k t => cases ho
    | p first w =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at ho ⊢
      exact ⟨⟨ho.1.1,rightImageTest_complete (by omega) (rightImageTest_sound ho.1.2)⟩,
        evalTest_complete (by simp only [sz] at hm; omega) (evalTest_sound ho.2)⟩
  · apply Or.inl; apply Or.inl; apply Or.inl; apply Or.inr
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hs ⊢
    exact ⟨hs.1,rightImageTest_complete (by omega) (rightImageTest_sound hs.2)⟩
  · apply Or.inl; apply Or.inl; apply Or.inr
    exact evalTest_complete (by simp only [sz]; omega) (evalTest_sound hk)
  · apply Or.inl; apply Or.inr
    simp only [Bool.and_eq_true] at hd ⊢
    obtain ⟨a,ha⟩ := codeKeys_nonempty hd.1
    have hb := drop_size_le x
    exact ⟨codeKeys_nonempty_complete (by omega) ha,
      evalTest_complete (by omega) (evalTest_sound hd.2)⟩
  · apply Or.inr
    simp only [Bool.and_eq_true] at hr ⊢
    exact ⟨evalTest_complete (by omega) (evalTest_sound hr.1),
      evalTest_complete (by simp only [sz]; omega) (evalTest_sound hr.2)⟩

theorem image_transfer_at (s : Nat) : ∀ {n m : Nat} (x y u : T), sz x + sz u = s →
    sz x + sz u + 2 < m → imageWithin (scope n) x y u = true →
    imageWithin (scope m) x y u = true := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro n m x y u hsize hm h
    rw [imageWithin.eq_def] at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with ho | hr
    · exact Or.inl (ordinaryImage_transfer hm ho)
    · apply Or.inr
      simp only [Bool.and_eq_true] at hr ⊢
      refine ⟨evalTest_complete (by omega) (evalTest_sound hr.1),?_⟩
      have ht := hr.2
      cases x with
      | e => cases ht
      | k c =>
        change (if c = y then imageWithin (scope n) u y c else false) = true at ht
        change (if c = y then imageWithin (scope m) u y c else false) = true
        split at ht
        · rename_i hc
          rw [if_pos hc]
          exact ih (sz u + sz c) (by simp only [sz] at hsize; omega) u y c rfl
            (by simp only [sz] at hm; omega) ht
        · cases ht
      | p a c =>
        change (if c = y then imageWithin (scope n) u y a else false) = true at ht
        change (if c = y then imageWithin (scope m) u y a else false) = true
        split at ht
        · rename_i hc
          rw [if_pos hc]
          exact ih (sz u + sz a) (by simp only [sz] at hsize; omega) u y a rfl
            (by simp only [sz] at hm; omega) ht
        · cases ht

theorem image_transfer {n m : Nat} {x y u : T} (hm : sz x + sz u + 2 < m)
    (h : imageWithin (scope n) x y u = true) : imageWithin (scope m) x y u = true :=
  image_transfer_at _ x y u rfl hm h

theorem image_sound {n : Nat} {x y u : T}
    (h : imageWithin (scope n) x y u = true) : Image x y u := by
  rw [imageWithin.eq_def] at h
  simp only [Bool.or_eq_true] at h
  rcases h with ho | hr
  · exact ordinaryImage_sound ho
  · simp only [Bool.and_eq_true] at hr
    have hraw := evalTest_sound hr.1
    have ht := hr.2
    refine ⟨u,?_⟩
    rw [hraw]
    cases x with
    | e => cases ht
    | k c =>
      change (if c = y then imageWithin (scope n) u y c else false) = true at ht
      split at ht
      · rename_i hc
        subst c
        have hi := image_transfer (m:=sz (p u (k y))) (by simp only [sz]; omega) ht
        exact q_hit (base_square_right hi)
      · cases ht
    | p a c =>
      change (if c = y then imageWithin (scope n) u y a else false) = true at ht
      split at ht
      · rename_i hc
        subst c
        have hi := image_transfer (m:=sz (p u (p a y))) (by simp only [sz]; omega) ht
        exact q_hit (base_pair hi)
      · cases ht

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem ordinary_of_raw {n : Nat} {x y w : T}
    (hx : sz x < n) (hw : sz w < n) (hi : ∃ z, q z x = w)
    (hq : q y w = p y w) : ordinaryImage (scope n) x y (p y w) = true := by
  have hr := rightImageTest_complete hx hi
  have he := evalTest_complete hw hq
  simp only [ordinaryImage,decide_true,hr,he,Bool.true_and,Bool.true_or]

theorem ordinary_of_square {n : Nat} {x y : T}
    (hx : sz x < n) (hi : ∃ z, q z x = y) : ordinaryImage (scope n) x y (k y) = true := by
  have hr := rightImageTest_complete hx hi
  simp only [ordinaryImage,decide_true,hr,Bool.and_self,Bool.false_or,Bool.true_or]

theorem ordinary_of_squareInput {n : Nat} {x y u : T}
    (hx : sz (k x) < n) (hq : q y (k x) = u) : ordinaryImage (scope n) x y u = true := by
  unfold ordinaryImage
  have he := evalTest_complete hx hq
  simp only [he,Bool.or_true,Bool.true_or]

theorem ordinary_of_decodedInput {n : Nat} {x y u z : T}
    (hx : sz x < n) (hc : Code x z) (hq : q y (drop x) = u) :
    ordinaryImage (scope n) x y u = true := by
  have hs := drop_size_le x
  have he := evalTest_complete (n:=n) (by omega) hq
  have hk := codeKeys_nonempty_complete hx hc
  simp only [ordinaryImage,he,hk,Bool.and_self,Bool.or_true,Bool.true_or]

theorem ordinary_of_recoveredInput {n : Nat} {x y u : T}
    (hx : sz (p u x) < n) (hr : q u x = p u x) (hq : q y (p u x) = u) :
    ordinaryImage (scope n) x y u = true := by
  have he := evalTest_complete (n:=n) (by simp only [sz] at hx; omega) hr
  have hk := evalTest_complete hx hq
  simp only [ordinaryImage,he,hk,Bool.and_self,Bool.or_true]

theorem ordinaryImage_complete {n : Nat} {x y u : T}
    (hn : sz x + sz u + 2 < n) (h : Image x y u) : ordinaryImage (scope n) x y u = true := by
  obtain ⟨z,hz⟩ := h
  rcases q_cases z x with hr | ⟨_,hk⟩ | ⟨hc,hd⟩
  · rw [hr] at hz
    rcases q_cases y (p z x) with hp | ⟨he,hs⟩ | ⟨_,hv⟩
    · have hu : u = p y (p z x) := hz.symm.trans hp
      rw [hu] at hn ⊢
      exact ordinary_of_raw (by omega) (by simp only [sz] at hn ⊢; omega) ⟨z,hr⟩ hp
    · have hu : u = k y := by rw [he]; exact hz.symm.trans hs
      rw [hu]
      exact ordinary_of_square (by omega) ⟨z,hr.trans he.symm⟩
    · have hu : u = z := hz.symm.trans hv
      subst z
      exact ordinary_of_recoveredInput (by simp only [sz]; omega) hr hz
  · rw [hk] at hz
    exact ordinary_of_squareInput (by simp only [sz]; omega) hz
  · rw [hd] at hz
    exact ordinary_of_decodedInput (by omega) hc hz

theorem image_of_ordinary {n : Nat} {x y u : T}
    (h : ordinaryImage (scope n) x y u = true) : imageWithin (scope n) x y u = true := by
  rw [imageWithin.eq_def]
  simp only [h,Bool.true_or]

theorem image_complete {n : Nat} {x y u : T}
    (hn : sz x + sz u + 2 < n) (h : Image x y u) : imageWithin (scope n) x y u = true :=
  image_of_ordinary (ordinaryImage_complete hn h)

theorem actual_image_key_bound {x y u : T} (h : Image x y u) : sz y < max (sz x) (sz u) :=
  image_key_bound (image_complete (n:=sz x + sz u + 3) (by omega) h)

theorem actual_image_not_both_small {x y u : T} (h : Image x y u)
    (hx : sz x ≤ sz y) (hu : sz u ≤ sz y) : False := by
  have hb := actual_image_key_bound h
  omega

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem base_pair_cases {n : Nat} {x v a : T}
    (h : a ∈ (baseWithin (scope n) (p x v)).terms) :
    (∃ u, v = p u a ∧ imageWithin (scope n) x a u = true) ∨
    (v = k a ∧ imageWithin (scope n) x a a = true) := by
  cases v with
  | e => cases h
  | k y =>
    obtain ⟨he,_,hi⟩ := (candidate_mem _ _ _).mp h
    subst a
    exact Or.inr ⟨rfl,hi⟩
  | p u y =>
    obtain ⟨he,_,hi⟩ := (candidate_mem _ _ _).mp h
    subst a
    exact Or.inl ⟨u,rfl,hi⟩

theorem extra_pair_facts {n : Nat} {x v a : T}
    (h : a ∈ (extraWithin (scope n) (p x v)).terms) :
    sz a < sz x ∧ drop a = v ∧ ∃ u, Code a u ∧ imageWithin (scope n) x a u = true := by
  obtain ⟨y,hy,ha⟩ := (collect_mem _ _ _).mp h
  obtain ⟨he,_,hv,u,hu,hi⟩ := (extraTest_mem _ _ _ _).mp ha
  subst a
  exact ⟨extraKeys_bound (fun _ _ _ h => code_key_root h) hy,hv,
    u,((codeKeys_mem u y).mp hu).2,hi⟩

theorem no_image_drop (x y : T) : ¬ Image x y (drop x) := by
  rintro ⟨z,hz⟩
  have hdrop := drop_size_le x
  rcases q_cases z x with hr | ⟨_,hk⟩ | ⟨_,hd⟩
  · rw [hr] at hz
    have hs : sz (drop x) < sz (p z x) := by simp only [sz]; omega
    obtain ⟨hc,he⟩ := q_small_output hz hs
    change drop x = z at he
    subst z
    rcases (decode_mem _ _).mp hc with hb | hx
    · rcases base_pair_cases hb with ⟨u,hu,hi⟩ | ⟨hy,hi⟩
      · have he : drop x = u := by rw [hu]; rfl
        rw [←he,no_self_image_test] at hi
        cases hi
      · have he : drop x = y := by rw [hy]; rfl
        rw [←he,no_self_image_test] at hi
        cases hi
    · obtain ⟨hy,hv,u,hu,_⟩ := extra_pair_facts hx
      have hs := drop_small_of_key (decode y) hu
      rw [hv] at hs
      omega
  · rw [hk] at hz
    exact no_square_code x y (q_small_output hz (by simp only [sz]; omega)).1
  · rw [hd] at hz
    exact q_ne_right y (drop x) hz

theorem no_diagonal_code (x a : T) : ¬ Code (p x x) a := by
  intro h
  rcases (decode_mem _ _).mp h with hb | he
  · rcases base_pair_cases hb with ⟨u,hu,hi⟩ | ⟨hx,hi⟩
    · have hd : u = drop x := by rw [hu]; rfl
      exact no_image_drop x a (by rw [←hd]; exact image_sound hi)
    · have hd : a = drop x := by rw [hx]; rfl
      exact no_image_drop x a (by rw [←hd]; exact image_sound hi)
  · obtain ⟨ha,hv,u,hu,_⟩ := extra_pair_facts he
    have hs := drop_small_of_key (decode a) hu
    rw [hv] at hs
    omega

theorem image_ne_third (x y u : T) (h : Image x y u) : x ≠ q u y := by
  intro he
  rcases q_cases u y with hr | ⟨hu,hk⟩ | ⟨hc,hd⟩
  · have hx := he.trans hr
    have hu : u = drop x := by rw [hx]; rfl
    exact no_image_drop x y (by rw [←hu]; exact h)
  · have hx := he.trans hk
    have hdrop : drop x = y := by rw [hx]; rfl
    have hout : drop x = u := hdrop.trans hu.symm
    exact no_image_drop x y (by rw [hout]; exact h)
  · have hs := drop_small_of_key (decode y) hc
    have ht := code_key_bound hc
    have hx := he.trans hd
    rw [←hx] at hs
    exact actual_image_not_both_small h (by omega) (by omega)

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem no_right_child_key (a b : T) : ¬ Code (p a b) b := by
  intro h
  rcases (decode_mem _ _).mp h with hb | he
  · rcases base_pair_cases hb with ⟨u,hu,_⟩ | ⟨hu,_⟩
    · have hs := congrArg sz hu
      simp only [sz] at hs; omega
    · have hs := congrArg sz hu
      simp only [sz] at hs; omega
  · obtain ⟨_,hd,u,hc,_⟩ := extra_pair_facts he
    have hs := drop_small_of_key (decode b) hc
    rw [hd] at hs; omega

theorem large_image_shape {x y u : T} (h : Image x y u) (hu : sz x ≤ sz u)
    (hc : ¬ Code (p u x) y) :
    (∃ w, u = p y w ∧ ∃ z, q z x = w) ∨ u = k y := by
  obtain ⟨z,hz⟩ := h
  rcases q_cases y (q z x) with hr | ⟨he,hk⟩ | ⟨hd,hv⟩
  · exact Or.inl ⟨q z x,hz.symm.trans hr,z,rfl⟩
  · exact Or.inr (by rw [←he] at hz hk; exact hz.symm.trans hk)
  · have hs := drop_small_of_key (decode (q z x)) hd
    have hout := hz.symm.trans hv
    rw [←hout] at hs
    rcases q_cases z x with hp | ⟨_,hk⟩ | ⟨hx,hq⟩
    · have he : u = z := by rw [hp] at hout; exact hout
      subst z
      rw [hp] at hd
      exact False.elim (hc hd)
    · rw [hk] at hd
      exact False.elim (no_square_code x y hd)
    · have ht := drop_small_of_key (decode x) hx
      rw [hq] at hs
      omega

theorem small_image_cases {u x t : T} (h : Image u x t) (ht : sz t < sz u) :
    Code (p t u) x ∨ (∃ z, Code u z ∧ q x (drop u) = t) := by
  obtain ⟨z,hz⟩ := h
  rcases q_cases z u with hr | ⟨_,hk⟩ | ⟨hc,hd⟩
  · rw [hr] at hz
    obtain ⟨hc,he⟩ := q_small_output hz (by simp only [sz]; omega)
    change t = z at he
    subst z
    exact Or.inl hc
  · rw [hk] at hz
    exact False.elim (no_square_code u x (q_small_output hz (by simp only [sz]; omega)).1)
  · exact Or.inr ⟨z,hc,by rw [hd] at hz; exact hz⟩

theorem image_triangle_false {x y u t : T}
    (h : Image x y u) (hr : Image u x t) (hu : sz x < sz u) (ht : sz t < sz u)
    (hc : ¬ Code (p u x) y) (hne : x ≠ y) (hlast : q x y ≠ t) : False := by
  have shape := large_image_shape h (by omega) hc
  have noEnd (a : T) : u ≠ p a x := by
    intro he
    rcases shape with ⟨w,hw,z,hz⟩ | hk
    · rw [he] at hw
      cases hw
      exact q_ne_right z x hz
    · rw [he] at hk; cases hk
  have noSquare : u ≠ k x := by
    intro he
    rcases shape with ⟨w,hw,_⟩ | hk
    · rw [he] at hw; cases hw
    · rw [he] at hk
      cases hk
      exact hne rfl
  rcases small_image_cases hr ht with hcode | ⟨z,hz,hq⟩
  · rcases (decode_mem _ _).mp hcode with hb | he
    · rcases base_pair_cases hb with ⟨a,ha,_⟩ | ⟨ha,_⟩
      · exact noEnd a ha
      · exact noSquare ha
    · obtain ⟨_,hd,a,ha,_⟩ := extra_pair_facts he
      have hs := drop_small_of_key (decode x) ha
      rw [hd] at hs; omega
  · rcases shape with ⟨w,hw,_⟩ | hk
    · rw [hw] at hq
      exact hlast hq
    · rw [hk] at hz
      exact no_square_code y z hz

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem primary_recovery_false {x y u t : T}
    (hy : y = p t x ∨ (y = k x ∧ t = x)) : ¬ Code (p u x) y := by
  intro h
  have hs : sz x < sz y := by
    rcases hy with hp | ⟨hk,_⟩
    · rw [hp]; simp only [sz]; omega
    · rw [hk]; simp only [sz]; omega
  rcases (decode_mem _ _).mp h with hb | he
  · rcases base_pair_cases hb with ⟨a,ha,_⟩ | ⟨ha,_⟩
    · have ht := congrArg sz ha
      simp only [sz] at ht; omega
    · have ht := congrArg sz ha
      simp only [sz] at ht; omega
  · obtain ⟨_,hd,a,ha,_⟩ := extra_pair_facts he
    rcases hy with hp | ⟨hk,_⟩
    · have ht : t = x := by rw [hp] at hd; exact hd
      rw [hp,ht] at ha
      exact no_diagonal_code x a ha
    · rw [hk] at ha
      exact no_square_code x a ha

theorem primary_last_false {x y t : T}
    (hy : y = p t x ∨ (y = k x ∧ t = x)) : q x y ≠ t := by
  intro h
  rcases hy with hp | ⟨hk,ht⟩
  · rw [hp] at h
    exact no_right_child_key t x (q_small_output h (by simp only [sz]; omega)).1
  · rw [hk,ht] at h
    exact no_square_code x x (q_small_output h (by simp only [sz]; omega)).1

theorem drop_recovery_false {x y u t : T} (hd : drop x = y) (ht : Code x t) :
    ¬ Code (p u x) y := by
  intro h
  have hs := drop_small_of_key (decode x) ht
  rw [hd] at hs
  rcases (decode_mem _ _).mp h with hb | he
  · rcases base_pair_cases hb with ⟨a,ha,_⟩ | ⟨ha,_⟩
    · have he : a = y := by rw [ha] at hd; exact hd
      rw [ha,he] at ht
      exact no_diagonal_code y t ht
    · rw [ha] at ht
      exact no_square_code y t ht
  · obtain ⟨_,hv,a,hc,_⟩ := extra_pair_facts he
    have hb := drop_small_of_key (decode y) hc
    rw [hv] at hb; omega

theorem drop_last_false {x y t : T} (hd : drop x = y) (ht : Code x t) : q x y ≠ t := by
  intro h
  have hi : Image x x t := ⟨t,by rw [q_hit ht,hd]; exact h⟩
  have hs := code_key_bound ht
  exact actual_image_not_both_small hi (by omega) (by omega)

theorem no_fourth_code {x y u : T} (h : Image x y u) : ¬ Code (q u y) x := by
  intro hc
  rcases q_cases u y with hr | ⟨_,hk⟩ | ⟨hu,hv⟩
  · rw [hr] at hc
    rcases (decode_mem _ _).mp hc with hb | he
    · have facts : ∃ t, (y = p t x ∨ (y = k x ∧ t = x)) ∧ Image u x t := by
        rcases base_pair_cases hb with ⟨t,ht,hi⟩ | ⟨hy,hi⟩
        · exact ⟨t,Or.inl ht,image_sound hi⟩
        · exact ⟨x,Or.inr ⟨hy,rfl⟩,image_sound hi⟩
      obtain ⟨t,hy,hi⟩ := facts
      have hs : sz x < sz y ∧ sz t < sz y := by
        rcases hy with hp | ⟨hk,ht⟩
        · rw [hp]; simp only [sz]; omega
        · rw [hk,ht]; simp only [sz]; omega
      have hb := actual_image_key_bound h
      exact image_triangle_false h hi (by omega) (by omega) (primary_recovery_false hy)
        (by intro he; rw [he] at hs; omega) (primary_last_false hy)
    · obtain ⟨hs,hd,t,ht,hi⟩ := extra_pair_facts he
      have hb := code_key_bound ht
      have hv := drop_small_of_key (decode x) ht
      rw [hd] at hv
      exact image_triangle_false h (image_sound hi) hs (by omega) (drop_recovery_false hd ht)
        (by intro he; rw [he] at hv; omega) (drop_last_false hd ht)
  · rw [hk] at hc
    exact no_square_code y x hc
  · have hs := code_key_bound hu
    have ht := code_key_bound hc
    have hb := drop_small_of_key (decode y) hu
    rw [hv] at ht
    exact actual_image_not_both_small h (by omega) (by omega)

theorem fourth_raw {x y u : T} (h : Image x y u) : q x (q u y) = p x (q u y) := by
  rcases q_cases x (q u y) with hr | ⟨he,_⟩ | ⟨hc,_⟩
  · exact hr
  · exact False.elim (image_ne_third x y u h he)
  · exact False.elim (no_fourth_code h hc)

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem q_small_left_output {a b out : T} (hq : q a b = out) (hs : sz out ≤ sz a) :
    Code b a ∧ out = drop b := by
  rcases q_cases a b with hr | ⟨he,hk⟩ | ⟨hc,hd⟩
  · rw [←hq,hr] at hs; simp only [sz] at hs; omega
  · rw [←hq,hk,he] at hs; simp only [sz] at hs; omega
  · exact ⟨hc,hq.symm.trans hd⟩

theorem extraKeys_root_pair {n : Nat} (a y : T) : y ∈ extraKeys (scope n) (p a y) := by
  unfold extraKeys
  apply List.mem_append.mpr; apply Or.inl
  apply List.mem_append.mpr; apply Or.inl
  simp

theorem extraKeys_drop {n : Nat} {x y z : T} (hn : sz x < n)
    (hx : Code x z) (hy : Code (drop x) y) : y ∈ extraKeys (scope n) x := by
  have hs := drop_size_le x
  have hm := (codeKeys_mem (n:=n) y (drop x)).mpr ⟨by omega,hy⟩
  have hk := codeKeys_nonempty_complete hn hx
  unfold extraKeys
  apply List.mem_append.mpr; apply Or.inr
  split
  · rename_i he
    rw [he] at hk; cases hk
  · exact hm

theorem contracting_recognition {n : Nat} {x y u : T}
    (hn : sz x + 1 < n) (h : Image x y u) (hu : Code y u) :
    imageWithin (scope n) x y u = true ∧ y ∈ extraKeys (scope n) x := by
  have hs := code_key_bound hu
  obtain ⟨z,hz⟩ := h
  rcases q_cases z x with hr | ⟨_,hk⟩ | ⟨hc,hd⟩
  · rw [hr] at hz
    obtain ⟨hy,he⟩ := q_small_left_output hz (by omega)
    change u = z at he
    subst z
    rcases (decode_mem _ _).mp hy with hb | he
    · rcases base_pair_cases hb with ⟨a,ha,hi⟩ | ⟨ha,hi⟩
      · subst x
        have hcap : sz u + sz a + 2 < n := by simp only [sz] at hn; omega
        have hnext := image_transfer hcap hi
        have hguard := evalTest_complete (n:=n) (by omega) hr
        refine ⟨?_,extraKeys_root_pair a y⟩
        rw [imageWithin.eq_def]
        simp only [hguard,↓reduceIte,hnext,Bool.and_self,Bool.or_true]
      · have hbound := image_key_bound hi
        omega
    · have hbound := (extra_pair_facts he).1
      omega
  · rw [hk] at hz
    exact False.elim (no_square_code x y (q_small_left_output hz (by omega)).1)
  · rw [hd] at hz
    have hy := (q_small_left_output hz (by omega)).1
    exact ⟨image_of_ordinary (ordinary_of_decodedInput (by omega) hc hz),
      extraKeys_drop (by omega) hc hy⟩

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587
open T

theorem final_key {x y u : T} (h : Image x y u) : Code (p x (q u y)) y := by
  rcases q_cases u y with hr | ⟨he,hk⟩ | ⟨hc,hd⟩
  · rw [hr]
    exact base_pair (image_complete (by simp only [sz]; omega) h)
  · rw [hk]
    apply base_square_right
    apply image_complete (by simp only [sz]; omega)
    subst u
    exact h
  · rw [hd]
    obtain ⟨hi,hy⟩ := contracting_recognition (n:=sz (p x (drop y)))
      (by simp only [sz]; omega) h hc
    have hb := actual_image_key_bound h
    have hs := code_key_bound hc
    exact extra_pair hy ((codeKeys_mem u y).mpr ⟨by simp only [sz]; omega,hc⟩) rfl hi

theorem source_from_image {x y u : T} (h : Image x y u) : q y (q x (q u y)) = x := by
  rw [fourth_raw h]
  exact q_hit (final_key h)

theorem equation7587 (x y z : T) : x = q y (q x (q (q y (q z x)) y)) :=
  (source_from_image ⟨z,rfl⟩).symm

end submission.Austin7587

set_option autoImplicit false
namespace submission.Austin7587

abbrev Carrier := T
def opposite (a b : T) : T := q b a

theorem equation38316 (x y z : T) :
    x = opposite (opposite (opposite y (opposite (opposite x z) y)) x) y :=
  equation7587 x y z

theorem infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op y (op x (op (op y (op z x)) y))) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨T,q,tower,equation7587,tower_injective⟩

theorem dual_infinite_model : ∃ (A : Type) (op : A → A → A) (f : Nat → A),
    (∀ x y z, x = op (op (op y (op (op x z) y)) x) y) ∧
    (∀ n j, f n = f j → n = j) :=
  ⟨T,opposite,tower,equation38316,tower_injective⟩

end submission.Austin7587

namespace submission
abbrev CM := Austin7587.Carrier
namespace CM
theorem tower_injective (n j : Nat)
    (h : Austin7587.tower n = Austin7587.tower j) : n = j :=
  Austin7587.tower_injective n j h
end CM
instance modelMagma : Magma CM := ⟨Austin7587.q⟩
end submission
theorem submission : Goal := by
  refine ⟨submission.CM, submission.modelMagma, ?_, ?_⟩
  · intro x y z
    exact submission.Austin7587.equation7587 x y z
  · intro h
    have bad : 0 = 1 := submission.Austin7587.tower_injective 0 1
      (h (submission.Austin7587.tower 0) (submission.Austin7587.tower 1))
    exact Nat.noConfusion bad
example : Goal := submission
#print axioms submission
#print axioms submission.CM.tower_injective

