prelude
import Init.Data.Option.Lemmas
import Init.Omega
import Init.RCases
import Init.WFTactics
import JudgeProblem
set_option Elab.async false

/- Checked module: TraceBasic -/
set_option autoImplicit false

namespace submission.Austin12087Trace

inductive T where
  | atom : Nat → T
  | s : T → T
  | p : T → T → T
  | c : T → T → T → T → T → T
  deriving DecidableEq

open T

def sz : T → Nat
  | atom _ => 1
  | s a => sz a + 1
  | p a b => sz a + sz b + 1
  | c y x z a b => sz y + sz x + sz z + sz a + sz b + 1

theorem sz_pos (a : T) : 0 < sz a := by cases a <;> simp only [sz] <;> omega

def rankM (a b : T) := 3 * max (sz a) (sz b) + 2
def rankI (a b : T) := 3 * max (sz a) (sz b) + 1

def origin : T → Option (T × T)
  | atom _ => none
  | s a => some (a,a)
  | p a b => some (a,b)
  | c _ _ _ a b => some (a,b)

theorem origin_size {t a b : T} (h : origin t = some (a,b)) :
    sz a < sz t ∧ sz b < sz t := by
  cases t <;> simp only [origin, Option.some.injEq, Prod.mk.injEq] at h
  · cases h
  all_goals rcases h with ⟨rfl,rfl⟩; simp only [sz]; omega

def leftCode (m i : T → T → Option T) (a b : T) : Option T :=
  match origin a with
  | none => none
  | some (u,z) => match m u z with
    | none => none
    | some value => if value = a then
        match i z b with
        | none => none
        | some x => match i x u with
          | none => none
          | some y => some (c y x z a b)
      else none

def rightCode (m i : T → T → Option T) (a b : T) : Option T :=
  match origin b with
  | none => none
  | some (x,z) => match m x z with
    | none => none
    | some value => if value = b then
        match i z a with
        | none => none
        | some u => match i x u with
          | none => none
          | some y => some (c y x z a b)
      else none

def decode (m i : T → T → Option T) (a b : T) : T :=
  match leftCode m i a b with
  | some out => out
  | none => (rightCode m i a b).getD (p a b)

def basicInverse (b out : T) : Option T :=
  match b with
  | c y x _ _ _ => if out = x then some y else none
  | _ => none

mutual
def mul (a b : T) : T :=
  if a = b then s a
  else
    let raw : T := decode
      (fun u v => if h : rankM u v < rankM a b then some (mul u v) else none)
      (fun u v => if h : rankI u v < rankM a b then inverse u v else none) a b
    match b with
    | c y x _ _ _ => if a = y then x else raw
    | _ => raw
termination_by rankM a b

def inverse (b out : T) : Option T :=
  if out = s b then some b
  else
    let rest := basicInverse b out
    match ho : out with
    | p a b' =>
        if b' = b then
          if h : rankM a b < rankI b out then
            if mul a b = out then some a else rest
          else rest
        else rest
    | c _ _ _ a b' =>
        if b' = b then
          if h : rankM a b < rankI b out then
            if mul a b = out then some a else rest
          else rest
        else rest
    | _ => rest
termination_by rankI b out
decreasing_by all_goals simpa only [ho] using h
end

def queryM (n : Nat) (a b : T) : Option T :=
  if rankM a b < n then some (mul a b) else none
def queryI (n : Nat) (a b : T) : Option T :=
  if rankI a b < n then inverse a b else none

theorem mul_equation (a b : T) : mul a b =
    if a = b then s a else
      match b with
      | c y x _ _ _ => if a = y then x else decode (queryM (rankM a b)) (queryI (rankM a b)) a b
      | _ => decode (queryM (rankM a b)) (queryI (rankM a b)) a b := by
  rw [mul.eq_def]
  rfl

theorem mul_square (a : T) : mul a a = s a := by
  rw [mul_equation]
  simp only [↓reduceIte]

theorem mul_code_return (y x z a b : T) : mul y (c y x z a b) = x := by
  have hn : y ≠ c y x z a b := by
    intro h
    have hs := congrArg sz h
    simp only [sz] at hs
    omega
  rw [mul_equation]
  simp only [hn,↓reduceIte]

theorem atom_injective (m n : Nat) (h : (atom m : T) = atom n) : m = n := T.atom.inj h

-- These total functions and local equations do not yet establish the source law.
end submission.Austin12087Trace


/- Checked module: TraceShape -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem leftCode_shape {m i : T → T → Option T} {a b out : T}
    (h : leftCode m i a b = some out) : ∃ y x z, out = c y x z a b := by
  cases ho : origin a with
  | none => simp only [leftCode,ho,Option.bind_none] at h; cases h
  | some uv =>
    rcases uv with ⟨u,z⟩
    cases hm : m u z with
    | none => simp only [leftCode,ho,hm,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none] at h; cases h
    | some v =>
      by_cases hv : v = a
      · cases hx : i z b with
        | none => simp only [leftCode,ho,hm,hv,hx,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
        | some x =>
          cases hy : i x u with
          | none => simp only [leftCode,ho,hm,hv,hx,hy,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
          | some y =>
            simp only [leftCode,ho,hm,hv,hx,hy,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte,Option.some.injEq] at h
            exact ⟨y,x,z,h.symm⟩
      · simp only [leftCode,ho,hm,hv,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte] at h; cases h

theorem rightCode_shape {m i : T → T → Option T} {a b out : T}
    (h : rightCode m i a b = some out) : ∃ y x z, out = c y x z a b := by
  cases ho : origin b with
  | none => simp only [rightCode,ho,Option.bind_none] at h; cases h
  | some xz =>
    rcases xz with ⟨x,z⟩
    cases hm : m x z with
    | none => simp only [rightCode,ho,hm,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none] at h; cases h
    | some v =>
      by_cases hv : v = b
      · cases hu : i z a with
        | none => simp only [rightCode,ho,hm,hv,hu,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
        | some u =>
          cases hy : i x u with
          | none => simp only [rightCode,ho,hm,hv,hu,hy,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
          | some y =>
            simp only [rightCode,ho,hm,hv,hu,hy,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte,Option.some.injEq] at h
            exact ⟨y,x,z,h.symm⟩
      · simp only [rightCode,ho,hm,hv,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte] at h; cases h

theorem decode_shape (m i : T → T → Option T) (a b : T) :
    decode m i a b = p a b ∨ ∃ y x z, decode m i a b = c y x z a b := by
  cases hl : leftCode m i a b with
  | some out =>
    obtain ⟨y,x,z,h⟩ := leftCode_shape hl
    exact Or.inr ⟨y,x,z,by simp only [decode,hl,h]⟩
  | none =>
    cases hr : rightCode m i a b with
    | some out =>
      obtain ⟨y,x,z,h⟩ := rightCode_shape hr
      exact Or.inr ⟨y,x,z,by simp only [decode,hl,hr,h,Option.getD_some]⟩
    | none => exact Or.inl (by simp only [decode,hl,hr,Option.getD_none])

theorem mul_cases (a b : T) :
    (a = b ∧ mul a b = s b) ∨
    (∃ x z l r, b = c a x z l r ∧ mul a b = x) ∨
    mul a b = p a b ∨ ∃ y x z, mul a b = c y x z a b := by
  by_cases he : a = b
  · subst b
    exact Or.inl ⟨rfl,mul_square a⟩
  · apply Or.inr
    have hd := decode_shape (queryM (rankM a b)) (queryI (rankM a b)) a b
    cases b with
    | c y x z l r =>
      by_cases hy : a = y
      · subst y
        exact Or.inl ⟨x,z,l,r,rfl,mul_code_return a x z l r⟩
      · apply Or.inr
        simpa only [mul_equation,he,hy,↓reduceIte] using hd
    | atom n => apply Or.inr; simpa only [mul_equation,he,↓reduceIte] using hd
    | s t => apply Or.inr; simpa only [mul_equation,he,↓reduceIte] using hd
    | p l r => apply Or.inr; simpa only [mul_equation,he,↓reduceIte] using hd

theorem mul_small_iff (a b : T) : sz (mul a b) < sz b ↔
    ∃ x z l r, b = c a x z l r := by
  constructor
  · intro hs
    rcases mul_cases a b with ⟨he,hm⟩ | ⟨x,z,l,r,hb,hm⟩ | hm | ⟨y,x,z,hm⟩
    · rw [hm] at hs; simp only [sz] at hs; omega
    · exact ⟨x,z,l,r,hb⟩
    · rw [hm] at hs; simp only [sz] at hs; omega
    · rw [hm] at hs; simp only [sz] at hs; omega
  · rintro ⟨x,z,l,r,rfl⟩
    rw [mul_code_return]; simp only [sz]; omega

theorem mul_ne_right (a b : T) : mul a b ≠ b := by
  intro h
  rcases mul_cases a b with ⟨he,hm⟩ | ⟨x,z,l,r,hb,hm⟩ | hm | ⟨y,x,z,hm⟩
  all_goals have hs := congrArg sz (hm.symm.trans h)
  · simp only [sz] at hs; omega
  · rw [hb] at hs; simp only [sz] at hs; omega
  · simp only [sz] at hs; omega
  · simp only [sz] at hs; omega

theorem mul_grows_or_returns (a b : T) :
    (sz a < sz (mul a b) ∧ sz b < sz (mul a b) ∧ origin (mul a b) = some (a,b)) ∨
    (∃ x z l r, b = c a x z l r ∧ mul a b = x) := by
  rcases mul_cases a b with ⟨he,hm⟩ | h | hm | ⟨y,x,z,hm⟩
  · subst b; exact Or.inl (by rw [hm]; simp only [sz,origin]; exact ⟨by omega,by omega,True.intro⟩)
  · exact Or.inr h
  · exact Or.inl (by rw [hm]; simp only [sz,origin]; exact ⟨by omega,by omega,True.intro⟩)
  · exact Or.inl (by rw [hm]; simp only [sz,origin]; exact ⟨by omega,by omega,True.intro⟩)

end submission.Austin12087Trace

/- Checked module: TraceInverse -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem basicInverse_cases {b out a : T} (h : basicInverse b out = some a) :
    ∃ z l r, b = c a out z l r := by
  cases b with
  | c y x z l r =>
    by_cases he : out = x
    · simp only [basicInverse,he,↓reduceIte,Option.some.injEq] at h
      exact ⟨z,l,r,by rw [h,he]⟩
    · simp only [basicInverse,he,↓reduceIte] at h; cases h
  | atom n => cases h
  | s t => cases h
  | p l r => cases h

theorem inverse_cases {b out a : T} (h : inverse b out = some a) :
    (a = b ∧ out = s b) ∨
    (origin out = some (a,b) ∧ mul a b = out) ∨ basicInverse b out = some a := by
  by_cases hs : out = s b
  · have ha : b = a := by simpa only [inverse.eq_def,hs,↓reduceIte,Option.some.injEq] using h
    exact Or.inl ⟨ha.symm,hs⟩
  · apply Or.inr
    cases out with
    | atom n => exact Or.inr (by simpa only [inverse.eq_def,hs,↓reduceIte] using h)
    | s t => exact Or.inr (by simpa only [inverse.eq_def,hs,↓reduceIte] using h)
    | p l r =>
      by_cases hr : r = b
      · subst r
        have hk : rankM l b < rankI b (p l b) := by simp only [rankM,rankI,sz]; omega
        by_cases hm : mul l b = p l b
        · have ha : l = a := by simpa only [inverse.eq_def,reduceCtorEq,hk,hm,↓reduceIte,↓reduceDIte,Option.some.injEq] using h
          exact Or.inl ⟨by rw [origin,ha],by rw [←ha]; exact hm⟩
        · exact Or.inr (by simpa only [inverse.eq_def,reduceCtorEq,hk,hm,↓reduceIte,↓reduceDIte] using h)
      · exact Or.inr (by simpa only [inverse.eq_def,hs,hr,↓reduceIte] using h)
    | c y x z l r =>
      by_cases hr : r = b
      · subst r
        have hk : rankM l b < rankI b (c y x z l b) := by simp only [rankM,rankI,sz]; omega
        by_cases hm : mul l b = c y x z l b
        · have ha : l = a := by simpa only [inverse.eq_def,reduceCtorEq,hk,hm,↓reduceIte,↓reduceDIte,Option.some.injEq] using h
          exact Or.inl ⟨by rw [origin,ha],by rw [←ha]; exact hm⟩
        · exact Or.inr (by simpa only [inverse.eq_def,reduceCtorEq,hk,hm,↓reduceIte,↓reduceDIte] using h)
      · exact Or.inr (by simpa only [inverse.eq_def,hs,hr,↓reduceIte] using h)

theorem inverse_size {b out a : T} (h : inverse b out = some a) :
    sz a ≤ max (sz b) (sz out) := by
  rcases inverse_cases h with ⟨rfl,_⟩ | ⟨ho,_⟩ | hb
  · omega
  · have hs := origin_size ho; omega
  · obtain ⟨z,l,r,hb⟩ := basicInverse_cases hb
    rw [hb]; simp only [sz]; omega

theorem inverse_sound {b out a : T} (h : inverse b out = some a) : mul a b = out := by
  rcases inverse_cases h with ⟨rfl,rfl⟩ | ⟨_,hm⟩ | hb
  · exact mul_square _
  · exact hm
  · obtain ⟨z,l,r,rfl⟩ := basicInverse_cases hb
    exact mul_code_return a out z l r

theorem inverse_square (b : T) : inverse b (s b) = some b := by
  rw [inverse.eq_def]
  simp only [↓reduceIte]

theorem inverse_raw {a b : T} (h : mul a b = p a b) : inverse b (p a b) = some a := by
  have hk : rankM a b < rankI b (p a b) := by
    simp only [rankM,rankI,sz]; omega
  rw [inverse.eq_def]
  simp only [reduceCtorEq,↓reduceIte,↓reduceDIte,hk,h]

theorem inverse_code {y x z a b : T} (h : mul a b = c y x z a b) :
    inverse b (c y x z a b) = some a := by
  have hk : rankM a b < rankI b (c y x z a b) := by
    simp only [rankM,rankI,sz]; omega
  rw [inverse.eq_def]
  simp only [reduceCtorEq,↓reduceIte,↓reduceDIte,hk,h]

theorem inverse_small {b out : T} (hs : sz out < sz b) :
    inverse b out = basicInverse b out := by
  have hn : out ≠ s b := by
    intro he; rw [he] at hs; simp only [sz] at hs; omega
  cases out with
  | atom n => rw [inverse.eq_def]; simp only [hn,↓reduceIte]
  | s t => rw [inverse.eq_def]; simp only [hn,↓reduceIte]
  | p l r =>
    have hr : r ≠ b := by
      intro he; rw [he] at hs; simp only [sz] at hs; omega
    rw [inverse.eq_def]; simp only [hn,hr,↓reduceIte]
  | c y x z l r =>
    have hr : r ≠ b := by
      intro he; rw [he] at hs; simp only [sz] at hs; omega
    rw [inverse.eq_def]; simp only [hn,hr,↓reduceIte]

theorem inverse_complete (a b : T) : inverse b (mul a b) = some a := by
  rcases mul_cases a b with ⟨he,hm⟩ | ⟨x,z,l,r,hb,hm⟩ | hm | ⟨y,x,z,hm⟩
  · subst b; rw [mul_square,inverse_square]
  · rw [hm,hb]
    rw [inverse_small (by simp only [sz]; omega)]
    simp only [basicInverse,↓reduceIte]
  · rw [hm]; exact inverse_raw hm
  · rw [hm]; exact inverse_code hm

theorem right_injective (a b z : T) (h : mul a z = mul b z) : a = b := by
  have hi := congrArg (inverse z) h
  rw [inverse_complete,inverse_complete] at hi
  exact Option.some.inj hi

end submission.Austin12087Trace

/- Checked module: TraceColumns -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem distinct_outputs_large_origin {a b u x z : T}
    (ha : mul u z = a) (hb : mul x z = b) (hne : a ≠ b) (hs : sz b ≤ sz a) :
    origin a = some (u,z) ∧ sz z < sz a := by
  rcases mul_grows_or_returns u z with ⟨hu,hz,ho⟩ | ⟨v,t,l,r,hz,hv⟩
  · exact ⟨by rw [←ha]; exact ho,by rw [←ha]; exact hz⟩
  · have hav : a = v := ha.symm.trans hv
    have has : sz a < sz z := by rw [hav,hz]; simp only [sz]; omega
    have hbs : sz (mul x z) < sz z := by rw [hb]; omega
    obtain ⟨v',t',l',r',hz'⟩ := (mul_small_iff x z).mp hbs
    have hux : u = x := (T.c.inj (hz.symm.trans hz')).1
    exact False.elim (hne (ha.symm.trans ((congrArg (fun k => mul k z) hux).trans hb)))

theorem common_column_key_unique {a b u x z v w t : T}
    (ha : mul u z = a) (hb : mul x z = b)
    (ha' : mul v t = a) (hb' : mul w t = b) (hne : a ≠ b) : z = t := by
  by_cases hs : sz b ≤ sz a
  · have h1 := (distinct_outputs_large_origin ha hb hne hs).1
    have h2 := (distinct_outputs_large_origin ha' hb' hne hs).1
    exact (Prod.mk.inj (Option.some.inj (h1.symm.trans h2))).2
  · have hsa : sz a ≤ sz b := by omega
    have h1 := (distinct_outputs_large_origin hb ha (Ne.symm hne) hsa).1
    have h2 := (distinct_outputs_large_origin hb' ha' (Ne.symm hne) hsa).1
    exact (Prod.mk.inj (Option.some.inj (h1.symm.trans h2))).2

theorem common_column_data_unique {a b y x z y' x' z' : T}
    (ha : mul (mul y x) z = a) (hb : mul x z = b)
    (ha' : mul (mul y' x') z' = a) (hb' : mul x' z' = b) :
    y = y' ∧ x = x' ∧ z = z' := by
  have hne : a ≠ b := by
    intro h
    have hu := right_injective (mul y x) x z (ha.trans (h.trans hb.symm))
    exact mul_ne_right y x hu
  have hz := common_column_key_unique ha hb ha' hb' hne
  subst z'
  have hx := right_injective x x' z (hb.trans hb'.symm)
  subst x'
  have hu := right_injective (mul y x) (mul y' x) z (ha.trans ha'.symm)
  exact ⟨right_injective y y' x hu,rfl,rfl⟩

theorem queryM_sound {n : Nat} {a b out : T} (h : queryM n a b = some out) : mul a b = out := by
  by_cases hn : rankM a b < n
  · simpa only [queryM,hn,↓reduceIte,Option.some.injEq] using h
  · simp only [queryM,hn,↓reduceIte] at h; cases h

theorem queryI_sound {n : Nat} {a b out : T} (h : queryI n a b = some out) : inverse a b = some out := by
  by_cases hn : rankI a b < n
  · simpa only [queryI,hn,↓reduceIte] using h
  · simp only [queryI,hn,↓reduceIte] at h; cases h

theorem leftCode_complete {a b y x z : T}
    (ho : origin a = some (mul y x,z))
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    leftCode (queryM (rankM a b)) (queryI (rankM a b)) a b = some (c y x z a b) := by
  have hos := origin_size ho
  have hxb := inverse_size (inverse_complete x z)
  rw [hb] at hxb
  have hm : rankM (mul y x) z < rankM a b := by simp only [rankM]; omega
  have hi : rankI z b < rankM a b := by simp only [rankI,rankM]; omega
  have hi' : rankI x (mul y x) < rankM a b := by simp only [rankI,rankM]; omega
  have ix : inverse z b = some x := by rw [←hb]; exact inverse_complete x z
  have iy : inverse x (mul y x) = some y := inverse_complete y x
  simp only [leftCode,ho,queryM,queryI,hm,hi,hi',ha,ix,iy,↓reduceIte]

theorem rightCode_complete {a b y x z : T}
    (ho : origin b = some (x,z))
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    rightCode (queryM (rankM a b)) (queryI (rankM a b)) a b = some (c y x z a b) := by
  have hos := origin_size ho
  have hub := inverse_size (inverse_complete (mul y x) z)
  rw [ha] at hub
  have hm : rankM x z < rankM a b := by simp only [rankM]; omega
  have hi : rankI z a < rankM a b := by simp only [rankI,rankM]; omega
  have hi' : rankI x (mul y x) < rankM a b := by simp only [rankI,rankM]; omega
  have iu : inverse z a = some (mul y x) := by rw [←ha]; exact inverse_complete (mul y x) z
  have iy : inverse x (mul y x) = some y := inverse_complete y x
  simp only [rightCode,ho,queryM,queryI,hm,hi,hi',hb,iu,iy,↓reduceIte]

end submission.Austin12087Trace

/- Checked module: TraceCodes -/
set_option autoImplicit false
namespace submission.Austin12087Trace
open T

theorem leftCode_witness {m i : T → T → Option T} {a b out : T}
    (h : leftCode m i a b = some out) : ∃ u z x y, origin a = some (u,z) ∧ m u z = some a ∧ i z b = some x ∧ i x u = some y ∧ out = c y x z a b := by
  cases ho : origin a with
  | none => simp only [leftCode,ho,Option.bind_none] at h; cases h
  | some uv =>
    rcases uv with ⟨u,z⟩
    cases hm : m u z with
    | none => simp only [leftCode,ho,hm,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none] at h; cases h
    | some v =>
      by_cases hv : v = a
      · cases hx : i z b with
        | none => simp only [leftCode,ho,hm,hv,hx,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
        | some x =>
          cases hy : i x u with
          | none => simp only [leftCode,ho,hm,hv,hx,hy,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
          | some y =>
            simp only [leftCode,ho,hm,hv,hx,hy,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte,Option.some.injEq] at h
            exact ⟨u,z,x,y,rfl,hm.trans (congrArg some hv),by simp only [hx],hy,h.symm⟩
      · simp only [leftCode,ho,hm,hv,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte] at h; cases h

theorem rightCode_witness {m i : T → T → Option T} {a b out : T}
    (h : rightCode m i a b = some out) : ∃ x z u y, origin b = some (x,z) ∧ m x z = some b ∧ i z a = some u ∧ i x u = some y ∧ out = c y x z a b := by
  cases ho : origin b with
  | none => simp only [rightCode,ho,Option.bind_none] at h; cases h
  | some xz =>
    rcases xz with ⟨x,z⟩
    cases hm : m x z with
    | none => simp only [rightCode,ho,hm,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none] at h; cases h
    | some v =>
      by_cases hv : v = b
      · cases hu : i z a with
        | none => simp only [rightCode,ho,hm,hv,hu,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
        | some u =>
          cases hy : i x u with
          | none => simp only [rightCode,ho,hm,hv,hu,hy,Option.bind_some,Prod.fst,Prod.snd,Option.bind_none,↓reduceIte] at h; cases h
          | some y =>
            simp only [rightCode,ho,hm,hv,hu,hy,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte,Option.some.injEq] at h
            exact ⟨x,z,u,y,rfl,hm.trans (congrArg some hv),by simp only [hu],hy,h.symm⟩
      · simp only [rightCode,ho,hm,hv,Option.bind_some,Prod.fst,Prod.snd,↓reduceIte] at h; cases h

theorem leftCode_sound {n : Nat} {a b out : T}
    (h : leftCode (queryM n) (queryI n) a b = some out) :
    ∃ y x z, out = c y x z a b ∧ mul (mul y x) z = a ∧ mul x z = b := by
  obtain ⟨u,z,x,y,ho,hm,hx,hy,he⟩ := leftCode_witness h
  have hu := inverse_sound (queryI_sound hy)
  exact ⟨y,x,z,he,by rw [hu]; exact queryM_sound hm,inverse_sound (queryI_sound hx)⟩

theorem rightCode_sound {n : Nat} {a b out : T}
    (h : rightCode (queryM n) (queryI n) a b = some out) :
    ∃ y x z, out = c y x z a b ∧ mul (mul y x) z = a ∧ mul x z = b := by
  obtain ⟨x,z,u,y,ho,hm,hu,hy,he⟩ := rightCode_witness h
  have huy := inverse_sound (queryI_sound hy)
  exact ⟨y,x,z,he,by rw [huy]; exact inverse_sound (queryI_sound hu),queryM_sound hm⟩

theorem decode_source {a b y x z : T}
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    decode (queryM (rankM a b)) (queryI (rankM a b)) a b = c y x z a b := by
  have hn : a ≠ b := by
    intro h
    exact mul_ne_right y x (right_injective (mul y x) x z (ha.trans (h.trans hb.symm)))
  cases hl : leftCode (queryM (rankM a b)) (queryI (rankM a b)) a b with
  | some out =>
    obtain ⟨y',x',z',he,ha',hb'⟩ := leftCode_sound hl
    obtain ⟨hy,hx,hz⟩ := common_column_data_unique ha hb ha' hb'
    simp only [decode,hl,he,hy,hx,hz]
  | none =>
    have hs : sz a ≤ sz b := by
      by_cases h : sz a ≤ sz b
      · exact h
      have hs' : sz b ≤ sz a := by omega
      have ho := (distinct_outputs_large_origin ha hb hn hs').1
      have hc := leftCode_complete ho ha hb
      rw [hl] at hc
      cases hc
    have ho := (distinct_outputs_large_origin hb ha (Ne.symm hn) hs).1
    have hc := rightCode_complete ho ha hb
    simp only [decode,hl,hc,Option.getD_some]

end submission.Austin12087Trace

/- Checked module: TraceSource -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

def Source12087 (x y z : T) : Prop :=
  x = mul y (mul (mul (mul y x) z) (mul x z))
def Law12087 : Prop := ∀ x y z : T, Source12087 x y z

theorem middle_cases (y x z : T) :
    mul (mul (mul y x) z) (mul x z) =
      c y x z (mul (mul y x) z) (mul x z) ∨
    ∃ q t l r, mul x z = c (mul (mul y x) z) q t l r ∧
      mul (mul (mul y x) z) (mul x z) = q := by
  generalize ha : mul (mul y x) z = a
  generalize hb : mul x z = b
  have hne : a ≠ b := by
    intro h
    exact mul_ne_right y x (right_injective (mul y x) x z (ha.trans (h.trans hb.symm)))
  have hd := decode_source ha hb
  cases b with
  | c y' q t l r =>
    by_cases he : a = y'
    · subst y'
      exact Or.inr ⟨q,t,l,r,rfl,mul_code_return a q t l r⟩
    · exact Or.inl (by simpa only [mul_equation,hne,he,↓reduceIte] using hd)
  | atom n => exact Or.inl (by simpa only [mul_equation,hne,↓reduceIte] using hd)
  | s t => exact Or.inl (by simpa only [mul_equation,hne,↓reduceIte] using hd)
  | p l r => exact Or.inl (by simpa only [mul_equation,hne,↓reduceIte] using hd)

theorem source_without_middle_return (x y z : T)
    (hn : ∀ q t l r, mul x z ≠ c (mul (mul y x) z) q t l r) : Source12087 x y z := by
  rcases middle_cases y x z with hc | ⟨q,t,l,r,hb,hm⟩
  · unfold Source12087
    rw [hc,mul_code_return]
  · exact False.elim (hn q t l r hb)

def CriticalReturn : Prop := ∀ x y z q t l r : T,
  mul x z = c (mul (mul y x) z) q t l r → mul y q = x

theorem law_iff_critical_return : Law12087 ↔ CriticalReturn := by
  constructor
  · intro h x y z q t l r hb
    have hs := h x y z
    unfold Source12087 at hs
    rw [hb,mul_code_return] at hs
    exact hs.symm
  · intro h x y z
    rcases middle_cases y x z with hc | ⟨q,t,l,r,hb,hm⟩
    · unfold Source12087
      rw [hc,mul_code_return]
    · unfold Source12087
      rw [hm]
      exact (h x y z q t l r hb).symm

theorem decode_generic_sound {n : Nat} {a b y x z : T}
    (h : decode (queryM n) (queryI n) a b = c y x z a b) :
    mul (mul y x) z = a ∧ mul x z = b := by
  cases hl : leftCode (queryM n) (queryI n) a b with
  | some out =>
    have he : out = c y x z a b := by simpa only [decode,hl] using h
    obtain ⟨y',x',z',he',ha,hb⟩ := leftCode_sound hl
    obtain ⟨hy,hx,hz,_,_⟩ := T.c.inj (he'.symm.trans he)
    simpa only [hy,hx,hz] using And.intro ha hb
  | none =>
    cases hr : rightCode (queryM n) (queryI n) a b with
    | none => simp only [decode,hl,hr,Option.getD_none] at h; cases h
    | some out =>
      have he : out = c y x z a b := by simpa only [decode,hl,hr,Option.getD_some] using h
      obtain ⟨y',x',z',he',ha,hb⟩ := rightCode_sound hr
      obtain ⟨hy,hx,hz,_,_⟩ := T.c.inj (he'.symm.trans he)
      simpa only [hy,hx,hz] using And.intro ha hb

theorem mul_code_semantics {y x z a b : T} (h : mul a b = c y x z a b) :
    mul (mul y x) z = a ∧ mul x z = b := by
  have hn : a ≠ b := by intro he; subst b; rw [mul_square] at h; cases h
  apply decode_generic_sound (n:=rankM a b)
  cases b with
  | atom n => simpa only [mul_equation,hn,↓reduceIte] using h
  | s t => simpa only [mul_equation,hn,↓reduceIte] using h
  | p l r => simpa only [mul_equation,hn,↓reduceIte] using h
  | c y' q t l r =>
    by_cases hy : a = y'
    · subst y'
      rw [mul_code_return] at h
      have hs := congrArg sz h
      simp only [sz] at hs
      omega
    · simpa only [mul_equation,hn,hy,↓reduceIte] using h

theorem critical_return_trace {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r) :
    l = x ∧ r = z ∧
    mul (mul (mul (mul y x) z) q) t = x ∧ mul q t = z := by
  have hn : mul (mul y x) z ≠ mul x z := by
    intro he
    exact mul_ne_right y x (right_injective (mul y x) x z he)
  have hs : sz (mul (mul y x) z) ≤ sz (mul x z) := by
    rw [h]; simp only [sz]; omega
  have ho := (distinct_outputs_large_origin (a:=mul x z) (b:=mul (mul y x) z)
    rfl rfl (Ne.symm hn) hs).1
  rw [h,origin] at ho
  have hp := Prod.mk.inj (Option.some.inj ho)
  rcases hp with ⟨hl,hr⟩
  subst l; subst r
  exact ⟨rfl,rfl,(mul_code_semantics h).1,(mul_code_semantics h).2⟩

theorem critical_return_is_small_first {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r) :
    sz (mul y x) < sz x ∨ sz (mul (mul y x) z) < sz z ∨
      sz (mul (mul (mul y x) z) q) < sz q ∨ sz x < sz t := by
  obtain ⟨hl,hr,hx,hz⟩ := critical_return_trace h
  rcases mul_grows_or_returns y x with ⟨_,h1,_⟩ | h1
  · rcases mul_grows_or_returns (mul y x) z with ⟨h2,_,_⟩ | h2
    · rcases mul_grows_or_returns (mul (mul y x) z) q with ⟨h3,_,_⟩ | h3
      · rcases mul_grows_or_returns (mul (mul (mul y x) z) q) t with ⟨h4,_,_⟩ | h4
        · rw [hx] at h4; omega
        · obtain ⟨v,s,a,b,ht,hm⟩ := h4
          apply Or.inr; apply Or.inr; apply Or.inr
          rw [←hx,hm,ht]; simp only [sz]; omega
      · obtain ⟨v,s,a,b,hq,hm⟩ := h3
        exact Or.inr (Or.inr (Or.inl ((mul_small_iff _ _).mpr ⟨v,s,a,b,hq⟩)))
    · obtain ⟨v,s,a,b,hz,hm⟩ := h2
      exact Or.inr (Or.inl ((mul_small_iff _ _).mpr ⟨v,s,a,b,hz⟩))
  · obtain ⟨v,s,a,b,hx,hm⟩ := h1
    exact Or.inl ((mul_small_iff _ _).mpr ⟨v,s,a,b,hx⟩)

-- CriticalReturn has NOT been established here. No model is registered.
end submission.Austin12087Trace

/- Checked module: TraceCritical -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem inverse_strict_size {b out a : T} (h : inverse b out = some a) :
    sz a < max (sz b) (sz out) := by
  rcases inverse_cases h with ⟨rfl,rfl⟩ | ⟨ho,_⟩ | hb
  · simp only [sz]; omega
  · have hs := origin_size ho; omega
  · obtain ⟨z,l,r,hb⟩ := basicInverse_cases hb
    rw [hb]; simp only [sz]; omega

theorem common_column_inputs_small {a b y x z : T}
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    sz y < max (sz a) (sz b) ∧ sz x < max (sz a) (sz b) ∧ sz z < max (sz a) (sz b) := by
  have hn : a ≠ b := by
    intro h
    exact mul_ne_right y x (right_injective (mul y x) x z (ha.trans (h.trans hb.symm)))
  have ix := inverse_strict_size (inverse_complete x z)
  have iu := inverse_strict_size (inverse_complete (mul y x) z)
  have iy := inverse_strict_size (inverse_complete y x)
  rw [ha] at iu; rw [hb] at ix
  by_cases hs : sz b ≤ sz a
  · have ho := (distinct_outputs_large_origin ha hb hn hs).1
    have hsz := origin_size ho
    exact ⟨by omega,by omega,by omega⟩
  · have hs' : sz a ≤ sz b := by omega
    have ho := (distinct_outputs_large_origin hb ha (Ne.symm hn) hs').1
    have hsz := origin_size ho
    exact ⟨by omega,by omega,by omega⟩

theorem code_choices_agree {n : Nat} {a b v w : T}
    (hl : leftCode (queryM n) (queryI n) a b = some v)
    (hr : rightCode (queryM n) (queryI n) a b = some w) : v = w := by
  obtain ⟨y,x,z,hv,ha,hb⟩ := leftCode_sound hl
  obtain ⟨y',x',z',hw,ha',hb'⟩ := rightCode_sound hr
  obtain ⟨hy,hx,hz⟩ := common_column_data_unique ha hb ha' hb'
  rw [hv,hw,hy,hx,hz]

theorem critical_first_or_second_return {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r) :
    sz (mul y x) < sz x ∨ sz (mul (mul y x) z) < sz z := by
  obtain ⟨hl,hr,hx,hz⟩ := critical_return_trace h
  have bound := (common_column_inputs_small hx hz).1
  rcases mul_grows_or_returns y x with ⟨_,h1,_⟩ | ⟨v,s,a,b,hx',hm⟩
  · rcases mul_grows_or_returns (mul y x) z with ⟨h2,h3,_⟩ | ⟨v,s,a,b,hz',hm⟩
    · omega
    · exact Or.inr ((mul_small_iff _ _).mpr ⟨v,s,a,b,hz'⟩)
  · exact Or.inl ((mul_small_iff _ _).mpr ⟨v,s,a,b,hx'⟩)

theorem source_when_first_two_do_not_return (x y z : T)
    (h1 : sz x ≤ sz (mul y x))
    (h2 : sz z ≤ sz (mul (mul y x) z)) : Source12087 x y z := by
  apply source_without_middle_return
  intro q t l r h
  rcases critical_first_or_second_return h with hs | hs <;> omega

def PlainRight : T → Prop
  | c _ _ _ _ _ => False
  | _ => True

theorem plain_right_grows (a b : T) (h : PlainRight b) : sz b < sz (mul a b) := by
  rcases mul_grows_or_returns a b with hg | ⟨x,z,l,r,hb,hm⟩
  · exact hg.2.1
  · rw [hb] at h; exact False.elim h

theorem source_for_plain_right_inputs (x y z : T) (hx : PlainRight x) (hz : PlainRight z) :
    Source12087 x y z :=
  source_when_first_two_do_not_return x y z
    (Nat.le_of_lt (plain_right_grows y x hx))
    (Nat.le_of_lt (plain_right_grows (mul y x) z hz))

theorem source_square_parameters (a y b : T) : Source12087 (s a) y (s b) :=
  source_for_plain_right_inputs (s a) y (s b) True.intro True.intro

end submission.Austin12087Trace

/- Checked module: TraceOrient -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem critical_x_max {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r)
    (hs : sz z ≤ sz x) :
    ∃ k, x = c y (mul y x) k (mul (mul (mul y x) z) q) t ∧
      mul (mul y (mul y x)) k = mul (mul (mul y x) z) q ∧
      mul (mul y x) k = t := by
  obtain ⟨_,_,hx,hz⟩ := critical_return_trace h
  have hb := common_column_inputs_small hx hz
  have hu := inverse_strict_size (inverse_complete (mul y x) z)
  have hu' : sz (mul y x) < sz x := by omega
  obtain ⟨v,k,a,b,he⟩ := (mul_small_iff y x).mp hu'
  have hv : v = mul y x := by rw [he,mul_code_return]
  subst v
  have hn : mul (mul (mul y x) z) q ≠ q := mul_ne_right _ _
  have hne : x ≠ z := by
    intro heq
    exact hn (right_injective _ _ t (hx.trans (heq.trans hz.symm)))
  have ho := (distinct_outputs_large_origin hx hz hne hs).1
  conv at ho => lhs; rw [he,origin]
  obtain ⟨ha,hb'⟩ := Prod.mk.inj (Option.some.inj ho)
  subst a; subst b
  have hd := mul_code_semantics (hx.trans he)
  exact ⟨k,he,hd.1,hd.2⟩

theorem critical_z_max {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r)
    (hs : sz x ≤ sz z) :
    ∃ k, z = c (mul y x) (mul (mul y x) z) k q t ∧
      mul (mul (mul y x) (mul (mul y x) z)) k = q ∧
      mul (mul (mul y x) z) k = t := by
  obtain ⟨_,_,hx,hz⟩ := critical_return_trace h
  have hb := (common_column_inputs_small hx hz).1
  have ha : sz (mul (mul y x) z) < sz z := by omega
  obtain ⟨v,k,a,b,he⟩ := (mul_small_iff (mul y x) z).mp ha
  have hv : v = mul (mul y x) z := by rw [he,mul_code_return]
  subst v
  have hn : mul (mul (mul y x) z) q ≠ q := mul_ne_right _ _
  have hne : z ≠ x := by
    intro heq
    exact hn (right_injective _ _ t (hx.trans (heq.symm.trans hz.symm)))
  have ho := (distinct_outputs_large_origin hz hx hne hs).1
  conv at ho => lhs; rw [he,origin]
  obtain ⟨ha',hb'⟩ := Prod.mk.inj (Option.some.inj ho)
  subst a; subst b
  have hd := mul_code_semantics (hz.trans he)
  exact ⟨k,he,hd.1,hd.2⟩

-- These are proposed sufficient conditions, not established lemmas.
def FirstCycleAbsent : Prop := ∀ u q k : T,
  (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none

def SecondCycleAbsent : Prop := ∀ u a k : T,
  inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none

theorem critical_excluded_by_three_parameter_queries
    (hf : FirstCycleAbsent) (hs : SecondCycleAbsent)
    {x y z q t l r : T}
    (h : mul x z = c (mul (mul y x) z) q t l r) : False := by
  obtain ⟨_,_,hx,hz⟩ := critical_return_trace h
  by_cases hsz : sz z ≤ sz x
  · obtain ⟨k,_,hv,ht⟩ := critical_x_max h hsz
    have h1 := inverse_complete (mul y (mul y x)) k
    rw [hv] at h1
    have h2 := inverse_complete y (mul y x)
    have he := hf (mul y x) q k
    rw [ht,hz,h1,Option.bind_some,h2] at he
    cases he
  · obtain ⟨k,_,hq,ht⟩ := critical_z_max h (by omega)
    have he := hs (mul y x) (mul (mul y x) z) k
    rw [hq,ht,hx,inverse_complete] at he
    cases he

theorem law_of_three_parameter_query_absence
    (hf : FirstCycleAbsent) (hs : SecondCycleAbsent) : Law12087 := by
  intro x y z
  apply source_without_middle_return
  intro q t l r h
  exact critical_excluded_by_three_parameter_queries hf hs h

end submission.Austin12087Trace

/- Checked module: TraceCycle -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem no_transposed_code (a b k : T) : mul a b ≠ c b a k a b := by
  intro h
  have hc := mul_code_semantics h
  have hs := common_column_inputs_small hc.1 hc.2
  omega

theorem no_cross_two_cycle (a b : T) : mul b (mul a b) ≠ a := by
  intro h
  have hi := inverse_strict_size (inverse_complete b (mul a b))
  rw [h] at hi
  rcases mul_grows_or_returns a b with hg | ⟨v,k,l,r,hb,hv⟩
  · have hs : sz (mul b (mul a b)) < sz (mul a b) := by rw [h]; exact hg.1
    obtain ⟨v,k,l,r,hv⟩ := (mul_small_iff b (mul a b)).mp hs
    have he : v = a := by rw [hv,mul_code_return] at h; exact h
    subst v
    have ho := hg.2.2
    conv at ho => lhs; rw [hv,origin]
    obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
    subst l; subst r
    exact no_transposed_code a b k hv
  · rw [hv,hb] at hi
    simp only [sz] at hi
    omega

theorem cross_two_cycle_inverse_absent (a b : T) :
    inverse (mul a b) a ≠ some b := by
  intro h
  exact no_cross_two_cycle a b (inverse_sound h)

end submission.Austin12087Trace

/- Checked module: TraceDescent -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem mul_origin_of_right_le {a b : T}
    (h : sz b ≤ sz (mul a b)) : origin (mul a b) = some (a,b) := by
  rcases mul_grows_or_returns a b with hg | ⟨v,k,l,r,hb,hv⟩
  · exact hg.2.2
  · rw [hv,hb] at h; simp only [sz] at h; omega

theorem row_column_collision_return {a z y : T}
    (he : mul a z = mul y a) (hn : z ≠ a) :
    ∃ k l r, z = c a (mul y a) k l r := by
  rcases mul_grows_or_returns a z with hg | ⟨v,k,l,r,hz,hv⟩
  · have hs : sz a ≤ sz (mul y a) := by rw [←he]; omega
    have ho := mul_origin_of_right_le hs
    rw [←he,hg.2.2] at ho
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact False.elim (hn hp.2)
  · exact ⟨k,l,r,by rw [←he,hv]; exact hz⟩

-- A diagonal first-query witness forces a strictly smaller second-query
-- witness. This is one descent branch, not the complete induction.
theorem first_diagonal_descent_trace {u k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul k (mul u k))) k) :
    ∃ a h, sz (mul u k) < sz k ∧ sz u < sz k ∧ sz a < sz k ∧ sz h < sz k ∧
      mul y (mul (mul a (mul (mul u a) h)) (mul a h)) = u ∧
      mul k (mul u k) = c u a h k (mul u k) := by
  let t := mul u k
  let z := mul k t
  let a := mul y u
  have ha : mul u z = a := (right_injective _ _ k hf).symm
  have hn : a ≠ u := mul_ne_right y u
  have hzu : z ≠ u := no_cross_two_cycle u k
  obtain ⟨h,l,r,hz⟩ := row_column_collision_return ha hzu
  change z = c u a h l r at hz
  have hzus : sz u < sz z := by rw [hz]; simp only [sz]; omega
  have hza : sz a < sz z := by rw [hz]; simp only [sz]; omega
  have hzlarge : sz t ≤ sz z := by
    by_cases hc : sz t ≤ sz z
    · exact hc
    apply False.elim
    have hsmall : sz (mul k t) < sz t := by change sz z < sz t; omega
    obtain ⟨v,j,b,c,ht⟩ := (mul_small_iff k t).mp hsmall
    have hv : v = z := by change v = mul k t; rw [ht,mul_code_return]
    subst v
    have htk : sz k ≤ sz t := by rw [ht]; simp only [sz]; omega
    have hot := mul_origin_of_right_le (a:=u) (b:=k) htk
    change origin t = some (u,k) at hot
    conv at hot => lhs; rw [ht,origin]
    obtain ⟨hb,hc⟩ := Prod.mk.inj (Option.some.inj hot)
    subst b; subst c
    have htsem := mul_code_semantics (show mul u k = c k z j u k from ht)
    have hbnd := common_column_inputs_small htsem.1 htsem.2
    omega
  have hoz := mul_origin_of_right_le (a:=k) (b:=t) hzlarge
  change origin z = some (k,t) at hoz
  conv at hoz => lhs; rw [hz,origin]
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hoz)
  subst l; subst r
  have hzsem := mul_code_semantics (show mul k t = c u a h k t from hz)
  have hk : mul (mul u a) h = k := hzsem.1
  have ht : mul a h = t := hzsem.2
  have hbnd := common_column_inputs_small hk ht
  have htk : sz t < sz k := by
    by_cases hc : sz t < sz k
    · exact hc
    apply False.elim
    have hot := mul_origin_of_right_le (a:=u) (b:=k) (by change sz k ≤ sz t; omega)
    change origin t = some (u,k) at hot
    have hh : sz h ≤ sz (mul a h) := by rw [ht]; omega
    have hot' := mul_origin_of_right_le hh
    rw [ht,hot] at hot'
    have hp := Prod.mk.inj (Option.some.inj hot')
    exact hn hp.1.symm
  have hu : sz u < sz k := by omega
  have haa : sz a < sz k := by omega
  have hh : sz h < sz k := by omega
  obtain ⟨v,j,l,r,hkr⟩ := (mul_small_iff u k).mp htk
  have hvk : sz k < sz (mul a k) := by
    rcases mul_grows_or_returns a k with hg | ⟨v',j',l',r',hkr',_⟩
    · exact hg.2.1
    · have hp := T.c.inj (hkr.symm.trans hkr')
      exact False.elim (hn hp.1.symm)
  have hs : Source12087 u y k := by
    apply source_without_middle_return
    intro q j l r he
    have hb : sz (mul (mul y u) k) < sz (mul u k) := by
      rw [he]; simp only [sz]; omega
    change sz (mul a k) < sz t at hb
    omega
  have hy : mul y (mul (mul a k) t) = u := hs.symm
  exact ⟨a,h,htk,hu,haa,hh,(by rw [hk,ht]; exact hy),hz⟩

theorem first_diagonal_descent {u k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul k (mul u k))) k) :
    ∃ a h, sz (mul u k) < sz k ∧ sz u < sz k ∧ sz a < sz k ∧ sz h < sz k ∧
      mul y (mul (mul a (mul (mul u a) h)) (mul a h)) = u := by
  obtain ⟨a,h,ht,hu,ha,hh,he,_⟩ := first_diagonal_descent_trace hf
  exact ⟨a,h,ht,hu,ha,hh,he⟩

theorem first_diagonal_query_absent_for_plain_parameter (u k : T) (hp : PlainRight k) :
    (inverse k (mul (mul u (mul k (mul u k))) k)).bind (inverse u) = none := by
  cases h1 : inverse k (mul (mul u (mul k (mul u k))) k) with
  | none => rfl
  | some w =>
    cases h2 : inverse u w with
    | none => exact h2
    | some y =>
      have hw := inverse_sound h1
      have hy := inverse_sound h2
      rw [←hy] at hw
      obtain ⟨a,h,htk,_⟩ := first_diagonal_descent hw
      have hg := plain_right_grows u k hp
      exact False.elim (by omega)

theorem first_diagonal_query_absent_of_smaller_second (u k : T)
    (hs : ∀ a h : T, sz u < sz k → sz a < sz k → sz h < sz k →
      inverse (mul (mul a (mul (mul u a) h)) (mul a h)) u = none) :
    (inverse k (mul (mul u (mul k (mul u k))) k)).bind (inverse u) = none := by
  cases h1 : inverse k (mul (mul u (mul k (mul u k))) k) with
  | none => rfl
  | some w =>
    cases h2 : inverse u w with
    | none => exact h2
    | some y =>
      have hw := inverse_sound h1
      have hy := inverse_sound h2
      rw [←hy] at hw
      obtain ⟨a,h,_,hu,ha,hh,he⟩ := first_diagonal_descent hw
      have hi := inverse_complete y (mul (mul a (mul (mul u a) h)) (mul a h))
      rw [he,hs a h hu ha hh] at hi
      cases hi

end submission.Austin12087Trace

/- Checked module: TraceColumnReturn -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem distinct_columns_larger_returns {a b q k v : T}
    (ha : mul a q = v) (hb : mul b k = v) (hn : q ≠ k)
    (hs : sz q ≤ sz k) : ∃ h l r, k = c b v h l r := by
  rcases mul_grows_or_returns b k with hg | ⟨w,h,l,r,hk,hw⟩
  · have hq : sz q ≤ sz (mul a q) := by rw [ha,←hb]; omega
    have ho := mul_origin_of_right_le hq
    rw [ha,←hb,hg.2.2] at ho
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact False.elim (hn hp.2.symm)
  · exact ⟨h,l,r,by rw [hb] at hw; rw [←hw] at hk; exact hk⟩

theorem different_plain_columns_disjoint {a b q k : T}
    (hq : PlainRight q) (hk : PlainRight k) (hn : q ≠ k) :
    mul a q ≠ mul b k := by
  intro he
  by_cases hs : sz q ≤ sz k
  · obtain ⟨h,l,r,hc⟩ := distinct_columns_larger_returns he rfl hn hs
    rw [hc] at hk; exact hk
  · obtain ⟨h,l,r,hc⟩ := distinct_columns_larger_returns he.symm rfl (Ne.symm hn) (by omega)
    rw [hc] at hq; exact hq

theorem first_offdiagonal_larger_k_return {u q k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hn : q ≠ k) (hs : sz q ≤ sz k) :
    (∃ h l r, k = c (mul y u) (mul (mul y u) k) h l r) ∧
    sz u < sz (mul u k) ∧ sz k < sz (mul u k) ∧
      origin (mul u k) = some (u,k) := by
  obtain ⟨h,l,r,hc⟩ := distinct_columns_larger_returns hf.symm rfl hn hs
  refine ⟨⟨h,l,r,hc⟩,?_⟩
  rcases mul_grows_or_returns u k with hg | ⟨v,j,l',r',hc',_⟩
  · exact hg
  · have hp := T.c.inj (hc.symm.trans hc')
    exact False.elim (mul_ne_right y u hp.1)

theorem first_offdiagonal_larger_q_return {u q k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hn : q ≠ k) (hs : sz k ≤ sz q) :
    ∃ h l r, q = c (mul u (mul q (mul u k))) (mul (mul y u) k) h l r := by
  exact distinct_columns_larger_returns rfl hf.symm (Ne.symm hn) hs

theorem first_query_absent_for_plain_parameters (u q k : T)
    (hq : PlainRight q) (hk : PlainRight k) :
    (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none := by
  by_cases hn : q = k
  · subst q
    exact first_diagonal_query_absent_for_plain_parameter u k hk
  · cases h1 : inverse k (mul (mul u (mul q (mul u k))) q) with
    | none => rfl
    | some w =>
      cases h2 : inverse u w with
      | none => exact h2
      | some y =>
        have hw := inverse_sound h1
        have hy := inverse_sound h2
        rw [←hy] at hw
        exact False.elim (different_plain_columns_disjoint hq hk hn hw.symm)

end submission.Austin12087Trace

/- Checked module: TraceNormal -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

-- Every non-square composite must be its recorded actual multiplication.
-- The atom/square clauses retain an explicit infinite supply of elements.
inductive NF : T → Prop where
  | atom (n : Nat) : NF (T.atom n)
  | square {a : T} : NF a → NF (s a)
  | pair {a b : T} : NF a → NF b → mul a b = p a b → NF (p a b)
  | code {y x z a b : T} : NF y → NF x → NF z → NF a → NF b →
      mul a b = c y x z a b → NF (c y x z a b)

theorem nf_origin {out a b : T} (hn : NF out) (ho : origin out = some (a,b)) :
    NF a ∧ NF b := by
  cases hn with
  | atom n => simp only [origin] at ho; cases ho
  | square ht =>
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact ⟨hp.1 ▸ ht,hp.2 ▸ ht⟩
  | pair hl hr hm =>
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact ⟨hp.1 ▸ hl,hp.2 ▸ hr⟩
  | code hy hx hz hl hr hm =>
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact ⟨hp.1 ▸ hl,hp.2 ▸ hr⟩

theorem nf_inverse {b out a : T} (hb : NF b) (ho : NF out)
    (hi : inverse b out = some a) : NF a := by
  rcases inverse_cases hi with ⟨he,_⟩ | ⟨hor,_⟩ | hbasic
  · exact he ▸ hb
  · exact (nf_origin ho hor).1
  · obtain ⟨z,l,r,hb'⟩ := basicInverse_cases hbasic
    rw [hb'] at hb
    cases hb with
    | code ha _ _ _ _ _ => exact ha

theorem nf_common_column_parameters {a b y x z : T}
    (ha : NF a) (hb : NF b)
    (hma : mul (mul y x) z = a) (hmb : mul x z = b) : NF y ∧ NF x ∧ NF z := by
  have hn : a ≠ b := by
    intro he
    exact mul_ne_right y x (right_injective _ _ z (hma.trans (he.trans hmb.symm)))
  have hz : NF z := by
    by_cases hs : sz b ≤ sz a
    · exact (nf_origin ha (distinct_outputs_large_origin hma hmb hn hs).1).2
    · exact (nf_origin hb (distinct_outputs_large_origin hmb hma (Ne.symm hn) (by omega)).1).2
  have hx : NF x := nf_inverse hz hb (by rw [←hmb]; exact inverse_complete x z)
  have hu : NF (mul y x) := nf_inverse hz ha (by rw [←hma]; exact inverse_complete _ z)
  exact ⟨nf_inverse hx hu (inverse_complete y x),hx,hz⟩

theorem nf_mul {a b : T} (ha : NF a) (hb : NF b) : NF (mul a b) := by
  rcases mul_cases a b with ⟨_,hm⟩ | ⟨x,z,l,r,hb',hm⟩ | hm | ⟨y,x,z,hm⟩
  · rw [hm]; exact NF.square hb
  · rw [hm]
    have hcode : NF (c a x z l r) := hb' ▸ hb
    cases hcode with
    | code _ hx _ _ _ _ => exact hx
  · rw [hm]; exact NF.pair ha hb hm
  · have hc := mul_code_semantics hm
    obtain ⟨hy,hx,hz⟩ := nf_common_column_parameters ha hb hc.1 hc.2
    rw [hm]; exact NF.code hy hx hz ha hb hm

theorem nf_code_actual {y x z a b : T} (h : NF (c y x z a b)) :
    NF y ∧ NF x ∧ NF z ∧ NF a ∧ NF b ∧
      mul a b = c y x z a b ∧ mul (mul y x) z = a ∧ mul x z = b := by
  cases h with
  | code hy hx hz ha hb hm =>
    exact ⟨hy,hx,hz,ha,hb,hm,mul_code_semantics hm⟩

def NormalTree := {a : T // NF a}

def normalMul (a b : NormalTree) : NormalTree := ⟨mul a.val b.val,nf_mul a.property b.property⟩

def normalAtom (n : Nat) : NormalTree := ⟨T.atom n,NF.atom n⟩

theorem normalAtom_injective {m n : Nat} (h : normalAtom m = normalAtom n) : m = n :=
  T.atom.inj (congrArg Subtype.val h)

theorem normalAtom_nontrivial : normalAtom 0 ≠ normalAtom 1 := by
  intro h
  have he := normalAtom_injective h
  omega

theorem normal_law_of_nf_source
    (h : ∀ x y z : T, NF x → NF y → NF z → Source12087 x y z) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) := by
  intro x y z
  apply Subtype.ext
  exact h x.val y.val z.val x.property y.property z.property

-- Closure and infinitude do not establish the source law on this carrier.
end submission.Austin12087Trace

/- Checked module: TraceNormalQueries -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

def NormalFirstCycleAbsent : Prop := ∀ u q k : T, NF u → NF q → NF k →
  (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none

def NormalSecondCycleAbsent : Prop := ∀ u a k : T, NF u → NF a → NF k →
  inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none

theorem normal_first_diagonal_descent {u k y : T} (hu : NF u) (hk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul k (mul u k))) k) :
    ∃ a h, NF a ∧ NF h ∧ sz u < sz k ∧ sz a < sz k ∧ sz h < sz k ∧
      mul y (mul (mul a (mul (mul u a) h)) (mul a h)) = u := by
  obtain ⟨a,h,_,hus,has,hhs,he,hcode⟩ := first_diagonal_descent_trace hf
  have hz := nf_mul hk (nf_mul hu hk)
  rw [hcode] at hz
  have hn := nf_code_actual hz
  exact ⟨a,h,hn.2.1,hn.2.2.1,hus,has,hhs,he⟩

theorem normal_first_diagonal_absent_of_smaller_second (u k : T)
    (hu : NF u) (hk : NF k)
    (hs : ∀ a h : T, NF a → NF h → sz u < sz k → sz a < sz k → sz h < sz k →
      inverse (mul (mul a (mul (mul u a) h)) (mul a h)) u = none) :
    (inverse k (mul (mul u (mul k (mul u k))) k)).bind (inverse u) = none := by
  cases h1 : inverse k (mul (mul u (mul k (mul u k))) k) with
  | none => rfl
  | some w =>
    cases h2 : inverse u w with
    | none => exact h2
    | some y =>
      have hw := inverse_sound h1
      have hy := inverse_sound h2
      rw [←hy] at hw
      obtain ⟨a,h,ha,hh,hus,has,hhs,he⟩ := normal_first_diagonal_descent hu hk hw
      have hi := inverse_complete y (mul (mul a (mul (mul u a) h)) (mul a h))
      rw [he,hs a h ha hh hus has hhs] at hi
      cases hi

theorem nf_critical_parameters {x y z q t l r : T}
    (hx : NF x) (hy : NF y) (hz : NF z)
    (he : mul x z = c (mul (mul y x) z) q t l r) :
    NF (mul y x) ∧ NF (mul (mul y x) z) ∧ NF q ∧ NF t := by
  have hu := nf_mul hy hx
  have ha := nf_mul hu hz
  have hb := nf_mul hx hz
  rw [he] at hb
  have hc := nf_code_actual hb
  exact ⟨hu,ha,hc.2.1,hc.2.2.1⟩

theorem normal_critical_excluded_by_queries
    (hf : NormalFirstCycleAbsent) (hs : NormalSecondCycleAbsent)
    {x y z q t l r : T}
    (hnx : NF x) (hny : NF y) (hnz : NF z)
    (he : mul x z = c (mul (mul y x) z) q t l r) : False := by
  obtain ⟨_,_,hx,hz⟩ := critical_return_trace he
  obtain ⟨hnu,hna,hnq,_⟩ := nf_critical_parameters hnx hny hnz he
  by_cases hsz : sz z ≤ sz x
  · obtain ⟨k,hcode,hv,ht⟩ := critical_x_max he hsz
    have hnx' := hnx
    rw [hcode] at hnx'
    have hnk := (nf_code_actual hnx').2.2.1
    have h1 := inverse_complete (mul y (mul y x)) k
    rw [hv] at h1
    have h2 := inverse_complete y (mul y x)
    have hquery := hf (mul y x) q k hnu hnq hnk
    rw [ht,hz,h1,Option.bind_some,h2] at hquery
    cases hquery
  · obtain ⟨k,hcode,hq,ht⟩ := critical_z_max he (by omega)
    have hnz' := hnz
    rw [hcode] at hnz'
    have hnk := (nf_code_actual hnz').2.2.1
    have hquery := hs (mul y x) (mul (mul y x) z) k hnu hna hnk
    rw [hq,ht,hx,inverse_complete] at hquery
    cases hquery

theorem nf_source_of_normal_queries
    (hf : NormalFirstCycleAbsent) (hs : NormalSecondCycleAbsent)
    (x y z : T) (hx : NF x) (hy : NF y) (hz : NF z) : Source12087 x y z := by
  apply source_without_middle_return
  intro q t l r he
  exact normal_critical_excluded_by_queries hf hs hx hy hz he

theorem normal_law_of_normal_queries
    (hf : NormalFirstCycleAbsent) (hs : NormalSecondCycleAbsent) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) :=
  normal_law_of_nf_source (nf_source_of_normal_queries hf hs)

-- The two normal query-absence statements are still open. No law instance or
-- InfiniteModel certificate is declared by this conditional bridge.
end submission.Austin12087Trace

/- Checked module: TraceFold -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem no_untransposed_code (a b k : T) : mul a b ≠ c a b k a b := by
  intro h
  have hc := mul_code_semantics h
  have hs := common_column_inputs_small hc.1 hc.2
  omega

theorem no_left_two_cycle (a b : T) : mul a (mul a b) ≠ b := by
  intro he
  rcases mul_grows_or_returns a b with hg | ⟨v,k,l,r,hb,hv⟩
  · have hs : sz (mul a (mul a b)) < sz (mul a b) := by rw [he]; exact hg.2.1
    obtain ⟨v,k,l,r,hv⟩ := (mul_small_iff a (mul a b)).mp hs
    have hvb : v = b := by rw [hv,mul_code_return] at he; exact he
    subst v
    have ho := hg.2.2
    conv at ho => lhs; rw [hv,origin]
    obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
    subst l; subst r
    exact no_untransposed_code a b k hv
  · have hav : mul a v = b := by rw [hv] at he; exact he
    have hs : sz v ≤ sz (mul a v) := by rw [hav,hb]; simp only [sz]; omega
    have ho := mul_origin_of_right_le hs
    rw [hav,hb,origin] at ho
    obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
    subst l; subst r
    exact no_untransposed_code a v k (hav.trans hb)

def FoldWitness (u a t j : T) : Prop :=
  mul u a = mul (mul u t) j ∧ mul a (mul t j) = t

theorem fold_right_larger {u a t j : T} (hf : FoldWitness u a t j) :
    sz (mul u a) < sz (mul t j) := by
  obtain ⟨hw,ht⟩ := hf
  have hb := common_column_inputs_small hw.symm (show mul t j = mul t j from rfl)
  have ha := inverse_strict_size (inverse_complete a (mul t j))
  rw [ht] at ha
  by_cases hs : sz (mul u a) < sz (mul t j)
  · exact hs
  apply False.elim
  have hwa : sz a ≤ sz (mul u a) := by omega
  have hwj : sz j ≤ sz (mul (mul u t) j) := by rw [←hw]; omega
  have ho := mul_origin_of_right_le hwa
  have ho' := mul_origin_of_right_le hwj
  rw [←hw,ho] at ho'
  have hp := Prod.mk.inj (Option.some.inj ho')
  rw [←hp.2] at ht
  exact no_cross_two_cycle t a ht

theorem fold_outer_trace {u a t j : T} (hf : FoldWitness u a t j) :
    ∃ h, mul t j = c a t h t j ∧ mul (mul a t) h = t ∧ mul t h = j ∧
      sz a < sz j ∧ sz t < sz j ∧ sz h < sz j := by
  obtain ⟨hw,ht⟩ := hf
  have hwb := fold_right_larger ⟨hw,ht⟩
  have hb := common_column_inputs_small hw.symm (show mul t j = mul t j from rfl)
  have hsmall : sz (mul a (mul t j)) < sz (mul t j) := by rw [ht]; omega
  obtain ⟨v,h,l,r,hc⟩ := (mul_small_iff a (mul t j)).mp hsmall
  have hvt : v = t := by rw [hc,mul_code_return] at ht; exact ht
  subst v
  have hbj : sz j ≤ sz (mul t j) := by omega
  have ho := mul_origin_of_right_le hbj
  conv at ho => lhs; rw [hc,origin]
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst r
  have hsem := mul_code_semantics hc
  have hbound := common_column_inputs_small hsem.1 hsem.2
  exact ⟨h,hc,hsem.1,hsem.2,by omega,by omega,by omega⟩

theorem normal_first_diagonal_fold_descent {u k y : T} (hu : NF u) (hk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul k (mul u k))) k) :
    ∃ a t j, NF a ∧ NF t ∧ NF j ∧
      sz u < sz k ∧ sz a < sz k ∧ sz t < sz k ∧ sz j < sz k ∧ FoldWitness u a t j := by
  obtain ⟨a,h,hts,hus,has,hhs,_,hz⟩ := first_diagonal_descent_trace hf
  have hnz := nf_mul hk (nf_mul hu hk)
  rw [hz] at hnz
  have hn := nf_code_actual hnz
  have hs := mul_code_semantics hz
  have hka : mul (mul u a) h = k := hs.1
  have hat : mul a h = mul u k := hs.2
  obtain ⟨t,j,l,r,hkc⟩ := (mul_small_iff u k).mp hts
  have htt : t = mul u k := by rw [hkc,mul_code_return]
  have hok := mul_origin_of_right_le (a:=mul u a) (b:=h) (by rw [hka]; omega)
  rw [hka] at hok
  conv at hok => lhs; rw [hkc,origin]
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hok)
  subst l; subst r
  have hks := mul_code_semantics (hka.trans hkc)
  have hnk := hk
  rw [hkc] at hnk
  have hnj := (nf_code_actual hnk).2.2.1
  have hnt : NF t := htt.symm ▸ nf_mul hu hk
  have hj : sz j < sz k := by rw [hkc]; simp only [sz]; omega
  have hft : FoldWitness u a t j := by
    refine ⟨hks.1.symm,?_⟩
    rw [hks.2]
    exact hat.trans htt.symm
  exact ⟨a,t,j,hn.2.1,hnt,hnj,hus,has,by rw [htt]; exact hts,hj,hft⟩

end submission.Austin12087Trace

/- Checked module: TraceHeight -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

def ht : T → Nat
  | atom _ => 1
  | s a => ht a + 1
  | p a b => max (ht a) (ht b) + 1
  | c y x z a b => max (ht y) (max (ht x) (max (ht z) (max (ht a) (ht b)))) + 1

theorem origin_height {out a b : T} (h : origin out = some (a,b)) :
    ht a < ht out ∧ ht b < ht out := by
  cases out with
  | atom n => simp only [origin] at h; cases h
  | s t =>
    obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj h)
    subst a; subst b; simp only [ht]; omega
  | p l r =>
    obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj h)
    subst a; subst b; simp only [ht]; omega
  | c y x z l r =>
    obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj h)
    subst a; subst b; simp only [ht]; omega

theorem mul_height_shape (a b : T) :
    (ht a < ht (mul a b) ∧ ht b < ht (mul a b) ∧ origin (mul a b) = some (a,b)) ∨
    ∃ x z l r, b = c a x z l r ∧ mul a b = x := by
  rcases mul_grows_or_returns a b with hg | hr
  · have hh := origin_height hg.2.2
    exact Or.inl ⟨hh.1,hh.2,hg.2.2⟩
  · exact Or.inr hr

theorem inverse_height_strict {b out a : T} (h : inverse b out = some a) :
    ht a < max (ht b) (ht out) := by
  rcases inverse_cases h with ⟨rfl,rfl⟩ | ⟨ho,_⟩ | hb
  · simp only [ht]; omega
  · have hh := origin_height ho; omega
  · obtain ⟨z,l,r,hb⟩ := basicInverse_cases hb
    rw [hb]; simp only [ht]; omega

theorem distinct_outputs_height_origin {u x z a b : T}
    (ha : mul u z = a) (hb : mul x z = b) (hne : a ≠ b)
    (hs : ht b ≤ ht a) : origin a = some (u,z) ∧ ht z < ht a := by
  rcases mul_height_shape u z with hg | ⟨v,k,l,r,hz,hm⟩
  · rw [ha] at hg; exact ⟨hg.2.2,hg.2.1⟩
  · have hv : v = a := hm.symm.trans ha
    rw [hv] at hz
    have hza : ht a < ht z := by rw [hz]; simp only [ht]; omega
    rcases mul_height_shape x z with hg | ⟨v',k',l',r',hz',hm'⟩
    · rw [hb] at hg; omega
    · have hv' : v' = b := hm'.symm.trans hb
      rw [hv'] at hz'
      have hp := T.c.inj (hz.symm.trans hz')
      exact False.elim (hne hp.2.1)

theorem common_column_height_bounds {a b y x z : T}
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    ht y < max (ht a) (ht b) ∧ ht x < max (ht a) (ht b) ∧ ht z < max (ht a) (ht b) := by
  have hn : a ≠ b := by
    intro he
    exact mul_ne_right y x (right_injective _ _ z (ha.trans (he.trans hb.symm)))
  have ix := inverse_height_strict (inverse_complete x z)
  have iu := inverse_height_strict (inverse_complete (mul y x) z)
  have iy := inverse_height_strict (inverse_complete y x)
  rw [ha] at iu; rw [hb] at ix
  by_cases hs : ht b ≤ ht a
  · have ho := (distinct_outputs_height_origin ha hb hn hs).1
    have hh := origin_height ho
    exact ⟨by omega,by omega,by omega⟩
  · have ho := (distinct_outputs_height_origin hb ha (Ne.symm hn) (by omega)).1
    have hh := origin_height ho
    exact ⟨by omega,by omega,by omega⟩

theorem mul_height_growth_or_return (a b : T) :
    ht (mul a b) = max (ht a) (ht b) + 1 ∨
    ∃ x z l r, b = c a x z l r ∧ mul a b = x := by
  rcases mul_cases a b with ⟨he,hm⟩ | hr | hm | ⟨y,x,z,hm⟩
  · exact Or.inl (by rw [hm,he]; simp only [ht]; omega)
  · exact Or.inr hr
  · exact Or.inl (by rw [hm]; rfl)
  · have hc := mul_code_semantics hm
    have hh := common_column_height_bounds hc.1 hc.2
    apply Or.inl
    rw [hm]; simp only [ht]; omega

theorem mul_height_upper (a b : T) : ht (mul a b) ≤ max (ht a) (ht b) + 1 := by
  rcases mul_height_growth_or_return a b with hg | ⟨x,z,l,r,hb,hm⟩
  · omega
  · rw [hm,hb]; simp only [ht]; omega

theorem nf_code_height_gap {y x z a b : T} (hn : NF (c y x z a b)) :
    ht y + 2 ≤ ht (c y x z a b) ∧ ht x + 2 ≤ ht (c y x z a b) ∧
      ht z + 2 ≤ ht (c y x z a b) := by
  have hc := nf_code_actual hn
  have hh := common_column_height_bounds hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
  simp only [ht]
  exact ⟨by omega,by omega,by omega⟩

theorem nf_mul_height_alternatives {a b : T} (hb : NF b) :
    ht (mul a b) = max (ht a) (ht b) + 1 ∨
      (ht a + 2 ≤ ht b ∧ ht (mul a b) + 2 ≤ ht b) := by
  rcases mul_height_growth_or_return a b with hg | ⟨x,z,l,r,hb',hm⟩
  · exact Or.inl hg
  · have hnf := hb' ▸ hb
    have hh := nf_code_height_gap hnf
    exact Or.inr (by rw [hm,hb']; exact ⟨hh.1,hh.2.1⟩)

end submission.Austin12087Trace

/- Checked module: TraceFlip -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem fold_column_trace {u a t j : T} (hf : FoldWitness u a t j) :
    ∃ h r, j = c (mul u t) (mul u a) r t h ∧
      mul (mul (mul u t) (mul u a)) r = t ∧ mul (mul u a) r = h ∧
      sz (mul u t) < sz j ∧ sz (mul u a) < sz j ∧ sz r < sz j := by
  obtain ⟨h,_,_,hj,has,_,hhs⟩ := fold_outer_trace hf
  have hne : a ≠ j := by intro he; rw [he] at has; omega
  obtain ⟨r,l,b,hc⟩ := distinct_columns_larger_returns rfl hf.1.symm hne (by omega)
  have ho := mul_origin_of_right_le (a:=t) (b:=h) (by rw [hj]; omega)
  rw [hj] at ho
  conv at ho => lhs; rw [hc,origin]
  obtain ⟨hl,hb⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst b
  have hs := mul_code_semantics (hj.trans hc)
  exact ⟨h,r,hc,hs.1,hs.2,by rw [hc]; simp only [sz]; omega,
    by rw [hc]; simp only [sz]; omega,by rw [hc]; simp only [sz]; omega⟩

theorem flip_fold_trace {u a k : T}
    (hf : mul u (mul (mul u a) k) = mul a k) :
    ∃ j, FoldWitness u a (mul a k) j ∧
      mul (mul u a) k = c u (mul a k) j (mul u a) k := by
  have hs := common_column_inputs_small
    (show mul (mul u a) k = mul (mul u a) k from rfl)
    (show mul a k = mul a k from rfl)
  have htq : sz (mul a k) < sz (mul (mul u a) k) := by
    by_cases hn : sz (mul a k) < sz (mul (mul u a) k)
    · exact hn
    apply False.elim
    have ho := mul_origin_of_right_le (a:=u) (b:=mul (mul u a) k) (by rw [hf]; omega)
    have ho' := mul_origin_of_right_le (a:=a) (b:=k) (by omega)
    rw [hf,ho'] at ho
    have hp := Prod.mk.inj (Option.some.inj ho)
    exact mul_ne_right (mul u a) k hp.2.symm
  have hsmall : sz (mul u (mul (mul u a) k)) < sz (mul (mul u a) k) := by
    rw [hf]; exact htq
  obtain ⟨v,j,l,r,hc⟩ := (mul_small_iff _ _).mp hsmall
  have hv : v = mul a k := by rw [hc,mul_code_return] at hf; exact hf
  subst v
  have ho := mul_origin_of_right_le (a:=mul u a) (b:=k) (by omega)
  conv at ho => lhs; rw [hc,origin]
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst r
  have hsem := mul_code_semantics hc
  refine ⟨j,⟨hsem.1.symm,?_⟩,hc⟩
  rw [hsem.2]

theorem no_flip_plain {u a k : T} (hk : PlainRight k) :
    mul u (mul (mul u a) k) ≠ mul a k := by
  intro hf
  obtain ⟨j,hfold,hc⟩ := flip_fold_trace hf
  have hs := (mul_code_semantics hc).2
  obtain ⟨h,hcode,_,_,_,_,_⟩ := fold_outer_trace hfold
  rw [hs] at hcode
  rw [hcode] at hk
  exact hk

end submission.Austin12087Trace

/- Checked module: TraceFoldTower -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem mul_origin_of_right_height_le {a b : T} (hh : ht b ≤ ht (mul a b)) :
    origin (mul a b) = some (a,b) := by
  rcases mul_height_shape a b with hg | ⟨x,z,l,r,hb,hm⟩
  · exact hg.2.2
  · rw [hm,hb] at hh; simp only [ht] at hh; omega

theorem mul_return_of_height_lt {a b : T} (hh : ht (mul a b) < ht b) :
    ∃ z l r, b = c a (mul a b) z l r := by
  rcases mul_height_shape a b with hg | ⟨x,z,l,r,hb,hm⟩
  · omega
  · exact ⟨z,l,r,by rw [hm]; exact hb⟩

theorem mul_height_growth_of_left_ge {a b : T} (hh : ht b ≤ ht a) :
    ht (mul a b) = max (ht a) (ht b) + 1 := by
  rcases mul_height_growth_or_return a b with hg | ⟨x,z,l,r,hb,_⟩
  · exact hg
  · rw [hb] at hh; simp only [ht] at hh; omega

theorem mul_height_growth_of_right_le {a b : T} (hh : ht b ≤ ht (mul a b)) :
    ht (mul a b) = max (ht a) (ht b) + 1 := by
  rcases mul_height_growth_or_return a b with hg | ⟨x,z,l,r,hb,hm⟩
  · exact hg
  · rw [hm,hb] at hh; simp only [ht] at hh; omega

theorem fold_next_trace {u a t j : T} (hf : FoldWitness u a t j) :
    ∃ h r s,
      j = c (mul u t) (mul u a) r t h ∧
      h = c (mul a t) t s (mul u a) r ∧
      mul (mul (mul a t) t) s = mul u a ∧ mul t s = r ∧
      mul (mul (mul u t) (mul u a)) r = t ∧ mul (mul u a) r = h ∧
      mul t h = j ∧ ht t < ht h := by
  obtain ⟨h,r,hj,het,hwh,_,_,_⟩ := fold_column_trace hf
  -- Recover the same h from the right input stored in j, without choosing an
  -- unrelated existential witness from the earlier outer trace.
  obtain ⟨h',hb',hth',hj',_,_,hhs⟩ := fold_outer_trace hf
  have hn : h' = h := by
    have ho := mul_origin_of_right_le (a:=t) (b:=h') (by
      rw [hj']; omega)
    rw [hj',hj,origin] at ho
    exact (Prod.mk.inj (Option.some.inj ho)).2.symm
  subst h'
  have hc := common_column_height_bounds het hwh
  have hth : ht t < ht h := by
    by_cases hh : ht t < ht h
    · exact hh
    apply False.elim
    have ho := mul_origin_of_right_height_le (a:=mul a t) (b:=h) (by rw [hth']; omega)
    have ho' := mul_origin_of_right_height_le (a:=mul (mul u t) (mul u a)) (b:=r) (by rw [het]; omega)
    rw [hth'] at ho
    rw [het,ho] at ho'
    have hp := Prod.mk.inj (Option.some.inj ho')
    exact mul_ne_right (mul u a) r (hwh.trans hp.2)
  obtain ⟨s,l,b,hcode⟩ := mul_return_of_height_lt (a:=mul a t) (b:=h) (by rw [hth']; exact hth)
  rw [hth'] at hcode
  have hor := mul_origin_of_right_height_le (a:=mul u a) (b:=r) (by rw [hwh]; omega)
  rw [hwh] at hor
  conv at hor => lhs; rw [hcode,origin]
  obtain ⟨hl,hb⟩ := Prod.mk.inj (Option.some.inj hor)
  subst l; subst b
  have hs := mul_code_semantics (hwh.trans hcode)
  exact ⟨h,r,s,hj,hcode,hs.1,hs.2,het,hwh,hj',hth⟩

theorem fold_trace_right_dominates {u a t r s : T}
    (hw : mul (mul (mul a t) t) s = mul u a) (hr : mul t s = r)
    (het : mul (mul (mul u t) (mul u a)) r = t) : ht (mul u a) < ht r := by
  have hc := common_column_height_bounds hw hr
  by_cases hwr : ht (mul u a) < ht r
  · exact hwr
  apply False.elim
  have hat := inverse_height_strict (inverse_complete a t)
  have ha : ht a < ht (mul u a) := by omega
  have hwg := mul_height_growth_of_right_le (a:=u) (b:=a) (by omega)
  have he := inverse_height_strict (inverse_complete (mul (mul u t) (mul u a)) r)
  rw [het] at he
  have hes : ht (mul (mul u t) (mul u a)) < ht (mul u a) := by omega
  obtain ⟨k,l,b,hcode⟩ := mul_return_of_height_lt hes
  have hq : ht (mul u t) < ht (mul u a) := by
    conv => rhs; rw [hcode]
    simp only [ht]; omega
  by_cases hua : ht u ≤ ht a
  · have hdt := mul_height_growth_of_left_ge (a:=a) (b:=t) (by omega)
    omega
  · have hqt := mul_height_growth_of_left_ge (a:=u) (b:=t) (by omega)
    omega

theorem fold_height_tower {u a t j : T} (hf : FoldWitness u a t j) :
    ∃ h r s,
      j = c (mul u t) (mul u a) r t h ∧
      h = c (mul a t) t s (mul u a) r ∧
      ht r = ht s + 1 ∧ ht h = ht s + 2 ∧ ht j = ht s + 3 ∧
      ht u < ht s ∧ ht a < ht s ∧ ht t < ht s ∧ ht (mul u a) < ht s := by
  obtain ⟨h,r,s,hj,hh,hw,hr,het,hwh,htj,hth⟩ := fold_next_trace hf
  have hc := common_column_height_bounds hw hr
  have hwr := fold_trace_right_dominates hw hr het
  have htr : ht t < ht r := by omega
  obtain ⟨k,l,b,hcode⟩ := mul_return_of_height_lt (a:=mul (mul u t) (mul u a)) (b:=r) (by rw [het]; exact htr)
  rw [het] at hcode
  have hor := mul_origin_of_right_height_le (a:=t) (b:=s) (by rw [hr]; omega)
  rw [hr] at hor
  conv at hor => lhs; rw [hcode,origin]
  obtain ⟨hl,hb⟩ := Prod.mk.inj (Option.some.inj hor)
  subst l; subst b
  have hsem := mul_code_semantics (hr.trans hcode)
  have hts : ht t < ht s := by
    have hb := common_column_height_bounds hsem.1 hsem.2
    omega
  have hrg := mul_height_growth_of_right_le (a:=t) (b:=s) (by rw [hr]; omega)
  rw [hr] at hrg
  have hhh : ht r < ht h := by rw [hh]; simp only [ht]; omega
  have hhg := mul_height_growth_of_right_le (a:=mul u a) (b:=r) (by rw [hwh]; omega)
  rw [hwh] at hhg
  have hjh : ht h < ht j := by rw [hj]; simp only [ht]; omega
  have hjg := mul_height_growth_of_right_le (a:=t) (b:=h) (by rw [htj]; omega)
  rw [htj] at hjg
  have hws : ht (mul u a) < ht s := by
    rcases mul_height_shape (mul (mul a t) t) s with hg | ⟨x,z,l,b,hs,hm⟩
    · rw [hw] at hg; omega
    · have hx : x = mul u a := hm.symm.trans hw
      rw [hx] at hs
      conv => rhs; rw [hs]
      simp only [ht]; omega
  have hai := inverse_height_strict (inverse_complete a t)
  have hui := inverse_height_strict (inverse_complete u a)
  exact ⟨h,r,s,hj,hh,by omega,by omega,by omega,by omega,by omega,hts,hws⟩

theorem normal_fold_height_parameter {u a t j : T} (hj : NF j) (hf : FoldWitness u a t j) :
    ∃ s, NF s ∧ ht j = ht s + 3 ∧
      ht u < ht s ∧ ht a < ht s ∧ ht t < ht s ∧ ht (mul u a) < ht s := by
  obtain ⟨h,r,s,hjc,hhc,_,_,hjs,hus,has,hts,hws⟩ := fold_height_tower hf
  rw [hjc] at hj
  have hh : NF h := (nf_code_actual hj).2.2.2.2.1
  rw [hhc] at hh
  exact ⟨s,(nf_code_actual hh).2.2.1,hjs,hus,has,hts,hws⟩

theorem common_column_key_height_gap {a b y x z : T}
    (ha : mul (mul y x) z = a) (hb : mul x z = b) :
    ht y + 2 ≤ max (ht a) (ht b) := by
  have hc := common_column_height_bounds ha hb
  by_cases hh : ht y + 2 ≤ max (ht a) (ht b)
  · exact hh
  apply False.elim
  have hu := mul_height_growth_of_left_ge (a:=y) (b:=x) (by omega)
  have haa := mul_height_growth_of_left_ge (a:=mul y x) (b:=z) (by omega)
  rw [ha] at haa
  omega

theorem nf_code_key_height_gap {y x z a b : T} (hn : NF (c y x z a b)) :
    ht y + 3 ≤ ht (c y x z a b) := by
  have hc := nf_code_actual hn
  have hh := common_column_key_height_gap hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
  simp only [ht]
  omega

theorem nf_mul_height_key_gap {a b : T} (hn : NF b) :
    ht (mul a b) = max (ht a) (ht b) + 1 ∨
      (ht a + 3 ≤ ht b ∧ ht (mul a b) + 2 ≤ ht b) := by
  rcases mul_height_growth_or_return a b with hg | ⟨x,z,l,r,hb,hm⟩
  · exact Or.inl hg
  · have hc : NF (c a x z l r) := hb ▸ hn
    have hy := nf_code_key_height_gap hc
    have hx := (nf_code_height_gap hc).2.1
    exact Or.inr (by rw [hm,hb]; exact ⟨hy,hx⟩)

end submission.Austin12087Trace

/- Checked module: TraceReturnLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

def ReturnLadder (a b c x y j h : T) : Prop :=
  NF j ∧ mul c h = j ∧ origin j = some (c,h) ∧ mul a j = x ∧ mul b h = y

theorem nf_return_origin_trace {a j x c h : T} (hn : NF j)
    (ho : origin j = some (c,h)) (hm : mul a j = x) (hs : ht x < ht j) :
    ∃ r, j = T.c a x r c h ∧ NF r ∧ NF h ∧
      mul (mul a x) r = c ∧ mul x r = h ∧
      ht r + 2 ≤ ht j ∧ ht a + 3 ≤ ht j := by
  obtain ⟨r,l,b,hj⟩ := mul_return_of_height_lt (a:=a) (b:=j) (by rw [hm]; exact hs)
  rw [hm] at hj
  rw [hj,origin] at ho
  obtain ⟨hl,hb⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst b
  have hnf : NF (T.c a x r c h) := hj ▸ hn
  have hc := nf_code_actual hnf
  have hg := nf_code_height_gap hnf
  have hk := nf_code_key_height_gap hnf
  exact ⟨r,hj,hc.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2.2.1,hc.2.2.2.2.2.2.2,
    by rw [hj]; exact hg.2.2,by rw [hj]; exact hk⟩

theorem return_ladder_step {a b c x y j h : T}
    (hl : ReturnLadder a b c x y j h) (hx : ht x < ht j) (hc : ht c < ht h) :
    ∃ r, ReturnLadder b (mul a x) x y c h r ∧ ht r < ht j := by
  obtain ⟨hn,hgen,hor,hfirst,hsecond⟩ := hl
  obtain ⟨r,_,hnr,hnh,hr,hh,hrgap,_⟩ := nf_return_origin_trace hn hor hfirst hx
  have hg := mul_height_growth_of_right_le (a:=c) (b:=h) (by
    rw [hgen]
    exact Nat.le_of_lt (origin_height hor).2)
  rw [hgen] at hg
  have hrs : ht r < ht h := by omega
  have hoh := mul_origin_of_right_height_le (a:=x) (b:=r) (by rw [hh]; omega)
  rw [hh] at hoh
  exact ⟨r,⟨hnh,hh,hoh,hsecond,hr⟩,by omega⟩

theorem return_ladder_dominant_impossible {a b c x y j h : T}
    (hl : ReturnLadder a b c x y j h)
    (hc : ht c ≤ ht a) (hx : ht x ≤ ht a) (hy : ht y ≤ ht a) : False := by
  have main : ∀ n, ∀ a b c x y j h : T, ht j = n →
      ReturnLadder a b c x y j h →
      ht c ≤ ht a → ht x ≤ ht a → ht y ≤ ht a → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b c x y j h hjn hl hc hx hy
      have ha := inverse_height_strict (inverse_complete a j)
      rw [hl.2.2.2.1] at ha
      have haj : ht a < ht j := by omega
      obtain ⟨_,_,_,_,_,_,_,hkey⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 (by omega)
      have hg := mul_height_growth_of_right_le (a:=c) (b:=h) (by
        rw [hl.2.1]
        exact Nat.le_of_lt (origin_height hl.2.2.1).2)
      rw [hl.2.1] at hg
      have hah : ht a < ht h := by omega
      obtain ⟨r,hl₁,hrj⟩ := return_ladder_step hl (by omega) (by omega)
      have hag := mul_height_growth_of_left_ge (a:=a) (b:=x) hx
      have har := inverse_height_strict (inverse_complete (mul a x) r)
      rw [hl₁.2.2.2.2] at har
      have hxr : ht x < ht r := by omega
      obtain ⟨s,hl₂,_⟩ := return_ladder_step hl₁ (by omega) hxr
      exact ih (ht r) (by omega) (mul a x) (mul b y) y c x r s rfl hl₂
        (by omega) (by omega) (by omega)
  exact main (ht j) a b c x y j h rfl hl hc hx hy

theorem return_ladder_second_dominant_impossible {a b c x y j h : T}
    (hl : ReturnLadder a b c x y j h) (hj : ht x < ht j)
    (hc : ht c ≤ ht b) (hx : ht x ≤ ht b) (hy : ht y ≤ ht b) : False := by
  have hb := inverse_height_strict (inverse_complete b h)
  rw [hl.2.2.2.2] at hb
  obtain ⟨r,hl',_⟩ := return_ladder_step hl hj (by omega)
  exact return_ladder_dominant_impossible hl' hx hy hc

end submission.Austin12087Trace

/- Checked module: TraceNormalFoldExclusion -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem initial_fold_keys_or_same {u a t : T} (hnt : NF t) :
    (ht (mul u a) ≤ ht (mul u t) ∧ ht t ≤ ht (mul u t)) ∨
    (ht (mul u a) ≤ ht (mul a t) ∧ ht t ≤ ht (mul a t)) ∨
    (u = a ∧ ht (mul u a) < ht t ∧ ht (mul u t) < ht t) := by
  have hw := mul_height_upper u a
  by_cases hv : ht t ≤ ht (mul u t)
  · have hg := mul_height_growth_of_right_le hv
    by_cases hwide : ht (mul u a) ≤ ht (mul u t)
    · exact Or.inl ⟨hwide,hv⟩
    · have had := mul_height_growth_of_left_ge (a:=a) (b:=t) (by omega)
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  by_cases hd : ht t ≤ ht (mul a t)
  · have hg := mul_height_growth_of_right_le hd
    by_cases hwide : ht (mul u a) ≤ ht (mul a t)
    · exact Or.inr (Or.inl ⟨hwide,hd⟩)
    · have hu := mul_height_growth_of_left_ge (a:=u) (b:=t) (by omega)
      exact Or.inl ⟨by omega,by omega⟩
  obtain ⟨r,l,b,htu⟩ := mul_return_of_height_lt (a:=u) (b:=t) (by omega)
  obtain ⟨s,c,d,hta⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by omega)
  have he : u = a := (T.c.inj (htu.symm.trans hta)).1
  have hk := nf_code_key_height_gap (htu ▸ hnt)
  rw [←htu] at hk
  apply Or.inr
  apply Or.inr
  refine ⟨he,?_,by omega⟩
  rw [←he,mul_square]
  simp only [ht]
  omega

theorem mul_height_off_return_key {a b k x z l r : T}
    (hb : b = T.c k x z l r) (ha : a ≠ k) :
    ht (mul a b) = max (ht a) (ht b) + 1 := by
  rcases mul_height_growth_or_return a b with hg | ⟨v,s,c,d,hcode,_⟩
  · exact hg
  · exact False.elim (ha (T.c.inj (hcode.symm.trans hb)).1)

theorem nf_fold_impossible {u a t j : T} (hn : NF j) (hf : FoldWitness u a t j) : False := by
  obtain ⟨h,r,s,hj,hh,hrs,hhs,hjs,_,_,hts,hws⟩ := fold_height_tower hf
  let w := mul u a
  let v := mul u t
  let d := mul a t
  let e := mul v w
  let g := mul d t
  change j = T.c v w r t h at hj
  change h = T.c d t s w r at hh
  change ht w < ht s at hws
  have cj := nf_code_actual (hj ▸ hn)
  have hnh : NF h := cj.2.2.2.2.1
  have ch := nf_code_actual (hh ▸ hnh)
  have jgen : mul t h = j := cj.2.2.2.2.2.1.trans hj.symm
  have jorigin : origin j = some (t,h) := by rw [hj]; rfl
  have jret : mul v j = w := hf.1.symm
  have hret : mul d h = t := by rw [hh,mul_code_return]
  have hl₀ : ReturnLadder v d t w t j h := ⟨hn,jgen,jorigin,jret,hret⟩
  have choices := initial_fold_keys_or_same (u:=u) (a:=a) cj.2.2.2.1
  change (ht w ≤ ht v ∧ ht t ≤ ht v) ∨
    (ht w ≤ ht d ∧ ht t ≤ ht d) ∨ (u=a ∧ ht w < ht t ∧ ht v < ht t) at choices
  rcases choices with hv | hd | ⟨hua,hwt,hvt⟩
  · exact return_ladder_dominant_impossible hl₀ hv.2 hv.1 hv.2
  · exact return_ladder_second_dominant_impossible hl₀ (by omega) hd.2 hd.1 hd.2
  · have rgen : mul t s = r := ch.2.2.2.2.2.2.2
    have rorigin := mul_origin_of_right_height_le (a:=t) (b:=s) (by rw [rgen]; omega)
    rw [rgen] at rorigin
    have rret : mul e r = t := cj.2.2.2.2.2.2.1
    obtain ⟨k,_,_,hns,hk,hkgen,hkgap,_⟩ :=
      nf_return_origin_trace cj.2.2.1 rorigin rret (by omega)
    have sorigin := mul_origin_of_right_height_le (a:=t) (b:=k) (by rw [hkgen]; omega)
    rw [hkgen] at sorigin
    have sret : mul g s = w := ch.2.2.2.2.2.2.1
    have hl₃ : ReturnLadder g (mul e t) t w t s k := ⟨hns,hkgen,sorigin,sret,hk⟩
    obtain ⟨z,l,b,htcode⟩ := mul_return_of_height_lt (a:=u) (b:=t) hvt
    have hdv : d = v := by dsimp only [d,v]; rw [hua]
    have hgv : g = mul v t := congrArg (fun q => mul q t) hdv
    by_cases hvu : v = u
    · have hwsq : w = T.s u := by dsimp only [w]; rw [←hua,mul_square]
      have heg : ht e = ht u + 2 := by
        change ht (mul v w) = ht u + 2
        rw [hvu,hwsq]
        rcases mul_height_growth_or_return u (T.s u) with hg | ⟨x,z,l,r,hc,_⟩
        · simp only [ht] at hg
          omega
        · cases hc
      have henu : e ≠ u := by intro he; have hs := congrArg ht he; omega
      have hegrow := mul_height_off_return_key (a:=e) htcode henu
      exact return_ladder_second_dominant_impossible hl₃ hws
        (by omega) (by omega) (by omega)
    · have hvgrow := mul_height_off_return_key (a:=v) htcode hvu
      rw [←hgv] at hvgrow
      exact return_ladder_dominant_impossible hl₃ (by omega) (by omega) (by omega)

end submission.Austin12087Trace

/- Checked module: TraceNormalFoldConsequences -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nf_no_flip {u a k : T} (hu : NF u) (ha : NF a) (hk : NF k) :
    mul u (mul (mul u a) k) ≠ mul a k := by
  intro he
  obtain ⟨j,hfold,hcode⟩ := flip_fold_trace he
  have hn := nf_mul (nf_mul hu ha) hk
  rw [hcode] at hn
  exact nf_fold_impossible (nf_code_actual hn).2.2.1 hfold

theorem normal_first_diagonal_query_absent (u k : T) (hu : NF u) (hk : NF k) :
    (inverse k (mul (mul u (mul k (mul u k))) k)).bind (inverse u) = none := by
  cases h₁ : inverse k (mul (mul u (mul k (mul u k))) k) with
  | none => rfl
  | some w =>
    cases h₂ : inverse u w with
    | none => exact h₂
    | some y =>
      have hw := inverse_sound h₁
      have hy := inverse_sound h₂
      rw [←hy] at hw
      obtain ⟨a,t,j,_,_,hj,_,_,_,_,hfold⟩ := normal_first_diagonal_fold_descent hu hk hw
      exact False.elim (nf_fold_impossible hj hfold)

end submission.Austin12087Trace

/- Checked module: TraceFirstOffdiagonal -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem first_larger_k_nested_code {u q k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) :
    ∃ t,
      mul u k = c q (mul q (mul u k)) t u k ∧
      mul (mul q (mul q (mul u k))) t = u ∧
      mul (mul q (mul u k)) t = k := by
  obtain ⟨⟨h,l,r,hk⟩,huv,hkv,hov⟩ := first_offdiagonal_larger_k_return hf hne hs
  let v := mul u k
  let b := mul q v
  let a := mul u b
  let w := mul (mul y u) k
  change sz u < sz v at huv
  change sz k < sz v at hkv
  change origin v = some (u,k) at hov
  have hws : sz w < sz k := by
    change sz (mul (mul y u) k) < sz k
    conv => rhs; rw [hk]
    simp only [sz]
    omega
  have hwa : mul a q = w := hf.symm
  have ha := inverse_strict_size (inverse_complete a q)
  rw [hwa] at ha
  have hret : ∃ t l r, v = c q b t l r := by
    rcases mul_grows_or_returns q v with hg | ⟨x,t,l,r,hv,hb⟩
    · have has : sz (mul u b) < sz b := by
        change sz a < sz b
        have hvb : sz v < sz b := hg.2.1
        omega
      obtain ⟨x,t,l,r,hb⟩ := (mul_small_iff u b).mp has
      have hxa : x = a := by change x = mul u b; rw [hb,mul_code_return]
      subst x
      have hob := hg.2.2
      change origin b = some (q,v) at hob
      rw [hb,origin] at hob
      obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hob)
      subst l; subst r
      have hbactual : mul q v = c u a t q v := hb
      have hbsem := mul_code_semantics hbactual
      have bounds := common_column_inputs_small hbsem.1 hbsem.2
      have hvt : sz t ≤ sz (mul a t) := by rw [hbsem.2]; omega
      have hoat := mul_origin_of_right_le hvt
      rw [hbsem.2] at hoat
      have hpo := Prod.mk.inj (Option.some.inj (hoat.symm.trans hov))
      have hau : a = u := hpo.1
      have htk : t = k := hpo.2
      have hq : mul (mul u u) k = q := by simpa only [hau,htk] using hbsem.1
      have hk₂ : ∃ z l r, k = c (mul u u) q z l r := by
        rcases mul_grows_or_returns (mul u u) k with hg₂ | ⟨v,z,l,r,hk₂,hv⟩
        · rw [hq] at hg₂
          exact False.elim (by omega)
        · have hvq : v = q := hv.symm.trans hq
          exact ⟨z,l,r,by rw [hvq] at hk₂; exact hk₂⟩
      obtain ⟨z,l,r,hk₂⟩ := hk₂
      have hkey : mul y u = mul u u := (T.c.inj (hk.symm.trans hk₂)).1
      have hyu : y = u := right_injective y u u hkey
      have hwq : w = q := by change mul (mul y u) k = q; rw [hyu,hq]
      have hbad : mul u q = q := by simpa only [hau,hwq] using hwa
      exact False.elim (mul_ne_right u q hbad)
    · have hxb : x = b := hb.symm
      exact ⟨t,l,r,by rw [hxb] at hv; exact hv⟩
  obtain ⟨t,l,r,hv⟩ := hret
  rw [hv,origin] at hov
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hov)
  subst l; subst r
  have hc : mul u k = c q b t u k := hv
  exact ⟨t,hc,mul_code_semantics hc⟩

theorem first_larger_k_height_dominates {u q k y : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) : ht u < ht k := by
  obtain ⟨t,hv,_,_⟩ := first_larger_k_nested_code hf hne hs
  obtain ⟨⟨s,l,r,hk⟩,_,_,_⟩ := first_offdiagonal_larger_k_return hf hne hs
  have nv := hv ▸ nf_mul hu hnk
  have hb := (nf_code_height_gap nv).2.1
  have hq := nf_code_key_height_gap nv
  rw [←hv] at hb hq
  have hw := (nf_code_height_gap (hk ▸ hnk)).2.1
  rw [←hk,hf] at hw
  have vg := mul_height_growth_of_right_le (a:=u) (b:=k) (by
    rw [hv]
    simp only [ht]
    omega)
  by_cases h : ht u < ht k
  · exact h
  · have ag := mul_height_growth_of_left_ge (a:=u) (b:=mul q (mul u k)) (by omega)
    have wg := mul_height_growth_of_left_ge (a:=mul u (mul q (mul u k))) (b:=q) (by omega)
    exact False.elim (by omega)

theorem first_larger_k_double_code {u q k y : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) :
    ∃ t s,
      mul u k = c q (mul q (mul u k)) t u k ∧
      k = c (mul y u) (mul (mul y u) k) s (mul q (mul u k)) t ∧
      mul (mul q (mul q (mul u k))) t = u ∧
      mul (mul q (mul u k)) t = k ∧
      mul (mul (mul y u) (mul (mul y u) k)) s = mul q (mul u k) ∧
      mul (mul (mul y u) k) s = t ∧
      ht u < ht k ∧ ht q < ht k ∧ ht y < ht k ∧
      ht (mul q (mul u k)) < ht k ∧ ht t < ht k ∧ ht s < ht k := by
  obtain ⟨t,hv,hut,hbt⟩ := first_larger_k_nested_code hf hne hs
  have huk := first_larger_k_height_dominates hu hnk hf hne hs
  obtain ⟨⟨s,l,r,hk⟩,_,_,_⟩ := first_offdiagonal_larger_k_return hf hne hs
  have hknu : k ≠ u := by intro he; have hh := congrArg ht he; omega
  have ho := (distinct_outputs_height_origin hbt hut hknu (by omega)).1
  conv at ho => lhs; rw [hk,origin]
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst r
  have hsem := mul_code_semantics (hbt.trans hk)
  have hkc := congrArg ht hk
  simp only [ht] at hkc
  have vg := mul_height_growth_of_right_le (a:=u) (b:=k) (by
    rw [hv]
    simp only [ht]
    omega)
  have hq := nf_code_key_height_gap (hv ▸ nf_mul hu hnk)
  rw [←hv] at hq
  have hy := inverse_height_strict (inverse_complete y u)
  exact ⟨t,s,hv,hk,hut,hbt,hsem.1,hsem.2,huk,
    by omega,by omega,by omega,by omega,by omega⟩

end submission.Austin12087Trace

/- Checked module: TraceFirstCodeOrder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem first_larger_k_head_forces_same_key {u q k y t : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k)
    (hc : mul u k = c q (mul q (mul u k)) t u k)
    (hh : ht t ≤ ht (mul q (mul u k))) : q = u := by
  let b := mul q (mul u k)
  have hsem := mul_code_semantics hc
  have huk := first_larger_k_height_dominates hu hnk hf hne hs
  obtain ⟨⟨s,l,r,hk⟩,_,_,_⟩ := first_offdiagonal_larger_k_return hf hne hs
  have hkg := mul_height_growth_of_left_ge hh
  rw [hsem.2] at hkg
  have hq := nf_code_key_height_gap (hc ▸ nf_mul hu hnk)
  rw [←hc] at hq
  have hvg := mul_height_growth_of_right_le (a:=u) (b:=k) (by
    rw [hc]
    simp only [ht]
    omega)
  have hw := (nf_code_height_gap (hk ▸ hnk)).2.1
  rw [←hk,hf] at hw
  have hai := inverse_height_strict (inverse_complete (mul u b) q)
  have ha : ht (mul u b) < ht b := by
    change ht (mul (mul u b) q) + 2 ≤ ht k at hw
    change ht k = max (ht b) (ht t) + 1 at hkg
    change ht t ≤ ht b at hh
    omega
  have hd : ht (mul q b) < ht b := by
    by_cases hn : ht (mul q b) < ht b
    · exact hn
    · have hdg := mul_height_growth_of_right_le (a:=q) (b:=b) (by omega)
      have hug := mul_height_growth_of_left_ge (a:=mul q b) (b:=t) (by
        change ht t ≤ ht b at hh
        omega)
      have hdu : mul (mul q b) t = u := hsem.1
      rw [hdu] at hug
      change ht k = max (ht b) (ht t) + 1 at hkg
      omega
  obtain ⟨za,la,ra,hba⟩ := mul_return_of_height_lt ha
  obtain ⟨zd,ld,rd,hbd⟩ := mul_return_of_height_lt hd
  exact (T.c.inj (hbd.symm.trans hba)).1

end submission.Austin12087Trace

/- Checked module: TraceTriangleLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem triangle_return_ladder_impossible {u b k w q e j h : T}
    (ha : origin (mul u b) = some (u,b))
    (hw : origin w = some (mul u b,k))
    (hl : ReturnLadder (mul q b) e w u b j h) : False := by
  have hau := (origin_height ha).1
  have hab := (origin_height ha).2
  have hwa := (origin_height hw).1
  have main : ∀ n, ∀ q e j h : T, ht j = n →
      ReturnLadder (mul q b) e w u b j h → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro q e j h hjn hl
      have hwj := (origin_height hl.2.2.1).1
      obtain ⟨r,_,hnr,_,hwr,hhr,hrj,_⟩ :=
        nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 (by omega)
      have hwh : ht w < ht h := by
        by_cases hh : ht w < ht h
        · exact hh
        · have hne : w ≠ h := by
            intro he
            have hbadu := right_injective _ _ r (hwr.trans (he.trans hhr.symm))
            exact mul_ne_right (mul q b) u hbadu
          have how := (distinct_outputs_height_origin hwr hhr hne (by omega)).1
          have he := Prod.mk.inj (Option.some.inj (how.symm.trans hw))
          have hsame := he.1
          have hao := mul_origin_of_right_height_le (a:=mul q b) (b:=u) (by
            rw [hsame]
            omega)
          rw [hsame] at hao
          have hi := Prod.mk.inj (Option.some.inj (hao.symm.trans ha))
          have hbad : mul q b = b := hi.1.trans hi.2
          exact False.elim (mul_ne_right q b hbad)
      obtain ⟨r',hl₁,_⟩ := return_ladder_step hl (by omega) hwh
      have hjg := mul_height_growth_of_right_le (a:=w) (b:=h) (by
        rw [hl.2.1]
        exact Nat.le_of_lt (origin_height hl.2.2.1).2)
      rw [hl.2.1] at hjg
      -- The code's column is unique, so the first transition uses the same r.
      have hrr : r' = r := by
        have ho₁ := hl₁.2.2.1
        have ho₂ := mul_origin_of_right_height_le (a:=u) (b:=r) (by
          rw [hhr]
          omega)
        rw [hhr] at ho₂
        exact (Prod.mk.inj (Option.some.inj (ho₁.symm.trans ho₂))).2
      subst r'
      have hhg := mul_height_growth_of_right_le (a:=u) (b:=r) (by
        rw [hhr]
        exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
      rw [hhr] at hhg
      have hwrsmall : ht w < ht r := by
        have hhret := nf_mul_height_key_gap (a:=mul (mul q b) u) hnr
        rw [hl₁.2.2.2.2] at hhret
        rcases hhret with hg | hg <;> omega
      obtain ⟨s,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      have hrg := mul_height_growth_of_right_le (a:=b) (b:=s) (by
        rw [hl₂.2.1]
        exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at hrg
      obtain ⟨t,hl₃,_⟩ := return_ladder_step hl₂ hwrsmall (by omega)
      have hsr := (origin_height hl₂.2.2.1).2
      exact ih (ht s) (by omega) e (mul (mul (mul q b) u) w) s t rfl hl₃
  exact main (ht j) q e j h rfl hl

end submission.Austin12087Trace

/- Checked module: TraceFirstRepeatedKey -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_first_larger_k_forces_repeated_key {u q k y : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) : q = u := by
  by_cases hqu : q = u
  · exact hqu
  · obtain ⟨t,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
      first_larger_k_double_code hu hnk hf hne hs
    let b := mul q (mul u k)
    let a := mul u b
    let d := mul q b
    let V := mul y u
    let w := mul V k
    have hwa : mul a q = w := hf.symm
    have hnc := nf_code_actual (hv ▸ nf_mul hu hnk)
    have hnq : NF q := hnc.1
    have hnb : NF b := hnc.2.1
    have hwk := (nf_code_height_gap (hk ▸ hnk)).2.1
    rw [←hk] at hwk
    change ht w + 2 ≤ ht k at hwk
    have hok : origin k = some (b,t) := by rw [hk]; rfl
    have hl : ReturnLadder V d b w u k t := ⟨hnk,hbt,hok,rfl,hut⟩
    have hab : ht b ≤ ht a := by
      by_cases hh : ht b ≤ ht a
      · exact hh
      · obtain ⟨z,l,r,hb⟩ := mul_return_of_height_lt (a:=u) (b:=b) (by
          change ht a < ht b
          omega)
        have hg := mul_height_off_return_key (a:=q) hb hqu
        have hgu := nf_code_key_height_gap (hb ▸ hnb)
        rw [←hb] at hgu
        have hgw := mul_height_upper a q
        rw [hwa] at hgw
        change ht d = max (ht q) (ht b) + 1 at hg
        exact False.elim (return_ladder_second_dominant_impossible hl (by omega)
          (by omega) (by omega) (by omega))
    have hao := mul_origin_of_right_height_le (a:=u) (b:=b) hab
    have hau := (origin_height hao).1
    change ht u < ht a at hau
    have haq : ht q ≤ ht w := by
      by_cases hh : ht q ≤ ht w
      · exact hh
      · have hqr := nf_mul_height_key_gap (a:=a) hnq
        rw [hwa] at hqr
        rcases hqr with hg | ⟨hga,hgw⟩
        · omega
        · have hdg := mul_height_growth_of_left_ge (a:=q) (b:=b) (by omega)
          change ht d = max (ht q) (ht b) + 1 at hdg
          exact False.elim (return_ladder_second_dominant_impossible hl (by omega)
            (by omega) (by omega) (by omega))
    have hwo := mul_origin_of_right_height_le (a:=a) (b:=q) (by rw [hwa]; exact haq)
    rw [hwa] at hwo
    have hbtlt : ht b < ht t := by
      by_cases hh : ht b < ht t
      · exact hh
      · exact False.elim (hqu (first_larger_k_head_forces_same_key hu hnk hf hne hs hv (by
          change ht t ≤ ht b
          omega)))
    obtain ⟨r,hl₂,_⟩ := return_ladder_step hl (by omega) hbtlt
    exact False.elim (triangle_return_ladder_impossible hao hwo hl₂)

theorem normal_first_larger_k_inner_returns {u q k y : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) :
    ht (mul u (mul q (mul u k))) < ht (mul q (mul u k)) := by
  have hqu := normal_first_larger_k_forces_repeated_key hu hnk hf hne hs
  subst q
  obtain ⟨t,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
    first_larger_k_double_code hu hnk hf hne hs
  let b := mul u (mul u k)
  let a := mul u b
  let V := mul y u
  let w := mul V k
  change ht a < ht b
  by_cases hh : ht a < ht b
  · exact hh
  · have hao := mul_origin_of_right_height_le (a:=u) (b:=b) (by
      change ht b ≤ ht a
      omega)
    have hau := (origin_height hao).1
    have hab := (origin_height hao).2
    change ht u < ht a at hau
    change ht b < ht a at hab
    have hwa : mul a u = w := hf.symm
    have hwg := mul_height_growth_of_left_ge (a:=a) (b:=u) (by omega)
    have hwo := mul_origin_of_right_height_le (a:=a) (b:=u) (by omega)
    rw [hwa] at hwo
    have hat := inverse_height_strict (inverse_complete a t)
    change mul a t = u at hut
    rw [hut] at hat
    have hwk := (nf_code_height_gap (hk ▸ hnk)).2.1
    rw [←hk] at hwk
    change ht w + 2 ≤ ht k at hwk
    have hok : origin k = some (b,t) := by rw [hk]; rfl
    have hl : ReturnLadder V a b w u k t := ⟨hnk,hbt,hok,rfl,hut⟩
    obtain ⟨r,hl₂,_⟩ := return_ladder_step hl (by omega) (by omega)
    exact False.elim (triangle_return_ladder_impossible hao hwo hl₂)

end submission.Austin12087Trace

/- Checked module: TraceRepeatedTail -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_first_repeated_tail_descent {u k y t : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hc : mul u k = c u (mul u (mul u k)) t u k)
    (hbtlt : ht (mul u (mul u k)) < ht t) :
    mul (mul y u) (mul (mul y u) k) = u ∧
    ∃ r, NF r ∧ sz u < sz r ∧ ht r < ht k ∧
      mul (mul (mul u (mul u (mul u k))) u) r =
        mul (mul u (mul u (mul u r))) u := by
  obtain ⟨t₀,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
    first_larger_k_double_code hu hnk hf hne hs
  have htt : t₀ = t := (T.c.inj (hv.symm.trans hc)).2.2.1
  rw [htt] at hv hk hut hbt hws htk
  clear htt t₀
  let b := mul u (mul u k)
  let a := mul u b
  let V := mul y u
  let w := mul V k
  let e := mul V w
  change mul a t = u at hut
  change mul b t = k at hbt
  change mul e s = b at hes
  change mul w s = t at hws
  have hwa : mul a u = w := hf.symm
  have hnc := nf_code_actual (hc ▸ nf_mul hu hnk)
  have hnb : NF b := hnc.2.1
  have hnt : NF t := hnc.2.2.1
  have hab := normal_first_larger_k_inner_returns hu hnk hf hne hs
  obtain ⟨z,l,r₀,hbc⟩ := mul_return_of_height_lt hab
  change b = c u a z l r₀ at hbc
  have hub := nf_code_key_height_gap (hbc ▸ hnb)
  have hba := (nf_code_height_gap (hbc ▸ hnb)).2.1
  rw [←hbc] at hub hba
  change ht u + 3 ≤ ht b at hub
  change ht a + 2 ≤ ht b at hba
  have hwu := mul_height_upper a u
  rw [hwa] at hwu
  have hkg := mul_height_growth_of_right_le (a:=b) (b:=t) (by
    rw [hbt]
    exact Nat.le_of_lt htk)
  rw [hbt] at hkg
  change ht b < ht t at hbtlt
  have hout : origin t = some (w,s) := by
    have hh : t ≠ b := by intro he; have ht' := congrArg ht he; omega
    exact (distinct_outputs_height_origin hws hes hh (by omega)).1
  have hutlt : ht u < ht t := by
    have hp := nf_mul_height_key_gap (a:=a) hnt
    rw [hut] at hp
    rcases hp with hg | hg <;> omega
  obtain ⟨r,htc,hnr,hns,hwr,hurs,hrt,_⟩ :=
    nf_return_origin_trace hnt hout hut hutlt
  change mul (mul a u) r = w at hwr
  rw [hwa] at hwr
  have hwrlt : ht w < ht r := by
    have hi := inverse_height_strict (inverse_complete w r)
    rw [hwr] at hi
    omega
  obtain ⟨z',l',r',hrc⟩ := mul_return_of_height_lt (a:=w) (b:=r) (by rw [hwr]; exact hwrlt)
  have huw : u ≠ w := by
    intro he
    exact mul_ne_right a u (hwa.trans he.symm)
  have hsg := mul_height_off_return_key (a:=u) hrc huw
  rw [hurs] at hsg
  have hos := mul_origin_of_right_height_le (a:=u) (b:=r) (by rw [hurs]; omega)
  rw [hurs] at hos
  have htg := mul_height_growth_of_right_le (a:=w) (b:=s) (by
    rw [hws]
    exact Nat.le_of_lt (origin_height hout).2)
  rw [hws] at htg
  have hbs : ht b < ht s := by
    have hp := nf_mul_height_key_gap (a:=e) hns
    rw [hes] at hp
    rcases hp with hg | hg <;> omega
  obtain ⟨j,hsc,hnj,_,huj,hbr,hjs,_⟩ :=
    nf_return_origin_trace hns hos hes hbs
  have hsb := (nf_code_height_gap (hsc ▸ hns)).2.1
  rw [←hsc] at hsb
  have hor := mul_origin_of_right_height_le (a:=b) (b:=j) (by rw [hbr]; omega)
  rw [hbr] at hor
  obtain ⟨h,hrcode,_,_,_,_,_,_⟩ := nf_return_origin_trace hnr hor hwr hwrlt
  have he : e = u := by
    by_cases hh : e = u
    · exact hh
    · have hg := mul_height_off_return_key (a:=e) hbc hh
      have hl : ReturnLadder w (mul e b) b w u r j := ⟨hnr,hbr,hor,hwr,huj⟩
      exact False.elim (return_ladder_second_dominant_impossible hl hwrlt
        (by omega) (by omega) (by omega))
  have hus : mul u s = b := by
    change s = c e b j u r at hsc
    rw [he] at hsc
    rw [hsc,mul_code_return]
  have hubs : sz u < sz b := by
    change b = c u a z l r₀ at hbc
    rw [hbc]
    simp only [sz]
    omega
  have hbrs : sz b < sz r := by
    rw [hrcode]
    simp only [sz]
    omega
  refine ⟨he,r,hnr,by omega,by omega,?_⟩
  change mul (mul a u) r = mul (mul u (mul u (mul u r))) u
  rw [hurs,hus]
  change mul (mul a u) r = mul a u
  rw [hwa,hwr]

end submission.Austin12087Trace

/- Checked module: TraceShortReturnControl -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_short_return_control :
    ∃ a u s : T, NF a ∧ NF u ∧ NF s ∧
      mul a (mul (mul a u) s) = u := by
  let u := atom 0
  let w := mul u u
  let j := mul (mul (mul w w) u) (mul w u)
  let s := mul u j
  have hnu : NF u := NF.atom 0
  have hnw : NF w := nf_mul hnu hnu
  have hnj : NF j := nf_mul (nf_mul (nf_mul hnw hnw) hnu) (nf_mul hnw hnu)
  refine ⟨u,u,s,hnu,hnu,nf_mul hnu hnj,?_⟩
  simp +decide [u,w,j,s,mul_equation,inverse.eq_def,decode,leftCode,rightCode,
    origin,queryM,queryI,rankM,rankI,sz,basicInverse]

end submission.Austin12087Trace

/- Checked module: TraceRepeatedFixed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem mul_commutative_only_equal {a b : T} (he : mul a b = mul b a) : a = b := by
  by_cases hh : ht b ≤ ht a
  · have hg := mul_height_growth_of_left_ge hh
    have ho := mul_origin_of_right_height_le (a:=a) (b:=b) (by omega)
    have ho' := mul_origin_of_right_height_le (a:=b) (b:=a) (by rw [←he]; omega)
    rw [←he] at ho'
    exact (Prod.mk.inj (Option.some.inj (ho.symm.trans ho'))).1
  · have hg := mul_height_growth_of_left_ge (a:=b) (b:=a) (by omega)
    have ho := mul_origin_of_right_height_le (a:=b) (b:=a) (by omega)
    have ho' := mul_origin_of_right_height_le (a:=a) (b:=b) (by rw [he]; omega)
    rw [he] at ho'
    exact (Prod.mk.inj (Option.some.inj (ho'.symm.trans ho))).1

theorem square_left_product_ne_right (a u : T) : mul (mul a u) (mul a u) ≠ u := by
  intro he
  let w := mul a u
  have hs : s w = u := by simpa only [mul_square] using he
  have hp : mul a (s w) = w := by rw [hs]
  rcases mul_height_growth_or_return a (s w) with hg | ⟨x,z,l,r,hc,_⟩
  · rw [hp] at hg
    simp only [ht] at hg
    omega
  · cases hc

theorem normal_first_repeated_fixed_head_order {u k y t : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hfixed : mul (mul y u) k = mul y u)
    (hc : mul u k = c u (mul u (mul u k)) t u k) :
    ht t ≤ ht (mul u (mul u k)) := by
  by_cases hh : ht t ≤ ht (mul u (mul u k))
  · exact hh
  · have he := (normal_first_repeated_tail_descent hu hnk hf hne hs hc (by omega)).1
    rw [hfixed] at he
    have hw : mul y u = mul (mul u (mul u (mul u k))) u := hfixed.symm.trans hf
    rw [hw] at he
    exact False.elim (square_left_product_ne_right _ _ he)

end submission.Austin12087Trace

/- Checked module: TraceFixedHeadGeometry -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nf_next_square_short_return_absent {u : T} (hu : NF u) :
    mul u (mul (mul u u) (mul u (mul u u))) ≠ u := by
  intro he
  let w := mul u u
  let s₀ := mul u w
  let t := mul w s₀
  have hnw : NF w := nf_mul hu hu
  have hns : NF s₀ := nf_mul hu hnw
  have hnt : NF t := nf_mul hnw hns
  have hw : ht w = ht u + 1 := by dsimp only [w]; rw [mul_square]; rfl
  have hsg : ht s₀ = ht u + 2 := by
    have hshape := mul_height_growth_or_return u w
    rcases hshape with hg | ⟨x,z,l,r,hc,_⟩
    · change ht s₀ = max (ht u) (ht w) + 1 at hg
      omega
    · change mul u u = c u x z l r at hc
      rw [mul_square] at hc
      cases hc
  have htg : ht t = ht u + 3 := by
    have hp := nf_mul_height_key_gap (a:=w) hns
    change ht t = max (ht w) (ht s₀) + 1 ∨
      (ht w + 3 ≤ ht s₀ ∧ ht t + 2 ≤ ht s₀) at hp
    rcases hp with hp | hp <;> omega
  have hot := mul_origin_of_right_height_le (a:=w) (b:=s₀) (by
    change ht s₀ ≤ ht t
    omega)
  change origin t = some (w,s₀) at hot
  change mul u t = u at he
  obtain ⟨r,_,_,_,hwr,_,hr,_⟩ := nf_return_origin_trace hnt hot he (by omega)
  change mul w r = w at hwr
  have hi := inverse_height_strict (inverse_complete w r)
  rw [hwr] at hi
  omega

theorem normal_first_fixed_head_trace {u k : T} (hu : NF u) (hnk : NF k)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hf : mul (mul (mul u (mul u (mul u k))) u) k =
      mul (mul u (mul u (mul u k))) u) :
    let b := mul u (mul u k)
    let a := mul u b
    let w := mul a u
    let e := mul w w
    ∃ t s j,
      mul u k = c u b t u k ∧ k = c w w s b t ∧ b = c u a j e s ∧
      mul a t = u ∧ mul b t = k ∧ mul e s = b ∧ mul w s = t ∧
      mul (mul u a) j = e ∧ mul a j = s ∧ ht t ≤ ht b ∧ ht e < ht s := by
  let b := mul u (mul u k)
  let a := mul u b
  let w := mul a u
  let e := mul w w
  have hfixed : mul w k = w := hf
  obtain ⟨t,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
    first_larger_k_double_code (y:=a) hu hnk hf hne hs
  have hhead := normal_first_repeated_fixed_head_order (y:=a) hu hnk hf hne hs hf hv
  change k = c w (mul w k) s b t at hk
  change mul (mul w (mul w k)) s = b at hes
  change mul (mul w k) s = t at hws
  change mul a t = u at hut
  change mul b t = k at hbt
  change ht t ≤ ht b at hhead
  rw [hfixed] at hk hes hws
  change mul e s = b at hes
  have hnb : NF b := (nf_code_actual (hv ▸ nf_mul hu hnk)).2.1
  have hab := normal_first_larger_k_inner_returns (y:=a) hu hnk hf hne hs
  change ht a < ht b at hab
  have hbne : b ≠ t := by
    intro he
    have hew := right_injective _ _ s (hes.trans (he.trans hws.symm))
    exact mul_ne_right w w hew
  have hob := (distinct_outputs_height_origin hes hws hbne hhead).1
  obtain ⟨j,hbc,_,_,hgj,haj,_,_⟩ := nf_return_origin_trace hnb hob (show mul u b = a from rfl) hab
  have heslt : ht e < ht s := by
    by_cases hh : ht e < ht s
    · exact hh
    · have hnes : e ≠ s := by
        intro he
        exact mul_ne_right u a (right_injective _ _ j (hgj.trans (he.trans haj.symm)))
      have hoe := (distinct_outputs_height_origin hgj haj hnes (by omega)).1
      have heo : origin e = some (w,w) := by
        change origin (mul w w) = some (w,w)
        rw [mul_square]
        rfl
      have hp := Prod.mk.inj (Option.some.inj (hoe.symm.trans heo))
      have hua : u = a := mul_commutative_only_equal hp.1
      have hww : w = mul u u := by dsimp only [w]; rw [←hua]
      have hss : s = mul u w := by rw [hp.2,←hua] at haj; exact haj.symm
      have hbad := hut
      rw [←hua,←hws] at hbad
      have hbad' : mul u (mul (mul u u) (mul u (mul u u))) = u := by
        simpa only [hss,hww] using hbad
      exact False.elim (nf_next_square_short_return_absent hu hbad')
  exact ⟨t,s,j,hv,hk,hbc,hut,hbt,hes,hws,hgj,haj,hhead,heslt⟩

end submission.Austin12087Trace

/- Checked module: TraceSquareLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem same_key_square_ladder_impossible {u a t j r : T}
    (hnu : NF u) (hat : mul a t = u) (hau : mul a u = a)
    (hl : ReturnLadder (mul u a) u t (mul a a) a j r)
    (he : ht (mul a a) < ht j) (hut : ht u < ht t) : False := by
  let g := mul u a
  let e := mul a a
  let f := mul g e
  have hnt : NF t := (nf_origin hl.1 hl.2.2.1).1
  have hnr : NF r := (nf_origin hl.1 hl.2.2.1).2
  have haur := nf_mul_height_key_gap (a:=a) hnu
  rw [hau] at haur
  have hau3 : ht a + 3 ≤ ht u := by rcases haur with hh | hh <;> omega
  have hg : ht g = ht u + 1 := by
    have hh := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hh
    omega
  have heh : ht e = ht a + 1 := by dsimp only [e]; rw [mul_square]; rfl
  have hf : ht f = ht u + 2 := by
    have hh := mul_height_growth_of_left_ge (a:=g) (b:=e) (by omega)
    change ht f = max (ht g) (ht e) + 1 at hh
    omega
  obtain ⟨zₜ,lₜ,rₜ,htcode⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; exact hut)
  rw [hat] at htcode
  have hur := inverse_height_strict (inverse_complete u r)
  rw [hl.2.2.2.2] at hur
  obtain ⟨zᵣ,lᵣ,rᵣ,hrcode⟩ := mul_return_of_height_lt (a:=u) (b:=r) (by
    rw [hl.2.2.2.2]
    omega)
  rw [hl.2.2.2.2] at hrcode
  have hur3 := nf_code_key_height_gap (hrcode ▸ hnr)
  rw [←hrcode] at hur3
  change ht e < ht j at he
  by_cases htr : ht t < ht r
  · obtain ⟨h,hl₁,_⟩ := return_ladder_step hl he htr
    change ReturnLadder u f e a t r h at hl₁
    by_cases htf : ht t ≤ ht f
    · exact return_ladder_second_dominant_impossible hl₁ (by omega)
        (by omega) (by omega) htf
    · have hrg := mul_height_growth_of_right_le (a:=e) (b:=h) (by
        rw [hl₁.2.1]
        exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
      rw [hl₁.2.1] at hrg
      have hnh : NF h := (nf_origin hl₁.1 hl₁.2.2.1).2
      have hth : ht t < ht h := by
        have hh := nf_mul_height_key_gap (a:=f) hnh
        rw [hl₁.2.2.2.2] at hh
        rcases hh with hh | hh <;> omega
      obtain ⟨z,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      change ReturnLadder f g a t e h z at hl₂
      have hhg := mul_height_growth_of_right_le (a:=a) (b:=z) (by
        rw [hl₂.2.1]
        exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at hhg
      obtain ⟨l,hl₃,_⟩ := return_ladder_step hl₂ hth (by omega)
      have hfg := mul_height_off_return_key (a:=f) htcode (by
        intro heq
        have hh := congrArg ht heq
        omega)
      exact return_ladder_second_dominant_impossible hl₃ (by omega)
        (by omega) (by omega) (by omega)
  · obtain ⟨h,_,hnh,_,hth,hrh,_,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 he
    change mul f h = t at hth
    change mul e h = r at hrh
    have hne : t ≠ r := by
      intro heq
      have hfe := right_injective _ _ h (hth.trans (heq.trans hrh.symm))
      have hh := congrArg ht hfe
      omega
    have hot := (distinct_outputs_height_origin hth hrh hne (by omega)).1
    obtain ⟨z,_,_,_,haz,huz,_,_⟩ := nf_return_origin_trace hnt hot hat hut
    rw [hau] at haz
    have hupper := mul_height_upper e h
    rw [hrh] at hupper
    have hne' : h ≠ f := by
      intro heq
      have hua := right_injective _ _ z (huz.trans (heq.trans haz.symm))
      have hh := congrArg ht hua
      omega
    have hoh := (distinct_outputs_height_origin huz haz hne' (by omega)).1
    have hrlt : ht r < ht h := by
      by_cases hh : ht r < ht h
      · exact hh
      · have hor := mul_origin_of_right_height_le (a:=e) (b:=h) (by rw [hrh]; omega)
        rw [hrh] at hor
        obtain ⟨q,_,_,_,hgq,haq,_,_⟩ :=
          nf_return_origin_trace hnr hor hl.2.2.2.2 (by omega)
        change mul g q = e at hgq
        have hi := inverse_height_strict (inverse_complete g q)
        rw [hgq] at hi
        obtain ⟨zq,lq,rq,hqc⟩ := mul_return_of_height_lt (a:=g) (b:=q) (by rw [hgq]; omega)
        have hag := mul_height_off_return_key (a:=a) hqc (by
          intro heq
          have h := congrArg ht heq
          omega)
        have hoh' := mul_origin_of_right_height_le (a:=a) (b:=q) (by omega)
        rw [haq] at hoh'
        have hua := (Prod.mk.inj (Option.some.inj (hoh.symm.trans hoh'))).1
        have heq := congrArg ht hua
        exact False.elim (by omega)
    have hlₕ : ReturnLadder e a u r f h z := ⟨hnh,huz,hoh,hrh,haz⟩
    have hhg := mul_height_growth_of_right_le (a:=u) (b:=z) (by
      rw [huz]
      exact Nat.le_of_lt (origin_height hoh).2)
    rw [huz] at hhg
    obtain ⟨l,hl',_⟩ := return_ladder_step hlₕ hrlt (by omega)
    have heg := mul_height_off_return_key (a:=e) hrcode (by
      intro heq
      have hh := congrArg ht heq
      omega)
    exact return_ladder_second_dominant_impossible hl' (by omega)
      (by omega) (by omega) (by omega)

end submission.Austin12087Trace

/- Checked module: TraceFixedHeadExclusion -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem square_return_ladder_impossible {u a t j r : T}
    (hnu : NF u) (hat : mul a t = u)
    (hl : ReturnLadder (mul u a) (mul (mul a u) t) t
      (mul (mul a u) (mul a u)) a j r)
    (he : ht (mul (mul a u) (mul a u)) < ht j) : False := by
  let w := mul a u
  let e := mul w w
  have hnt : NF t := (nf_origin hl.1 hl.2.2.1).1
  have heh : ht e = ht w + 1 := by dsimp only [e]; rw [mul_square]; rfl
  change ht e < ht j at he
  change ReturnLadder (mul u a) (mul w t) t e a j r at hl
  have hw := nf_mul_height_key_gap (a:=a) hnu
  change ht w = max (ht a) (ht u) + 1 ∨
    (ht a + 3 ≤ ht u ∧ ht w + 2 ≤ ht u) at hw
  rcases hw with hw | hw
  · by_cases htu : ht t ≤ ht u
    · have hdg := mul_height_growth_of_left_ge (a:=w) (b:=t) (by omega)
      exact return_ladder_second_dominant_impossible hl he (by omega) (by omega) (by omega)
    · obtain ⟨z,l,r,htcode⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; omega)
      have hdg := mul_height_off_return_key (a:=w) htcode (by
        intro heq
        have hh := congrArg ht heq
        omega)
      exact return_ladder_second_dominant_impossible hl he (by omega) (by omega) (by omega)
  · by_cases htu : ht t ≤ ht u
    · have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
      exact return_ladder_dominant_impossible hl (by omega) (by omega) (by omega)
    · by_cases hwa : w = a
      · have hl' : ReturnLadder (mul u a) u t (mul a a) a j r := by
          change ReturnLadder (mul u a) (mul w t) t (mul w w) a j r at hl
          rw [hwa,hat] at hl
          exact hl
        have he' : ht (mul a a) < ht j := by change ht (mul w w) < ht j at he; rw [hwa] at he; exact he
        exact same_key_square_ladder_impossible hnu hat hwa hl' he' (by omega)
      · obtain ⟨z,l,r,htcode⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; omega)
        have hdg := mul_height_off_return_key (a:=w) htcode hwa
        exact return_ladder_second_dominant_impossible hl he (by omega) (by omega) (by omega)

theorem normal_first_fixed_query_absent {u k : T} (hu : NF u) (hnk : NF k)
    (hne : u ≠ k) (hs : sz u ≤ sz k) :
    mul (mul (mul u (mul u (mul u k))) u) k ≠ mul (mul u (mul u (mul u k))) u := by
  intro hf
  let b := mul u (mul u k)
  let a := mul u b
  let w := mul a u
  let e := mul w w
  let g := mul u a
  obtain ⟨t,s,j,hv,hk,hbc,hat,hbt,hes,hws,hgj,haj,hhead,hse⟩ :=
    normal_first_fixed_head_trace hu hnk hne hs hf
  change b = c u a j e s at hbc
  change k = c w w s b t at hk
  change mul a t = u at hat
  change mul b t = k at hbt
  change mul e s = b at hes
  change mul w s = t at hws
  change mul g j = e at hgj
  change mul a j = s at haj
  change ht t ≤ ht b at hhead
  change ht e < ht s at hse
  have hkc := nf_code_actual (hk ▸ hnk)
  have hnb : NF b := hkc.2.2.2.1
  have hnt : NF t := hkc.2.2.2.2.1
  have hns : NF s := hkc.2.2.1
  have hnj : NF j := (nf_code_actual (hbc ▸ hnb)).2.2.1
  have hub := nf_code_key_height_gap (hbc ▸ hnb)
  rw [←hbc] at hub
  have heh : ht e = ht w + 1 := by dsimp only [e]; rw [mul_square]; rfl
  have hos : origin s = some (a,j) := by
    have hne' : s ≠ e := by intro heq; have hh := congrArg ht heq; omega
    exact (distinct_outputs_height_origin haj hgj hne' (by omega)).1
  have hbg := mul_height_growth_of_right_le (a:=e) (b:=s) (by
    rw [hes]
    have ho : origin b = some (e,s) := by rw [hbc]; rfl
    exact Nat.le_of_lt (origin_height ho).2)
  rw [hes] at hbg
  have htret : ht t < ht s := by
    by_cases hh : ht t < ht s
    · exact hh
    · have htg := mul_height_growth_of_right_le (a:=w) (b:=s) (by rw [hws]; omega)
      rw [hws] at htg
      have hot := mul_origin_of_right_height_le (a:=w) (b:=s) (by rw [hws]; omega)
      rw [hws] at hot
      obtain ⟨r,_,_,_,hwr,hurs,_,_⟩ := nf_return_origin_trace hnt hot hat (by omega)
      change mul w r = w at hwr
      have hi := inverse_height_strict (inverse_complete w r)
      rw [hwr] at hi
      obtain ⟨z,l,q,hrc⟩ := mul_return_of_height_lt (a:=w) (b:=r) (by rw [hwr]; omega)
      have huw : u ≠ w := by intro heq; exact mul_ne_right a u heq.symm
      have hsg := mul_height_off_return_key (a:=u) hrc huw
      have hos' := mul_origin_of_right_height_le (a:=u) (b:=r) (by omega)
      rw [hurs] at hos'
      have hp := Prod.mk.inj (Option.some.inj (hos'.symm.trans hos))
      have hgw : g = w := by dsimp only [g,w]; rw [hp.1]
      rw [hp.2] at hwr
      rw [hgw] at hgj
      exact False.elim (mul_ne_right w w (hgj.symm.trans hwr))
  have hej : ht e < ht j := by
    by_cases hh : ht e < ht j
    · exact hh
    · have hoe := mul_origin_of_right_height_le (a:=g) (b:=j) (by rw [hgj]; omega)
      rw [hgj] at hoe
      have hoe' : origin e = some (w,w) := by change origin (mul w w) = some (w,w); rw [mul_square]; rfl
      have hp := Prod.mk.inj (Option.some.inj (hoe.symm.trans hoe'))
      have hua : u = a := mul_commutative_only_equal hp.1
      have hw : ht w = ht u + 1 := by dsimp only [w]; rw [←hua,mul_square]; rfl
      have hupper := mul_height_upper a j
      rw [haj,hp.2,←hua] at hupper
      exact False.elim (by omega)
  obtain ⟨r,hsc,_,_,hdr,htr,hrs,_⟩ := nf_return_origin_trace hns hos hws htret
  have hgjj := nf_mul_height_key_gap (a:=g) hnj
  rw [hgj] at hgjj
  have hug := inverse_height_strict (inverse_complete u a)
  have haw := inverse_height_strict (inverse_complete a u)
  change ht u < max (ht a) (ht g) at hug
  change ht a < max (ht u) (ht w) at haw
  have hgjlt : ht g < ht j := by rcases hgjj with hh | hh <;> omega
  have hsg := mul_height_growth_of_right_le (a:=a) (b:=j) (by
    rw [haj]
    exact Nat.le_of_lt (origin_height hos).2)
  rw [haj] at hsg
  have hor := mul_origin_of_right_height_le (a:=t) (b:=r) (by rw [htr]; omega)
  rw [htr] at hor
  have hl : ReturnLadder g (mul w t) t e a j r := ⟨hnj,htr,hor,hgj,hdr⟩
  exact square_return_ladder_impossible hu hat hl hej

end submission.Austin12087Trace

/- Checked module: TraceRepeatedTailClosure -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_first_repeated_tail_impossible {u k y t : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hc : mul u k = c u (mul u (mul u k)) t u k)
    (hbtlt : ht (mul u (mul u k)) < ht t) : False := by
  have he := (normal_first_repeated_tail_descent hu hnk hf hne hs hc hbtlt).1
  obtain ⟨t₀,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
    first_larger_k_double_code hu hnk hf hne hs
  have htt : t₀ = t := (T.c.inj (hv.symm.trans hc)).2.2.1
  rw [htt] at hv hk hut hbt hws htk
  clear htt t₀
  let b := mul u (mul u k)
  let a := mul u b
  let V := mul y u
  let w := mul V k
  change mul a t = u at hut
  change mul b t = k at hbt
  change mul w s = t at hws
  rw [he] at hes
  change mul u s = b at hes
  have hwa : mul a u = w := hf.symm
  have hnc := nf_code_actual (hc ▸ nf_mul hu hnk)
  have hnb : NF b := hnc.2.1
  have hnt : NF t := hnc.2.2.1
  have hab := normal_first_larger_k_inner_returns hu hnk hf hne hs
  obtain ⟨z,l,r₀,hbc⟩ := mul_return_of_height_lt hab
  change b = c u a z l r₀ at hbc
  have hub := nf_code_key_height_gap (hbc ▸ hnb)
  rw [←hbc] at hub
  have hkg := mul_height_growth_of_right_le (a:=b) (b:=t) (by rw [hbt]; exact Nat.le_of_lt htk)
  rw [hbt] at hkg
  change ht b < ht t at hbtlt
  have hout : origin t = some (w,s) := by
    have hh : t ≠ b := by intro heq; have ht' := congrArg ht heq; omega
    exact (distinct_outputs_height_origin hws hes hh (by omega)).1
  have hutlt : ht u < ht t := by
    have hp := nf_mul_height_key_gap (a:=a) hnt
    rw [hut] at hp
    rcases hp with hg | hg <;> omega
  obtain ⟨r,_,hnr,hns,hwr,hurs,hrt,_⟩ := nf_return_origin_trace hnt hout hut hutlt
  change mul (mul a u) r = w at hwr
  rw [hwa] at hwr
  have hwrlt : ht w < ht r := by
    have hi := inverse_height_strict (inverse_complete w r)
    rw [hwr] at hi
    omega
  obtain ⟨z',l',r',hrc⟩ := mul_return_of_height_lt (a:=w) (b:=r) (by rw [hwr]; exact hwrlt)
  have huw : u ≠ w := by intro heq; exact mul_ne_right a u (hwa.trans heq.symm)
  have hsg := mul_height_off_return_key (a:=u) hrc huw
  rw [hurs] at hsg
  have hos := mul_origin_of_right_height_le (a:=u) (b:=r) (by rw [hurs]; omega)
  rw [hurs] at hos
  have htg := mul_height_growth_of_right_le (a:=w) (b:=s) (by
    rw [hws]
    exact Nat.le_of_lt (origin_height hout).2)
  rw [hws] at htg
  have hbs : ht b < ht s := by
    have hp := nf_mul_height_key_gap (a:=u) hns
    rw [hes] at hp
    rcases hp with hg | hg <;> omega
  obtain ⟨j,hsc,_,_,_,hbr,hjs,_⟩ := nf_return_origin_trace hns hos hes hbs
  have hsb := (nf_code_height_gap (hsc ▸ hns)).2.1
  rw [←hsc] at hsb
  have hor := mul_origin_of_right_height_le (a:=b) (b:=j) (by rw [hbr]; omega)
  rw [hbr] at hor
  obtain ⟨h,hrcode,_,_,_,_,_,_⟩ := nf_return_origin_trace hnr hor hwr hwrlt
  have hubs : sz u < sz b := by rw [hbc]; simp only [sz]; omega
  have hbrs : sz b < sz r := by rw [hrcode]; simp only [sz]; omega
  have hne' : u ≠ r := by intro heq; have hh := congrArg sz heq; omega
  apply normal_first_fixed_query_absent hu hnr hne' (by omega)
  rw [hurs,hes]
  change mul (mul a u) r = mul a u
  rw [hwa,hwr]

theorem normal_first_repeated_head_order {u k y t : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hc : mul u k = c u (mul u (mul u k)) t u k) :
    ht t ≤ ht (mul u (mul u k)) := by
  by_cases hh : ht t ≤ ht (mul u (mul u k))
  · exact hh
  · exact False.elim (normal_first_repeated_tail_impossible hu hnk hf hne hs hc (by omega))

end submission.Austin12087Trace

/- Checked module: TraceGeneralHeadGeometry -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nf_short_chain_absent_of_left_ge {a u : T} (ha : NF a) (hu : NF u)
    (hle : ht u ≤ ht a) : mul a (mul (mul a u) (mul a (mul a u))) ≠ u := by
  intro he
  let w := mul a u
  let s₀ := mul a w
  let t := mul w s₀
  have hnw : NF w := nf_mul ha hu
  have hns : NF s₀ := nf_mul ha hnw
  have hnt : NF t := nf_mul hnw hns
  have hw : ht w = ht a + 1 := by
    have hg := mul_height_growth_of_left_ge hle
    change ht w = max (ht a) (ht u) + 1 at hg
    omega
  have hsg : ht s₀ = ht a + 2 := by
    have hh := nf_mul_height_key_gap (a:=a) hnw
    change ht s₀ = max (ht a) (ht w) + 1 ∨
      (ht a + 3 ≤ ht w ∧ ht s₀ + 2 ≤ ht w) at hh
    rcases hh with hh | hh <;> omega
  have htg : ht t = ht a + 3 := by
    have hh := nf_mul_height_key_gap (a:=w) hns
    change ht t = max (ht w) (ht s₀) + 1 ∨
      (ht w + 3 ≤ ht s₀ ∧ ht t + 2 ≤ ht s₀) at hh
    rcases hh with hh | hh <;> omega
  have hot := mul_origin_of_right_height_le (a:=w) (b:=s₀) (by
    change ht s₀ ≤ ht t
    omega)
  change origin t = some (w,s₀) at hot
  change mul a t = u at he
  obtain ⟨r,_,_,_,hwr,_,hr,_⟩ := nf_return_origin_trace hnt hot he (by omega)
  change mul w r = w at hwr
  have hi := inverse_height_strict (inverse_complete w r)
  rw [hwr] at hi
  omega

theorem normal_first_general_head_trace {u k y : T} (hu : NF u) (hnk : NF k)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u) :
    let b := mul u (mul u k)
    let a := mul u b
    let V := mul y u
    let w := mul a u
    let e := mul V w
    ∃ t s j,
      mul u k = c u b t u k ∧ k = c V w s b t ∧ b = c u a j e s ∧
      mul a t = u ∧ mul b t = k ∧ mul e s = b ∧ mul w s = t ∧
      mul (mul u a) j = e ∧ mul a j = s ∧ ht t ≤ ht b ∧ ht e < ht s ∧ V ≠ w := by
  let b := mul u (mul u k)
  let a := mul u b
  let V := mul y u
  let w := mul a u
  let e := mul V w
  have hret : mul V k = w := hf
  obtain ⟨t,s,hv,hk,hut,hbt,hes,hws,huk,hqk,hyk,hbk,htk,hsk⟩ :=
    first_larger_k_double_code hu hnk hf hne hs
  have hhead := normal_first_repeated_head_order hu hnk hf hne hs hv
  change k = c V (mul V k) s b t at hk
  change mul (mul V (mul V k)) s = b at hes
  change mul (mul V k) s = t at hws
  change mul a t = u at hut
  change mul b t = k at hbt
  change ht t ≤ ht b at hhead
  rw [hret] at hk hes hws
  change mul e s = b at hes
  have hnb : NF b := (nf_code_actual (hv ▸ nf_mul hu hnk)).2.1
  have hna : NF a := nf_mul hu hnb
  have hab := normal_first_larger_k_inner_returns hu hnk hf hne hs
  change ht a < ht b at hab
  have hbne : b ≠ t := by
    intro he
    exact mul_ne_right V w (right_injective _ _ s (hes.trans (he.trans hws.symm)))
  have hob := (distinct_outputs_height_origin hes hws hbne hhead).1
  obtain ⟨j,hbc,_,_,hgj,haj,_,_⟩ := nf_return_origin_trace hnb hob (show mul u b = a from rfl) hab
  have heslt : ht e < ht s := by
    by_cases hh : ht e < ht s
    · exact hh
    · have hbg := mul_height_growth_of_right_le (a:=e) (b:=s) (by
        rw [hes]
        exact Nat.le_of_lt (origin_height hob).2)
      rw [hes] at hbg
      have hkg := mul_height_growth_of_right_le (a:=b) (b:=t) (by rw [hbt]; exact Nat.le_of_lt htk)
      rw [hbt] at hkg
      have hwk := (nf_code_height_gap (hk ▸ hnk)).2.1
      rw [←hk] at hwk
      have hnes : e ≠ s := by
        intro he
        exact mul_ne_right u a (right_injective _ _ j (hgj.trans (he.trans haj.symm)))
      have hoe := (distinct_outputs_height_origin hgj haj hnes (by omega)).1
      have hoe' := mul_origin_of_right_height_le (a:=V) (b:=w) (by
        change ht w ≤ ht e
        omega)
      change origin e = some (V,w) at hoe'
      have hp := Prod.mk.inj (Option.some.inj (hoe.symm.trans hoe'))
      have hua : ht u ≤ ht a := by
        by_cases h : ht u ≤ ht a
        · exact h
        · have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
          have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by omega)
          have hoy := mul_origin_of_right_height_le (a:=y) (b:=u) (by
            change ht u ≤ ht V
            rw [←hp.1]
            omega)
          rw [hp.1] at hog
          change origin V = some (y,u) at hoy
          have hau := (Prod.mk.inj (Option.some.inj (hog.symm.trans hoy))).2
          have heq := congrArg ht hau
          exact False.elim (by omega)
      have hss : s = mul a w := by rw [hp.2] at haj; exact haj.symm
      have hbad := hut
      rw [←hws,hss] at hbad
      exact False.elim (nf_short_chain_absent_of_left_ge hna hu hua hbad)
  have hvw : V ≠ w := by
    intro he
    have hfixed := hret
    rw [he] at hfixed
    exact normal_first_fixed_query_absent hu hnk hne hs hfixed
  exact ⟨t,s,j,hv,hk,hbc,hut,hbt,hes,hws,hgj,haj,hhead,heslt,hvw⟩

end submission.Austin12087Trace

/- Checked module: TraceGeneralHeadLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_first_general_head_ladder {u k y : T} (hu : NF u) (hnk : NF k)
    (hne : u ≠ k) (hs : sz u ≤ sz k)
    (hf : mul (mul y u) k = mul (mul u (mul u (mul u k))) u) :
    let b := mul u (mul u k)
    let a := mul u b
    let V := mul y u
    let w := mul a u
    let e := mul V w
    ∃ t j r, NF a ∧ mul a t = u ∧
      ReturnLadder (mul u a) (mul w t) t e a j r ∧ ht e < ht j ∧ V ≠ w := by
  let b := mul u (mul u k)
  let a := mul u b
  let V := mul y u
  let w := mul a u
  let e := mul V w
  let g := mul u a
  obtain ⟨t,s,j,hv,hk,hbc,hat,hbt,hes,hws,hgj,haj,hhead,hse,hvw⟩ :=
    normal_first_general_head_trace hu hnk hne hs hf
  change b = c u a j e s at hbc
  change k = c V w s b t at hk
  change mul a t = u at hat
  change mul b t = k at hbt
  change mul e s = b at hes
  change mul w s = t at hws
  change mul g j = e at hgj
  change mul a j = s at haj
  change ht t ≤ ht b at hhead
  change ht e < ht s at hse
  have hkc := nf_code_actual (hk ▸ hnk)
  have hnb : NF b := hkc.2.2.2.1
  have hnt : NF t := hkc.2.2.2.2.1
  have hns : NF s := hkc.2.2.1
  have hnj : NF j := (nf_code_actual (hbc ▸ hnb)).2.2.1
  have hna : NF a := nf_mul hu hnb
  have hub := nf_code_key_height_gap (hbc ▸ hnb)
  rw [←hbc] at hub
  have hos : origin s = some (a,j) := by
    have hne' : s ≠ e := by intro heq; have hh := congrArg ht heq; omega
    exact (distinct_outputs_height_origin haj hgj hne' (by omega)).1
  have hbg := mul_height_growth_of_right_le (a:=e) (b:=s) (by
    rw [hes]
    have ho : origin b = some (e,s) := by rw [hbc]; rfl
    exact Nat.le_of_lt (origin_height ho).2)
  rw [hes] at hbg
  have hkg := mul_height_growth_of_right_le (a:=b) (b:=t) (by
    rw [hbt]
    have ho : origin k = some (b,t) := by rw [hk]; rfl
    exact Nat.le_of_lt (origin_height ho).2)
  rw [hbt] at hkg
  have hwk := (nf_code_height_gap (hk ▸ hnk)).2.1
  rw [←hk] at hwk
  have htret : ht t < ht s := by
    by_cases hh : ht t < ht s
    · exact hh
    · have htg := mul_height_growth_of_right_le (a:=w) (b:=s) (by rw [hws]; omega)
      rw [hws] at htg
      have hot := mul_origin_of_right_height_le (a:=w) (b:=s) (by rw [hws]; omega)
      rw [hws] at hot
      obtain ⟨r,_,_,_,hwr,hurs,_,_⟩ := nf_return_origin_trace hnt hot hat (by omega)
      change mul w r = w at hwr
      have hi := inverse_height_strict (inverse_complete w r)
      rw [hwr] at hi
      obtain ⟨z,l,q,hrc⟩ := mul_return_of_height_lt (a:=w) (b:=r) (by rw [hwr]; omega)
      have huw : u ≠ w := by intro heq; exact mul_ne_right a u heq.symm
      have hsg := mul_height_off_return_key (a:=u) hrc huw
      have hos' := mul_origin_of_right_height_le (a:=u) (b:=r) (by omega)
      rw [hurs] at hos'
      have hp := Prod.mk.inj (Option.some.inj (hos'.symm.trans hos))
      have hgw : g = w := by dsimp only [g,w]; rw [hp.1]
      rw [hp.2] at hwr
      rw [hgw] at hgj
      exact False.elim (mul_ne_right V w (hgj.symm.trans hwr))
  obtain ⟨r,hsc,_,_,hdr,htr,hrs,_⟩ := nf_return_origin_trace hns hos hws htret
  have hwskey := nf_code_key_height_gap (hsc ▸ hns)
  rw [←hsc] at hwskey
  have hug := inverse_height_strict (inverse_complete u a)
  have haw := inverse_height_strict (inverse_complete a u)
  change ht u < max (ht a) (ht g) at hug
  change ht a < max (ht u) (ht w) at haw
  have hsg := mul_height_growth_of_right_le (a:=a) (b:=j) (by
    rw [haj]
    exact Nat.le_of_lt (origin_height hos).2)
  rw [haj] at hsg
  have hej : ht e < ht j := by
    by_cases hh : ht e < ht j
    · exact hh
    · have heg := mul_height_growth_of_right_le (a:=g) (b:=j) (by rw [hgj]; omega)
      rw [hgj] at heg
      by_cases hwe : ht w ≤ ht e
      · have hoe := mul_origin_of_right_height_le (a:=g) (b:=j) (by rw [hgj]; omega)
        rw [hgj] at hoe
        have hoe' := mul_origin_of_right_height_le (a:=V) (b:=w) hwe
        change origin e = some (V,w) at hoe'
        have hp := Prod.mk.inj (Option.some.inj (hoe.symm.trans hoe'))
        have hjw := congrArg ht hp.2
        exact False.elim (by omega)
      · exact False.elim (by omega)
  have hgjj := nf_mul_height_key_gap (a:=g) hnj
  rw [hgj] at hgjj
  have hgjlt : ht g < ht j := by rcases hgjj with hh | hh <;> omega
  have hor := mul_origin_of_right_height_le (a:=t) (b:=r) (by rw [htr]; omega)
  rw [htr] at hor
  exact ⟨t,j,r,hna,hat,⟨hnj,htr,hor,hgj,hdr⟩,hej,hvw⟩

end submission.Austin12087Trace

/- Checked module: TraceLeftFour -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

private theorem four_cycle_at_max {a x₀ x₁ x₂ x₃ : T}
    (hn₀ : NF x₀) (hn₂ : NF x₂) (hn₃ : NF x₃)
    (h₀ : mul a x₀ = x₁) (h₁ : mul a x₁ = x₂)
    (h₂ : mul a x₂ = x₃) (h₃ : mul a x₃ = x₀)
    (hm₁ : ht x₁ ≤ ht x₀) (hm₂ : ht x₂ ≤ ht x₀) (hm₃ : ht x₃ ≤ ht x₀) : False := by
  have hg₀ := nf_mul_height_key_gap (a:=a) hn₃
  rw [h₃] at hg₀
  have hx₀ : ht x₀ = max (ht a) (ht x₃) + 1 := by rcases hg₀ with hh | hh <;> omega
  have ho₀ := mul_origin_of_right_height_le (a:=a) (b:=x₃) (by rw [h₃]; omega)
  rw [h₃] at ho₀
  have hr₀ := nf_mul_height_key_gap (a:=a) hn₀
  rw [h₀] at hr₀
  have hx₁ : ht x₁ < ht x₀ := by rcases hr₀ with hh | hh <;> omega
  obtain ⟨z,_,_,_,h₂z,h₁z,_,_⟩ := nf_return_origin_trace hn₀ ho₀ h₀ hx₁
  have bounds := common_column_height_bounds h₂z h₁z
  rw [h₁] at h₂z
  have hg₃ := nf_mul_height_key_gap (a:=a) hn₂
  rw [h₂] at hg₃
  have hx₃ : ht x₃ = max (ht a) (ht x₂) + 1 := by rcases hg₃ with hh | hh <;> omega
  have ho₃ := mul_origin_of_right_height_le (a:=a) (b:=x₂) (by rw [h₂]; omega)
  rw [h₂] at ho₃
  have ho₃' := mul_origin_of_right_height_le (a:=x₁) (b:=z) (by rw [h₁z]; omega)
  rw [h₁z] at ho₃'
  have hp := Prod.mk.inj (Option.some.inj (ho₃'.symm.trans ho₃))
  have hs₂ : x₂ = s a := by rw [hp.1,mul_square] at h₁; exact h₁.symm
  rw [hp.2,mul_square,hs₂] at h₂z
  have hbad := congrArg ht h₂z
  simp only [ht] at hbad
  omega

theorem nf_no_left_four_cycle {a x : T} (ha : NF a) (hx : NF x) :
    mul a (mul a (mul a (mul a x))) ≠ x := by
  intro he
  let x₀ := x
  let x₁ := mul a x₀
  let x₂ := mul a x₁
  let x₃ := mul a x₂
  have hn₀ : NF x₀ := hx
  have hn₁ : NF x₁ := nf_mul ha hn₀
  have hn₂ : NF x₂ := nf_mul ha hn₁
  have hn₃ : NF x₃ := nf_mul ha hn₂
  have h₃ : mul a x₃ = x₀ := he
  by_cases hm₀ : ht x₁ ≤ ht x₀ ∧ ht x₂ ≤ ht x₀ ∧ ht x₃ ≤ ht x₀
  · exact four_cycle_at_max hn₀ hn₂ hn₃ rfl rfl rfl h₃ hm₀.1 hm₀.2.1 hm₀.2.2
  by_cases hm₁ : ht x₀ ≤ ht x₁ ∧ ht x₂ ≤ ht x₁ ∧ ht x₃ ≤ ht x₁
  · exact four_cycle_at_max hn₁ hn₃ hn₀ rfl rfl h₃ rfl hm₁.2.1 hm₁.2.2 hm₁.1
  by_cases hm₂ : ht x₀ ≤ ht x₂ ∧ ht x₁ ≤ ht x₂ ∧ ht x₃ ≤ ht x₂
  · exact four_cycle_at_max hn₂ hn₀ hn₁ rfl h₃ rfl rfl hm₂.2.2 hm₂.1 hm₂.2.1
  exact four_cycle_at_max hn₃ hn₁ hn₂ h₃ rfl rfl rfl (by omega) (by omega) (by omega)

end submission.Austin12087Trace

/- Checked module: TraceLargeHeadLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem return_from_column_product {u y a g V w e : T}
    (hV : mul y u = V) (hw : mul a u = w) (he : mul V w = e)
    (ho : origin e = some (V,w)) (hne : V ≠ w)
    (hr : ht (mul g e) < ht e) :
    e = c g a u V w ∧ mul g e = a ∧ mul g a = y := by
  obtain ⟨z,l,r,hc⟩ := mul_return_of_height_lt hr
  conv at ho => lhs; rw [hc,origin]
  obtain ⟨hl,hrr⟩ := Prod.mk.inj (Option.some.inj ho)
  subst l; subst r
  have hsem := mul_code_semantics (he.trans hc)
  have hzu := common_column_key_unique hsem.1 hsem.2 hV hw hne
  subst z
  have hfa := right_injective _ _ u (hsem.2.trans hw.symm)
  rw [hfa] at hc hsem
  have hgy := right_injective _ _ u (hsem.1.trans hV.symm)
  exact ⟨hc,hfa,hgy⟩

theorem large_head_return_ladder_impossible {u a y V w e t j r : T}
    (hna : NF a) (hnu : NF u) (hV : mul y u = V) (hw : mul a u = w)
    (he : mul V w = e) (hne : V ≠ w) (hat : mul a t = u)
    (hae : ht a < ht e) (hue : ht u < ht e) (hwe : ht w < ht e) (hte : ht t < ht e)
    (hl : ReturnLadder (mul u a) (mul w t) t e a j r) (hej : ht e < ht j) : False := by
  let g := mul u a
  let d := mul w t
  have hnw : NF w := hw ▸ nf_mul hna hnu
  have hoe := mul_origin_of_right_height_le (a:=V) (b:=w) (by rw [he]; omega)
  rw [he] at hoe
  have main : ∀ n, ∀ j r : T, ht j = n → ReturnLadder g d t e a j r → ht e < ht j → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j r hjn hl hej
      have hjg := mul_height_growth_of_right_le (a:=t) (b:=r) (by
        rw [hl.2.1]
        exact Nat.le_of_lt (origin_height hl.2.2.1).2)
      rw [hl.2.1] at hjg
      have hegap : ht e + 2 ≤ ht j := by
        have hp := nf_mul_height_key_gap (a:=g) hl.1
        rw [hl.2.2.2.1] at hp
        rcases hp with hp | hp <;> omega
      obtain ⟨h,hl₁,_⟩ := return_ladder_step hl hej (by omega)
      have hfa : ht (mul g e) < ht e := by
        by_cases hh : ht (mul g e) < ht e
        · exact hh
        · have hfg := mul_height_growth_of_right_le (a:=g) (b:=e) (by omega)
          exact False.elim (return_ladder_second_dominant_impossible hl₁ (by omega)
            (by omega) (by omega) (by omega))
      obtain ⟨hecode,hfa,_⟩ := return_from_column_product hV hw he hoe hne hfa
      rw [hfa] at hl₁
      change ReturnLadder d a e a t r h at hl₁
      have heh : ht e < ht h := by
        by_cases hh : ht e < ht h
        · exact hh
        · obtain ⟨z,_,_,_,hez,haz,_,_⟩ :=
            nf_return_origin_trace hl₁.1 hl₁.2.2.1 hl₁.2.2.2.1 (by omega)
          have hneh : e ≠ h := by
            intro heq
            exact mul_ne_right d a (right_injective _ _ z (hez.trans (heq.trans haz.symm)))
          have hoe' := (distinct_outputs_height_origin hez haz hneh (by omega)).1
          have hp := Prod.mk.inj (Option.some.inj (hoe'.symm.trans hoe))
          rw [hp.2] at haz
          have hcycle : mul a (mul a (mul a (mul a w))) = w := by
            rw [haz,hl₁.2.2.2.2,hat,hw]
          exact False.elim (nf_no_left_four_cycle hna hnw hcycle)
      obtain ⟨z,hl₂,_⟩ := return_ladder_step hl₁ (by omega) heh
      have hhg := mul_height_growth_of_right_le (a:=a) (b:=z) (by
        rw [hl₂.2.1]
        exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at hhg
      obtain ⟨l,hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      rw [hat] at hl₃
      change ReturnLadder (mul d a) u t e a z l at hl₃
      have hez : ht e < ht z := by
        have hp := nf_mul_height_key_gap (a:=mul d a) hl₃.1
        rw [hl₃.2.2.2.1] at hp
        rcases hp with hp | hp <;> omega
      by_cases hwa : w = a
      · have hd : d = u := by dsimp only [d]; rw [hwa,hat]
        have hlnew : ReturnLadder g d t e a z l := by
          change ReturnLadder (mul u a) d t e a z l
          simpa only [hd] using hl₃
        have hzh := (origin_height hl₂.2.2.1).2
        have hhr := (origin_height hl₁.2.2.1).2
        have hrj := (origin_height hl.2.2.1).2
        exact ih (ht z) (by omega) z l rfl hlnew hez
      · have hdg : mul d a ≠ g := by
          intro heq
          have hdu := right_injective _ _ a heq
          have hwa' := right_injective _ _ t (hdu.trans hat.symm)
          exact hwa hwa'
        have hzg := mul_height_growth_of_right_le (a:=t) (b:=l) (by
          rw [hl₃.2.1]
          exact Nat.le_of_lt (origin_height hl₃.2.2.1).2)
        rw [hl₃.2.1] at hzg
        obtain ⟨m,hl₄,_⟩ := return_ladder_step hl₃ hez (by omega)
        have hD := mul_height_off_return_key (a:=mul d a) hecode hdg
        exact return_ladder_second_dominant_impossible hl₄ (by omega)
          (by omega) (by omega) (by omega)
  exact main (ht j) j r rfl hl hej

end submission.Austin12087Trace

/- Checked module: TraceNonfixedSameKey -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

private theorem return_of_wrong_origin {a b out l r : T}
    (hm : mul a b = out) (ho : origin out = some (l,r)) (hne : a ≠ l) :
    ∃ z x y, b = c a out z x y := by
  rcases mul_height_shape a b with hg | ⟨v,z,x,y,hb,hv⟩
  · rw [hm] at hg
    exact False.elim (hne (Prod.mk.inj (Option.some.inj (hg.2.2.symm.trans ho))).1)
  · have he : v = out := hv.symm.trans hm
    exact ⟨z,x,y,by rw [he] at hb; exact hb⟩

theorem nonfixed_same_key_ladder_impossible {u a y V e t j r : T}
    (hna : NF a) (hnu : NF u) (hau : mul a u = a) (hat : mul a t = u)
    (hV : mul y u = V) (he : mul V a = e) (hne : V ≠ a)
    (hbig : ht u + 1 < ht e) (hte : ht e ≤ ht t)
    (hl : ReturnLadder (mul u a) u t e a j r) (hej : ht e < ht j) : False := by
  let g := mul u a
  let f := mul g e
  have hpu := nf_mul_height_key_gap (a:=a) hnu
  rw [hau] at hpu
  have hau3 : ht a + 3 ≤ ht u := by rcases hpu with hh | hh <;> omega
  have hg : ht g = ht u + 1 := by
    have hh := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hh
    omega
  have hoe := mul_origin_of_right_height_le (a:=V) (b:=a) (by rw [he]; omega)
  rw [he] at hoe
  have hag : a ≠ g := by intro h; exact mul_ne_right u a h.symm
  have hua : u ≠ a := by intro h; have hh := congrArg ht h; omega
  have hcases : f = a ∨ (ht f = ht e + 1 ∧ origin f = some (g,e)) := by
    by_cases hh : ht f < ht e
    · exact Or.inl (return_from_column_product hV hau he hoe hne hh).2.1
    · have hfg := mul_height_growth_of_right_le (a:=g) (b:=e) (by change ht e ≤ ht f; omega)
      have hof := mul_origin_of_right_height_le (a:=g) (b:=e) (by change ht e ≤ ht f; omega)
      change ht f = max (ht g) (ht e) + 1 at hfg
      exact Or.inr ⟨by omega,hof⟩
  have main : ∀ n, ∀ j r : T, ht j = n → ReturnLadder g u t e a j r → ht e < ht j → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j r hjn hl hej
      have hnt := (nf_origin hl.1 hl.2.2.1).1
      have hnr := (nf_origin hl.1 hl.2.2.1).2
      obtain ⟨zt,lt,rt,htcode⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; omega)
      rw [hat] at htcode
      have hir := inverse_height_strict (inverse_complete u r)
      rw [hl.2.2.2.2] at hir
      obtain ⟨zr,lr,rr,hrcode⟩ := mul_return_of_height_lt (a:=u) (b:=r) (by rw [hl.2.2.2.2]; omega)
      rw [hl.2.2.2.2] at hrcode
      have hur := nf_code_key_height_gap (hrcode ▸ hnr)
      rw [←hrcode] at hur
      by_cases htr : ht t < ht r
      · obtain ⟨h,hl₁,_⟩ := return_ladder_step hl hej htr
        change ReturnLadder u f e a t r h at hl₁
        have hrg := mul_height_growth_of_right_le (a:=e) (b:=h) (by
          rw [hl₁.2.1]
          exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
        rw [hl₁.2.1] at hrg
        have hnh := (nf_origin hl₁.1 hl₁.2.2.1).2
        have heh : ht e < ht h := by
          by_cases hh : ht e < ht h
          · exact hh
          · rcases hcases with hfa | ⟨hfg,_⟩
            · obtain ⟨z,_,_,_,hez,haz,_,_⟩ :=
                nf_return_origin_trace hl₁.1 hl₁.2.2.1 hl₁.2.2.2.1 (by omega)
              have hneh : e ≠ h := by
                intro heq
                exact mul_ne_right u a (right_injective _ _ z (hez.trans (heq.trans haz.symm)))
              have hoe' := (distinct_outputs_height_origin hez haz hneh (by omega)).1
              have hp := Prod.mk.inj (Option.some.inj (hoe'.symm.trans hoe))
              rw [hp.2] at haz
              have hath : mul a h = t := by rw [←hfa]; exact hl₁.2.2.2.2
              have hcycle : mul a (mul a (mul a (mul a a))) = a := by
                rw [haz,hath,hat,hau]
              exact False.elim (nf_no_left_four_cycle hna hna hcycle)
            · exact False.elim (return_ladder_second_dominant_impossible hl₁ (by omega)
                (by omega) (by omega) (by omega))
        have hth : ht t < ht h := by
          have hp := nf_mul_height_key_gap (a:=f) hnh
          rw [hl₁.2.2.2.2] at hp
          rcases hp with hp | hp <;> omega
        obtain ⟨z,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
        change ReturnLadder f g a t e h z at hl₂
        have hhg := mul_height_growth_of_right_le (a:=a) (b:=z) (by
          rw [hl₂.2.1]
          exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
        rw [hl₂.2.1] at hhg
        obtain ⟨l,hl₃,_⟩ := return_ladder_step hl₂ hth (by omega)
        have hez : ht e < ht z := by
          have hp := nf_mul_height_key_gap (a:=g) hl₃.1
          rw [hl₃.2.2.2.1] at hp
          rcases hp with hp | hp <;> omega
        rcases hcases with hfa | ⟨hfg,_⟩
        · rw [hfa,hat] at hl₃
          have hzh := (origin_height hl₂.2.2.1).2
          have hhr := (origin_height hl₁.2.2.1).2
          have hrj := (origin_height hl.2.2.1).2
          exact ih (ht z) (by omega) z l rfl hl₃ hez
        · have hft := mul_height_off_return_key (a:=f) htcode (by
            intro h
            have hh := congrArg ht h
            omega)
          exact return_ladder_second_dominant_impossible hl₃ hez (by omega) (by omega) (by omega)
      · obtain ⟨h,_,hnh,_,hfh,heh,_,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hej
        change mul f h = t at hfh
        have hfe : f ≠ e := by
          intro h
          have hh := congrArg ht h
          rcases hcases with hfa | hf
          · have ha' := congrArg ht hfa
            omega
          · omega
        have hne' : t ≠ r := by
          intro heq
          exact hfe (right_injective _ _ h (hfh.trans (heq.trans heh.symm)))
        have hot := (distinct_outputs_height_origin hfh heh hne' (by omega)).1
        obtain ⟨z,_,_,_,haz,huz,_,_⟩ := nf_return_origin_trace hnt hot hat (by omega)
        rw [hau] at haz
        have hzc : ∃ q l b, z = c a f q l b := by
          rcases hcases with hfa | ⟨_,hof⟩
          · have hi := inverse_height_strict (inverse_complete a z)
            rw [haz,hfa] at hi
            obtain ⟨q,l,b,hc⟩ := mul_return_of_height_lt (a:=a) (b:=z) (by rw [haz,hfa]; omega)
            rw [haz] at hc
            exact ⟨q,l,b,hc⟩
          · exact return_of_wrong_origin haz hof hag
        obtain ⟨qz,lz,bz,hzc⟩ := hzc
        have hgz := mul_height_off_return_key (a:=u) hzc hua
        have hoh := mul_origin_of_right_height_le (a:=u) (b:=z) (by omega)
        rw [huz] at hgz hoh
        have hfz : ht f < ht z := by rw [hzc]; simp only [ht]; omega
        have hrh : ht r < ht h := by
          by_cases hh : ht r < ht h
          · exact hh
          · have hor := mul_origin_of_right_height_le (a:=e) (b:=h) (by rw [heh]; omega)
            rw [heh] at hor
            obtain ⟨q,_,_,_,hgq,haq,_,_⟩ :=
              nf_return_origin_trace hnr hor hl.2.2.2.2 (by omega)
            change mul g q = e at hgq
            obtain ⟨zq,lq,rq,hqc⟩ := return_of_wrong_origin haq hoh (Ne.symm hua)
            have hgrowth := mul_height_off_return_key (a:=g) hqc (Ne.symm hag)
            rw [hgq] at hgrowth
            have hqh : ht h < ht q := by rw [hqc]; simp only [ht]; omega
            have hrg := mul_height_growth_of_right_le (a:=e) (b:=h) (by rw [heh]; omega)
            rw [heh] at hrg
            have htu := mul_height_upper f h
            rw [hfh] at htu
            exact False.elim (by omega)
        have hlh : ReturnLadder e a u r f h z := ⟨hnh,huz,hoh,heh,haz⟩
        obtain ⟨l,hl',_⟩ := return_ladder_step hlh hrh (by omega)
        have her := mul_height_off_return_key (a:=e) hrcode (by
          intro h
          have hh := congrArg ht h
          omega)
        have hfb : ht f ≤ ht (mul e r) := by
          rcases hcases with hfa | hf
          · have hh := congrArg ht hfa
            omega
          · omega
        exact return_ladder_second_dominant_impossible hl' hfz (by omega) hfb (by omega)
  exact main (ht j) j r rfl hl hej

end submission.Austin12087Trace

/- Checked module: TraceGeneralHeadExclusion -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem general_head_return_ladder_impossible {u a y V w e t j r : T}
    (hna : NF a) (hnu : NF u) (hV : mul y u = V) (hw : mul a u = w)
    (he : mul V w = e) (hne : V ≠ w) (hat : mul a t = u)
    (hl : ReturnLadder (mul u a) (mul w t) t e a j r) (hej : ht e < ht j) : False := by
  have hnt := (nf_origin hl.1 hl.2.2.1).1
  rcases nf_mul_height_key_gap (a:=a) hnu with hwg | ⟨hau,hwu⟩
  · rw [hw] at hwg
    have hwa : w ≠ a := by intro hh; have hh' := congrArg ht hh; omega
    have hd : ht (mul w t) = max (ht w) (ht t) + 1 := by
      by_cases htu : ht t ≤ ht u
      · exact mul_height_growth_of_left_ge (by omega)
      · obtain ⟨z,l,r,htc⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; omega)
        exact mul_height_off_return_key htc hwa
    have hde : ht (mul w t) < ht e := by
      by_cases hh : ht (mul w t) < ht e
      · exact hh
      · exact False.elim (return_ladder_second_dominant_impossible hl hej
          (by omega) (by omega) (by omega))
    exact large_head_return_ladder_impossible hna hnu hV hw he hne hat
      (by omega) (by omega) (by omega) (by omega) hl hej
  · rw [hw] at hwu
    obtain ⟨z,l,r,huc⟩ := mul_return_of_height_lt (a:=a) (b:=u) (by rw [hw]; omega)
    have hya : y ≠ a := by
      intro hh
      rw [hh,hw] at hV
      exact hne hV.symm
    have hVg := mul_height_off_return_key (a:=y) huc hya
    rw [hV] at hVg
    have heg := mul_height_growth_of_left_ge (a:=V) (b:=w) (by omega)
    rw [he] at heg
    have hbig : ht u + 1 < ht e := by omega
    by_cases hte : ht t < ht e
    · exact large_head_return_ladder_impossible hna hnu hV hw he hne hat
        (by omega) (by omega) (by omega) hte hl hej
    · obtain ⟨zt,lt,rt,htc⟩ := mul_return_of_height_lt (a:=a) (b:=t) (by rw [hat]; omega)
      by_cases hwa : w = a
      · rw [hwa,hat] at hl
        rw [hwa] at hw he hne
        exact nonfixed_same_key_ladder_impossible hna hnu hw hat hV he hne hbig (by omega) hl hej
      · have hd := mul_height_off_return_key (a:=w) htc hwa
        exact return_ladder_second_dominant_impossible hl hej (by omega) (by omega) (by omega)

theorem normal_first_larger_k_equation_impossible {u q k y : T}
    (hu : NF u) (hnk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz q ≤ sz k) : False := by
  have hqu := normal_first_larger_k_forces_repeated_key hu hnk hf hne hs
  subst q
  obtain ⟨t,j,r,hna,hat,hl,hej,hvw⟩ := normal_first_general_head_ladder hu hnk hne hs hf
  exact general_head_return_ladder_impossible hna hu rfl rfl rfl hvw hat hl hej

theorem normal_first_larger_k_query_absent (u q k : T) (hu : NF u) (hk : NF k)
    (hs : sz q ≤ sz k) :
    (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none := by
  by_cases hqk : q = k
  · subst q
    exact normal_first_diagonal_query_absent u k hu hk
  · cases h₁ : inverse k (mul (mul u (mul q (mul u k))) q) with
    | none => rfl
    | some w =>
      cases h₂ : inverse u w with
      | none => exact h₂
      | some y =>
        have hw := inverse_sound h₁
        have hy := inverse_sound h₂
        rw [←hy] at hw
        exact False.elim (normal_first_larger_k_equation_impossible hu hk hw hqk hs)

end submission.Austin12087Trace

/- Checked module: TraceFirstLargerQStructure -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem first_larger_q_inner_code {u q k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz k ≤ sz q) :
    ∃ j, mul q (mul u k) = c u (mul u (mul q (mul u k))) j q (mul u k) ∧
      mul (mul u (mul u (mul q (mul u k)))) j = q ∧
      mul (mul u (mul q (mul u k))) j = mul u k := by
  let v := mul u k
  let b := mul q v
  let a := mul u b
  obtain ⟨h,l,r,hqc⟩ := first_offdiagonal_larger_q_return hf hne hs
  change q = c a (mul (mul y u) k) h l r at hqc
  have haq : sz a < sz q := by rw [hqc]; simp only [sz]; omega
  have hbg : sz q < sz b ∧ origin b = some (q,v) := by
    rcases mul_grows_or_returns q v with hg | ⟨x,t,l',r',hvc,hx⟩
    · exact ⟨hg.1,hg.2.2⟩
    · have hxb : x = b := hx.symm
      rw [hxb] at hvc
      have hqv : sz q < sz v := by rw [hvc]; simp only [sz]; omega
      have hov : origin v = some (u,k) := by
        rcases mul_grows_or_returns u k with hv | ⟨z,t',l'',r'',hkc,hz⟩
        · exact hv.2.2
        · have hzk : sz z < sz k := by rw [hkc]; simp only [sz]; omega
          change v = z at hz
          have hh := congrArg sz hz
          exact False.elim (by omega)
      conv at hov => lhs; rw [hvc,origin]
      obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hov)
      subst l'; subst r'
      have hsem := mul_code_semantics (show mul u k = c q b t u k from hvc)
      have bounds := common_column_inputs_small hsem.1 hsem.2
      have hi := inverse_strict_size (inverse_complete u b)
      change sz u < max (sz b) (sz a) at hi
      exact False.elim (by omega)
  obtain ⟨x,j,l',r',hbc⟩ := (mul_small_iff u b).mp (by change sz a < sz b; omega)
  have hxa : x = a := by change x = mul u b; rw [hbc,mul_code_return]
  rw [hxa] at hbc
  have hob := hbg.2
  rw [hbc,origin] at hob
  obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hob)
  subst l'; subst r'
  have hsem := mul_code_semantics (show mul q v = c u a j q v from hbc)
  exact ⟨j,hbc,hsem⟩

theorem first_larger_q_height_order {u q k y : T}
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz k ≤ sz q) : ht (mul u k) ≤ ht q := by
  let v := mul u k
  let a := mul u (mul q v)
  obtain ⟨j,hbc,hgq,haj⟩ := first_larger_q_inner_code hf hne hs
  change mul (mul u a) j = q at hgq
  change mul a j = v at haj
  obtain ⟨h,l,r,hqc⟩ := first_offdiagonal_larger_q_return hf hne hs
  change q = c a (mul (mul y u) k) h l r at hqc
  have haq : ht a < ht q := by rw [hqc]; simp only [ht]; omega
  have hqv : q ≠ v := by
    intro heq
    exact mul_ne_right u a (right_injective _ _ j (hgq.trans (heq.trans haj.symm)))
  by_cases hvq : sz v ≤ sz q
  · have hoq := (distinct_outputs_large_origin hgq haj hqv hvq).1
    have hjq := (origin_height hoq).2
    have hp := mul_height_upper a j
    rw [haj] at hp
    change ht v ≤ ht q
    omega
  · have hov := (distinct_outputs_large_origin haj hgq (Ne.symm hqv) (by omega)).1
    have hov' := mul_origin_of_right_le (a:=u) (b:=k) (by change sz k ≤ sz v; omega)
    have heq := Prod.mk.inj (Option.some.inj (hov.symm.trans hov'))
    rw [heq.1,heq.2] at hgq
    have hoq := mul_origin_of_right_le (a:=mul u u) (b:=k) (by rw [hgq]; exact hs)
    rw [hgq] at hoq
    have hkq := (origin_height hoq).2
    have hqg := mul_height_growth_of_right_le (a:=mul u u) (b:=k) (by rw [hgq]; omega)
    rw [hgq,mul_square] at hqg
    simp only [ht] at hqg
    have hv := mul_height_upper u k
    change ht v ≤ ht q
    change ht v ≤ max (ht u) (ht k) + 1 at hv
    omega

theorem normal_first_larger_q_trace {u q k y : T}
    (hu : NF u) (hq : NF q) (hk : NF k)
    (hf : mul (mul y u) k = mul (mul u (mul q (mul u k))) q)
    (hne : q ≠ k) (hs : sz k ≤ sz q) :
    let v := mul u k
    let b := mul q v
    let a := mul u b
    let w := mul (mul y u) k
    ∃ j h, NF a ∧ NF j ∧ b = c u a j q v ∧
      q = c a w h (mul u a) j ∧
      mul (mul u a) j = q ∧ mul a j = v ∧
      mul (mul a w) h = mul u a ∧ mul w h = j ∧
      ht v ≤ ht q ∧ ht u < ht q ∧ ht w < ht q ∧
      ReturnLadder a a (mul u a) w v q j := by
  let v := mul u k
  let b := mul q v
  let a := mul u b
  let w := mul (mul y u) k
  obtain ⟨j,hbc,hgq,haj⟩ := first_larger_q_inner_code hf hne hs
  change b = c u a j q v at hbc
  change mul (mul u a) j = q at hgq
  change mul a j = v at haj
  have hvq := first_larger_q_height_order hf hne hs
  change ht v ≤ ht q at hvq
  have hnb : NF b := nf_mul hq (nf_mul hu hk)
  have hna : NF a := nf_mul hu hnb
  have hnj : NF j := (nf_code_actual (hbc ▸ hnb)).2.2.1
  have hqv : q ≠ v := by
    intro heq
    exact mul_ne_right u a (right_injective _ _ j (hgq.trans (heq.trans haj.symm)))
  have hoq := (distinct_outputs_height_origin hgq haj hqv hvq).1
  obtain ⟨h',l',r',hqc'⟩ := first_offdiagonal_larger_q_return hf hne hs
  change q = c a w h' l' r' at hqc'
  have hwq : ht w < ht q := by rw [hqc']; simp only [ht]; omega
  have haq : mul a q = w := hf.symm
  obtain ⟨h,hqc,_,_,hgh,hwh,_,_⟩ := nf_return_origin_trace hq hoq haq hwq
  have hbg := mul_height_growth_of_right_le (a:=q) (b:=v) (by
    change ht v ≤ ht b
    rw [hbc]; simp only [ht]; omega)
  change ht b = max (ht q) (ht v) + 1 at hbg
  have hub := nf_code_key_height_gap (hbc ▸ hnb)
  rw [←hbc] at hub
  exact ⟨j,h,hna,hnj,hbc,hqc,hgq,haj,hgh,hwh,hvq,by omega,hwq,
    hq,hgq,hoq,haq,haj⟩

end submission.Austin12087Trace

/- Checked module: TraceLargerQHeadOrder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nf_common_column_head_order {u a y k v w j h : T}
    (hnw : NF w) (hnk : NF k)
    (hv : mul u k = v) (hw : mul (mul y u) k = w)
    (haj : mul a j = v) (hgh : mul (mul a w) h = mul u a)
    (hwh : mul w h = j) (hhg : ht h < ht (mul u a)) :
    ht (mul u a) < ht j := by
  by_cases hgj : ht (mul u a) < ht j
  · exact hgj
  · let g := mul u a
    let d := mul a w
    change ht h < ht g at hhg
    change ¬ht g < ht j at hgj
    change mul d h = g at hgh
    have hgg := mul_height_growth_of_right_le (a:=d) (b:=h) (by rw [hgh]; omega)
    rw [hgh] at hgg
    have hiw := inverse_height_strict (inverse_complete w h)
    rw [hwh] at hiw
    have hia := inverse_height_strict (inverse_complete a w)
    change ht a < max (ht w) (ht d) at hia
    have haw : ht a < ht g := by omega
    have hug := mul_height_growth_of_right_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
    change ht g = max (ht u) (ht a) + 1 at hug
    have hau : ht a < ht u := by
      by_cases hh : ht a < ht u
      · exact hh
      · have hp := nf_mul_height_key_gap (a:=a) hnw
        change ht d = max (ht a) (ht w) + 1 ∨
          (ht a + 3 ≤ ht w ∧ ht d + 2 ≤ ht w) at hp
        rcases hp with hp | hp <;> exact False.elim (by omega)
    have hvk : ht k ≤ ht v := by
      by_cases hh : ht k ≤ ht v
      · exact hh
      · obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt (a:=u) (b:=k) (by rw [hv]; omega)
        have huk := nf_code_key_height_gap (hkc ▸ hnk)
        rw [←hkc] at huk
        have hwg := mul_height_off_return_key (a:=mul y u) hkc (mul_ne_right y u)
        rw [hw] at hwg
        exact False.elim (by omega)
    have hvg := mul_height_growth_of_right_le (a:=u) (b:=k) (by rw [hv]; exact hvk)
    rw [hv] at hvg
    have hov := mul_origin_of_right_height_le (a:=u) (b:=k) (by rw [hv]; exact hvk)
    rw [hv] at hov
    have hov' := mul_origin_of_right_height_le (a:=a) (b:=j) (by rw [haj]; omega)
    rw [haj] at hov'
    have hua := (Prod.mk.inj (Option.some.inj (hov.symm.trans hov'))).1
    have hh := congrArg ht hua
    exact False.elim (by omega)

theorem normal_first_larger_q_column_order {u q k y j h : T}
    (hq : NF q) (hk : NF k)
    (hqc : q = c (mul u (mul q (mul u k))) (mul (mul y u) k) h
      (mul u (mul u (mul q (mul u k)))) j)
    (haj : mul (mul u (mul q (mul u k))) j = mul u k) :
    ht (mul u (mul u (mul q (mul u k)))) < ht j := by
  let a := mul u (mul q (mul u k))
  let w := mul (mul y u) k
  change q = c a w h (mul u a) j at hqc
  have hnf := nf_code_actual (hqc ▸ hq)
  have hnw : NF w := hnf.2.1
  have hhq := (nf_code_height_gap (hqc ▸ hq)).2.2
  rw [←hqc] at hhq
  have hsem := hnf.2.2.2.2.2.2
  have hactual := hnf.2.2.2.2.2.1
  rw [←hqc] at hactual
  have hqg := mul_height_growth_of_right_le (a:=mul u a) (b:=j) (by
    rw [hactual,hqc]; simp only [ht]; omega)
  rw [hactual] at hqg
  by_cases hgj : ht (mul u a) < ht j
  · exact hgj
  · exact nf_common_column_head_order hnw hk rfl rfl haj hsem.1 hsem.2 (by
      change ht h < ht (mul u a)
      omega)

end submission.Austin12087Trace

/- Checked module: TraceReturnProductGap -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nf_code_product_height_gap {a x z l r : T} (hn : NF (c a x z l r)) :
    ht (mul a x) + 2 ≤ ht (c a x z l r) := by
  have hs := (nf_code_actual hn).2.2.2.2.2.2.1
  have hi := inverse_height_strict (inverse_complete (mul a x) z)
  rw [hs] at hi
  simp only [ht]
  omega

theorem nf_return_product_height_gap {a b out : T} (hn : NF b)
    (hm : mul a b = out) (hh : ht out < ht b) :
    ht (mul a out) + 2 ≤ ht b := by
  obtain ⟨z,l,r,hc⟩ := mul_return_of_height_lt (a:=a) (b:=b) (by rw [hm]; exact hh)
  rw [hm] at hc
  have hg := nf_code_product_height_gap (hc ▸ hn)
  rw [←hc] at hg
  exact hg

theorem nf_return_target_or_key_gap {a b out : T} (hn : NF b)
    (hm : mul a b = out) (hh : ht out < ht b) :
    ht out + 3 ≤ ht b ∨ ht a + 3 ≤ ht out := by
  obtain ⟨z,l,r,hc⟩ := mul_return_of_height_lt (a:=a) (b:=b) (by rw [hm]; exact hh)
  rw [hm] at hc
  have hno := (nf_code_actual (hc ▸ hn)).2.1
  have hg := nf_return_product_height_gap hn hm hh
  rcases nf_mul_height_key_gap (a:=a) hno with hp | hp
  · exact Or.inl (by omega)
  · exact Or.inr hp.1

end submission.Austin12087Trace

/- Checked module: TraceLowerQuerySource -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_critical_excluded_by_lower_queries {x y z q t l r : T}
    (hnx : NF x) (hny : NF y) (hnz : NF z)
    (hf : ∀ u q' k : T, NF u → NF q' → NF k →
      ht u < max (ht x) (ht z) → ht q' < max (ht x) (ht z) → ht k < max (ht x) (ht z) →
      (inverse k (mul (mul u (mul q' (mul u k))) q')).bind (inverse u) = none)
    (hs : ∀ u a k : T, NF u → NF a → NF k →
      ht u < max (ht x) (ht z) → ht a < max (ht x) (ht z) → ht k < max (ht x) (ht z) →
      inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none)
    (he : mul x z = c (mul (mul y x) z) q t l r) : False := by
  obtain ⟨hl,hr,hx,hz⟩ := critical_return_trace he
  subst l; subst r
  obtain ⟨hnu,hna,hnq,_⟩ := nf_critical_parameters hnx hny hnz he
  have hqgap := (nf_code_height_gap (he ▸ nf_mul hnx hnz)).2.1
  rw [←he] at hqgap
  have hbg := mul_height_growth_of_right_le (a:=x) (b:=z) (by
    rw [he]; simp only [ht]; omega)
  by_cases hsz : sz z ≤ sz x
  · obtain ⟨k,hcode,hv,ht⟩ := critical_x_max he hsz
    have hnc := nf_code_actual (hcode ▸ hnx)
    have hnk := hnc.2.2.1
    have hgap := nf_code_height_gap (hcode ▸ hnx)
    rw [←hcode] at hgap
    have h1 := inverse_complete (mul y (mul y x)) k
    rw [hv] at h1
    have h2 := inverse_complete y (mul y x)
    have hquery := hf (mul y x) q k hnu hnq hnk (by omega) (by omega) (by omega)
    rw [ht,hz,h1,Option.bind_some,h2] at hquery
    cases hquery
  · obtain ⟨k,hcode,hq,ht⟩ := critical_z_max he (by omega)
    have hnc := nf_code_actual (hcode ▸ hnz)
    have hnk := hnc.2.2.1
    have hgap := nf_code_height_gap (hcode ▸ hnz)
    rw [←hcode] at hgap
    have hquery := hs (mul y x) (mul (mul y x) z) k hnu hna hnk
      (by omega) (by omega) (by omega)
    rw [hq,ht,hx,inverse_complete] at hquery
    cases hquery

theorem normal_source_of_lower_queries {x y z : T}
    (hnx : NF x) (hny : NF y) (hnz : NF z)
    (hf : ∀ u q k : T, NF u → NF q → NF k →
      ht u < max (ht x) (ht z) → ht q < max (ht x) (ht z) → ht k < max (ht x) (ht z) →
      (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none)
    (hs : ∀ u a k : T, NF u → NF a → NF k →
      ht u < max (ht x) (ht z) → ht a < max (ht x) (ht z) → ht k < max (ht x) (ht z) →
      inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none) : Source12087 x y z := by
  apply source_without_middle_return
  intro q t l r he
  exact normal_critical_excluded_by_lower_queries hnx hny hnz hf hs he

end submission.Austin12087Trace

/- Checked module: TraceSecondSuffices -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_first_of_second (hs : NormalSecondCycleAbsent) : NormalFirstCycleAbsent := by
  have main : ∀ n, ∀ u q k : T, NF u → NF q → NF k → ht q = n →
      (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro u q k hu hq hk hqn
      by_cases hsize : sz q ≤ sz k
      · exact normal_first_larger_k_query_absent u q k hu hk hsize
      · have hne : q ≠ k := by intro heq; rw [heq] at hsize; exact hsize (Nat.le_refl _)
        cases h₁ : inverse k (mul (mul u (mul q (mul u k))) q) with
        | none => rfl
        | some V =>
          cases h₂ : inverse u V with
          | none => exact h₂
          | some y =>
            have hf := inverse_sound h₁
            have hy := inverse_sound h₂
            rw [←hy] at hf
            let a := mul u (mul q (mul u k))
            let w := mul (mul y u) k
            obtain ⟨j,h,hna,hnj,hbc,hqc,hgq,haj,had,hwh,hvq,huq,hwq,hl⟩ :=
              normal_first_larger_q_trace hu hq hk hf hne (by omega)
            change NF a at hna
            change mul (mul u a) j = q at hgq
            change mul a j = mul u k at haj
            change ht w < ht q at hwq
            change q = c a w h (mul u a) j at hqc
            have hnw := (nf_code_actual (hqc ▸ hq)).2.1
            have hnV := nf_inverse hk hnw (inverse_complete (mul y u) k)
            have hny := nf_inverse hu hnV (inverse_complete y u)
            have bounds := common_column_height_bounds
              (show mul (mul y u) k = w from rfl) (show mul u k = mul u k from rfl)
            have hkq : ht k < ht q := by omega
            have hsrc := normal_source_of_lower_queries hu hny hk
              (by
                intro u' q' k' hu' hq' hk' _ hqsmall _
                exact ih (ht q') (by omega) u' q' k' hu' hq' hk' rfl)
              (by
                intro u' a' k' hu' ha' hk' _ _ _
                exact hs u' a' k' hu' ha' hk')
            change u = mul y (mul w (mul u k)) at hsrc
            have hi := inverse_complete y (mul w (mul u k))
            rw [←hsrc] at hi
            have hwa : mul a q = w := hf.symm
            have hquery := hs u a j hu hna hnj
            rw [hgq,haj,hwa,hi] at hquery
            cases hquery
  intro u q k hu hq hk
  exact main (ht q) u q k hu hq hk rfl

theorem normal_source_of_second (hs : NormalSecondCycleAbsent)
    {x y z : T} (hx : NF x) (hy : NF y) (hz : NF z) : Source12087 x y z := by
  exact nf_source_of_normal_queries (normal_first_of_second hs) hs x y z hx hy hz

theorem normal_law_of_second_query_absence (hs : NormalSecondCycleAbsent) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) := by
  exact normal_law_of_normal_queries (normal_first_of_second hs) hs

end submission.Austin12087Trace

/- Checked module: TraceSecondMaxHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_max_u_head {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hau : ht a ≤ ht u) (hku : ht k ≤ ht u)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    let w := mul a (mul (mul u a) k)
    mul a w = u ∧ mul w a = k ∧ ht a < ht u ∧ ht w < ht u := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change mul a w = u ∧ mul w a = k ∧ ht a < ht u ∧ ht w < ht u
  have hng : NF g := nf_mul hu ha
  have hnq : NF q := nf_mul hng hk
  have hnv : NF v := nf_mul ha hk
  have hnw : NF w := nf_mul ha hnq
  have hne : NF e := nf_mul hnw hnv
  have hgg := mul_height_growth_of_left_ge (a:=u) (b:=a) hau
  change ht g = max (ht u) (ht a) + 1 at hgg
  have hqg := mul_height_growth_of_left_ge (a:=g) (b:=k) (by omega)
  change ht q = max (ht g) (ht k) + 1 at hqg
  have hvu := mul_height_upper a k
  change ht v ≤ max (ht a) (ht k) + 1 at hvu
  have how : ht w < ht q := by
    by_cases hh : ht w < ht q
    · exact hh
    · have hwg := mul_height_growth_of_right_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
      change ht w = max (ht a) (ht q) + 1 at hwg
      have how := mul_origin_of_right_height_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
      change origin w = some (a,q) at how
      have heg := mul_height_growth_of_left_ge (a:=w) (b:=v) (by omega)
      change ht e = max (ht w) (ht v) + 1 at heg
      have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
      change origin e = some (w,v) at hoe
      obtain ⟨h,_,_,_,hfh,huh,_,_⟩ := nf_return_origin_trace hne hoe hf (by omega)
      have hwv : w ≠ v := by intro heq; have hh' := congrArg ht heq; omega
      have how' := (distinct_outputs_height_origin hfh huh hwv (by omega)).1
      have hp := Prod.mk.inj (Option.some.inj (how'.symm.trans how))
      rw [hp.2] at huh
      exact False.elim (nf_no_flip hu ha hk huh)
  have hoq := mul_origin_of_right_height_le (a:=g) (b:=k) (by change ht k ≤ ht q; omega)
  change origin q = some (g,k) at hoq
  obtain ⟨r,hqc,_,_,hbr,hwr,hrr,haq⟩ :=
    nf_return_origin_trace hnq hoq (show mul a q = w from rfl) how
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change origin g = some (u,a) at hog
  have hog' := mul_origin_of_right_height_le (a:=mul a w) (b:=r) (by rw [hbr]; omega)
  rw [hbr] at hog'
  have hp := Prod.mk.inj (Option.some.inj (hog'.symm.trans hog))
  have hwa : mul w a = k := by rw [hp.2] at hwr; exact hwr
  have hwu := mul_height_growth_of_right_le (a:=a) (b:=w) (by
    rw [hp.1]
    have hwq := (nf_code_height_gap (hqc ▸ hnq)).2.1
    rw [←hqc] at hwq
    omega)
  rw [hp.1] at hwu
  exact ⟨hp.1,hwa,by omega,by omega⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondMaxExclusion -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nf_transposed_pair_no_preimage {a w y : T} (ha : NF a) (hw : NF w)
    (hau : ht a < ht (mul a w)) (hwu : ht w < ht (mul a w)) :
    mul y (mul w (mul a (mul w a))) ≠ mul a w := by
  intro hf
  let u := mul a w
  let k := mul w a
  let v := mul a k
  let e := mul w v
  change mul y e = u at hf
  change ht a < ht u at hau
  change ht w < ht u at hwu
  have hk : NF k := nf_mul hw ha
  have hv : NF v := nf_mul ha hk
  have he : NF e := nf_mul hw hv
  have hug := mul_height_growth_of_right_le (a:=a) (b:=w) (by change ht w ≤ ht u; omega)
  change ht u = max (ht a) (ht w) + 1 at hug
  have hku := mul_height_upper w a
  change ht k ≤ max (ht w) (ht a) + 1 at hku
  have hvu := mul_height_upper a k
  change ht v ≤ max (ht a) (ht k) + 1 at hvu
  have hpout := nf_mul_height_key_gap (a:=y) he
  rw [hf] at hpout
  by_cases hev : ht e < ht v
  · have hpv := nf_mul_height_key_gap (a:=w) hv
    change ht e = max (ht w) (ht v) + 1 ∨ (ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at hpv
    have hret : ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v := by
      rcases hpv with hpv | hpv
      · exact False.elim (by omega)
      · exact hpv
    have hou := mul_origin_of_right_height_le (a:=a) (b:=w) (by change ht w ≤ ht u; omega)
    change origin u = some (a,w) at hou
    have hou' := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; omega)
    rw [hf] at hou'
    have hew : e = w := (Prod.mk.inj (Option.some.inj (hou'.symm.trans hou))).2
    have hkv : ht k ≤ ht v := by
      have hp := nf_mul_height_key_gap (a:=a) hk
      change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hp
      rcases hp with hp | hp
      · omega
      · have hp' := nf_mul_height_key_gap (a:=w) ha
        change ht k = max (ht w) (ht a) + 1 ∨ (ht w + 3 ≤ ht a ∧ ht k + 2 ≤ ht a) at hp'
        rcases hp' with hp' | hp' <;> exact False.elim (by omega)
    have hov := mul_origin_of_right_height_le (a:=a) (b:=k) hkv
    change origin v = some (a,k) at hov
    obtain ⟨t,_,hnt,_,hs,ht',_,_⟩ :=
      nf_return_origin_trace hv hov (show mul w v = e from rfl) hev
    rw [hew] at hs ht'
    have hflip : mul w (mul (mul w w) t) = mul w t := by
      rw [hs]
      exact ht'.symm
    exact nf_no_flip hw hw hnt hflip
  · have heg := mul_height_growth_of_right_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
    change ht e = max (ht w) (ht v) + 1 at heg
    have hkv : ht k ≤ ht v := by
      have hp := nf_mul_height_key_gap (a:=a) hk
      change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hp
      rcases hp with hp | hp
      · omega
      · have hp' := nf_mul_height_key_gap (a:=w) ha
        change ht k = max (ht w) (ht a) + 1 ∨ (ht w + 3 ≤ ht a ∧ ht k + 2 ≤ ht a) at hp'
        rcases hp' with hp' | hp'
        · rcases hpout with hpout | hpout <;> exact False.elim (by omega)
        · exact False.elim (by omega)
    have hvg := mul_height_growth_of_right_le (a:=a) (b:=k) hkv
    change ht v = max (ht a) (ht k) + 1 at hvg
    have hkg : ht k = ht u := by
      have hp := nf_mul_height_key_gap (a:=w) ha
      change ht k = max (ht w) (ht a) + 1 ∨ (ht w + 3 ≤ ht a ∧ ht k + 2 ≤ ht a) at hp
      rcases hp with hp | hp
      · omega
      · rcases hpout with hpout | hpout <;> exact False.elim (by omega)
    have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
    change origin e = some (w,v) at hoe
    obtain ⟨t,_,_,_,hwt,hvt,_,_⟩ := nf_return_origin_trace he hoe hf (by omega)
    have hvw : v ≠ w := by intro heq; have hh := congrArg ht heq; omega
    have hov := (distinct_outputs_height_origin hvt hwt hvw (by omega)).1
    have hov' := mul_origin_of_right_height_le (a:=a) (b:=k) hkv
    change origin v = some (a,k) at hov'
    have hua := (Prod.mk.inj (Option.some.inj (hov.symm.trans hov'))).1
    have hh := congrArg ht hua
    omega

theorem normal_second_max_u_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hau : ht a ≤ ht u) (hku : ht k ≤ ht u)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) : False := by
  let w := mul a (mul (mul u a) k)
  obtain ⟨haw,hwa,ha',hw'⟩ := normal_second_max_u_head hu ha hk hau hku hf
  change mul a w = u at haw
  change mul w a = k at hwa
  change ht w < ht u at hw'
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hh := nf_transposed_pair_no_preimage (y:=y) ha hnw (by rw [haw]; exact ha') (by rw [haw]; exact hw')
  rw [hwa,haw] at hh
  exact hh hf

theorem normal_second_query_height_order {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    ht u < max (ht a) (ht k) := by
  by_cases hh : ht u < max (ht a) (ht k)
  · exact hh
  · exact False.elim (normal_second_max_u_impossible hu ha hk (by omega) (by omega) hf)

end submission.Austin12087Trace

/- Checked module: TraceSecondMaxA -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_max_a_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hua : ht u ≤ ht a) (hka : ht k ≤ ht a)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  have hnv : NF v := nf_mul ha hk
  have hnw : NF w := nf_mul ha hnq
  have hne : NF e := nf_mul hnw hnv
  have hgu := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hgu
  have hqu := mul_height_upper g k
  change ht q ≤ max (ht g) (ht k) + 1 at hqu
  have hvg := mul_height_growth_of_left_ge (a:=a) (b:=k) hka
  change ht v = max (ht a) (ht k) + 1 at hvg
  have hwg : ht w = max (ht a) (ht q) + 1 := by
    have hp := nf_mul_height_key_gap (a:=a) hnq
    change ht w = max (ht a) (ht q) + 1 ∨ (ht a + 3 ≤ ht q ∧ ht w + 2 ≤ ht q) at hp
    rcases hp with hp | hp
    · exact hp
    · exact False.elim (by omega)
  have how := mul_origin_of_right_height_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
  change origin w = some (a,q) at how
  have heg := mul_height_growth_of_left_ge (a:=w) (b:=v) (by omega)
  change ht e = max (ht w) (ht v) + 1 at heg
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
  change origin e = some (w,v) at hoe
  obtain ⟨t,_,_,_,hft,hut,_,_⟩ := nf_return_origin_trace hne hoe hf (by omega)
  have hwv : w ≠ v := by
    intro heq
    exact mul_ne_right y u (right_injective _ _ t (hft.trans (heq.trans hut.symm)))
  have how' := (distinct_outputs_height_origin hft hut hwv (by omega)).1
  have hp := Prod.mk.inj (Option.some.inj (how'.symm.trans how))
  rw [hp.2] at hut
  exact nf_no_flip hu ha hk hut

theorem normal_second_query_k_dominates {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    ht u < ht k ∧ ht a < ht k := by
  have hu' := normal_second_query_height_order hu ha hk hf
  have ha' : ht a < max (ht u) (ht k) := by
    by_cases hh : ht a < max (ht u) (ht k)
    · exact hh
    · exact False.elim (normal_second_max_a_impossible hu ha hk (by omega) (by omega) hf)
  exact ⟨by omega,by omega⟩

end submission.Austin12087Trace

/- Checked module: TraceNestedRightLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem nested_right_return_ladder_impossible {c d h z k x y A B j r : T}
    (hoc : origin c = some (d,k)) (hod : origin d = some (h,z))
    (hxd : ht x < ht d) (hxz : x ≠ z) (hyc : ht y < ht c)
    (hl : ReturnLadder A B c x y j r) : False := by
  have hdc := (origin_height hoc).1
  have main : ∀ n, ∀ A B j r : T, ht j = n → ReturnLadder A B c x y j r → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro A B j r hjn hl
      have hcj := (origin_height hl.2.2.1).1
      have hrj := (origin_height hl.2.2.1).2
      have hcr : ht c < ht r := by
        by_cases hh : ht c < ht r
        · exact hh
        · obtain ⟨t,_,_,_,hct,hrt,_,_⟩ :=
            nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 (by omega)
          have hne : c ≠ r := by
            intro heq
            exact mul_ne_right A x (right_injective _ _ t (hct.trans (heq.trans hrt.symm)))
          have hoc' := (distinct_outputs_height_origin hct hrt hne (by omega)).1
          have hp := Prod.mk.inj (Option.some.inj (hoc'.symm.trans hoc))
          have hod' := mul_origin_of_right_height_le (a:=A) (b:=x) (by rw [hp.1]; omega)
          rw [hp.1] at hod'
          have hp' := Prod.mk.inj (Option.some.inj (hod'.symm.trans hod))
          exact False.elim (hxz hp'.2)
      obtain ⟨t,hl₁,_⟩ := return_ladder_step hl (by omega) hcr
      have hnt := (nf_origin hl₁.1 hl₁.2.2.1).2
      have hrg := mul_height_growth_of_right_le (a:=x) (b:=t) (by
        rw [hl₁.2.1]
        exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
      rw [hl₁.2.1] at hrg
      have hct : ht c + 2 ≤ ht t := by
        have hp := nf_mul_height_key_gap (a:=mul A x) hnt
        rw [hl₁.2.2.2.2] at hp
        rcases hp with hp | hp
        · exact False.elim (by omega)
        · exact hp.2
      obtain ⟨s,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      have htg := mul_height_growth_of_right_le (a:=y) (b:=s) (by
        rw [hl₂.2.1]
        exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at htg
      obtain ⟨t',hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      have hst := (origin_height hl₂.2.2.1).2
      have htr := (origin_height hl₁.2.2.1).2
      exact ih (ht s) (by omega) (mul B y) (mul (mul A x) c) s t' rfl hl₃
  exact main (ht j) A B j r rfl hl

end submission.Austin12087Trace

/- Checked module: TraceSecondDoubleGrowth -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_double_growth_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hve : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k)))
    (heu : ht (mul (mul a (mul (mul u a) k)) (mul a k)) ≤ ht u) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change ht v ≤ ht e at hve
  change ht e ≤ ht u at heu
  change mul y e = u at hf
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  have heg := mul_height_growth_of_right_le (a:=w) (b:=v) hve
  change ht e = max (ht w) (ht v) + 1 at heg
  have hug := mul_height_growth_of_right_le (a:=y) (b:=e) (by rw [hf]; exact heu)
  rw [hf] at hug
  have hou := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; exact heu)
  rw [hf] at hou
  have hbounds := normal_second_query_k_dominates hu ha hk hf
  obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt (a:=a) (b:=k) (by change ht v < ht k; omega)
  have hqg := mul_height_off_return_key (a:=g) hkc (mul_ne_right u a)
  change ht q = max (ht g) (ht k) + 1 at hqg
  have hoq := mul_origin_of_right_height_le (a:=g) (b:=k) (by change ht k ≤ ht q; omega)
  change origin q = some (g,k) at hoq
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  have hl : ReturnLadder a a g w v q k := ⟨hnq,rfl,hoq,rfl,rfl⟩
  by_cases hag : ht a ≤ ht g
  · have hgg := mul_height_growth_of_right_le (a:=u) (b:=a) hag
    change ht g = max (ht u) (ht a) + 1 at hgg
    have hog := mul_origin_of_right_height_le (a:=u) (b:=a) hag
    change origin g = some (u,a) at hog
    exact nested_right_return_ladder_impossible hog hou (by omega)
      (by intro heq; have hh := congrArg ht heq; omega) (by omega) hl
  · have hp := nf_mul_height_key_gap (a:=u) ha
    change ht g = max (ht u) (ht a) + 1 ∨ (ht u + 3 ≤ ht a ∧ ht g + 2 ≤ ht a) at hp
    rcases hp with hp | hp
    · omega
    · exact return_ladder_dominant_impossible hl (by omega) (by omega) (by omega)

theorem normal_second_growth_order {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k)) ∨
      ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k) := by
  by_cases hh : ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k))
  · exact Or.inl hh
  · by_cases hv : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))
    · exact False.elim (normal_second_double_growth_impossible hu ha hk hf hv (by omega))
    · exact Or.inr (by omega)

end submission.Austin12087Trace

/- Checked module: TraceLocalSecondInduction -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

def NormalFirstBelow (n : Nat) : Prop := ∀ u q k : T, NF u → NF q → NF k →
  ht u < n → ht q < n → ht k < n →
  (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none

def NormalSecondBelow (n : Nat) : Prop := ∀ u a k : T, NF u → NF a → NF k →
  ht u < n → ht a < n → ht k < n →
  inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none

theorem normal_first_below_of_second_below {n : Nat} (hs : NormalSecondBelow n) :
    NormalFirstBelow n := by
  have main : ∀ m, ∀ u q k : T, NF u → NF q → NF k → ht q = m →
      ht u < n → ht q < n → ht k < n →
      (inverse k (mul (mul u (mul q (mul u k))) q)).bind (inverse u) = none := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro u q k hu hq hk hqm hun hqn hkn
      by_cases hsize : sz q ≤ sz k
      · exact normal_first_larger_k_query_absent u q k hu hk hsize
      · have hneq : q ≠ k := by intro heq; rw [heq] at hsize; exact hsize (Nat.le_refl _)
        cases h₁ : inverse k (mul (mul u (mul q (mul u k))) q) with
        | none => rfl
        | some V =>
          cases h₂ : inverse u V with
          | none => exact h₂
          | some y =>
            have hf := inverse_sound h₁
            have hy := inverse_sound h₂
            rw [←hy] at hf
            let a := mul u (mul q (mul u k))
            let w := mul (mul y u) k
            obtain ⟨j,h,hna,hnj,hbc,hqc,hgq,haj,had,hwh,hvq,huq,hwq,hl⟩ :=
              normal_first_larger_q_trace hu hq hk hf hneq (by omega)
            change NF a at hna
            change mul (mul u a) j = q at hgq
            change mul a j = mul u k at haj
            change ht w < ht q at hwq
            change q = c a w h (mul u a) j at hqc
            have hanc := nf_code_key_height_gap (hqc ▸ hq)
            rw [←hqc] at hanc
            have hjq := (origin_height hl.2.2.1).2
            have hnw := (nf_code_actual (hqc ▸ hq)).2.1
            have hnV := nf_inverse hk hnw (inverse_complete (mul y u) k)
            have hny := nf_inverse hu hnV (inverse_complete y u)
            have bounds := common_column_height_bounds
              (show mul (mul y u) k = w from rfl) (show mul u k = mul u k from rfl)
            have hkq : ht k < ht q := by omega
            have hsrc := normal_source_of_lower_queries hu hny hk
              (by
                intro u' q' k' hu' hq' hk' hus hqs hks
                exact ih (ht q') (by omega) u' q' k' hu' hq' hk' rfl
                  (by omega) (by omega) (by omega))
              (by
                intro u' a' k' hu' ha' hk' hus has hks
                exact hs u' a' k' hu' ha' hk' (by omega) (by omega) (by omega))
            change u = mul y (mul w (mul u k)) at hsrc
            have hi := inverse_complete y (mul w (mul u k))
            rw [←hsrc] at hi
            have hwa : mul a q = w := hf.symm
            have hquery := hs u a j hu hna hnj (by omega) (by omega) (by omega)
            rw [hgq,haj,hwa,hi] at hquery
            cases hquery
  intro u q k hu hq hk hun hqn hkn
  exact main (ht q) u q k hu hq hk rfl hun hqn hkn

theorem normal_source_of_second_below {x y z : T}
    (hx : NF x) (hy : NF y) (hz : NF z)
    (hs : NormalSecondBelow (max (ht x) (ht z))) : Source12087 x y z := by
  exact normal_source_of_lower_queries hx hy hz (normal_first_below_of_second_below hs) hs

end submission.Austin12087Trace

/- Checked module: TraceSecondReturningQ -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_returning_q_growing_middle_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change ht q < ht k at hqr
  change ht v ≤ ht e at hmid
  change mul y e = u at hf
  have hbounds := normal_second_query_k_dominates hu ha hk hf
  obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt (a:=g) (b:=k) hqr
  change k = c g q z l r at hkc
  have hvg := mul_height_off_return_key (a:=a) hkc (Ne.symm (mul_ne_right u a))
  change ht v = max (ht a) (ht k) + 1 at hvg
  have hov := mul_origin_of_right_height_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
  change origin v = some (a,k) at hov
  have hwu := mul_height_upper a q
  change ht w ≤ max (ht a) (ht q) + 1 at hwu
  have heg := mul_height_growth_of_right_le (a:=w) (b:=v) hmid
  change ht e = max (ht w) (ht v) + 1 at heg
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) hmid
  change origin e = some (w,v) at hoe
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  obtain ⟨t,_,_,_,hwt,hvt,_,_⟩ := nf_return_origin_trace hne hoe hf (by omega)
  have hvw : v ≠ w := by intro heq; have hh := congrArg ht heq; omega
  have hov' := (distinct_outputs_height_origin hvt hwt hvw (by omega)).1
  have hp := Prod.mk.inj (Option.some.inj (hov'.symm.trans hov))
  have hua : u = a := hp.1
  rw [hp.2] at hwt
  have hsrc := normal_source_of_second_below ha hu hk (by
    have hh : max (ht a) (ht k) = ht k := by omega
    rw [hh]
    exact hs)
  change a = mul u (mul q v) at hsrc
  have hvk : mul u k = v := by rw [hua]
  have hinner : mul u (mul q (mul u k)) = a := by rw [hvk]; exact hsrc.symm
  have hfirst : mul (mul y u) k = mul (mul u (mul q (mul u k))) q := by
    rw [hinner]
    exact hwt
  have hsize : sz q < sz k := by rw [hkc]; simp only [sz]; omega
  exact normal_first_larger_k_equation_impossible hu hk hfirst
    (by intro heq; have hh := congrArg ht heq; omega) (by omega)

end submission.Austin12087Trace

/- Checked module: TraceSquareTransport -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem square_column_transport_impossible (w y r : T) :
    mul (mul y w) (mul (mul w w) r) ≠
      mul (mul (mul (mul w w) r) w) r := by
  let a := mul (mul w w) r
  let b := mul a w
  let g := mul b r
  intro hf
  change mul (mul y w) a = g at hf
  have has : ht a < ht r := by
    by_cases hh : ht a < ht r
    · exact hh
    · have hag := mul_height_growth_of_right_le (a:=mul w w) (b:=r) (by change ht r ≤ ht a; omega)
      change ht a = max (ht (mul w w)) (ht r) + 1 at hag
      rw [mul_square] at hag
      simp only [ht] at hag
      have hbg := mul_height_growth_of_left_ge (a:=a) (b:=w) (by omega)
      change ht b = max (ht a) (ht w) + 1 at hbg
      have hgg := mul_height_growth_of_left_ge (a:=b) (b:=r) (by omega)
      change ht g = max (ht b) (ht r) + 1 at hgg
      have ho := mul_origin_of_right_height_le (a:=mul y w) (b:=a) (by rw [hf]; omega)
      rw [hf] at ho
      have ho' := mul_origin_of_right_height_le (a:=b) (b:=r) (by change ht r ≤ ht g; omega)
      change origin g = some (b,r) at ho'
      have hp := (Prod.mk.inj (Option.some.inj (ho.symm.trans ho'))).2
      have hp' := congrArg ht hp
      exact False.elim (by omega)
  have hgr : ht g < ht r := by
    by_cases hh : ht g < ht r
    · exact hh
    · have ho := mul_origin_of_right_height_le (a:=mul y w) (b:=a) (by rw [hf]; omega)
      rw [hf] at ho
      have ho' := mul_origin_of_right_height_le (a:=b) (b:=r) (by change ht r ≤ ht g; omega)
      change origin g = some (b,r) at ho'
      have hp := (Prod.mk.inj (Option.some.inj (ho.symm.trans ho'))).2
      have hp' := congrArg ht hp
      exact False.elim (by omega)
  obtain ⟨z,l,s,hr₁⟩ := mul_return_of_height_lt (a:=mul w w) (b:=r) has
  obtain ⟨z',l',s',hr₂⟩ := mul_return_of_height_lt (a:=b) (b:=r) hgr
  change r = c (mul w w) a z l s at hr₁
  change r = c b g z' l' s' at hr₂
  have hag : a = g := (T.c.inj (hr₁.symm.trans hr₂)).2.1
  exact mul_ne_right (mul y w) a (hf.trans hag.symm)

end submission.Austin12087Trace

/- Checked module: TraceSecondGrowingQHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_growing_q_head {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqg : ht k ≤ ht (mul (mul u a) k)) :
    let g := mul u a
    let q := mul g k
    let w := mul a q
    ∃ r, NF r ∧ q = c a w r g k ∧
      mul (mul a w) r = g ∧ mul w r = k ∧
      ht q = ht k + 1 ∧ ht w < ht k ∧ ht r < ht k := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change ht k ≤ ht q at hqg
  change mul y e = u at hf
  have hb := normal_second_query_k_dominates hu ha hk hf
  have hgu := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hgu
  have hq := mul_height_growth_of_right_le (a:=g) (b:=k) hqg
  change ht q = max (ht g) (ht k) + 1 at hq
  have hoq := mul_origin_of_right_height_le (a:=g) (b:=k) hqg
  change origin q = some (g,k) at hoq
  have hvu := mul_height_upper a k
  change ht v ≤ max (ht a) (ht k) + 1 at hvu
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  have hnw : NF w := nf_mul ha hnq
  have hne : NF e := nf_mul hnw (nf_mul ha hk)
  have hwq : ht w < ht q := by
    by_cases hh : ht w < ht q
    · exact hh
    · have hwg := mul_height_growth_of_right_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
      change ht w = max (ht a) (ht q) + 1 at hwg
      have how := mul_origin_of_right_height_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
      change origin w = some (a,q) at how
      have heg := mul_height_growth_of_left_ge (a:=w) (b:=v) (by omega)
      change ht e = max (ht w) (ht v) + 1 at heg
      have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
      change origin e = some (w,v) at hoe
      obtain ⟨t,_,_,_,hft,hut,_,_⟩ := nf_return_origin_trace hne hoe hf (by omega)
      have hwv : w ≠ v := by intro heq; have hh' := congrArg ht heq; omega
      have how' := (distinct_outputs_height_origin hft hut hwv (by omega)).1
      have hp := Prod.mk.inj (Option.some.inj (how'.symm.trans how))
      rw [hp.2] at hut
      exact False.elim (nf_no_flip hu ha hk hut)
  obtain ⟨r,hcode,hnr,_,hgr,hkr,hrgap,_⟩ :=
    nf_return_origin_trace hnq hoq (show mul a q = w from rfl) hwq
  have hgap := nf_code_height_gap (show NF (c a w r g k) from hcode ▸ hnq)
  change ht a + 2 ≤ ht (c a w r g k) ∧ ht w + 2 ≤ ht (c a w r g k) ∧
    ht r + 2 ≤ ht (c a w r g k) at hgap
  rw [← hcode] at hgap
  change ∃ r, NF r ∧ q = c a w r g k ∧ mul (mul a w) r = g ∧
    mul w r = k ∧ ht q = ht k + 1 ∧ ht w < ht k ∧ ht r < ht k
  exact ⟨r,hnr,hcode,hgr,hkr,by omega,by omega,by omega⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondTwoColumnsReturn -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_two_growing_columns_returning_middle_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqg : ht k ≤ ht (mul (mul u a) k))
    (hvg : ht k ≤ ht (mul a k))
    (hm : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k)) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change ht k ≤ ht v at hvg
  change ht e < ht v at hm
  change mul y e = u at hf
  have hb := normal_second_query_k_dominates hu ha hk hf
  obtain ⟨r,hnr,hqc,hgr,hkr,hq,hw,hr⟩ := normal_second_growing_q_head hu ha hk hf hqg
  change q = c a w r g k at hqc
  change mul (mul a w) r = g at hgr
  change mul w r = k at hkr
  change ht w < ht k at hw
  have hv := mul_height_growth_of_right_le (a:=a) (b:=k) hvg
  change ht v = max (ht a) (ht k) + 1 at hv
  have hov := mul_origin_of_right_height_le (a:=a) (b:=k) hvg
  change origin v = some (a,k) at hov
  have hnv : NF v := nf_mul ha hk
  obtain ⟨t,_,_,_,hat,hkt,htgap,_⟩ :=
    nf_return_origin_trace hnv hov (show mul w v = e from rfl) hm
  have hok := mul_origin_of_right_height_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hok
  have hok' := mul_origin_of_right_height_le (a:=e) (b:=t) (by rw [hkt]; omega)
  rw [hkt] at hok'
  have hp := Prod.mk.inj (Option.some.inj (hok'.symm.trans hok))
  have hew : e = w := hp.1
  have htr : t = r := hp.2
  rw [hew,htr] at hat
  rw [hew] at hf
  have hag : a = mul (mul w w) r := hat.symm
  have hg : mul (mul y w) (mul (mul w w) r) = mul (mul (mul (mul w w) r) w) r := by
    rw [← hag,hf]
    exact hgr.symm
  exact square_column_transport_impossible w y r hg

end submission.Austin12087Trace

/- Checked module: TraceSquareTargetLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem square_target_return_ladder_impossible {u f w j h : T}
    (hfu : f ≠ u)
    (hl : ReturnLadder (mul u w) (mul f w) w (mul u u) w j h)
    (hs : ht (mul u u) < ht j) : False := by
  have hsq : ht (mul u u) = ht u + 1 := by rw [mul_square]; rfl
  by_cases hwu : ht w ≤ ht u
  · have hg := mul_height_growth_of_left_ge (a:=u) (b:=w) hwu
    exact return_ladder_dominant_impossible hl (by omega) (by omega) (by omega)
  · rcases mul_height_growth_or_return u w with hg | ⟨x,z,l,r,hw,_⟩
    · exact return_ladder_dominant_impossible hl (by omega) (by omega) (by omega)
    · have hg := mul_height_off_return_key (a:=f) hw hfu
      exact return_ladder_second_dominant_impossible hl hs (by omega) (by omega) (by omega)

end submission.Austin12087Trace

/- Checked module: TraceSecondTwoColumnsGrow -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_two_growing_columns_growing_middle_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqg : ht k ≤ ht (mul (mul u a) k))
    (hvg : ht k ≤ ht (mul a k))
    (hm : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  let f := mul y u
  change ht k ≤ ht v at hvg
  change ht v ≤ ht e at hm
  change mul y e = u at hf
  have hb := normal_second_query_k_dominates hu ha hk hf
  obtain ⟨r,hnr,hqc,hgr,hkr,hq,hw,hr⟩ := normal_second_growing_q_head hu ha hk hf hqg
  change q = c a w r g k at hqc
  change mul (mul a w) r = g at hgr
  change mul w r = k at hkr
  change ht q = ht k + 1 at hq
  change ht w < ht k at hw
  have hv := mul_height_growth_of_right_le (a:=a) (b:=k) hvg
  change ht v = max (ht a) (ht k) + 1 at hv
  have hov := mul_origin_of_right_height_le (a:=a) (b:=k) hvg
  change origin v = some (a,k) at hov
  have he := mul_height_growth_of_right_le (a:=w) (b:=v) hm
  change ht e = max (ht w) (ht v) + 1 at he
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) hm
  change origin e = some (w,v) at hoe
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  have hne : NF e := nf_mul (nf_mul ha hnq) (nf_mul ha hk)
  obtain ⟨t,_,_,_,hft,hut,_,_⟩ := nf_return_origin_trace hne hoe hf (by omega)
  have hvw : v ≠ w := by intro hh; have hh' := congrArg ht hh; omega
  have hov' := (distinct_outputs_height_origin hut hft hvw (by omega)).1
  have hp := Prod.mk.inj (Option.some.inj (hov'.symm.trans hov))
  have hua : u = a := hp.1
  rw [hp.2] at hft
  change mul f k = w at hft
  have hkey := nf_code_key_height_gap (show NF (c a w r g k) from hqc ▸ hnq)
  rw [← hqc,← hua] at hkey
  have hsu : ht (mul u u) = ht u + 1 := by rw [mul_square]; rfl
  have hok := mul_origin_of_right_height_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hok
  obtain ⟨h,_,hnh,_,hfh,hwh,hgap,_⟩ := nf_return_origin_trace hk hok hft hw
  have hkgrow := mul_height_growth_of_right_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hkgrow
  have hwgap := nf_return_product_height_gap hk hft hw
  have hpw := nf_mul_height_key_gap (a:=f) hk
  rw [hft] at hpw
  have hw2 : ht w + 2 ≤ ht k := by rcases hpw with hpw | hpw <;> omega
  have hrh : ht h < ht r := by omega
  have hor := mul_origin_of_right_height_le (a:=w) (b:=h) (by rw [hwh]; omega)
  rw [hwh] at hor
  have hgr' : mul (mul u w) r = mul u u := by
    change mul (mul a w) r = mul u a at hgr
    rw [hua] at hgr
    rw [hua]
    exact hgr
  have hsbound : ht (mul u u) < ht r := by
    have hpg := nf_mul_height_key_gap (a:=mul u w) hnr
    rw [hgr'] at hpg
    rcases hpg with hpg | hpg <;> omega
  have hl : ReturnLadder (mul u w) (mul f w) w (mul u u) w r h :=
    ⟨hnr,hwh,hor,hgr',hfh⟩
  exact square_target_return_ladder_impossible (mul_ne_right y u) hl hsbound

end submission.Austin12087Trace

/- Checked module: TraceSecondColumnAlternatives -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_two_growing_columns_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqg : ht k ≤ ht (mul (mul u a) k))
    (hvg : ht k ≤ ht (mul a k)) : False := by
  by_cases hm : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))
  · exact normal_second_two_growing_columns_growing_middle_impossible hu ha hk hf hqg hvg hm
  · exact normal_second_two_growing_columns_returning_middle_impossible hu ha hk hf hqg hvg (by omega)

theorem normal_second_column_alternatives {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    (ht (mul (mul u a) k) < ht k ∧ ht k < ht (mul a k)) ∨
    (ht (mul a k) < ht k ∧ ht k < ht (mul (mul u a) k)) := by
  by_cases hqr : ht (mul (mul u a) k) < ht k
  · obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt hqr
    have hv := mul_height_off_return_key (a:=a) hkc (Ne.symm (mul_ne_right u a))
    exact Or.inl ⟨hqr,by omega⟩
  · have hvr : ht (mul a k) < ht k := by
      by_cases hvr : ht (mul a k) < ht k
      · exact hvr
      · exact False.elim (normal_second_two_growing_columns_impossible hu ha hk hf (by omega) (by omega))
    have hq := mul_height_growth_of_right_le (a:=mul u a) (b:=k) (by omega)
    exact Or.inr ⟨hvr,by omega⟩

theorem normal_second_growing_middle_column_order {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hm : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) :
    ht (mul a k) < ht k ∧ ht k < ht (mul (mul u a) k) := by
  rcases normal_second_column_alternatives hu ha hk hf with h | h
  · exact False.elim (normal_second_returning_q_growing_middle_impossible hu ha hk hs hf h.1 hm)
  · exact h

end submission.Austin12087Trace

/- Checked module: TraceSecondReturningColumnTraces -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_returning_v_trace {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k) :
    let g := mul u a
    let q := mul g k
    let v := mul a k
    let w := mul a q
    ∃ r s, NF r ∧ NF s ∧ q = c a w r g k ∧ k = c a v s w r ∧
      mul (mul a w) r = g ∧ mul w r = k ∧
      mul (mul a v) s = w ∧ mul v s = r ∧
      ht w < ht k ∧ ht r < ht k ∧ ht s + 2 ≤ ht k ∧
      ReturnLadder a a g w v q k := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  have hqg : ht k < ht q := by
    rcases normal_second_column_alternatives hu ha hk hf with hh | hh
    · exact False.elim (by omega)
    · exact hh.2
  obtain ⟨r,hnr,hqc,hgr,hkr,hq,hw,hr⟩ := normal_second_growing_q_head hu ha hk hf (by change ht k ≤ ht q; omega)
  change q = c a w r g k at hqc
  change mul w r = k at hkr
  have hok := mul_origin_of_right_height_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hok
  obtain ⟨s,hkc,hns,_,hws,hrs,hsgap,_⟩ :=
    nf_return_origin_trace hk hok (show mul a k = v from rfl) hvr
  have hoq := mul_origin_of_right_height_le (a:=g) (b:=k) (by change ht k ≤ ht q; omega)
  change origin q = some (g,k) at hoq
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  change ∃ r s, NF r ∧ NF s ∧ q = c a w r g k ∧ k = c a v s w r ∧
    mul (mul a w) r = g ∧ mul w r = k ∧ mul (mul a v) s = w ∧
    mul v s = r ∧ ht w < ht k ∧ ht r < ht k ∧ ht s + 2 ≤ ht k ∧
    ReturnLadder a a g w v q k
  exact ⟨r,s,hnr,hns,hqc,hkc,hgr,hkr,hws,hrs,hw,hr,hsgap,
    hnq,rfl,hoq,rfl,rfl⟩

theorem normal_second_returning_q_trace {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    let g := mul u a
    let q := mul g k
    let v := mul a k
    let w := mul a q
    let e := mul w v
    ∃ t z, NF t ∧ NF z ∧ v = c w e t a k ∧ k = c g q z e t ∧
      mul (mul w e) t = a ∧ mul e t = k ∧
      mul (mul g q) z = e ∧ mul q z = t ∧
      ht e < ht k ∧ ht t < ht k ∧ ht z + 2 ≤ ht k ∧
      ReturnLadder g (mul w e) e q a k t := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change ht q < ht k at hqr
  have hb := normal_second_query_k_dominates hu ha hk hf
  have hvg : ht k < ht v := by
    rcases normal_second_column_alternatives hu ha hk hf with hh | hh
    · exact hh.2
    · change ht v < ht k ∧ ht k < ht q at hh
      exact False.elim (by omega)
  have her : ht e < ht v := by
    by_cases hh : ht e < ht v
    · exact hh
    · exact False.elim (normal_second_returning_q_growing_middle_impossible hu ha hk hs hf hqr (by change ht v ≤ ht e; omega))
  have hv := mul_height_growth_of_right_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
  change ht v = max (ht a) (ht k) + 1 at hv
  have hov := mul_origin_of_right_height_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
  change origin v = some (a,k) at hov
  have hnv : NF v := nf_mul ha hk
  obtain ⟨t,hvc,hnt,_,hat,hkt,htgap,_⟩ :=
    nf_return_origin_trace hnv hov (show mul w v = e from rfl) her
  have hgap := nf_mul_height_key_gap (a:=w) hnv
  change ht e = max (ht w) (ht v) + 1 ∨ (ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at hgap
  have hegap : ht e + 2 ≤ ht v := by rcases hgap with hh | hh <;> omega
  have hok := mul_origin_of_right_height_le (a:=e) (b:=t) (by rw [hkt]; omega)
  rw [hkt] at hok
  obtain ⟨z,hkc,hnz,_,hez,htz,hzgap,_⟩ :=
    nf_return_origin_trace hk hok (show mul g k = q from rfl) hqr
  change ∃ t z, NF t ∧ NF z ∧ v = c w e t a k ∧ k = c g q z e t ∧
    mul (mul w e) t = a ∧ mul e t = k ∧ mul (mul g q) z = e ∧
    mul q z = t ∧ ht e < ht k ∧ ht t < ht k ∧ ht z + 2 ≤ ht k ∧
    ReturnLadder g (mul w e) e q a k t
  exact ⟨t,z,hnt,hnz,hvc,hkc,hat,hkt,hez,htz,by omega,by omega,hzgap,
    hk,hkt,hok,rfl,hat⟩

end submission.Austin12087Trace

/- Checked module: TraceOuterGrowthLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem outer_growth_return_ladder_impossible {u a q e k t : T}
    (ha : NF a) (hq : NF q) (heu : ht e < ht u)
    (hl : ReturnLadder (mul u a) (mul (mul a q) e) e q a k t)
    (hqk : ht q < ht k) : False := by
  let g := mul u a
  let w := mul a q
  let A := mul w e
  change ReturnLadder g A e q a k t at hl
  by_cases hd : ht e ≤ ht g ∧ ht a ≤ ht g ∧ ht q ≤ ht g
  · exact return_ladder_dominant_impossible hl hd.1 hd.2.2 hd.2.1
  · have hem : ht e < max (ht a) (ht q) := by
      have hg := nf_mul_height_key_gap (a:=u) ha
      change ht g = max (ht u) (ht a) + 1 ∨ (ht u + 3 ≤ ht a ∧ ht g + 2 ≤ ht a) at hg
      rcases hg with hg | hg <;> omega
    have hwq : ht w < ht q := by
      by_cases hh : ht w < ht q
      · exact hh
      · have hwg := mul_height_growth_of_right_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
        change ht w = max (ht a) (ht q) + 1 at hwg
        have hAg := mul_height_growth_of_left_ge (a:=w) (b:=e) (by omega)
        change ht A = max (ht w) (ht e) + 1 at hAg
        exact False.elim (return_ladder_second_dominant_impossible hl hqk (by omega) (by omega) (by omega))
    have hwgap := nf_mul_height_key_gap (a:=a) hq
    change ht w = max (ht a) (ht q) + 1 ∨ (ht a + 3 ≤ ht q ∧ ht w + 2 ≤ ht q) at hwgap
    have haq : ht a < ht q := by rcases hwgap with hh | hh <;> omega
    have heq : ht e < ht q := by omega
    obtain ⟨z,l,r,hqc⟩ := mul_return_of_height_lt (a:=a) (b:=q) hwq
    have hb := mul_height_off_return_key (a:=g) hqc (mul_ne_right u a)
    have hpg := nf_mul_height_key_gap (a:=g) hl.1
    rw [hl.2.2.2.1] at hpg
    have hq2 : ht q + 2 ≤ ht k := by rcases hpg with hh | hh <;> omega
    have hkg := mul_height_growth_of_right_le (a:=e) (b:=t) (by
      rw [hl.2.1]
      exact Nat.le_of_lt (origin_height hl.2.2.1).2)
    rw [hl.2.1] at hkg
    obtain ⟨r',hl',_⟩ := return_ladder_step hl hqk (by omega)
    exact return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega)

end submission.Austin12087Trace

/- Checked module: TraceSecondReturningQOuter -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_returning_q_outer_growth_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k)
    (houter : ht (mul (mul a (mul (mul u a) k)) (mul a k)) ≤ ht u) : False := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  change mul y e = u at hf
  change ht e ≤ ht u at houter
  have hug := mul_height_growth_of_right_le (a:=y) (b:=e) (by rw [hf]; exact houter)
  rw [hf] at hug
  have hvg : ht k < ht v := by
    rcases normal_second_column_alternatives hu ha hk hf with hh | hh
    · exact hh.2
    · exact False.elim (by omega)
  have her : ht e < ht v := by
    by_cases hh : ht e < ht v
    · exact hh
    · exact False.elim (normal_second_double_growth_impossible hu ha hk hf (by change ht v ≤ ht e; omega) houter)
  have hb := normal_second_query_k_dominates hu ha hk hf
  have hv := mul_height_growth_of_right_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
  change ht v = max (ht a) (ht k) + 1 at hv
  have hov := mul_origin_of_right_height_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
  change origin v = some (a,k) at hov
  have hnv : NF v := nf_mul ha hk
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  obtain ⟨t,_,_,_,hat,hkt,htgap,_⟩ :=
    nf_return_origin_trace hnv hov (show mul w v = e from rfl) her
  have hok := mul_origin_of_right_height_le (a:=e) (b:=t) (by rw [hkt]; omega)
  rw [hkt] at hok
  have hl : ReturnLadder g (mul w e) e q a k t := ⟨hk,hkt,hok,rfl,hat⟩
  exact outer_growth_return_ladder_impossible ha hnq (by omega) hl hqr

theorem normal_second_returning_q_outer_returns {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k)) := by
  by_cases hh : ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k))
  · exact hh
  · exact False.elim (normal_second_returning_q_outer_growth_impossible hu ha hk hf hqr (by omega))

end submission.Austin12087Trace

/- Checked module: TraceFactoredLadderHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem factored_return_ladder_head_order {u a q e k t : T}
    (hq : NF q)
    (hl : ReturnLadder (mul u a) (mul (mul a q) e) e q a k t)
    (hqk : ht q < ht k) :
    max (ht a) (ht q) < ht e ∧ ht (mul u a) < ht e ∧
      ht (mul (mul a q) e) < ht e := by
  let g := mul u a
  let w := mul a q
  let A := mul w e
  change ReturnLadder g A e q a k t at hl
  have hem : max (ht a) (ht q) < ht e := by
    by_cases hh : max (ht a) (ht q) < ht e
    · exact hh
    · have hwq : ht w < ht q := by
        by_cases hwq : ht w < ht q
        · exact hwq
        · have hwg := mul_height_growth_of_right_le (a:=a) (b:=q) (by change ht q ≤ ht w; omega)
          change ht w = max (ht a) (ht q) + 1 at hwg
          have hAg := mul_height_growth_of_left_ge (a:=w) (b:=e) (by omega)
          change ht A = max (ht w) (ht e) + 1 at hAg
          exact False.elim (return_ladder_second_dominant_impossible hl hqk (by omega) (by omega) (by omega))
      have hwgap := nf_mul_height_key_gap (a:=a) hq
      change ht w = max (ht a) (ht q) + 1 ∨ (ht a + 3 ≤ ht q ∧ ht w + 2 ≤ ht q) at hwgap
      have haq : ht a < ht q := by rcases hwgap with hh | hh <;> omega
      have heq : ht e ≤ ht q := by omega
      obtain ⟨z,l,r,hqc⟩ := mul_return_of_height_lt (a:=a) (b:=q) hwq
      have hb := mul_height_off_return_key (a:=g) hqc (mul_ne_right u a)
      have hpg := nf_mul_height_key_gap (a:=g) hl.1
      rw [hl.2.2.2.1] at hpg
      have hq2 : ht q + 2 ≤ ht k := by rcases hpg with hh | hh <;> omega
      have hkg := mul_height_growth_of_right_le (a:=e) (b:=t) (by
        rw [hl.2.1]
        exact Nat.le_of_lt (origin_height hl.2.2.1).2)
      rw [hl.2.1] at hkg
      obtain ⟨r',hl',_⟩ := return_ladder_step hl hqk (by omega)
      exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))
  have hge : ht g < ht e := by
    by_cases hh : ht g < ht e
    · exact hh
    · exact False.elim (return_ladder_dominant_impossible hl (by omega) (by omega) (by omega))
  have hAe : ht A < ht e := by
    by_cases hh : ht A < ht e
    · exact hh
    · exact False.elim (return_ladder_second_dominant_impossible hl hqk (by omega) (by omega) (by omega))
  exact ⟨hem,hge,hAe⟩

theorem factored_return_ladder_tail_stops {u a q e k t z l r : T}
    (hl : ReturnLadder (mul u a) u e q a k t)
    (hec : e = c (mul a q) u z l r)
    (hae : ht a < ht e) (hqe : ht q < ht e) (hqk : ht q < ht k) :
    ht t ≤ ht e := by
  let g := mul u a
  let w := mul a q
  let b := mul g q
  change ReturnLadder g u e q a k t at hl
  have hte : ht t ≤ ht e := by
    by_cases hh : ht t ≤ ht e
    · exact hh
    · obtain ⟨s,hl₁,_⟩ := return_ladder_step hl hqk (by omega)
      have htg := mul_height_growth_of_right_le (a:=q) (b:=s) (by
        rw [hl₁.2.1]
        exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
      rw [hl₁.2.1] at htg
      have hns := (nf_origin hl₁.1 hl₁.2.2.1).2
      have hpg := nf_mul_height_key_gap (a:=b) hns
      rw [hl₁.2.2.2.2] at hpg
      have he2 : ht e + 2 ≤ ht s := by rcases hpg with hp | hp <;> omega
      obtain ⟨s',hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      have hsg := mul_height_growth_of_right_le (a:=a) (b:=s') (by
        rw [hl₂.2.1]
        exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at hsg
      obtain ⟨s'',hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      change ReturnLadder g (mul b e) e q a s' s'' at hl₃
      have hbw : b ≠ w := by
        intro heq
        exact mul_ne_right u a (right_injective _ _ q heq)
      have hbg := mul_height_off_return_key (a:=b) hec hbw
      exact False.elim (return_ladder_second_dominant_impossible hl₃ (by omega) (by omega) (by omega) (by omega))
  exact hte

end submission.Austin12087Trace

/- Checked module: TraceSecondReturningQHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_returning_q_head {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    let g := mul u a
    let q := mul g k
    let v := mul a k
    let w := mul a q
    let e := mul w v
    ∃ t z h, NF t ∧ NF z ∧ NF h ∧
      v = c w e t a k ∧ k = c g q z e t ∧ e = c w u h (mul g q) z ∧
      w = y ∧ mul u t = a ∧ mul (mul w u) h = mul g q ∧ mul u h = z ∧
      ht t ≤ ht e ∧ max (ht a) (ht q) < ht e ∧ ht g < ht e ∧
      ht e < ht k ∧ ReturnLadder g u e q a k t := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  obtain ⟨t,z,hnt,hnz,hvc,hkc,hat,hkt,hez,htz,hek,htk,hzgap,hl⟩ :=
    normal_second_returning_q_trace hu ha hk hs hf hqr
  change v = c w e t a k at hvc
  change k = c g q z e t at hkc
  change mul (mul w e) t = a at hat
  change mul (mul g q) z = e at hez
  change mul q z = t at htz
  change ht e < ht k at hek
  change ReturnLadder g (mul w e) e q a k t at hl
  have hnq : NF q := nf_mul (nf_mul hu ha) hk
  have hne : NF e := nf_mul (nf_mul ha hnq) (nf_mul ha hk)
  have hhead := factored_return_ladder_head_order hnq hl hqr
  change max (ht a) (ht q) < ht e ∧ ht g < ht e ∧ ht (mul w e) < ht e at hhead
  have hou := normal_second_returning_q_outer_returns hu ha hk hf hqr
  change ht u < ht e at hou
  change mul y e = u at hf
  obtain ⟨j,l,r,hec₁⟩ := mul_return_of_height_lt hhead.2.2
  obtain ⟨j',l',r',hec₂⟩ := mul_return_of_height_lt (a:=y) (b:=e) (by rw [hf]; exact hou)
  rw [hf] at hec₂
  have hp := T.c.inj (hec₁.symm.trans hec₂)
  have hwy : w = y := hp.1
  have hwu : mul w e = u := hp.2.1
  rw [hwu] at hat hl hec₁
  have hte := factored_return_ladder_tail_stops hl hec₁ (by omega) (by omega) hqr
  have het : e ≠ t := by
    intro heq
    exact mul_ne_right g q (right_injective _ _ z (hez.trans (heq.trans htz.symm)))
  have hoe := (distinct_outputs_height_origin hez htz het (by omega)).1
  obtain ⟨h,hec,hnh,_,hbh,hzh,_,_⟩ := nf_return_origin_trace hne hoe hwu hou
  change ∃ t z h, NF t ∧ NF z ∧ NF h ∧ v = c w e t a k ∧
    k = c g q z e t ∧ e = c w u h (mul g q) z ∧ w = y ∧ mul u t = a ∧
    mul (mul w u) h = mul g q ∧ mul u h = z ∧ ht t ≤ ht e ∧
    max (ht a) (ht q) < ht e ∧ ht g < ht e ∧ ht e < ht k ∧
    ReturnLadder g u e q a k t
  exact ⟨t,z,h,hnt,hnz,hnh,hvc,hkc,hec,hwy,hat,hbh,hzh,hte,hhead.1,hhead.2.1,hek,hl⟩

end submission.Austin12087Trace

/- Checked module: TraceFixedSquareSuccessor -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_small_left_alternative_impossible {a v : T}
    (ha : NF a) (hv : NF v)
    (heq : mul a (mul a v) = mul (mul a a) v)
    (hout : ht (mul (mul a a) v) ≤ ht a) : False := by
  let A := mul a a
  let r := mul a v
  let x := mul A v
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  change ht x ≤ ht a at hout
  have hgap := nf_mul_height_key_gap (a:=A) hv
  change ht x = max (ht A) (ht v) + 1 ∨ (ht A + 3 ≤ ht v ∧ ht x + 2 ≤ ht v) at hgap
  have hxv : ht x < ht v := by rcases hgap with hp | hp <;> omega
  obtain ⟨z,l,t,hvc⟩ := mul_return_of_height_lt (a:=A) (b:=v) hxv
  have hag : a ≠ A := by intro he; have heh := congrArg ht he; omega
  have hrg := mul_height_off_return_key (a:=a) hvc hag
  change ht r = max (ht a) (ht v) + 1 at hrg
  have hor := mul_origin_of_right_height_le (a:=a) (b:=v) (by change ht v ≤ ht r; omega)
  change origin r = some (a,v) at hor
  have hl : ReturnLadder a A a x x r v := ⟨nf_mul ha hv,rfl,hor,heq,rfl⟩
  exact return_ladder_second_dominant_impossible hl (by omega) (by omega) (by omega) (by omega)

theorem normal_fixed_square_successor_impossible {u k : T}
    (hu : NF u) (hk : NF k) (hfixed : mul u k = u) :
    mul u (mul (mul u u) k) ≠ u := by
  let A := mul u u
  let q := mul A k
  intro hqfixed
  change mul u q = u at hqfixed
  have hA : ht A = ht u + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have huk : ht u < ht k := by
    have hi := inverse_height_strict (inverse_complete u k)
    rw [hfixed] at hi
    omega
  obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt (a:=u) (b:=k) (by rw [hfixed]; exact huk)
  rw [hfixed] at hkc
  have hAu : A ≠ u := by intro he; have heh := congrArg ht he; omega
  have hqg := mul_height_off_return_key (a:=A) hkc hAu
  change ht q = max (ht A) (ht k) + 1 at hqg
  have hoq := mul_origin_of_right_height_le (a:=A) (b:=k) (by change ht k ≤ ht q; omega)
  change origin q = some (A,k) at hoq
  have hnA : NF A := nf_mul hu hu
  have hnq : NF q := nf_mul hnA hk
  obtain ⟨s,_,hns,_,hAs,hks,hsgap,_⟩ := nf_return_origin_trace hnq hoq hqfixed (by omega)
  change mul A s = A at hAs
  have hAsize : ht A < ht s := by
    have hi := inverse_height_strict (inverse_complete A s)
    rw [hAs] at hi
    omega
  have hksize : ht s < ht k := by omega
  have hkg := mul_height_growth_of_right_le (a:=u) (b:=s) (by rw [hks]; omega)
  rw [hks] at hkg
  have hok := mul_origin_of_right_height_le (a:=u) (b:=s) (by rw [hks]; omega)
  rw [hks] at hok
  obtain ⟨t,_,hnt,_,hut,hst,htgap,_⟩ := nf_return_origin_trace hk hok hfixed huk
  change mul A t = u at hut
  have hos := mul_origin_of_right_height_le (a:=u) (b:=t) (by rw [hst]; omega)
  rw [hst] at hos
  obtain ⟨v,_,hnv,_,huv,htv,_,_⟩ := nf_return_origin_trace hns hos hAs hAsize
  have halt : mul A (mul A v) = mul (mul A A) v := by rw [htv,hut,huv]
  exact normal_small_left_alternative_impossible hnA hnv halt (by rw [huv]; omega)

end submission.Austin12087Trace

/- Checked module: TraceFixedRotation -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_fixed_rotation_impossible {u q : T}
    (hu : NF u) (hq : NF q) (hfixed : mul u q = u) :
    mul u (mul q u) ≠ u := by
  intro hrotate
  have huq : ht u < ht q := by
    have hi := inverse_height_strict (inverse_complete u q)
    rw [hfixed] at hi
    omega
  have htg := mul_height_growth_of_left_ge (a:=q) (b:=u) (by omega)
  have hot := mul_origin_of_right_height_le (a:=q) (b:=u) (by omega)
  obtain ⟨s,_,hns,_,hqs,hus,_,_⟩ := nf_return_origin_trace (nf_mul hq hu) hot hrotate (by omega)
  have hbad := normal_fixed_square_successor_impossible hu hns hus
  rw [hqs] at hbad
  exact hbad hfixed

end submission.Austin12087Trace

/- Checked module: TraceFixedCodeHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_fixed_code_head_order {u q h z : T}
    (hu : NF u) (hq : NF q)
    (hn : NF (c (mul u q) u h (mul (mul u u) q) z))
    (hsmall : ht q < ht (c (mul u q) u h (mul (mul u u) q) z))
    (hfixed : mul u (mul q z) = u) :
    ht (mul (mul u u) q) < ht z := by
  let A := mul u u
  let b := mul A q
  let w := mul u q
  let e := c w u h b z
  change NF e at hn
  change ht q < ht e at hsmall
  change ht b < ht z
  by_cases hh : ht b < ht z
  · exact hh
  · have hnc : NF (c w u h b z) := hn
    have hc := nf_code_actual hnc
    have hgap := nf_code_height_gap hnc
    change ht w + 2 ≤ ht e ∧ ht u + 2 ≤ ht e ∧ ht h + 2 ≤ ht e at hgap
    have heact : mul b z = e := hc.2.2.2.2.2.1
    have heo : origin e = some (b,z) := rfl
    have heg := mul_height_growth_of_right_le (a:=b) (b:=z) (by
      rw [heact]
      exact Nat.le_of_lt (origin_height heo).2)
    rw [heact] at heg
    have hbg := nf_mul_height_key_gap (a:=A) hq
    change ht b = max (ht A) (ht q) + 1 ∨ (ht A + 3 ≤ ht q ∧ ht b + 2 ≤ ht q) at hbg
    have hqb : ht q < ht b := by rcases hbg with hp | hp <;> omega
    have hob := mul_origin_of_right_height_le (a:=A) (b:=q) (by change ht q ≤ ht b; omega)
    change origin b = some (A,q) at hob
    have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
    have hzh : mul u h = z := hc.2.2.2.2.2.2.2
    have hob' := mul_origin_of_right_height_le (a:=mul w u) (b:=h) (by rw [hbh]; omega)
    rw [hbh] at hob'
    have hp := Prod.mk.inj (Option.some.inj (hob'.symm.trans hob))
    have hwu : w = u := right_injective _ _ u hp.1
    have hright : mul u q = u := hwu
    rw [hp.2,hright] at hzh
    rw [← hzh] at hfixed
    exact False.elim (normal_fixed_rotation_impossible hu hq hright hfixed)

end submission.Austin12087Trace

/- Checked module: TraceSecondEqualInputHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_equal_input_returning_q_head {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u)
    (hqr : ht (mul (mul u u) k) < ht k) :
    let q := mul (mul u u) k
    let w := mul u q
    let e := mul w (mul u k)
    ∃ z h, NF z ∧ NF h ∧ e = c w u h (mul (mul u u) q) z ∧
      ht (mul (mul u u) q) < ht z ∧ ht z < ht e ∧ ht e < ht k := by
  let q := mul (mul u u) k
  let w := mul u q
  let e := mul w (mul u k)
  obtain ⟨t,z,h,_,hnz,hnh,_,hkc,hec,_,hat,_,_,_,hhead,_,hek,_⟩ :=
    normal_second_returning_q_head hu hu hk hs hf hqr
  change k = c (mul u u) q z e t at hkc
  change e = c w u h (mul (mul u u) q) z at hec
  change mul u t = u at hat
  change max (ht u) (ht q) < ht e at hhead
  change ht e < ht k at hek
  have hkc' : NF (c (mul u u) q z e t) := hkc ▸ hk
  have htz : mul q z = t := (nf_code_actual hkc').2.2.2.2.2.2.2
  have hnq : NF q := nf_mul (nf_mul hu hu) hk
  have hne : NF e := nf_mul (nf_mul hu hnq) (nf_mul hu hk)
  have hec' : NF (c w u h (mul (mul u u) q) z) := hec ▸ hne
  have hbz := normal_fixed_code_head_order hu hnq hec'
    (by rw [← hec]; change ht q < ht e; omega)
    (by rw [htz]; exact hat)
  have heo : origin e = some (mul (mul u u) q,z) := by rw [hec]; rfl
  change ∃ z h, NF z ∧ NF h ∧ e = c w u h (mul (mul u u) q) z ∧
    ht (mul (mul u u) q) < ht z ∧ ht z < ht e ∧ ht e < ht k
  exact ⟨z,h,hnz,hnh,hec,hbz,(origin_height heo).2,hek⟩

end submission.Austin12087Trace

/- Checked module: TraceEqualCodeGeometry -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_equal_code_geometry {u q h z : T}
    (hq : NF q)
    (hn : NF (c (mul u q) u h (mul (mul u u) q) z))
    (hsmall : ht q < ht (c (mul u q) u h (mul (mul u u) q) z))
    (hbz : ht (mul (mul u u) q) < ht z) :
    ht u + 3 ≤ ht z ∧ ht (mul u q) + 2 ≤ ht z ∧
      ht h + 1 = ht z ∧ ht (mul (mul u u) q) + 2 ≤ ht h ∧
      origin z = some (u,h) := by
  let b := mul (mul u u) q
  let w := mul u q
  let e := c w u h b z
  change NF e at hn
  change ht q < ht e at hsmall
  change ht b < ht z at hbz
  have hc := nf_code_actual hn
  have hgap := nf_code_height_gap hn
  have hkey := nf_code_key_height_gap hn
  change ht w + 2 ≤ ht e ∧ ht u + 2 ≤ ht e ∧ ht h + 2 ≤ ht e at hgap
  change ht w + 3 ≤ ht e at hkey
  have heact : mul b z = e := hc.2.2.2.2.2.1
  have heo : origin e = some (b,z) := rfl
  have heg := mul_height_growth_of_right_le (a:=b) (b:=z) (by
    rw [heact]
    exact Nat.le_of_lt (origin_height heo).2)
  rw [heact] at heg
  have hez : ht e = ht z + 1 := by omega
  have hw := nf_mul_height_key_gap (a:=u) hq
  change ht w = max (ht u) (ht q) + 1 ∨ (ht u + 3 ≤ ht q ∧ ht w + 2 ≤ ht q) at hw
  have hu3 : ht u + 3 ≤ ht z := by rcases hw with hw | hw <;> omega
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  have hzg := mul_height_growth_of_right_le (a:=u) (b:=h) (by rw [hzh]; omega)
  rw [hzh] at hzg
  have hoz := mul_origin_of_right_height_le (a:=u) (b:=h) (by rw [hzh]; omega)
  rw [hzh] at hoz
  have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
  have hb := nf_mul_height_key_gap (a:=mul w u) hc.2.2.1
  rw [hbh] at hb
  have hb2 : ht b + 2 ≤ ht h := by rcases hb with hb | hb <;> omega
  exact ⟨hu3,by change ht w + 2 ≤ ht z; omega,by omega,hb2,hoz⟩

end submission.Austin12087Trace

/- Checked module: TraceEqualCodeTail -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_equal_code_tail_returns {u q h z : T}
    (hu : NF u) (hq : NF q)
    (hn : NF (c (mul u q) u h (mul (mul u u) q) z))
    (hsmall : ht q < ht (c (mul u q) u h (mul (mul u u) q) z))
    (hbz : ht (mul (mul u u) q) < ht z)
    (hfixed : mul u (mul q z) = u) : ht (mul q z) < ht z := by
  let A := mul u u
  let b := mul A q
  let w := mul u q
  let e := c w u h b z
  let t := mul q z
  change NF e at hn
  change mul u t = u at hfixed
  have hA : ht A = ht u + 1 := by dsimp only [A]; rw [mul_square]; rfl
  obtain ⟨hu3,hw2,hhz,hb2,hoz⟩ := normal_equal_code_geometry hq hn hsmall hbz
  change ht w + 2 ≤ ht z at hw2
  change ht b + 2 ≤ ht h at hb2
  have hc := nf_code_actual hn
  have hnh : NF h := hc.2.2.1
  have hnz : NF z := hc.2.2.2.2.1
  have hnt : NF t := nf_mul hq hnz
  have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  change ht t < ht z
  by_cases htz : ht t < ht z
  · exact htz
  · have htg := mul_height_growth_of_right_le (a:=q) (b:=z) (by change ht z ≤ ht t; omega)
    change ht t = max (ht q) (ht z) + 1 at htg
    have heact : mul b z = e := hc.2.2.2.2.2.1
    have heo : origin e = some (b,z) := rfl
    have heg := mul_height_growth_of_right_le (a:=b) (b:=z) (by
      rw [heact]
      exact Nat.le_of_lt (origin_height heo).2)
    rw [heact] at heg
    change ht q < ht e at hsmall
    change ht b < ht z at hbz
    have hot := mul_origin_of_right_height_le (a:=q) (b:=z) (by change ht z ≤ ht t; omega)
    change origin t = some (q,z) at hot
    obtain ⟨s,_,_,_,hqs,hzs,hsgap,_⟩ := nf_return_origin_trace hnt hot hfixed (by omega)
    change mul A s = q at hqs
    have hoz' := mul_origin_of_right_height_le (a:=u) (b:=s) (by rw [hzs]; omega)
    rw [hzs] at hoz'
    have hsh : s = h := (Prod.mk.inj (Option.some.inj (hoz'.symm.trans hoz))).2
    rw [hsh] at hqs
    have hAD : A ≠ mul w u := by
      intro heq
      have hqb : q = b := hqs.symm.trans (by rw [heq]; exact hbh)
      exact mul_ne_right A q hqb.symm
    obtain ⟨r,l,j,hhc⟩ := mul_return_of_height_lt (a:=mul w u) (b:=h) (by rw [hbh]; omega)
    have hqg := mul_height_off_return_key (a:=A) hhc hAD
    rw [hqs] at hqg
    have hqz : ht q = ht z := by omega
    obtain ⟨r',l',j',hqc⟩ := mul_return_of_height_lt (a:=u) (b:=q) (by change ht w < ht q; omega)
    have hAu : A ≠ u := by intro heq; have heh := congrArg ht heq; omega
    have hbg := mul_height_off_return_key (a:=A) hqc hAu
    change ht b = max (ht A) (ht q) + 1 at hbg
    exact False.elim (by omega)

theorem normal_equal_code_key_repeats {u q h z : T}
    (hu : NF u) (hq : NF q)
    (hn : NF (c (mul u q) u h (mul (mul u u) q) z))
    (hsmall : ht q < ht (c (mul u q) u h (mul (mul u u) q) z))
    (hbz : ht (mul (mul u u) q) < ht z)
    (hfixed : mul u (mul q z) = u) : q = u := by
  let A := mul u u
  let b := mul A q
  let w := mul u q
  let e := c w u h b z
  let t := mul q z
  change NF e at hn
  change mul u t = u at hfixed
  have htz := normal_equal_code_tail_returns hu hq hn hsmall hbz hfixed
  change ht t < ht z at htz
  obtain ⟨hu3,_,hhz,hb2,hoz⟩ := normal_equal_code_geometry hq hn hsmall hbz
  change ht b + 2 ≤ ht h at hb2
  have hc := nf_code_actual hn
  have hnz : NF z := hc.2.2.2.2.1
  have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  by_cases hqu : q = u
  · exact hqu
  · have hut : ht u < ht t := by
      have hi := inverse_height_strict (inverse_complete u t)
      rw [hfixed] at hi
      omega
    obtain ⟨s,l,r,htc⟩ := mul_return_of_height_lt (a:=u) (b:=t) (by rw [hfixed]; exact hut)
    have hBg := mul_height_off_return_key (a:=q) htc hqu
    have hA : ht A = ht u + 1 := by dsimp only [A]; rw [mul_square]; rfl
    have hbu := mul_height_upper A q
    change ht b ≤ max (ht A) (ht q) + 1 at hbu
    have hl : ReturnLadder q (mul w u) u t b z h := ⟨hnz,hzh,hoz,rfl,hbh⟩
    obtain ⟨s',hl',_⟩ := return_ladder_step hl htz (by omega)
    exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))

end submission.Austin12087Trace

/- Checked module: TraceSecondEqualKey -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_equal_input_q_key {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u)
    (hqr : ht (mul (mul u u) k) < ht k) :
    mul (mul u u) k = u ∧ y = mul u u := by
  let q := mul (mul u u) k
  let w := mul u q
  let e := mul w (mul u k)
  obtain ⟨t,z,h,_,_,_,_,hkc,hec,hwy,hat,_,_,_,hhead,_,_,_⟩ :=
    normal_second_returning_q_head hu hu hk hs hf hqr
  change k = c (mul u u) q z e t at hkc
  change e = c w u h (mul (mul u u) q) z at hec
  change w = y at hwy
  change mul u t = u at hat
  change max (ht u) (ht q) < ht e at hhead
  have hkc' : NF (c (mul u u) q z e t) := hkc ▸ hk
  have htz : mul q z = t := (nf_code_actual hkc').2.2.2.2.2.2.2
  have hnq : NF q := nf_mul (nf_mul hu hu) hk
  have hne : NF e := nf_mul (nf_mul hu hnq) (nf_mul hu hk)
  have hec' : NF (c w u h (mul (mul u u) q) z) := hec ▸ hne
  have hsmall : ht q < ht (c w u h (mul (mul u u) q) z) := by rw [← hec]; omega
  have hfixed : mul u (mul q z) = u := by rw [htz]; exact hat
  have hbz := normal_fixed_code_head_order hu hnq hec' hsmall hfixed
  have hqu := normal_equal_code_key_repeats hu hnq hec' hsmall hbz hfixed
  refine ⟨hqu,?_⟩
  change mul u q = y at hwy
  rw [hqu] at hwy
  exact hwy.symm

theorem normal_second_equal_input_q_core {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u)
    (hqr : ht (mul (mul u u) k) < ht k) :
    mul (mul u u) k = u ∧
      mul (mul u u) (mul (mul u u) (mul u k)) = u := by
  obtain ⟨hqu,hy⟩ := normal_second_equal_input_q_key hu hk hs hf hqr
  rw [hqu,hy] at hf
  exact ⟨hqu,hf⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondFixedPairReduction -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_equal_input_q_fixed_pair {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u)
    (hqr : ht (mul (mul u u) k) < ht k) :
    let b := mul (mul u u) u
    ∃ s, NF s ∧ ht s < ht k ∧
      mul u (mul b s) = u ∧ mul u (mul (mul b b) s) = u := by
  let q := mul (mul u u) k
  let w := mul u q
  let b := mul (mul u u) q
  let e := mul w (mul u k)
  obtain ⟨t,z,h,_,hnz,hnh,_,hkc,hec,_,hat,hbh,hzh,_,hhead,_,hek,_⟩ :=
    normal_second_returning_q_head hu hu hk hs hf hqr
  change k = c (mul u u) q z e t at hkc
  change e = c w u h b z at hec
  change mul u t = u at hat
  change mul (mul w u) h = b at hbh
  change mul u h = z at hzh
  change max (ht u) (ht q) < ht e at hhead
  change ht e < ht k at hek
  have hkc' : NF (c (mul u u) q z e t) := hkc ▸ hk
  have htz : mul q z = t := (nf_code_actual hkc').2.2.2.2.2.2.2
  have hnq : NF q := nf_mul (nf_mul hu hu) hk
  have hne : NF e := nf_mul (nf_mul hu hnq) (nf_mul hu hk)
  have hec' : NF (c w u h b z) := hec ▸ hne
  have hsmall : ht q < ht (c w u h b z) := by rw [← hec]; omega
  have hfixed : mul u (mul q z) = u := by rw [htz]; exact hat
  have hbz := normal_fixed_code_head_order hu hnq hec' hsmall hfixed
  have hqu := normal_equal_code_key_repeats hu hnq hec' hsmall hbz hfixed
  have htr := normal_equal_code_tail_returns hu hnq hec' hsmall hbz hfixed
  rw [htz] at htr
  obtain ⟨hu3,_,hhz,hb2,hoz⟩ := normal_equal_code_geometry hnq hec' hsmall hbz
  change ht b + 2 ≤ ht h at hb2
  have hww : w = mul u u := by change mul u q = mul u u; rw [hqu]
  have hb : b = mul (mul u u) u := by change mul (mul u u) q = mul (mul u u) u; rw [hqu]
  have htuz : mul u z = t := by rw [← hqu]; exact htz
  obtain ⟨r,_,_,_,hur,hhr,hrgap,_⟩ := nf_return_origin_trace hnz hoz htuz htr
  rw [hat] at hur
  have hoh := mul_origin_of_right_height_le (a:=t) (b:=r) (by rw [hhr]; omega)
  rw [hhr] at hoh
  have hbfixed : mul b h = b := by rw [hww,← hb] at hbh; exact hbh
  obtain ⟨s,_,hns,_,hts,hrs,hsgap,_⟩ := nf_return_origin_trace hnh hoh hbfixed (by omega)
  have hhsmall : ht h < ht e := by
    have hh := nf_code_height_gap hec'
    rw [← hec] at hh
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_succ 1)) hh.2.2
  refine ⟨s,hns,by omega,?_,?_⟩
  · rw [← hb,hrs]
    exact hur
  · rw [← hb,hts]
    exact hat

end submission.Austin12087Trace

/- Checked module: TraceFixedSquarePairGrowth -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_fixed_square_pair_both_growth_impossible {u b k : T}
    (hu : NF u) (hb : NF b) (hk : NF k)
    (hr : mul u (mul b k) = u)
    (hfixT : mul u (mul (mul b b) k) = u)
    (hrg : ht k ≤ ht (mul b k))
    (htg : ht k ≤ ht (mul (mul b b) k)) : False := by
  let A := mul u u
  let B := mul b b
  let r := mul b k
  let t := mul B k
  have hA : ht A = ht u + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have hB : ht B = ht b + 1 := by dsimp only [B]; rw [mul_square]; rfl
  change mul u r = u at hr
  change mul u t = u at hfixT
  have hur : ht u < ht r := by
    have hi := inverse_height_strict (inverse_complete u r)
    rw [hr] at hi
    omega
  have hut : ht u < ht t := by
    have hi := inverse_height_strict (inverse_complete u t)
    rw [hfixT] at hi
    omega
  have hrg' := mul_height_growth_of_right_le (a:=b) (b:=k) hrg
  change ht r = max (ht b) (ht k) + 1 at hrg'
  have htg' := mul_height_growth_of_right_le (a:=B) (b:=k) htg
  change ht t = max (ht B) (ht k) + 1 at htg'
  have hor := mul_origin_of_right_height_le (a:=b) (b:=k) hrg
  change origin r = some (b,k) at hor
  have hot := mul_origin_of_right_height_le (a:=B) (b:=k) htg
  change origin t = some (B,k) at hot
  obtain ⟨j,_,_,_,hbj,hkj,hjgap,_⟩ := nf_return_origin_trace (nf_mul hb hk) hor hr hur
  obtain ⟨h,_,_,_,hBh,hkh,hhgap,_⟩ := nf_return_origin_trace (nf_mul (nf_mul hb hb) hk) hot hfixT hut
  change ht j + 2 ≤ ht r at hjgap
  change ht h + 2 ≤ ht t at hhgap
  change mul A j = b at hbj
  change mul A h = B at hBh
  by_cases hkb : ht k ≤ ht b
  · have hoB := mul_origin_of_right_height_le (a:=A) (b:=h) (by rw [hBh]; omega)
    rw [hBh] at hoB
    have hoB' : origin B = some (b,b) := by dsimp only [B]; rw [mul_square]; rfl
    have hp := Prod.mk.inj (Option.some.inj (hoB.symm.trans hoB'))
    have hAb : A = b := hp.1
    rw [hp.2,← hAb] at hkh
    rcases mul_height_growth_or_return u A with hg | ⟨x,z,l,r',hc,_⟩
    · rw [hkh] at hg
      have hh := congrArg ht hAb
      omega
    · change mul u u = c u x z l r' at hc
      rw [mul_square] at hc
      cases hc
  · have hok₁ := mul_origin_of_right_height_le (a:=u) (b:=h) (by rw [hkh]; omega)
    rw [hkh] at hok₁
    have hok₂ := mul_origin_of_right_height_le (a:=u) (b:=j) (by rw [hkj]; omega)
    rw [hkj] at hok₂
    have hhj := (Prod.mk.inj (Option.some.inj (hok₁.symm.trans hok₂))).2
    rw [hhj,hbj] at hBh
    have hh := congrArg ht hBh
    omega

theorem normal_fixed_square_pair_alternatives {u b k : T}
    (hu : NF u) (hb : NF b) (hk : NF k)
    (hr : mul u (mul b k) = u)
    (hfixT : mul u (mul (mul b b) k) = u) :
    (ht (mul b k) < ht k ∧ ht k < ht (mul (mul b b) k)) ∨
    (ht (mul (mul b b) k) < ht k ∧ ht k < ht (mul b k)) := by
  have hB : ht (mul b b) = ht b + 1 := by rw [mul_square]; rfl
  by_cases hh : ht (mul b k) < ht k
  · obtain ⟨z,l,r,hkc⟩ := mul_return_of_height_lt hh
    have hneq : mul b b ≠ b := by intro heq; have heh := congrArg ht heq; omega
    have hg := mul_height_off_return_key (a:=mul b b) hkc hneq
    exact Or.inl ⟨hh,by omega⟩
  · have hret : ht (mul (mul b b) k) < ht k := by
      by_cases hret : ht (mul (mul b b) k) < ht k
      · exact hret
      · exact False.elim (normal_fixed_square_pair_both_growth_impossible hu hb hk hr hfixT (by omega) (by omega))
    have hg := mul_height_growth_of_right_le (a:=b) (b:=k) (by omega)
    exact Or.inr ⟨hret,by omega⟩

end submission.Austin12087Trace

/- Checked module: TraceSmallFixedPair -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_fixed_pair_small_growing_key_impossible {u a b k : T}
    (hu : NF u) (ha : NF a) (hb : NF b) (hk : NF k)
    (hua : ht u < ht a) (hbu : ht b ≤ ht u + 3)
    (hr : mul u (mul a k) = u) (hfixT : mul u (mul b k) = u)
    (hret : ht (mul a k) < ht k) (hgrow : ht k ≤ ht (mul b k)) : False := by
  let A := mul u u
  let r := mul a k
  let t := mul b k
  change mul u r = u at hr
  change mul u t = u at hfixT
  change ht r < ht k at hret
  have hnr : NF r := nf_mul ha hk
  have hnt : NF t := nf_mul hb hk
  have hkgap := nf_mul_height_key_gap (a:=a) hk
  change ht r = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht r + 2 ≤ ht k) at hkgap
  have ha3 : ht a + 3 ≤ ht k := by rcases hkgap with hh | hh <;> omega
  have htg := mul_height_growth_of_right_le (a:=b) (b:=k) hgrow
  change ht t = max (ht b) (ht k) + 1 at htg
  have hot := mul_origin_of_right_height_le (a:=b) (b:=k) hgrow
  change origin t = some (b,k) at hot
  have hut : ht u < ht t := by
    have hi := inverse_height_strict (inverse_complete u t)
    rw [hfixT] at hi
    omega
  obtain ⟨h,_,hnh,_,hbh,hkh,hhgap,_⟩ := nf_return_origin_trace hnt hot hfixT hut
  change mul A h = b at hbh
  change ht h + 2 ≤ ht t at hhgap
  have hkg := mul_height_growth_of_right_le (a:=u) (b:=h) (by rw [hkh]; omega)
  rw [hkh] at hkg
  have hok := mul_origin_of_right_height_le (a:=u) (b:=h) (by rw [hkh]; omega)
  rw [hkh] at hok
  obtain ⟨j,_,_,_,huj,hhj,hjgap,_⟩ :=
    nf_return_origin_trace hk hok (show mul a k = r from rfl) hret
  have hoh := mul_origin_of_right_height_le (a:=r) (b:=j) (by rw [hhj]; omega)
  rw [hhj] at hoh
  have hbr := nf_mul_height_key_gap (a:=A) hnh
  rw [hbh] at hbr
  have hbhsmall : ht b < ht h := by rcases hbr with hh | hh <;> omega
  have hufixed := nf_mul_height_key_gap (a:=u) hnr
  rw [hr] at hufixed
  have hur3 : ht u + 3 ≤ ht r := by rcases hufixed with hh | hh <;> omega
  obtain ⟨s,l,z,hrc⟩ := mul_return_of_height_lt (a:=u) (b:=r) (by rw [hr]; omega)
  have hau : a ≠ u := by intro heq; have hh := congrArg ht heq; omega
  have harg := mul_height_off_return_key (a:=a) hrc hau
  have hl : ReturnLadder A (mul a r) r b u h j := ⟨hnh,hhj,hoh,hbh,huj⟩
  exact return_ladder_second_dominant_impossible hl hbhsmall (by omega) (by omega) (by omega)

theorem normal_small_base_fixed_square_pair_impossible {u b k : T}
    (hu : NF u) (hb : NF b) (hk : NF k)
    (hub : ht u < ht b) (hbu : ht b ≤ ht u + 2)
    (hr : mul u (mul b k) = u)
    (hfixT : mul u (mul (mul b b) k) = u) : False := by
  have hB : ht (mul b b) = ht b + 1 := by rw [mul_square]; rfl
  rcases normal_fixed_square_pair_alternatives hu hb hk hr hfixT with hh | hh
  · exact normal_fixed_pair_small_growing_key_impossible hu hb (nf_mul hb hb) hk hub (by omega)
      hr hfixT hh.1 (by omega)
  · exact normal_fixed_pair_small_growing_key_impossible hu (nf_mul hb hb) hb hk (by omega) (by omega)
      hfixT hr hh.1 (by omega)

end submission.Austin12087Trace

/- Checked module: TraceSecondEqualReturnClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_equal_input_returning_q_impossible {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u)
    (hqr : ht (mul (mul u u) k) < ht k) : False := by
  obtain ⟨s,hns,_,hr,hfixT⟩ := normal_second_equal_input_q_fixed_pair hu hk hs hf hqr
  let b := mul (mul u u) u
  have hnB : NF b := nf_mul (nf_mul hu hu) hu
  have hsq : ht (mul u u) = ht u + 1 := by rw [mul_square]; rfl
  have hbg := mul_height_growth_of_left_ge (a:=mul u u) (b:=u) (by omega)
  change ht b = max (ht (mul u u)) (ht u) + 1 at hbg
  exact normal_small_base_fixed_square_pair_impossible hu hnB hns (by omega) (by omega) hr hfixT

theorem normal_second_returning_q_inputs_distinct {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) : u ≠ a := by
  intro hua
  rw [← hua] at hf hqr
  exact normal_second_equal_input_returning_q_impossible hu hk hs hf hqr

theorem normal_second_equal_input_column_order {u k y : T}
    (hu : NF u) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul u (mul (mul u u) k)) (mul u k)) = u) :
    ht (mul u k) < ht k ∧ ht k < ht (mul (mul u u) k) := by
  rcases normal_second_column_alternatives hu hu hk hf with hh | hh
  · exact False.elim (normal_second_equal_input_returning_q_impossible hu hk hs hf hh.1)
  · exact hh

end submission.Austin12087Trace

/- Checked module: TraceSecondStrictTail -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_factored_code_equal_tail_inputs {u a q h z : T}
    (hnq : NF q)
    (hn : NF (c (mul a q) u h (mul (mul u a) q) z))
    (hfix : mul u (mul q z) = a)
    (hae : ht a < ht (c (mul a q) u h (mul (mul u a) q) z))
    (hte : ht (mul q z) = ht (c (mul a q) u h (mul (mul u a) q) z)) : u = a := by
  let b := mul (mul u a) q
  let w := mul a q
  let e := c w u h b z
  let t := mul q z
  change NF e at hn
  change mul u t = a at hfix
  change ht a < ht e at hae
  change ht t = ht e at hte
  have hc := nf_code_actual hn
  have hgap := nf_code_height_gap hn
  change ht w + 2 ≤ ht e ∧ ht u + 2 ≤ ht e ∧ ht h + 2 ≤ ht e at hgap
  have hob : origin e = some (b,z) := rfl
  have hb := (origin_height hob).1
  have hz := (origin_height hob).2
  have hcol := common_column_height_bounds
    (show mul (mul u a) q = b from rfl) (show mul a q = w from rfl)
  have hq : ht q + 2 ≤ ht e := by omega
  have htg := mul_height_growth_of_right_le (a:=q) (b:=z) (by change ht z ≤ ht t; omega)
  change ht t = max (ht q) (ht z) + 1 at htg
  have hze : ht z + 1 = ht e := by omega
  have hot := mul_origin_of_right_height_le (a:=q) (b:=z) (by change ht z ≤ ht t; omega)
  change origin t = some (q,z) at hot
  have hnt : NF t := nf_mul hnq hc.2.2.2.2.1
  obtain ⟨s,_,_,_,_,hzs,hsgap,_⟩ := nf_return_origin_trace hnt hot hfix (by omega)
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  have hoz₁ := mul_origin_of_right_height_le (a:=u) (b:=h) (by rw [hzh]; omega)
  rw [hzh] at hoz₁
  have hoz₂ := mul_origin_of_right_height_le (a:=a) (b:=s) (by rw [hzs]; omega)
  rw [hzs] at hoz₂
  exact (Prod.mk.inj (Option.some.inj (hoz₁.symm.trans hoz₂))).1

theorem normal_second_returning_q_strict_tail {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    let g := mul u a
    let q := mul g k
    let v := mul a k
    let w := mul a q
    let e := mul w v
    ∃ t z h, NF t ∧ NF z ∧ NF h ∧
      v = c w e t a k ∧ k = c g q z e t ∧ e = c w u h (mul g q) z ∧
      mul u t = a ∧ mul q z = t ∧ ht t < ht e ∧ ht e < ht k := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  obtain ⟨t,z,h,hnt,hnz,hnh,hvc,hkc,hec,_,hat,_,_,hte,hhead,_,hek,_⟩ :=
    normal_second_returning_q_head hu ha hk hs hf hqr
  change v = c w e t a k at hvc
  change k = c g q z e t at hkc
  change e = c w u h (mul g q) z at hec
  change mul u t = a at hat
  change ht t ≤ ht e at hte
  change max (ht a) (ht q) < ht e at hhead
  change ht e < ht k at hek
  have htz : mul q z = t := (nf_code_actual (hkc ▸ hk)).2.2.2.2.2.2.2
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  have hstrict : ht t < ht e := by
    by_cases hh : ht t < ht e
    · exact hh
    · have hua := normal_factored_code_equal_tail_inputs (nf_mul (nf_mul hu ha) hk) (hec ▸ hne)
        (by rw [htz]; exact hat) (by rw [← hec]; omega) (by rw [htz,← hec]; omega)
      exact False.elim ((normal_second_returning_q_inputs_distinct hu ha hk hs hf hqr) hua)
  exact ⟨t,z,h,hnt,hnz,hnh,hvc,hkc,hec,hat,htz,hstrict,hek⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondReturningQTail -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem rotated_product_column_order {u a q : T}
    (he : mul (mul a q) u = mul u a) (hne : u ≠ a) :
    ht (mul (mul u a) q) ≤ ht (mul u q) := by
  let w := mul a q
  let g := mul u a
  let b := mul g q
  let z := mul u q
  change mul w u = g at he
  change ht b ≤ ht z
  by_cases hh : ht b ≤ ht z
  · exact hh
  · have hbg := mul_height_upper g q
    change ht b ≤ max (ht g) (ht q) + 1 at hbg
    have hwg : ht w < ht g ∧ ht u < ht g ∧ origin g = some (w,u) := by
      rcases mul_height_shape u q with hz | ⟨x,r,l,s,hqc,hzx⟩
      · change ht u < ht z ∧ ht q < ht z ∧ origin z = some (u,q) at hz
        have ho := mul_origin_of_right_height_le (a:=w) (b:=u) (by rw [he]; omega)
        rw [he] at ho
        exact ⟨(origin_height ho).1,(origin_height ho).2,ho⟩
      · have hw := mul_height_off_return_key (a:=a) hqc (Ne.symm hne)
        change ht w = max (ht a) (ht q) + 1 at hw
        rcases mul_height_shape w u with hg | ⟨x',r',l',s',huc,hgx⟩
        · rw [he] at hg
          exact hg
        · have hu : ht w < ht u ∧ ht g < ht u := by
            rw [he] at hgx
            rw [huc,← hgx]
            simp only [ht]
            omega
          have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
          change ht g = max (ht u) (ht a) + 1 at hg
          exact False.elim (by omega)
    have hag : ht a < ht g := by
      rcases mul_height_shape a q with hw | ⟨x,r,l,s,hqc,hwx⟩
      · change ht a < ht w ∧ ht q < ht w ∧ origin w = some (a,q) at hw
        omega
      · have hzg := mul_height_off_return_key (a:=u) hqc hne
        change ht z = max (ht u) (ht q) + 1 at hzg
        have haq : ht a < ht q := by rw [hqc]; simp only [ht]; omega
        omega
    have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
    change origin g = some (u,a) at hog
    exact False.elim (hne (Prod.mk.inj (Option.some.inj (hwg.2.2.symm.trans hog))).2)

theorem normal_factored_code_head_le_tail {u a q h z : T}
    (hn : NF (c (mul a q) u h (mul (mul u a) q) z))
    (hqe : ht q < ht (c (mul a q) u h (mul (mul u a) q) z))
    (hne : u ≠ a) : ht (mul (mul u a) q) ≤ ht z := by
  let b := mul (mul u a) q
  let w := mul a q
  let e := c w u h b z
  change NF e at hn
  change ht q < ht e at hqe
  change ht b ≤ ht z
  by_cases hh : ht b ≤ ht z
  · exact hh
  · have hc := nf_code_actual hn
    have hgap := nf_code_height_gap hn
    change ht w + 2 ≤ ht e ∧ ht u + 2 ≤ ht e ∧ ht h + 2 ≤ ht e at hgap
    have heact : mul b z = e := hc.2.2.2.2.2.1
    have heo : origin e = some (b,z) := rfl
    have heg := mul_height_growth_of_right_le (a:=b) (b:=z) (by
      rw [heact]
      exact Nat.le_of_lt (origin_height heo).2)
    rw [heact] at heg
    have hob := mul_origin_of_right_height_le (a:=mul u a) (b:=q) (by change ht q ≤ ht b; omega)
    change origin b = some (mul u a,q) at hob
    have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
    have hzh : mul u h = z := hc.2.2.2.2.2.2.2
    have hob' := mul_origin_of_right_height_le (a:=mul w u) (b:=h) (by rw [hbh]; omega)
    rw [hbh] at hob'
    have hp := Prod.mk.inj (Option.some.inj (hob'.symm.trans hob))
    have ho := rotated_product_column_order hp.1 hne
    rw [hp.2] at hzh
    rw [hzh] at ho
    exact False.elim (by change ht b ≤ ht z at ho; omega)

theorem normal_second_returning_q_tail_returns {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    let g := mul u a
    let q := mul g k
    let v := mul a k
    let w := mul a q
    let e := mul w v
    ∃ t z h, NF t ∧ NF z ∧ NF h ∧
      v = c w e t a k ∧ k = c g q z e t ∧ e = c w u h (mul g q) z ∧
      mul u t = a ∧ mul q z = t ∧ ht (mul g q) ≤ ht z ∧
      ht t < ht z ∧ ht z + 1 = ht e ∧ ht e < ht k := by
  let g := mul u a
  let q := mul g k
  let v := mul a k
  let w := mul a q
  let e := mul w v
  obtain ⟨t,z,h,hnt,hnz,hnh,hvc,hkc,hec,hat,htz,hte,hek⟩ :=
    normal_second_returning_q_strict_tail hu ha hk hs hf hqr
  change e = c w u h (mul g q) z at hec
  change ht t < ht e at hte
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  have hqc : ht q < ht e := by
    have ho : origin e = some (mul g q,z) := by rw [hec]; rfl
    have hc := common_column_height_bounds
      (show mul (mul u a) q = mul g q from rfl) (show mul a q = w from rfl)
    have hb := (origin_height ho).1
    have hw := (nf_code_height_gap (hec ▸ hne)).1
    rw [← hec] at hw
    omega
  have hbz := normal_factored_code_head_le_tail (hec ▸ hne) (by rw [← hec]; exact hqc)
    (normal_second_returning_q_inputs_distinct hu ha hk hs hf hqr)
  change ht (mul g q) ≤ ht z at hbz
  have heact : mul (mul g q) z = e := by
    have hh := (nf_code_actual (hec ▸ hne)).2.2.2.2.2.1
    rw [← hec] at hh
    exact hh
  have heo : origin e = some (mul g q,z) := by rw [hec]; rfl
  have heg := mul_height_growth_of_right_le (a:=mul g q) (b:=z) (by
    rw [heact]
    exact Nat.le_of_lt (origin_height heo).2)
  rw [heact] at heg
  have hze : ht z + 1 = ht e := by omega
  have htr : ht t < ht z := by
    by_cases hh : ht t < ht z
    · exact hh
    · have hg := mul_height_growth_of_right_le (a:=q) (b:=z) (by rw [htz]; omega)
      rw [htz] at hg
      exact False.elim (by omega)
  exact ⟨t,z,h,hnt,hnz,hnh,hvc,hkc,hec,hat,htz,hbz,htr,hze,hek⟩

end submission.Austin12087Trace

/- Checked module: TraceFactoredTailKey -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_factored_returning_tail_geometry {u a q h z : T}
    (hq : NF q)
    (hn : NF (c (mul a q) u h (mul (mul u a) q) z))
    (hfix : mul u (mul q z) = a)
    (hbz : ht (mul (mul u a) q) ≤ ht z)
    (htr : ht (mul q z) < ht z) :
    ht u + 3 ≤ ht z ∧ ht a + 3 ≤ ht z ∧
      ht h + 1 = ht z ∧ ht (mul (mul u a) q) + 2 ≤ ht h ∧
      origin z = some (u,h) := by
  let b := mul (mul u a) q
  let w := mul a q
  let e := c w u h b z
  let t := mul q z
  change NF e at hn
  change mul u t = a at hfix
  change ht b ≤ ht z at hbz
  change ht t < ht z at htr
  have hc := nf_code_actual hn
  have hgap := nf_code_height_gap hn
  have hkey := nf_code_key_height_gap hn
  change ht w + 2 ≤ ht e ∧ ht u + 2 ≤ ht e ∧ ht h + 2 ≤ ht e at hgap
  change ht w + 3 ≤ ht e at hkey
  have heact : mul b z = e := hc.2.2.2.2.2.1
  have heo : origin e = some (b,z) := rfl
  have heg := mul_height_growth_of_right_le (a:=b) (b:=z) (by
    rw [heact]
    exact Nat.le_of_lt (origin_height heo).2)
  rw [heact] at heg
  have hez : ht e = ht z + 1 := by omega
  have htgap := nf_mul_height_key_gap (a:=q) hc.2.2.2.2.1
  change ht t = max (ht q) (ht z) + 1 ∨ (ht q + 3 ≤ ht z ∧ ht t + 2 ≤ ht z) at htgap
  have hqt : ht q + 3 ≤ ht z ∧ ht t + 2 ≤ ht z := by rcases htgap with hh | hh <;> omega
  have hai := inverse_height_strict (inverse_complete a q)
  change ht a < max (ht q) (ht w) at hai
  have hui := inverse_height_strict (inverse_complete u t)
  rw [hfix] at hui
  have ha3 : ht a + 3 ≤ ht z := by omega
  have hu3 : ht u + 3 ≤ ht z := by omega
  have hg := mul_height_upper u a
  have hb := mul_height_upper (mul u a) q
  change ht b ≤ max (ht (mul u a)) (ht q) + 1 at hb
  have hbsmall : ht b < ht z := by omega
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  have hzg := mul_height_growth_of_right_le (a:=u) (b:=h) (by rw [hzh]; omega)
  rw [hzh] at hzg
  have hoz := mul_origin_of_right_height_le (a:=u) (b:=h) (by rw [hzh]; omega)
  rw [hzh] at hoz
  have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
  have hbret := nf_mul_height_key_gap (a:=mul w u) hc.2.2.1
  rw [hbh] at hbret
  have hb2 : ht b + 2 ≤ ht h := by rcases hbret with hh | hh <;> omega
  exact ⟨hu3,ha3,by omega,hb2,hoz⟩

theorem normal_factored_returning_tail_output_returns {u a q h z : T}
    (hq : NF q)
    (hn : NF (c (mul a q) u h (mul (mul u a) q) z))
    (hfix : mul u (mul q z) = a)
    (hbz : ht (mul (mul u a) q) ≤ ht z)
    (htr : ht (mul q z) < ht z) : ht a < ht (mul q z) := by
  let b := mul (mul u a) q
  let w := mul a q
  let t := mul q z
  let D := mul w u
  change mul u t = a at hfix
  change ht t < ht z at htr
  obtain ⟨hu3,ha3,hhz,hb2,hoz⟩ := normal_factored_returning_tail_geometry hq hn hfix hbz htr
  change ht b + 2 ≤ ht h at hb2
  have hc := nf_code_actual hn
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  have hbh : mul D h = b := hc.2.2.2.2.2.2.1
  have hl : ReturnLadder q D u t b z h := ⟨hc.2.2.2.2.1,hzh,hoz,rfl,hbh⟩
  change ht a < ht t
  by_cases hh : ht a < ht t
  · exact hh
  · have hag := mul_height_growth_of_right_le (a:=u) (b:=t) (by rw [hfix]; omega)
    rw [hfix] at hag
    have hg := mul_height_upper u a
    have hb := mul_height_upper (mul u a) q
    change ht b ≤ max (ht (mul u a)) (ht q) + 1 at hb
    rcases mul_height_growth_or_return a q with hw | ⟨x,r,l,s,hqc,hwx⟩
    · change ht w = max (ht a) (ht q) + 1 at hw
      have hD := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
      change ht D = max (ht w) (ht u) + 1 at hD
      exact False.elim (return_ladder_second_dominant_impossible hl htr (by omega) (by omega) (by omega))
    · have haq : ht a < ht q := by rw [hqc]; simp only [ht]; omega
      have hB := mul_height_growth_of_left_ge (a:=q) (b:=t) (by omega)
      obtain ⟨s',hl',_⟩ := return_ladder_step hl htr (by omega)
      exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))

theorem normal_factored_returning_tail_key_repeats {u a q h z : T}
    (hq : NF q)
    (hn : NF (c (mul a q) u h (mul (mul u a) q) z))
    (hfix : mul u (mul q z) = a)
    (hbz : ht (mul (mul u a) q) ≤ ht z)
    (htr : ht (mul q z) < ht z) : q = u := by
  let b := mul (mul u a) q
  let w := mul a q
  let t := mul q z
  change mul u t = a at hfix
  change ht t < ht z at htr
  obtain ⟨hu3,_,hhz,hb2,hoz⟩ := normal_factored_returning_tail_geometry hq hn hfix hbz htr
  change ht b + 2 ≤ ht h at hb2
  have hat := normal_factored_returning_tail_output_returns hq hn hfix hbz htr
  change ht a < ht t at hat
  have hc := nf_code_actual hn
  have hnt : NF t := nf_mul hq hc.2.2.2.2.1
  have hgap := nf_mul_height_key_gap (a:=u) hnt
  rw [hfix] at hgap
  have hut : ht u + 3 ≤ ht t ∧ ht a + 2 ≤ ht t := by rcases hgap with hh | hh <;> omega
  by_cases hqu : q = u
  · exact hqu
  · obtain ⟨s,l,r,htc⟩ := mul_return_of_height_lt (a:=u) (b:=t) (by rw [hfix]; exact hat)
    have hB := mul_height_off_return_key (a:=q) htc hqu
    have hg := mul_height_upper u a
    have hb := mul_height_upper (mul u a) q
    change ht b ≤ max (ht (mul u a)) (ht q) + 1 at hb
    have hzh : mul u h = z := hc.2.2.2.2.2.2.2
    have hbh : mul (mul w u) h = b := hc.2.2.2.2.2.2.1
    have hl : ReturnLadder q (mul w u) u t b z h := ⟨hc.2.2.2.2.1,hzh,hoz,rfl,hbh⟩
    obtain ⟨s',hl',_⟩ := return_ladder_step hl htr (by omega)
    exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))

end submission.Austin12087Trace

/- Checked module: TraceSecondReturningQRepeated -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_returning_q_key_repeats {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    mul (mul u a) k = u ∧ y = mul a u := by
  let q := mul (mul u a) k
  let e := mul (mul a q) (mul a k)
  obtain ⟨t,z,h,_,_,_,_,_,hec,hat,htz,hbz,htr,_,_⟩ :=
    normal_second_returning_q_tail_returns hu ha hk hs hf hqr
  change e = c (mul a q) u h (mul (mul u a) q) z at hec
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  have hqu := normal_factored_returning_tail_key_repeats (nf_mul (nf_mul hu ha) hk)
    (hec ▸ hne) (by rw [htz]; exact hat) hbz (by rw [htz]; exact htr)
  change q = u at hqu
  obtain ⟨_,_,_,_,_,_,_,_,_,hwy,_,_,_,_,_,_,_,_⟩ :=
    normal_second_returning_q_head hu ha hk hs hf hqr
  change mul a q = y at hwy
  rw [hqu] at hwy
  exact ⟨hqu,hwy.symm⟩

theorem normal_second_returning_q_repeated_core {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) :
    u ≠ a ∧ mul (mul u a) k = u ∧ y = mul a u ∧
    ∃ t z h s, NF t ∧ NF z ∧ NF h ∧ NF s ∧
      mul u t = a ∧ mul u z = t ∧ mul u h = z ∧
      mul a s = u ∧ mul t s = h ∧
      mul (mul (mul a u) u) h = mul (mul u a) u ∧
      ht u + 3 ≤ ht t ∧ ht a + 2 ≤ ht t ∧
      ht t + 2 ≤ ht z ∧ ht h + 1 = ht z ∧ ht z < ht k := by
  let q := mul (mul u a) k
  let e := mul (mul a q) (mul a k)
  obtain ⟨hqu,hy⟩ := normal_second_returning_q_key_repeats hu ha hk hs hf hqr
  change q = u at hqu
  obtain ⟨t,z,h,hnt,hnz,hnh,_,_,hec,hat,htz,hbz,htr,hze,hek⟩ :=
    normal_second_returning_q_tail_returns hu ha hk hs hf hqr
  change e = c (mul a q) u h (mul (mul u a) q) z at hec
  have hne : NF e := nf_mul (nf_mul ha (nf_mul (nf_mul hu ha) hk)) (nf_mul ha hk)
  have hn := hec ▸ hne
  have hfix : mul u (mul q z) = a := by rw [htz]; exact hat
  have hret : ht (mul q z) < ht z := by rw [htz]; exact htr
  obtain ⟨_,_,hhz,_,hoz⟩ := normal_factored_returning_tail_geometry (nf_mul (nf_mul hu ha) hk) hn hfix hbz hret
  have hatret := normal_factored_returning_tail_output_returns (nf_mul (nf_mul hu ha) hk) hn hfix hbz hret
  rw [htz] at hatret
  have hgap := nf_mul_height_key_gap (a:=u) hnt
  rw [hat] at hgap
  have hut : ht u + 3 ≤ ht t ∧ ht a + 2 ≤ ht t := by rcases hgap with hh | hh <;> omega
  have hc := nf_code_actual hn
  have hzh : mul u h = z := hc.2.2.2.2.2.2.2
  have hbh : mul (mul (mul a u) u) h = mul (mul u a) u := by
    have hh := hc.2.2.2.2.2.2.1
    rw [hqu] at hh
    exact hh
  change mul q z = t at htz
  rw [hqu] at htz
  obtain ⟨s,_,hns,_,has,hhs,_,_⟩ := nf_return_origin_trace hnz hoz htz htr
  rw [hat] at has
  have htg := nf_mul_height_key_gap (a:=u) hnz
  rw [htz] at htg
  have ht2 : ht t + 2 ≤ ht z := by rcases htg with hh | hh <;> omega
  exact ⟨normal_second_returning_q_inputs_distinct hu ha hk hs hf hqr,hqu,hy,
    t,z,h,s,hnt,hnz,hnh,hns,hat,htz,hzh,has,hhs,hbh,hut.1,hut.2,ht2,hhz,by omega⟩

end submission.Austin12087Trace

/- Checked module: TraceRepeatedQProducts -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem right_repeated_product_ne_transpose (a u : T) :
    mul (mul a u) u ≠ mul u a := by
  intro he
  let w := mul a u
  let g := mul u a
  change mul w u = g at he
  rcases mul_height_growth_or_return a u with hw | ⟨x,z,l,r,huc,hwx⟩
  · change ht w = max (ht a) (ht u) + 1 at hw
    have hD := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
    rw [he] at hD
    have hg := mul_height_upper u a
    change ht g ≤ max (ht u) (ht a) + 1 at hg
    omega
  · have hau : ht a < ht u := by rw [huc]; simp only [ht]; omega
    have hwu : ht w < ht u := by change ht (mul a u) < ht u; rw [hwx,huc]; simp only [ht]; omega
    have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hg
    have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
    change origin g = some (u,a) at hog
    have hog' := mul_origin_of_right_height_le (a:=w) (b:=u) (by rw [he]; omega)
    rw [he] at hog'
    have hwu' := (Prod.mk.inj (Option.some.inj (hog'.symm.trans hog))).1
    have hh := congrArg ht hwu'
    omega

theorem normal_repeated_q_product_ne_u {u a : T} (hu : NF u) (ha : NF a) :
    mul (mul (mul a u) u) (mul (mul u a) u) ≠ u := by
  intro he
  let w := mul a u
  let g := mul u a
  let D := mul w u
  let b := mul g u
  change mul D b = u at he
  have hnb : NF b := nf_mul (nf_mul hu ha) hu
  rcases nf_mul_height_key_gap (a:=a) hu with hw | hw
  · change ht w = max (ht a) (ht u) + 1 at hw
    have hD := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
    change ht D = max (ht w) (ht u) + 1 at hD
    have hg := mul_height_upper u a
    change ht g ≤ max (ht u) (ht a) + 1 at hg
    have hb := mul_height_upper g u
    change ht b ≤ max (ht g) (ht u) + 1 at hb
    have hA := mul_height_growth_of_left_ge (a:=D) (b:=b) (by omega)
    rw [he] at hA
    omega
  · change ht a + 3 ≤ ht u ∧ ht w + 2 ≤ ht u at hw
    have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hg
    have hb := mul_height_growth_of_left_ge (a:=g) (b:=u) (by omega)
    change ht b = max (ht g) (ht u) + 1 at hb
    have hob := mul_origin_of_right_height_le (a:=g) (b:=u) (by change ht u ≤ ht b; omega)
    change origin b = some (g,u) at hob
    have hkey := nf_mul_height_key_gap (a:=D) hnb
    rw [he] at hkey
    have hDsmall : ht D + 3 ≤ ht b := by rcases hkey with hh | hh <;> omega
    have hDr := nf_mul_height_key_gap (a:=w) hu
    change ht D = max (ht w) (ht u) + 1 ∨ (ht w + 3 ≤ ht u ∧ ht D + 2 ≤ ht u) at hDr
    have hDu : ht D < ht u := by rcases hDr with hh | hh <;> omega
    obtain ⟨za,la,ra,huc⟩ := mul_return_of_height_lt (a:=a) (b:=u) (by change ht w < ht u; omega)
    obtain ⟨zw,lw,rw,huc'⟩ := mul_return_of_height_lt (a:=w) (b:=u) hDu
    have hwa : w = a := (T.c.inj (huc'.symm.trans huc)).1
    have hDa : D = a := by change mul w u = a; rw [hwa]; exact hwa
    obtain ⟨r,_,_,_,_,hur,hrgap,_⟩ := nf_return_origin_trace hnb hob he (by omega)
    have hi := inverse_height_strict (inverse_complete u r)
    rw [hur] at hi
    omega

end submission.Austin12087Trace

/- Checked module: TraceRepeatedQTailStop -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem repeated_q_boundary_product_height {u a t : T}
    (hut : ht u + 3 ≤ ht t) (hat : ht a + 2 ≤ ht t)
    (hbt : ht (mul (mul u a) u) = ht t) :
    ht t < ht (mul (mul (mul a u) u) (mul (mul u a) u)) := by
  have hg := mul_height_upper u a
  have hb := mul_height_upper (mul u a) u
  have hau : ht u ≤ ht a := by omega
  have hw := mul_height_growth_of_left_ge (a:=a) (b:=u) hau
  have hD := mul_height_growth_of_left_ge (a:=mul a u) (b:=u) (by omega)
  have hA := mul_height_growth_of_left_ge (a:=mul (mul a u) u) (b:=mul (mul u a) u) (by omega)
  omega

theorem normal_repeated_q_tail_stops {u a t h s : T}
    (hu : NF u) (ha : NF a) (htn : NF t) (hhn : NF h) (hsn : NF s)
    (hat : mul u t = a) (hus : mul a s = u) (hhs : mul t s = h)
    (hbh : mul (mul (mul a u) u) h = mul (mul u a) u)
    (hut : ht u + 3 ≤ ht t) (hatgap : ht a + 2 ≤ ht t)
    (hth : ht t < ht h) : ht s ≤ ht t := by
  let w := mul a u
  let D := mul w u
  let b := mul (mul u a) u
  let A := mul D b
  change mul D h = b at hbh
  have hg := mul_height_upper u a
  have hb := mul_height_upper (mul u a) u
  change ht b ≤ max (ht (mul u a)) (ht u) + 1 at hb
  have hbt : ht b ≤ ht t := by omega
  by_cases hst : ht s ≤ ht t
  · exact hst
  · have hho := (distinct_outputs_height_origin hhs hus (by
      intro heq
      have hh := congrArg ht heq
      omega) (by omega)).1
    have hhg := mul_height_growth_of_right_le (a:=t) (b:=s) (by rw [hhs]; exact Nat.le_of_lt (origin_height hho).2)
    rw [hhs] at hhg
    obtain ⟨r,_,hnr,_,hAr,hsr,hrgap,_⟩ := nf_return_origin_trace hhn hho hbh (by omega)
    change mul A r = t at hAr
    change mul b r = s at hsr
    have hso := mul_origin_of_right_height_le (a:=b) (b:=r) (by rw [hsr]; omega)
    rw [hsr] at hso
    have hsg := mul_height_growth_of_right_le (a:=b) (b:=r) (by rw [hsr]; omega)
    rw [hsr] at hsg
    have htr : ht t < ht r := by
      by_cases hbr : ht b ≤ ht r
      · have htalt := nf_mul_height_key_gap (a:=A) hnr
        rw [hAr] at htalt
        rcases htalt with hh | hh <;> omega
      · have hbteq : ht b = ht t := by omega
        have hAb := repeated_q_boundary_product_height hut hatgap hbteq
        change ht t < ht A at hAb
        have hi := inverse_height_strict (inverse_complete A r)
        rw [hAr] at hi
        omega
    obtain ⟨j,_,hnj,_,hbj,hrj,hjgap,_⟩ := nf_return_origin_trace hsn hso hus (by omega)
    change mul w j = b at hbj
    have hro := mul_origin_of_right_height_le (a:=u) (b:=j) (by rw [hrj]; omega)
    rw [hrj] at hro
    have hrg := mul_height_growth_of_right_le (a:=u) (b:=j) (by rw [hrj]; omega)
    rw [hrj] at hrg
    have hl : ReturnLadder A w u t b r j := ⟨hnr,hrj,hro,hAr,hbj⟩
    obtain ⟨l,hl',_⟩ := return_ladder_step hl htr (by omega)
    obtain ⟨z,lt,rt,htc⟩ := mul_return_of_height_lt (a:=u) (b:=t) (by rw [hat]; omega)
    have hAu : A ≠ u := normal_repeated_q_product_ne_u hu ha
    have hAt := mul_height_off_return_key (a:=A) htc hAu
    have hbjret : ht b < ht j := by
      have hh := nf_mul_height_key_gap (a:=w) hnj
      rw [hbj] at hh
      rcases hh with hh | hh <;> omega
    exact False.elim (return_ladder_second_dominant_impossible hl' hbjret (by omega) (by omega) (by omega))

end submission.Austin12087Trace

/- Checked module: TraceRepeatedQDescendingHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_repeated_q_descending_head {u a t h s : T}
    (hu : NF u) (ha : NF a) (htn : NF t) (hhn : NF h) (hsn : NF s)
    (hne : u ≠ a)
    (hat : mul u t = a) (hus : mul a s = u) (hhs : mul t s = h)
    (hbh : mul (mul (mul a u) u) h = mul (mul u a) u)
    (hut : ht u + 3 ≤ ht t) (hatgap : ht a + 2 ≤ ht t)
    (hth : ht t < ht h) :
    let g := mul u a
    let D := mul (mul a u) u
    let b := mul g u
    let A := mul D b
    ∃ r l, NF r ∧ NF l ∧
      h = c D b r t s ∧ t = c u a l A r ∧
      mul A r = t ∧ mul b r = s ∧ mul g l = A ∧ mul a l = r ∧
      origin r = some (a,l) ∧
      ht h = ht t + 1 ∧ ht r + 1 = ht t ∧ ht l + 1 = ht r ∧
      ht s + 2 ≤ ht r ∧ ht A + 2 ≤ ht l := by
  let g := mul u a
  let w := mul a u
  let D := mul w u
  let b := mul g u
  let A := mul D b
  change mul D h = b at hbh
  have hst := normal_repeated_q_tail_stops hu ha htn hhn hsn hat hus hhs hbh hut hatgap hth
  have hho := (distinct_outputs_height_origin hhs hus (by
    intro heq
    have hh := congrArg ht heq
    omega) (by omega)).1
  have hhg := mul_height_growth_of_right_le (a:=t) (b:=s) (by
    rw [hhs]
    exact Nat.le_of_lt (origin_height hho).2)
  rw [hhs] at hhg
  have hht : ht h = ht t + 1 := by omega
  have hg := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hg
  have hb := mul_height_upper g u
  change ht b ≤ max (ht g) (ht u) + 1 at hb
  have hbt : ht b ≤ ht t := by omega
  obtain ⟨r,hcode,hnr,_,hAr,hsr,hrgap,_⟩ := nf_return_origin_trace hhn hho hbh (by omega)
  change mul A r = t at hAr
  change mul b r = s at hsr
  have hbgap := nf_code_height_gap (hcode ▸ hhn)
  rw [← hcode] at hbgap
  have hbt' : ht b < ht t := by omega
  have hto := mul_origin_of_right_height_le (a:=A) (b:=r) (by rw [hAr]; omega)
  rw [hAr] at hto
  have htg := mul_height_growth_of_right_le (a:=A) (b:=r) (by rw [hAr]; omega)
  rw [hAr] at htg
  obtain ⟨l,tcode,hnl,_,hAl,hrl,hlgap,_⟩ := nf_return_origin_trace htn hto hat (by omega)
  change mul g l = A at hAl
  have hArlt : ht A < ht r := by
    by_cases hh : ht A < ht r
    · exact hh
    · have hoA := mul_origin_of_right_height_le (a:=g) (b:=l) (by rw [hAl]; omega)
      rw [hAl] at hoA
      have hoA' := mul_origin_of_right_height_le (a:=D) (b:=b) (by change ht b ≤ ht A; omega)
      change origin A = some (D,b) at hoA'
      have hDg := (Prod.mk.inj (Option.some.inj (hoA'.symm.trans hoA))).1
      exact False.elim (right_repeated_product_ne_transpose a u hDg)
  have hrt : ht r + 1 = ht t := by omega
  have hro := mul_origin_of_right_height_le (a:=a) (b:=l) (by rw [hrl]; omega)
  rw [hrl] at hro
  have hrg := mul_height_growth_of_right_le (a:=a) (b:=l) (by rw [hrl]; omega)
  rw [hrl] at hrg
  have hal : ht a < ht l := by
    by_cases hh : ht a < ht l
    · exact hh
    · have hDkey := nf_code_key_height_gap (hcode ▸ hhn)
      rw [← hcode] at hDkey
      have hwg := mul_height_growth_of_left_ge (a:=a) (b:=u) (by omega)
      change ht w = max (ht a) (ht u) + 1 at hwg
      have hDg := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
      change ht D = max (ht w) (ht u) + 1 at hDg
      exact False.elim (by omega)
  have hlr : ht l + 1 = ht r := by omega
  have hAret := nf_mul_height_key_gap (a:=g) hnl
  rw [hAl] at hAret
  have hA2 : ht A + 2 ≤ ht l := by rcases hAret with hh | hh <;> omega
  have hsrlt : ht s < ht r := by
    by_cases hh : ht s < ht r
    · exact hh
    · have hsg := mul_height_growth_of_right_le (a:=b) (b:=r) (by rw [hsr]; omega)
      rw [hsr] at hsg
      have hso := mul_origin_of_right_height_le (a:=b) (b:=r) (by rw [hsr]; omega)
      rw [hsr] at hso
      obtain ⟨j,_,_,_,_,hrj,hjgap,_⟩ := nf_return_origin_trace hsn hso hus (by omega)
      have hro' := mul_origin_of_right_height_le (a:=u) (b:=j) (by rw [hrj]; omega)
      rw [hrj] at hro'
      exact False.elim (hne (Prod.mk.inj (Option.some.inj (hro'.symm.trans hro))).1)
  have hsret := nf_mul_height_key_gap (a:=b) hnr
  rw [hsr] at hsret
  have hs2 : ht s + 2 ≤ ht r := by rcases hsret with hh | hh <;> omega
  exact ⟨r,l,hnr,hnl,hcode,tcode,hAr,hsr,hAl,hrl,hro,hht,hrt,hlr,hs2,hA2⟩

end submission.Austin12087Trace

/- Checked module: TraceRepeatedQGrowingKey -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem transposed_product_ne_square (u a : T) : mul a u ≠ mul (mul u a) (mul u a) := by
  intro he
  have hs : ht (mul (mul u a) (mul u a)) = ht (mul u a) + 1 := by rw [mul_square]; rfl
  rcases mul_height_growth_or_return u a with hg | ⟨x,z,l,r,hac,hgx⟩
  · have hw := mul_height_upper a u
    have hh := congrArg ht he
    omega
  · have hua : ht u < ht a := by rw [hac]; simp only [ht]; omega
    have hga : ht (mul u a) < ht a := by rw [hgx,hac]; simp only [ht]; omega
    have hw := mul_height_growth_of_left_ge (a:=a) (b:=u) (by omega)
    have hh := congrArg ht he
    omega

theorem repeated_q_target_ne_a (u a : T) : mul (mul u a) u ≠ a := by
  intro he
  have hh := no_cross_two_cycle (mul u a) u
  rw [he] at hh
  exact hh rfl

theorem normal_repeated_q_growing_key {u a : T} (hu : NF u) (ha : NF a) (hne : u ≠ a) :
    let g := mul u a
    let D := mul (mul a u) u
    let b := mul g u
    let A := mul D b
    ht (mul g A) = max (ht g) (ht A) + 1 ∧
      ht u ≤ max (ht g) (ht A) ∧ ht a ≤ max (ht g) (ht A) := by
  let g := mul u a
  let w := mul a u
  let D := mul w u
  let b := mul g u
  let A := mul D b
  have hnb : NF b := nf_mul (nf_mul hu ha) hu
  have hne' : D ≠ b := by
    intro heq
    have hwg := right_injective _ _ u heq
    exact hne (mul_commutative_only_equal hwg.symm)
  change ht (mul g A) = max (ht g) (ht A) + 1 ∧
    ht u ≤ max (ht g) (ht A) ∧ ht a ≤ max (ht g) (ht A)
  rcases nf_mul_height_key_gap (a:=D) hnb with hAg | hAr
  · change ht A = max (ht D) (ht b) + 1 at hAg
    have hoA := mul_origin_of_right_height_le (a:=D) (b:=b) (by change ht b ≤ ht A; omega)
    change origin A = some (D,b) at hoA
    have hF : ht (mul g A) = max (ht g) (ht A) + 1 := by
      by_cases hh : ht (mul g A) < ht A
      · have hret := return_from_column_product
          (show mul w u = D from rfl) (show mul g u = b from rfl)
          (show mul D b = A from rfl) hoA hne' hh
        exact False.elim (transposed_product_ne_square u a hret.2.2.symm)
      · exact mul_height_growth_of_right_le (by omega)
    have hub : ht u < ht A ∧ ht a < ht A := by
      rcases mul_height_growth_or_return a u with hwg | ⟨x,z,l,r,huc,_⟩
      · change ht w = max (ht a) (ht u) + 1 at hwg
        have hDg := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
        change ht D = max (ht w) (ht u) + 1 at hDg
        omega
      · have hau : ht a < ht u := by rw [huc]; simp only [ht]; omega
        have hgg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
        change ht g = max (ht u) (ht a) + 1 at hgg
        have hbg := mul_height_growth_of_left_ge (a:=g) (b:=u) (by omega)
        change ht b = max (ht g) (ht u) + 1 at hbg
        omega
    exact ⟨hF,by omega,by omega⟩
  · change ht D + 3 ≤ ht b ∧ ht A + 2 ≤ ht b at hAr
    have hg := mul_height_upper u a
    change ht g ≤ max (ht u) (ht a) + 1 at hg
    have hb := mul_height_upper g u
    change ht b ≤ max (ht g) (ht u) + 1 at hb
    have hau : ht a < ht u := by
      rcases mul_height_growth_or_return a u with hwg | ⟨x,z,l,r,huc,_⟩
      · change ht w = max (ht a) (ht u) + 1 at hwg
        have hDg := mul_height_growth_of_left_ge (a:=w) (b:=u) (by omega)
        change ht D = max (ht w) (ht u) + 1 at hDg
        omega
      · rw [huc]; simp only [ht]; omega
    have hgg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hgg
    have hF := mul_height_growth_of_left_ge (a:=g) (b:=A) (by omega)
    exact ⟨hF,by omega,by omega⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondReturningQClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem factored_growing_key_ladder_impossible {g b s A a u l j : T}
    (hl : ReturnLadder g (mul b s) s A a l j)
    (hAl : ht A < ht l) (hus : mul a s = u) (hba : b ≠ a)
    (hF : ht (mul g A) = max (ht g) (ht A) + 1)
    (hu : ht u ≤ max (ht g) (ht A))
    (ha : ht a ≤ max (ht g) (ht A)) : False := by
  by_cases hsm : ht s ≤ max (ht g) (ht A)
  · by_cases hAg : ht A ≤ ht g
    · exact return_ladder_dominant_impossible hl (by omega) hAg (by omega)
    · have hlg := mul_height_growth_of_right_le (a:=s) (b:=j) (by
        rw [hl.2.1]
        exact Nat.le_of_lt (origin_height hl.2.2.1).2)
      rw [hl.2.1] at hlg
      have hgap := nf_mul_height_key_gap (a:=g) hl.1
      rw [hl.2.2.2.1] at hgap
      have hA2 : ht A + 2 ≤ ht l := by rcases hgap with hh | hh <;> omega
      obtain ⟨m,hl',_⟩ := return_ladder_step hl hAl (by omega)
      exact return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega)
  · obtain ⟨z,x,y,hsc⟩ := mul_return_of_height_lt (a:=a) (b:=s) (by rw [hus]; omega)
    have hbs := mul_height_off_return_key (a:=b) hsc hba
    exact return_ladder_second_dominant_impossible hl hAl (by omega) (by omega) (by omega)

theorem normal_repeated_q_core_impossible {u a t h s : T}
    (hu : NF u) (ha : NF a) (htn : NF t) (hhn : NF h) (hsn : NF s)
    (hne : u ≠ a)
    (hat : mul u t = a) (hus : mul a s = u) (hhs : mul t s = h)
    (hbh : mul (mul (mul a u) u) h = mul (mul u a) u)
    (hut : ht u + 3 ≤ ht t) (hatgap : ht a + 2 ≤ ht t)
    (hth : ht t < ht h) : False := by
  let g := mul u a
  let D := mul (mul a u) u
  let b := mul g u
  let A := mul D b
  obtain ⟨r,l,hnr,hnl,_,_,_,hsr,hAl,_,hro,_,hrt,hlr,hs2,hA2⟩ :=
    normal_repeated_q_descending_head hu ha htn hhn hsn hne hat hus hhs hbh hut hatgap hth
  change mul b r = s at hsr
  change mul g l = A at hAl
  change ht A + 2 ≤ ht l at hA2
  obtain ⟨j,_,_,_,haj,hlj,hjgap,_⟩ := nf_return_origin_trace hnr hro hsr (by omega)
  have hlo := mul_origin_of_right_height_le (a:=s) (b:=j) (by rw [hlj]; omega)
  rw [hlj] at hlo
  have hl : ReturnLadder g (mul b s) s A a l j := ⟨hnl,hlj,hlo,hAl,haj⟩
  obtain ⟨hF,hub,hab⟩ := normal_repeated_q_growing_key hu ha hne
  exact factored_growing_key_ladder_impossible hl (by omega) hus
    (repeated_q_target_ne_a u a) hF hub hab

theorem normal_second_returning_q_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hqr : ht (mul (mul u a) k) < ht k) : False := by
  obtain ⟨hne,_,_,t,z,h,s,hnt,_,hnh,hns,hat,_,_,hus,hhs,hbh,hut,hatgap,htz,hhz,_⟩ :=
    normal_second_returning_q_repeated_core hu ha hk hs hf hqr
  exact normal_repeated_q_core_impossible hu ha hnt hnh hns hne hat hus hhs hbh hut hatgap (by omega)

theorem normal_second_induction_requires_returning_v {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    ht (mul a k) < ht k ∧ ht k < ht (mul (mul u a) k) := by
  rcases normal_second_column_alternatives hu ha hk hf with hh | hh
  · exact False.elim (normal_second_returning_q_impossible hu ha hk hs hf hh.1)
  · exact hh

end submission.Austin12087Trace

/- Checked module: TraceReturningVInduction -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

def NormalReturningVStep : Prop := ∀ u a k y : T, NF u → NF a → NF k →
  NormalSecondBelow (ht k) →
  mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u →
  ht (mul a k) < ht k → False

theorem normal_second_of_returning_v_step (hv : NormalReturningVStep) :
    NormalSecondCycleAbsent := by
  have main : ∀ n, ∀ u a k : T, NF u → NF a → NF k → ht k = n →
      inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u = none := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro u a k hu ha hk hkn
      have hs : NormalSecondBelow (ht k) := by
        intro u' a' k' hu' ha' hk' _ _ hsmall
        exact ih (ht k') (by omega) u' a' k' hu' ha' hk' rfl
      cases hi : inverse (mul (mul a (mul (mul u a) k)) (mul a k)) u with
      | none => rfl
      | some y =>
        have hf := inverse_sound hi
        have hvr := (normal_second_induction_requires_returning_v hu ha hk hs hf).1
        exact False.elim (hv u a k y hu ha hk hs hf hvr)
  intro u a k hu ha hk
  exact main (ht k) u a k hu ha hk rfl

theorem normal_source_of_returning_v_step (hv : NormalReturningVStep)
    {x y z : T} (hx : NF x) (hy : NF y) (hz : NF z) : Source12087 x y z := by
  exact normal_source_of_second (normal_second_of_returning_v_step hv) hx hy hz

theorem normal_law_of_returning_v_step (hv : NormalReturningVStep) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) := by
  exact normal_law_of_second_query_absence (normal_second_of_returning_v_step hv)

end submission.Austin12087Trace

/- Checked module: TraceTwoColumnReturnChain -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_two_column_return_chain_impossible {a u v s : T}
    (ha : NF a) (hu : NF u) (hv : NF v) (hs : NF s)
    (hus : mul u s = v) (hvs : mul v s = a)
    (haw : mul a (mul (mul a v) s) = u)
    (hret : ht u < ht (mul (mul a v) s)) : False := by
  let w := mul (mul a v) s
  change mul a w = u at haw
  change ht u < ht w at hret
  have hnw : NF w := nf_mul (nf_mul ha hv) hs
  have hkey := nf_mul_height_key_gap (a:=a) hnw
  rw [haw] at hkey
  have ha3 : ht a + 3 ≤ ht w := by rcases hkey with hh | hh <;> omega
  have hav := mul_height_upper a v
  have hw := mul_height_upper (mul a v) s
  change ht w ≤ max (ht (mul a v)) (ht s) + 1 at hw
  have hasmall : ht a < max (ht v) (ht s) := by omega
  have hvsret : ht a < ht s := by
    have hh := nf_mul_height_key_gap (a:=v) hs
    rw [hvs] at hh
    rcases hh with hh | hh <;> omega
  obtain ⟨z,l,r,hsc⟩ := mul_return_of_height_lt (a:=v) (b:=s) (by rw [hvs]; exact hvsret)
  have hvsmall : ht v < ht s := by rw [hsc]; simp only [ht]; omega
  obtain ⟨z',l',r',hsc'⟩ := mul_return_of_height_lt (a:=u) (b:=s) (by rw [hus]; exact hvsmall)
  rw [hvs] at hsc
  rw [hus] at hsc'
  have hp := T.c.inj (hsc'.symm.trans hsc)
  have huv : u = v := hp.1
  have hva : v = a := hp.2.1
  have hus' : mul u s = u := hus.trans huv.symm
  change mul a (mul (mul a v) s) = u at haw
  rw [← hva,← huv] at haw
  exact normal_fixed_square_successor_impossible hu hs hus' haw

end submission.Austin12087Trace

/- Checked module: TraceTransposedPairExclusion -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_transposed_pair_returning_output_impossible {a w y : T}
    (ha : NF a) (hw : NF w)
    (hret : ht (mul a w) < ht w)
    (hf : mul y (mul w (mul a (mul w a))) = mul a w) : False := by
  let u := mul a w
  let k := mul w a
  let v := mul a k
  let e := mul w v
  change ht u < ht w at hret
  change mul y e = u at hf
  have hnU : NF u := nf_mul ha hw
  have hnK : NF k := nf_mul hw ha
  have hnV : NF v := nf_mul ha hnK
  have hnE : NF e := nf_mul hw hnV
  have hagap := nf_mul_height_key_gap (a:=a) hw
  change ht u = max (ht a) (ht w) + 1 ∨ (ht a + 3 ≤ ht w ∧ ht u + 2 ≤ ht w) at hagap
  have haw : ht a + 3 ≤ ht w ∧ ht u + 2 ≤ ht w := by rcases hagap with hh | hh <;> omega
  have hkg := mul_height_growth_of_left_ge (a:=w) (b:=a) (by omega)
  change ht k = max (ht w) (ht a) + 1 at hkg
  have hok := mul_origin_of_right_height_le (a:=w) (b:=a) (by change ht a ≤ ht k; omega)
  change origin k = some (w,a) at hok
  have hvupper := mul_height_upper a k
  change ht v ≤ max (ht a) (ht k) + 1 at hvupper
  have heg : ht e = max (ht w) (ht v) + 1 := by
    have hh := nf_mul_height_key_gap (a:=w) hnV
    change ht e = max (ht w) (ht v) + 1 ∨ (ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at hh
    rcases hh with hh | hh <;> omega
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
  change origin e = some (w,v) at hoe
  obtain ⟨t,_,hnt,_,hwt,hvt,htgap,_⟩ := nf_return_origin_trace hnE hoe hf (by omega)
  have hvr : ht v < ht k := by
    by_cases hh : ht v < ht k
    · exact hh
    · have hvg := mul_height_growth_of_right_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
      change ht v = max (ht a) (ht k) + 1 at hvg
      have hov := mul_origin_of_right_height_le (a:=a) (b:=k) (by change ht k ≤ ht v; omega)
      change origin v = some (a,k) at hov
      have hov' := (distinct_outputs_height_origin hvt hwt (by
        intro heq
        have hh' := congrArg ht heq
        omega) (by omega)).1
      have hp := Prod.mk.inj (Option.some.inj (hov'.symm.trans hov))
      rw [hp.2] at hwt
      have hgap := nf_mul_height_key_gap (a:=mul y u) hnK
      rw [hwt] at hgap
      exact False.elim (by rcases hgap with hh | hh <;> omega)
  have hvgap := nf_mul_height_key_gap (a:=a) hnK
  change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hvgap
  have hvw : ht v < ht w := by rcases hvgap with hh | hh <;> omega
  obtain ⟨s,_,hns,_,hws,has,hsgap,_⟩ := nf_return_origin_trace hnK hok (show mul a k = v from rfl) hvr
  have how := mul_origin_of_right_height_le (a:=mul a v) (b:=s) (by rw [hws]; omega)
  rw [hws] at how
  have how' := mul_origin_of_right_height_le (a:=mul y u) (b:=t) (by rw [hwt]; omega)
  rw [hwt] at how'
  have hts := (Prod.mk.inj (Option.some.inj (how'.symm.trans how))).2
  rw [hts] at hvt
  exact normal_two_column_return_chain_impossible ha hnU hnV hns hvt has
    (by rw [hws]) (by rw [hws]; exact hret)

theorem normal_transposed_pair_no_preimage {a w y : T} (ha : NF a) (hw : NF w) :
    mul y (mul w (mul a (mul w a))) ≠ mul a w := by
  intro hf
  by_cases hh : ht (mul a w) < ht w
  · exact normal_transposed_pair_returning_output_impossible ha hw hh hf
  · have hg := mul_height_growth_of_right_le (a:=a) (b:=w) (by omega)
    exact nf_transposed_pair_no_preimage ha hw (by omega) (by omega) hf

end submission.Austin12087Trace

/- Checked module: TraceSecondVFactorOrder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_factor_no_double_growth {u a k y r : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hgr : mul (mul a (mul a (mul (mul u a) k))) r = mul u a)
    (hkr : mul (mul a (mul (mul u a) k)) r = k)
    (hga : ht a ≤ ht (mul u a))
    (hgrgrow : ht r ≤ ht (mul u a)) : False := by
  let w := mul a (mul (mul u a) k)
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) hga
  have hog' := mul_origin_of_right_height_le (a:=mul a w) (b:=r) (by rw [hgr]; exact hgrgrow)
  rw [hgr] at hog'
  have hp := Prod.mk.inj (Option.some.inj (hog'.symm.trans hog))
  change mul a w = u ∧ r = a at hp
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hwa : mul w a = k := by rw [← hp.2]; exact hkr
  have hbad := normal_transposed_pair_no_preimage (y:=y) ha hnw
  rw [hwa,hp.1] at hbad
  exact hbad hf

theorem normal_second_v_factor_order {u a k y r : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hgr : mul (mul a (mul a (mul (mul u a) k))) r = mul u a)
    (hkr : mul (mul a (mul (mul u a) k)) r = k) :
    ht u < max (ht a) (ht r) ∧
      (ht (mul u a) < ht a ∨ ht (mul u a) < ht r) := by
  have hcases : ht (mul u a) < ht a ∨ ht (mul u a) < ht r := by
    by_cases hh : ht (mul u a) < ht a
    · exact Or.inl hh
    · by_cases hh' : ht (mul u a) < ht r
      · exact Or.inr hh'
      · exact False.elim (normal_second_v_factor_no_double_growth hu ha hk hf hgr hkr (by omega) (by omega))
  have hu' : ht u < max (ht a) (ht r) := by
    by_cases hh : ht u < max (ht a) (ht r)
    · exact hh
    · have hg := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
      rcases hcases with hh | hh <;> omega
  exact ⟨hu',hcases⟩

end submission.Austin12087Trace

/- Checked module: TraceRepeatedRightGrowth -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_repeated_right_growth_no_return {u s d x : T}
    (hu : NF u) (hs : NF s)
    (hg : ht s ≤ ht (mul u s))
    (he : mul d (mul (mul u s) s) = x)
    (hr : ht x < ht (mul (mul u s) s)) : False := by
  let v := mul u s
  let r := mul v s
  change ht s ≤ ht v at hg
  change mul d r = x at he
  change ht x < ht r at hr
  have hv := mul_height_growth_of_right_le (a:=u) (b:=s) hg
  change ht v = max (ht u) (ht s) + 1 at hv
  have hov := mul_origin_of_right_height_le (a:=u) (b:=s) hg
  change origin v = some (u,s) at hov
  have hrg := mul_height_growth_of_left_ge (a:=v) (b:=s) (by omega)
  change ht r = max (ht v) (ht s) + 1 at hrg
  have hor := mul_origin_of_right_height_le (a:=v) (b:=s) (by change ht s ≤ ht r; omega)
  change origin r = some (v,s) at hor
  have hnr : NF r := nf_mul (nf_mul hu hs) hs
  obtain ⟨j,_,_,_,hvj,hsj,hjgap,_⟩ := nf_return_origin_trace hnr hor he hr
  have hov' := mul_origin_of_right_height_le (a:=mul d x) (b:=j) (by rw [hvj]; omega)
  rw [hvj] at hov'
  have hjs := (Prod.mk.inj (Option.some.inj (hov'.symm.trans hov))).2
  rw [hjs] at hsj
  exact mul_ne_right x s hsj

end submission.Austin12087Trace

/- Checked module: TraceSecondVHighHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_high_head_trace {u a k y r s : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hs : NF s)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hgr : mul (mul a (mul a (mul (mul u a) k))) r = mul u a)
    (hkr : mul (mul a (mul (mul u a) k)) r = k)
    (hws : mul (mul a (mul a k)) s = mul a (mul (mul u a) k))
    (hrs : mul (mul a k) s = r)
    (hwk : ht (mul a (mul (mul u a) k)) < ht k)
    (hrk : ht r < ht k) (hsk : ht s + 2 ≤ ht k)
    (hrw : ht r ≤ ht (mul a (mul (mul u a) k))) :
    let v := mul a k
    let w := mul a (mul (mul u a) k)
    mul u s = v ∧ mul y u = mul a v ∧
      ht (mul a w) < ht w ∧ ht v < ht s ∧
      ht u < ht s ∧ ht a < ht s ∧ ht w = ht s + 1 ∧ ht k = ht s + 2 := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  let e := mul w v
  change mul u s = v ∧ mul y u = mul a v ∧ ht (mul a w) < ht w ∧
    ht v < ht s ∧ ht u < ht s ∧ ht a < ht s ∧ ht w = ht s + 1 ∧ ht k = ht s + 2
  change mul y e = u at hf
  change ht v < ht k at hvr
  change mul (mul a w) r = g at hgr
  change mul w r = k at hkr
  change mul (mul a v) s = w at hws
  change mul v s = r at hrs
  change ht w < ht k at hwk
  change ht r ≤ ht w at hrw
  have hkdom := normal_second_query_k_dominates hu ha hk hf
  have hkg := mul_height_growth_of_right_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hkg
  have hkw : ht k = ht w + 1 := by omega
  have hvret := nf_mul_height_key_gap (a:=a) hk
  change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hvret
  have hvw : ht v < ht w := by rcases hvret with hh | hh <;> omega
  have heg := mul_height_growth_of_left_ge (a:=w) (b:=v) (by omega)
  change ht e = max (ht w) (ht v) + 1 at heg
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by change ht v ≤ ht e; omega)
  change origin e = some (w,v) at hoe
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hnv : NF v := nf_mul ha hk
  obtain ⟨t,_,_,_,hwt,hvt,htgap,_⟩ := nf_return_origin_trace (nf_mul hnw hnv) hoe hf (by change ht u < ht e; omega)
  change ht t + 2 ≤ ht e at htgap
  have how := mul_origin_of_right_height_le (a:=mul a v) (b:=s) (by rw [hws]; omega)
  rw [hws] at how
  have how' := mul_origin_of_right_height_le (a:=mul y u) (b:=t) (by rw [hwt]; omega)
  rw [hwt] at how'
  have hp := Prod.mk.inj (Option.some.inj (how'.symm.trans how))
  rw [hp.2] at hvt
  have hgupper := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hgupper
  have hAw : ht (mul a w) < ht w := by
    by_cases hh : ht (mul a w) < ht w
    · exact hh
    · have hAg := mul_height_growth_of_right_le (a:=a) (b:=w) (by omega)
      have hgg := mul_height_growth_of_left_ge (a:=mul a w) (b:=r) (by omega)
      rw [hgr] at hgg
      exact False.elim (by omega)
  have hawgap := nf_mul_height_key_gap (a:=a) hnw
  have ha3 : ht a + 3 ≤ ht w := by rcases hawgap with hh | hh <;> omega
  have hav := mul_height_upper a v
  have hwupper := mul_height_upper (mul a v) s
  rw [hws] at hwupper
  have hvs : ht v < ht s := by
    by_cases hh : ht v < ht s
    · exact hh
    · have hvg := mul_height_growth_of_right_le (a:=u) (b:=s) (by rw [hvt]; omega)
      rw [hvt] at hvg
      have hav' : ht a < ht v := by omega
      have hrg := mul_height_growth_of_left_ge (a:=v) (b:=s) (by omega)
      rw [hrs] at hrg
      have hret : ht g < ht r := by omega
      have hgr' : mul (mul a w) (mul (mul u s) s) = g := by rw [hvt,hrs]; exact hgr
      exact False.elim (normal_repeated_right_growth_no_return hu hs (by rw [hvt]; omega)
        hgr' (by rw [hvt,hrs]; exact hret))
  have huvs := nf_mul_height_key_gap (a:=u) hs
  rw [hvt] at huvs
  have husmall : ht u < ht s := by rcases huvs with hh | hh <;> omega
  have hasmall : ht a < ht s := by omega
  have hwg := mul_height_growth_of_right_le (a:=mul a v) (b:=s) (by rw [hws]; omega)
  rw [hws] at hwg
  exact ⟨hvt,hp.1,hAw,hvs,husmall,hasmall,by omega,by omega⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondVHighFixed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_v_high_head_distinct_fixed {u a v w r s : T}
    (hu : NF u) (ha : NF a) (hw : NF w) (hr : NF r)
    (hus : mul u s = v) (hrs : mul v s = r)
    (hws : mul (mul a v) s = w) (hgr : mul (mul a w) r = mul u a)
    (hAw : ht (mul a w) < ht w)
    (hvs : ht v < ht s) (husmall : ht u < ht s) (hasmall : ht a < ht s)
    (hwh : ht w = ht s + 1) (hne : v ≠ u) :
    let g := mul u a
    mul a w = g ∧ mul g r = g ∧ ht r = ht w ∧
      ∃ t, NF t ∧ mul g t = s ∧ mul (mul g g) t = v ∧
        mul (mul a g) t = mul a v ∧ ht t + 1 = ht s := by
  let g := mul u a
  let A := mul a w
  change mul A r = g at hgr
  change ht A < ht w at hAw
  obtain ⟨z,l,j,hsc⟩ := mul_return_of_height_lt (a:=u) (b:=s) (by rw [hus]; exact hvs)
  have hrg := mul_height_off_return_key (a:=v) hsc hne
  rw [hrs] at hrg
  have hor := mul_origin_of_right_height_le (a:=v) (b:=s) (by rw [hrs]; omega)
  rw [hrs] at hor
  have hg := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hg
  obtain ⟨t,_,hnt,_,hvt,hst,htgap,hAkey⟩ := nf_return_origin_trace hr hor hgr (by omega)
  have how := mul_origin_of_right_height_le (a:=mul a v) (b:=s) (by rw [hws]; omega)
  rw [hws] at how
  obtain ⟨j,_,_,_,havj,hsj,hjgap,_⟩ := nf_return_origin_trace hw how (show mul a w = A from rfl) hAw
  have hos := mul_origin_of_right_height_le (a:=g) (b:=t) (by rw [hst]; omega)
  rw [hst] at hos
  have hos' := mul_origin_of_right_height_le (a:=A) (b:=j) (by rw [hsj]; omega)
  rw [hsj] at hos'
  have hp := Prod.mk.inj (Option.some.inj (hos'.symm.trans hos))
  have hAg : A = g := hp.1
  rw [hAg] at hvt hgr hAkey
  rw [hAg,hp.2] at havj
  have hsg := mul_height_growth_of_right_le (a:=g) (b:=t) (by rw [hst]; omega)
  rw [hst] at hsg
  exact ⟨hAg,hgr,by omega,t,hnt,hst,hvt,havj,by omega⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondVLowHead -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_low_head_trace {u a k y r s : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hr : NF r)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hgr : mul (mul a (mul a (mul (mul u a) k))) r = mul u a)
    (hkr : mul (mul a (mul (mul u a) k)) r = k)
    (hrs : mul (mul a k) s = r)
    (hrk : ht r < ht k) (hsk : ht s + 2 ≤ ht k)
    (hwr : ht (mul a (mul (mul u a) k)) < ht r) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    ht u < ht r ∧ ht a < ht r ∧ ht g < ht r ∧ ht k = ht r + 1 ∧
      ∃ t, NF t ∧ r = c (mul a w) g t v s ∧
        mul (mul (mul a w) g) t = v ∧ mul g t = s ∧ ht t + 2 ≤ ht r := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  change mul (mul a w) r = g at hgr
  change mul w r = k at hkr
  change mul v s = r at hrs
  change ht v < ht k at hvr
  change ht w < ht r at hwr
  have hkg := mul_height_growth_of_right_le (a:=w) (b:=r) (by rw [hkr]; omega)
  rw [hkr] at hkg
  have hkrht : ht k = ht r + 1 := by omega
  have hvret := nf_mul_height_key_gap (a:=a) hk
  change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hvret
  have har : ht a < ht r := by rcases hvret with hh | hh <;> omega
  have horder := normal_second_v_factor_order hu ha hk hf hgr hkr
  change ht u < max (ht a) (ht r) ∧ (ht g < ht a ∨ ht g < ht r) at horder
  have hur : ht u < ht r := by omega
  have hgrret : ht g < ht r := by
    rcases horder.2 with hh | hh <;> omega
  have hor := mul_origin_of_right_height_le (a:=v) (b:=s) (by rw [hrs]; omega)
  rw [hrs] at hor
  obtain ⟨t,hcode,hnt,_,hvt,hst,htgap,_⟩ := nf_return_origin_trace hr hor hgr hgrret
  exact ⟨hur,har,hgrret,hkrht,t,hnt,hcode,hvt,hst,htgap⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondVFrontier -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_returning_v_frontier {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    ∃ r s, NF r ∧ NF s ∧ ht r < ht k ∧ ht s < ht k ∧
      mul (mul a w) r = g ∧ mul w r = k ∧ mul (mul a v) s = w ∧ mul v s = r ∧
      ((ht w < ht r ∧ ht u < ht r ∧ ht a < ht r ∧ ht g < ht r ∧ ht k = ht r + 1 ∧
        ∃ t, NF t ∧ r = c (mul a w) g t v s ∧
          mul (mul (mul a w) g) t = v ∧ mul g t = s ∧ ht t + 2 ≤ ht r) ∨
       (v = u ∧ r = u ∧ y = a ∧ ht u < ht a ∧ ht g < ht a ∧
        mul u s = u ∧ ht (mul a w) < ht w ∧ ht w = ht s + 1 ∧ ht k = ht s + 2) ∨
       (v ≠ u ∧ mul a w = g ∧ mul g r = g ∧ mul y u = mul a v ∧ mul u s = v ∧
        ht r = ht w ∧ ht w = ht s + 1 ∧ ht k = ht s + 2 ∧
        ∃ t, NF t ∧ mul g t = s ∧ mul (mul g g) t = v ∧
          mul (mul a g) t = mul a v ∧ ht t + 1 = ht s)) := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  obtain ⟨r,s,hnr,hns,_,_,hgr,hkr,hws,hrs,hwk,hrk,hsk,_⟩ :=
    normal_second_returning_v_trace hu ha hk hf hvr
  change mul (mul a w) r = g at hgr
  change mul w r = k at hkr
  change mul (mul a v) s = w at hws
  change mul v s = r at hrs
  change ht w < ht k at hwk
  refine ⟨r,s,hnr,hns,hrk,by omega,hgr,hkr,hws,hrs,?_⟩
  by_cases hwr : ht w < ht r
  · have hh := normal_second_v_low_head_trace hu ha hk hnr hf hvr hgr hkr hrs hrk hsk hwr
    exact Or.inl ⟨hwr,hh⟩
  · obtain ⟨hus,hyu,hAw,hvs,husmall,hasmall,hwh,hkh⟩ :=
      normal_second_v_high_head_trace hu ha hk hns hf hvr hgr hkr hws hrs hwk hrk hsk (by change ht r ≤ ht w; omega)
    change mul u s = v at hus
    change mul y u = mul a v at hyu
    change ht (mul a w) < ht w at hAw
    change ht v < ht s at hvs
    change ht w = ht s + 1 at hwh
    by_cases hvu : v = u
    · have hru : r = u := by rw [hvu,hus,hvu] at hrs; exact hrs.symm
      have hya : y = a := by rw [hvu] at hyu; exact right_injective _ _ u hyu
      have horder := normal_second_v_factor_order hu ha hk hf hgr hkr
      change ht u < max (ht a) (ht r) ∧ (ht g < ht a ∨ ht g < ht r) at horder
      rw [hru] at horder
      have hua : ht u < ht a := by omega
      have hga : ht g < ht a := by rcases horder.2 with hh | hh <;> omega
      exact Or.inr (Or.inl ⟨hvu,hru,hya,hua,hga,hus.trans hvu,hAw,hwh,hkh⟩)
    · have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
      obtain ⟨hag,hfix,hrw,t,hnt,hst,hvt,havt,hth⟩ :=
        normal_v_high_head_distinct_fixed hu ha hnw hnr hus hrs hws hgr hAw hvs husmall hasmall hwh hvu
      exact Or.inr (Or.inr ⟨hvu,hag,hfix,hyu,hus,hrw,hwh,hkh,t,hnt,hst,hvt,havt,hth⟩)

end submission.Austin12087Trace

/- Checked module: TraceSecondVEqualFixedClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_fixed_column_short_key_impossible {u a w s : T}
    (hw : NF w)
    (hfixed : mul u s = u) (hws : mul (mul a u) s = w)
    (hua : ht u < ht a) (hAa : ht (mul a w) < ht a)
    (hAw : ht (mul a w) < ht w) (hwh : ht w = ht s + 1) : False := by
  let A := mul a w
  let B := mul a u
  let C := mul a A
  change ht A < ht a at hAa
  change ht A < ht w at hAw
  have how := mul_origin_of_right_height_le (a:=B) (b:=s) (by rw [hws]; omega)
  rw [hws] at how
  obtain ⟨j,_,_,hns,hCj,hAj,hjgap,_⟩ :=
    nf_return_origin_trace hw how (show mul a w = A from rfl) hAw
  have hos := mul_origin_of_right_height_le (a:=A) (b:=j) (by rw [hAj]; omega)
  rw [hAj] at hos
  have huS := inverse_height_strict (inverse_complete u s)
  rw [hfixed] at huS
  have hB := mul_height_growth_of_left_ge (a:=a) (b:=u) (by omega)
  have hC := mul_height_growth_of_left_ge (a:=a) (b:=A) (by omega)
  change ht B = max (ht a) (ht u) + 1 at hB
  change ht C = max (ht a) (ht A) + 1 at hC
  have hl : ReturnLadder u C A u B s j := ⟨hns,hAj,hos,hfixed,hCj⟩
  exact return_ladder_second_dominant_impossible hl (by omega) (by omega) (by omega) (by omega)

theorem normal_v_equal_fixed_exception_impossible {u a w s : T}
    (hw : NF w)
    (hfixed : mul u s = u) (hws : mul (mul a u) s = w)
    (hgr : mul (mul a w) u = mul u a)
    (hua : ht u < ht a) (hga : ht (mul u a) < ht a)
    (hAw : ht (mul a w) < ht w) (hwh : ht w = ht s + 1) : False := by
  have hA := inverse_height_strict (inverse_complete (mul a w) u)
  rw [hgr] at hA
  exact normal_fixed_column_short_key_impossible hw hfixed hws hua (by omega) hAw hwh

end submission.Austin12087Trace

/- Checked module: TraceShortColumnTransport -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_short_column_transport_impossible {a b d t v : T}
    (htn : NF t) (hb : mul b t = v) (hd : mul d t = mul a v)
    (hat : ht a < ht t) (hvt : ht v < ht t) : False := by
  have hbGap := nf_mul_height_key_gap (a:=b) htn
  rw [hb] at hbGap
  have hv2 : ht v + 2 ≤ ht t := by rcases hbGap with hh | hh <;> omega
  have hav := mul_height_upper a v
  have hdGap := nf_mul_height_key_gap (a:=d) htn
  rw [hd] at hdGap
  have havt : ht (mul a v) < ht t := by rcases hdGap with hh | hh <;> omega
  obtain ⟨z,l,r,hct⟩ := mul_return_of_height_lt (a:=b) (b:=t) (by rw [hb]; exact hvt)
  obtain ⟨z',l',r',hct'⟩ := mul_return_of_height_lt (a:=d) (b:=t) (by rw [hd]; exact havt)
  have hout := (T.c.inj (hct.symm.trans hct')).2.1
  rw [hb,hd] at hout
  exact mul_ne_right a v hout.symm

theorem normal_v_distinct_fixed_exception_impossible {a g v w s t : T}
    (hw : NF w) (htn : NF t)
    (hAw : ht (mul a w) < ht w)
    (hwh : ht w = ht s + 1) (hth : ht t + 1 = ht s)
    (hvs : ht v < ht s)
    (hvt : mul (mul g g) t = v) (havt : mul (mul a g) t = mul a v) : False := by
  have haGap := nf_mul_height_key_gap (a:=a) hw
  have ha3 : ht a + 3 ≤ ht w := by rcases haGap with hh | hh <;> omega
  have hvGap := nf_mul_height_key_gap (a:=mul g g) htn
  rw [hvt] at hvGap
  have hvsmall : ht v < ht t := by rcases hvGap with hh | hh <;> omega
  exact normal_short_column_transport_impossible htn hvt havt (by omega) hvsmall

end submission.Austin12087Trace

/- Checked module: TraceSecondVHighClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_high_head_impossible {u a k y r s : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hnr : NF r) (hns : NF s)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hgr : mul (mul a (mul a (mul (mul u a) k))) r = mul u a)
    (hkr : mul (mul a (mul (mul u a) k)) r = k)
    (hws : mul (mul a (mul a k)) s = mul a (mul (mul u a) k))
    (hrs : mul (mul a k) s = r)
    (hwk : ht (mul a (mul (mul u a) k)) < ht k)
    (hrk : ht r < ht k) (hsk : ht s + 2 ≤ ht k)
    (hrw : ht r ≤ ht (mul a (mul (mul u a) k))) : False := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  obtain ⟨hus,_,hAw,hvs,husmall,hasmall,hwh,_⟩ :=
    normal_second_v_high_head_trace hu ha hk hns hf hvr hgr hkr hws hrs hwk hrk hsk hrw
  change mul u s = v at hus
  change ht (mul a w) < ht w at hAw
  change ht v < ht s at hvs
  change ht w = ht s + 1 at hwh
  change mul (mul a w) r = g at hgr
  change mul (mul a v) s = w at hws
  change mul v s = r at hrs
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  by_cases hvu : v = u
  · have hru : r = u := by rw [hvu,hus,hvu] at hrs; exact hrs.symm
    have horder := normal_second_v_factor_order hu ha hk hf hgr hkr
    change ht u < max (ht a) (ht r) ∧ (ht g < ht a ∨ ht g < ht r) at horder
    rw [hru] at horder
    have hua : ht u < ht a := by omega
    have hga : ht g < ht a := by rcases horder.2 with hh | hh <;> omega
    rw [hru] at hgr
    rw [hvu] at hws
    exact normal_v_equal_fixed_exception_impossible hnw (hus.trans hvu) hws hgr hua hga hAw hwh
  · obtain ⟨_,_,_,t,hnt,_,hvt,havt,hth⟩ :=
      normal_v_high_head_distinct_fixed hu ha hnw hnr hus hrs hws hgr hAw hvs husmall hasmall hwh hvu
    exact normal_v_distinct_fixed_exception_impossible hnw hnt hAw hwh hth hvs hvt havt

theorem normal_second_returning_v_low_head {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    ∃ r s, NF r ∧ NF s ∧ ht r < ht k ∧ ht s + 2 ≤ ht k ∧
      mul (mul a w) r = g ∧ mul w r = k ∧ mul (mul a v) s = w ∧ mul v s = r ∧
      ht w < ht r ∧ ht u < ht r ∧ ht a < ht r ∧ ht g < ht r ∧ ht k = ht r + 1 ∧
      ∃ t, NF t ∧ r = c (mul a w) g t v s ∧
        mul (mul (mul a w) g) t = v ∧ mul g t = s ∧ ht t + 2 ≤ ht r := by
  obtain ⟨r,s,hnr,hns,_,_,hgr,hkr,hws,hrs,hwk,hrk,hsk,_⟩ :=
    normal_second_returning_v_trace hu ha hk hf hvr
  have hwr : ht (mul a (mul (mul u a) k)) < ht r := by
    by_cases hh : ht (mul a (mul (mul u a) k)) < ht r
    · exact hh
    · exact False.elim (normal_second_v_high_head_impossible hu ha hk hnr hns hf hvr
        hgr hkr hws hrs hwk hrk hsk (by omega))
  exact ⟨r,s,hnr,hns,hrk,hsk,hgr,hkr,hws,hrs,hwr,
    normal_second_v_low_head_trace hu ha hk hnr hf hvr hgr hkr hrs hrk hsk hwr⟩

end submission.Austin12087Trace

/- Checked module: TraceLowAlignedColumns -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_aligned_columns_impossible {u a v w s t d : T}
    (hnv : NF v) (hns : NF s) (hnt : NF t)
    (hvt : mul u t = v) (hwt : mul d t = w) (hst : mul (mul u a) t = s)
    (hws : mul (mul a v) s = w) (hback : mul (mul a w) (mul u a) = u)
    (hvht : ht v = ht t + 1) (hsv : ht s ≤ ht v) (hwv : ht w ≤ ht v)
    (hgv : ht (mul u a) < ht v) : False := by
  let g := mul u a
  let D := mul a v
  let A := mul a w
  change mul g t = s at hst
  change mul D s = w at hws
  change mul A g = u at hback
  change ht g < ht v at hgv
  have hD := inverse_height_strict (inverse_complete D s)
  rw [hws] at hD
  have hDsmall : ht D < ht v := by omega
  have hDgap := nf_mul_height_key_gap (a:=a) hnv
  change ht D = max (ht a) (ht v) + 1 ∨ (ht a + 3 ≤ ht v ∧ ht D + 2 ≤ ht v) at hDgap
  have ha3 : ht a + 3 ≤ ht v := by rcases hDgap with hh | hh <;> omega
  have hD2 : ht D + 2 ≤ ht v := by rcases hDgap with hh | hh <;> omega
  by_cases hsvlt : ht s < ht v
  · have hsGap := nf_mul_height_key_gap (a:=g) hnt
    rw [hst] at hsGap
    have hs2 : ht s + 2 ≤ ht t := by rcases hsGap with hh | hh <;> omega
    have hwUpper := mul_height_upper D s
    rw [hws] at hwUpper
    have hwGap := nf_mul_height_key_gap (a:=d) hnt
    rw [hwt] at hwGap
    have hwtSmall : ht w < ht t := by rcases hwGap with hh | hh <;> omega
    obtain ⟨z,l,r,hct⟩ := mul_return_of_height_lt (a:=g) (b:=t) (by rw [hst]; omega)
    obtain ⟨z',l',r',hct'⟩ := mul_return_of_height_lt (a:=d) (b:=t) (by rw [hwt]; omega)
    have hsw := (T.c.inj (hct.symm.trans hct')).2.1
    rw [hst,hwt] at hsw
    exact mul_ne_right D s (hws.trans hsw.symm)
  · have hsvEq : ht s = ht v := by omega
    have hwGap := nf_mul_height_key_gap (a:=D) hns
    rw [hws] at hwGap
    have hw2 : ht w + 2 ≤ ht s := by rcases hwGap with hh | hh <;> omega
    have hwGap' := nf_mul_height_key_gap (a:=d) hnt
    rw [hwt] at hwGap'
    have hwt2 : ht w + 2 ≤ ht t := by rcases hwGap' with hh | hh <;> omega
    have hov := mul_origin_of_right_height_le (a:=u) (b:=t) (by rw [hvt]; omega)
    rw [hvt] at hov
    have hos := mul_origin_of_right_height_le (a:=g) (b:=t) (by rw [hst]; omega)
    rw [hst] at hos
    obtain ⟨j,_,hnj,_,huj,htj,hjGap,_⟩ :=
      nf_return_origin_trace hnv hov (show mul a v = D from rfl) hDsmall
    obtain ⟨l,_,_,_,hgl,htl,hlGap,_⟩ :=
      nf_return_origin_trace hns hos hws (by omega)
    have hot := mul_origin_of_right_height_le (a:=D) (b:=j) (by rw [htj]; omega)
    rw [htj] at hot
    have hot' := mul_origin_of_right_height_le (a:=w) (b:=l) (by rw [htl]; omega)
    rw [htl] at hot'
    have hp := Prod.mk.inj (Option.some.inj (hot.symm.trans hot'))
    rw [hp.1] at huj htj hgl
    rw [←hp.2] at hgl
    change mul A j = u at huj
    have hjHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by rw [htj]; omega)
    rw [htj] at hjHeight
    have hjt : ht j + 1 = ht t := by omega
    have huHeight := inverse_height_strict (inverse_complete u a)
    change ht u < max (ht a) (ht g) at huHeight
    have huGap := nf_mul_height_key_gap (a:=A) hnj
    rw [huj] at huGap
    have hu2 : ht u + 2 ≤ ht j := by rcases huGap with hh | hh <;> omega
    have hneq : mul w w ≠ A := by
      intro he
      rw [he,huj] at hgl
      have hgu : g = u := hgl.symm
      exact mul_ne_right A g (hback.trans hgu.symm)
    obtain ⟨z,l',r,hjc⟩ := mul_return_of_height_lt (a:=A) (b:=j) (by rw [huj]; omega)
    have hgGrow := mul_height_off_return_key (a:=mul w w) hjc hneq
    rw [hgl] at hgGrow
    have hgUpper := mul_height_upper u a
    change ht g ≤ max (ht u) (ht a) + 1 at hgUpper
    omega

end submission.Austin12087Trace

/- Checked module: TraceSecondVLowGrowingMiddle -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_low_growing_middle_v_large_impossible {u a k y r s t : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hnr : NF r) (hns : NF s) (hnt : NF t)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hws : mul (mul a (mul a k)) s = mul a (mul (mul u a) k))
    (hrs : mul (mul a k) s = r)
    (hwr : ht (mul a (mul (mul u a) k)) < ht r)
    (hkh : ht k = ht r + 1)
    (hrc : r = c (mul a (mul a (mul (mul u a) k))) (mul u a) t (mul a k) s)
    (hvt : mul (mul (mul a (mul a (mul (mul u a) k))) (mul u a)) t = mul a k)
    (hst : mul (mul u a) t = s)
    (hsv : ht s ≤ ht (mul a k))
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) : False := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  let A := mul a w
  let B := mul A g
  let e := mul w v
  change mul y e = u at hf
  change ht v < ht k at hvr
  change mul (mul a v) s = w at hws
  change mul v s = r at hrs
  change ht w < ht r at hwr
  change r = c A g t v s at hrc
  change mul B t = v at hvt
  change mul g t = s at hst
  change ht s ≤ ht v at hsv
  change ht v ≤ ht e at hmid
  have hrHeight := mul_height_growth_of_left_ge (a:=v) (b:=s) hsv
  rw [hrs] at hrHeight
  have hrh : ht r = ht v + 1 := by omega
  have hretGap := nf_mul_height_key_gap (a:=a) hk
  change ht v = max (ht a) (ht k) + 1 ∨ (ht a + 3 ≤ ht k ∧ ht v + 2 ≤ ht k) at hretGap
  have ha3 : ht a + 3 ≤ ht k := by rcases hretGap with hh | hh <;> omega
  have hcodeGap := nf_code_height_gap (hrc ▸ hnr)
  rw [←hrc] at hcodeGap
  have huHeight := inverse_height_strict (inverse_complete u a)
  change ht u < max (ht a) (ht g) at huHeight
  have hu2 : ht u + 2 ≤ ht v := by omega
  have heHeight := mul_height_growth_of_right_le (a:=w) (b:=v) hmid
  change ht e = max (ht w) (ht v) + 1 at heHeight
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) hmid
  change origin e = some (w,v) at hoe
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hnv : NF v := nf_mul ha hk
  obtain ⟨j,_,_,_,hwj,hvj,hjGap,_⟩ :=
    nf_return_origin_trace (nf_mul hnw hnv) hoe hf (by change ht u < ht e; omega)
  change ht j + 2 ≤ ht e at hjGap
  have hov := mul_origin_of_right_height_le (a:=u) (b:=j) (by rw [hvj]; omega)
  rw [hvj] at hov
  have hov' := mul_origin_of_right_height_le (a:=B) (b:=t) (by rw [hvt]; omega)
  rw [hvt] at hov'
  have hp := Prod.mk.inj (Option.some.inj (hov.symm.trans hov'))
  rw [hp.2] at hvj hwj
  have hvHeight := mul_height_growth_of_right_le (a:=u) (b:=t) (by rw [hvj]; omega)
  rw [hvj] at hvHeight
  exact normal_low_aligned_columns_impossible hnv hns hnt hvj hwj hst hws hp.1.symm
    (by omega) hsv (by omega) (by change ht g < ht v; omega)

theorem normal_second_v_growing_middle_low_trace {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    ∃ r s t, NF r ∧ NF s ∧ NF t ∧ ht r < ht k ∧ ht s + 2 ≤ ht k ∧
      mul (mul a w) r = g ∧ mul w r = k ∧ mul (mul a v) s = w ∧ mul v s = r ∧
      ht w < ht r ∧ ht u < ht r ∧ ht a < ht r ∧ ht g < ht r ∧ ht k = ht r + 1 ∧
      r = c (mul a w) g t v s ∧ mul (mul (mul a w) g) t = v ∧ mul g t = s ∧
      ht t + 2 ≤ ht r ∧ ht v < ht s := by
  obtain ⟨r,s,hnr,hns,hrk,hsk,hgr,hkr,hws,hrs,hwr,hur,har,hgrh,hkh,t,hnt,hrc,hvt,hst,htgap⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  have hvs : ht (mul a k) < ht s := by
    by_cases hh : ht (mul a k) < ht s
    · exact hh
    · exact False.elim (normal_second_v_low_growing_middle_v_large_impossible
        hu ha hk hnr hns hnt hf hvr hws hrs hwr hkh hrc hvt hst (by omega) hmid)
  exact ⟨r,s,t,hnr,hns,hnt,hrk,hsk,hgr,hkr,hws,hrs,hwr,hur,har,hgrh,hkh,hrc,hvt,hst,htgap,hvs⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondVLowKeyDescent -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_low_equal_keys_descent_impossible {u a k y s t : T}
    (hu : NF u) (ha : NF a) (hnt : NF t)
    (hs : NormalSecondBelow (ht k))
    (huk : ht u < ht k) (hak : ht a < ht k) (htk : ht t < ht k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hws : mul (mul a (mul a k)) s = mul a (mul (mul u a) k))
    (hvt : mul (mul (mul a (mul a (mul (mul u a) k))) (mul u a)) t = mul a k)
    (hst : mul (mul u a) t = s)
    (hB : mul (mul a (mul a (mul (mul u a) k))) (mul u a) = a)
    (hD : mul a (mul a k) = a) : False := by
  rw [hB] at hvt
  rw [hD] at hws
  have hquery := hs u a t hu ha hnt huk hak htk
  have hsmall : mul y (mul (mul a (mul (mul u a) t)) (mul a t)) = u := by
    rw [hst,hws,hvt]
    exact hf
  have hi := inverse_complete y (mul (mul a (mul (mul u a) t)) (mul a t))
  rw [hsmall,hquery] at hi
  cases hi

end submission.Austin12087Trace

/- Checked module: TraceSecondVLowColumnHeight -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_growing_middle_column_height {u a v w r s t y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v) (hnw : NF w) (hnr : NF r) (hns : NF s) (hnt : NF t)
    (hf : mul y (mul w v) = u)
    (hws : mul (mul a v) s = w) (hrs : mul v s = r)
    (hvt : mul (mul (mul a w) (mul u a)) t = v) (hst : mul (mul u a) t = s)
    (hrc : r = c (mul a w) (mul u a) t v s)
    (hwr : ht w < ht r) (hvs : ht v < ht s)
    (hmid : ht v ≤ ht (mul w v)) (houter : ht u < ht (mul w v)) :
    ht (mul u a) < ht t ∧ ht t + 1 = ht s ∧ ht r = ht s + 1 ∧
      ht v + 2 ≤ ht t ∧ ht (mul (mul a w) (mul u a)) + 3 ≤ ht t ∧
      ht w + 2 ≤ ht s ∧ ht (mul a v) + 3 ≤ ht s := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  let D := mul a v
  let e := mul w v
  change mul y e = u at hf
  change mul D s = w at hws
  change mul B t = v at hvt
  change mul g t = s at hst
  change r = c A g t v s at hrc
  change ht v ≤ ht e at hmid
  change ht u < ht e at houter
  have hrOrigin : origin r = some (v,s) := by rw [hrc]; rfl
  have hrGrow := mul_height_growth_of_right_le (a:=v) (b:=s) (by
    rw [hrs]; exact Nat.le_of_lt (origin_height hrOrigin).2)
  rw [hrs] at hrGrow
  have hrh : ht r = ht s + 1 := by omega
  have hrGap := nf_code_height_gap (hrc ▸ hnr)
  have hrKey := nf_code_key_height_gap (hrc ▸ hnr)
  rw [←hrc] at hrGap hrKey
  have hwGap := nf_mul_height_key_gap (a:=D) hns
  rw [hws] at hwGap
  have hw2 : ht w + 2 ≤ ht s := by rcases hwGap with hh | hh <;> omega
  have hD3 : ht D + 3 ≤ ht s := by rcases hwGap with hh | hh <;> omega
  have haHeight := inverse_height_strict (inverse_complete a w)
  change ht a < max (ht w) (ht A) at haHeight
  have ha3 : ht a + 3 ≤ ht s := by omega
  have heGrow := mul_height_growth_of_right_le (a:=w) (b:=v) hmid
  change ht e = max (ht w) (ht v) + 1 at heGrow
  have heNF : NF e := nf_mul hnw hnv
  have huGap := nf_mul_height_key_gap (a:=y) heNF
  rw [hf] at huGap
  have hu2 : ht u + 2 ≤ ht e := by rcases huGap with hh | hh <;> omega
  have hgUpper := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hgUpper
  have hg2 : ht g + 2 ≤ ht s := by
    by_cases hh : ht g + 2 ≤ ht s
    · exact hh
    · have hvh : ht v + 1 = ht s := by omega
      have hut : ht u + 1 = ht g := by omega
      have hvGap := nf_mul_height_key_gap (a:=B) hnt
      rw [hvt] at hvGap
      have htv : ht t < ht v := by rcases hvGap with hp | hp <;> omega
      have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) hmid
      change origin e = some (w,v) at hoe
      obtain ⟨j,_,_,_,_,hvj,hjGap,_⟩ := nf_return_origin_trace heNF hoe hf houter
      change ht j + 2 ≤ ht e at hjGap
      have hov := mul_origin_of_right_height_le (a:=u) (b:=j) (by rw [hvj]; omega)
      rw [hvj] at hov
      have hov' := mul_origin_of_right_height_le (a:=B) (b:=t) (by rw [hvt]; omega)
      rw [hvt] at hov'
      have huB : u = B := (Prod.mk.inj (Option.some.inj (hov.symm.trans hov'))).1
      have hgNF : NF g := nf_mul hu ha
      have hBGap := nf_mul_height_key_gap (a:=A) hgNF
      change ht B = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht B + 2 ≤ ht g) at hBGap
      rw [←huB] at hBGap
      rcases hBGap with hp | hp <;> omega
  have hsGrow := mul_height_growth_of_right_le (a:=g) (b:=t) (by rw [hst]; omega)
  rw [hst] at hsGrow
  have hts : ht t + 1 = ht s := by omega
  have hvGap := nf_mul_height_key_gap (a:=B) hnt
  rw [hvt] at hvGap
  have hv2 : ht v + 2 ≤ ht t := by rcases hvGap with hh | hh <;> omega
  have hB3 : ht B + 3 ≤ ht t := by rcases hvGap with hh | hh <;> omega
  exact ⟨by change ht g < ht t; omega,hts,hrh,hv2,hB3,hw2,hD3⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondVLowLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_growing_middle_ladder {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    let B := mul (mul a w) g
    let D := mul a v
    ∃ r s t j, NF r ∧ NF s ∧ NF t ∧ NF j ∧
      mul w r = k ∧ mul v s = r ∧ mul D s = w ∧ mul g t = s ∧ mul B t = v ∧
      ht k = ht s + 2 ∧ ht r = ht s + 1 ∧ ht t + 1 = ht s ∧ ht g < ht t ∧
      ht v + 2 ≤ ht t ∧ ht B + 3 ≤ ht t ∧ ht w + 2 ≤ ht s ∧ ht D + 3 ≤ ht s ∧
      mul (mul D w) j = g ∧ mul w j = t ∧ ht j < ht t ∧
      ReturnLadder B (mul D w) w v g t j := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  let B := mul (mul a w) g
  let D := mul a v
  obtain ⟨r,s,t,hnr,hns,hnt,_,_,_,hkr,hws,hrs,hwr,_,_,_,hkh,hrc,hvt,hst,_,hvs⟩ :=
    normal_second_v_growing_middle_low_trace hu ha hk hf hvr hmid
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hnv : NF v := nf_mul ha hk
  have houter : ht u < ht (mul w v) := by
    by_cases hh : ht u < ht (mul w v)
    · exact hh
    · exact False.elim (normal_second_double_growth_impossible hu ha hk hf hmid
        (by change ht (mul w v) ≤ ht u; omega))
  obtain ⟨hgt,hts,hrsHeight,hv2,hB3,hw2,hD3⟩ := normal_low_growing_middle_column_height
    hu ha hnv hnw hnr hns hnt hf hws hrs hvt hst hrc hwr hvs hmid houter
  change mul D s = w at hws
  change mul g t = s at hst
  change mul B t = v at hvt
  change ht w + 2 ≤ ht s at hw2
  have hos := mul_origin_of_right_height_le (a:=g) (b:=t) (by rw [hst]; omega)
  rw [hst] at hos
  obtain ⟨j,_,hnj,_,hgj,htj,hjgap,_⟩ := nf_return_origin_trace hns hos hws (by omega)
  have hot := mul_origin_of_right_height_le (a:=w) (b:=j) (by rw [htj]; omega)
  rw [htj] at hot
  exact ⟨r,s,t,j,hnr,hns,hnt,hnj,hkr,hrs,hws,hst,hvt,by omega,hrsHeight,hts,hgt,
    hv2,hB3,hw2,hD3,hgj,htj,by omega,⟨hnt,htj,hot,hvt,hgj⟩⟩

end submission.Austin12087Trace

/- Checked module: TraceLowLadderMaxW -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_w_max_forces_fixed {a g v w t j : T}
    (hl : ReturnLadder (mul (mul a w) g) (mul (mul a v) w) w v g t j)
    (hvt : ht v < ht t) (hvw : ht v ≤ ht w) (hgw : ht g ≤ ht w) :
    ht (mul a w) < ht w ∧ mul a v = a ∧ mul (mul a v) w = mul a w := by
  let A := mul a w
  let B := mul A g
  let D := mul a v
  let C := mul D w
  change ReturnLadder B C w v g t j at hl
  have hAw : ht A < ht w := by
    by_cases hh : ht A < ht w
    · exact hh
    · have hA := mul_height_growth_of_right_le (a:=a) (b:=w) (by change ht w ≤ ht A; omega)
      change ht A = max (ht a) (ht w) + 1 at hA
      have hB := mul_height_growth_of_left_ge (a:=A) (b:=g) (by omega)
      change ht B = max (ht A) (ht g) + 1 at hB
      exact False.elim (return_ladder_dominant_impossible hl (by omega) (by omega) (by omega))
  obtain ⟨z,l,r,hwc⟩ := mul_return_of_height_lt (a:=a) (b:=w) hAw
  have hDa : D = a := by
    by_cases hh : D = a
    · exact hh
    · have hC := mul_height_off_return_key (a:=D) hwc hh
      change ht C = max (ht D) (ht w) + 1 at hC
      exact False.elim (return_ladder_second_dominant_impossible hl hvt (by omega) (by omega) (by omega))
  exact ⟨hAw,hDa,by change mul D w = mul a w; rw [hDa]⟩

end submission.Austin12087Trace

/- Checked module: TraceLowLadderTailStop -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_w_max_tail_stops {a g v w t j : T}
    (hnv : NF v)
    (hl : ReturnLadder (mul (mul a w) g) (mul (mul a v) w) w v g t j)
    (hvt : ht v < ht t) (hvw : ht v < ht w) (hgw : ht g ≤ ht w)
    (hBa : mul (mul a w) g ≠ a) : ht j ≤ ht w := by
  let A := mul a w
  let B := mul A g
  obtain ⟨hAw,hDa,_⟩ := normal_low_ladder_w_max_forces_fixed hl hvt (by omega) hgw
  rw [hDa] at hl
  change ReturnLadder B A w v g t j at hl
  change B ≠ a at hBa
  have haHeight := inverse_height_strict (inverse_complete a v)
  rw [hDa] at haHeight
  obtain ⟨z,l,r,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) (by rw [hDa]; omega)
  have hF := mul_height_off_return_key (a:=B) hvc hBa
  have hFa : mul B v ≠ a := by intro he; have hh := congrArg ht he; omega
  obtain ⟨zw,lw,rw,hwc⟩ := mul_return_of_height_lt (a:=a) (b:=w) hAw
  by_cases hjw : ht j ≤ ht w
  · exact hjw
  · have hwj : ht w < ht j := by omega
    obtain ⟨l,hl₁,_⟩ := return_ladder_step hl hvt hwj
    change ReturnLadder A (mul B v) v g w j l at hl₁
    have hjGrow := mul_height_growth_of_right_le (a:=v) (b:=l) (by
      rw [hl₁.2.1]; exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
    rw [hl₁.2.1] at hjGrow
    have hlh : ht l + 1 = ht j := by omega
    have hnl : NF l := (nf_origin hl₁.1 hl₁.2.2.1).2
    have hwGap := nf_mul_height_key_gap (a:=mul B v) hnl
    rw [hl₁.2.2.2.2] at hwGap
    have hwl : ht w < ht l := by rcases hwGap with hh | hh <;> omega
    obtain ⟨m,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
    change ReturnLadder (mul B v) B g w v l m at hl₂
    have hlGrow := mul_height_growth_of_right_le (a:=g) (b:=m) (by
      rw [hl₂.2.1]; exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
    rw [hl₂.2.1] at hlGrow
    have hw2 : ht w + 2 ≤ ht l := by rcases hwGap with hh | hh <;> omega
    have hmh : ht m + 1 = ht l := by omega
    obtain ⟨n,hl₃,_⟩ := return_ladder_step hl₂ hwl (by omega)
    change ReturnLadder B (mul (mul B v) w) w v g m n at hl₃
    have hC := mul_height_off_return_key (a:=mul B v) hwc hFa
    exact False.elim (return_ladder_second_dominant_impossible hl₃ (by omega)
      (by omega) (by omega) (by omega))

end submission.Austin12087Trace

/- Checked module: TraceSecondVLowWMax -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_v_growing_middle_w_max_height {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k)))
    (hvw : ht (mul a k) < ht (mul a (mul (mul u a) k)))
    (hgw : ht (mul u a) ≤ ht (mul a (mul (mul u a) k))) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    ht k = ht w + 4 ∧ mul a v = a ∧ mul (mul a w) g ≠ a := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  let B := mul (mul a w) g
  change ht k = ht w + 4 ∧ mul a v = a ∧ B ≠ a
  obtain ⟨r,s,t,j,_,_,hnt,_,_,_,hws,hst,hvt,hks,_,hts,_,hv2,_,_,_,_,_,_,hl⟩ :=
    normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
  change ht v < ht w at hvw
  change ht g ≤ ht w at hgw
  change ht v + 2 ≤ ht t at hv2
  change mul B t = v at hvt
  change ReturnLadder B (mul (mul a v) w) w v g t j at hl
  have hbounds := normal_second_query_k_dominates hu ha hk hf
  obtain ⟨_,hDa,_⟩ := normal_low_ladder_w_max_forces_fixed hl (by omega) (by omega) hgw
  have hBa : B ≠ a := by
    intro hB
    exact normal_second_v_low_equal_keys_descent_impossible hu ha hnt hs hbounds.1 hbounds.2
      (by omega) hf hws hvt hst hB hDa
  have hnv : NF v := nf_mul ha hk
  have hjw := normal_low_ladder_w_max_tail_stops hnv hl (by omega) hvw hgw hBa
  have htHeight := mul_height_growth_of_left_ge (a:=w) (b:=j) hjw
  rw [hl.2.1] at htHeight
  exact ⟨by omega,hDa,hBa⟩

end submission.Austin12087Trace

/- Checked module: TraceSemanticEdge -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

def actualLeft (b : T) : T := ((origin b).getD (atom 0, atom 0)).1
def actualRight (b : T) : T := ((origin b).getD (atom 0, atom 0)).2
def returnKey : T → T
  | c a _ _ _ _ => a
  | _ => atom 0
def returnValue : T → T
  | c _ x _ _ _ => x
  | _ => atom 0
def returnColumn : T → T
  | c _ _ z _ _ => z
  | _ => atom 0

def SemanticEdge (a b out : T) : Prop :=
  mul a b = out ∧ out ≠ b ∧ mul a out ≠ b ∧ mul b out ≠ a ∧
  ((ht out = max (ht a) (ht b) + 1 ∧ actualLeft out = a ∧ actualRight out = b) ∨
   (ht a + 3 ≤ ht b ∧ ht out + 2 ≤ ht b ∧ returnKey b = a ∧ returnValue b = out))

theorem semantic_edge {a b out : T} (hb : NF b) (hm : mul a b = out) :
    SemanticEdge a b out := by
  refine ⟨hm, ?_, ?_, ?_, ?_⟩
  · rw [← hm]; exact mul_ne_right a b
  · rw [← hm]; exact no_left_two_cycle a b
  · rw [← hm]; exact no_cross_two_cycle a b
  · rcases nf_mul_height_key_gap (a:=a) hb with hg | hr
    · have ho := mul_origin_of_right_height_le (a:=a) (b:=b) (by omega)
      rw [hm] at ho hg
      exact Or.inl ⟨hg, by simp only [actualLeft,ho,Option.getD_some],
        by simp only [actualRight,ho,Option.getD_some]⟩
    · obtain ⟨z,l,r,hc⟩ := mul_return_of_height_lt (a:=a) (b:=b) (by omega)
      rw [hm] at hc hr
      exact Or.inr ⟨hr.1,hr.2,by rw [hc]; rfl,by rw [hc]; rfl⟩

theorem semantic_return {a b out : T} (hb : NF b) (hm : mul a b = out)
    (hs : ht out < ht b) :
    NF a ∧ NF out ∧ NF (returnColumn b) ∧ NF (actualLeft b) ∧ NF (actualRight b) ∧
    mul (mul a out) (returnColumn b) = actualLeft b ∧
    mul out (returnColumn b) = actualRight b ∧
    ht (returnColumn b) + 2 ≤ ht b ∧
    ht b = max (ht (actualLeft b)) (ht (actualRight b)) + 1 := by
  obtain ⟨z,l,r,hc⟩ := mul_return_of_height_lt (a:=a) (b:=b) (by rw [hm]; exact hs)
  rw [hm] at hc
  have hn := nf_code_actual (hc ▸ hb)
  have hg := nf_code_height_gap (hc ▸ hb)
  have hh := common_column_height_bounds hn.2.2.2.2.2.2.1 hn.2.2.2.2.2.2.2
  rw [hc]
  simp only [returnColumn,actualLeft,actualRight,origin,Option.getD_some]
  refine ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,
    hn.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2,hg.2.2,?_⟩
  simp only [ht]; omega

end submission.Austin12087Trace

/- Checked module: TraceLowShortTailConflict -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_fixed_column_no_transpose {a v b : T}
    (hnv : NF v) (hav : mul a v = a) : mul b v ≠ mul v a := by
  have ha := inverse_height_strict (inverse_complete a v)
  rw [hav] at ha
  have havh : ht a < ht v := by omega
  have hvag := mul_height_growth_of_left_ge (a:=v) (b:=a) (by omega)
  have hova := mul_origin_of_right_height_le (a:=v) (b:=a) (by omega)
  intro he
  have hobv := mul_origin_of_right_height_le (a:=b) (b:=v) (by rw [he]; omega)
  rw [he,hova] at hobv
  have hp := Prod.mk.inj (Option.some.inj hobv)
  rw [hp.2] at havh
  omega

theorem normal_low_short_tail_conflict {u a v w j l n y : T}
    (hnv : NF v) (hnj : NF j) (hnl : NF l)
    (hav : mul a v = a)
    (hBa : mul (mul a w) (mul u a) ≠ a)
    (hyu : mul y u = mul (mul (mul a w) (mul u a)) v)
    (hul : mul u l = v) (hvl : mul v l = j)
    (hwl : mul (mul (mul (mul a w) (mul u a)) v) l = w)
    (hAn : mul (mul a w) n = l)
    (hHn : mul (mul a (mul a w)) n = mul (mul (mul a w) (mul u a)) v)
    (hAj : mul (mul a w) j = mul u a)
    (hnw : ht n + 2 ≤ ht w) (hlw : ht l < ht w) : False := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  let F := mul B v
  change B ≠ a at hBa
  change mul y u = F at hyu
  change mul F l = w at hwl
  change mul A n = l at hAn
  change mul (mul a A) n = F at hHn
  change mul A j = g at hAj
  have ha := inverse_height_strict (inverse_complete a v)
  rw [hav] at ha
  have havh : ht a < ht v := by omega
  obtain ⟨z,lv,rv,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) (by rw [hav]; omega)
  have hF := mul_height_off_return_key (a:=B) hvc hBa
  change ht F = max (ht B) (ht v) + 1 at hF
  have hoF := mul_origin_of_right_height_le (a:=B) (b:=v) (by change ht v ≤ ht F; omega)
  change origin F = some (B,v) at hoF
  have huv : u ≠ v := by
    intro he
    have hjv : j = v := by rw [← he] at hvl; exact hvl.symm.trans hul
    have hb : mul A v = mul v a := by simpa only [g,hjv,he] using hAj
    exact normal_fixed_column_no_transpose hnv hav hb
  have hFu : ht F < ht u := by
    by_cases hh : ht F < ht u
    · exact hh
    · have hou := mul_origin_of_right_height_le (a:=y) (b:=u) (by rw [hyu]; omega)
      rw [hyu,hoF] at hou
      have hp := Prod.mk.inj (Option.some.inj hou)
      exact False.elim (huv hp.2.symm)
  have hulGap := nf_mul_height_key_gap (a:=u) hnl
  rw [hul] at hulGap
  have hulh : ht u + 3 ≤ ht l := by rcases hulGap with hh | hh <;> omega
  have hwHeight := mul_height_growth_of_right_le (a:=F) (b:=l) (by rw [hwl]; omega)
  rw [hwl] at hwHeight
  have hwlh : ht w = ht l + 1 := by omega
  obtain ⟨zl,ll,rl,hlc⟩ := mul_return_of_height_lt (a:=u) (b:=l) (by rw [hul]; omega)
  have hjHeight := mul_height_off_return_key (a:=v) hlc (Ne.symm huv)
  rw [hvl] at hjHeight
  have hjlh : ht j = ht l + 1 := by omega
  have hoj := mul_origin_of_right_height_le (a:=v) (b:=l) (by rw [hvl]; omega)
  rw [hvl] at hoj
  have hgHeight := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
  change ht g = max (ht u) (ht a) + 1 at hgHeight
  obtain ⟨m,_,_,_,hBm,hgm,hmGap,_⟩ := nf_return_origin_trace hnj hoj hAj (by omega)
  change mul B m = v at hBm
  have hol := mul_origin_of_right_height_le (a:=A) (b:=n) (by rw [hAn]; omega)
  rw [hAn] at hol
  have hol' := mul_origin_of_right_height_le (a:=g) (b:=m) (by rw [hgm]; omega)
  rw [hgm] at hol'
  have hp := Prod.mk.inj (Option.some.inj (hol.symm.trans hol'))
  have hlHeight := mul_height_growth_of_right_le (a:=g) (b:=m) (by rw [hgm]; omega)
  rw [hgm] at hlHeight
  have hnm : n = m := hp.2
  have hnmHeight := congrArg ht hnm
  have hBn : mul B n = v := by rw [hnm]; exact hBm
  have hnF := (distinct_outputs_height_origin hHn hBn (by intro he; have hh := congrArg ht he; omega)
    (by omega)).2
  omega

end submission.Austin12087Trace

/- Checked module: TraceSecondVWMaxClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_w_max_impossible {u a v w t j y : T}
    (hnv : NF v) (hnw : NF w)
    (hl : ReturnLadder (mul (mul a w) (mul u a)) (mul (mul a v) w) w v (mul u a) t j)
    (hf : mul y (mul w v) = u)
    (hvt : ht v < ht t) (hvw : ht v < ht w) (hgw : ht (mul u a) ≤ ht w)
    (hBa : mul (mul a w) (mul u a) ≠ a) : False := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  let F := mul B v
  obtain ⟨hAw,hav,_⟩ := normal_low_ladder_w_max_forces_fixed hl hvt (by omega) hgw
  have hjw := normal_low_ladder_w_max_tail_stops hnv hl hvt hvw hgw hBa
  rw [hav] at hl
  change ReturnLadder B A w v g t j at hl
  have htHeight := mul_height_growth_of_left_ge (a:=w) (b:=j) hjw
  rw [hl.2.1] at htHeight
  obtain ⟨l,_,hnl,hnj,hFl,hvl,hlGap,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hvt
  change mul F l = w at hFl
  have how := mul_origin_of_right_height_le (a:=F) (b:=l) (by rw [hFl]; omega)
  rw [hFl] at how
  obtain ⟨n,_,_,_,hHn,hAn,hnGap,_⟩ := nf_return_origin_trace hnw how (show mul a w = A from rfl) hAw
  have hne := nf_mul hnw hnv
  have heHeight := mul_height_growth_of_left_ge (a:=w) (b:=v) (by omega)
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) (by omega)
  have ha := inverse_height_strict (inverse_complete a v)
  rw [hav] at ha
  have hu := inverse_height_strict (inverse_complete u a)
  have houter : ht u < ht (mul w v) := by omega
  obtain ⟨z,_,_,_,hYz,huz,hzGap,_⟩ := nf_return_origin_trace hne hoe hf houter
  have how' := mul_origin_of_right_height_le (a:=mul y u) (b:=z) (by rw [hYz]; omega)
  rw [hYz] at how'
  have hp := Prod.mk.inj (Option.some.inj (how.symm.trans how'))
  have hyu : mul y u = F := hp.1.symm
  have hul : mul u l = v := by rw [hp.2]; exact huz
  exact normal_low_short_tail_conflict hnv hnj hnl hav hBa hyu hul hvl hFl hAn hHn
    hl.2.2.2.2 hnGap (by omega)

theorem normal_second_v_growing_middle_w_max_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k)))
    (hvw : ht (mul a k) < ht (mul a (mul (mul u a) k)))
    (hgw : ht (mul u a) ≤ ht (mul a (mul (mul u a) k))) : False := by
  have hBa := (normal_second_v_growing_middle_w_max_height hu ha hk hs hf hvr hmid hvw hgw).2.2
  obtain ⟨r,s,t,j,_,_,_,_,_,_,_,_,_,_,_,_,_,hv2,_,_,_,_,_,_,hl⟩ :=
    normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
  have hnv := nf_mul ha hk
  have hnw := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  exact normal_low_ladder_w_max_impossible hnv hnw hl hf (by omega) hvw hgw hBa

end submission.Austin12087Trace

/- Checked module: TraceSecondVWMaxBoundary -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_equal_max_impossible {a g v w t j : T}
    (hnv : NF v)
    (hl : ReturnLadder (mul (mul a w) g) (mul (mul a v) w) w v g t j)
    (hvt : ht v < ht t) (hvw : ht v = ht w) (hgw : ht g ≤ ht w)
    (hBa : mul (mul a w) g ≠ a) : False := by
  let A := mul a w
  let B := mul A g
  let F := mul B v
  obtain ⟨_,hav,_⟩ := normal_low_ladder_w_max_forces_fixed hl hvt (by omega) hgw
  rw [hav] at hl
  change ReturnLadder B A w v g t j at hl
  have ha := inverse_height_strict (inverse_complete a v)
  rw [hav] at ha
  obtain ⟨z,lv,rv,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) (by rw [hav]; omega)
  have hF := mul_height_off_return_key (a:=B) hvc hBa
  change ht F = max (ht B) (ht v) + 1 at hF
  obtain ⟨l,_,_,_,hFl,_,hlGap,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hvt
  change mul F l = w at hFl
  have hFlHeight := inverse_height_strict (inverse_complete F l)
  rw [hFl] at hFlHeight
  have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  obtain ⟨m,hl',_⟩ := return_ladder_step hl hvt (by omega)
  change ReturnLadder A F v g w j m at hl'
  exact return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega)

theorem normal_second_v_growing_middle_w_dominant_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k)))
    (hvw : ht (mul a k) ≤ ht (mul a (mul (mul u a) k)))
    (hgw : ht (mul u a) ≤ ht (mul a (mul (mul u a) k))) : False := by
  by_cases hvw' : ht (mul a k) < ht (mul a (mul (mul u a) k))
  · exact normal_second_v_growing_middle_w_max_impossible hu ha hk hs hf hvr hmid hvw' hgw
  · obtain ⟨r,s,t,j,_,_,hnt,_,_,_,hws,hst,hvt,_,_,hts,_,hv2,_,_,_,_,_,_,hl⟩ :=
      normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
    have hnv := nf_mul ha hk
    obtain ⟨_,hDa,_⟩ := normal_low_ladder_w_max_forces_fixed hl (by omega) hvw hgw
    have hbounds := normal_second_query_k_dominates hu ha hk hf
    have hBa : mul (mul a (mul a (mul (mul u a) k))) (mul u a) ≠ a := by
      intro hB
      exact normal_second_v_low_equal_keys_descent_impossible hu ha hnt hs hbounds.1 hbounds.2
        (by omega) hf hws hvt hst hB hDa
    exact normal_low_ladder_equal_max_impossible hnv hl (by omega) (by omega) hgw hBa

end submission.Austin12087Trace

/- Checked module: TraceSecondVGMaxClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_g_strict_max_impossible {u a v w t j y : T}
    (hne : NF (mul w v))
    (hl : ReturnLadder (mul (mul a w) (mul u a)) (mul (mul a v) w) w v (mul u a) t j)
    (hf : mul y (mul w v) = u) (houter : ht u < ht (mul w v))
    (hwg : ht w < ht (mul u a)) (hvg : ht v < ht (mul u a)) : False := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  change ht w < ht g at hwg
  change ht v < ht g at hvg
  change ReturnLadder B (mul (mul a v) w) w v g t j at hl
  have huGap := nf_mul_height_key_gap (a:=y) hne
  rw [hf] at huGap
  have heUpper := mul_height_upper w v
  have hu2 : ht u + 2 ≤ ht (mul w v) := by rcases huGap with hh | hh <;> omega
  have hgUpper := mul_height_upper u a
  change ht g ≤ max (ht u) (ht a) + 1 at hgUpper
  have haw : ht w ≤ ht a := by omega
  have hAg := mul_height_growth_of_left_ge (a:=a) (b:=w) haw
  change ht A = max (ht a) (ht w) + 1 at hAg
  have hBg := mul_height_growth_of_left_ge (a:=A) (b:=g) (by change ht g ≤ ht A; omega)
  change ht B = max (ht A) (ht g) + 1 at hBg
  exact return_ladder_dominant_impossible hl (by omega) (by omega) (by omega)

theorem normal_second_v_growing_middle_frontier {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) :
    ht (mul a (mul (mul u a) k)) < ht (mul a k) ∧ ht (mul u a) ≤ ht (mul a k) := by
  let g := mul u a
  let v := mul a k
  let w := mul a (mul g k)
  change ht w < ht v ∧ ht g ≤ ht v
  have hnv : NF v := nf_mul ha hk
  have hnw : NF w := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have houter : ht u < ht (mul w v) := by
    by_cases hh : ht u < ht (mul w v)
    · exact hh
    · exact False.elim (normal_second_double_growth_impossible hu ha hk hf hmid
        (by change ht (mul w v) ≤ ht u; omega))
  obtain ⟨r,s,t,j,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hl⟩ :=
    normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
  have hnotg : ¬ (ht w < ht g ∧ ht v < ht g) := by
    intro hh
    exact normal_low_ladder_g_strict_max_impossible (nf_mul hnw hnv) hl hf houter hh.1 hh.2
  have hnotw : ¬ (ht v ≤ ht w ∧ ht g ≤ ht w) := by
    intro hh
    exact normal_second_v_growing_middle_w_dominant_impossible hu ha hk hs hf hvr hmid hh.1 hh.2
  constructor <;> omega

end submission.Austin12087Trace

/- Checked module: TraceSecondVVMaxKeys -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_ladder_v_max_keys {a g v w t j : T}
    (hnv : NF v)
    (hl : ReturnLadder (mul (mul a w) g) (mul (mul a v) w) w v g t j)
    (hvt : ht v < ht t) (hwv : ht w < ht v) (hgv : ht g ≤ ht v) :
    mul (mul a w) g = a ∧ ht (mul a v) < ht v := by
  let B := mul (mul a w) g
  let D := mul a v
  let C := mul D w
  change ReturnLadder B C w v g t j at hl
  change B = a ∧ ht D < ht v
  have hCv : ht C < ht v := by
    by_cases hh : ht C < ht v
    · exact hh
    · exact False.elim (return_ladder_second_dominant_impossible hl hvt (by omega) (by omega) (by omega))
  have hD := inverse_height_strict (inverse_complete D w)
  change ht D < max (ht w) (ht C) at hD
  have hDv : ht D < ht v := by omega
  obtain ⟨z,l,r,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) hDv
  have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  have hnj := (nf_origin hl.1 hl.2.2.1).2
  have hgGap := nf_mul_height_key_gap (a:=C) hnj
  rw [hl.2.2.2.2] at hgGap
  have hgj : ht g < ht j := by rcases hgGap with hh | hh <;> omega
  have hBa : B = a := by
    by_cases hh : B = a
    · exact hh
    · have hF := mul_height_off_return_key (a:=B) hvc hh
      obtain ⟨m,hl',_⟩ := return_ladder_step hl hvt (by omega)
      exact False.elim (return_ladder_second_dominant_impossible hl' hgj (by omega) (by omega) (by omega))
  exact ⟨hBa,hDv⟩

theorem normal_second_v_growing_middle_key_frontier {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    mul (mul a w) g = a ∧ mul a v ≠ a ∧ ht (mul a v) < ht v := by
  obtain ⟨hwv,hgv⟩ := normal_second_v_growing_middle_frontier hu ha hk hs hf hvr hmid
  obtain ⟨r,s,t,j,_,_,hnt,_,_,_,hws,hst,hvt,_,_,_,_,hv2,_,_,_,_,_,_,hl⟩ :=
    normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
  obtain ⟨hBa,hDv⟩ := normal_low_ladder_v_max_keys (nf_mul ha hk) hl (by omega) hwv hgv
  have hbounds := normal_second_query_k_dominates hu ha hk hf
  refine ⟨hBa,?_,hDv⟩
  intro hDa
  exact normal_second_v_low_equal_keys_descent_impossible hu ha hnt hs hbounds.1 hbounds.2
    (by omega) hf hws hvt hst hBa hDa

end submission.Austin12087Trace

/- Checked module: TraceVHeadKeyRigidity -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_ladder_first_key_of_highest_return {a d z lv rv b c w v g t j : T}
    (hvc : v = T.c a d z lv rv) (hl : ReturnLadder b c w v g t j)
    (hvt : ht v < ht t) (hwv : ht w < ht v) (hgv : ht g ≤ ht v) : b = a := by
  have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  have hnj := (nf_origin hl.1 hl.2.2.1).2
  have hgGap := nf_mul_height_key_gap (a:=c) hnj
  rw [hl.2.2.2.2] at hgGap
  have hgj : ht g < ht j := by rcases hgGap with hh | hh <;> omega
  by_cases he : b = a
  · exact he
  · have hF := mul_height_off_return_key (a:=b) hvc he
    obtain ⟨m,hl',_⟩ := return_ladder_step hl hvt (by omega)
    exact False.elim (return_ladder_second_dominant_impossible hl' hgj (by omega) (by omega) (by omega))

theorem normal_changed_key_growth {u a w d : T} (ha : NF a)
    (hB : mul (mul a w) (mul u a) = a) (hda : d ≠ a) :
    let g := mul u a
    let C := mul d w
    ht (mul C g) = max (ht C) (ht g) + 1 ∧
    ht u < ht (mul C g) ∧ ht a < ht (mul C g) := by
  let g := mul u a
  let A := mul a w
  let C := mul d w
  change mul A g = a at hB
  change ht (mul C g) = max (ht C) (ht g) + 1 ∧ ht u < ht (mul C g) ∧ ht a < ht (mul C g)
  have hCA : C ≠ A := by
    intro he
    exact hda (right_injective d a w he)
  by_cases hag : ht a < ht g
  · obtain ⟨z,l,r,hgc⟩ := mul_return_of_height_lt (a:=A) (b:=g) (by rw [hB]; exact hag)
    have hK := mul_height_off_return_key (a:=C) hgc hCA
    have hu := inverse_height_strict (inverse_complete u a)
    change ht u < max (ht a) (ht g) at hu
    exact ⟨hK,by omega,by omega⟩
  · have hgGap := nf_mul_height_key_gap (a:=u) ha
    change ht g = max (ht u) (ht a) + 1 ∨ (ht u + 3 ≤ ht a ∧ ht g + 2 ≤ ht a) at hgGap
    have hug : ht u + 3 ≤ ht a ∧ ht g + 2 ≤ ht a := by rcases hgGap with hh | hh <;> omega
    have hA := inverse_height_strict (inverse_complete A g)
    rw [hB] at hA
    have hAw : ht A < ht w := by
      have ha' := inverse_height_strict (inverse_complete a w)
      change ht a < max (ht w) (ht A) at ha'
      omega
    obtain ⟨z,l,r,hwc⟩ := mul_return_of_height_lt (a:=a) (b:=w) hAw
    have hC := mul_height_off_return_key (a:=d) hwc hda
    change ht C = max (ht d) (ht w) + 1 at hC
    have hw := inverse_height_strict (inverse_complete a w)
    change ht a < max (ht w) (ht A) at hw
    have hK := mul_height_growth_of_left_ge (a:=C) (b:=g) (by omega)
    exact ⟨hK,by omega,by omega⟩

end submission.Austin12087Trace

/- Checked module: TraceSecondVGrowingClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_v_head_cycle_impossible {u a v w t j y : T}
    (ha : NF a) (hnv : NF v) (hnw : NF w)
    (hl : ReturnLadder (mul (mul a w) (mul u a)) (mul (mul a v) w) w v (mul u a) t j)
    (hf : mul y (mul w v) = u) (houter : ht u < ht (mul w v))
    (hmid : ht v ≤ ht (mul w v))
    (hvt : ht v < ht t) (hwv : ht w < ht v) (hgv : ht (mul u a) ≤ ht v)
    (hB : mul (mul a w) (mul u a) = a) (hDa : mul a v ≠ a)
    (hDv : ht (mul a v) < ht v) : False := by
  let g := mul u a
  let D := mul a v
  let C := mul D w
  let K := mul C g
  have hK := normal_changed_key_growth ha hB hDa
  change ht K = max (ht C) (ht g) + 1 ∧ ht u < ht K ∧ ht a < ht K at hK
  change ht g ≤ ht v at hgv
  change ht D < ht v at hDv
  rw [hB] at hl
  change ReturnLadder a C w v g t j at hl
  obtain ⟨zv,lv,rv,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) hDv
  have heHeight := mul_height_growth_of_right_le (a:=w) (b:=v) hmid
  have hoe := mul_origin_of_right_height_le (a:=w) (b:=v) hmid
  obtain ⟨z,_,_,_,_,huz,hzGap,_⟩ := nf_return_origin_trace (nf_mul hnw hnv) hoe hf houter
  have hov := mul_origin_of_right_height_le (a:=u) (b:=z) (by rw [huz]; omega)
  rw [huz] at hov
  have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  obtain ⟨l,_,hnl,hnj,hDl,hvl,hlGap,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hvt
  change mul D l = w at hDl
  have hoj := mul_origin_of_right_height_le (a:=v) (b:=l) (by rw [hvl]; omega)
  rw [hvl] at hoj
  have hgGap := nf_mul_height_key_gap (a:=C) hnj
  rw [hl.2.2.2.2] at hgGap
  have hgj : ht g < ht j := by rcases hgGap with hh | hh <;> omega
  obtain ⟨m,_,_,_,hKm,hgm,hmGap,_⟩ := nf_return_origin_trace hnj hoj hl.2.2.2.2 hgj
  change mul K m = v at hKm
  have hvm : ht v < ht m := by
    rcases mul_height_shape K m with hg | ⟨x,z',l',r',hm,ho⟩
    · rw [hKm,hov] at hg
      have hp := Prod.mk.inj (Option.some.inj hg.2.2)
      have hh := congrArg ht hp.1
      omega
    · have hx : x = v := ho.symm.trans hKm
      rw [hx] at hm
      rw [hm]; simp only [ht]; omega
  have hjHeight := mul_height_growth_of_right_le (a:=v) (b:=l) (by rw [hvl]; omega)
  rw [hvl] at hjHeight
  have hol := mul_origin_of_right_height_le (a:=g) (b:=m) (by rw [hgm]; omega)
  rw [hgm] at hol
  have hl₂ : ReturnLadder D K g w v l m := ⟨hnl,hgm,hol,hDl,hKm⟩
  obtain ⟨n,hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
  change ReturnLadder K C w v g m n at hl₃
  have hKa := normal_ladder_first_key_of_highest_return hvc hl₃ hvm hwv hgv
  have hh := congrArg ht hKa
  omega

theorem normal_second_v_growing_middle_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (hmid : ht (mul a k) ≤ ht (mul (mul a (mul (mul u a) k)) (mul a k))) : False := by
  obtain ⟨hwv,hgv⟩ := normal_second_v_growing_middle_frontier hu ha hk hs hf hvr hmid
  obtain ⟨hBa,hDa,hDv⟩ := normal_second_v_growing_middle_key_frontier hu ha hk hs hf hvr hmid
  obtain ⟨r,s,t,j,_,_,_,_,_,_,_,_,_,_,_,_,_,hv2,_,_,_,_,_,_,hl⟩ :=
    normal_second_v_growing_middle_ladder hu ha hk hf hvr hmid
  have hnw := nf_mul ha (nf_mul (nf_mul hu ha) hk)
  have hnv := nf_mul ha hk
  have houter : ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k)) := by
    by_cases hh : ht u < ht (mul (mul a (mul (mul u a) k)) (mul a k))
    · exact hh
    · exact False.elim (normal_second_double_growth_impossible hu ha hk hf hmid (by omega))
  exact normal_v_head_cycle_impossible ha hnv hnw hl hf houter hmid (by omega) hwv hgv hBa hDa hDv

end submission.Austin12087Trace

/- Checked module: TraceReturningMiddleFrontier -/
set_option autoImplicit false

namespace submission.Austin12087Trace

theorem normal_second_induction_requires_two_returns {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    ht (mul a k) < ht k ∧
    ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k) := by
  have hvr := (normal_second_induction_requires_returning_v hu ha hk hs hf).1
  refine ⟨hvr,?_⟩
  by_cases hh : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k)
  · exact hh
  · exact False.elim (normal_second_v_growing_middle_impossible hu ha hk hs hf hvr (by omega))

def NormalReturningMiddleStep : Prop := ∀ u a k y : T, NF u → NF a → NF k →
  NormalSecondBelow (ht k) →
  mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u →
  ht (mul a k) < ht k →
  ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k) → False

theorem normal_returning_v_of_returning_middle (hm : NormalReturningMiddleStep) :
    NormalReturningVStep := by
  intro u a k y hu ha hk hs hf hvr
  have hr := (normal_second_induction_requires_two_returns hu ha hk hs hf).2
  exact hm u a k y hu ha hk hs hf hvr hr

theorem normal_law_of_returning_middle_step (hm : NormalReturningMiddleStep) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) :=
  normal_law_of_returning_v_step (normal_returning_v_of_returning_middle hm)

end submission.Austin12087Trace

/- Checked module: TraceDoubleReturnOffKey -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_double_return_offkey_geometry {u a v w r s y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v)
    (hl : ReturnLadder (mul a w) (mul a v) v (mul u a) w r s)
    (hgr : ht (mul u a) < ht r)
    (hf : mul y (mul w v) = u) (he : ht (mul w v) < ht v) (haw : a ≠ w) :
    let g := mul u a
    let A := mul a w
    let B := mul A g
    let D := mul a v
    ht v < ht D ∧ ht D < ht g ∧ ht (mul w v) < ht u ∧
    ht B < ht g ∧ mul A B = y ∧ mul B (mul w v) = a := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  let D := mul a v
  let e := mul w v
  change ReturnLadder A D v g w r s at hl
  change ht g < ht r at hgr
  change mul y e = u at hf
  change ht e < ht v at he
  change ht v < ht D ∧ ht D < ht g ∧ ht e < ht u ∧ ht B < ht g ∧ mul A B = y ∧ mul B e = a
  have heGap := nf_mul_height_key_gap (a:=w) hnv
  change ht e = max (ht w) (ht v) + 1 ∨ (ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at heGap
  have hew : ht w + 3 ≤ ht v ∧ ht e + 2 ≤ ht v := by rcases heGap with hh | hh <;> omega
  obtain ⟨z,l,b,hvc⟩ := mul_return_of_height_lt (a:=w) (b:=v) he
  have hD := mul_height_off_return_key (a:=a) hvc haw
  change ht D = max (ht a) (ht v) + 1 at hD
  have hDg : ht D < ht g := by
    by_cases hh : ht D < ht g
    · exact hh
    · exact False.elim (return_ladder_second_dominant_impossible hl hgr (by omega) (by omega) (by omega))
  have hng : NF g := nf_mul hu ha
  have hg := mul_height_growth_of_right_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change ht g = max (ht u) (ht a) + 1 at hg
  have hug : ht g = ht u + 1 := by omega
  have heu : ht e < ht u := by omega
  have hou := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; omega)
  rw [hf] at hou
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change origin g = some (u,a) at hog
  have hBg : ht B < ht g := by
    by_cases hh : ht B < ht g
    · exact hh
    · have hB := mul_height_growth_of_right_le (a:=A) (b:=g) (by change ht g ≤ ht B; omega)
      exact False.elim (factored_growing_key_ladder_impossible hl hgr (show mul w v = e from rfl)
        haw hB (by omega) (by omega))
  obtain ⟨m,_,_,_,hABm,hBm,hmGap,_⟩ := nf_return_origin_trace hng hog (show mul A g = B from rfl) hBg
  have hou' := mul_origin_of_right_height_le (a:=mul A B) (b:=m) (by rw [hABm]; omega)
  rw [hABm,hou] at hou'
  have hp := Prod.mk.inj (Option.some.inj hou')
  have hAB : mul A B = y := hp.1.symm
  have hme : m = e := hp.2.symm
  have hBe : mul B e = a := by rw [← hme]; exact hBm
  exact ⟨by omega,hDg,heu,hBg,hAB,hBe⟩

theorem normal_second_two_return_offkey_trace {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (he : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k))
    (haw : a ≠ mul a (mul (mul u a) k)) :
    let g := mul u a
    let v := mul a k
    let w := mul a (mul g k)
    let A := mul a w
    let B := mul A g
    let D := mul a v
    ht v < ht D ∧ ht D < ht g ∧ ht (mul w v) < ht u ∧
    ht B < ht g ∧ mul A B = y ∧ mul B (mul w v) = a := by
  obtain ⟨r,s,hnr,_,_,_,hAr,_,hDs,hvs,_,_,_,hgr,_,t,_,hrc,_,_,_⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a (mul a (mul (mul u a) k))) (mul a (mul a k))
      (mul a k) (mul u a) (mul a (mul (mul u a) k)) r s := ⟨hnr,hvs,hor,hAr,hDs⟩
  exact normal_double_return_offkey_geometry hu ha (nf_mul ha hk) hl hgr hf he haw

end submission.Austin12087Trace

/- Checked module: TraceDoubleReturnOffKeyClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_double_return_offkey_impossible {u a v w r s y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v) (hnw : NF w)
    (hl : ReturnLadder (mul a w) (mul a v) v (mul u a) w r s)
    (hgr : ht (mul u a) < ht r)
    (hf : mul y (mul w v) = u) (he : ht (mul w v) < ht v) (haw : a ≠ w) : False := by
  let g := mul u a
  let A := mul a w
  let B := mul A g
  let D := mul a v
  let C := mul D w
  let e := mul w v
  obtain ⟨hvD,hDg,heu,hBg,hAB,hBe⟩ := normal_double_return_offkey_geometry hu ha hnv hl hgr hf he haw
  change ht v < ht D at hvD
  change ht D < ht g at hDg
  change ht e < ht u at heu
  change ht B < ht g at hBg
  change mul A B = y at hAB
  change mul B e = a at hBe
  change ReturnLadder A D v g w r s at hl
  change ht g < ht r at hgr
  change mul y e = u at hf
  change ht e < ht v at he
  obtain ⟨ze,le,re,hvc⟩ := mul_return_of_height_lt (a:=w) (b:=v) he
  have hwv := inverse_height_strict (inverse_complete w v)
  change ht w < max (ht v) (ht e) at hwv
  have hD := mul_height_off_return_key (a:=a) hvc haw
  change ht D = max (ht a) (ht v) + 1 at hD
  have hCA : C ≠ A := by
    intro hh
    have hd : D = a := right_injective D a w hh
    have hd' := congrArg ht hd
    omega
  have hng : NF g := nf_mul hu ha
  obtain ⟨zg,lg,rg,hgc⟩ := mul_return_of_height_lt (a:=A) (b:=g) hBg
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change origin g = some (u,a) at hog
  have hrHeight := mul_height_growth_of_right_le (a:=v) (b:=s) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at hrHeight
  have hgGap := nf_mul_height_key_gap (a:=A) hl.1
  rw [hl.2.2.2.1] at hgGap
  have hgs : ht g < ht s := by rcases hgGap with hh | hh <;> omega
  obtain ⟨t,hl₁,_⟩ := return_ladder_step hl hgr (by omega)
  change ReturnLadder D B g w v s t at hl₁
  have htg : ht t ≤ ht g := by
    by_cases hh : ht t ≤ ht g
    · exact hh
    · obtain ⟨j,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      change ReturnLadder B C w v g t j at hl₂
      have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
        rw [hl₂.2.1]; exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at htHeight
      have hnj := (nf_origin hl₂.1 hl₂.2.2.1).2
      have hjGap := nf_mul_height_key_gap (a:=C) hnj
      rw [hl₂.2.2.2.2] at hjGap
      have hgj : ht g < ht j := by rcases hjGap with hj | hj <;> omega
      obtain ⟨l,hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      have hkey := normal_ladder_first_key_of_highest_return hgc hl₃ hgj (by omega) (by omega)
      exact False.elim (hCA hkey)
  have hsHeight := mul_height_growth_of_left_ge (a:=g) (b:=t) htg
  rw [hl₁.2.1] at hsHeight
  obtain ⟨j,_,_,_,hCj,_,hjGap,_⟩ := nf_return_origin_trace hl₁.1 hl₁.2.2.1 hl₁.2.2.2.1 (by omega)
  change mul C j = g at hCj
  have hog' := mul_origin_of_right_height_le (a:=C) (b:=j) (by rw [hCj]; omega)
  rw [hCj,hog] at hog'
  have hCu : C = u := (Prod.mk.inj (Option.some.inj hog')).1.symm
  have hC := mul_height_growth_of_left_ge (a:=D) (b:=w) (by omega)
  change ht C = max (ht D) (ht w) + 1 at hC
  have hoC := mul_origin_of_right_height_le (a:=D) (b:=w) (by change ht w ≤ ht C; omega)
  change origin C = some (D,w) at hoC
  have hou := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; omega)
  rw [hf,← hCu,hoC] at hou
  have hp := Prod.mk.inj (Option.some.inj hou)
  have hDy : D = y := hp.1
  have hwe : w = e := hp.2
  have hCuHeight := congrArg ht hCu
  have hgHeight := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
  change ht g = max (ht u) (ht a) + 1 at hgHeight
  have hBGap := nf_mul_height_key_gap (a:=A) hng
  change ht B = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht B + 2 ≤ ht g) at hBGap
  have hB2 : ht B + 2 ≤ ht g := by rcases hBGap with hh | hh <;> omega
  have hABD : mul A B = D := hAB.trans hDy.symm
  have hoD := mul_origin_of_right_height_le (a:=a) (b:=v) (by change ht v ≤ ht D; omega)
  change origin D = some (a,v) at hoD
  have hoD' := mul_origin_of_right_height_le (a:=A) (b:=B) (by rw [hABD]; omega)
  rw [hABD,hoD] at hoD'
  have hp' := Prod.mk.inj (Option.some.inj hoD')
  have hAa : A = a := hp'.1.symm
  have hBv : B = v := hp'.2.symm
  have havw : mul a w = a := hAa
  have hvw : mul v w = a := by rw [← hBv,hwe]; exact hBe
  have hva : v = a := right_injective v a w (hvw.trans havw.symm)
  have hwafix : mul w a = w := by rw [← hva]; exact hwe.symm
  exact normal_fixed_rotation_impossible ha hnw havw (by rw [hwafix,havw])

theorem normal_second_two_return_offkey_impossible {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (he : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k))
    (haw : a ≠ mul a (mul (mul u a) k)) : False := by
  obtain ⟨r,s,hnr,_,_,_,hAr,_,hDs,hvs,_,_,_,hgr,_,t,_,hrc,_,_,_⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a (mul a (mul (mul u a) k))) (mul a (mul a k))
      (mul a k) (mul u a) (mul a (mul (mul u a) k)) r s := ⟨hnr,hvs,hor,hAr,hDs⟩
  exact normal_double_return_offkey_impossible hu ha (nf_mul ha hk)
    (nf_mul ha (nf_mul (nf_mul hu ha) hk)) hl hgr hf he haw

end submission.Austin12087Trace

/- Checked module: TraceSameKeyMiddleFrontier -/
set_option autoImplicit false

namespace submission.Austin12087Trace

theorem normal_second_induction_requires_equal_return_keys {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    a = mul a (mul (mul u a) k) := by
  obtain ⟨hvr,he⟩ := normal_second_induction_requires_two_returns hu ha hk hs hf
  by_cases hh : a = mul a (mul (mul u a) k)
  · exact hh
  · exact False.elim (normal_second_two_return_offkey_impossible hu ha hk hf hvr he hh)

def NormalSameKeyMiddleStep : Prop := ∀ u a k y : T, NF u → NF a → NF k →
  NormalSecondBelow (ht k) →
  mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u →
  ht (mul a k) < ht k →
  ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k) →
  a = mul a (mul (mul u a) k) → False

theorem normal_returning_middle_of_same_key (hm : NormalSameKeyMiddleStep) :
    NormalReturningMiddleStep := by
  intro u a k y hu ha hk hs hf hvr he
  exact hm u a k y hu ha hk hs hf hvr he
    (normal_second_induction_requires_equal_return_keys hu ha hk hs hf)

theorem normal_law_of_same_key_middle_step (hm : NormalSameKeyMiddleStep) :
    ∀ x y z : NormalTree,
      x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) :=
  normal_law_of_returning_middle_step (normal_returning_middle_of_same_key hm)

end submission.Austin12087Trace

/- Checked module: TraceSameKeyAlignedColumns -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_swapped_returns_top_column_impossible {a e g B v s t : T}
    (hnv : NF v) (hns : NF s) (hvt : mul B t = v) (hst : mul g t = s)
    (hav : mul a v = e) (hes : mul e s = a) (he : ht e < ht v)
    (hv : ht v = ht t + 1) (hs : ht s = ht t + 1) (hBg : B ≠ g) : False := by
  have havGap := nf_mul_height_key_gap (a:=a) hnv
  rw [hav] at havGap
  have ha3 : ht a + 3 ≤ ht v := by rcases havGap with hh | hh <;> omega
  have hov := mul_origin_of_right_height_le (a:=B) (b:=t) (by rw [hvt]; omega)
  rw [hvt] at hov
  have hos := mul_origin_of_right_height_le (a:=g) (b:=t) (by rw [hst]; omega)
  rw [hst] at hos
  obtain ⟨j,_,_,_,hBj,htj,hjGap,_⟩ := nf_return_origin_trace hnv hov hav he
  obtain ⟨l,_,_,_,hgl,htl,hlGap,_⟩ := nf_return_origin_trace hns hos hes (by omega)
  have hot := mul_origin_of_right_height_le (a:=e) (b:=j) (by rw [htj]; omega)
  rw [htj] at hot
  have hot' := mul_origin_of_right_height_le (a:=a) (b:=l) (by rw [htl]; omega)
  rw [htl] at hot'
  have hp := Prod.mk.inj (Option.some.inj (hot.symm.trans hot'))
  rw [hp.1,hp.2] at hBj
  rw [hp.1] at hgl
  exact hBg (hBj.symm.trans hgl)

theorem normal_same_key_equal_column_impossible {a e g v r s t : T}
    (hnv : NF v) (hnr : NF r) (hns : NF s) (hng : NF g)
    (hgr : mul (mul a a) r = g) (hgrh : ht g < ht r)
    (hvs : mul v s = r) (hor : origin r = some (v,s))
    (hvt : mul (mul (mul a a) g) t = v) (hst : mul g t = s)
    (hav : mul a v = e) (hes : mul e s = a) (he : ht e < ht v)
    (htGap : ht t + 2 ≤ ht r) (hsv : ht s = ht v) : False := by
  let A := mul a a
  let B := mul A g
  change mul A r = g at hgr
  change mul B t = v at hvt
  have hrHeight := mul_height_growth_of_right_le (a:=v) (b:=s) (by
    rw [hvs]; exact Nat.le_of_lt (origin_height hor).2)
  rw [hvs] at hrHeight
  have hgGap := nf_mul_height_key_gap (a:=A) hnr
  rw [hgr] at hgGap
  have hg2 : ht g + 2 ≤ ht r := by rcases hgGap with hh | hh <;> omega
  have hBg : B ≠ g := mul_ne_right A g
  by_cases httop : ht v = ht t + 1
  · exact normal_swapped_returns_top_column_impossible hnv hns hvt hst hav hes he httop (by omega) hBg
  · have htlow : ht t + 2 ≤ ht v := by omega
    have hvUpper := mul_height_upper B t
    rw [hvt] at hvUpper
    have hsUpper := mul_height_upper g t
    rw [hst] at hsUpper
    have hBHeight := inverse_height_strict (inverse_complete B t)
    rw [hvt] at hBHeight
    have hBgGap := nf_mul_height_key_gap (a:=A) hng
    change ht B = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht B + 2 ≤ ht g) at hBgGap
    rcases hBgGap with hh | hh <;> omega

theorem normal_second_same_key_unequal_column_trace {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (he : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k))
    (haw : a = mul a (mul (mul u a) k)) :
    let g := mul u a
    let v := mul a k
    ∃ r s, NF r ∧ NF s ∧ mul (mul a a) r = g ∧ mul a r = k ∧
      mul (mul a v) s = a ∧ mul v s = r ∧ ht s ≠ ht v := by
  obtain ⟨r,s,hnr,hns,_,_,hAr,hkr,hDs,hvs,_,_,_,hgr,_,t,_,hrc,hvt,hst,htGap⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  rw [← haw] at hAr hkr hDs hrc hvt he
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  refine ⟨r,s,hnr,hns,hAr,hkr,hDs,hvs,?_⟩
  intro hh
  exact normal_same_key_equal_column_impossible (nf_mul ha hk) hnr hns (nf_mul hu ha)
    hAr hgr hvs hor hvt hst rfl hDs he htGap hh

end submission.Austin12087Trace

/- Checked module: TraceHighestReturnExit -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_ladder_first_key_at_max {a d z lv rv b c w v g t j : T}
    (hvc : v = T.c a d z lv rv) (hl : ReturnLadder b c w v g t j)
    (hvt : ht v < ht t) (hwv : ht w ≤ ht v) (hgv : ht g ≤ ht v) : b = a := by
  have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  have hvGap := nf_mul_height_key_gap (a:=b) hl.1
  rw [hl.2.2.2.1] at hvGap
  have hv2 : ht v + 2 ≤ ht t := by rcases hvGap with hh | hh <;> omega
  by_cases he : b = a
  · exact he
  · have hF := mul_height_off_return_key (a:=b) hvc he
    obtain ⟨m,hl',_⟩ := return_ladder_step hl hvt (by omega)
    exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))

theorem normal_highest_g_ladder_exit {A d v g w r s u a B z l b : T}
    (hl : ReturnLadder A d v g w r s) (hgr : ht g < ht r)
    (hvg : ht v ≤ ht g) (hwg : ht w < ht g)
    (hgc : g = T.c A B z l b) (hog : origin g = some (u,a))
    (hCA : mul d w ≠ A) : mul d w = u := by
  let C := mul d w
  have hrHeight := mul_height_growth_of_right_le (a:=v) (b:=s) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at hrHeight
  have hgGap := nf_mul_height_key_gap (a:=A) hl.1
  rw [hl.2.2.2.1] at hgGap
  have hgs : ht g < ht s := by rcases hgGap with hh | hh <;> omega
  obtain ⟨t,hl₁,_⟩ := return_ladder_step hl hgr (by omega)
  have htg : ht t ≤ ht g := by
    by_cases hh : ht t ≤ ht g
    · exact hh
    · obtain ⟨j,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
      change ReturnLadder (mul A g) C w v g t j at hl₂
      have htHeight := mul_height_growth_of_right_le (a:=w) (b:=j) (by
        rw [hl₂.2.1]; exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
      rw [hl₂.2.1] at htHeight
      have hnj := (nf_origin hl₂.1 hl₂.2.2.1).2
      have hjGap := nf_mul_height_key_gap (a:=C) hnj
      rw [hl₂.2.2.2.2] at hjGap
      have hgj : ht g < ht j := by rcases hjGap with hj | hj <;> omega
      obtain ⟨n,hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      exact False.elim (hCA (normal_ladder_first_key_at_max hgc hl₃ hgj hvg (by omega)))
  have hsHeight := mul_height_growth_of_left_ge (a:=g) (b:=t) htg
  rw [hl₁.2.1] at hsHeight
  obtain ⟨j,_,_,_,hCj,_,hjGap,_⟩ := nf_return_origin_trace hl₁.1 hl₁.2.2.1 hl₁.2.2.2.1 (by omega)
  change mul C j = g at hCj
  have hog' := mul_origin_of_right_height_le (a:=C) (b:=j) (by rw [hCj]; omega)
  rw [hCj,hog] at hog'
  exact (Prod.mk.inj (Option.some.inj hog')).1.symm

end submission.Austin12087Trace

/- Checked module: TraceSameKeyHighGClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_same_key_high_g_impossible {u a v r s y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v)
    (hl : ReturnLadder (mul a a) (mul a v) v (mul u a) a r s)
    (hgr : ht (mul u a) < ht r)
    (hf : mul y (mul a v) = u) (he : ht (mul a v) < ht v)
    (hvg : ht v ≤ ht (mul u a)) : False := by
  let A := mul a a
  let g := mul u a
  let B := mul A g
  let e := mul a v
  change ReturnLadder A e v g a r s at hl
  change ht g < ht r at hgr
  change ht v ≤ ht g at hvg
  change mul y e = u at hf
  change ht e < ht v at he
  have havGap := nf_mul_height_key_gap (a:=a) hnv
  change ht e = max (ht a) (ht v) + 1 ∨ (ht a + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at havGap
  have hav : ht a + 3 ≤ ht v ∧ ht e + 2 ≤ ht v := by rcases havGap with hh | hh <;> omega
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have hgHeight := mul_height_growth_of_right_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change ht g = max (ht u) (ht a) + 1 at hgHeight
  have hug : ht g = ht u + 1 := by omega
  have heu : ht e < ht u := by omega
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change origin g = some (u,a) at hog
  have hou := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; omega)
  rw [hf] at hou
  have hrHeight := mul_height_growth_of_right_le (a:=v) (b:=s) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at hrHeight
  have hgrGap := nf_mul_height_key_gap (a:=A) hl.1
  rw [hl.2.2.2.1] at hgrGap
  have hgs : ht g < ht s := by rcases hgrGap with hh | hh <;> omega
  have hBg : ht B < ht g := by
    by_cases hh : ht B < ht g
    · exact hh
    · have hB := mul_height_growth_of_right_le (a:=A) (b:=g) (by change ht g ≤ ht B; omega)
      change ht B = max (ht A) (ht g) + 1 at hB
      obtain ⟨t,hl',_⟩ := return_ladder_step hl hgr (by omega)
      change ReturnLadder e B g a v s t at hl'
      exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))
  have hng : NF g := nf_mul hu ha
  obtain ⟨m,hgc,_,_,hABm,hBm,hmGap,_⟩ := nf_return_origin_trace hng hog (show mul A g = B from rfl) hBg
  have hou' := mul_origin_of_right_height_le (a:=mul A B) (b:=m) (by rw [hABm]; omega)
  rw [hABm,hou] at hou'
  have hme : m = e := (Prod.mk.inj (Option.some.inj hou')).2.symm
  have hBe : mul B e = a := by rw [← hme]; exact hBm
  have hea : e ≠ a := by intro hh; rw [hh] at hBe; exact mul_ne_right B a hBe
  have hCA : mul e a ≠ A := by
    intro hh
    exact hea (right_injective e a a hh)
  have hCu : mul e a = u := normal_highest_g_ladder_exit hl hgr hvg (by omega) hgc hog hCA
  have hou'' := mul_origin_of_right_height_le (a:=e) (b:=a) (by rw [hCu]; omega)
  rw [hCu,hou] at hou''
  have hae : a = e := (Prod.mk.inj (Option.some.inj hou'')).2.symm
  exact hea hae.symm

theorem normal_second_same_key_g_below_v {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (he : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k))
    (haw : a = mul a (mul (mul u a) k)) : ht (mul u a) < ht (mul a k) := by
  obtain ⟨r,s,hnr,_,_,_,hAr,_,hDs,hvs,_,_,_,hgr,_,t,_,hrc,_,_,_⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  rw [← haw] at hAr hDs hrc hf he
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a a) (mul a (mul a k)) (mul a k) (mul u a) a r s :=
    ⟨hnr,hvs,hor,hAr,hDs⟩
  by_cases hh : ht (mul u a) < ht (mul a k)
  · exact hh
  · exact False.elim (normal_same_key_high_g_impossible hu ha (nf_mul ha hk) hl hgr hf he (by omega))

end submission.Austin12087Trace

/- Checked module: TraceSameKeyHighColumnKeys -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_same_key_high_column_keys {a g v r s : T}
    (hnv : NF v)
    (hl : ReturnLadder (mul a a) (mul a v) v g a r s)
    (hgr : ht g < ht r) (he : ht (mul a v) < ht v)
    (hgv : ht g < ht v) (hvs : ht v < ht s) :
    mul (mul a a) g = a ∧
    ∃ t j, ReturnLadder a (mul (mul a v) a) a v g t j ∧
      ht v < ht t ∧ ht t < ht r ∧ mul g t = s := by
  have havGap := nf_mul_height_key_gap (a:=a) hnv
  have hav : ht a + 3 ≤ ht v := by rcases havGap with hh | hh <;> omega
  obtain ⟨t,hl₁,htr⟩ := return_ladder_step hl hgr hvs
  have hsHeight := mul_height_growth_of_right_le (a:=g) (b:=t) (by
    rw [hl₁.2.1]; exact Nat.le_of_lt (origin_height hl₁.2.2.1).2)
  rw [hl₁.2.1] at hsHeight
  have hnt := (nf_origin hl₁.1 hl₁.2.2.1).2
  have hvGap := nf_mul_height_key_gap (a:=mul (mul a a) g) hnt
  rw [hl₁.2.2.2.2] at hvGap
  have hvt : ht v < ht t := by rcases hvGap with hh | hh <;> omega
  obtain ⟨j,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
  obtain ⟨z,l,b,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) he
  have hBa := normal_ladder_first_key_at_max hvc hl₂ hvt (by omega) (by omega)
  refine ⟨hBa,t,j,?_,hvt,htr,hl₁.2.1⟩
  rw [hBa] at hl₂
  exact hl₂

theorem normal_second_same_key_high_column_frontier {u a k y r s : T}
    (hu : NF u) (ha : NF a) (hk : NF k)
    (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u)
    (hvr : ht (mul a k) < ht k)
    (he : ht (mul a (mul a k)) < ht (mul a k))
    (haw : a = mul a (mul (mul u a) k))
    (hl : ReturnLadder (mul a a) (mul a (mul a k)) (mul a k) (mul u a) a r s)
    (hgr : ht (mul u a) < ht r) (hrk : ht r < ht k)
    (hvs : ht (mul a k) < ht s) :
    mul (mul a a) (mul u a) = a ∧ mul a (mul a k) ≠ a := by
  have he' : ht (mul (mul a (mul (mul u a) k)) (mul a k)) < ht (mul a k) := by
    rw [← haw]; exact he
  have hgv := normal_second_same_key_g_below_v hu ha hk hf hvr he' haw
  obtain ⟨hB,t,j,hl₂,hvt,htr,hst⟩ := normal_same_key_high_column_keys (nf_mul ha hk) hl hgr he hgv hvs
  refine ⟨hB,?_⟩
  intro hD
  have hbounds := normal_second_query_k_dominates hu ha hk hf
  have hsmall : mul y (mul (mul a (mul (mul u a) t)) (mul a t)) = u := by
    rw [hst,hl₂.2.2.2.1]
    rw [hD] at hl
    rw [hl.2.2.2.2]
    rw [← haw] at hf
    exact hf
  have hquery := hs u a t hu ha hl₂.1 hbounds.1 hbounds.2 (by omega)
  have hi := inverse_complete y (mul (mul a (mul (mul u a) t)) (mul a t))
  rw [hsmall,hquery] at hi
  cases hi

end submission.Austin12087Trace

/- Checked module: TraceSquareKeyReturnGeometry -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_square_key_return_geometry {u a : T} (hu : NF u) (ha : NF a)
    (hB : mul (mul a a) (mul u a) = a) :
    ∃ m, NF m ∧ mul a m = a ∧ mul (mul (mul a a) a) m = u ∧
      origin u = some (mul (mul a a) a,m) ∧
      ht a + 3 ≤ ht m ∧ ht u = ht m + 1 ∧ ht (mul u a) = ht m + 2 ∧
      mul u a = c (mul a a) a m u a := by
  let A := mul a a
  let g := mul u a
  let Y := mul A a
  change mul A g = a at hB
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have hAg := inverse_height_strict (inverse_complete A g)
  rw [hB] at hAg
  have hag : ht a < ht g := by omega
  have hgGap := nf_mul_height_key_gap (a:=A) (nf_mul hu ha)
  change ht (mul A g) = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht (mul A g) + 2 ≤ ht g) at hgGap
  rw [hB] at hgGap
  have ha4 : ht a + 4 ≤ ht g := by rcases hgGap with hh | hh <;> omega
  have hgHeight := mul_height_growth_of_right_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  change ht g = max (ht u) (ht a) + 1 at hgHeight
  have hug : ht g = ht u + 1 := by omega
  have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
  obtain ⟨m,hgc,hnm,_,hYm,ham,hmGap,_⟩ := nf_return_origin_trace (nf_mul hu ha) hog hB hag
  have hmKey := nf_mul_height_key_gap (a:=a) hnm
  rw [ham] at hmKey
  have ham3 : ht a + 3 ≤ ht m := by rcases hmKey with hh | hh <;> omega
  have hY := mul_height_growth_of_left_ge (a:=A) (b:=a) (by omega)
  change ht Y = max (ht A) (ht a) + 1 at hY
  have huHeight := mul_height_growth_of_right_le (a:=Y) (b:=m) (by
    change mul Y m = u at hYm
    rw [hYm]; change ht m + 2 ≤ ht g at hmGap; omega)
  change mul Y m = u at hYm
  rw [hYm] at huHeight
  have hou := mul_origin_of_right_height_le (a:=Y) (b:=m) (by rw [hYm]; omega)
  rw [hYm] at hou
  exact ⟨m,hnm,ham,hYm,hou,ham3,by omega,by change ht g = ht m + 2; omega,hgc⟩

theorem normal_square_key_outer_alternatives {u a y e : T}
    (hu : NF u) (ha : NF a) (hne : NF e)
    (hB : mul (mul a a) (mul u a) = a) (hf : mul y e = u) :
    (mul a e = a ∧ y = mul (mul a a) a ∧ ht u = ht e + 1) ∨
      (ht (mul u a) + 1 ≤ ht e ∧ ht y + 3 ≤ ht e) := by
  obtain ⟨m,_,ham,_,hou,_,hum,hgm,_⟩ := normal_square_key_return_geometry hu ha hB
  by_cases heu : ht e ≤ ht u
  · have hou' := mul_origin_of_right_height_le (a:=y) (b:=e) (by rw [hf]; exact heu)
    rw [hf,hou] at hou'
    have hp := Prod.mk.inj (Option.some.inj hou')
    left
    rw [← hp.2]
    exact ⟨ham,hp.1.symm,hum⟩
  · right
    have hgap := nf_mul_height_key_gap (a:=y) hne
    rw [hf] at hgap
    rcases hgap with hh | hh <;> omega

end submission.Austin12087Trace

/- Checked module: TraceSameKeyHighColumnOuter -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_same_key_high_column_outer_return {u a v r s y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v)
    (hl : ReturnLadder (mul a a) (mul a v) v (mul u a) a r s)
    (hgr : ht (mul u a) < ht r) (he : ht (mul a v) < ht v)
    (hgv : ht (mul u a) < ht v) (hvs : ht v < ht s)
    (hf : mul y (mul a v) = u) :
    ht (mul u a) + 1 ≤ ht (mul a v) ∧ ht y + 3 ≤ ht (mul a v) := by
  let e := mul a v
  let g := mul u a
  change ReturnLadder (mul a a) e v g a r s at hl
  change ht g < ht r at hgr
  change ht e < ht v at he
  change ht g < ht v at hgv
  change mul y e = u at hf
  change ht g + 1 ≤ ht e ∧ ht y + 3 ≤ ht e
  obtain ⟨hB,t,j,hl₂,hvt,_,_⟩ := normal_same_key_high_column_keys hnv hl hgr he hgv hvs
  rcases normal_square_key_outer_alternatives hu ha (nf_mul ha hnv) hB hf with ⟨hae,_,hue⟩ | hret
  · change ht u = ht e + 1 at hue
    have heGap := nf_mul_height_key_gap (a:=a) hnv
    change ht e = max (ht a) (ht v) + 1 ∨ (ht a + 3 ≤ ht v ∧ ht e + 2 ≤ ht v) at heGap
    have hav : ht a + 3 ≤ ht v := by rcases heGap with hh | hh <;> omega
    have haGap := nf_mul_height_key_gap (a:=a) (nf_mul ha hnv)
    change ht (mul a e) = max (ht a) (ht e) + 1 ∨ (ht a + 3 ≤ ht e ∧ ht (mul a e) + 2 ≤ ht e) at haGap
    rw [hae] at haGap
    have hae3 : ht a + 3 ≤ ht e := by rcases haGap with hh | hh <;> omega
    have hgHeight := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hgHeight
    have hge : ht g = ht e + 2 := by omega
    have htHeight := mul_height_growth_of_right_le (a:=a) (b:=j) (by
      rw [hl₂.2.1]; exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
    rw [hl₂.2.1] at htHeight
    have htGap := nf_mul_height_key_gap (a:=a) hl₂.1
    rw [hl₂.2.2.2.1] at htGap
    have hvj : ht v < ht j := by rcases htGap with hh | hh <;> omega
    obtain ⟨l,hl₃,_⟩ := return_ladder_step hl₂ hvt (by omega)
    change ReturnLadder (mul e a) e v g a j l at hl₃
    have hua : u ≠ a := by intro hh; have hh' := congrArg ht hh; omega
    exact False.elim (nonfixed_same_key_ladder_impossible ha (nf_mul ha hnv) hae rfl hf rfl hua
      (by change ht e + 1 < ht g; omega) (by change ht g ≤ ht v; omega) hl₃
      (by change ht g < ht j; omega))
  · exact hret

end submission.Austin12087Trace

/- Checked module: TraceSameKeyColumnFrontier -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_second_same_key_column_frontier {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    let g := mul u a
    let v := mul a k
    let e := mul a v
    a = mul a (mul g k) ∧ ht g < ht v ∧
    ∃ r s, NF r ∧ NF s ∧ mul (mul a a) r = g ∧ mul a r = k ∧
      mul e s = a ∧ mul v s = r ∧
      (ht s < ht v ∨ (ht v < ht s ∧ mul (mul a a) g = a ∧
        ht g + 1 ≤ ht e ∧ ht y + 3 ≤ ht e)) := by
  have haw := normal_second_induction_requires_equal_return_keys hu ha hk hs hf
  obtain ⟨hvr,he⟩ := normal_second_induction_requires_two_returns hu ha hk hs hf
  have hgv := normal_second_same_key_g_below_v hu ha hk hf hvr he haw
  obtain ⟨r,s,hnr,hns,hrk,_,hAr,hkr,hDs,hvs,_,_,_,hgr,_,t,_,hrc,hvt,hst,htGap⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  rw [← haw] at hAr hkr hDs hrc hvt hf he
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a a) (mul a (mul a k)) (mul a k) (mul u a) a r s :=
    ⟨hnr,hvs,hor,hAr,hDs⟩
  refine ⟨haw,hgv,r,s,hnr,hns,hAr,hkr,hDs,hvs,?_⟩
  have hne : ht s ≠ ht (mul a k) := by
    intro hh
    exact normal_same_key_equal_column_impossible (nf_mul ha hk) hnr hns (nf_mul hu ha)
      hAr hgr hvs hor hvt hst rfl hDs he htGap hh
  by_cases hsv : ht s < ht (mul a k)
  · exact Or.inl hsv
  · have hvs' : ht (mul a k) < ht s := by omega
    obtain ⟨hB,_⟩ := normal_same_key_high_column_keys (nf_mul ha hk) hl hgr he hgv hvs'
    have ho := normal_same_key_high_column_outer_return hu ha (nf_mul ha hk) hl hgr he hgv hvs' hf
    exact Or.inr ⟨hvs',hB,ho⟩

end submission.Austin12087Trace

/- Checked module: TraceHighColumnReturnCycle -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_high_v_tail_growth {a e g v t j : T}
    (hnv : NF v) (hav : mul a v = e) (he : ht e < ht v)
    (hag : ht a < ht v) (hgv : ht g < ht v)
    (hl : ReturnLadder a (mul e a) a v g t j) (hvt : ht v < ht t)
    (hKa : mul (mul e a) g ≠ a) :
    ∃ l m, NF l ∧ NF m ∧ mul e l = a ∧ mul v l = j ∧
      mul (mul (mul e a) g) m = v ∧ mul g m = l ∧
      origin v = some (mul (mul e a) g,m) ∧ ht m < ht v := by
  let C := mul e a
  let K := mul C g
  change ReturnLadder a C a v g t j at hl
  change K ≠ a at hKa
  obtain ⟨z,lv,rv,hvc⟩ := mul_return_of_height_lt (a:=a) (b:=v) (by rw [hav]; exact he)
  rw [hav] at hvc
  have htHeight := mul_height_growth_of_right_le (a:=a) (b:=j) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at htHeight
  have htGap := nf_mul_height_key_gap (a:=a) hl.1
  rw [hl.2.2.2.1] at htGap
  have hvj : ht v < ht j := by rcases htGap with hh | hh <;> omega
  obtain ⟨l,_,hnl,hnj,hel,hvl,hlGap,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hvt
  rw [hav] at hel
  have hjHeight := mul_height_growth_of_right_le (a:=v) (b:=l) (by rw [hvl]; omega)
  rw [hvl] at hjHeight
  have hoj := mul_origin_of_right_height_le (a:=v) (b:=l) (by rw [hvl]; omega)
  rw [hvl] at hoj
  obtain ⟨m,_,hnm,_,hKm,hgm,hmGap,_⟩ := nf_return_origin_trace hnj hoj hl.2.2.2.2 (by omega)
  change mul K m = v at hKm
  have hmv : ht m ≤ ht v := by
    by_cases hh : ht m ≤ ht v
    · exact hh
    · have hml : ht m < ht l := by omega
      have hol := mul_origin_of_right_height_le (a:=g) (b:=m) (by rw [hgm]; omega)
      rw [hgm] at hol
      have hl₂ : ReturnLadder e K g a v l m := ⟨hnl,hgm,hol,hel,hKm⟩
      obtain ⟨n,hl₃,_⟩ := return_ladder_step hl₂ (by omega) (by omega)
      change ReturnLadder K C a v g m n at hl₃
      exact False.elim (hKa (normal_ladder_first_key_at_max hvc hl₃ (by omega) (by omega) (by omega)))
  have hvHeight := mul_height_growth_of_right_le (a:=K) (b:=m) (by rw [hKm]; exact hmv)
  rw [hKm] at hvHeight
  have hov := mul_origin_of_right_height_le (a:=K) (b:=m) (by rw [hKm]; exact hmv)
  rw [hKm] at hov
  exact ⟨l,m,hnl,hnm,hel,hvl,hKm,hgm,hov,by omega⟩

theorem normal_high_column_return_cycle_impossible {a e g v t j : T}
    (ha : NF a) (hnv : NF v) (hav : mul a v = e)
    (he : ht e < ht v) (hae : ht a < ht e) (hge : ht g < ht e)
    (hl : ReturnLadder a (mul e a) a v g t j) (hvt : ht v < ht t) : False := by
  let C := mul e a
  let K := mul C g
  let H := mul a e
  have hC := mul_height_growth_of_left_ge (a:=e) (b:=a) (by omega)
  change ht C = max (ht e) (ht a) + 1 at hC
  have hK := mul_height_growth_of_left_ge (a:=C) (b:=g) (by omega)
  change ht K = max (ht C) (ht g) + 1 at hK
  have hKe : ht K = ht e + 2 := by omega
  have hoK := mul_origin_of_right_height_le (a:=C) (b:=g) (by change ht g ≤ ht K; omega)
  change origin K = some (C,g) at hoK
  have hKa : K ≠ a := by intro hh; have hh' := congrArg ht hh; omega
  obtain ⟨l,m,hnl,hnm,hel,_,hKm,hgm,hov,hmv⟩ :=
    normal_high_v_tail_growth hnv hav he (by omega) (by omega) hl hvt hKa
  change mul K m = v at hKm
  change origin v = some (K,m) at hov
  obtain ⟨n,_,hnn,_,hHn,hen,hnGap,_⟩ := nf_return_origin_trace hnv hov hav he
  change mul H n = K at hHn
  have hKn : ht K < ht n := by
    by_cases hh : ht K < ht n
    · exact hh
    · have hoK' := mul_origin_of_right_height_le (a:=H) (b:=n) (by rw [hHn]; omega)
      rw [hHn,hoK] at hoK'
      have hHC : H = C := (Prod.mk.inj (Option.some.inj hoK')).1.symm
      have hae' := mul_commutative_only_equal hHC
      have hheight := congrArg ht hae'
      exact False.elim (by omega)
  obtain ⟨z,ln,rn,hnc⟩ := mul_return_of_height_lt (a:=H) (b:=n) (by rw [hHn]; exact hKn)
  have heH : e ≠ H := by intro hh; exact mul_ne_right a e hh.symm
  have hmHeight := mul_height_off_return_key (a:=e) hnc heH
  rw [hen] at hmHeight
  have hom := mul_origin_of_right_height_le (a:=e) (b:=n) (by rw [hen]; omega)
  rw [hen] at hom
  have hvHeight := mul_height_growth_of_right_le (a:=K) (b:=m) (by rw [hKm]; omega)
  rw [hKm] at hvHeight
  have hlm : ht l < ht m := by
    by_cases hh : ht l < ht m
    · exact hh
    · have hlHeight := mul_height_growth_of_right_le (a:=g) (b:=m) (by rw [hgm]; omega)
      rw [hgm] at hlHeight
      have hol := mul_origin_of_right_height_le (a:=g) (b:=m) (by rw [hgm]; omega)
      rw [hgm] at hol
      obtain ⟨p,_,_,_,_,hap,hpGap,_⟩ := nf_return_origin_trace hnl hol hel (by omega)
      have hom' := mul_origin_of_right_height_le (a:=a) (b:=p) (by rw [hap]; omega)
      rw [hap,hom] at hom'
      have hea' := (Prod.mk.inj (Option.some.inj hom')).1
      have hheight := congrArg ht hea'
      exact False.elim (by omega)
  obtain ⟨p,_,_,_,hGl,hlp,hpGap,_⟩ := nf_return_origin_trace hnm hom hgm hlm
  have hon := mul_origin_of_right_height_le (a:=l) (b:=p) (by rw [hlp]; omega)
  rw [hlp] at hon
  have hl₂ : ReturnLadder H (mul g l) l K e n p := ⟨hnn,hlp,hon,hHn,hGl⟩
  have hlGap := nf_mul_height_key_gap (a:=e) hnl
  rw [hel] at hlGap
  have hel3 : ht e + 3 ≤ ht l := by rcases hlGap with hh | hh <;> omega
  obtain ⟨zl,ll,rl,hlc⟩ := mul_return_of_height_lt (a:=e) (b:=l) (by rw [hel]; omega)
  have hge' : g ≠ e := by intro hh; have hh' := congrArg ht hh; omega
  have hG := mul_height_off_return_key (a:=g) hlc hge'
  exact return_ladder_second_dominant_impossible hl₂ hKn (by omega) (by omega) (by omega)

end submission.Austin12087Trace

/- Checked module: TraceSameKeyHighColumnClosed -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_same_key_high_column_impossible {u a v r s y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v)
    (hl : ReturnLadder (mul a a) (mul a v) v (mul u a) a r s)
    (hgr : ht (mul u a) < ht r) (he : ht (mul a v) < ht v)
    (hgv : ht (mul u a) < ht v) (hvs : ht v < ht s)
    (hf : mul y (mul a v) = u) : False := by
  obtain ⟨hB,t,j,hl₂,hvt,_,_⟩ := normal_same_key_high_column_keys hnv hl hgr he hgv hvs
  have hout := normal_same_key_high_column_outer_return hu ha hnv hl hgr he hgv hvs hf
  obtain ⟨m,_,_,_,_,ham,_,hgm,_⟩ := normal_square_key_return_geometry hu ha hB
  exact normal_high_column_return_cycle_impossible ha hnv rfl he (by omega) (by omega) hl₂ hvt

theorem normal_second_same_key_low_column_frontier {u a k y : T}
    (hu : NF u) (ha : NF a) (hk : NF k) (hs : NormalSecondBelow (ht k))
    (hf : mul y (mul (mul a (mul (mul u a) k)) (mul a k)) = u) :
    let g := mul u a
    let v := mul a k
    let e := mul a v
    a = mul a (mul g k) ∧ ht g < ht v ∧ ht e < ht v ∧
    ∃ r s, NF r ∧ NF s ∧ mul (mul a a) r = g ∧ mul a r = k ∧
      mul e s = a ∧ mul v s = r ∧ ht s < ht v := by
  have haw := normal_second_induction_requires_equal_return_keys hu ha hk hs hf
  obtain ⟨hvr,he⟩ := normal_second_induction_requires_two_returns hu ha hk hs hf
  have hgv := normal_second_same_key_g_below_v hu ha hk hf hvr he haw
  obtain ⟨r,s,hnr,hns,_,_,hAr,hkr,hDs,hvs,_,_,_,hgr,_,t,_,hrc,hvt,hst,htGap⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  rw [← haw] at hAr hkr hDs hrc hvt hf he
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a a) (mul a (mul a k)) (mul a k) (mul u a) a r s :=
    ⟨hnr,hvs,hor,hAr,hDs⟩
  refine ⟨haw,hgv,he,r,s,hnr,hns,hAr,hkr,hDs,hvs,?_⟩
  by_cases hh : ht s < ht (mul a k)
  · exact hh
  · by_cases heq : ht s = ht (mul a k)
    · exact False.elim (normal_same_key_equal_column_impossible (nf_mul ha hk) hnr hns (nf_mul hu ha)
        hAr hgr hvs hor hvt hst rfl hDs he htGap heq)
    · exact False.elim (normal_same_key_high_column_impossible hu ha (nf_mul ha hk) hl hgr he hgv (by omega) hf)

end submission.Austin12087Trace

/- Checked module: TraceLowColumnTailHeight -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem square_preimage_height {a e : T} (h : mul a e = mul a a) : ht a ≤ ht e := by
  by_cases hh : ht a ≤ ht e
  · exact hh
  · have hs : ht (mul a a) = ht a + 1 := by rw [mul_square]; rfl
    have ho := mul_origin_of_right_height_le (a:=a) (b:=e) (by rw [h]; omega)
    rw [h,mul_square] at ho
    have hea := (Prod.mk.inj (Option.some.inj ho)).2
    have heh := congrArg ht hea
    omega

theorem normal_low_column_tail_at_top {u a e v s t : T}
    (ha : NF a) (hng : NF (mul u a)) (hnv : NF v) (hns : NF s)
    (hvt : mul (mul (mul a a) (mul u a)) t = v)
    (hst : mul (mul u a) t = s) (hav : mul a v = e) (hes : mul e s = a)
    (he : ht e < ht v) (hsv : ht s < ht v) (hgv : ht (mul u a) < ht v)
    (htv : ht t < ht v) : ht v = ht t + 1 := by
  let A := mul a a
  let g := mul u a
  let B := mul A g
  change mul B t = v at hvt
  change mul g t = s at hst
  change NF g at hng
  change ht g < ht v at hgv
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have havGap := nf_mul_height_key_gap (a:=a) hnv
  rw [hav] at havGap
  have hav3 : ht a + 3 ≤ ht v := by rcases havGap with hh | hh <;> omega
  have hvHeight := mul_height_growth_of_right_le (a:=B) (b:=t) (by rw [hvt]; omega)
  rw [hvt] at hvHeight
  have hov := mul_origin_of_right_height_le (a:=B) (b:=t) (by rw [hvt]; omega)
  rw [hvt] at hov
  by_cases hh : ht v = ht t + 1
  · exact hh
  · have hBv : ht B + 1 = ht v := by omega
    have hBgGap := nf_mul_height_key_gap (a:=A) hng
    change ht B = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht B + 2 ≤ ht g) at hBgGap
    have hBg : ht B = max (ht A) (ht g) + 1 := by rcases hBgGap with hh | hh <;> omega
    have hoB := mul_origin_of_right_height_le (a:=A) (b:=g) (by change ht g ≤ ht B; omega)
    change origin B = some (A,g) at hoB
    obtain ⟨n,_,_,_,hHn,hen,hnGap,_⟩ := nf_return_origin_trace hnv hov hav he
    have hoB' := mul_origin_of_right_height_le (a:=mul a e) (b:=n) (by rw [hHn]; omega)
    rw [hHn,hoB] at hoB'
    have hp := Prod.mk.inj (Option.some.inj hoB')
    have hH : mul a e = A := hp.1.symm
    have hng' : n = g := hp.2.symm
    rw [hng'] at hen
    have hae := square_preimage_height hH
    have hesGap := nf_mul_height_key_gap (a:=e) hns
    rw [hes] at hesGap
    have hes3 : ht e + 3 ≤ ht s := by rcases hesGap with hh | hh <;> omega
    have hgv2 : ht g + 2 = ht v := by omega
    have htGap := nf_mul_height_key_gap (a:=e) hng
    rw [hen] at htGap
    have hgt : ht e + 3 ≤ ht g ∧ ht t + 2 ≤ ht g := by rcases htGap with hh | hh <;> omega
    have hsHeight := mul_height_growth_of_left_ge (a:=g) (b:=t) (by omega)
    rw [hst] at hsHeight
    have hos := mul_origin_of_right_height_le (a:=g) (b:=t) (by rw [hst]; omega)
    rw [hst] at hos
    obtain ⟨p,_,_,_,hCp,hap,hpGap,_⟩ := nf_return_origin_trace hns hos hes (by omega)
    have hog := mul_origin_of_right_height_le (a:=u) (b:=a) (by change ht a ≤ ht g; omega)
    change origin g = some (u,a) at hog
    have hog' := mul_origin_of_right_height_le (a:=mul e a) (b:=p) (by rw [hCp]; omega)
    rw [hCp,hog] at hog'
    have hCu : mul e a = u := (Prod.mk.inj (Option.some.inj hog')).1.symm
    have huHeight := mul_height_growth_of_left_ge (a:=e) (b:=a) hae
    rw [hCu] at huHeight
    have hgHeight := mul_height_growth_of_left_ge (a:=u) (b:=a) (by omega)
    change ht g = max (ht u) (ht a) + 1 at hgHeight
    omega

end submission.Austin12087Trace

/- Checked module: TraceLowColumnCrossLadder -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_column_cross_ladder {a e g v s t : T}
    (hng : NF g) (hnv : NF v) (hns : NF s) (hnt : NF t)
    (hvt : mul (mul (mul a a) g) t = v) (hst : mul g t = s)
    (hav : mul a v = e) (hes : mul e s = a)
    (he : ht e < ht v) (hsv : ht s < ht v) (htv : ht v = ht t + 1) :
    ∃ n p, ReturnLadder (mul a e) (mul g s) s (mul (mul a a) g) e n p ∧
      ht (mul (mul a a) g) < ht n ∧ ht v = ht n + 2 := by
  let A := mul a a
  let B := mul A g
  let H := mul a e
  change mul B t = v at hvt
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have havGap := nf_mul_height_key_gap (a:=a) hnv
  rw [hav] at havGap
  have ha3 : ht a + 3 ≤ ht v := by rcases havGap with hh | hh <;> omega
  have hesGap := nf_mul_height_key_gap (a:=e) hns
  rw [hes] at hesGap
  have he4 : ht e + 4 ≤ ht v := by rcases hesGap with hh | hh <;> omega
  have hsGap := nf_mul_height_key_gap (a:=g) hnt
  rw [hst] at hsGap
  have hg3 : ht g + 3 ≤ ht t ∧ ht s + 2 ≤ ht t := by rcases hsGap with hh | hh <;> omega
  have hov := mul_origin_of_right_height_le (a:=B) (b:=t) (by rw [hvt]; omega)
  rw [hvt] at hov
  obtain ⟨n,_,hnn,_,hHn,hen,hnGap,_⟩ := nf_return_origin_trace hnv hov hav he
  change mul H n = B at hHn
  have htUpper := mul_height_upper e n
  rw [hen] at htUpper
  have htn : ht t = ht n + 1 := by omega
  have hom := mul_origin_of_right_height_le (a:=e) (b:=n) (by rw [hen]; omega)
  rw [hen] at hom
  have hBn : ht B < ht n := by
    by_cases hh : ht B < ht n
    · exact hh
    · have hBHeight := mul_height_growth_of_right_le (a:=H) (b:=n) (by rw [hHn]; omega)
      rw [hHn] at hBHeight
      have hBgap := nf_mul_height_key_gap (a:=A) hng
      change ht B = max (ht A) (ht g) + 1 ∨ (ht A + 3 ≤ ht g ∧ ht B + 2 ≤ ht g) at hBgap
      have hBg : ht B = max (ht A) (ht g) + 1 := by rcases hBgap with hh | hh <;> omega
      have hoB := mul_origin_of_right_height_le (a:=A) (b:=g) (by change ht g ≤ ht B; omega)
      change origin B = some (A,g) at hoB
      have hoB' := mul_origin_of_right_height_le (a:=H) (b:=n) (by rw [hHn]; omega)
      rw [hHn,hoB] at hoB'
      have hgn := (Prod.mk.inj (Option.some.inj hoB')).2
      have hh' := congrArg ht hgn
      omega
  obtain ⟨p,_,_,_,hGp,hsp,hpGap,_⟩ := nf_return_origin_trace hnt hom hst (by omega)
  have hon := mul_origin_of_right_height_le (a:=s) (b:=p) (by rw [hsp]; omega)
  rw [hsp] at hon
  exact ⟨n,p,⟨hnn,hsp,hon,hHn,hGp⟩,hBn,by omega⟩

theorem normal_low_cross_ladder_equal_heads {a e g s n p : T}
    (ha : NF a) (hne : NF e) (hng : NF g) (hns : NF s)
    (hes : mul e s = a)
    (hl : ReturnLadder (mul a e) (mul g s) s (mul (mul a a) g) e n p)
    (hBn : ht (mul (mul a a) g) < ht n) : g = e ∧ ht a < ht s := by
  let A := mul a a
  let B := mul A g
  let H := mul a e
  let G := mul g s
  change ReturnLadder H G s B e n p at hl
  change ht B < ht n at hBn
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have hBUpper := mul_height_upper A g
  change ht B ≤ max (ht A) (ht g) + 1 at hBUpper
  have hesGap := nf_mul_height_key_gap (a:=e) hns
  rw [hes] at hesGap
  have has : ht a < ht s := by
    by_cases hh : ht a < ht s
    · exact hh
    · have haGrow : ht a = max (ht e) (ht s) + 1 := by rcases hesGap with hh | hh <;> omega
      have hH := mul_height_growth_of_left_ge (a:=a) (b:=e) (by omega)
      change ht H = max (ht a) (ht e) + 1 at hH
      by_cases hgA : ht A ≤ ht g
      · have hG := mul_height_growth_of_left_ge (a:=g) (b:=s) (by omega)
        change ht G = max (ht g) (ht s) + 1 at hG
        exact False.elim (return_ladder_second_dominant_impossible hl hBn (by omega) (by omega) (by omega))
      · have hB := mul_height_growth_of_left_ge (a:=A) (b:=g) (by omega)
        change ht B = max (ht A) (ht g) + 1 at hB
        have hFgap := nf_mul_height_key_gap (a:=H) (nf_mul (nf_mul ha ha) hng)
        change ht (mul H B) = max (ht H) (ht B) + 1 ∨ (ht H + 3 ≤ ht B ∧ ht (mul H B) + 2 ≤ ht B) at hFgap
        have hF : ht (mul H B) = max (ht H) (ht B) + 1 := by rcases hFgap with hh | hh <;> omega
        have hnHeight := mul_height_growth_of_right_le (a:=s) (b:=p) (by
          rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
        rw [hl.2.1] at hnHeight
        have hnGap := nf_mul_height_key_gap (a:=H) hl.1
        rw [hl.2.2.2.1] at hnGap
        have hB2 : ht B + 2 ≤ ht n := by rcases hnGap with hh | hh <;> omega
        obtain ⟨q,hl',_⟩ := return_ladder_step hl hBn (by omega)
        exact False.elim (return_ladder_second_dominant_impossible hl' (by omega) (by omega) (by omega) (by omega))
  have hsRet : ht e + 3 ≤ ht s ∧ ht a + 2 ≤ ht s := by rcases hesGap with hh | hh <;> omega
  refine ⟨?_,has⟩
  by_cases hge : g = e
  · exact hge
  · obtain ⟨z,l,r,hsc⟩ := mul_return_of_height_lt (a:=e) (b:=s) (by rw [hes]; exact has)
    have hG := mul_height_off_return_key (a:=g) hsc hge
    change ht G = max (ht g) (ht s) + 1 at hG
    exact False.elim (return_ladder_second_dominant_impossible hl hBn (by omega) (by omega) (by omega))

end submission.Austin12087Trace

/- Checked module: TraceLowEqualHeadCycle -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_equal_head_height {u a y : T} (ha : NF a) (hu : NF u)
    (hf : mul y (mul u a) = u) : ht (mul u a) ≤ ht a + 1 := by
  have hg := nf_mul_height_key_gap (a:=u) ha
  have hfGap := nf_mul_height_key_gap (a:=y) (nf_mul hu ha)
  rw [hf] at hfGap
  rcases hg with hg | hg <;> rcases hfGap with hh | hh <;> omega

theorem normal_equal_head_ladder_impossible {a e s n p : T}
    (ha : NF a) (hne : NF e) (hns : NF s)
    (hea : e ≠ a) (heHeight : ht e ≤ ht a + 1)
    (hes : mul e s = a) (has : ht a < ht s)
    (hl : ReturnLadder (mul a e) a s (mul (mul a a) e) e n p)
    (hBn : ht (mul (mul a a) e) < ht n) : False := by
  let A := mul a a
  let B := mul A e
  let H := mul a e
  let F := mul H B
  let C := mul e a
  change ReturnLadder H a s B e n p at hl
  change ht B < ht n at hBn
  have hA : ht A = ht a + 1 := by dsimp only [A]; rw [mul_square]; rfl
  have hHgap := nf_mul_height_key_gap (a:=a) hne
  change ht H = max (ht a) (ht e) + 1 ∨ (ht a + 3 ≤ ht e ∧ ht H + 2 ≤ ht e) at hHgap
  have hH : ht H = max (ht a) (ht e) + 1 := by rcases hHgap with hh | hh <;> omega
  have hBgap := nf_mul_height_key_gap (a:=A) hne
  change ht B = max (ht A) (ht e) + 1 ∨ (ht A + 3 ≤ ht e ∧ ht B + 2 ≤ ht e) at hBgap
  have hB : ht B = ht a + 2 := by rcases hBgap with hh | hh <;> omega
  have hFgap := nf_mul_height_key_gap (a:=H) (nf_mul (nf_mul ha ha) hne)
  change ht F = max (ht H) (ht B) + 1 ∨ (ht H + 3 ≤ ht B ∧ ht F + 2 ≤ ht B) at hFgap
  have hF : ht F = ht B + 1 := by rcases hFgap with hh | hh <;> omega
  have hoF := mul_origin_of_right_height_le (a:=H) (b:=B) (by change ht B ≤ ht F; omega)
  change origin F = some (H,B) at hoF
  have hesGap := nf_mul_height_key_gap (a:=e) hns
  rw [hes] at hesGap
  have hsRet : ht e + 3 ≤ ht s ∧ ht a + 2 ≤ ht s := by rcases hesGap with hh | hh <;> omega
  have hnHeight := mul_height_growth_of_right_le (a:=s) (b:=p) (by
    rw [hl.2.1]; exact Nat.le_of_lt (origin_height hl.2.2.1).2)
  rw [hl.2.1] at hnHeight
  obtain ⟨q,_,hnq,hnp,hFq,hBq,hqGap,_⟩ := nf_return_origin_trace hl.1 hl.2.2.1 hl.2.2.2.1 hBn
  change mul F q = s at hFq
  by_cases hps : ht p ≤ ht s
  · have hsHeight := mul_height_growth_of_right_le (a:=F) (b:=q) (by rw [hFq]; omega)
    rw [hFq] at hsHeight
    have hos := mul_origin_of_right_height_le (a:=F) (b:=q) (by rw [hFq]; omega)
    rw [hFq] at hos
    obtain ⟨z,_,hnz,_,hCz,haz,hzGap,_⟩ := nf_return_origin_trace hns hos hes has
    change mul C z = F at hCz
    have hCH : C ≠ H := by
      intro hh
      exact hea (mul_commutative_only_equal hh)
    have hFz : ht F < ht z := by
      by_cases hh : ht F < ht z
      · exact hh
      · have hoF' := mul_origin_of_right_height_le (a:=C) (b:=z) (by rw [hCz]; omega)
        rw [hCz,hoF] at hoF'
        exact False.elim (hCH (Prod.mk.inj (Option.some.inj hoF')).1.symm)
    have hsq : ht s = ht q + 1 := by omega
    have hqUpper := mul_height_upper a z
    rw [haz] at hqUpper
    have hqz : ht q = ht z + 1 := by omega
    have hoq := mul_origin_of_right_height_le (a:=a) (b:=z) (by rw [haz]; omega)
    rw [haz] at hoq
    have hpq : ht p < ht q := by
      by_cases hh : ht p < ht q
      · exact hh
      · have hpHeight := mul_height_growth_of_right_le (a:=B) (b:=q) (by rw [hBq]; omega)
        rw [hBq] at hpHeight
        have hBF : B ≠ F := by intro hh; have hh' := congrArg ht hh; omega
        exact False.elim (normal_swapped_returns_top_column_impossible hnp hns hBq hFq
          hl.2.2.2.2 hes (by omega) (by omega) hsq hBF)
    obtain ⟨w,_,_,_,hBPw,hpw,hwGap,_⟩ := nf_return_origin_trace hnq hoq hBq hpq
    have hoz := mul_origin_of_right_height_le (a:=p) (b:=w) (by rw [hpw]; omega)
    rw [hpw] at hoz
    have hl' : ReturnLadder C (mul B p) p F a z w := ⟨hnz,hpw,hoz,hCz,hBPw⟩
    have hBP : ht (mul B p) = max (ht B) (ht p) + 1 := by
      by_cases hpB : ht p ≤ ht B
      · exact mul_height_growth_of_left_ge hpB
      · obtain ⟨zp,lp,rp,hpc⟩ := mul_return_of_height_lt (a:=a) (b:=p) (by rw [hl.2.2.2.2]; omega)
        have hBa : B ≠ a := by intro hh; have hh' := congrArg ht hh; omega
        exact mul_height_off_return_key hpc hBa
    exact return_ladder_second_dominant_impossible hl' hFz (by omega) (by omega) (by omega)
  · have hpHeight := mul_height_growth_of_right_le (a:=B) (b:=q) (by rw [hBq]; omega)
    rw [hBq] at hpHeight
    have hsq : ht s < ht q := by
      have hsGap := nf_mul_height_key_gap (a:=F) hnq
      rw [hFq] at hsGap
      rcases hsGap with hh | hh <;> omega
    obtain ⟨q',hl₁,_⟩ := return_ladder_step hl hBn (by omega)
    have hq'q : q' = q := by
      have hoq := mul_origin_of_right_height_le (a:=B) (b:=q) (by rw [hBq]; omega)
      rw [hBq] at hoq
      exact (Prod.mk.inj (Option.some.inj (hl₁.2.2.1.symm.trans hoq))).2
    subst q'
    obtain ⟨r,hl₂,_⟩ := return_ladder_step hl₁ (by omega) (by omega)
    change ReturnLadder F H e s B q r at hl₂
    have hqHeight := mul_height_growth_of_right_le (a:=e) (b:=r) (by
      rw [hl₂.2.1]; exact Nat.le_of_lt (origin_height hl₂.2.2.1).2)
    rw [hl₂.2.1] at hqHeight
    have hqGap := nf_mul_height_key_gap (a:=F) hl₂.1
    rw [hl₂.2.2.2.1] at hqGap
    have hsr : ht s < ht r := by rcases hqGap with hh | hh <;> omega
    obtain ⟨z,hl₃,_⟩ := return_ladder_step hl₂ hsq (by omega)
    change ReturnLadder H (mul F s) s B e r z at hl₃
    obtain ⟨zs,ls,rs,hsc⟩ := mul_return_of_height_lt (a:=e) (b:=s) (by rw [hes]; exact has)
    have hFe : F ≠ e := by intro hh; have hh' := congrArg ht hh; omega
    have hFs := mul_height_off_return_key (a:=F) hsc hFe
    exact return_ladder_second_dominant_impossible hl₃ (by omega) (by omega) (by omega) (by omega)

end submission.Austin12087Trace

/- Checked module: TraceFullSource -/
set_option autoImplicit false

namespace submission.Austin12087Trace
open T

theorem normal_low_column_cycle_impossible {u a e v s t y : T}
    (hu : NF u) (ha : NF a) (hnv : NF v) (hns : NF s) (hnt : NF t)
    (hvt : mul (mul (mul a a) (mul u a)) t = v)
    (hst : mul (mul u a) t = s) (hav : mul a v = e) (hes : mul e s = a)
    (he : ht e < ht v) (hsv : ht s < ht v) (hgv : ht (mul u a) < ht v)
    (htv : ht t < ht v) (hf : mul y e = u) : False := by
  have hng := nf_mul hu ha
  have hne : NF e := hav ▸ nf_mul ha hnv
  have httop := normal_low_column_tail_at_top ha hng hnv hns hvt hst hav hes he hsv hgv htv
  obtain ⟨n,p,hl,hBn,_⟩ := normal_low_column_cross_ladder hng hnv hns hnt hvt hst hav hes he hsv httop
  obtain ⟨hge,has⟩ := normal_low_cross_ladder_equal_heads ha hne hng hns hes hl hBn
  rw [hge,hes] at hl
  rw [hge] at hBn
  have hea : e ≠ a := by rw [← hge]; exact mul_ne_right u a
  have hf' : mul y (mul u a) = u := by rw [hge]; exact hf
  have hh := normal_equal_head_height ha hu hf'
  rw [hge] at hh
  exact normal_equal_head_ladder_impossible ha hne hns hea hh hes has hl hBn

theorem normal_same_key_middle_step : NormalSameKeyMiddleStep := by
  intro u a k y hu ha hk hs hf hvr he haw
  have hgv := normal_second_same_key_g_below_v hu ha hk hf hvr he haw
  obtain ⟨r,s,hnr,hns,_,_,hAr,hkr,hDs,hvs,_,_,_,hgr,_,t,hnt,hrc,hvt,hst,htGap⟩ :=
    normal_second_returning_v_low_head hu ha hk hf hvr
  rw [← haw] at hAr hkr hDs hrc hvt hf he
  have hor : origin r = some (mul a k,s) := by rw [hrc]; rfl
  have hl : ReturnLadder (mul a a) (mul a (mul a k)) (mul a k) (mul u a) a r s :=
    ⟨hnr,hvs,hor,hAr,hDs⟩
  have hsv : ht s < ht (mul a k) := by
    by_cases hh : ht s < ht (mul a k)
    · exact hh
    · by_cases heq : ht s = ht (mul a k)
      · exact False.elim (normal_same_key_equal_column_impossible (nf_mul ha hk) hnr hns (nf_mul hu ha)
          hAr hgr hvs hor hvt hst rfl hDs he htGap heq)
      · exact False.elim (normal_same_key_high_column_impossible hu ha (nf_mul ha hk) hl hgr he hgv (by omega) hf)
  have hrHeight := mul_height_growth_of_right_le (a:=mul a k) (b:=s) (by
    rw [hvs]; exact Nat.le_of_lt (origin_height hor).2)
  rw [hvs] at hrHeight
  exact normal_low_column_cycle_impossible hu ha (nf_mul ha hk) hns hnt hvt hst rfl hDs
    he hsv hgv (by omega) hf

theorem full_source_law : ∀ x y z : NormalTree,
    x = normalMul y (normalMul (normalMul (normalMul y x) z) (normalMul x z)) :=
  normal_law_of_same_key_middle_step normal_same_key_middle_step

theorem infinite_model : ∃ (G : Type) (op : G → G → G) (embed : Nat → G),
    (∀ x y z, x = op y (op (op (op y x) z) (op x z))) ∧
    (∀ m n, embed m = embed n → m = n) ∧ embed 0 ≠ embed 1 := by
  exact ⟨NormalTree,normalMul,normalAtom,full_source_law,
    fun _ _ h => normalAtom_injective h,normalAtom_nontrivial⟩

end submission.Austin12087Trace

set_option autoImplicit false

namespace submission
abbrev CM := submission.Austin12087Trace.NormalTree
instance modelMagma : Magma CM := ⟨submission.Austin12087Trace.normalMul⟩
namespace CM
theorem tower_injective (m n : Nat)
    (h : submission.Austin12087Trace.normalAtom m = submission.Austin12087Trace.normalAtom n) : m = n :=
  submission.Austin12087Trace.normalAtom_injective h
end CM
theorem source_law : EquationLHS CM := submission.Austin12087Trace.full_source_law
end submission

theorem submission : Goal := by
  refine ⟨submission.CM,submission.modelMagma,submission.source_law,?_⟩
  intro h
  exact submission.Austin12087Trace.normalAtom_nontrivial
    (h (submission.Austin12087Trace.normalAtom 0) (submission.Austin12087Trace.normalAtom 1))

#print axioms submission
#print axioms submission.source_law
#print axioms submission.CM.tower_injective
#print axioms submission.Austin12087Trace.infinite_model
