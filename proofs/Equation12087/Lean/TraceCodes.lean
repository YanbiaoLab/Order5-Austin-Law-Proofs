prelude
import TraceColumns
set_option autoImplicit false
namespace Austin12087Trace
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

end Austin12087Trace
#print axioms Austin12087Trace.leftCode_witness
#print axioms Austin12087Trace.rightCode_witness
#print axioms Austin12087Trace.leftCode_sound
#print axioms Austin12087Trace.rightCode_sound
#print axioms Austin12087Trace.decode_source
