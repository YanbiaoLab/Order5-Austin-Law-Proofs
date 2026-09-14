prelude
import TraceSecondVLowWMax
set_option autoImplicit false

namespace Austin12087Trace
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

end Austin12087Trace
#print axioms Austin12087Trace.semantic_edge
#print axioms Austin12087Trace.semantic_return
