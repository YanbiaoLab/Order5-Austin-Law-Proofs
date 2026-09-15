prelude
import Init.Classical
import Init.Data.Nat.Lemmas
import Init.RCases
import ExportLineageSyntaxTransportTriangles
set_option Elab.async false
set_option autoImplicit false
set_option Elab.async false

namespace submission.Equation22446Lineage
open submission.Equation22446Guarded

def triangleSize (p a q : T) : Nat := nodes p + nodes a + nodes q

 

theorem joint_triangle_exclusion (n : Nat) :
    (∀ p a q, triangleSize p a q = n → Image p q → Column p a → Image a q → False) ∧
    (∀ u p a, triangleSize p a u = n → Column u p → Column p a → Column u a → False) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have image_here : ∀ p a q, triangleSize p a q = n →
          Image p q → Column p a → Image a q → False := by
        intro p a q hn hi hc hj
        cases hi with
        | square p => exact column_square_image_false hc hj
        | literal p z => exact image_literal_triangle_false hc hj rfl
        | @transport u p v hk hl =>
            have hm := image_transport_common_column hk hl hc hj rfl
            have hs : triangleSize p a u < n := by
              rw [←hn]
              exact Nat.add_lt_add_left (pair_left .zero u v) (nodes p + nodes a)
            exact (ih _ hs).2 u p a rfl hk hc hm
        | inverseFollowup v => exact image_inverse_triangle_false hc hj rfl
        | returnFollowup hk => exact image_rotated_pair_triangle_false hc hj rfl
        | cycleFollowup hs hk hl =>
            rw [cycle_followup_input_eq hs hk hl] at hc
            exact image_rotated_pair_triangle_false hc hj rfl
      refine ⟨image_here,?_⟩
      intro u p a hn hc hd he
      have hi := column_triangle_inverse_origin hc hd he
      cases he with
      | ancestry hl => exact column_chain_ancestral_false hl hc hd
      | literal u y =>
          have hp := principal_pair_target hd hi
          have hor := principal_pair_inner_image hd hi
          have hcp : Column y p := by rw [hp]; exact column_completed hor
          have hy := pair_left .zero y (S u)
          have hs : triangleSize y p (S u) < triangleSize p (P y (S u)) u := by
            unfold triangleSize
            rw [nodes_S,Nat.add_comm (nodes y) (nodes p)]
            exact Nat.add_lt_add_right (Nat.add_lt_add_left hy (nodes p)) (nodes u)
          have hs' : triangleSize y p (S u) < n := by rwa [hn] at hs
          exact (ih _ hs').1 y p (S u) rfl hor hcp hi
      | inverseImage hj =>
          have hn' : triangleSize p a (S u) = n := by
            unfold triangleSize
            rw [nodes_S]
            exact hn
          exact image_here p a (S u) hn' hi hd hj

theorem image_triangle_false {p a q : T} (hi : Image p q) (hc : Column p a)
    (hj : Image a q) : False :=
  (joint_triangle_exclusion (triangleSize p a q)).1 p a q rfl hi hc hj

theorem column_triangle_false {u p a : T} (hc : Column u p) (hd : Column p a)
    (he : Column u a) : False :=
  (joint_triangle_exclusion (triangleSize p a u)).2 u p a rfl hc hd he

end submission.Equation22446Lineage
