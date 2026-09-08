import Model
namespace Austin12857
example (x y z : Carrier) : mul y (mul (mul x (mul y (mul z z))) y) = x :=
  equation12857 x y z
example (n k : Nat) : embed n = embed k → n = k := embed_injective n k
example (x y z : Carrier) :
    opposite (opposite y (opposite (opposite (opposite z z) y) x)) y = x :=
  equation33436 x y z
#print axioms infinite_model
#print axioms equation12857
#print axioms equation33436
#print axioms embed_injective
#print axioms confluent
#print axioms step_decreases
end Austin12857
