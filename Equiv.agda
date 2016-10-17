data _≡_ {A : Set} (a : A) : A → Set where
    refl : _≡_ a a


data Equiv (a b : Set) : Set where
    eq : (to   : a → b)
       → (from : b → a)
       → ((x : a) → from (to x) ≡ x)
       → ((y : b) → to (from y) ≡ y)
       → Equiv a b

data B1 : Set where T : B1; F : B1
data B2 : Set where O : B2; Z : B2

iso : Equiv B1 B2
iso = eq f g fogid gofid
    where f     = λ { T → O; F → Z }
          g     = λ { O → T; Z → F }
          fogid = λ { T → refl; F → refl }
          gofid = λ { O → refl; Z → refl }
