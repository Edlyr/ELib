{-# OPTIONS --cubical #-}

module ELib.ConcreteGroup.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation
open import ELib.Connectedness.Base
open import ELib.Connectedness.Properties

record ConcreteGroupStruct {ℓ} (A : Type ℓ) : Type ℓ where
  constructor struct-conc-group
  field
    pnt : A
    conn : (x : A) → ∥ pnt ≡ x ∥
    grpd : isSet (pnt ≡ pnt)

  isConn : isConnected A
  isConn x y = rec propTruncIsProp (λ px → (rec propTruncIsProp (λ py → ∣ sym px ∙ py ∣) (conn y))) (conn x)

  isGrpd : isGroupoid A
  isGrpd x y = rec isPropIsSet (λ px → rec isPropIsSet (λ py → transport (λ i → isSet(px i ≡ py i)) (grpd)) (conn y)) (conn x)
  
record ConcreteGroup {ℓ} : Type (ℓ-suc ℓ) where
  constructor conc-group
  field
    type : Type ℓ
    struct : ConcreteGroupStruct type
  open ConcreteGroupStruct struct public
  
  Ptd : Pointed ℓ
  Ptd = (type , pnt)



-- Group of automorphisms of a point "a" in a type "A"
Aut : ∀ {ℓ} {A : Type ℓ} (a : A) → isGroupoid A → ConcreteGroup {ℓ}
Aut {ℓ} {A} a p = conc-group (fst Ptd) (struct-conc-group (snd Ptd)
  (snd (isConnectedConnectedComponent (A , a))) (isOfHLevelConnectedComponent ((A , a)) 3 p _ _)) where
  Ptd = connectedComponent (A , a)

isAbelian : ∀ {ℓ} → ConcreteGroup {ℓ} → Type ℓ
isAbelian G = (x y : pnt ≡ pnt) → (x ∙ y) ≡ (y ∙ x) where open ConcreteGroup G

isPropIsAbelian : ∀ {ℓ} (G : ConcreteGroup {ℓ}) → isProp (isAbelian G)
isPropIsAbelian G = isPropΠ2 λ _ _ → isGrpd _ _ _ _ where open ConcreteGroup G

-- Concrete definition of the center of a group
Z : ∀ {ℓ} → ConcreteGroup {ℓ} → ConcreteGroup {ℓ}
Z G = Aut {A = (type ≃ type)} (idEquiv _) (isOfHLevel≃ 3 isGrpd isGrpd) where
  open ConcreteGroup G

𝓩 : ∀ {ℓ} → (G : ConcreteGroup {ℓ}) → ConcreteGroup.Ptd (Z G) →∙ ConcreteGroup.Ptd G
fst (𝓩 G) ((f , _) , _) = f (ConcreteGroup.pnt G)
snd (𝓩 G) = refl
