{-# OPTIONS --cubical #-}

module ELib.ConcreteGroup.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.HITs.SetTruncation renaming (rec to recSetTrunc)
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv
open import ELib.Connectedness.Base
open import ELib.Connectedness.Properties

record ConcreteGroupStruct {ℓ} (A : Type ℓ) : Type ℓ where
  constructor struct-conc-group
  field
    pnt : A
    conn : (x : A) → ∥ pnt ≡ x ∥
    grpd : isSet (pnt ≡ pnt)

  isConn : isConnected A
  isConn x y = recPropTrunc propTruncIsProp (λ px → recPropTrunc propTruncIsProp (λ py → ∣ sym px ∙ py ∣) (conn y)) (conn x)

  isGrpd : isGroupoid A
  isGrpd x y = recPropTrunc isPropIsSet (λ px → recPropTrunc isPropIsSet (λ py → transport (λ i → isSet(px i ≡ py i)) (grpd)) (conn y)) (conn x)

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

-- Inclusion homomorphism from ZG to G
𝓩 : ∀ {ℓ} (G : ConcreteGroup {ℓ}) → ConcreteGroup.Ptd (Z G) →∙ ConcreteGroup.Ptd G
fst (𝓩 G) ((f , _) , _) = f (ConcreteGroup.pnt G)
snd (𝓩 G) = refl

typeof : ∀ {ℓ} {A : Type ℓ} → A → Type ℓ
typeof {ℓ} {A} a = A


PathP≡compPathR : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
                 → (PathP (λ i → x ≡ q i) p r) ≡ (p ∙ q ≡ r)
PathP≡compPathR p q r k = PathP (λ i → p i0 ≡ q (i ∨ k)) (λ j → compPath-filler p q k j) r

PathP≡compPathL : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
                 → (PathP (λ i → p i ≡ z) r q) ≡ (p ⁻¹ ∙ r ≡ q)
PathP≡compPathL p q r = _ ≡⟨ PathP≡doubleCompPathˡ p r q refl ⟩ cong (λ x → x ≡ q) (sym (compPath≡compPath' _ _))

lemma𝓩SetFibers : ∀ {ℓ} (G : ConcreteGroup {ℓ}) (x : ConcreteGroup.type G) → isSet (fiber (fst (𝓩 G)) x)
lemma𝓩SetFibers {ℓ} G x = recPropTrunc isPropIsSet (λ p → transport (λ i → isSet (fiber (fst (𝓩 G)) (p i))) lemma) (conn x) where
  open ConcreteGroup G
  test3 : ∀ {ℓ} {A : Type ℓ} {B C : A → Type ℓ} →
    (Σ[ x ∈ (Σ[ y ∈ A ] (B y)) ] C (fst x))
    ≡ (Σ[ x ∈ (Σ[ y ∈ A ] (C y)) ] B (fst x))
  test3 = isoToPath (iso (λ ((a , b) , c) → ((a , c) , b)) ((λ ((a , c) , b) → ((a , b) , c))) (λ _ → refl) (λ _ → refl))
  lemma : isSet (fiber (fst (𝓩 G)) pnt)
  lemma = transport (cong isSet (sym test3)) (isSetΣ (transport (cong isSet test3) (isSetΣ subLemma (λ _ → isProp→isSet (isPropIsEquiv _)))) λ _ → isProp→isSet propTruncIsProp) where
    subLemma : _
    subLemma (ϕ , p) (ψ , q) =
      transport (cong isProp (ua Σ≡))
      (transport (cong (λ x → isProp(Σ _ x)) (funExt λ _ → sym (PathP≡compPathL _ _ _)))
      λ π π' → ΣPathP (lama2 _ _ (cong sym (lama-1 q (snd π) ∙ sym (lama-1 q (snd π')))) , toPathP (isGrpd _ _ _ _ _ _))) where
        lama-1 : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p : a ≡ b} {q : b ≡ c} → (s : a ≡ c) → p ∙ q ≡ s → p ≡ s ∙ sym q
        lama-1 {a = a} {p = p} {q = q} = J (λ c q → (s : a ≡ c) → p ∙ q ≡ s → p ≡ s ∙ sym q) (λ _ r → rUnit _ ∙ r ∙ rUnit _) q
        lama0 : isSet(ϕ ≡ ψ)
        lama0 = transport (cong isSet funExtPath) (isSetΠ λ _ → isGrpd _ _)
        eval : (ϕ ≡ ψ) → (x : type) → (ϕ x ≡ ψ x)
        eval π x i = π i x
        lama2 : (π π' : ϕ ≡ ψ) → (eval π pnt) ≡ (eval π' pnt) → π ≡ π'
        lama2 π π' p = cong funExt (funExt λ x → recPropTrunc (isGrpd _ _ _ _) (λ q →
          transport (let path : (ϕ x ≡ ψ x) ≡ (ϕ pnt ≡ ψ pnt)
                         path = λ i → ϕ (q (~ i)) ≡ ψ (q (~ i)) in
                     let fin : path ∙ refl ∙ path ⁻¹ ≡ refl
                         fin = cong (λ x → path ∙ x) (sym (lUnit _)) ∙ lCancel _ in λ i → PathP (λ j → fin i j) (λ i → π i x) (λ i → π' i x)) (compPathP (cong (eval π) (sym q)) (compPathP p (cong (eval π') q)))) (conn x))
  
