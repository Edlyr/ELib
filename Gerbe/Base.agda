{-# OPTIONS --cubical #-}

module ELib.Gerbe.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import ELib.UsefulLemmas

private
  variable
    ℓ ℓ' ℓ'' : Level

isSetGroupEquiv : ∀ {ℓ ℓ' : Level} (G₁ : Group {ℓ}) (G₂ : Group {ℓ'}) → isSet (GroupEquiv G₁ G₂)
isSetGroupEquiv G₁ G₂ = isOfHLevelRespectEquiv 2 lemma
  (isSetΣ (isSetΣ (isOfHLevelΠ 2 λ _ → Group.is-set G₂) λ _ → isProp→isSet (isPropIsEquiv _)) λ _ → isProp→isSet (isPropIsGroupHom G₁ G₂))
  where
  open GroupEquiv
  X₁ = Group.Carrier G₁
  X₂ = Group.Carrier G₂
  lemma : (Σ[ f ∈ X₁ ≃ X₂ ] isGroupHom G₁ G₂ (equivFun f)) ≃ GroupEquiv G₁ G₂
  lemma = isoToEquiv (iso (λ (f , m) → groupequiv f m) (λ (groupequiv f m) → f , m) (λ _ → refl) λ _ → refl)

-------------------

record IsGerbe (X : Type ℓ) : Type ℓ where
  constructor isgerbe
  field
    inhabited : ∥ X ∥
    grpd : isGroupoid X
    conn : (x y : X) → ∥ x ≡ y ∥
    comm : (x : X) → (p q : x ≡ x) → p ∙ q ≡ q ∙ p

record Gerbe : Type (ℓ-suc ℓ) where
  constructor gerbe
  field
    Carrier : Type ℓ
    isGerbe : IsGerbe Carrier

  open IsGerbe isGerbe public

⟨_⟩ : Gerbe → Type ℓ
⟨_⟩ = Gerbe.Carrier

isPropIsGerbe : {X : Type ℓ} → isProp (IsGerbe X)
isPropIsGerbe {X = X} g1 g2 i = isgerbe
  (propTruncIsProp g1.inhabited g2.inhabited i)
  (isPropIsGroupoid g1.grpd g2.grpd i)
  (isPropΠ2 (λ _ _ → propTruncIsProp) g1.conn g2.conn i)
  ((isPropΠ (λ x → isPropΠ2 λ p q → g1.grpd _ _ _ _)) g1.comm g2.comm i) where
  module g1 = IsGerbe g1
  module g2 = IsGerbe g2

gerbeEq : {G H : Gerbe {ℓ}} → (Gerbe.Carrier G ≡ Gerbe.Carrier H) → G ≡ H
gerbeEq {G = G} {H = H} p i = gerbe (p i) (grb i) where
  open Gerbe
  grb : PathP (λ i → IsGerbe (p i)) (isGerbe G) (isGerbe H)
  grb = toPathP (isPropIsGerbe _ _)

{-
isGerbe : Type ℓ → Type ℓ
isGerbe X = ∥ X ∥ × isGroupoid X × ((x y : X) → ∥ x ≡ y ∥) × ((x : X) → (p q : x ≡ x) → p ∙ q ≡ q ∙ p)

isPropIsGerbe : (X : Type ℓ) → isProp (isGerbe X)
isPropIsGerbe X =
  isProp×
    propTruncIsProp
    (isPropΣ
      isPropIsGroupoid
      (λ grpd → isProp×
        (isPropΠ2 λ x y → propTruncIsProp)
        (isPropΠ λ x → isPropΠ2 λ p q → grpd x x (p ∙ q) (q ∙ p))
      )
    )

Gerbe : Type (ℓ-suc ℓ)
Gerbe {ℓ} = TypeWithStr ℓ isGerbe

⟨_⟩ : Gerbe → Type ℓ
⟨_⟩ = fst

gerbe-inhabited : (G : Gerbe {ℓ}) → ∥ ⟨ G ⟩ ∥
gerbe-inhabited G = fst (snd G)

gerbe-grpd : (G : Gerbe {ℓ}) → isGroupoid ⟨ G ⟩
gerbe-grpd G = fst (snd (snd G))

gerbe-conn : (G : Gerbe {ℓ}) → ((x y : ⟨ G ⟩) → ∥ x ≡ y ∥)
gerbe-conn G = fst (snd (snd (snd G)))

gerbe-comm : (G : Gerbe {ℓ}) → ((x : ⟨ G ⟩) → (p q : x ≡ x) → p ∙ q ≡ q ∙ p)
gerbe-comm G = snd (snd (snd (snd G)))

-}
π : (G : Gerbe {ℓ}) (x : ⟨ G ⟩) → AbGroup {ℓ}
π G x = makeAbGroup (refl {x = x}) _∙_ sym (Gerbe.grpd G _ _) assoc (λ x → sym (rUnit x)) rCancel (Gerbe.comm G x)


module S (G : Gerbe {ℓ}) where
  X = ⟨ G ⟩

  s-type : (x y : X) → Type ℓ
  s-type x y = Σ[ f ∈ ((x ≡ x) ≃ (y ≡ y)) ] ((p : x ≡ y) (q : x ≡ x) → f .fst q ≡ sym p ∙ q ∙ p)

  abstract
    s-def : (x y : X) → s-type x y
    s-def x y = fst (T x y) where
      T : (x y : X) → isContr (s-type x y)
      T x y = recPropTrunc isPropIsContr (λ x≡y → transport (λ i → isContr (s-type x (x≡y i))) base-case) (Gerbe.conn G x y) where
        base-case : isContr (s-type x x)
        base-case = center , contr where
          center : s-type x x
          center = idEquiv _ , λ p q → sym (cong (λ r → (sym p) ∙ r) (Gerbe.comm G x q p) ∙ compPathl-cancel _ _)

          contr : (f : s-type x x) → center ≡ f
          contr (f , !) = Σ≡Prop (λ f → isPropΠ2 λ p q → Gerbe.grpd G _ _ _ _) id≡f where
            id≡f : fst center ≡ f
            id≡f = equivEq _ _ (funExt λ q → rUnit _ ∙ lUnit _ ∙ sym (! refl q))

    s : (x y : X) → (x ≡ x) → (y ≡ y)
    s x y = s-def x y .fst .fst

    isEquiv-s : (x y : X) → isEquiv (s x y)
    isEquiv-s x y = s-def x y .fst .snd

    s-eq : (x y : X) → (x ≡ x) ≃ (y ≡ y)
    s-eq x y = s x y , isEquiv-s x y

    s-carac : (x y : X) (p : x ≡ y) (q : x ≡ x) → s x y q ≡ sym p ∙ q ∙ p
    s-carac x y p q = s-def x y .snd p q

    s-id : (x : X) → s x x ≡ λ q → q
    s-id x = funExt λ q → s-carac x x refl q ∙ sym (rUnit _ ∙ lUnit _)

    s-inv : (x y : X) → invEq (s-eq x y) ≡ s y x
    s-inv x y = recPropTrunc prop (λ p → transport (λ i → invEq (s-eq x (p i)) ≡ s (p i) x) lemma) (Gerbe.conn G x y) where
      prop : isProp (invEq (s-eq x y) ≡ s y x)
      prop = isOfHLevelPathP' 1 (isSetΠ λ _ → Gerbe.grpd G _ _) _ _

      lemma : invEq (s-eq x x) ≡ s x x
      lemma =
        invEq (s-eq x x)
          ≡⟨ cong invEq (equivEq (s-eq x x) (idEquiv _) (s-id x)) ⟩
        invEq (idEquiv _)
          ≡⟨ cong equivFun (invEquivIdEquiv _) ⟩
        (λ q → q)
          ≡⟨ sym (s-id x) ⟩
        s x x ∎
        
    isHom-s : (x y : X) → isGroupHom (AbGroup→Group (π G x)) (AbGroup→Group (π G y)) (s x y)
    isHom-s x y = recPropTrunc prop (λ p →
      transport (λ i → isGroupHom (AbGroup→Group (π G x)) (AbGroup→Group (π G (p i))) (s x (p i))) lemma)
      (Gerbe.conn G x y) where
      prop : isProp _
      prop = isPropIsGroupHom (AbGroup→Group (π G x)) (AbGroup→Group (π G y))

      lemma : isGroupHom (AbGroup→Group (π G x)) (AbGroup→Group (π G x)) (s x x)
      lemma p q =
        s x x (p ∙ q)
          ≡⟨ (λ i → s-id x i (p ∙ q)) ⟩
        p ∙ q
          ≡⟨ (λ i → s-id x (~ i) p ∙ s-id x (~ i) q) ⟩
        s x x p ∙ s x x q ∎

      s-hom : (x y : X) → AbGroupHom (π G x) (π G y)
      s-hom x y = grouphom (s x y) (isHom-s x y)

      s-groupEquiv : (x y : X) → AbGroupEquiv (π G x) (π G y)
      s-groupEquiv x y = groupequiv (s-eq x y) (isHom-s x y)
