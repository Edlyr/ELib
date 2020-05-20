{-# OPTIONS --cubical #-}

module ELib.B1.Torsor where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Sigma
open import Cubical.Structures.Group
open import Cubical.Functions.FunExtEquiv
open import ELib.UsefulLemmas

RActionAxioms : {ℓ ℓ' : Level} → (G : Group {ℓ}) → (X : Type ℓ') → (X → ⟨ G ⟩ → X) → Type (ℓ-max ℓ ℓ')
RActionAxioms G X _⋆_ =
  ((x : X) (g g' : ⟨ G ⟩) → (x ⋆ g) ⋆ g' ≡ x ⋆ (g ⨀ g')) ×
  ((x : X) → x ⋆ id ≡ x) where
  _⨀_ = GroupLemmas.op G
  id = GroupLemmas.id G

isPropRActionAxioms : {ℓ ℓ' : Level} → (G : Group {ℓ}) → (X : Type ℓ') → isSet X → (r : X → ⟨ G ⟩ → X) → isProp(RActionAxioms G X r)
isPropRActionAxioms G X isSetX _⋆_ = isProp× (isPropΠ λ _ → isPropΠ2 λ _ _ → isSetX _ _) (isPropΠ λ _ → isSetX _ _)

RActionOn : {ℓ ℓ' : Level} → Group {ℓ} → Type ℓ' → Type (ℓ-max ℓ ℓ')
RActionOn G X = Σ[ _⋆_ ∈ (X → ⟨ G ⟩ → X) ] (RActionAxioms G X _⋆_)

RAction : {ℓ ℓ' : Level} → Group {ℓ} → Type (ℓ-max (ℓ-suc ℓ') ℓ)
RAction {ℓ' = ℓ'} G = Σ[ X ∈ Type ℓ' ] RActionOn G X

isTorsor : {ℓ ℓ' : Level} (G : Group {ℓ}) → (RAction {ℓ' = ℓ'} G) → Type (ℓ-max ℓ ℓ')
isTorsor G (X , _⋆_ , _ , _) = ∥ X ∥ × isSet X × ((x y : X) → isContr (Σ[ g ∈ ⟨ G ⟩ ] x ⋆ g ≡ y))

isPropIsTorsor : ∀ {ℓ ℓ' : Level} (G : Group {ℓ}) (r : RAction {ℓ' = ℓ'} G) → isProp(isTorsor G r)
isPropIsTorsor G r = isProp× propTruncIsProp (isProp× isPropIsSet (isPropΠ2 (λ _ _ → isPropIsContr)))

principalTorsor : ∀ {ℓ} (G : Group {ℓ}) → RAction G
principalTorsor G = ⟨ G ⟩ , _⨀_ , assocG , λ x → sym (rUnitG x) where
  _⨀_ = GroupLemmas.op G
  assocG = GroupLemmas.assoc G
  rUnitG = GroupLemmas.rUnit G

isTorsorPrincipalTorsor : ∀ {ℓ} (G : Group {ℓ}) → isTorsor G (principalTorsor G)
isTorsorPrincipalTorsor G =
  ∣ id ∣ , isSetG ,
  λ x y → (trans x y , transProof x y) ,
  λ (g , p) → ΣProp≡ (λ _ → isSetG _ _) (simplL x (transProof x y ∙ sym p)) where
    open GroupLemmas G renaming (set to isSetG ; assoc to assocG ; lUnit to lUnitG ; rCancel to rCancelG)
    trans : (x y : ⟨ G ⟩) → ⟨ G ⟩
    trans x y = inv x ⨀ y
    transProof : (x y : ⟨ G ⟩) → x ⨀ trans x y ≡ y
    transProof x y = sym (assocG _ _ _) ∙ cong (λ r → r ⨀ y) (rCancelG x) ∙ sym (lUnitG y)

module TorsorEquality {ℓ ℓ' : Level} (Ggrp : Group {ℓ}) (T¹ T² : RAction {ℓ' = ℓ'} Ggrp) (tors¹ : isTorsor Ggrp T¹) (tors² : isTorsor Ggrp T²) where
  module G = GroupLemmas Ggrp
  X¹ = fst T¹
  X² = fst T²
  _⋆¹_ = fst (snd T¹)
  _⋆²_ = fst (snd T²)
  isSetX² : isSet X²
  isSetX² = fst (snd tors²)

  equalityCaracType : Type (ℓ-max ℓ ℓ')
  equalityCaracType = (Σ[ f ∈ X¹ ≃ X² ] ((x : X¹) (g : ⟨ Ggrp ⟩) → equivFun f (x ⋆¹ g) ≡ equivFun f x ⋆² g))
  T¹≃T² = equalityCaracType

  equiv0 : (T¹ ≡ T²) ≃ (Σ[ p ∈ X¹ ≡ X² ] PathP (λ i → RActionOn Ggrp (p i)) (snd T¹) (snd T²))
  equiv0 = isoToEquiv (iso (λ p → cong fst p , cong snd p) ΣPathP (λ _ → refl) λ _ → refl)
    -- Σ≡ could not be used instead of equiv0 because of universe level issues in the definition of Σ≡
    -- it may be a good idea to relax the level hypothesis in the definiton of Σ≡

  equiv1 : (Σ[ p ∈ X¹ ≡ X² ] PathP (λ i → RActionOn Ggrp (p i)) (snd T¹) (snd T²)) ≃ (Σ[ p ∈ X¹ ≡ X² ] PathP ((λ i → p i → ⟨ Ggrp ⟩ → p i)) _⋆¹_ _⋆²_)
  equiv1 =
    (congΣEquiv λ p → compEquiv (PathP≃Path _ _ _) (compEquiv
      (isoToEquiv (iso
        (cong fst)
        (λ p → ΣProp≡ (isPropRActionAxioms Ggrp X² isSetX²) p)
        (λ p → refl)
        λ p → cong ΣPathP (ΣProp≡ (λ r → transport (cong isProp (sym (PathP≡Path _ _ _))) (isProp→isSet (isPropRActionAxioms Ggrp X² isSetX² (r i1)) _ _)) refl)
      ))
    (invEquiv (PathP≃Path _ _ _))))

  preEquiv2 : (p : X¹ ≡ X²) → (PathP (λ i → p i → ⟨ Ggrp ⟩ → p i) _⋆¹_ _⋆²_) ≡ ((x : X¹) (g : ⟨ Ggrp ⟩) → transport p (x ⋆¹ g) ≡ (transport p x) ⋆² g)
  preEquiv2 p =
    PathP (λ i → p i → ⟨ Ggrp ⟩ → p i) _⋆¹_ _⋆²_
      ≡⟨ PathP→ (Type ℓ') (λ x → x) (λ x → ⟨ Ggrp ⟩ → x) X¹ X² p _⋆¹_ _⋆²_ ⟩
    ((x : X¹) → transport (cong (λ r → ⟨ Ggrp ⟩ → r) p) (_⋆¹_ x) ≡ _⋆²_ (transport p x))
      ≡⟨ (λ i → (x : X¹) → lemma x i ≡ _⋆²_ (transport p x)) ⟩
    ((x : X¹) → (λ g → transport p (x ⋆¹ g)) ≡ _⋆²_ (transport p x))
      ≡⟨ sym (λ i → (x : X¹) → funExtPath {f = λ g → transport p (x ⋆¹ g)} {g = _⋆²_ (transport p x)} i) ⟩
    ((x : X¹) (g : ⟨ Ggrp ⟩) → transport p (x ⋆¹ g) ≡ (transport p x) ⋆² g) ∎
    where
    lemma : (x : X¹) → transport (cong (λ r → ⟨ Ggrp ⟩ → r) p) (_⋆¹_ x) ≡ (λ g → transport p (x ⋆¹ g))
    lemma x = transport→R (Type ℓ') ⟨ Ggrp ⟩ (λ x → x) X¹ X² p (_⋆¹_ x)

  equiv2 : (Σ[ p ∈ X¹ ≡ X² ] PathP ((λ i → p i → ⟨ Ggrp ⟩ → p i)) _⋆¹_ _⋆²_) ≃
    (Σ[ p ∈ X¹ ≡ X² ] ((x : X¹) (g : ⟨ Ggrp ⟩) → transport p (x ⋆¹ g) ≡ (transport p x) ⋆² g))
  equiv2 = congΣEquiv λ p → pathToEquiv (preEquiv2 p)

  equiv3 : (Σ[ p ∈ X¹ ≡ X² ] ((x : X¹) (g : ⟨ Ggrp ⟩) → transport p (x ⋆¹ g) ≡ (transport p x) ⋆² g)) ≃ T¹≃T²
  equiv3 = isoToEquiv (iso
    (λ P → pathToEquiv (fst P) , λ x g → sym (transport≡pathToEquiv (fst P) _) ∙ snd P x g ∙ cong (λ y → y ⋆² g) (transport≡pathToEquiv (fst P) _))
    (λ Q → ua (fst Q) , λ x g → uaβ (fst Q) _ ∙ snd Q x g ∙ cong (λ y → y ⋆² g) (sym (uaβ (fst Q) _)))
    (λ Q → ΣProp≡ (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetX² _ _) (pathToEquiv-ua _))
    (λ P → ΣProp≡ (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetX² _ _) (ua-pathToEquiv _))
   )

  abstract
    torsorEqualityEquiv : (T¹ ≡ T²) ≃ T¹≃T²
    torsorEqualityEquiv = compEquiv equiv0 (compEquiv equiv1 (compEquiv equiv2 equiv3))

    torsorEqualityEquivFst : (p : T¹ ≡ T²) → (fst (equivFun torsorEqualityEquiv p)) ≡ pathToEquiv (cong fst p)
    torsorEqualityEquivFst p = refl

module TorsorLoopspace  {ℓ : Level} (Ggrp : Group {ℓ}) where
  Torsor : ∀ {ℓ'} → Type (ℓ-max (ℓ-suc ℓ') ℓ)
  Torsor {ℓ'} = Σ (RAction {ℓ' = ℓ'} Ggrp) (isTorsor Ggrp)

  _T≃T_ : ∀ {ℓ'} (T¹ T² : Torsor {ℓ' = ℓ'}) → Type (ℓ-max ℓ ℓ')
  _T≃T_ T¹ T² = TorsorEquality.T¹≃T² Ggrp (fst T¹) (fst T²) (snd T¹) (snd T²)

  torsorEqCarac : ∀ {ℓ'} (T¹ T² : Torsor {ℓ' = ℓ'}) → (fst T¹ ≡ fst T²) ≃ (T¹ T≃T T²)
  torsorEqCarac {ℓ'} T¹ T² = TorsorEquality.torsorEqualityEquiv Ggrp (fst T¹) (fst T²) (snd T¹) (snd T²)

  comp≃T : ∀ {ℓ'} {T¹ T² T³ : Torsor {ℓ' = ℓ'}} → (T¹ T≃T T²) → (T² T≃T T³) → (T¹ T≃T T³)
  comp≃T {ℓ'} {T¹} {T²} {T³} (f , p) (f' , p') = compEquiv f f' , λ x g → cong (equivFun f') (p _ _) ∙ p' _ _

  torsorEqCaracMorph : ∀ {ℓ'} (T¹ T² T³ : Torsor {ℓ' = ℓ'}) (p : fst T¹ ≡ fst T²) (q : fst T² ≡ fst T³) →
    equivFun (torsorEqCarac T¹ T³) (p ∙ q) ≡ comp≃T {T¹ = T¹} {T² = T²} {T³ = T³} (equivFun (torsorEqCarac T¹ T²) p) (equivFun (torsorEqCarac T² T³) q)
  torsorEqCaracMorph {ℓ'} T¹ T² T³ p q = ΣProp≡ (λ x → isPropΠ λ _ → isPropΠ λ _ → fst (snd (snd T³)) _ _)
    (lemma-p∙q ∙ cong pathToEquiv (cong-∙ _ p q) ∙
    pathToEquiv∙ (cong fst p) (cong fst q) ∙ λ i → compEquiv (lemma-p (~ i)) (lemma-q (~ i))) where
      lemma-p = TorsorEquality.torsorEqualityEquivFst Ggrp (fst T¹) (fst T²) (snd T¹) (snd T²) p
      lemma-q = TorsorEquality.torsorEqualityEquivFst Ggrp (fst T²) (fst T³) (snd T²) (snd T³) q
      lemma-p∙q = TorsorEquality.torsorEqualityEquivFst Ggrp (fst T¹) (fst T³) (snd T¹) (snd T³) (p ∙ q)
