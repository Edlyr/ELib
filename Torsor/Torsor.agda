{-# OPTIONS --cubical #-}

module ELib.Torsor.Torsor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Sigma
open import Cubical.Structures.Group
open import Cubical.Functions.FunExtEquiv
open import ELib.UsefulLemmas

open import Cubical.Structures.Auto
open import Cubical.Structures.Axioms
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws hiding (assoc)

private
  variable
    ℓ ℓ' : Level

record IsTorsor (G : Group {ℓ}) (X : Type ℓ) (_⋆_ : X → ⟨ G ⟩ → X) : Type ℓ where
  constructor istorsor
  private
    module G = Group G
  field
    is-set : isSet X
    inhabited : ∥ X ∥
    assoc : (x : X) (g g' : ⟨ G ⟩) → (x ⋆ g) ⋆ g' ≡ x ⋆ (g G.+ g')
    neutral : (x : X) → x ⋆ G.0g ≡ x
    trans : (x y : X) → ⟨ G ⟩
    trans-eq : (x y : X) → x ⋆ trans x y ≡ y
    trans-unique : (x y : X) (g : ⟨ G ⟩) → x ⋆ g ≡ y → trans x y ≡ g

record Torsor (G : Group {ℓ}) : Type (ℓ-suc ℓ) where
  constructor torsor
  module G = Group G
  field
    Carrier : Type ℓ
    _⋆_ : Carrier → ⟨ G ⟩ → Carrier
    isTorsor : IsTorsor G Carrier _⋆_

  open IsTorsor isTorsor public

record TorsorEquiv {G : Group {ℓ}} (T T' : Torsor G) : Type (ℓ-suc ℓ) where
  constructor t-equiv
  module T = Torsor T
  module T' = Torsor T'
  field
    eq : T.Carrier ≃ T'.Carrier
    hom : (x : T.Carrier) (g : ⟨ G ⟩) → equivFun eq (x T.⋆ g) ≡ (equivFun eq x T'.⋆ g)

isPropIsTorsor : {G : Group {ℓ}} {X : Type ℓ} {_⋆_ : X → ⟨ G ⟩ → X} → isProp (IsTorsor G X _⋆_)
isPropIsTorsor {G = G} {X = X} {_⋆_ = _⋆_} = isOfHLevelRespectEquiv 1 equiv isPropType where
  module G = Group G
  type : Type _
  type =
    Σ[ is-set ∈ isSet X ]
    Σ[ inhabited ∈ ∥ X ∥ ]
    Σ[ assoc ∈ ((x : X) (g g' : ⟨ G ⟩) → (x ⋆ g) ⋆ g' ≡ x ⋆ (g G.+ g')) ]
    Σ[ neutral ∈ ((x : X) → x ⋆ G.0g ≡ x) ]
    Σ[ trans ∈ ((x y : X) → ⟨ G ⟩) ]
    ((x y : X) → x ⋆ trans x y ≡ y) ×
    ((x y : X) (g : ⟨ G ⟩) → x ⋆ g ≡ y → trans x y ≡ g)

  isPropType : isProp type
  isPropType = isPropΣ isPropIsSet (λ is-set → isProp×
    propTruncIsProp (isProp×
    (isPropΠ λ _ → isPropΠ2 λ _ _ → is-set _ _) (isProp×
    (isPropΠ λ _ → is-set _ _) λ trans1 trans2 → Σ≡Prop (λ trans → isProp×
      (isPropΠ2 λ _ _ → is-set _ _) (isPropΠ2 λ _ _ → isPropΠ λ _ → isPropΠ λ _ → G.is-set _ _))
      (funExt λ x → funExt λ y → trans1 .snd .snd x y _ (trans2 .snd .fst x y)))))

  equiv : type ≃ IsTorsor G X _⋆_ 
  equiv = isoToEquiv (iso
    (λ (is-set , inhabited , assoc , neutral , trans , trans-eq , trans-unique) → istorsor is-set inhabited assoc neutral trans trans-eq trans-unique)
    (λ (istorsor is-set inhabited assoc neutral trans trans-eq trans-unique) → is-set , inhabited , assoc , neutral , trans , trans-eq , trans-unique)
    (λ _ → refl) λ _ → refl)

torsorEq : {G : Group {ℓ}} {T1 T2 : Torsor G} (p : Torsor.Carrier T1 ≡ Torsor.Carrier T2) →
  PathP (λ i → p i → ⟨ G ⟩ → p i) (Torsor._⋆_ T1) (Torsor._⋆_ T2) → T1 ≡ T2
torsorEq {G = G} {T1 = T1} {T2 = T2} p q i = torsor (p i) (q i) (lemma i) where
  open Torsor
  lemma : PathP (λ i → IsTorsor G (p i) (q i)) (isTorsor T1) (isTorsor T2)
  lemma = toPathP (isPropIsTorsor _ _)

principalTorsor : (G : Group {ℓ}) → Torsor G
principalTorsor G = torsor ⟨ G ⟩ _+_ (istorsor is-set ∣ 0g ∣ (λ x y z → sym (assoc x y z)) rid (λ x y → - x + y)
  (λ x y → assoc _ _ _ ∙ cong (_+ y) (invr x) ∙ lid y)
  λ x y g p → sym (sym (lid g) ∙ cong (_+ g) (sym (invl x)) ∙ sym (assoc _ _ _) ∙ cong (- x +_) p))
  where open Group G

trivialize : {G : Group {ℓ}} (T : Torsor G) (t₀ : Torsor.Carrier T) → TorsorEquiv (principalTorsor G) T
trivialize {G = G} T t₀ = t-equiv (isoToEquiv (iso f g sec retr)) lemma where
  module T = Torsor T
  module P = Torsor (principalTorsor G)
  open Group G
  f : P.Carrier → T.Carrier
  f g = t₀ T.⋆ g

  g : T.Carrier → P.Carrier
  g t = T.trans t₀ t

  sec : section f g
  sec = T.trans-eq _

  retr : retract f g
  retr g = T.trans-unique _ _ _ refl

  lemma : (g g' : ⟨ G ⟩) → f (g + g') ≡ f g T.⋆ g'
  lemma g g' = sym (T.assoc _ _ _)
  

module TorsorΣTheory {ℓ : Level} (G : Group {ℓ}) where
  open Group G
  RawRActionStruct : Type ℓ → Type _
  RawRActionStruct X = X → ⟨ G ⟩ → X

  TorsorAxioms : (X : Type ℓ) → (X → ⟨ G ⟩ → X) → Type ℓ
  TorsorAxioms X _⋆_ =
    isSet X ×
    ∥ X ∥ ×
    ((x : X) (g g' : ⟨ G ⟩) → (x ⋆ g) ⋆ g' ≡ x ⋆ (g + g')) ×
    ((x : X) → x ⋆ 0g ≡ x) ×
    ((x y : X) → isContr (Σ[ g ∈ ⟨ G ⟩ ] x ⋆ g ≡ y))

  isPropTorsorAxioms : (X : Type ℓ) (s : X → ⟨ G ⟩ → X) → isProp (TorsorAxioms X s)
  isPropTorsorAxioms X _⋆_ = isPropΣ isPropIsSet (λ set → isProp×
    propTruncIsProp (isProp×
    (isPropΠ λ _ → isPropΠ2 λ _ _ → set _ _) (isProp×
    (isPropΠ λ _ → set _ _)
    (isPropΠ2 λ _ _ → isPropIsContr))))

  TorsorStructure : Type ℓ → Type _
  TorsorStructure = AxiomsStructure RawRActionStruct TorsorAxioms

  TorsorEquivStr : StrEquiv TorsorStructure _
  TorsorEquivStr = AxiomsEquivStr (AutoEquivStr RawRActionStruct) TorsorAxioms

  TorsorUnivalentStr : UnivalentStr TorsorStructure TorsorEquivStr
  TorsorUnivalentStr = axiomsUnivalentStr _ isPropTorsorAxioms (autoUnivalentStr RawRActionStruct)

  TorsorΣ = TypeWithStr _ TorsorStructure

  TorsorΣPath : (T T' : TorsorΣ) → T ≃[ TorsorEquivStr ] T' ≃ (T ≡ T')
  TorsorΣPath = SIP TorsorUnivalentStr
  ------------

  Torsor→TorsorΣ : Torsor G → TorsorΣ
  Torsor→TorsorΣ (torsor Carrier _⋆_ (istorsor is-set inhabited assoc neutral trans trans-eq trans-unique)) =
    Carrier , _⋆_ , is-set , inhabited , assoc , neutral ,
    λ x y → (trans x y , trans-eq x y) , λ α → Σ≡Prop (λ _ → is-set _ _) (trans-unique _ _ _ (snd α))

  TorsorΣ→Torsor : TorsorΣ → Torsor G
  TorsorΣ→Torsor (Carrier , _⋆_ , is-set , inhabited , assoc , neutral , contr) = torsor Carrier _⋆_
    (istorsor is-set inhabited assoc neutral
    (λ x y → contr x y .fst .fst) (λ x y → contr x y .fst .snd) λ x y g p → cong fst (contr x y .snd (g , p)))

  TorsorIsoTorsorΣ : Iso (Torsor G) TorsorΣ
  TorsorIsoTorsorΣ = iso Torsor→TorsorΣ TorsorΣ→Torsor
    (λ _ → ΣPathP (refl , Σ≡Prop (isPropTorsorAxioms _) refl))
    (λ _ → torsorEq refl refl)

  TorsorEquivΣ : (T T' : Torsor G) → Type ℓ
  TorsorEquivΣ T T' = Torsor→TorsorΣ T ≃[ TorsorEquivStr ] Torsor→TorsorΣ T'

  TorsorIsoΣPath : {T T' : Torsor G} → Iso (TorsorEquiv T T') (TorsorEquivΣ T T')
  TorsorIsoΣPath = iso
    (λ (t-equiv eq hom) → eq , hom)
    (λ (eq , hom) → t-equiv eq hom)
    (λ _ → refl) λ _ → refl

  TorsorPath : (T T' : Torsor G) → (TorsorEquiv T T') ≃ (T ≡ T')
  TorsorPath T T' =
    TorsorEquiv T T' ≃⟨ isoToEquiv TorsorIsoΣPath ⟩
    TorsorEquivΣ T T' ≃⟨ TorsorΣPath _ _ ⟩
    Torsor→TorsorΣ T ≡ Torsor→TorsorΣ T' ≃⟨ isoToEquiv (invIso (congIso TorsorIsoTorsorΣ)) ⟩
    T ≡ T' ■

open TorsorΣTheory using (TorsorPath) public

uaTorsor : {G : Group {ℓ}} {T T' : Torsor G} → TorsorEquiv T T' → T ≡ T'
uaTorsor = equivFun (TorsorPath _ _ _)

carac-uaTorsor : {G : Group {ℓ}} {T T' : Torsor G} (f : TorsorEquiv T T') → cong Torsor.Carrier (uaTorsor f) ≡ ua (TorsorEquiv.eq f)
carac-uaTorsor (t-equiv f m) = refl ∙∙ ua f ∙∙ refl ≡⟨ sym (rUnit (ua f)) ⟩ ua f ∎
