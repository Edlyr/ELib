{-# OPTIONS --cubical #-}

module ELib.Torsor.Base where

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
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)

private
  variable
    ℓ ℓ' : Level

record IsTorsor (G : Group {ℓ}) (X : Type ℓ') (_⋆_ : X → ⟨ G ⟩ → X) : Type (ℓ-max ℓ ℓ') where
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

record Torsor (G : Group {ℓ}) {ℓ' : Level} : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  constructor torsor
  module G = Group G
  field
    Carrier : Type ℓ'
    _⋆_ : Carrier → ⟨ G ⟩ → Carrier
    isTorsor : IsTorsor G Carrier _⋆_

  open IsTorsor isTorsor public

record TorsorEquiv {G : Group {ℓ}} {ℓT ℓT' : Level} (T : Torsor G {ℓT}) (T' : Torsor G {ℓT'}) : Type (ℓ-max ℓ (ℓ-max ℓT ℓT')) where
  constructor t-equiv
  module T = Torsor T
  module T' = Torsor T'
  field
    eq : T.Carrier ≃ T'.Carrier
    hom : (x : T.Carrier) (g : ⟨ G ⟩) → equivFun eq (x T.⋆ g) ≡ (equivFun eq x T'.⋆ g)

compTorsorEquiv : {G : Group {ℓ}} {ℓT ℓT' ℓT'' : Level} {T : Torsor G {ℓT}} {T' : Torsor G {ℓT'}} {T'' : Torsor G {ℓT''}} →
  TorsorEquiv T T' → TorsorEquiv T' T'' → TorsorEquiv T T''
compTorsorEquiv {G = G} {T = T} {T' = T'} {T'' = T''} (t-equiv (f , eqf) homf) (t-equiv (g , eqg) homg) =
  t-equiv (compEquiv (f , eqf) (g , eqg)) (λ x h → cong g (homf _ _) ∙ homg _ _)

invTorsorEquiv : {G : Group {ℓ}} {ℓT ℓT' : Level} {T : Torsor G {ℓT}} {T' : Torsor G {ℓT'}} → TorsorEquiv T T' → TorsorEquiv T' T
invTorsorEquiv {G = G} {T = T} {T' = T'} (t-equiv f hom) = t-equiv (invEquiv f) lemma where
  _⋆¹_ = Torsor._⋆_ T
  _⋆²_ = Torsor._⋆_ T'
  f-inj : (a b : _) → fst f a ≡ fst f b → a ≡ b
  f-inj a b p = transport (λ i → secEq f a i ≡ secEq f b i) (cong (invEq f) p)
  lemma : (x : _) (g : ⟨ G ⟩) → invEq f (x ⋆² g) ≡ invEq f x ⋆¹ g
  lemma x g = f-inj _ _ (
    fst f (invEq f (x ⋆² g)) ≡⟨ retEq f (x ⋆² g) ⟩
    x ⋆² g                   ≡⟨ cong (_⋆² g) (sym (retEq f x)) ⟩
    fst f (invEq f x) ⋆² g   ≡⟨ sym (hom _ _) ⟩
    fst f (invEq f x ⋆¹ g) ∎)

torsorEquivEq : {G : Group {ℓ}} {ℓT ℓT' : Level} {T : Torsor G {ℓT}} {T' : Torsor G {ℓT'}} (f g : TorsorEquiv T T') → TorsorEquiv.eq f ≡ TorsorEquiv.eq g → f ≡ g
torsorEquivEq {G = G} {T = T} {T' = T'} f g p i = t-equiv (p i) (lemma i) where
  open Torsor
  lemma : PathP (λ i → (x : Carrier T) (g : ⟨ G ⟩) → equivFun (p i) ((T ⋆ x) g) ≡ (T' ⋆ equivFun (p i) x) g) (TorsorEquiv.hom f) (TorsorEquiv.hom g)
  lemma = toPathP ((isPropΠ2 λ _ _ → is-set T' _ _) _ _)

isPropIsTorsor : {G : Group {ℓ}} {X : Type ℓ'} {_⋆_ : X → ⟨ G ⟩ → X} → isProp (IsTorsor G X _⋆_)
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

torsorEq : {G : Group {ℓ}} {T1 T2 : Torsor G {ℓ'}} (p : Torsor.Carrier T1 ≡ Torsor.Carrier T2) →
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

trivialize : {G : Group {ℓ}} {ℓT : Level} (T : Torsor G {ℓT}) (t₀ : Torsor.Carrier T) → TorsorEquiv (principalTorsor G) T
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

trivializeEquiv : {G : Group {ℓ}} {ℓT : Level} (T : Torsor G {ℓT}) → Torsor.Carrier T ≃ TorsorEquiv (principalTorsor G) T
trivializeEquiv {G = G} T = isoToEquiv (iso f g sec retr) where
  module T = Torsor T
  module P = Torsor (principalTorsor G)
  module G = Group G
  f : T.Carrier → TorsorEquiv (principalTorsor G) T
  f = trivialize T
  g : TorsorEquiv (principalTorsor G) T → T.Carrier
  g eq = TorsorEquiv.eq eq .fst G.0g

  sec : section f g
  sec (t-equiv (fun , eq) hom) = torsorEquivEq _ _ (equivEq _ _ (funExt λ x →
    fun G.0g T.⋆ x   ≡⟨ sym (hom G.0g x) ⟩
    fun (G.0g G.+ x) ≡⟨ cong fun (G.lid x) ⟩
    fun x ∎
    ))

  retr : retract f g
  retr t = t T.⋆ G.0g ≡⟨ T.neutral t ⟩ t ∎
{-
module TorsorΣTheory {ℓ : Level} (G : Group {ℓ}) {ℓ' : Level} where
  open Group G
  RawRActionStruct : Type ℓ' → Type _
  RawRActionStruct X = X → ⟨ G ⟩ → X

  TorsorAxioms : (X : Type ℓ') → (X → ⟨ G ⟩ → X) → Type _
  TorsorAxioms X _⋆_ =
    isSet X ×
    ∥ X ∥ ×
    ((x : X) (g g' : ⟨ G ⟩) → (x ⋆ g) ⋆ g' ≡ x ⋆ (g + g')) ×
    ((x : X) → x ⋆ 0g ≡ x) ×
    ((x y : X) → isContr (Σ[ g ∈ ⟨ G ⟩ ] x ⋆ g ≡ y))

  isPropTorsorAxioms : (X : Type ℓ') (s : X → ⟨ G ⟩ → X) → isProp (TorsorAxioms X s)
  isPropTorsorAxioms X _⋆_ = isPropΣ isPropIsSet (λ set → isProp×
    propTruncIsProp (isProp×
    (isPropΠ λ _ → isPropΠ2 λ _ _ → set _ _) (isProp×
    (isPropΠ λ _ → set _ _)
    (isPropΠ2 λ _ _ → isPropIsContr))))

  TorsorStructure : Type ℓ' → Type _
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

  TorsorIsoTorsorΣ : Iso (Torsor G {ℓ'}) TorsorΣ
  TorsorIsoTorsorΣ = iso Torsor→TorsorΣ TorsorΣ→Torsor
    (λ _ → ΣPathP (refl , Σ≡Prop (isPropTorsorAxioms _) refl))
    (λ _ → torsorEq refl refl)

  TorsorEquivΣ : (T T' : Torsor G) → Type _
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

abstract
  TorsorPath : {G : Group {ℓ}} (T T' : Torsor G {ℓ'}) → TorsorEquiv T T' ≃ (T ≡ T')
  TorsorPath = TorsorΣTheory.TorsorPath _

  carac-uaTorsor : {G : Group {ℓ}} {T T' : Torsor G {ℓ'}} (f : TorsorEquiv T T') → cong Torsor.Carrier (fst (TorsorPath T T') f) ≡ ua (TorsorEquiv.eq f)
  carac-uaTorsor (t-equiv f m) = refl ∙∙ ua f ∙∙ refl ≡⟨ sym (rUnit (ua f)) ⟩ ua f ∎

uaTorsor : {G : Group {ℓ}} {T T' : Torsor G {ℓ'}} → TorsorEquiv T T' → T ≡ T'
uaTorsor = equivFun (TorsorPath _ _)

pathToTorsorEquiv : {G : Group {ℓ}} {T T' : Torsor G {ℓ'}} → T ≡ T' → TorsorEquiv T T'
pathToTorsorEquiv = invEq (TorsorPath _ _)

carac-pathToTorsorEquiv : {G : Group {ℓ}} {T T' : Torsor G {ℓ'}} (p : T ≡ T') → pathToEquiv (cong Torsor.Carrier p) ≡ TorsorEquiv.eq (pathToTorsorEquiv p)
carac-pathToTorsorEquiv {T = T} {T' = T'} p = ua-inj _ _ (
  ua (pathToEquiv (cong Carrier p))             ≡⟨ ua-pathToEquiv _ ⟩
  cong Carrier p                                ≡⟨ cong (cong Carrier) (sym (retEq (TorsorPath T T') p)) ⟩
  cong Carrier (uaTorsor (pathToTorsorEquiv p)) ≡⟨ carac-uaTorsor _ ⟩
  ua (TorsorEquiv.eq (pathToTorsorEquiv p)) ∎) where
  open Torsor
  ua-inj : (a b : _) → ua a ≡ ua b → a ≡ b
  ua-inj a b p = a ≡⟨ sym (pathToEquiv-ua a) ⟩ pathToEquiv (ua a) ≡⟨ cong pathToEquiv p ⟩ pathToEquiv (ua b) ≡⟨ pathToEquiv-ua b ⟩ b ∎

torsorPathEq : {G : Group {ℓ}} {T T' : Torsor G {ℓ'}} (p q : T ≡ T') → (cong Torsor.Carrier p ≡ cong Torsor.Carrier q) → p ≡ q
torsorPathEq p q path =
  p                              ≡⟨ sym (retEq (TorsorPath _ _) p) ⟩
  uaTorsor (pathToTorsorEquiv p) ≡⟨ cong uaTorsor (torsorEquivEq _ _ lemma) ⟩
  uaTorsor (pathToTorsorEquiv q) ≡⟨ retEq (TorsorPath _ _) q ⟩
  q ∎ where
  lemma : TorsorEquiv.eq (pathToTorsorEquiv p) ≡ TorsorEquiv.eq (pathToTorsorEquiv q)
  lemma =
    TorsorEquiv.eq (pathToTorsorEquiv p) ≡⟨ sym (carac-pathToTorsorEquiv p) ⟩
    pathToEquiv (cong Torsor.Carrier p)  ≡⟨ cong pathToEquiv path ⟩
    pathToEquiv (cong Torsor.Carrier q)  ≡⟨ carac-pathToTorsorEquiv q ⟩
    TorsorEquiv.eq (pathToTorsorEquiv q) ∎

isGroupoidTorsor : {G : Group {ℓ}} → isGroupoid (Torsor G {ℓ'})
isGroupoidTorsor {G = G} = isOfHLevelRespectEquiv 3 (isoToEquiv (invIso TorsorIsoTorsorΣ)) lemma where
  open TorsorΣTheory G
  is-set : (T : TorsorΣ) → isSet (fst T)
  is-set T = T .snd .snd .fst
  lemma : isGroupoid TorsorΣ
  lemma T T' = isOfHLevelRespectEquiv 2 ΣPath≃PathΣ (isSetΣ (isOfHLevel≡ 2 (is-set T) (is-set T')) λ X →
    isOfHLevelPathP 2 (isSetΣ
      (isSetΠ2 λ _ _ → is-set T') λ _⋆_ → isProp→isSet (isPropTorsorAxioms _ _)) _ _)

module _ (G : Group {ℓ}) where
  PT : Torsor G
  PT = principalTorsor G

  ΩB : Group
  ΩB = makeGroup {G = PT ≡ PT} refl _∙_ sym (isGroupoidTorsor _ _) assoc∙
    (λ _ → sym (rUnit _)) (λ _ → sym (lUnit _)) rCancel lCancel

  ΩB≃ : Group
  ΩB≃ = makeGroup-left {A = TorsorEquiv PT PT} (t-equiv (idEquiv _) (λ _ _ → refl))
    compTorsorEquiv invTorsorEquiv (isOfHLevelRespectEquiv 2 (invEquiv (TorsorPath PT PT)) (isGroupoidTorsor _ _))
    (λ f g h → torsorEquivEq _ _ (equivEq _ _ refl))
    (λ f → torsorEquivEq _ _ (equivEq _ _ refl))
    λ f → torsorEquivEq _ _ (invEquiv-is-linv (TorsorEquiv.eq f))

  eq1 : GroupEquiv ΩB ΩB≃
  eq1 = groupequiv (invEquiv (TorsorPath PT PT)) morph where
    open TorsorEquiv
    open Torsor
    morph : isGroupHom ΩB ΩB≃ (invEq (TorsorPath PT PT))
    morph p q = torsorEquivEq _ _ (
      eq (pathToTorsorEquiv (p ∙ q))                                          ≡⟨ sym (carac-pathToTorsorEquiv _) ⟩
      pathToEquiv (cong Carrier (p ∙ q))                                      ≡⟨ cong pathToEquiv (cong-∙ Carrier p q) ⟩
      pathToEquiv (cong Carrier p ∙ cong Carrier q)                           ≡⟨ pathToEquiv∙ _ _ ⟩
      compEquiv (pathToEquiv (cong Carrier p)) (pathToEquiv (cong Carrier q)) ≡⟨ (λ i → compEquiv (carac-pathToTorsorEquiv p i) (carac-pathToTorsorEquiv q i)) ⟩
      compEquiv (eq (pathToTorsorEquiv p)) (eq (pathToTorsorEquiv q)) ∎)

  dual : Group
  dual = makeGroup 0g (λ x y → y + x) -_ is-set (λ x y z → sym (assoc z y x)) lid rid invl invr where open Group G

  eq2 : GroupEquiv ΩB≃ dual
  eq2 = groupequiv (isoToEquiv (iso f g sec retr)) morph where
    open Group G
    f : ⟨ ΩB≃ ⟩ → ⟨ dual ⟩
    f (t-equiv eq hom) = fst eq (Group.0g G)

    g : ⟨ dual ⟩ → ⟨ ΩB≃ ⟩
    g x = trivialize _ x

    sec : section f g
    sec x = rid x

    retr : retract f g
    retr (t-equiv eq hom) = torsorEquivEq _ _ (equivEq _ _ (funExt (λ x →
      fst eq 0g + x ≡⟨ sym (hom _ _) ∙ cong (fst eq) (lid x) ⟩ fst eq x ∎)))

    morph : (a b : ⟨ ΩB≃ ⟩) → f (compTorsorEquiv a b) ≡ (f b + f a)
    morph a b =
      fst (eq b) (f a) ≡⟨ cong (fst (eq b)) (sym (lid (f a))) ⟩
      fst (eq b) (0g + f a) ≡⟨ hom b 0g (f a) ⟩
      f b + f a ∎
      where open TorsorEquiv

  eq3 : GroupEquiv dual G
  eq3 = groupequiv eq morph where
    open GroupLemmas G
    eq : ⟨ dual ⟩ ≃ ⟨ G ⟩
    eq = isoToEquiv (iso (λ x → - x) (λ x → - x) invInvo invInvo)

    morph : (x y : _) → - (y + x) ≡ (- x - y)
    morph x y = sym (invUniqueL (assoc _ _ _ ∙ cong (_+ x) (sym (assoc _ _ _) ∙ cong (- x +_) (invl y) ∙ rid (- x)) ∙ invl x))

  finalLemma : GroupEquiv ΩB G
  finalLemma = compGroupEquiv eq1 (compGroupEquiv eq2 eq3)
-}
