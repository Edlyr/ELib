{-# OPTIONS --cubical #-}

module ELib.Gerbe.Link where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Data.Sigma
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩ ; AbGroup→Group to GRP)

open import ELib.Gerbe.Base
open import ELib.Gerbe.S

open import ELib.B1.MorphismDelooping
open import ELib.UsefulLemmas

private
  variable
    ℓ ℓ' : Level

record IsLink (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) (e : (x : ⟨ G ⟩) → Ab⟨ π G x ⟩ → Ab⟨ A ⟩) : Type (ℓ-max ℓ ℓ') where
  constructor islink
  open S G
  field
    e-eq : (x : ⟨ G ⟩) → isEquiv (e x)
    e-hom : (x : ⟨ G ⟩) → isGroupHom (GRP (π G x)) (GRP A) (e x)

record Link (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor link
  field
    e : (x : ⟨ G ⟩) → Ab⟨ π G x ⟩ → Ab⟨ A ⟩
    isLink : IsLink G A e

  open S G public
  open IsLink isLink public

  eq : (x : ⟨ G ⟩) → Ab⟨ π G x ⟩ ≃ Ab⟨ A ⟩
  eq x = (e x , e-eq x)

  hom : (x : ⟨ G ⟩) → AbGroupHom (π G x) A
  hom x = grouphom (e x) (e-hom x)

  group-equiv : (x : ⟨ G ⟩) → AbGroupEquiv (π G x) A
  group-equiv x = groupequiv (eq x) (e-hom x)

  coherence : (x y : ⟨ G ⟩) → e x ≡ e y ∘ s x y
  coherence x y = recPropTrunc (isSetΠ (λ _ → AbGroup.is-set A) _ _) (λ p → transport
    (cong (λ y → e x ≡ e y ∘ s x y) p) lemma) (Gerbe.conn G x y) where
    lemma : e x ≡ e x ∘ s x x
    lemma = λ i → e x ∘ s-id x (~ i)

  coherence-inv : (x y : ⟨ G ⟩) → invEq (eq x) ≡ s y x ∘ invEq (eq y)
  coherence-inv x y = recPropTrunc (isSetΠ (λ _ → AbGroup.is-set (π G x)) _ _) (λ p → transport
    (cong (λ y → invEq (eq x) ≡ s y x ∘ invEq (eq y)) p) lemma) (Gerbe.conn G x y) where
    lemma : invEq (eq x) ≡ s x x ∘ invEq (eq x)
    lemma = λ i → s-id x (~ i) ∘ invEq (eq x)

trivialLink : (G : Gerbe {ℓ}) (x : ⟨ G ⟩) → Link G (π G x)
trivialLink G x₀ = link (λ x → s x x₀) (islink (λ x → isEquiv-s x x₀) (λ x → isHom-s x x₀))
  where open S G

congHom : ∀ (G : Gerbe {ℓ}) (H : Gerbe {ℓ'}) (f : ⟨ G ⟩ → ⟨ H ⟩) (x : ⟨ G ⟩) → AbGroupHom (π G x) (π H (f x))
congHom G H f x = grouphom (cong f) (cong-∙ f)

congLink-pnt : ∀ {ℓA ℓB} {G : Gerbe {ℓ}} {H : Gerbe {ℓ'}} {A : AbGroup {ℓA}} {B : AbGroup {ℓB}} →
  Link G A → Link H B → (⟨ G ⟩ → ⟨ H ⟩) → ⟨ G ⟩ → AbGroupHom A B
congLink-pnt {G = G} {H = H} {A = A} {B = B} lA lB f x₀ = grouphom fun (GroupHom.isHom test) where
  module lA = Link lA
  module lB = Link lB
  fun : Ab⟨ A ⟩ → Ab⟨ B ⟩
  fun = lB.e (f x₀) ∘ cong f ∘ invEq (lA.eq x₀)

  test : AbGroupHom A B
  test = compGroupHom (GroupEquiv.hom (invGroupEquiv (lA.group-equiv x₀))) (compGroupHom (congHom G H f x₀) (lB.hom (f x₀)))

module _ {ℓA ℓB} {G : Gerbe {ℓ}} {H : Gerbe {ℓ'}} {A : AbGroup {ℓA}} {B : AbGroup {ℓB}}
  (lA : Link G A) (lB : Link H B) (g : ⟨ G ⟩ → ⟨ H ⟩) where
  congLinkType : Type _
  congLinkType = Σ[ f ∈ (AbGroupHom A B) ] ((x : ⟨ G ⟩) → f ≡ congLink-pnt lA lB g x)

  isPropCongLinkType : isProp congLinkType
  isPropCongLinkType = recPropTrunc isPropIsProp
    (λ x f f' → Σ≡Prop (λ _ → isPropΠ λ _ → isSetGroupHom _ _) (snd f x ∙ sym (snd f' x)))
    (Gerbe.inhabited G)

  congLink-def : congLinkType
  congLink-def = recPropTrunc isPropCongLinkType (λ x₀ → congLink-pnt lA lB g x₀ , lemma x₀) (Gerbe.inhabited G) where
    lemma : (x y : ⟨ G ⟩) → congLink-pnt lA lB g x ≡ congLink-pnt lA lB g y
    lemma x y = recPropTrunc (isSetGroupHom _ _) (cong (λ x → congLink-pnt lA lB g x)) (Gerbe.conn G x y)

  congLink : AbGroupHom A B
  congLink = fst congLink-def

  congLink-carac : (x : ⟨ G ⟩) → congLink ≡ congLink-pnt lA lB g x
  congLink-carac = snd congLink-def

module _ {ℓA ℓB} {G : Gerbe {ℓ}} {H : Gerbe {ℓ'}} {A : AbGroup {ℓA}} {B : AbGroup {ℓB}}
  (lA : Link G A) (lB : Link H B) (f : AbGroupHom A B) (x₀ : ⟨ G ⟩) (y₀ : ⟨ H ⟩) where
  deloopType : Type _
  deloopType = Σ[ g ∈ (⟨ G ⟩ → ⟨ H ⟩) ] (y₀ ≡ g x₀) × (congLink lA lB g ≡ f)

  module lA = Link lA
  module lB = Link lB
  f' : x₀ ≡ x₀ → y₀ ≡ y₀
  f' = invEq (lB.eq y₀) ∘ GroupHom.fun f ∘ lA.e x₀

  f'test : AbGroupHom (π G x₀) (π H y₀)
  f'test = compGroupHom (lA.hom x₀) (compGroupHom f (GroupEquiv.hom (invGroupEquiv (lB.group-equiv y₀))))

  module Deloop = Delooping (Gerbe.conn G) (Gerbe.grpd H) f' (GroupHom.isHom f'test)

  caracDeloopType : deloopType ≃ Deloop.deloopingType
  caracDeloopType = isoToEquiv (iso eq→ eq← sec retr) where
    eq→ : deloopType → Deloop.deloopingType
    eq→ (g , p , coh) = g , p ,
      λ q → 
        p ∙ cong g q
          ≡⟨ cong (p ∙_) (λ i → testok i q) ⟩
        p ∙ lB.s y₀ (g x₀) (f' q)
          ≡⟨ cong (p ∙_) (lB.s-carac y₀ (g x₀) p (f' q)) ⟩
        p ∙ (sym p) ∙ f' q ∙ p
          ≡⟨ compPathl-cancel p _ ⟩
        f' q ∙ p ∎
      where
      testok : cong g ≡ S.s H y₀ (g x₀) ∘ f'
      testok =
        cong g
          ≡⟨ (λ i → funExt (secEq (lB.eq (g x₀))) (~ i) ∘ cong g ∘ funExt (secEq (lA.eq x₀)) (~ i)) ⟩
        invEq (lB.eq (g x₀)) ∘ lB.e (g x₀) ∘ cong g ∘ invEq (lA.eq x₀) ∘ lA.e x₀
          ≡⟨ cong (λ r → invEq (lB.eq (g x₀)) ∘ r ∘ lA.e x₀) (cong GroupHom.fun (sym (congLink-carac lA lB g x₀) ∙ coh)) ⟩
        invEq (lB.eq (g x₀)) ∘ GroupHom.fun f ∘ lA.e x₀
          ≡⟨ cong (λ r → r ∘ GroupHom.fun f ∘ lA.e x₀) (lB.coherence-inv (g x₀) y₀) ⟩
        S.s H y₀ (g x₀) ∘ f' ∎

    eq← : Deloop.deloopingType → deloopType
    eq← (g , p , !) = g , p , congLink-carac lA lB g x₀ ∙ groupHomEq (
      lB.e (g x₀) ∘ cong g ∘ invEq (lA.eq x₀)
        ≡⟨ cong (λ h → lB.e (g x₀) ∘ h ∘ cong g ∘ invEq (lA.eq x₀)) (sym (S.s-id H (g x₀)) ∙ S.s-comp H _ _ _) ⟩
      lB.e (g x₀) ∘ S.s H y₀ (g x₀) ∘ S.s H (g x₀) y₀ ∘ cong g ∘ invEq (lA.eq x₀)
        ≡⟨ cong (λ h → h ∘ S.s H (g x₀) y₀ ∘ cong g ∘ invEq (lA.eq x₀)) (sym (lB.coherence y₀ (g x₀))) ⟩
      lB.e y₀ ∘ S.s H (g x₀) y₀ ∘ cong g ∘ invEq (lA.eq x₀)
        ≡⟨ cong (λ h → lB.e y₀ ∘ h ∘ cong g ∘ invEq (lA.eq x₀)) (funExt (S.s-carac H _ _ (sym p))) ⟩
      lB.e y₀ ∘ (λ q → p ∙ cong g q ∙ sym p) ∘ invEq (lA.eq x₀)
        ≡⟨ cong (λ h → lB.e y₀ ∘ h ∘ invEq (lA.eq x₀)) (funExt λ q →
          p ∙ cong g q ∙ sym p
            ≡⟨ assoc _ _ _ ∙ cong (_∙ sym p) (! q) ⟩
          (f' q ∙ p) ∙ sym p
            ≡⟨ compPathr-cancel _ _ ⟩
          f' q ∎
        )⟩
      lB.e y₀ ∘ f' ∘ invEq (lA.eq x₀)
        ≡⟨ refl ⟩
      lB.e y₀ ∘ invEq (lB.eq y₀) ∘ GroupHom.fun f ∘ lA.e x₀ ∘ invEq (lA.eq x₀)
        ≡⟨ (λ i → funExt (retEq (lB.eq y₀)) i ∘ GroupHom.fun f ∘ funExt (retEq (lA.eq x₀)) i) ⟩
      GroupHom.fun f ∎)

    sec : section eq→ eq←
    sec (g , p , !) = Deloop.propDeloop _ _

    retr : retract eq→ eq←
    retr (g , coh) = ΣPathP (refl , Σ≡Prop (λ _ → isSetGroupHom _ _) refl)

  deloopUnique : isContr deloopType
  deloopUnique = isOfHLevelRespectEquiv 0 (invEquiv caracDeloopType) (Deloop.deloop , Deloop.propDeloop _)


{-
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Foundations.SIP

open import ELib.UsefulLemmas
open import ELib.Gerbe.Base

open import ELib.ConcreteGroup.Base
open import ELib.ConcreteGroup.DeloopMorph

private
  variable
    ℓ ℓ' ℓ'' : Level

GRP = AbGroup→Group

linked-by-ab : (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) → Type (ℓ-max ℓ ℓ')
linked-by-ab G A = Σ[ e ∈ ((x : ⟨ G ⟩) → AbGroupIso A (π G x)) ]
  ((x y : ⟨ G ⟩) → compGroupIso (e x) (s-iso x y) ≡ e y) where
  open S G
  H : (x : _) → _
  H x = AbGroup→Group (π G x)

linkStructure : (A : AbGroup {ℓ'}) → Type ℓ → Type _
linkStructure {ℓ} A = add-to-structure isGerbe (λ X gerbe → linked-by-ab (X , gerbe) A)

B² : (A : AbGroup {ℓ'}) → Type _
B² {ℓ'} A = TypeWithStr ℓ' (linkStructure A)

linkHom : ∀ {ℓ ℓ'} → (A : AbGroup {ℓ}) → StrHom {ℓ = ℓ'} (linkStructure A) _
linkHom A (X₁ , gerbe₁ , l₁ , _) (X₂ , gerbe₂ , l₂ , _) f =
  (x : X₁) → cong f ∘ (l₁ x .eq .fst) ≡ l₂ (f x) .eq .fst where
  open GroupIso

linkIso : ∀ {ℓ ℓ'} → (A : AbGroup {ℓ}) → StrIso {ℓ = ℓ'} (linkStructure A) _
linkIso A = StrHom→StrIso (linkHom A)

abstract
  linkSNS-≡ : (A : AbGroup {ℓ}) → SNS-≡ {ℓ₁ = ℓ'} (linkStructure A) (linkIso A)
  linkSNS-≡ A {X} (gerbe₁ , l₁) (gerbe₂ , l₂) = transport path (test gerbe₂ l₁' l₂) where
    p : gerbe₁ ≡ gerbe₂
    p = isPropIsGerbe X _ _
    l₁' : _
    l₁' = transp (λ i → linked-by-ab (X , p i) A) i0 l₁

    ok : (gerbe : isGerbe X) (l : linked-by-ab (X , gerbe) A) → linkStructure A X
    ok gerbe l = (gerbe , l)

    wesh : ok gerbe₁ l₁ ≡ ok gerbe₂ l₁'
    wesh i = ok (p i) (transp (λ j → linked-by-ab (X , p (i ∧ j)) A) (~ i) l₁)

    path :
      ((linkIso A (X , gerbe₂ , l₁') (X , gerbe₂ , l₂) (idEquiv X)) ≃ (ok gerbe₂ l₁' ≡ ok gerbe₂ l₂)) ≡
      ((linkIso A (X , gerbe₁ , l₁ ) (X , gerbe₂ , l₂) (idEquiv X)) ≃ (ok gerbe₁ l₁ ≡ ok gerbe₂ l₂))
    path i = (linkIso A (X , wesh (~ i)) (X , gerbe₂ , l₂) (idEquiv X)) ≃ (wesh (~ i) ≡ ok gerbe₂ l₂)

    π₁ : (x : X) → Group
    π₁ x = GRP (π (X , gerbe₁) x)

    test : (gerbe : isGerbe X) (l₁ l₂ : linked-by-ab (X , gerbe) A) →
      linkIso A (X , gerbe , l₁) (X , gerbe , l₂) (idEquiv X) ≃ (ok gerbe l₁ ≡ ok gerbe l₂)
    test gerbe l₁ l₂ = isoToEquiv (iso Iso→≡ ≡→Iso sec retr) where
      Iso→≡  : linkIso A (X , gerbe , l₁) (X , gerbe , l₂) (idEquiv X) → ok gerbe l₁ ≡ ok gerbe l₂
      Iso→≡ link-iso = ΣPathP (refl , Σ≡Prop
        (λ _ → isPropΠ2 λ _ y → isSetGroupIso _ _ _ _)
        (funExt λ x → groupIsoEq _ _ _ _ (equivEq _ _ (link-iso x))))

      ≡→Iso : ok gerbe l₁ ≡ ok gerbe l₂ → linkIso A (X , gerbe , l₁) (X , gerbe , l₂) (idEquiv X)
      ≡→Iso p x i = snd (p i) .fst x .eq .fst where open GroupIso

      isSetLinkStructure : isSet (linkStructure A X)
      isSetLinkStructure = isSetΣ (isProp→isSet (isPropIsGerbe X)) λ gerbe → isSetΣ
          (isSetΠ λ x → isSetGroupIso _ _)
          λ f → isSetΠ2 λ y z → isProp→isSet (isSetGroupIso _ _ _ _)

      sec : section Iso→≡ ≡→Iso
      sec p = isSetLinkStructure _ _ _ _

      isPropLinkIso : isProp (linkIso A (X , gerbe , l₁) (X , gerbe , l₂) (idEquiv X))
      isPropLinkIso = isPropΠ λ x → isSetΠ (λ g → gerbe-grpd (X , gerbe) _ _) _ _

      retr : retract Iso→≡ ≡→Iso
      retr link-iso = isPropLinkIso _ _

  linkSNS : (A : AbGroup {ℓ}) → SNS {ℓ₁ = ℓ'} (linkStructure A) (linkIso A)
  linkSNS A = SNS-≡→SNS-PathP (linkIso A) (linkSNS-≡ A)

link-by-π : (G : Gerbe {ℓ}) (x : ⟨ G ⟩) → linked-by-ab G (π G x)
link-by-π G x = (λ y → s-iso x y) , λ y z →
  groupIsoEq (AbGroup→Group (π G x)) (AbGroup→Group (π G z)) _ _
  (equivEq _ _ (funExt λ t → recPropTrunc (gerbe-grpd G _ _ _ _) (λ py → recPropTrunc (gerbe-grpd G _ _ _ _) (λ pz →
    transport (λ i → s-fun (py i) (pz i) (s-fun x (py i) t) ≡ s-fun x (pz i) t)
      (! _)
  ) (gerbe-conn G x z)) (gerbe-conn G x y)))
  where
  open S G
  s-fun : (x : _) (y : _) → _
  s-fun x y = s x y .fst .fst
  ! : (t : _) → s-fun x x t ≡ t
  ! t = snd (s x x) refl t ∙ sym (rUnit _ ∙ lUnit _)



module _ (A : AbGroup {ℓ'}) (G : B² {ℓ'} A) where
  open GroupIso
  X = fst G
  gerbe : Gerbe
  gerbe = (fst G , fst (snd G))
  link = snd (snd G)
  l = fst (link)
  equiv1 : Σ (fst G ≃ fst G) (λ f → (x : X) → cong (fst f) ∘ l x .eq .fst ≡ l (fst f x) .eq .fst) ≃ (G ≡ G)
  equiv1 = SIP (linkSNS A) G G

  equiv2 : (f : fst G ≃ fst G) → ((x : X) → cong (fst f) ∘ l x .eq .fst ≡ l (fst f x) .eq .fst) ≃ ∥ idEquiv X ≡ f ∥
  equiv2 f = isoToEquiv (iso fun→ fun← sec retr) where
    fun← : ∥ idEquiv X ≡ f ∥ → ((x : X) → cong (fst f) ∘ l x .eq .fst ≡ l (fst f x) .eq .fst)
    fun← = recPropTrunc (isPropΠ λ x → isSetΠ (λ g → gerbe-grpd gerbe _ _) _ _)
      λ p x → transport (λ i → cong (fst (p i)) ∘ l x .eq .fst ≡ l (fst (p i) x) .eq .fst) refl

    fun→ : ((x : X) → cong (fst f) ∘ l x .eq .fst ≡ l (fst f x) .eq .fst) → ∥ idEquiv X ≡ f ∥
    fun→ prop =
      recPropTrunc propTruncIsProp (λ x₀ → recPropTrunc propTruncIsProp (λ p₀ → ∣ lemma x₀ p₀ ∣)
      (gerbe-conn gerbe x₀ (fst f x₀))) (gerbe-inhabited gerbe)
      where
      s : (x y : X) → _
      s x y = S.s-iso gerbe x y .eq .fst
      sf : (x : X) → _
      sf x = S.s-iso gerbe x (fst f x) .eq .fst

      cong-f : (x : X) → (x ≡ x) → ((fst f x) ≡ (fst f x))
      cong-f x = cong (fst f)

      carac-cong-f : (x : X) → cong-f x ≡ sf x
      carac-cong-f x = invEquiv (_ , isEquiv→isEmbedding (isEquivPreComp (l x .eq)) (cong-f x) (sf x)) .fst (pre-carac2 x) where
        pre-carac1 : (x : X) → sf x ∘ (l x .eq .fst) ≡ l (fst f x) .eq .fst
        pre-carac1 x = cong fst (cong eq (snd link x (fst f x)))
        pre-carac2 : (x : X) → (cong-f x) ∘ (l x .eq .fst) ≡ sf x ∘ (l x .eq .fst)
        pre-carac2 x = (prop x) ∙ sym (pre-carac1 x)

      lemma : (x₀ : ⟨ gerbe ⟩) (p₀ : x₀ ≡ fst f x₀) → idEquiv X ≡ f
      lemma x₀ p₀ = equivEq _ _ (funExt id≡f) where
        CG : ConcreteGroup _
        CG = conc-group X (struct-conc-group x₀ (gerbe-conn gerbe x₀) (gerbe-grpd gerbe x₀ x₀))
        morph-id : GroupHom (abs CG) (abs CG)
        morph-id = (λ x → x) , λ x y → refl

        f-is-deloop : (x : X) → delooping CG CG morph-id x
        f-is-deloop x = fst f x , (λ q → p₀ ∙ cong (fst f) q) , λ ω α →
          p₀ ∙ cong (fst f) (ω ∙ α)
            ≡⟨ cong (p₀ ∙_) (cong-∙ (fst f) _ _) ⟩
          p₀ ∙ cong-f x₀ ω ∙ cong (fst f) α
            ≡⟨ cong (λ r → p₀ ∙ r ∙ cong (fst f) α) (λ i → carac-cong-f x₀ i ω) ⟩
          p₀ ∙ sf x₀ ω ∙ cong (fst f) α
            ≡⟨ assoc _ _ _ ⟩
          (p₀ ∙ sf x₀ ω) ∙ cong (fst f) α
            ≡⟨ cong (λ r → (p₀ ∙ r) ∙ cong (fst f) α) (S.s gerbe x₀ (fst f x₀) .snd p₀ ω) ⟩
          (p₀ ∙ sym p₀ ∙ ω ∙ p₀) ∙ cong (fst f) α
            ≡⟨ cong (_∙ cong (fst f) α) (compPathl-cancel p₀ (ω ∙ p₀)) ⟩
          (ω ∙ p₀) ∙ cong (fst f) α
            ≡⟨ sym (assoc _ _ _) ⟩
          ω ∙ p₀ ∙ cong (fst f) α ∎
        id-is-deloop : (x : X) → delooping CG CG morph-id x
        id-is-deloop x = x , (λ p → p) , λ _ _ → refl

        id≡f : (x : X) → x ≡ fst f x
        id≡f x = cong fst (isContr→isProp (deloopingContr CG CG morph-id x) (id-is-deloop x) (f-is-deloop x))

    sec : section fun→ fun←
    sec _ = propTruncIsProp _ _

    retr : retract fun→ fun←
    retr _ = isPropΠ (λ _ → isSetΠ (λ _ → gerbe-grpd gerbe _ _) _ _) _ _
{-
  ZG : Type ℓ'
  ZG = Σ[ f ∈ X ≃ X ] ∥ idEquiv X ≡ f ∥

  B²Path≃ZG : (G ≡ G) ≃ ZG
  B²Path≃ZG = compEquiv (invEquiv equiv1) (Σ-cong-equiv-snd equiv2)
-}


-------------------
{-
module _ (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) (ℒ : linked-by-ab G A) where
  eA = fst ℒ
  condA = snd ℒ
  Agrp = AbGroup→Group A
  test : (B : AbGroup {ℓ'}) → linked-by-ab G B ≃ GroupIso (Agrp) (AbGroup→Group B)
  test B = isoToEquiv (iso f g sec retr) where
    Bgrp = AbGroup→Group B

    pre-f : (linked-by-ab G B) → (x : ⟨ G ⟩) → GroupIso Agrp Bgrp
    pre-f (eB , _) x = compGroupIso Agrp (AbGroup→Group (π G x)) Bgrp (eA x) (invGroupIso Bgrp (AbGroup→Group (π G x)) (eB x))

    f₀ : (l : linked-by-ab G B) → Σ[ i ∈ GroupIso Agrp Bgrp ] (((x : ⟨ G ⟩) (g : Ab⟨ A ⟩) → i .fst .fst g ≡ pre-f l x .fst .fst g ))
    f₀ (eB , condB) = isContrT .fst where
      pre-f₀ : (x : ⟨ G ⟩) → GroupIso Agrp Bgrp
      pre-f₀ = pre-f (eB , condB)

      T : Type _
      T = Σ[ i ∈ (GroupIso Agrp Bgrp) ] ((x : ⟨ G ⟩) (g : Ab⟨ A ⟩) → i .fst .fst g ≡ pre-f₀ x .fst .fst g )

      isContrT : isContr T
      isContrT = recPropTrunc isPropIsContr (λ x₀ → (pre-f₀ x₀ , λ x g → recPropTrunc (group-is-set Bgrp _ _)
        (λ p → cong (λ ok → pre-f₀ ok .fst .fst g) p) (gerbe-conn G x₀ x)) ,
        λ f → ΣProp≡ (λ x → isPropΠ λ x₁ → isPropΠ λ g → group-is-set Bgrp _ _)
        (groupIsoEq Agrp Bgrp _ _ (equivEq _ _ (funExt λ g → sym (snd f _ g))))) (gerbe-inhabited G)

    f : linked-by-ab G B → GroupIso Agrp Bgrp
    f x = fst (f₀ x)

    assocGroupComp : ∀ {ℓ ℓ' ℓ'' ℓ''' : Level} → (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) (I : Group {ℓ'''})
      (f : GroupIso F G) (g : GroupIso G H) (h : GroupIso H I) →
      compGroupIso F G I f (compGroupIso G H I g h) ≡ compGroupIso F H I (compGroupIso F G H f g) h
    assocGroupComp F G H I f g h = groupIsoEq F I _ _ (equivEq _ _ refl)

    g : GroupIso Agrp Bgrp → linked-by-ab G B
    g i = eB , coherence where
      j = invGroupIso Agrp Bgrp i

      eB : (x : ⟨ G ⟩) → GroupIso Bgrp (AbGroup→Group (π G x))
      eB x = compGroupIso Bgrp Agrp (AbGroup→Group (π G x)) j (eA x)

      coherence : _
      coherence x y =
        sym (assocGroupComp Bgrp Agrp (AbGroup→Group (π G x)) (AbGroup→Group (π G y)) j (eA x) (S.s-iso G x y)) ∙
        cong (λ ok → compGroupIso Bgrp Agrp (AbGroup→Group (π G y)) j ok) (condA x y)

    abstract
      sec : section f g
      sec ((i , eq) , morph) = groupIsoEq Agrp Bgrp _ _ (equivEq _ _ (funExt λ a → recPropTrunc (group-is-set Bgrp _ _) (λ x →
        f (g ((i , eq) , morph)) .fst .fst a
          ≡⟨ snd (f₀ (g ((i , eq) , morph))) x a ⟩
        pre-f (g ((i , eq) , morph)) x .fst .fst a
          ≡⟨ refl ⟩
        i (invEq (fst (eA x)) (fst (eA x) .fst a))
          ≡⟨ cong i (secEq (fst (eA x)) a) ⟩
        i a ∎
        ) (gerbe-inhabited G)))

      invEquivCompEquiv : ∀ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (e : A ≃ B) (f : B ≃ C) →
        invEquiv (compEquiv e f) ≡ compEquiv (invEquiv f) (invEquiv e)
      invEquivCompEquiv {A = A} e f = equivEq _ _ (funExt λ c → inj
        (_
          ≡⟨ retEq (compEquiv e f) c ⟩
        c
          ≡⟨ sym (retEq f c)  ⟩
        _
          ≡⟨ cong (f .fst) (sym (retEq e _)) ⟩
        _ ∎)
        ) where
        inj : {x y : A} → f .fst (e .fst x) ≡ f .fst (e .fst y) → x ≡ y
        inj {x} {y} = invEq (_ , (isEquiv→isEmbedding (compEquiv e f .snd) x y))

      retr : retract f g
      retr (eB , condB) =
        ΣProp≡ (λ e → isPropΠ2 λ x y → isSetGroupIso Bgrp (AbGroup→Group (π G y)) _ (e y))
        (funExt λ x → groupIsoEq Bgrp (AbGroup→Group (π G x)) _ _ (equivEq _ _ (funExt λ b →
          g (f (eB , condB)) .fst x .fst .fst b
            ≡⟨ refl ⟩
          eA x .fst .fst (invEq (fst (f (eB , condB))) b)
            ≡⟨ cong (λ U → eA x .fst .fst (invEq U b))
              (fst (f (eB , condB))
                ≡⟨ equivEq _ _ (funExt λ a → f₀ (eB , condB) .snd x a) ⟩
              fst (pre-f (eB , condB) x) ∎)
            ⟩
          eA x .fst .fst (invEq (fst (pre-f (eB , condB) x)) b)
            ≡⟨ refl ⟩
          compEquiv (invEquiv (compEquiv (fst (eA x)) (invEquiv (fst (eB x))))) (fst (eA x)) .fst b
            ≡⟨ cong (λ F → F .fst b) (
              compEquiv (invEquiv (compEquiv (fst (eA x)) (invEquiv (fst (eB x))))) (fst (eA x))
                ≡⟨ cong (λ F → compEquiv F (fst (eA x))) (invEquivCompEquiv (fst (eA x)) (invEquiv (fst (eB x)))) ⟩
              compEquiv (compEquiv (invEquiv (invEquiv (fst (eB x)))) (invEquiv (fst (eA x)))) (fst (eA x))
                ≡⟨ equivEq _ _ refl ⟩
              compEquiv (compEquiv (fst (eB x)) (invEquiv (fst (eA x)))) (fst (eA x))
                ≡⟨ equivEq _ _ refl ⟩
              compEquiv (fst (eB x)) (compEquiv (invEquiv (fst (eA x))) (fst (eA x)))
                ≡⟨ cong (compEquiv (fst (eB x))) (equivEq (compEquiv (invEquiv (fst (eA x))) (fst (eA x))) (idEquiv _) (funExt (retEq (fst (eA x))))) ⟩
              compEquiv (fst (eB x)) (idEquiv _)
                ≡⟨ equivEq _ _ refl ⟩
              fst (eB x) ∎)
            ⟩
          eB x .fst .fst b ∎
        )))

AbGroup-ua : (G G' : AbGroup {ℓ}) → GroupIso (AbGroup→Group G) (AbGroup→Group G') ≃ (G ≡ G')
AbGroup-ua = AbGroupPath

Π : (G : Gerbe {ℓ}) → Σ[ A ∈ AbGroup {ℓ} ] (linked-by-ab G A)
Π {ℓ} G = fst contr where
  type = Σ[ A ∈ AbGroup {ℓ} ] (linked-by-ab G A)
  type2 = λ (A : type) → Σ[ B ∈ AbGroup {ℓ} ] (GroupIso (AbGroup→Group (fst A)) (AbGroup→Group B))
  type3 = λ (A : type) → Σ[ B ∈ AbGroup {ℓ} ] (fst A ≡ B)

  type≃type2 : (A : type) → type ≃ type2 A
  type≃type2 (A , l) = congΣEquiv λ B → test G A l B

  type2≃type3 : (A : type) → type2 A ≃ type3 A
  type2≃type3 A = congΣEquiv λ B → AbGroup-ua (fst A) B

  isContr-type3 : (A : type) → isContr (type3 A)
  isContr-type3 A = (fst A , refl) , λ B → ΣPathP (snd B , λ i j → snd B (i ∧ j))

  contr : isContr type
  contr = recPropTrunc isPropIsContr
    (λ x₀ → isOfHLevelRespectEquiv 0 (invEquiv (
      compEquiv (type≃type2 (π G x₀ , link-by-π G x₀)) (type2≃type3 (π G x₀ , link-by-π G x₀))))
      (isContr-type3 (π G x₀ , link-by-π G x₀))
    )
    (fst (snd G))

B² : (AbGroup {ℓ}) → Type (ℓ-suc ℓ)
B² {ℓ} A = Σ[ G ∈ Gerbe {ℓ} ] (linked-by-ab G A)

module tests (A : AbGroup {ℓ}) (G : B² A) where
  B2 = B² A
  carac : (G G' : B2) → (G ≡ G') ≃ (Σ (fst G ≡ fst G') (λ p → PathP (λ i → linked-by-ab (p i) A) (snd G) (snd G')))
  carac G G' = invEquiv Σ≃

  ΣProp≡P : {ℓ ℓ' : Level} {A A' : Type ℓ} {B : A → Type ℓ'} {B' : A' → Type ℓ'}
    (p : A ≡ A') (q : PathP (λ i → p i → Type ℓ') B B') → (x : Σ A B) (y : Σ A' B') →
    PathP (λ i → Σ (p i) (q i)) x y → PathP (λ i → p i) (fst x) (fst y)
  ΣProp≡P p q x y s = λ i → fst (s i)

  ΣProp≡P2 : {ℓ ℓ' : Level} {A A' : Type ℓ} {B : A → Type ℓ'} {B' : A' → Type ℓ'}
    (p : A ≡ A') (q : PathP (λ i → p i → Type ℓ') B B') → (x : Σ A B) (y : Σ A' B') →
    ((i : I) (α : p i) → isProp (q i α)) →
    PathP (λ i → p i) (fst x) (fst y) → PathP (λ i → Σ (p i) (q i)) x y
  ΣProp≡P2 p q x y prop s = λ i → (s i) , prop i (s i)
    (transp (λ j → q (i ∧ j) (s (i ∧ j))) (~ i) (snd x))
    (transp (λ j → q (i ∨ ~ j) (s (i ∨ ~ j))) i (snd y)) i

  ΣProp≃P : {ℓ ℓ' : Level} {A A' : Type ℓ} {B : A → Type ℓ'} {B' : A' → Type ℓ'}
    (p : A ≡ A') (q : PathP (λ i → p i → Type ℓ') B B') → (x : Σ A B) (y : Σ A' B') →
    ((i : I) (α : p i) → isProp (q i α)) →
    PathP (λ i → p i) (fst x) (fst y) ≃ PathP (λ i → Σ (p i) (q i)) x y
  ΣProp≃P {B' = B'} p q x y prop = isoToEquiv
    (iso
      (ΣProp≡P2 p q x y prop)
      (ΣProp≡P p q x y)
      (λ r i j → fst (r j) , right r i j )
      (λ r → refl)
    ) where
      right : (r : _) → (λ i → prop i (fst (r i))
        (transp (λ j → q (i ∧ j) (fst (r (i ∧ j)))) (~ i) (snd x))
        (transp (λ j → q (i ∨ ~ j) (fst (r (i ∨ ~ j)))) i (snd y)) i) ≡ λ i → snd (r i)
      right r = lemma _ _ where
        lemma : isProp (PathP (λ i → q i (fst (r i))) (snd x) (snd y))
        lemma = transport (cong isProp (sym (PathP≡Path _ _ _))) (isProp→isSet (prop i1 (fst y)) _ _)

  carac2 : (G G' : B2) →
    (Σ (fst G ≡ fst G') λ p → PathP (λ i → linked-by-ab (p i) A) (snd G) (snd G'))
      ≃
    (Σ (fst G ≡ fst G') λ p → PathP (λ i → (x : ⟨ p i ⟩) → GroupIso (AbGroup→Group A) (AbGroup→Group (π (p i) x))) (G .snd .fst) (G' .snd .fst))
  carac2 G G' = congΣEquiv λ p → invEquiv (ΣProp≃P _ _ _ _ λ i α → isPropΠ2 λ x y → isSetGroupIso (AbGroup→Group A) (AbGroup→Group (π (p i) y)) _ _ )

  --link-iso : (G G' : B2) → Type _
  --link-iso (G , e , _) (G' , f , _) = Σ[ p ∈ (⟨ G ⟩ ≃ ⟨ G' ⟩) ] ((x : ⟨ G ⟩) →  {!!} ≡ f (fst p x))
-}
-}
