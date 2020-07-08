{-# OPTIONS --cubical #-}

module ELib.Gerbe.B2 where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Structures.Group renaming (⟨_⟩ to Grp⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Equiv.HalfAdjoint

open import ELib.UsefulLemmas
open import ELib.Gerbe.Base
open import ELib.Gerbe.Link

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (A : AbGroup {ℓ}) {ℓ' : Level} where
  record B² : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    constructor b²
    field
      grb : Gerbe {ℓ'}
      lnk : Link grb A

    open Gerbe grb public
    open Link lnk public

  record B²Equiv (G H : B²) : Type (ℓ-max ℓ' ℓ) where
    constructor b²equiv
    module G = B² G
    module H = B² H
    field
      fun : G.Carrier → H.Carrier
      p : congLink G.lnk H.lnk fun ≡ grouphom (λ x → x) (λ _ _ → refl)

    abstract
      isEquiv-fun : isEquiv fun
      isEquiv-fun = isEmbedding×isSurjection→isEquiv (embed , surj) where
        lemma : (x : G.Carrier) → isEquiv (cong {x = x} {y = x} fun)
        lemma x = transport (cong isEquiv (sym p')) (snd (compEquiv (G.eq x) (invEquiv (H.eq (fun x))))) where
          p' : (cong {x = x} {y = x} fun) ≡ invEq (H.eq (fun x)) ∘ G.e x
          p' =
            cong {x = x} {y = x} fun
              ≡⟨ (λ i → funExt (secEq (H.eq (fun x))) (~ i) ∘ cong fun ∘ funExt (secEq (G.eq x)) (~ i)) ⟩
            invEq (H.eq (fun x)) ∘ H.e (fun x) ∘ cong {x = x} {y = x} fun ∘ invEq (G.eq x) ∘ G.e x
              ≡⟨ cong (λ r → invEq (H.eq (fun x)) ∘ r ∘ G.e x) (sym (cong GroupHom.fun (congLink-carac G.lnk H.lnk fun x))) ⟩
            invEq (H.eq (fun x)) ∘ GroupHom.fun (congLink G.lnk H.lnk fun) ∘ G.e x
              ≡⟨ cong (λ r → invEq (H.eq (fun x)) ∘ r ∘ G.e x) (cong GroupHom.fun p) ⟩
            invEq (H.eq (fun x)) ∘ G.e x ∎

        embed : isEmbedding fun
        embed x y = recPropTrunc (isPropIsEquiv _) (subLemma x y) (G.conn x y) where
          subLemma : (x y : _) (p : x ≡ y) → isEquiv (cong {x = x} {y = y} fun)
          subLemma x y = J (λ y p → isEquiv (cong {x = x} {y = y} fun)) (lemma x)

        surj : isSurjection fun
        surj y = recPropTrunc propTruncIsProp (λ x → recPropTrunc propTruncIsProp (λ p → ∣ x , p ∣) (H.conn (fun x) y)) (G.inhabited)

    eq : G.Carrier ≃ H.Carrier
    eq = fun , isEquiv-fun

{-  record B²Equiv (G H : B²) : Type ℓ where
    constructor b²equiv
    module G = B² G
    module H = B² H
    field
      eq : G.Carrier ≃ H.Carrier
      p : congLink G.lnk H.lnk (equivFun eq) ≡ grouphom (λ x → x) (λ _ _ → refl)
-}
isSetGroupEquiv : {A : Group {ℓ}} {B : Group {ℓ'}} → isSet (GroupEquiv A B)
isSetGroupEquiv {A = A} {B = B} = isOfHLevelRespectEquiv 2 (invEquiv lemma) (isSetΣ (isSetΠ λ _ → Group.is-set B)
  λ _ → isSetΣ (isProp→isSet (isPropIsEquiv _)) λ _ → isProp→isSet (isPropIsGroupHom A B)) where
  lemma : GroupEquiv A B ≃ (Σ[ f ∈ (Grp⟨ A ⟩ → Grp⟨ B ⟩) ] (isEquiv f) × isGroupHom A B f)
  lemma = isoToEquiv (iso (λ (groupequiv eq hom) → fst eq , snd eq , hom) (λ (f , eq , hom) → groupequiv (f , eq) hom)
    (λ _ → refl) λ _ → refl)

idGroupHom : {A : Group {ℓ}} → GroupHom A A
idGroupHom = grouphom (λ x → x) (λ _ _ → refl)

isPropIsLink : {G : Gerbe {ℓ'}} {A : AbGroup {ℓ}} {e : _} → isProp (IsLink G A e)
isPropIsLink {G = G} {A = A} {e = e} = isOfHLevelRespectEquiv 1 lemma (isProp× (isPropΠ λ _ → isPropIsEquiv _)
  (isPropΠ λ x → isPropIsGroupHom (AbGroup→Group (π G x)) (AbGroup→Group A))) where
  lemma : (((x : _) → isEquiv (e x)) × ((x : _) → isGroupHom (AbGroup→Group (π G x)) (AbGroup→Group A) (e x))) ≃ IsLink G A e
  lemma = isoToEquiv (iso (λ (a , b) → islink a b) (λ (islink a b) → a , b) (λ _ → refl) λ _ → refl)

isSetLink : {G : Gerbe {ℓ'}} {A : AbGroup {ℓ}} → isSet (Link G A)
isSetLink {G = G} {A = A} = isOfHLevelRespectEquiv 2 (invEquiv lemma) (isSetΠ λ _ → isSetGroupEquiv) where
  lemma : Link G A ≃ ((x : ⟨ G ⟩) → AbGroupEquiv (π G x) A)
  lemma = isoToEquiv (iso (λ l x → Link.group-equiv l x) (λ l → link (λ x → GroupEquiv.eq (l x) .fst)
    (islink (λ x → GroupEquiv.eq (l x) .snd) λ x → GroupEquiv.isHom (l x))) (λ _ → refl) λ _ → refl)

linkEq : {G : Gerbe {ℓ'}} {A : AbGroup {ℓ}} {l1 l2 : Link G A} → (Link.e l1 ≡ Link.e l2) → l1 ≡ l2
linkEq {G = G} {A = A} {l1 = l1} {l2 = l2} p i = link (p i) (lemma i) where
  lemma : PathP (λ i → IsLink G A (p i)) (Link.isLink l1) (Link.isLink l2)
  lemma = toPathP (isPropIsLink _ _)

module B²ΣTheory (A : AbGroup {ℓ}) {ℓ' : Level} where
  B²Struct : Type ℓ' → Type (ℓ-max ℓ ℓ')
  B²Struct X = Σ[ isGerbe ∈ IsGerbe X ] Link (gerbe X isGerbe) A

  isSetB²Struct : {X : Type ℓ'} → isSet (B²Struct X)
  isSetB²Struct {X = X} = isSetΣ (isProp→isSet isPropIsGerbe) λ _ → isSetLink

  B²Σ : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  B²Σ = TypeWithStr ℓ' B²Struct

  B²EquivStr : StrEquiv B²Struct ℓ
  B²EquivStr (X , grb , lnk) (X' , grb' , lnk') (f , eq) = congLink lnk lnk' f ≡ grouphom (λ x → x) (λ _ _ → refl)

  B²→B²Σ : B² A → B²Σ
  B²→B²Σ (b² grb lnk) = Gerbe.Carrier grb , Gerbe.isGerbe grb , lnk

  B²Σ→B² : B²Σ → B² A
  B²Σ→B² (X , grb , lnk) = b² (gerbe X grb) lnk

  open import Cubical.Foundations.Isomorphism
  open Iso
  B²IsoB²Σ : Iso (B² A) B²Σ
  B²IsoB²Σ = iso B²→B²Σ B²Σ→B² (λ _ → refl) (λ _ → refl)

  B²SNS : SNS B²Struct B²EquivStr
  B²SNS {X = X} (grb1 , lnk1) (grb2 , lnk2) = transport pathLemma (equiv grb2 lnk1' lnk2 ) where
    grb1≡grb2 : grb1 ≡ grb2
    grb1≡grb2 = isPropIsGerbe _ _
    lnk1' : Link (gerbe X grb2) A
    lnk1' = transport (λ i → Link (gerbe X (grb1≡grb2 i)) A) lnk1
    pathLemma : (B²EquivStr (X , grb2 , lnk1') (X , grb2 , lnk2) (idEquiv X) ≃ ((grb2 , lnk1') ≡ (grb2 , lnk2)))
              ≡ (B²EquivStr (X , grb1 , lnk1 ) (X , grb2 , lnk2) (idEquiv X) ≃ ((grb1 , lnk1 ) ≡ (grb2 , lnk2)))
    pathLemma i = B²EquivStr (X , finalLemma i) (X , grb2 , lnk2) (idEquiv X) ≃ (finalLemma i ≡ (grb2 , lnk2)) where
      finalLemma : (grb2 , lnk1') ≡ (grb1 , lnk1)
      finalLemma = sym (ΣPathP (grb1≡grb2 , toPathP refl))
    module _ (grb : IsGerbe X) (l1 l2 : Link (gerbe X grb) A) where
      module l1 = Link l1
      module l2 = Link l2
      G : Gerbe
      G = gerbe X grb
      α : B²Struct X
      α = grb , l1
      β : B²Struct X
      β = grb , l2

      isPropGoal : isProp (B²EquivStr (X , α) (X , β) (idEquiv X))
      isPropGoal = isSetGroupHom _ _

      fun1 : B²EquivStr (X , α) (X , β) (idEquiv X) → α ≡ β
      fun1 p = ΣPathP (refl , linkEq (funExt lemma2)) where
        lemma1 : (x : ⟨ G ⟩) → l2.e x ∘ invEq (l1.eq x) ≡ λ y → y
        lemma1 x = cong GroupHom.fun (sym (congLink-carac l1 l2 (λ y → y) x) ∙ p)
        lemma2 : (x : ⟨ G ⟩) → l1.e x ≡ l2.e x
        lemma2 x = l1.e x                            ≡⟨ cong (_∘ l1.e x) (sym (lemma1 x)) ⟩
                   l2.e x ∘ invEq (l1.eq x) ∘ l1.e x ≡⟨ cong (l2.e x ∘_) (funExt λ y → (secEq (l1.eq x) y)) ⟩
                   l2.e x ∎
      fun2 : α ≡ β → B²EquivStr (X , α) (X , β) (idEquiv X)
      fun2 p = recPropTrunc isPropGoal (λ x₀ → congLink-carac _ _ _ x₀ ∙ groupHomEq (lemma x₀)) (Gerbe.inhabited G) where
        q : l1 ≡ l2
        q = transport path (cong snd p) where
          path : PathP (λ i → Link (gerbe X (fst (p i))) A) (snd α) (snd β) ≡ PathP (λ i → Link (gerbe X grb) A) l1 l2
          path j = PathP (λ i → Link (gerbe X (isProp→isSet isPropIsGerbe grb grb (cong fst p) refl j i)) A) l1 l2
        lemma : (x : ⟨ G ⟩) → l2.e x ∘ invEq (l1.eq x) ≡ λ y → y
        lemma x = l2.e x ∘ invEq (l1.eq x) ≡⟨ (λ i → l2.e x ∘ invEq (Link.eq (q i) x)) ⟩
                  l2.e x ∘ invEq (l2.eq x) ≡⟨ (funExt λ y → retEq (l2.eq x) y) ⟩
                  (λ y → y) ∎

      equiv : (B²EquivStr (X , α) (X , β) (idEquiv X)) ≃ (α ≡ β)
      equiv = isoToEquiv (iso fun1 fun2 (λ _ → isSetB²Struct _ _ _ _) (λ _ → isPropGoal _ _))

  B²UnivalentStr : UnivalentStr B²Struct B²EquivStr
  B²UnivalentStr = SNS→UnivalentStr B²EquivStr B²SNS

  B²ΣPath : (X Y : B²Σ) → (X ≃[ B²EquivStr ] Y) ≃ (X ≡ Y)
  B²ΣPath = SIP B²UnivalentStr

  B²EquivΣ : (X Y : B² A) → Type _
  B²EquivΣ X Y = B²→B²Σ X ≃[ B²EquivStr ] B²→B²Σ Y

  B²IsoΣPath : {X Y : B² A} → Iso (B²Equiv A X Y) (B²EquivΣ X Y)
  fun B²IsoΣPath eq             = B²Equiv.eq eq , B²Equiv.p eq
  inv B²IsoΣPath (eq , p)       = b²equiv (fst eq) p
  rightInv B²IsoΣPath b         = ΣPathP (equivEq _ _ refl , refl)
  leftInv  B²IsoΣPath eq        = refl

  B²Path : (X Y : B² A) → (B²Equiv A X Y) ≃ (X ≡ Y)
  B²Path X Y =
    B²Equiv A X Y       ≃⟨ isoToEquiv B²IsoΣPath ⟩
    B²EquivΣ X Y        ≃⟨ B²ΣPath _ _ ⟩
    B²→B²Σ X ≡ B²→B²Σ Y ≃⟨ isoToEquiv (invIso (congIso B²IsoB²Σ)) ⟩
    X ≡ Y ■

  uaB² : {X Y : B² A} → B²Equiv A X Y → X ≡ Y
  uaB² = equivFun (B²Path _ _)

  carac-uaB² : {X Y : B² A} → (f : B²Equiv A X Y) → (cong B².Carrier (uaB² f)) ≡ ua (B²Equiv.eq f)
  carac-uaB² e = (refl ∙∙ ua eq ∙∙ refl) ≡⟨ sym (rUnit _) ⟩ ua eq ∎ where open B²Equiv e

open B²ΣTheory using (B²Path ; uaB² ; carac-uaB²) public

module Deloop2 (A : AbGroup {ℓ}) (B : AbGroup {ℓ'}) (f : AbGroupHom A B) {ℓG ℓH : Level}  where
  open B²
  type : B² A {ℓG} → Type _
  type G = Σ[ H ∈ B² B {ℓH} ] Σ[ g ∈ (Carrier G → Carrier H) ] congLink (B².lnk G) (B².lnk H) g ≡ f

  abstract
    isPropType : (G : B² A) → isProp (type G)
    isPropType G = recPropTrunc isPropIsProp lemma (inhabited G) where
      module G = B² G
      lG = G.lnk
      lemma : (x : G.Carrier) → isProp (type G)
      lemma x (H1 , g1 , !1) (H2 , g2 , !2) = ΣPathP (path-H , ΣPathP ((λ i → fst (path-g i)) , toPathP (isSetGroupHom _ _ _ _))) where
        module H1 = B² H1
        module H2 = B² H2
        h1 = g1 x
        h2 = g2 x
        l1 = H1.lnk
        l2 = H2.lnk

        H→ : Σ[ j ∈ (H1.Carrier → H2.Carrier) ] (h2 ≡ j h1) × (congLink l1 l2 j ≡ idGroupHom)
        H→ = deloopUnique l1 l2 idGroupHom h1 h2 .fst

        equiv : B²Equiv B H1 H2
        equiv = b²equiv (H→ .fst) (H→ .snd .snd)
        module equiv = B²Equiv equiv

        path-H : H1 ≡ H2
        path-H = uaB² B equiv

        isDeloop-g1 : deloopType lG l1 f x h1
        isDeloop-g1 = g1 , refl , !1
        isDeloop-g2 : deloopType lG l2 f x h2
        isDeloop-g2 = g2 , refl , !2

        pointed : PathP (λ i → B².Carrier (path-H i)) h1 h2
        pointed = toPathP (
          transport (cong Carrier path-H) h1 ≡⟨ (λ i → transport (carac-uaB² B equiv i) h1) ⟩
          transport (ua equiv.eq) h1         ≡⟨ uaβ equiv.eq h1 ⟩
          equiv.fun h1                       ≡⟨ sym (H→ .snd .fst) ⟩
          h2 ∎)

        path-g : PathP (λ i → deloopType lG (B².lnk (path-H i)) f x (pointed i)) isDeloop-g1 isDeloop-g2
        path-g = toPathP (isContr→isProp (deloopUnique lG l2 f x h2) _ _)

    -- Any pointed gerbe in B² B gives rise to a definition of 2-delooping
    -- If ℓH is (ℓ-suc ℓ'), then the Gerbe of B-torsors will do
    2-deloop-def : (H : B² B {ℓH}) (h : B².Carrier H) (G : B² A) → type G
    2-deloop-def H h G = recPropTrunc (isPropType G) lemma (B².inhabited G) where
      module G = B² G
      module H = B² H
      lemma : B².Carrier G → type G
      lemma x = H , fst deloop , snd (snd deloop) where
        deloop : deloopType G.lnk H.lnk f x h
        deloop = deloopUnique _ _ _ _ _ .fst

  2-deloop : (H : B² B) → B².Carrier H → B² A → B² B
  2-deloop H h = fst ∘ 2-deloop-def H h

module DeloopFunctoriality where
  2-deloop-id : {A : AbGroup {ℓ}} (H : B² A {ℓ'}) (h : B².Carrier H) → Deloop2.2-deloop A A (grouphom (λ x → x) (λ _ _ → refl)) H h ≡ λ x → x
  2-deloop-id {A = A} H h = funExt λ G → cong fst (isPropType G (2-deloop-def H h G) (id-deloop G)) where
    open Deloop2 A A (grouphom (λ x → x) (λ _ _ → refl))
    id-deloop : (G : B² A {ℓ'}) → type G
    id-deloop G = G , (λ x → x) , recPropTrunc (isSetGroupHom _ _) (λ x₀ →
      congLink-carac _ _ _ x₀ ∙ groupHomEq (funExt λ x →
        B².e G x₀ (invEq (B².eq G x₀) x) ≡⟨ retEq (B².eq G x₀) x ⟩ x ∎
      )) (B².inhabited G)

  2-deloop-comp : {A : AbGroup {ℓ}} {B : AbGroup {ℓ'}} {C : AbGroup {ℓ''}} {ℓG ℓH ℓF : Level}
    (H : B² B {ℓH}) (x₀ : B².Carrier H)
    (F : B² C {ℓF}) (y₀ : B².Carrier F)
    (f : AbGroupHom A B) (g : AbGroupHom B C) →
    Deloop2.2-deloop A C (compGroupHom f g) {ℓG = ℓG} F y₀ ≡ Deloop2.2-deloop B C g F y₀ ∘ Deloop2.2-deloop A B f H x₀
  2-deloop-comp {A = A} {B = B} {C = C} H x₀ F y₀ f g = funExt λ G →
    cong fst (Deloop2.isPropType A C (compGroupHom f g) G (Deloop2.2-deloop-def A C (compGroupHom f g) F y₀ G) (comp-deloop G))
    where
    open Deloop2
    comp-deloop : (G : B² A) → Deloop2.type A C (compGroupHom f g) G
    comp-deloop G =
      (2-deloop B C g F y₀ ∘ 2-deloop A B f H x₀) G ,
      (λ x → 2-deloop-def B C g F y₀ _ .snd .fst (2-deloop-def A B f H x₀ G .snd .fst x)) ,
      (congLink (B².lnk G) _ (2-deloop-def B C g F y₀ _ .snd .fst ∘ 2-deloop-def A B f H x₀ G .snd .fst)
        ≡⟨ congLink-comp _ (B².lnk H') _ (2-deloop-def A B f H x₀ G .snd .fst) (2-deloop-def B C g F y₀ _ .snd .fst) ⟩
      compGroupHom (congLink _ (B².lnk H') (2-deloop-def A B f H x₀ G .snd .fst)) (congLink (B².lnk H') (B².lnk F') (2-deloop-def B C g F y₀ _ .snd .fst))
        ≡⟨ (λ i → compGroupHom (2-deloop-def A B f H x₀ G .snd .snd i) (2-deloop-def B C g F y₀ H' .snd .snd i)) ⟩
      compGroupHom f g ∎) where
      H' = 2-deloop A B f H x₀ G
      F' = 2-deloop B C g F y₀ H'

{-
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
