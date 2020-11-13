#lang racket/base

(require redex/reduction-semantics)

;; Syntax
(define-language
  Fω

  ;; Terms
  (e ::=
     x
     (λ x e)
     (e_1 [e_2 τ])
     (Λ α e)
     (e [α τ_1] [τ_2 k])
     )

  ;; Kinds
  (k ::=
     ⋆
     (k_1 ⇒ k_2)
     )

  ;; Types
  (τ ::=
     void
     (τ_1 → τ_2)
     (∀ [α k] τ)
     α
     (λ α τ)
     (τ_1 [τ_2 k])
     )

  ;; Normal Types
  (τⱽ ::=
      τᴺ
      (λ α τⱽ)
      )

  ;; Neutral Types
  (τᴺ ::=
      void
      (τᴺ_1 → τᴺ_2)
      (∀ [α k] τᴺ)
      α
      (τᴺ [τⱽ k])
      )

  ;; Type Evaluation Contexts
  (τᴱ ::=
      hole
      (τᴱ → τ)
      (τⱽ → τᴱ)
      (∀ [α k] τᴱ)
      (λ α τᴱ)
      (τᴱ [τ k])
      (τⱽ [τᴱ k])
      )

  ;; Type Environments
  (Γ ::=
     (x τ Γ)
     ∙
     )

  ;; Kind Environments
  (Δ ::=
     (α k Δ)
     ∙
     )

  ;; Variables
  (x y ::= variable-not-otherwise-mentioned)
  (α β ::= variable-not-otherwise-mentioned)

  ;; Binding forms
  #:binding-forms
  (λ x e #:refers-to x)
  (Λ α e #:refers-to α)
  (e [α τ_1 #:refers-to α] [τ_2 k])
  (∀ [α k] τ #:refers-to α)
  (λ α τ #:refers-to α)
  (λ α τⱽ #:refers-to α)
  (∀ [α k] τᴺ #:refers-to α)
  (∀ [α k] τᴱ #:refers-to α)
  (λ α τᴱ #:refers-to α)
  )

;; Kind Lookup
(define-metafunction
  Fω
  kind-lookup : Δ α -> k or #f
  [(kind-lookup (α k Δ) α) k]
  [(kind-lookup (α k Δ) α_2) (kind-lookup Δ α_2)]
  [(kind-lookup ∙ α) #f]
  )

;; Kind Checking
(define-judgment-form
  Fω
  #:mode (kindof I I I)
  #:contract (kindof Δ τ k)

  [-----------------
   (kindof Δ void ⋆)]

  [(kindof Δ τ_1 ⋆)
   (kindof Δ τ_2 ⋆)
   ------------------------
   (kindof Δ (τ_1 → τ_2) ⋆)]

  [(kindof (α k Δ) τ ⋆)
   ----------------------
   (kindof Δ (∀ [α k] τ) ⋆)]

  [(where k (kind-lookup Δ α))
   ---------------------------
   (kindof Δ α k)]

  [(kindof (α k_1 Δ) τ k_2)
   ------------------------------
   (kindof Δ (λ α τ) (k_1 ⇒ k_2))]

  [(kindof Δ τ_1 (k_1 ⇒ k_2))
   (kindof Δ τ_2 k_1)
   ------------------------------
   (kindof Δ (τ_1 [τ_2 k_1]) k_2)]
  )

(test-equal (judgment-holds (kindof ∙ void ⋆)) #t)
(test-equal (judgment-holds (kindof ∙ (λ α α) (⋆ ⇒ ⋆))) #t)
(test-equal (judgment-holds (kindof ∙ (∀ (α ⋆) (α → α)) ⋆)) #t)

;; Type Reduction
(define type-red
  (reduction-relation
   Fω
   #:domain τ
   #:codomain τ
   #:arrow ⟶τ
   (⟶τ
    (in-hole τᴱ ((λ α τ_1) [τ_2 k]))
    (in-hole τᴱ (substitute τ_1 α τ_2)))
   ))

(test-->> type-red (term ((λ α α) [void ⋆])) (term void))
(test-->> type-red (term ((λ α (α → α)) [void ⋆])) (term (void → void)))
(test-results)

;; Test Progress and Determinism
(define (singleton? l)
  (and (pair? l) (null? (cdr l))))
(define (type-normal? τ)
  (redex-match? Fω τⱽ (term τ)))
(define (type-neutral? τ)
  (redex-match? Fω τᴺ (term τ)))
(define (type-reduces? τ)
  (singleton? (apply-reduction-relation type-red (term τ))))
(redex-check Fω
             #:satisfying
             (kindof ∙ τ k)
             (or (type-normal? (term τ))
                 (type-reduces? (term τ)))
             #:attempts 100)

;; Deterministic Reduction
(define (apply-type-red τ)
  (car (apply-reduction-relation type-red (term τ))))

;; Type Lookup
(define-metafunction
  Fω
  type-lookup : Γ x -> τ or #f
  [(type-lookup (x τ Γ) x) k]
  [(type-lookup (x τ Γ) x_2) (type-lookup Γ x_2)]
  [(type-lookup ∙ x) #f]
  )

;; Type Checking
(define-judgment-form
  Fω
  #:mode (typeof I I I I)
  #:contract (typeof Γ Δ e τ)

  [(where τ (type-lookup Γ x))
   ---------------------------
   (typeof Γ Δ x τ)]

  [(typeof (x τ_1 Γ) Δ e τ_2)
   --------------------------------
   (typeof Γ Δ (λ x e) (τ_1 → τ_2))]

  [(typeof Γ Δ e_1 (τ_1 → τ_2))
   (typeof Γ Δ e_2 τ_1)
   --------------------------------
   (typeof Γ Δ (e_1 [e_2 τ_1]) τ_2)]

  [(typeof Γ (α k Δ) e τ)
   --------------------------------
   (typeof Γ Δ (Λ α e) (∀ [α k] τ))]

  [(typeof Γ Δ e (∀ [α k] τ_1))
   (kindof Δ τ_2 k)
   (where τ (apply-type-red ((λ α τ_1) (τ_2 k))))
   ----------------------------------------------
   (typeof Γ Δ (e [α τ_1] [τ_2 k]) τ)]
  )
