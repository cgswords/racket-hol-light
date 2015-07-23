#lang racket

(struct hol_type ())
(struct tyvar    hol_type (name))     ;; name : string
(struct tyapp    hol_type (name sig)) ;; name : string, sig: [hol_type]

(struct hol_term ())
(struct var      hol_term (name type))   ;; name : string, type : hol_type
(struct constant hol_term (name type))   ;; name : string, type : hol_type
(struct comb     hol_term (term1 term2)) ;; term1 : hol_term, term2 : hol_term
(struct lam_abs  hol_term (term1 term2)) ;; term1 : hol_term, term2 : hol_term

(struct thm     ())
(struct sequent thm (terms term)) ;; terms : [hol_term], term : hol_term

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Ghetto helpers
(define (try/throw test msg)
  (let ([x test])
    (if x x (error msg))))

(define (union l s)
  (foldr (lambda (x ls) (if (memq x ls) ls (cons x ls))) s l))

;; Looks up based on the cdr of the pair in the assoc list, where the last
;; argument is a default value if it doesn't fine one.
(define (rev_assocd a l d)
  (cond
    [(findf (lambda (y) (eq? a (cdr y))) l) => car]
    [else d]))

;; Kick off the initial types
(define the_type_constants (box '(("bool" . 0) ("fun" . 2))))

;; Define all returned types
(define (types) (unbox the_type_constants))

;; Lookup funciton for type constants, returns arity if it succeeds
;; assoc in ML sort of had this behaviour, but they use 'can', so I sorta need this
(define (get_type_arity s) 
  (cond
    [(assq s (types)) => cdr]
    [else #f])) 

;; Delcare a new type
(define (new_type name arity)
  (if (get_type_arity name)
      (error (format "new_type: type ~s has already been delared" name))
      (set-box! the_type_constants `((,name . ,arity) . ,(types)))))

;; Basic type constructors
(define (mk_type tyop args)
  (let ([arity (try/throw (get_type_arity tyop) (format "mk_type: type ~s has not been defined" tyop))])
    (cond
      [(= arity (length args)) (tyapp tyop args)]
      [else (error (format "mk_type: wrong number of arguments to ~s" tyop))])))

(define mk_vartype tyvar)

;; Basic type destructors

(define (dest_type ty)
  (match ty
    [(tyapp s t) (cons s t)]
    [(tyvar _)   (error "dest_type: type variable is not a constructor")]))

(define (dest_vartype ty)
  (match ty
    [(tyapp _s _t) (error "dest_vartype: type constructor is not a variable")]
    [(tyvar s)     s]))

;; Basic type discriminators

(define is_type    tyapp?)
(define is_vartype tyvar?)

;; Return the type variable in a type and in a list of types
;; itlist appears to be fold
(define (tyvars ty)
  (match ty
    [(tyapp s args) (foldr union '() (map tyvars args))]
    [(tyvar v)      (list v)]))

;; Substitute types for type variables
;; non-variables in the subst list are just ignored (?), as a repetitions (first always taken)
;; I didn't use qmap or any of the other optimizations here because who cares!
;; If it's slow, avoid rebuilding new tyapps and try qmap
;; i is a weird substituion; maybe we'll learn its shape alter
(define (type_subst i ty) 
  (match ty
    [(tyapp tycon args)  
     (tyapp tycon (map (lambda (ty) (type_subst i ty)) args)) ] 
    [else               (rev_assocd ty i ty)]))

(define bool_ty (tyapp "bool" '()))
(define aty     (tyvar "A"))

;; List of the term constants and their types.
;; We begine with just euqality (over all types). We'll add Hilbert's choice operator later.
(define the_term_constants (box `(("=" . ,(tyapp "fun" 
                                                  (list aty (tyapp "fun" (list aty bool_ty))))))))

;; Gets all of the define constants with their types
(define (constants) (unbox the_term_constants))

;; Gets type of constant
(define (get_const_type s)
  (cond
    [(assq s (constants)) => cdr]
    [else #f]))

;; Declare a new constant
(define (new_constant name ty)
  (if (get_const_type name)
      (error (format "new_constant: constant ~s has already been delared" name))
      (set-box! the_term_constants `((,name . ,ty) . ,(constants)))))

;; Find the type of a term (assuming it's well-typed)
(define (type_of term)
  (match term 
    [(var      name type)                                    type] 
    [(constant name type)                                    type]
    [(comb (app type_of (tyapp "fun" (list dty rty))) term2) rty]
    [(lam_abs  (var nm type) term2)                          (tyapp "fun" (list type (type_of term2)))]))

;; primitive discriminators
(define is_var      var?)
(define is_constant constant?)
(define is_abs      lam_abs?)
(define is_comb     comb?)

;; primitive constructors
(define mk_var   var)

(define (mk_const name theta)
  (let ([uty (try/throw (get_const_type name) "mk_const: not a constant name")])
    (const name (type_subst theta uty))))

(define (mk_abs bvar bod)
  (lam_abs (if (var? bvar) bvar (error "mk_abs: not a variable")) bod))

(define (mk_comb f a)
  (match (type_of f)
    [(tyapp "fun" `(,t1  . ,t2s)) 
     (comb (if (equal? t1 (type_of a)) f (error "mk_comb: types do not agree")) a)]
    [else (error "mk_comb: types do not agree")]))

;; primitive destructors
(define (dest_var term)
  (match term
    [(var s ty) (cons s ty)]
    [else (error "dest_var: not a variable")]))

(define (dest_const term)
  (match term
    [(constant s ty) (cons s ty)]
    [else (error "dest_const: not a constant")]))

(define (dest_comb term)
  (match term
    [(comb f x) (cons f x)]
    [else (error "dest_comb: not a combination")]))

(define (dest_abs term)
  (match term
    [(lam_abs v b) (cons v b)]
    [else (error "dest_abs: not an abstraction")]))

;; finds the free variables within a term
(define (frees term)
  (match term
    [(var      name type) (list term)] 
    [(constant name type) '()]
    [(comb s t)           (union (frees s) (frees t))]
    [(lam_abs  bv bod)    (remove bv (frees bod))]))

(define (freesl termlist) (foldr union '() (map frees termlist)))

;; Whether all the free variables in a term appear in the list

(define (frees_in acc term)
  (match term
    [(var      name type) (member term acc)] 
    [(constant name type) #t]
    [(comb s t)           (and (frees acc s) (frees acc t))]
    [(lam_abs  bv bod)    (frees_in (cons bv acc) bod)]))

;; Whether a variable (or constant in fact) is free in a term
(define (vfree_in v term)
  (match term
    [(lam_abs  bv bod)    (and (not (equal? bv v)) (vfree_in v bod))]
    [(comb s t)           (or (vfree_in v s) (vfree_in v t))]
    [else (equal? term v)]))

;; Find the type variables (free) in a term

(define (type_vars_in_term term)
  (match term
    [(var      name type)     (tyvars type)] 
    [(constant name type)     (tyvars type)]
    [(comb s t)               (union (type_vars_in_term s) (type_vars_in_term t))]
    [(lam_abs (var x ty) bod) (union (tyvars ty) (type_vars_in_term bod))]))

;; For name-carrying syntax, we need this early

(define (variant avoid v)
  (cond
    [(not (ormap (lambda (t) (vfree_in v t)) avoid)) v]
    [else (match v
            [(var s ty) (variant avoid (var (string-append s "'") ty))]
            [else (error "variant: not a variable")])]))

