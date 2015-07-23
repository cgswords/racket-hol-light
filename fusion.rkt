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

;; (define (union l s)
;;   (foldr (lambda (x ls) (if (memq x ls) ls (cons x ls))) s l))

;; Looks up based on the cdr of the pair in the assoc list, where the last
;; argument is a default value if it doesn't fine one.
(define (rev_assocd a l d)
  (cond
    [(findf (lambda (y) (equal? a (cdr y))) l) => car]
    [else d]))

;; Kick off the initial types
(define the_type_constants (box '(("bool" . 0) ("fun" . 2))))

;; Define all returned types
(define (types) (unbox the_type_constants))

;; Lookup funciton for type constants, returns arity if it succeeds
;; assoc in ML sort of had this behaviour, but they use 'can', so I sorta need this
(define (get_type_arity s) 
  (cond
    [(assoc s (types)) => cdr]
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
    [(tyapp s args) (foldr set-union '() (map tyvars args))]
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
    [(assoc s (constants)) => cdr]
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
    [(comb s t)           (set-union (frees s) (frees t))]
    [(lam_abs  bv bod)    (remove bv (frees bod))]))

(define (freesl termlist) (foldr set-union '() (map frees termlist)))

;; Whether all the free variables in a term appear in the list

(define (freesin acc term)
  (match term
    [(var      name type) (member term acc)] 
    [(constant name type) #t]
    [(comb s t)           (and (freesin acc s) (freesin acc t))]
    [(lam_abs  bv bod)    (freesin (cons bv acc) bod)]))

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
    [(comb s t)               (set-union (type_vars_in_term s) (type_vars_in_term t))]
    [(lam_abs (var x ty) bod) (set-union (tyvars ty) (type_vars_in_term bod))]))

;; For name-carrying syntax, we need this early

(define (variant avoid v)
  (cond
    [(not (ormap (lambda (t) (vfree_in v t)) avoid)) v] ;; (not (exists (vfree_in v) avoid)
    [else (match v
            [(var s ty) (variant avoid (var (string-append s "'") ty))]
            [else (error "variant: not a variable")])]))

;; Substitution primitive (for variables only)
(define vsubst
  (letrec 
    ([vsubst (lambda (ilist term)
               (match term
                 [(var      name type)     (rev_assocd term ilist term)] 
                 [(constant name type)     term]
                 [(comb s t)               (comb (vsubst ilist s) (vsubst ilist t))]
                 [(lam_abs (var v ty) bod) 
                  (let ([ilist^ (filter (lambda (tx) (not (equal? (cdr tx) v)) ilist))])
                    (if (null? ilist^)
                        term
                        (let ([bod^ (vsubst ilist^ bod)])
                          (cond
                            [(equal? bod^ bod) term]
                            [(ormap (lambda (tx) (and (vfree_in v (car tx)) (vfree_in (cdr tx) bod))) 
                                    ilist^)
                             (let ([v^ (variant (list bod^) v)])
                               (lam_abs v^ (vsubst `((,v^ . ,v) . ,ilist^) bod)))]
                            [else (abs v bod^)]))))]))])
    (lambda (theta term)
      (cond
        [(null? theta) term]
        [(andmap (lambda (tx) (equal? (type_of (car tx) ) (var-type (cdr tx)))) theta) 
         (vsubst theta term)]
        [else (error "vsubst: Bad substitution list")]))))


;; type instantiation primitive

(define (inst tyin term)
  (letrec
    ([inst (lambda (env tyin term) 
             (match term
               [(var n ty)      (let ([term^ (var n (type_subst tyin ty))])
                                  (if (equal? (rev_assocd term^ env term) term) 
                                      term^
                                      (raise term^)))]
               [(constant c ty) (constant c (type_subst tyin ty))]
               [(comb f x)      (comb (inst env tyin f) (inst env tyin x))]
               [(lam_abs y t)   (let* ([y^ (inst '() tyin y)]
                                       [env^ `((,y . ,y^) . ,env)]) 
                                  (with-handlers 
                                    ([var? (lambda (w^) 
                                             (if (not (equal? w^ y^))
                                                 (raise w^)
                                                 (let* ([ifrees (map (lambda (n) (inst '() tyin n)) (frees t))]
                                                        [y^^ (variant ifrees y^)]
                                                        [z (var (car (dest_var y^^)) (cdr (dest_var y)))])
                                                   (inst env 
                                                         tyin 
                                                         (lam_abs z (vsubst `((,z . ,y)) t))))))])
                                    (lam_abs y^ (inst env^ tyin t))))]))])
    (cond
      [(null? tyin) term]
      [else (inst '() tyin term)])))

;; A few bits of general derived syntax

(define rator comb-term1)
(define rand  comb-term2)

;; Syntax operators for equations

(define (safe_mk_eq l r)
  (let ([ty (type_of l)])
    (comb 
      (comb 
        (constant "=" (tyapp "fun" (list ty (tyapp "fun" (list ty bool_ty))))) 
        l) 
      r)))

(define (dest_eq term) 
  (match term
    [(comb (comb (constant "=" ty) l) r) (cons l r)]
    [else (error "dest_eq")]))

;; Useful to have term union modulo alpha-conversion for assumption lists (Wat)

(define alphaOrder (lambda (x y) 0))
(define term_union list)
(define term_image list)

;; Basic theorem destructors

(define (dest_thm thm)
  (match thm
    ([sequent asl c] (cons asl c))))

(define (hyp thm)
  (match thm
    ([sequent asl c] asl)))

(define (concl thm)
  (match thm
    ([sequent asl c] c)))

;; Basic equality properties. Trans is derivable but included for being fast while I fight

(define (REFL term) (sequent '() (safe_mk_eq term term)))

(define (TRANS s1 s2)
  (match (list s1 s2)
    [(list (sequent asl1 c1) (sequent asl2 c2))
     (let* ([m1  (rand c1)]
            [eql (rator c1)]
            [m2r (dest_eq c2)]
            [m2  (car m2r)]
            [r   (cdr m2r)])
      (if (zero? (alphaOrder m1 m2))
          (sequent (term_union asl1 asl2) (comb eql r))
          (raise "TRANS")))]
     [else (raise "TRANS")]))

;; Congruence properties of equality

(define (MK_COMB s1 s2)
  (match (list s1 s2)
    [(list (sequent asl1 c1) (sequent asl2 c2))
     (let* ([l1r1 (dest_eq c1)]
            [l2r2 (dest_eq c2)]
            [l1 (car l1r1)]
            [r1 (cdr l1r1)]
            [l2 (car l2r2)]
            [r2 (cdr l2r2)])
       (match (type_of l1)
         [(tyapp "fun" `(,ty . ,_)) 
          (if (equal? (type_of l2) ty) 
              (sequent (term_union asl1 asl2) (safe_mk_eq (comb l1 l2) (comb r1 r2)))
              (raise "MK_COMB: types do not agree"))]
         [else (raise "MK_COMB: not both equations")]))]))

(define (ABS v s)
  (match s
    [(sequent asl c)
     (let* ([lr (dest_eq c)]
            [l  (car lr)]
            [r  (cdr lr)])
       (if (not (ormap (lambda (t) (vfree_in v t)) asl)) ;; not (exists (vfree_in v) asl)
           (sequent asl (safe_mk_eq (lam_abs v l) (lam_abs v r)))
           (raise "ABS")))]
    [else (raise "ABS")]))

;; Trivial case of lambda calculus beta-conversion

(define (BETA term)
  (match term
    [(comb (lam_abs v bod) arg)
     (if (equal? v arg)
         (sequent '() (safe_mk_eq term bod))
         (raise "BETA: not a trivial beta-redex"))]
    [else (raise "BETA: not a trivial beta-redex")]))

;; Rules connected with deduction

(define (ASSUME term)
  (if (equal? (type_of term) bool_ty)
      (sequent (list term) term)
      (raise "ASSUME: not a proposition")))

;; Type and term instantiation

(define (INST_TYPE theta s)
  (let ([inst_fn (lambda (x) (inst theta x))])
    (sequent (term_image inst_fn (sequent-terms s)) (inst_fn (sequent-term s)))))

(define (INST theta s)
  (let ([inst_fn (lambda (x) (vsubst theta x))])
    (sequent (term_image inst_fn (sequent-terms s)) (inst_fn (sequent-term s)))))

;; Handling of axioms

(define the_axioms (box '())) ;; Theorem list

(define (axioms) (unbox the_axioms))

(define (new_axiom term)
  (if (equal? (type_of term) bool_ty)
      (let ([thm (sequent '() term)])
        (set-box! the_axioms (cons (sequent '() term) (axioms)))
        thm)
      (raise "new_axiom: Not a proposition")))

;; Handling of (term) definitions

(define the_definitions (box '())) ;; Theorem list

(define (definitions) (unbox the_definitions))

(define (new_basic_definition term)
  (match term
    [(comb (comb (constant "=" _) (var cname ty)) r)
     (cond
       [(not (freesin '() r)) (raise "new_definition: term not closed")]
       [(not (subset? (type_vars_in_term r) (tyvars ty))) ;; should write subset
        (raise "new_definition: Type variables not reflected in constant")]
       [else (let* ([c (begin (new_constant cname ty) (constant cname ty))]
                    [dth (sequent '() (safe_mk_eq c r))])
               (set-box! the_definitions (cons dth (definitions)))
               dth)])]
     [else (raise "new_basic_definition: malformed input")]))

;; Handling of type definitions

(define (new_basic_type_definition tyname absxrep sqt)
  (let ([absname (car absxrep)]
        [repname (cdr absxrep)])
    (match sqt
      [(sequent asl c)
       (cond
        [(ormap get_const_type (list absname repname)) 
         (raise "new_basic_type_definition: Constant(s) already in use")]
        [(not (equal? asl '())) 
         (raise "new_basic_type_definition: Assumptions in theorem")]
        [else (let* ([Px (dest_comb c)]
                     [P  (car Px)]
                     [x  (cdr Px)])
                (if (not (freesin '() P))
                    (raise "new_basic_type_definition: Predicate is not closed")
                    (let* ([tyvars  (sort (type_vars_in_term P) string<=?)] ;; Why do we sort them?
                           [nothing (new_type tyname (length tyvars))]
                           [aty (tyapp tyname tyvars)]
                           [rty (type_of x)]
                           [absty (tyapp "fun" (list rty aty))]
                           [repty (tyapp "fun" (list aty rty))]
                           [abs   (begin (new_constant absname absty) (constant absname absty))]
                           [rep   (begin (new_constant repname repty) (constant repname repty))]
                           [a (var "a" aty)]
                           [r (var "r" rty)])
                      (cons
                        (sequent '() (safe_mk_eq (comb abs (mk_comb rep a)) a))
                        (sequent '() (safe_mk_eq (comb P r) 
                                                 (safe_mk_eq (mk_comb rep (mk_comb abs r)) r)))))))])])))

;; Stuff that doesn't seem worth putting in (?)

