;;; Macros
(define-syntax letg@
  ;; let with state inspection
  (syntax-rules (:)
    [(_ (c : s* ...) e)
     (let ([s* (c-> c 's*)] ...) e)]))
(define-syntax lambdag@
  ;; lambda with state inspection
  (syntax-rules (:)
    [(_ (c) e) (lambda (c) e)]
    [(_ (c : s* ...) e)
     (lambda (c) (letg@ (c : s* ...) e))]))
(define-syntax case-term
  ;; A type dispatcher for mk terms
  (syntax-rules ()
    [(_ e [v e1] [(a d) e2] [atom e3])
     (let ([term e])
       (cond
        [(var? term) (let ([v term]) e1)]
        [(pair? term) (let ([a (car term)] [d (cdr term)]) e2)]
        [else (let ([atom term]) e3)]))]))

(define teq?
  ;; Compares two mk terms
  (lambda (t1 t2)
    (or (eq? t1 t2)
        (and (pair? t1) (pair? t2)
             (teq? (car t1) (car t2))
             (teq? (cdr t1) (cdr t2))))))
(define occurs?
  (lambda (v t S)
    (let occurs? ([t t])
      (let ([t (walk t S)])
        (case-term t
          [u (eq? u v)]
          [(a d) (or (occurs? a) (occurs? d))]
          [atom #f])))))

;;; Variables
(;; name is a symbol, bd is a number
 define var (lambda (name bd) (vector name bd)))
(define var->name (lambda (var) (vector-ref var 0)))
(define var->bd (lambda (var) (vector-ref var 1)))
(define var? vector?)
(define var>?
  ;; v1 is prioritized over v2
  (lambda (v1 v2)
    (let ([n1 (symbol->string (var->name v1))] [bd1 (var->bd v1)]
          [n2 (symbol->string (var->name v2))] [bd2 (var->bd v2)])
      (or (< bd1 bd2)
          (and (= bd1 bd2) (string<? n1 n2))))))

;;; Associations and Environments
(define make-s (lambda (u v) `(,u ,v)))
(define lhs car)
(define rhs cadr)
(define extend (lambda (l r S) `(,(make-s l r) . ,S)))
(define extend-check
  (lambda (v t S)
    (and (not (occurs? v t S))
         (extend v t S))))

;;; Constraints
(define all-constraints '(S C D F))
(define init-S '())
(define init-C 0)
(define init-D '())
(define init-F '())
(define make-c (lambda (S C D F) (list S C D F)))
(define init-c (make-c init-S init-C init-D init-F))
(define c->
  (lambda (c store)
    (rhs (assq store (map list all-constraints c)))))
(define update-S (lambda (c S) (letg@ (c : C D F) (make-c S C D F))))
(define update-C (lambda (c C) (letg@ (c : S D F) (make-c S C D F))))
(define update-D (lambda (c D) (letg@ (c : S C F) (make-c S C D F))))
(define update-F (lambda (c F) (letg@ (c : S C D) (make-c S C D F))))

;;; Answer stream monad (actually just lists)
(define mzero (lambda () '()))
(define unit (lambda (x) `(,x)))
(define choice (lambda (x y) `(,x . ,y)))
(define mplus append)
(define bind (lambda (c* g) (apply mplus (map g c*))))

(define walk
  (lambda (u S)
    (let walk ([u u])
      (cond
       [(and (var? u) (assq u S)) =>
        (lambda (pr) (walk (rhs pr)))]
       [else u]))))

(define walk*
  (lambda (t S)
    (let ([t (walk t S)])
      (case-term t
        [v v]
        [(a d) `(,(walk* a S) . ,(walk* d S))]
        [a a]))))

(define unify
  (lambda (t1 t2 S)
    (let ([t1 (walk t1 S)]
          [t2 (walk t2 S)])
      (cond
       [(eq? t1 t2) S]
       [(and (var? t1) (var? t2))
        (cond
         [(var>? t2 t1) (extend t1 t2 S)]
         [else (extend t2 t1 S)])]
       [(var? t1) (extend-check t1 t2 S)]
       [(var? t2) (extend-check t2 t1 S)]
       [(and (pair? t1) (pair? t2))
        (let ([S+ (unify (car t1) (car t2) S)])
          (and S+ (unify (cdr t1) (cdr t2) S+)))]
       [(equal? t1 t2) S]
       [else #f]))))

(define ==
  (lambda (u v)
    (lambdag@ (c : S D)
      (cond
       [(unify u v S) =>
        (lambda (S+)
          (cond
           [(==fail? S+ D) (mzero)]
           [else (unit (update-S c S+))]))]
       [else (mzero)]))))

(define =/=
  (lambda (u v)
    (lambdag@ (c : S D)
      (cond
       [(unify u v S) =>
        (lambda (S+)
          (let ([pS (prefix-S S+ S)])
            (cond
             [(null? pS) (mzero)]
             [else (unit (update-D c `(,pS . ,D)))])))]
       [else (unit c)]))))

(define ==fail?
  (lambda (S D)
    (=/=-fail? S D)))

(define =/=-fail?
  (lambda (S D)
    (exists (d-fail? S) D)))

(define d-fail?
  (lambda (S)
    (lambda (d)
      (cond
       [(unify* d S) =>
	(lambda (S+) (null? (prefix-S S+ S)))]
       [else #f]))))

(define unify*
  (lambda (S+ S)
    (unify (map lhs S+) (map rhs S+) S)))

(define subsumed?
  ;; Is d subsumed by d*?
  (lambda (d d*)
    (cond
     [(null? d*) #f]
     [else (let ([d^ (unify* (car d*) d)])
             (or (and d^ (eq? d^ d))
                 (subsumed? d (cdr d*))))])))
(define rem-subsumed
  (lambda (D)
    (let rem-subsumed ([D D] [d^* '()])
      (cond
       [(null? D) d^*]
       [(or (;; Is is subsumed by the unprocessed list?
             subsumed? (car D) (cdr D))
            (;; Is it subsumed the processed list?
             subsumed? (car D) d^*))
        (rem-subsumed (cdr D) d^*)]
       [else
        (rem-subsumed (cdr D) `(,(car D) . ,d^*))]))))

(define prefix-S
  (lambda (S+ S)
    (cond
     [(eq? S+ S) '()]
     [else `(,(car S+) . ,(prefix-S (cdr S+) S))])))

;;; Goal constructors
(define fake
  (lambda (expr)
    (lambdag@ (c : F)
      (unit (update-F c `(,expr . ,F))))))

(define succeed (lambdag@ (c) (unit c)))
(define fail (lambdag@ (c) (mzero)))

(define conj2
  (lambda (g1 g2) (lambdag@ (c) (bind (g1 c) g2))))

(define-syntax conj
  (syntax-rules ()
    [(_) succeed]
    [(_ g) g]
    [(_ g g* ...) (conj2 g (conj g* ...))]))

(define disj2
  (lambda (g1 g2) (lambdag@ (c) (mplus (g1 c) (g2 c)))))

(define-syntax disj
  (syntax-rules ()
    [(_) fail]
    [(_ g) g]
    [(_ g g* ...) (disj2 g (disj g* ...))]))

(define-syntax fresh
  (syntax-rules ()
    [(_ (x* ...) g g* ...)
     (letv (x* ...) (conj g g* ...))]))
(define-syntax letv
  (syntax-rules ()
    [(_ (x* ...) g)
     (lambdag@ (c : C)
       (let ([x* (var 'x* C)] ...)
         (g (update-C c (+ C 1)))))]))

(define-syntax conde
  (syntax-rules ()
    [(_ [g g* ...] ...)
     (disj (conj g g* ...) ...)]))

(define-syntax run*
  (syntax-rules ()
    [(_ (q q* ...) g g* ...)
     ((fresh (q q* ...) g g* ... (finalize `(,q ,q* ...)))
      init-c)]))

(define finalize
  (lambda (qs)
    (lambdag@ (final-c) (unit (reify final-c qs)))))

(define reify
  ;; This will return a c with clausal S
  (lambda (c q*)
    (letg@ (c : S D F)
      (let ([t (walk* q* S)]
            [D (walk* D S)]
            [F (walk* F S)])
        (let ([R (get-vars `(,t ,F))])
          (let ([D (rem-subsumed (purify-D D R))])
            `(,t ,D ,F)))))))

(define get-vars
  (lambda (t)
    (case-term t
      [v `(,v)]
      [(a d) (append (get-vars a) (get-vars d))]
      [a '()])))
(define purify-D
  (lambda (D R)
    (filter (lambda (d)
              (not (or (constant? d)
                       (has-iv? d R))))
            D)))
(define constant?
  (lambda (t)
    (case-term t
      [v #f]
      [(a d) (and (constant? a) (constant? d))]
      [atom #t])))
(define has-iv?
  (lambda (t R)
    (let has-iv? ([t t])
      (case-term t
        [v (not (memq v R))]
        [(a d) (or (has-iv? a) (has-iv? d))]
        [atom #f]))))



;;; Code generation techniques

;;; Returning substitution
(define-syntax run*su
  ;; run* with substitutions
  (syntax-rules ()
    [(_ (q q* ...) g g* ...)
     (let ([q (var 'q init-C)] [q* (var 'q* init-C)] ...)
       (let ([qs `(,q ,q* ...)])
         (let ([c* ((conj g g* ... (finalize qs))
                    (update-C init-c (+ init-C 1)))])
           (map (lambda (c) (su c qs)) c*))))]))

(define su
  (lambda (c qs)
    `(,(unify (car c) qs init-S)
      .
      ,(cdr c))))

;;; Anti-unification
(define-syntax run*au
  ;; run* with anti-unification analysis
  (syntax-rules ()
    [(_ (q q* ...) g g* ...)
     (let ([q (var 'q init-C)] [q* (var 'q* init-C)] ...)
       (let ([qs `(,q ,q* ...)])
         (let ([c* ((conj g g* ... (finalize qs))
                    (update-C init-c (+ init-C 1)))])
           (au-extract c* qs))))]))

(define au-extract
  (lambda (c* qs)
    (let ([t* (map car c*)]
          [D* (map cadr c*)]
          [F* (map caddr c*)])
      (let ([au (anti-unify t*)])
        (let ([auS (unify qs au init-S)])
          (let ([S* (map (lambda (t) (prefix-unify au t auS))
                         t*)])
            `(,(purify-S auS init-C)
              ,(map au-helper S* D* F*))))))))

(define prefix-unify
  (lambda (t1 t2 S) (prefix-S (unify t1 t2 S) S)))

(define au-helper
  (lambda (S D F)
    (let ([S (purify-S S AU-BD)]
          [D (walk* D S)]
          [F (walk* F S)])
      `(,S ,D ,F))))

(define purify-S
  (lambda (S date)
    (filter (lambda (s) (<= (var->bd (lhs s)) date))
            S)))

(define anti-unify
  (lambda (t*)
    (let-values
        ([(res _iS)
          (let au ([t* t*] [iS '()])
            (cond
             [;; rule 7: eq? deal with variables as well
              ;; hence, it would not introduce useless new vars
              (for-all (eqp? (car t*)) (cdr t*))
              (values (car t*) iS)]
             [;; rule 8
              (for-all pair? t*)
              (let-values ([(a iS+) (au (map car t*) iS)])
                (let-values ([(d iS++)
                              (au (map cdr t*) iS+)])
                  (values `(,a . ,d) iS++)))]
             [;; rule 9
              (find (lambda (s) (teq? (lhs s) t*)) iS)
              =>
              (lambda (s) (values (rhs s) iS))]
             [;; rule 10
              else
              (let ([new-var
                     (var (au-name (length iS)) AU-BD)])
                (values new-var (extend t* new-var iS)))]))])
      res)))
(define eqp? (lambda (u) (lambda (v) (eq? u v))))

(define AU-BD (+ init-C 0.5))
(define au-name
  (lambda (n) (string->symbol (string-append "au" (number->string n)))))


#!eof
