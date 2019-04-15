(define truet (lambda () (lambda (?) (== #t ?))))
(define falset (lambda () (lambda (?) (== #f ?))))

(define ==t
  (lambda (x y)
    (lambda (?)
      (conde
       [(== #t ?) (== x y)]
       [(== #f ?) (=/= x y)]))))

(define =/=t
  (lambda (x y) (negt (==t x y))))

(define negt
  (lambda (g)
    (lambda (?)
      (conde
       [(== #t ?) (g #f)]
       [(== #f ?) (g #t)]))))

(define-syntax conjt
  ;; A conjunction test
  (syntax-rules ()
    [(_) (truet)]
    [(_ g) g]
    [(_ g1 g2 gs ...)
     (lambda (?)
       (conde
        [(g1 #t) ((conjt g2 gs ...) ?)]
        [(== #f ?) (g1 #f)]))]))

(define-syntax disjt
  ;; A disjunction test
  (syntax-rules ()
    [(_) (falset)]
    [(_ g) g]
    [(_ g1 g2 gs ...)
     (lambda (?)
       (conde
        [(== #t ?) (g1 #t)]
        [(g1 #f)  ((disjt g2 gs ...) ?)]))]))

(define-syntax fresht
  (syntax-rules ()
    [(_ (idens ...) gs ...)
     (lambda (?) (fresh (idens ...) ((conjt gs ...) ?)))]))

;; Next: condt?

(define-syntax condo
  ;; Literally the relational version of 'cond'
  ;; Fails if no clauses match
  (syntax-rules (else)
    [(_ [else]) succeed]
    [(_ [else g]) g]
    [(_ [else g1 g2 g* ...])
     (fresh () g1 g2 g* ...)]
    [(_ [test g* ...] c* ...)
     (conde
      [(test #t) g* ...]
      [(test #f) (condo c* ...)])]
    [(_) fail]))
