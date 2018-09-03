(define apply-env
  (lambda (env var)
    (cond
      [(null? env) (error 'apply-env (format "Unbound variable: ~s" var))]
      [(assq var (car env)) => cdr]
      [else (apply-env (cdr env) var)])))

(define extend-env
  (lambda (formals args env)
    (cons (map cons formals args) env)))

(define free-vars
  (lambda (exp)
    (cond
      ((and (symbol? exp) (not (memq exp '(zero? + - * if))))
       (list exp))
      ((and (pair? exp) (eq? (car exp) 'lambda))
       (set-diff (free-vars (caddr exp)) (cadr exp)))
      ((pair? exp)
       (append (free-vars (car exp)) (free-vars (cdr exp))))
      (else (list)))))

(define set-diff
  (lambda (a b)
    (if (null? b) a
        (set-diff (remq (car b) a) (cdr b)))))

(define potentially-apply-procedure
  (lambda (eval)
    (lambda (proc args)
      (match proc
        [(closure ,formals ,body ,env)
         (eval body (extend-env formals args env))]
        [,else (error 'potentially-apply-procedure
                      (format "Cannot apply closure: ~s" proc))]))))

(define potentially-recursive-eval-maker
  (lambda (D-int D-bool D-zero? D-plus D-minus D-times D-if D-closure D-apply-hov)
    (lambda (eval)
      (lambda (exp env)
        (match exp
          [,int (guard (integer? int)) (D-int int)]
          [,bool (guard (boolean? bool)) (D-bool bool)]
          [,var (guard (symbol? var)) (apply-env env var)]
          [(zero? ,e1) (D-zero? (eval e1 env))]
          [(+ ,e1 ,e2) (D-plus (eval e1 env) (eval e2 env))]
          [(- ,e1 ,e2) (D-minus (eval e1 env) (eval e2 env))]
          [(* ,e1 ,e2) (D-times (eval e1 env) (eval e2 env))]
          [(if ,test-exp ,then-exp ,else-exp)
          ((D-if eval) test-exp then-exp else-exp env)]
          [(lambda ,formals ,body) (D-closure `(closure ,formals ,body ,env))]
          [,else
           (let ([rator (car exp)]
                 [rands (cdr exp)])
             ((D-apply-hov eval) (eval rator env)
              (map (lambda (x) (eval x env)) rands)))])))))

(define Ds-int
  (lambda (x)
    (cond
      [(positive? x) 1]
      [(negative? x) -1]
      [else 0])))

(define Ds-bool
  (lambda (x)
    'bottom))

(define Ds-zero?
  (lambda (x)
    (match x
      [bottom 'bottom]
      [,x (guard (integer? x)) (zero? x)]
      [,else 'top])))

(define Ds-plus
  (lambda (x y)
    (match `(,x ,y)
      [(bottom ,y) 'bottom]
      [(,x bottom) 'bottom]
      [(,x ,y) (guard (integer? x) (integer? y))
       (cond
         [(or (zero? x) (zero? y)) (+ x y)]
         [(= x y) x]
         [else 'top])]
      [,else 'top])))

(define Ds-minus
  (lambda (x y)
    (match `(,x ,y)
      [(bottom ,y) 'bottom]
      [(,x bottom) 'bottom]
      [(,any ,y) (guard (integer? y)) (Ds-plus any (- y))]
      [,else 'top])))

(define Ds-times
  (lambda (x y)
    (match `(,x ,y)
      [(bottom ,y) 'bottom]
      [(,x bottom) 'bottom]
      [(,x ,y) (guard (integer? x) (integer? y)) (* x y)]
      [,else 'top])))

(define Ds-closure-equiv?
  (lambda (cl-x cl-y)
    (match `(,cl-x ,cl-y)
      [((closure ,formals-x ,body-x ,env-x)
        (closure ,formals-y ,body-y ,env-y))
       (and
        (eq? body-x body-y)
        (andmap
         (lambda (var)
           (Ds-equiv? (apply-env env-x var) (apply-env env-y var)))
         (set-diff (free-vars body-x) formals-x)))])))

(define Ds-equiv?
  (lambda (x y)
    (match `(,x ,y)
      [(,x ,y) (guard (eq? x y)) #t]
      [((hov ,closures-x) (hov ,closures-y)) (seq-equiv? closures-x closures-y)]
      [((top ,closures-x) (top ,closures-y)) (seq-equiv? closures-x closures-y)]
      [,else #f])))

(define cache-maker
  (lambda (binary-predicate? not-found-value-constructor)
    (let ([cache '()])
      (lambda (target)
        (letrec
            ([lookup
              (lambda (table)
                (cond
                  [(null? table)
                   (let ([value (not-found-value-constructor target)])
                     (set! cache (cons `(,target . ,value) cache))
                     value)]
                  [(binary-predicate? target (caar table)) (cdar table)]
                  [else (lookup (cdr table))]))])
          (lookup cache))))))

(define initialize-hov-cache
  (lambda ()
    (set! **hov-cache** (cache-maker (lambda (x y) (Ds-closure-equiv? (car x) (car y))) (lambda (target) (list 'hov target))))))

(define Ds-closure
  (lambda (closure)
    (**hov-cache** (list closure))))

(define Ds-lub
  (lambda (x y)
    (match `(,x ,y)
      [(,x ,y) (guard (Ds-equiv? x y)) x]
      [(bottom ,y) y]
      [(,x bottom) x]
      [(,x ,y) (guard (integer? x) (integer? y)) (Ds-plus x y)]
      [((hov ,closures-x) (hov ,closures-y))
       (**hov-cache** (union closures-x closures-y))]
      [((hov ,closures-x) ,y) `(top ,closures-x)]
      [(,x (hov ,closures-y)) `(top ,closures-y)]
      [((top ,closures-x) (top ,closures-y))
       `(top ,(union closures-x closures-y))]
      [(top ,y) 'top]
      [(,x top) 'top]
      [,else (error 'Ds-lub (format "Cannot take lub of ~s and ~s" x y))])))

(define Ds-lub-map
  (lambda (f l)
    (cond
      [(null? l) 'bottom]
      [else (Ds-lub (f (car l)) (Ds-lub-map f (cdr l)))])))

(define Ds-apply-hov
  (lambda (eval)
    (let ([apply-procedure (potentially-apply-procedure eval)])
      (lambda (hov args)
        (match hov
          [bottom 'bottom]
          [(hov ,closures)
           (Ds-lub-map (lambda (proc)
                         (apply-procedure proc args))
                       closures)]
          [,else (error 'Ds-apply-hov (format "Unmatched ~s" hov))])))))

(define Ds-if
  (lambda (eval)
    (lambda (test-exp then-exp else-exp env)
      (let ([test (eval test-exp env)])
        (Ds-lub (eval then-exp env) (eval else-exp env))))))

(define fix-maker
  (lambda (binary-op predicate?)
    (lambda (memo thunk)
      (letrec
          ([fix-loop
            (lambda ()
              (let ([value (binary-op (thunk) (cdr memo))])
                (cond
                  [(predicate? value (cdr memo)) value]
                  [else (begin
                          (set-cdr! memo value)
                          (fix-loop))])))])
        (fix-loop)))))

(define fix-memo (fix-maker Ds-lub Ds-equiv?))

(define fix-finite
  (lambda (potentially-recursive-eval)
    (let ([stack '()])
      (letrec
          ([eval (potentially-recursive-eval
                  (lambda (exp env)
                    (cond
                      [(assq exp stack) => cdr]
                      [else (let ([memo (cons exp 'bottom)]
                                  [thunk (lambda () (eval exp env))])
                              (set! stack (cons memo stack))
                              (let ([value (fix-memo memo thunk)])
                                (set! stack (cdr stack))
                                value))])))])
        eval))))

(define Ds-eval
  (fix-finite
   (potentially-recursive-eval-maker
    Ds-int Ds-bool Ds-zero? Ds-plus Ds-minus Ds-times Ds-if Ds-closure Ds-apply-hov)))

(initialize-hov-cache)
