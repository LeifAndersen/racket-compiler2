#lang racket/base

(require nanopass/base
         syntax/parse
         racket/match
         racket/set
         racket/dict
         racket/hash
         racket/port
         racket/list
         racket/function
         racket/bool
         racket/stxparam
         racket/stxparam-exptime
         racket/block
         racket/splicing
         compiler/zo-marshal
         syntax/toplevel
         syntax/strip-context
         rackunit
         (prefix-in zo: compiler/zo-structs)
         (rename-in racket/base
                    [compile base:compile]
                    [current-compile base:current-compile])
         (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     racket/stxparam
                     racket/stxparam-exptime)
         "languages.rkt"
         "utils.rkt"
         "components.rkt"
         "compiler.rkt")

(module+ test
  (require rackunit
           rackunit/text-ui)

  (provide (all-defined-out))

  ;; Store of all tests created with define-compiler-test
  (define all-compiler-tests '())

  ; Defines a test-suite for nanopass,
  ; binds quasiquote to the language, test called `lang`-tests
  ; lang tests ... -> void
  (define-syntax (define-compiler-test stx)
    (syntax-parse stx
      [(_ lang form body ...+)
       #:with with-output-language (format-id stx "with-output-language")
       #:with name (format-id stx "~a-tests~a" #'lang (gensym))
       #:with current-compile (format-id stx "current-compile")
       #`(begin
           (define name
               (with-output-language (lang form)
                 (let ([current-compile current-compile-top])
                   (test-suite
                    (format "Test suite for: ~a" '#,(syntax->datum #'lang))
                    (test-case (format "Test case for: ~a" '#,(syntax->datum #'lang))
                               body) ...))))
           (set! all-compiler-tests (cons name all-compiler-tests)))]))

  ;; Run all tests defined with define-compiler-test
  (define-syntax-rule (run-all-compiler-tests)
    (let ()
      (define res (map run-tests (reverse all-compiler-tests)))
      (exit-handler (lambda (code)
                      (max code (min (apply + res) 255))))
      (void)))

  (define current-visited-structs (make-parameter (set)))

  (define (compiler-equal? actual expected)
    (cond [(set-member? (current-visited-structs) (cons actual expected))
           #t]
          [(and (syntax? actual) (syntax? expected))
           (equal? (syntax->datum actual) (syntax->datum expected))]
          [(and (variable? actual) (variable? expected))
           (equal? (variable-name actual) (variable-name expected))]
          [else
           (parameterize ([current-visited-structs
                           (set-add (current-visited-structs) (cons actual expected))])
             (equal?/recur actual expected compiler-equal?))]))
  (define-binary-check (check-compiler-equal? compiler-equal? actual expected))

  ;; Compare result of current compiler to regular compiler
  (define-syntax (compile-compare stx)
    (syntax-case stx ()
      [(_ expression)
       #`(test-case "Test case for finished compiler"
           #,(quasisyntax/loc stx
               (check-equal?
                (parameterize ([current-namespace (make-base-namespace)])
                  (namespace-require 'racket/undefined)
                  #,(quasisyntax/loc stx
                      (eval #,(syntax/loc stx
                                (compile (namespace-syntax-introduce
                                          (strip-context expression)))))))
                (parameterize ([current-namespace (make-base-namespace)])
                  (namespace-require 'racket/undefined)
                  (eval (namespace-syntax-introduce
                         (strip-context expression)))))))]))

  ;; Used to update the current compiler while testing
  (define current-compile-number 1)
  (define current-compile-top (list-ref compilers current-compile-number))
  (define (update-current-compile!)
    (set! current-compile-number (+ current-compile-number 1))
    (set! current-compile-top (list-ref compilers current-compile-number))))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
   (define x (make-variable 'x))
   (define a (make-variable 'a))
   (define b (make-variable 'b))
   (define c (make-variable 'c))
   (define match (make-variable 'match))
   (define match2 (make-variable 'match2))
   (define-compiler-test Lsrc top-level-form
      (check-compiler-equal?
       (current-compile #'(lambda (x) x))
       `(#%expression (#%plain-lambda (,x) ,x)))
      (check-compiler-equal?
       (current-compile #'(module outer racket
                            (#%plain-module-begin
                             (module* post racket
                               (#%plain-module-begin
                                (+ 1 2)))
                             (+ 3 4)
                             (module pre racket
                               (#%plain-module-begin
                                (+ 5 6))))))
       `(module outer racket
          ((submodule* post racket
                       ((#%plain-app (primitive +) '1 '2)))
           (#%plain-app (primitive +) '3 '4)
           (submodule pre racket
                      ((#%plain-app (primitive +) '5 '6))))))
      (check-compiler-equal?
       (current-compile #'(begin-for-syntax
                            (define x 5)))
       `(begin-for-syntax*
          (define-values (,x) '5)))
      (check-compiler-equal?
       (current-compile #'(module test racket
                            (#%plain-module-begin
                             (begin-for-syntax
                               (define x 5)))))
       `(module test racket
          ((begin-for-syntax
             (define-values (,x) '5)))))
     ;; XXX The ,'() ... should NOT be needed
      (check-compiler-equal?
       (current-compile #'(lambda () 5))
       `(#%expression (#%plain-lambda (,'() ...) '5)))
      (check-compiler-equal?
       (current-compile #'(lambda (a b . c)
                            (apply + a b c)))
       `(#%expression (#%plain-lambda (,a ,b . ,c)
                                      (#%plain-app (primitive apply) (primitive +) ,a ,b ,c))))
      (check-compiler-equal?
       (current-compile #'(module foo racket/base
                            (#%plain-module-begin
                             (require racket/match)
                             (#%provide (all-from-except racket/match match)))))
       `(module foo racket/base
          ((#%require racket/match)
           (#%provide (all-from-except racket/match ,(make-variable 'match))))))
      (check-compiler-equal?
       (current-compile #'(module bar racket/base
                            (#%plain-module-begin
                             (#%require (for-template racket/base)
                                        (for-label racket/base)
                                        (just-meta 0 racket))
                             42)))
       `(module bar racket/base
          ((#%require (for-meta -1 racket/base)
                      (for-meta #f racket/base)
                      (just-meta 0 racket))
           '42)))
      (check-compiler-equal?
       (current-compile #'(module bar racket/base
                            (#%plain-module-begin
                             (#%require (only racket/match match)
                                        (all-except racket/match match)
                                        (rename racket/match match2 match)
                                        (prefix match2: racket/match)
                                        (prefix-all-except match: racket/match match)
                                        ; TODO (planet "match" ("match" "match")) ; Not a real package
                                        ))))
       `(module bar racket/base
          ((#%require (only racket/match ,match)
                      (all-except racket/match ,match)
                      (rename racket/match ,match2 ,match)
                      (prefix-all-except match2: racket/match)
                      (prefix-all-except match: racket/match ,match)
                      ; TODO (planet "match" ("match" "match"))
                      ))))
      (check-compiler-equal?
       (current-compile #'(module bar racket
                            (#%plain-module-begin
                             (define x 5)
                             (provide x))))
       `(module bar racket
          ((define-values (,x) '5)
           (#%provide ,x))))
      (let*-values ([(code) (current-compile #'(begin (define x 5)
                                                      x))]
                    [(v1 v2) (nanopass-case (Lsrc top-level-form) code
                                            [(begin* (define-values (,var1) ,expr)
                                                     ,var2)
                                             (values var1 var2)])])
        (check-true (eq? v1 v2)))
     (check-compiler-equal?
      (current-compile #`(eval #'(+ 1 2)))
      `(#%plain-app (primitive eval) (quote-syntax ,#'(+ 1 2))))
     (check-compiler-equal?
      (current-compile #`(eval (quote-syntax (+ 1 2) #:local)))
      `(#%plain-app (primitive eval) (quote-syntax-local ,#'(+ 1 2))))
     (check-compiler-equal?
      (current-compile #'(begin
                           (define x 5)
                           (#%variable-reference (#%top . x))))
      `(begin*
         (define-values (,x) '5)
         (#%variable-reference-top ,x)))
     (check-compiler-equal?
      (current-compile #'(module foo racket/base
                           (#%plain-module-begin
                            (#%require (for-label racket/match))
                            (#%provide (for-label match))
                            (define x 5)
                            (#%provide (protect x)))))
      `(module foo racket/base
         ((#%require (for-meta #f racket/match))
          (#%provide (for-meta* #f ,match))
          (define-values (,x) '5)
          (#%provide (protect ,x)))))
     (check-compiler-equal?
      (current-compile #'(module foo racket/base
                           (#%plain-module-begin
                            (module bar racket/base
                              (#%plain-module-begin
                               42))
                            (#%require (submod "." bar)))))
      `(module foo racket/base
         ((submodule bar racket/base
            ('42))
          (#%require (submod "." bar))))))))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
   (define x (make-variable 'x))
   (define-compiler-test Lsubmodules top-level-form
      (check-compiler-equal?
       (current-compile #'(module foo racket/base
                            (#%plain-module-begin
                             (module bar racket/base
                               (#%plain-module-begin
                                12))
                             (define x 5)
                             (module* baz racket/base
                               (#%plain-module-begin
                                1)))))
       `(module foo racket/base
          ((#%plain-app (primitive void))
           (define-values (,x) '5)
           (#%plain-app (primitive void)))
          ((module bar racket/base
             ('12) () ()))
          ((module baz racket/base
             ('1) () ()))))
      (check-compiler-equal?
       (current-compile #'(module outer racket
                            (#%plain-module-begin
                             (begin-for-syntax
                               (define x 6)
                               (module* test #f
                                 (#%plain-module-begin
                                  x))))))
       `(module outer racket
          ((begin-for-syntax
             (define-values (,x) '6)
             (#%plain-app (primitive void))))
          ()
          ((module test #f
             (,x) () ()))))
      (check-compiler-equal?
       (current-compile #'(module outer racket
                            (#%plain-module-begin
                             (module* inner #f
                               (#%plain-module-begin
                                5)))))
       `(module outer racket
          ((#%plain-app (primitive void)))
          ()
          ((module inner #f
             ('5) () ()))))
      (check-compiler-equal?
       (current-compile #'(module foo racket/base
                            (#%plain-module-begin
                             (begin
                               (module bar racket/base
                                 (#%plain-module-begin
                                  5))
                               (module baz racket/base
                                 (#%plain-module-begin
                                  6))
                               (define x 5))
                             x)))
       `(module foo racket/base
          ((#%plain-app (primitive void))
           (#%plain-app (primitive void))
           (define-values (,x) '5)
           ,x)
          ((module bar racket/base
             ('5) () ())
           (module baz racket/base
             ('6) () ()))
          ()))
      (check-compiler-equal?
       (current-compile #'(module foo racket/base
                            (#%plain-module-begin
                             (module bar racket/base
                               (#%plain-module-begin
                                (module baz racket/base
                                  (#%plain-module-begin
                                   42)))))))
       `(module foo racket/base
          ((#%plain-app (primitive void)))
          ((module bar racket/base
             ((#%plain-app (primitive void)))
             ((module baz racket/base
                ('42)
                () ()))
             ()))
          ())))))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
   (define x (make-variable 'x))
   (define-compiler-test Lreqprov top-level-form
     (check-compiler-equal?
       (current-compile #'(module foo racket
                            (#%plain-module-begin
                             (#%require (for-syntax racket/match)
                                        (for-meta 2 racket/list))
                             (#%provide (for-syntax (all-from-except racket/match match))
                                        (for-meta 2 (all-from-except racket/list))
                                        (all-defined)))))
       `(module foo racket
          ((for-meta* 1 (all-from-except racket/match ,(make-variable 'match)))
           (for-meta* 2 (all-from-except racket/list))
           (all-defined-except))
          ((for-meta 1 racket/match)
           (for-meta 2 racket/list))
          ((#%plain-app (primitive void)) (#%plain-app (primitive void)))
          () ()))
      (check-compiler-equal?
       (current-compile #'(module foo racket/base
                            (#%plain-module-begin
                             (begin-for-syntax
                               (define x 5)
                               (#%provide x)))))
       `(module foo racket/base
          ((for-meta* 1 ,x))
          ()
          ((begin-for-syntax
             (define-values (,x) '5)
             (#%plain-app (primitive void))))
          () ())))))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
    (define x (make-variable 'x))
    (define-compiler-test Lsyntax top-level-form
      (check-compiler-equal?
       (current-compile #'(module foo racket
                            (#%plain-module-begin
                             (begin-for-syntax
                               (define x 5))
                             (define-syntax foo (lambda (x) x)))))
       `(module foo racket
          () ()
          ((#%plain-app (primitive void))
           (#%plain-app (primitive void)))
          ((syntax 1 ((begin-for-syntax
                        (define-values (,x) '5))
                      (define-syntaxes (,(make-variable 'foo)) (#%plain-lambda (,x) ,x)))))
          () ())))))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
    (define x* (make-variable 'x))
    (define y (make-variable 'y))
    (define z (make-variable 'z))
    (define-compiler-test Lmodulevars top-level-form
      (check-compiler-equal?
       (current-compile #'(module foo racket
                            (#%plain-module-begin
                             (define x 5)
                             (define-syntax y 6)
                             (begin-for-syntax
                               (define z 8)))))
       `(module foo racket (,x*) (,y)
                () ()
                ((define-values (,x*) '5)
                 (#%plain-app (primitive void))
                 (#%plain-app (primitive void)))
                ((syntax 1 (,z) ()
                         ((define-syntaxes (,y) '6)
                          (begin-for-syntax
                            (define-values (,z) '8)))))
                () ()))
      (check-compiler-equal?
       (current-compile #'(begin
                            (module foo racket
                              (#%plain-module-begin
                               (provide x)
                               (define x 5)))
                            (require 'foo)
                            x))
       `(begin*
          (module foo racket (,x*) ()
                  (,x*) ()
                  ((#%plain-app (primitive void))
                   (define-values (,x*) '5))
                  ()
                  () ())
          (#%require (quote* foo))
          ,x*)))))

;; ===================================================================================================

;; TODO, these tests
(module+ test
  (update-current-compile!)
  #;(block
    (define x (make-variable 'x))
    (define-compiler-test Lsrubreqprov top-level-form
      (check-equal?
       (current-compile #'(begin
                            (require racket/list)
                            rest))
       `(begin*
          (#%require (for-meta 0 racket/list))
          ,(make-variable rest)))
      (check-equal?
       (current-compile #'(module foo racket
                            (#%plain-module-begin
                             (provide x)
                             (define x 5))))
       `(module foo racket (,x) ()
          ((for-meta* 0 ,x)) ()
          ((#%plain-app (primitive void))
           (define-values (,x) '5))
          () () ())))))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define f (make-variable 'f))
    (define-compiler-test Lbeginexplicit top-level-form
      (check-compiler-equal?
       (current-compile #'(lambda (x) x x))
       `(#%expression (#%plain-lambda (,x) (begin ,x ,x))))
      (check-compiler-equal?
       (current-compile #'(case-lambda [(x) (+ x 1) (begin0 x (set! x 42))]))
       `(#%plain-lambda (,x)
                        (begin (#%plain-app (primitive +) ,x'1)
                               (begin0 ,x
                                       (set! ,x '42)))))
      (check-compiler-equal?
       (current-compile #'(case-lambda [(x) (+ x 1)]
                                       [(x y) x (+ x y)]))
       `(case-lambda (#%plain-lambda (,x) (#%plain-app (primitive +) ,x '1))
                     (#%plain-lambda (,x ,y) (begin ,x (#%plain-app (primitive +) ,x ,y)))))
      (check-compiler-equal?
       (current-compile #'(letrec ([f 5])
                      (display "Hello")
                      f))
       `(letrec-values ([(,f) '5])
          (begin
            (#%plain-app (primitive display) '"Hello")
            ,f))))))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define-compiler-test Lidentifyassigned top-level-form
      (check-compiler-equal?
       (current-compile #'(letrec ([y 8])
                            y))
       `(letrec-values ([(,y) '8])
          (assigned ()
                    ,y)))
      (check-compiler-equal?
       (current-compile #'(let ([x 8])
                            (set! x 5)
                            (+ x 42)))
       `(let-values ([(,x) '8])
          (assigned (,x)
                    (begin (set! ,x '5)
                           (#%plain-app (primitive +) ,x '42)))))
      (check-compiler-equal?
       (current-compile #'(let ([x 1])
                            (letrec ([y (lambda (x) y)])
                              (+ x y))))
       `(let-values ([(,x) '1])
          (assigned ()
                    (letrec-values ([(,y) (#%plain-lambda (,x) (assigned () ,y))])
                      (assigned ()
                                (#%plain-app (primitive +) ,x ,y))))))
      (check-compiler-equal?
       (current-compile #'(lambda x
                            (set! x 42)
                            x))
       `(#%expression (#%plain-lambda ,x
                                      (assigned (,x)
                                                (begin
                                                  (set! ,x '42)
                                                  ,x))))))))

;; ===================================================================================================

;; TODO: need tests here
;; (Use tests from cp0 pass)
(module+ test
  (update-current-compile!))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
    (block
     (define a (make-variable 'a))
     (define b (make-variable 'b))
     (define c (make-variable 'c))
     (define f (make-variable 'f))
     (define x (make-variable 'x))
     (define y (make-variable 'y))
     (define z (make-variable 'z))
     (define-compiler-test Lpurifyletrec top-level-form
       (check-compiler-equal?
        (current-compile #'((lambda (x) 42) 54))
        `'42)
       (check-compiler-equal?
        (current-compile #'((lambda (x) x) (lambda (y) y)))
        `(#%plain-lambda (,y) (assigned () ,y)))
       (check-compiler-equal?
        (current-compile #'(let ([x 5]
                                 [y 6])
                             (+ x y)))
        `'11)
       (check-compiler-equal?
        (current-compile #'(letrec-values ([(a) (lambda (x) a)])
                             a))
        `(letrec ([,a (#%plain-lambda (,x) (assigned () ,a))])
           ,a))
       (check-compiler-equal?
        (current-compile #'(letrec-values ([(a) (lambda (x) b)]
                                           [(b) (lambda (y) a)])
                             (a b)))
        `(letrec ([,a (#%plain-lambda (,x) (assigned () ,b))]
                  [,b (#%plain-lambda (,y) (assigned () ,a))])
           ,b))
       (check-compiler-equal?
        (current-compile #'(letrec-values ([(a) 5]
                                           [(b c) (values 6 7)])
                             (+ a b c)))
        `(let ([,a (undefined)]
               [,b (undefined)]
               [,c (undefined)])
           (begin-set!
             (set!-values (,a) '5)
             (set!-values (,b ,c) (#%plain-app (primitive values) '6 '7))
             (assigned (,c ,b ,a)
                       (#%plain-app (primitive +) ,a ,b ,c)))))
       (check-compiler-equal?
        (current-compile #'(let ([x (if #t 5 6)])
                             (set! x (+ x 1))))
        `(let ([,x '5])
           (begin-set!
             (assigned (,x) (set!-values (,x) (#%plain-app (primitive +) ,x '1))))))
       (check-compiler-equal?
        (current-compile #'(let-values ([(x y) (values 1 2)]
                                        [(z) 3])
                             (set! x 5)
                             (+ y z)))
        `(let ([,x (undefined)]
               [,y (undefined)]
               [,z (undefined)])
           (begin-set!
             (set!-values (,x ,y) (#%plain-app (primitive values) '1 '2))
             (set!-values (,z) '3)
             (assigned (,x)
                       (#%plain-app (primitive +) ,y ,z)))))
       (check-compiler-equal?
        (current-compile #'(let-values ([(x y) (values 1 2)])
                             (set! x y)
                             y))
        `(let ([,x (undefined)]
               [,y (undefined)])
           (begin-set!
             (set!-values (,x ,y) (#%plain-app (primitive values) '1 '2))
             (assigned (,x)
                       ,y))))
       (check-compiler-equal?
        (current-compile #'(letrec ([fact (lambda (x)
                                                 (if (x . <= . 0)
                                                     1
                                                     (* x (fact (- x 1)))))])
                             (fact 5)))
        `'120)
       (check-compiler-equal?
        (current-compile #'(string-append "hello " (symbol->string 'world)))
        `'"hello world")
       (check-compiler-equal?
        (current-compile #'(/ 5 0))
        `(#%plain-app (primitive /) '5 '0))
       (check-compiler-equal?
        (current-compile #'(let ([x 5])
                             (set! x 6)
                             x))
        `(let ([,x '5])
           (begin-set!
             (assigned (,x)
                       (begin
                         (set!-values (,x) '6)
                         ,x)))))
       (check-compiler-equal?
        (current-compile #'(let ([x 5])
                             (lambda (y) x)))
        `(#%plain-lambda (,y) (assigned () '5)))
       (check-compiler-equal?
        (current-compile #'(let ([x (read)])
                             (let ([x x])
                               (+ x x))))
        `(let ([,x (#%plain-app (primitive read))])
           (begin-set!
             (assigned ()
                       (#%plain-app (primitive +) ,x ,x)))))
       (check-compiler-equal?
        (current-compile  #'(let ()
                              (define (f a)
                                (f a))
                              (f (lambda (x) '(1 2 3)))))
        `(letrec ([,f (#%plain-lambda (,a) (assigned () (#%plain-app ,f ,a)))])
           (let ([,a (#%plain-lambda (,x) (assigned () ','(1 2 3)))])
             (begin-set! (assigned () (#%plain-app ,f ,a))))))
       (check-compiler-equal?
        (current-compile #'(if (lambda (x) x) 5 6))
        `'5)
       (check-compiler-equal?
        (current-compile #'(let ([x 5])
                             (set! x (begin (lambda (x) 5)
                                            6))
                             x))
        `(let ([,x '5])
           (begin-set!
             (assigned (,x)
                       (begin
                         (set!-values (,x) '6)
                         ,x)))))
       (check-compiler-equal?
        (current-compile #'((lambda (x) 5) 6 7))
        `(#%plain-app
          (#%plain-lambda (,x) (assigned () '5))
          '6 '7))
       (current-compile
        #'(let ()
            (define (fold l init f)
              (if (null? l)
                  init
                  (fold (cdr l) (f init (car l)) f)))
            (define (pow-sum l n)
              (fold l 0 (lambda (x y) (+ (expt x n) (expt y n)))))
            (pow-sum '(1 2 3) 2))))))

;; ===================================================================================================


(module+ test
  (update-current-compile!)
  (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define f (make-variable 'f))
    (define a (make-variable 'a))
    (define-compiler-test Lconvertassignments top-level-form
      (check-compiler-equal?
       (current-compile #'(let ([x 5])
                            (set! x 6)
                            x))
       `(let ([,x '5])
          (begin
            (set!-values (,x) (#%box ,x))
            (begin
              (set!-boxes (,x) '6)
              (#%unbox ,x)))))
      (check-compiler-equal?
       (current-compile #'(lambda (x y)
                            (set! x 5)
                            (list x y)))
       `(#%expression (#%plain-lambda (,x ,y)
                                      (begin
                                        (set!-values (,x) (#%box ,x))
                                        (begin
                                          (set!-boxes (,x) '5)
                                          (#%plain-app (primitive list) (#%unbox ,x) ,y))))))
      (check-compiler-equal?
       (current-compile #'(lambda x
                            (let ()
                              (set! x 42)
                              (+ x 8))))
       `(#%expression (#%plain-lambda ,x
                                      (begin
                                        (set!-values (,x) (#%box ,x))
                                        (begin
                                          (set!-boxes (,x) '42)
                                          (#%plain-app (primitive +) (#%unbox ,x) '8))))))
      (check-compiler-equal?
       (current-compile #'(let-values ([(x y) (values 1 2)])
                            (set! x y)
                            y))
       `(let ([,x (undefined)]
              [,y (undefined)])
          (begin
            (set!-values (,x ,y) (#%plain-app (primitive values) '1 '2))
            (begin
              (set!-values (,x) (#%box ,x))
              ,y))))
      (check-compiler-equal?
       (current-compile #'(letrec ([f (lambda (a) (f a))])
                            (f 1)))
       `(letrec ([,f (#%plain-lambda (,a) (#%plain-app ,f ,a))])
          (#%plain-app ,f '1))))))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define z (make-variable 'z))
    (define w (make-variable 'w))
    (define f (make-variable 'f))
    (define-compiler-test Luncoverfree compilation-top
      (check-compiler-equal?
       (current-compile #'(lambda (x)
                            (lambda (y)
                              x)))
       `(program () (#%expression
                     (#%plain-lambda (,x)
                                     (free () ()
                                           (#%plain-lambda (,y)
                                                           (free (,x) ()
                                                                 ,x)))))))
      (check-compiler-equal?
       (current-compile #'(let ([x 5])
                            (lambda (y)
                              x)))
       `(program ()  (#%plain-lambda (,y) (free () () '5))))
      (check-compiler-equal?
       (current-compile #'(begin
                            (define x 5)
                            (lambda y (if x 4 5))))
       `(program (,x) (begin*
                       (define-values (,x) '5)
                       (#%expression
                        (#%plain-lambda ,y
                                        (free () (,x)
                                              (if ,x '4 '5)))))))
      (check-compiler-equal?
       (current-compile #'(let ([x 5])
                            (set! x 6)
                            x))
       `(program () (let ([,x '5])
                      (begin
                        (set!-values (,x) (#%box ,x))
                        (begin
                          (set!-boxes (,x) '6)
                          (#%unbox ,x))))))
      (check-compiler-equal?
       (current-compile #'(let ([x 6])
                            (letrec ([f (lambda () x)])
                              (set! x 7)
                              (f f))))
       `(program ()
                 (let ([,x '6])
                   (begin
                     (set!-values (,x) (#%box ,x))
                     ;; The ,'() ... should NOT be needed
                     (letrec ([,f (#%plain-lambda (,'() ...) (free (,x) () (#%unbox ,x)))])
                       (begin
                         (set!-boxes (,x) '7)
                         (#%plain-app (#%plain-lambda (,'() ...) (free (,x) () (#%unbox ,x)))
                                      ,f)))))))
      (check-compiler-equal?
       (current-compile #'(begin
                            (define x 5)
                            (set! x 6)))
       `(program (,x) (begin*
                        (define-values (,x) '5)
                        (set!-values (,x) '6))))
      (check-compiler-equal?
       (current-compile #'(letrec ([f (lambda (x) x)])
                            (f 12)))
       `(program () '12))
      (check-compiler-equal?
       (current-compile #'(begin
                            (define x 5)
                            (define y 6)
                            (module foo racket/base
                              (#%plain-module-begin
                               (define x 12)
                               (define z 13)))))
       `(program (,y ,x) (begin*
                           (define-values (,x) '5)
                           (define-values (,y) '6)
                           (module foo racket/base (,z ,x) ()
                                   () ()
                                   ((define-values (,x) '12)
                                    (define-values (,z) '13))
                                   () () ()))))
      (check-compiler-equal?
       (current-compile #'(lambda (x)
                            (#%variable-reference)))
       `(program (#f) (#%expression
                       (#%plain-lambda (,x)
                                       (free () (#f)
                                             (#%variable-reference))))))
      (check-compiler-equal?
       (current-compile #'(module foobar racket/base
                            (#%plain-module-begin
                             (define x 5)
                             (define-values (y z) (values 6 7))
                             (define-syntax w 'hello))))
       `(program () (module foobar racket/base (,z ,y ,x) (,w)
                            () ()
                            ((define-values (,x) '5)
                             (define-values (,y ,z) (#%plain-app (primitive values) '6 '7))
                             (#%plain-app (primitive void)))
                            ((syntax 1 () () ((define-syntaxes (,w) 'hello))))
                            () ()))))))

;; ===================================================================================================


(module+ test
  (update-current-compile!)
  (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define z (make-variable 'z))
    (define-compiler-test Lraisetoplevel compilation-top
      (check-compiler-equal?
       (current-compile #'(begin
                            (define x 5)
                            (set! x 6)
                            x))
       `(program (,x) (begin*
                        (define-values (,x) '5)
                        (set!-global ,x '6)
                        (#%top . ,x))))
      (check-compiler-equal?
       (current-compile #'(begin
                            (define x 5)
                            (#%variable-reference x)))
       `(program (,x) (begin*
                        (define-values (,x) '5)
                        (#%variable-reference-top ,x))))
      (check-compiler-equal?
       (current-compile #'(begin
                            (define x 5)
                            (lambda (y)
                              (lambda (z)
                                (+ x y z)))))
       `(program (,x) (begin*
                       (define-values (,x) '5)
                       (#%expression
                        (#%plain-lambda (,y)
                                        (free () (,x)
                                              (#%plain-lambda (,z)
                                                              (free (,y) (,x)
                                                                    (#%plain-app
                                                                     (primitive +)
                                                                     (#%top . ,x) ,y ,z)))))))))
      (check-compiler-equal?
       (current-compile #'(begin
                            (define x 5)
                            (let ([y 6])
                              (set! x (+ x 1))
                              (set! y (+ y 1))
                              (+ x y))))
       `(program (,x) (begin*
                       (define-values (,x) '5)
                       (let ([,y '6])
                         (begin
                           (set!-values (,y) (#%box ,y))
                           (begin
                             (set!-global ,x (#%plain-app (primitive +) (#%top . ,x) '1))
                             (set!-boxes (,y) (#%plain-app (primitive +) (#%unbox ,y) '1))
                             (#%plain-app (primitive +) (#%top . ,x) (#%unbox ,y)))))))))))

;; ===================================================================================================


(module+ test
  (update-current-compile!)
    (block
     (define x (make-variable 'x))
     (define f (make-variable 'f))
     (define g (make-variable 'g))
     (define-compiler-test Lclosurify compilation-top
       (check-compiler-equal?
        (current-compile #'(letrec ([f (lambda (x) x)])
                             (f 12)))
        `(program () '12))
       (check-compiler-equal?
        (current-compile #'(letrec ([f (lambda (x) x)])
                             (f f 12)))
        `(program ()
                  (let ([,f (closure ,f (#%plain-lambda (,x) (free () () ,x)))])
                     (#%plain-app
                      (#%plain-lambda (,x) (free (,f) () ,f))
                      ,f '12))))
       (check-compiler-equal?
        (current-compile #'(letrec ([f (lambda () (g))]
                                    [g (lambda () (f))])
                             (f)))
        `(program ()
                  (letrec ([,f (#%plain-lambda (,'() ...) (free (,f) () (#%plain-app ,f)))])
                    (#%plain-app ,f))))
       (check-compiler-equal?
        (current-compile #'(letrec ([f (lambda (x) x)])
                             (f f)))
        `(program ()
                  (let ([,f (closure ,f (#%plain-lambda (,x) (free () () ,x)))])
                    ,f))))))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define z (make-variable 'z))
    (define-compiler-test Lvoidlets compilation-top
      (check-compiler-equal?
       (current-compile #'(let ([x 1]) x))
       `(program () '1))
      (check-compiler-equal?
       (current-compile #'(let ([x 1]
                                [y 2])
                            (+ x y)))
       `(program () '3))
      (check-compiler-equal?
       (current-compile #'(let-values ([(x y) (values 1 2)]
                                       [(z) 3])
                            (set! x 5)
                            (+ x y z)))
       `(program () (let-void (,x ,y ,z)
                              (begin
                                (set!-values (,x ,y) (#%plain-app (primitive values) '1 '2))
                                (set!-values (,z) '3)
                                (begin
                                  (set!-values (,x) (#%box ,x))
                                  (begin
                                    (set!-boxes (,x) '5)
                                    (#%plain-app (primitive +) (#%unbox ,x) ,y ,z)))))))
      (check-compiler-equal?
       (current-compile #'(let ([x 5])
                            (lambda (y)
                              (set! x 6)
                              (+ x y))))
       `(program () (let ([,x '5])
                      (begin
                        (set!-values (,x) (#%box ,x))
                        (#%plain-lambda (,y)
                                        (free (,x) ()
                                              (begin
                                                (set!-boxes (,x) '6)
                                                (#%plain-app (primitive +)
                                                             (#%unbox ,x) ,y)))))))))))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define z (make-variable 'z))
    (define-compiler-test Lscrubsyntax compilation-top
      (check-compiler-equal?
       (current-compile #'(syntax->datum #'(+ 1 2)))
       `(program ()
                 (,#'(+ 1 2))
                 (0)
                 (#%plain-app (primitive syntax->datum) (quote-syntax 0))))
      (check-compiler-equal?
       (current-compile #'(let ([x (quote-syntax (+ 1 2))])
                            (let ([y (quote-syntax (+ 3 4) #:local)])
                              (list (syntax->datum x) (syntax->datum y)))))
       `(program ()
                 (,#'(+ 1 2) ,#'(+ 3 4))
                 (0 1)
                 (let ([,x (quote-syntax 0)])
                   (let ([,y (quote-syntax 1)])
                     (#%plain-app (primitive list)
                                  (#%plain-app (primitive syntax->datum) ,x)
                                  (#%plain-app (primitive syntax->datum) ,y)))))))))
 
;; ===================================================================================================

(module+ test
  (update-current-compile!))

;; ===================================================================================================

(module+ test
  (update-current-compile!)
  (block
    (define x* (make-variable 'x))
    (define-compiler-test Ldebruijn compilation-top
      (check-compiler-equal?
       (current-compile #'(lambda (x) x))
       `(program () () (#%expression (#%plain-lambda 1 #f () () 0))))
      (check-compiler-equal?
       (current-compile #'(let ([x 5])
                       (lambda (y . z) x)))
       `(program () () (#%plain-lambda 2 #t () () '5)))
      (check-compiler-equal?
       (current-compile #'(let ([x 5]
                           [y 6])
                       (+ x y)))
       `(program () () '11))
      (check-compiler-equal?
       (current-compile #'(begin
                            (define x 5)
                       (+ x 5)))
       `(program (,x*) ()
                 (begin*
                   (define-values (0) '5)
                   (#%plain-app (primitive ,(dict-ref primitive-table* '+)) (#%top 2 0) '5))))
      (check-compiler-equal?
       (current-compile #'(begin
                            (define x 5)
                            (lambda (y)
                              y x)))
       `(program (,x*) ()
                 (begin*
                   (define-values (0) '5)
                   (#%expression
                    (#%plain-lambda 1 #f (0) (0)
                                    (#%top 0 0))))))
      ;; TODO
      #;(check-equal?
       (current-compile #'(begin
                            (module foo racket
                              (#%plain-module-begin
                               (provide x)
                               (define x 12)))
                            (require 'foo)
                            x))
       `(program (,x*) (begin*
                      (module foo racket (,x*) ()
                              (,x*) ()
                              ((#%plain-app (primitive 35))
                               (define-values (0) '12))
                              ()
                              () ())
                      (#%require (for-meta 0 (quote* foo)))
                      (#%top 0 0)))))))

;; ===================================================================================================

(module+ test
    (update-current-compile!)
    (define-compiler-test Lfindletdepth compilation-top
      (check-compiler-equal?
       (current-compile #'(lambda (x) (let ([y 5]) (+ x y))))
       `(program 1 () ()
                 (#%expression
                  (#%plain-lambda 1 #f () () 9
                                  (#%plain-app
                                   (primitive ,(dict-ref primitive-table* '+))
                                   2 '5)))))
      (check-compiler-equal?
       (current-compile #'(if (= 5 6)
                              (let ([x '5]
                                    [y '6])
                                y)
                              (let ([x '6])
                                x)))
       `(program 0 () () '6))))

(module+ test
  (parameterize ([current-environment-variables
                  (environment-variables-copy (current-environment-variables))])
    (putenv "PLT_VALIDATE_COMPILE" "true")
    (set! all-compiler-tests
          (cons
           (test-suite
               "Tests for finished compiler"
             (compile-compare #'42)
             (compile-compare #'(if #t 5 6))
             (compile-compare #'((lambda (x) x) 42))
             (compile-compare #'((lambda (x) (+ x 5)) 84))
             (compile-compare #'(((lambda (x) (lambda (y) (+ x y))) 2) 3))
             ;; TODO this test
             ;(compile-compare #'((lambda x (car x)) '(84 91 514)))
             (compile-compare #'(let ([x (lambda () 42)])
                                  (x)))
             (compile-compare #'(let ([x 5])
                                  (set! x 6)
                                  x))
             (compile-compare #'(letrec ([f (lambda (x) x)])
                                  (f 12)))
             ;; TODO This test
             #;(compile-compare #'(letrec ([fact (lambda (x)
                                                 (if (x . <= . 0)
                                                     1
                                                     (* x (fact (- x 1)))))])
                                  (fact 5)))
             (compile-compare #'(with-continuation-mark 'hello 'world
                                  (continuation-mark-set->list
                                   (current-continuation-marks) 'hello)))
             (compile-compare #'(if (= 4 4)
                                    (begin
                                      1 ;; (random 1) TODO
                                      4)
                                    3))
             (compile-compare #'(let ([+ 12])
                                  (- + 8)))
             (compile-compare #'(begin0 12 42 (+ 3 8)))
             (compile-compare #'(begin
                                  (define x 5)
                                  x))
             (compile-compare #'(begin
                                  (define x 5)
                                  (set! x 6)
                                  x))
             (compile-compare #'(begin
                                  (define x 5)
                                  (let ([b (lambda (y) (+ x y))])
                                    (b 12))))
             (compile-compare #'(begin
                                  (define x 5)
                                  ((lambda (y)
                                     ((lambda (z)
                                        (+ x y z)) 4)) 5)))
             (compile-compare #'(begin
                                  (define x 5)
                                  (((let ([a (lambda (y)
                                               (let ([b (lambda (z)
                                                          (+ x y z))])
                                                 b))])
                                      a) 3) 4)))
             (compile-compare #'(begin
                                  (define x 5)
                                  (let ([y 6])
                                    (set! x (+ x 1))
                                    (set! y (+ y 1))
                                    (+ x y))))
             (compile-compare #'(eval '(+ 1 2)
                                      (variable-reference->namespace
                                       (#%variable-reference))))
             (compile-compare #'(begin
                                  (define x 48)
                                  (let ([x 6])
                                    (#%top . x))))
             (compile-compare #'(call-with-current-continuation (lambda (x) 12)))
             (compile-compare #'(syntax->datum #'(+ 1 2)))
             ;; TODO, this test
             #;(compile-compare #'(begin
                                  (module foo racket
                                    (#%plain-module-begin
                                     (provide x)
                                     (define x 481)))
                                  (require 'foo)
                                  x)))
           all-compiler-tests))))

;; ===================================================================================================

(module+ test
  (run-all-compiler-tests))
