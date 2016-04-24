#lang racket/base

(provide compile)

(require (except-in nanopass/base
                    define-language
                    define-pass)
         (rename-in nanopass/base
                    [define-language nanopass:define-language]
                    [define-pass nanopass:define-pass])
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
         "private/utils.rkt"
         "private/components.rkt")

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
                 (let* ([current-compile* current-compile-top]
                        [current-compile (lambda (src)
                                           (parameterize ([current-variable-equal? eq?])
                                             (current-compile* src)))])
                   (test-suite
                       (format "Test suite for: ~a" '#,(syntax->datum #'lang))
                     (parameterize ([current-variable-equal?
                                     (lambda (a b)
                                       (equal? (variable-name a) (variable-name b)))])
                       (test-case (format "Test case for: ~a" '#,(syntax->datum #'lang))
                         body) ...)))))
           (set! all-compiler-tests (cons name all-compiler-tests)))]))

  ;; Run all tests defined with define-compiler-test
  (define-syntax-rule (run-all-compiler-tests)
    (let ()
      (define res (map run-tests (reverse all-compiler-tests)))
      (exit-handler (lambda (code)
                      (max code (min (apply + res) 255))))
      (void)))

  ;; Compare result of current compiler to regular compiler
  (define-syntax (compile-compare stx)
    (syntax-case stx ()
      [(_ expression)
       #`(test-case "Test case for finished compiler"
           #,(syntax/loc stx
               (check-equal?
                (parameterize ([current-namespace (make-base-namespace)])
                  (namespace-require 'racket/undefined)
                  (eval (compile (namespace-syntax-introduce
                                  (strip-context expression)))))
                (parameterize ([current-namespace (make-base-namespace)])
                  (namespace-require 'racket/undefined)
                  (eval (namespace-syntax-introduce
                         (strip-context expression)))))))]))

  ;; Used to update the current compiler while testing
  (define current-compile-number 0)
  (define current-compile-top (list-ref compilers current-compile-number))
  (define (update-current-compile!)
    (set! current-compile-number (+ current-compile-number 1))
    (set! current-compile-top (list-ref compilers current-compile-number))))

; Grabs set of identifiers out of formals non-terminal in a language
; lang formals -> (listof identifiers)
(define-syntax-rule (formals->identifiers lang fmls)
  (nanopass-case (lang formals) fmls
                 [,v                       (list v)]
                 [(,v (... ...))           v]
                 [(,v ,v* (... ...) . ,v2) (set-union (list v v2) v*)]))

; lang formals -> boolean
(define-syntax-rule (formals-rest? lang fmls)
  (nanopass-case (lang formals) fmls
                 [,v                       #t]
                 [(,v (... ...))           #f]
                 [(,v ,v* (... ...) . ,v2) #t]))

;; ===================================================================================================

(start-current-language! L)

(define-language current-target
  (terminals
   (maybe-module-path (maybe-module-path module-path))
   (declaration-keyword (declaration-keyword))
   (datum (datum))
   (symbol (id))
   (variable (v var variable))
   (string (string))
   (path (path))
   (phase-level (phase-level))
   (false (false))
   (exact-nonnegative-integer (exact-nonnegative-integer eni))
   (boolean (boolean)))
  (top-level-form (top-level-form)
                  general-top-level-form
                  (#%expression expr)
                  (module id module-path
                    (module-level-form ...))
                  (begin* top-level-form ...)
                  (begin-for-syntax* top-level-form ...))
  (module-level-form (module-level-form)
                     general-top-level-form
                     (#%provide raw-provide-spec ...)
                     (begin-for-syntax module-level-form ...)
                     submodule-form
                     (#%declare declaration-keyword ...))
  (submodule-form (submodule-form)
                  (submodule id module-path
                             (module-level-form ...))
                  (submodule* id module-path
                              (module-level-form ...))
                  (submodule* id
                              (module-level-form ...)))
  (general-top-level-form (general-top-level-form)
                          expr
                          (define-values (v ...) expr)
                          (define-syntaxes (v ...) expr)
                          (#%require raw-require-spec ...))
  (expr (expr)
        v
        (primitive id)
        (#%plain-lambda formals expr* ... expr)
        (case-lambda (formals expr* ... expr) ...)
        (if expr1 expr2 expr3)
        (begin expr* ... expr)
        (begin0 expr expr* ...)
        (let-values ([(v ...) expr1] ...)
          expr* ... expr)
        (letrec-values ([(v ...) expr1] ...)
          expr* ... expr)
        (set! v expr)
        (quote datum)
        (quote-syntax datum)
        (with-continuation-mark expr1 expr2 expr3)
        (#%plain-app expr expr* ...)
        (#%top . v)
        (#%variable-reference v)
        (#%variable-reference-top v)
        (#%variable-reference))
  (formals (formals)
           v
           (v ...)
           (v v* ... . v2))
  (raw-require-spec (raw-require-spec rrs)
                    phaseless-req-spec
                    (for-meta phase-level phaseless-req-spec ...)
                    (just-meta phase-level raw-require-spec ...))
  (phaseless-req-spec (phaseless-req-spec)
                      raw-module-path
                      (only raw-module-path v ...)
                      (all-except raw-module-path v ...)
                      (prefix-all-except id raw-module-path v* ...)
                      (rename raw-module-path v1 v2))
  (raw-module-path (raw-module-path)
                   raw-root-module-path
                   (submod raw-root-module-path id ...))
  (raw-root-module-path (raw-root-module-path)
                        id
                        string
                        (quote* id)
                        (lib string ...)
                        (file string)
                        (planet string1
                                (string2 string3 string* ...))
                        path)
  (raw-provide-spec (raw-provide-spec rps)
                    phaseless-prov-spec
                    (for-meta* phase-level phaseless-prov-spec)
                    (protect raw-provide-spec))
  (phaseless-prov-spec (phaseless-prov-spec)
                       v
                       (rename* v1 v2)
                       (struct v (v* ...))
                       (all-from-except raw-module-path v ...)
                       (all-defined-except v ...)
                       (prefix-all-defined-except id v* ...)
                       (protect* phaseless-prov-spec ...)))

;; Parse and alpha-rename expanded program
(define-pass parse-and-rename : * (form) -> current-target ()
  (definitions

    (define current-global-env (make-parameter (make-hash)))

    ; Initial environment for local variables
    (define initial-env (hash))
    (define (extend-env env vars)
      (for/fold ([acc env])
                ([var (in-list vars)])
        (define var* (syntax->datum var))
        (dict-set acc var* (make-variable var*
                                          #:source-location (syntax-source var)))))
    (define ((lookup-env env) var)
      (define var* (syntax->datum var))
      (dict-ref env var*
                (lambda ()
                  (dict-ref (current-global-env) var*
                            (lambda ()
                              (let ([x (make-variable var*
                                                      #:source-location (syntax-source var))])
                                (dict-set! (current-global-env) var* x)
                                x)))))))

  (parse-top : * (form env) -> top-level-form ()
             (syntax-parse form
               #:literals (#%expression module #%plain-module-begin begin begin-for-syntax)
               [(#%expression body)
                `(#%expression ,(parse-expr #'body env))]
               [(module id:id path
                  (#%plain-module-begin body ...))
                (parameterize ([current-global-env (make-hash)])
                  `(module ,(syntax->datum #'id) ,(syntax->datum #'path)
                     (,(for/list ([i (in-list (syntax->list #'(body ...)))])
                         (parse-mod i env)) ...)))]
               [(begin body ...)
                `(begin* ,(for/list ([i (in-list (syntax->list #'(body ...)))])
                            (parse-top i env)) ...)]
               [(begin-for-syntax body ...)
                `(begin-for-syntax* ,(for/list ([i (in-list (syntax->list #'(body ...)))])
                                       (parse-top (syntax-shift-phase-level i -1) env)) ...)]
               [else
                (parse-gen #'else env)]))

  (parse-mod : * (form env) -> module-level-form ()
             (syntax-parse form
               #:literals (#%provide begin-for-syntax #%declare module module*
                                     #%plain-module-begin)
               [(#%provide spec ...)
                `(#%provide ,(for/list ([s (in-list (syntax->list #'(spec ...)))])
                               (parse-raw-provide-spec s env)) ...)]
               [(begin-for-syntax body ...)
                `(begin-for-syntax ,(for/list ([i (in-list (syntax->list #'(body ...)))])
                                      (parse-mod (syntax-shift-phase-level i -1) env)) ...)]
               [(#%declare keyword ...)
                `(#%declare ,(syntax->list #'(keyword ...)) ...)]
               [(module id:id path
                  (#%plain-module-begin body ...))
                (parameterize ([current-global-env (make-hash)])
                  `(submodule ,(syntax->datum #'id) ,(syntax->datum #'path)
                              (,(for/list ([i (in-list (syntax->list #'(body ...)))])
                                  (parse-mod i env)) ...)))]
               [(module* id:id path
                  (#%plain-module-begin body ...))
                (parameterize ([current-global-env (make-hash)])
                  `(submodule* ,(syntax->datum #'id) ,(syntax->datum #'path)
                               (,(for/list ([i (in-list (syntax->list #'(body ...)))])
                                   (parse-mod i env)) ...)))]
               [(module* id:id path
                  (#%plain-module-begin body ...))
                (parameterize ([current-global-env (make-hash)])
                  `(submodule* ,(syntax->datum #'id)
                               (,(for/list ([i (in-list (syntax->list #'(body ...)))])
                                   (parse-mod i env)) ...)))]
               [else
                (parse-gen #'else env)]))

  (parse-gen : * (form env) -> general-top-level-form ()
             (syntax-parse form
               #:literals (define-values define-syntaxes #%require)
               [(define-values (id:id ...) body)
                ;(define env* (extend-env env (syntax->list #'(id ...))))
                `(define-values (,(for/list ([i (in-list (syntax->list #'(id ...)))])
                                    (parse-expr i env)) ...)
                   ,(parse-expr #'body env))]
               [(define-syntaxes (id:id ...) body)
                ;(define env* (extend-env env (syntax->list #'(id ...))))
                `(define-syntaxes (,(for/list ([i (in-list (syntax->list #'(id ...)))])
                                      (parse-expr i env)) ...)
                   ,(parse-expr (syntax-shift-phase-level #'body -1) env))]
               [(#%require spec ...)
                `(#%require ,(for/list ([s (in-list (syntax->list #'(spec ...)))])
                               (parse-raw-require-spec s env)) ...)]
               [else
                (parse-expr #'else env)]))

  (parse-expr : * (form env) -> expr ()
              (syntax-parse form
                #:literals (#%plain-lambda case-lambda if begin begin0 let-values letrec-values set!
                                           quote quote-syntax with-continuation-mark #%plain-app
                                           #%top #%variable-reference)
                [id:id (if (primitive-identifier? #'id)
                           `(primitive ,(primitive->symbol #'id))
                           ((lookup-env env) #'id))]
                [(#%plain-lambda formals body* ... body)
                 (define-values (formals* env*) (parse-formals #'formals env))
                 `(#%plain-lambda ,formals*
                                  ,(for/list ([b (in-list (syntax->list #'(body* ...)))])
                                     (parse-expr b env*)) ...
                                  ,(parse-expr #'body env*))]
                [(case-lambda (formals body* ... body) ...)
                 (match (for/list ([formal (in-list (syntax->list #'(formals ...)))]
                                   [b1 (in-list (syntax->list #'(body ...)))]
                                   [b (in-list (syntax->list #'((body* ...) ...)))])
                          (define-values (formals* env*) (parse-formals formal env))
                          (list formals*
                                (for/list ([b* (in-list (syntax->list b))])
                                  (parse-expr b* env*))
                                (parse-expr b1 env*)))
                   [`((,formal ,body* ,body) ...)
                    `(case-lambda (,formal ,body* ... ,body) ...)])]
                [(if test tbranch fbranch)
                 `(if ,(parse-expr #'test env)
                      ,(parse-expr #'tbranch env)
                      ,(parse-expr #'fbranch env))]
                [(begin body* ... body)
                 `(begin ,(for/list ([b (in-list (syntax->list #'(body* ...)))])
                            (parse-expr b env)) ...
                         ,(parse-expr #'body env))]
                [(begin0 body body* ...)
                 `(begin0 ,(parse-expr #'body env)
                          ,(for/list ([b (in-list (syntax->list #'(body* ...)))])
                             (parse-expr b env)) ...)]
                [(let-values ([(ids:id ...) val] ...)
                   body* ... body)
                 (define env* (extend-env env
                                          (apply
                                           append
                                           (map syntax->list (syntax->list #'((ids ...) ...))))))
                 (match (for/list ([i (in-list (syntax->list #'((ids ...) ...)))]
                                   [v (in-list (syntax->list #'(val ...)))])
                          (list (map (lookup-env env*) (syntax->list i))
                                (parse-expr v env)))
                   [`([(,args ...) ,exp] ...)
                    `(let-values ([(,args ...) ,exp] ...)
                       ,(for/list ([b (in-list (syntax->list #'(body* ...)))])
                          (parse-expr b env*)) ...
                       ,(parse-expr #'body env*))])]
                [(letrec-values ([(ids:id ...) val] ...)
                   body* ... body)
                 (define env* (extend-env env
                                          (apply
                                           append
                                           (map syntax->list (syntax->list #'((ids ...) ...))))))
                 (match (for/list ([i (in-list (syntax->list #'((ids ...) ...)))]
                                   [v (in-list (syntax->list #'(val ...)))])
                          (list (map (lookup-env env*) (syntax->list i))
                                (parse-expr v env*)))
                   [`([(,args ...) ,exp] ...)
                    `(letrec-values ([(,args ...) ,exp] ...)
                       ,(for/list ([b (in-list (syntax->list #'(body* ...)))])
                          (parse-expr b env*)) ...
                       ,(parse-expr #'body env*))])]
                [(set! id:id body)
                 `(set! ,(parse-expr #'id env) ,(parse-expr #'body env))]
                [(quote datum)
                 `(quote ,(syntax->datum #'datum))]
                [(with-continuation-mark key val result)
                 `(with-continuation-mark ,(parse-expr #'key env) ,(parse-expr #'val env)
                    ,(parse-expr #'result env))]
                [(#%plain-app func body ...)
                 `(#%plain-app ,(parse-expr #'func env)
                               ,(for/list ([i (in-list (syntax->list #'(body ...)))])
                                  (parse-expr i env)) ...)]
                [(#%top . id:id)
                 `(#%top . ,(parse-expr #'id (hash)))]
                [(#%variable-reference id:id)
                 `(#%variable-reference ,(parse-expr #'id env))]
                [(#%variable-reference (#%top . id:id))
                 `(#%variable-reference-top ,((lookup-env env) #'id))]
                [(#%variable-reference)
                 `(#%variable-reference)]))

  (parse-formals : * (formals env) -> formals (env)
                (syntax-parse formals
                  [(ids:id ...)
                   (define env* (extend-env env (syntax->list #'(ids ...))))
                   (values
                    `(,(for/list ([i (in-list (syntax->list #'(ids ...)))])
                         (parse-expr i env*)) ...)
                    env*)]
                  [(id:id ids:id ... . rest:id)
                   (define env* (extend-env env (list* #'id #'rest (syntax->list #'(ids ...)))))
                   (values
                    `(,(parse-expr #'id env*)
                      ,(for/list ([i (in-list (syntax->list #'(ids ...)))])
                         (parse-expr i env*)) ...
                      . ,(parse-expr #'rest env*))
                    env*)]
                  [rest:id
                   (define env* (extend-env env (list #'rest)))
                   (values (parse-expr #'rest env*) env*)]))

  (parse-raw-require-spec : * (form env) -> raw-require-spec ()
                          (syntax-parse form
                            #:datum-literals (for-meta for-syntax for-template for-label just-meta)
                            [(for-meta phase-level phaseless-req-spec ...)
                             `(for-meta
                               ,(syntax-e #'phase-level)
                               ,(for/list ([i (in-list (syntax->list #'(phaseless-req-spec ...)))])
                                  (parse-phaseless-req-spec i env)) ...)]
                            [(for-syntax phaseless-req-spec ...)
                             `(for-meta
                               ,1
                               ,(for/list ([i (in-list (syntax->list #'(phaseless-req-spec ...)))])
                                  (parse-phaseless-req-spec i env)) ...)]
                            [(for-template phaseless-req-spec ...)
                             `(for-meta
                               ,#f
                               ,(for/list ([i (in-list (syntax->list #'(phaseless-req-spec ...)))])
                                  (parse-phaseless-req-spec i env)) ...)]
                            [(for-label phaseless-req-spec ...)
                             `(for-meta
                               ,-1
                               ,(for/list ([i (in-list (syntax->list #'(phaseless-req-spec ...)))])
                                  (parse-phaseless-req-spec i env)) ...)]
                            [(just-meta phase-level raw-req-spec ...)
                             `(just-meta
                               ,(syntax-e #'phase-level)
                               ,(for/list ([i (in-list (syntax->list #'(raw-req-spec ...)))])
                                  (parse-raw-require-spec i env)) ...)]
                            [else (parse-phaseless-req-spec #'else env)]))

  (parse-phaseless-req-spec : * (form env) -> phaseless-req-spec ()
                            (syntax-parse form
                              #:datum-literals (only prefix all-except prefix-all-except rename)
                              [(only raw-module-path ids:id ...)
                               `(only ,(parse-raw-module-path #'raw-module-path env)
                                      ,(map (curryr parse-expr env) (syntax->list #'(ids ...))) ...)]
                              [(prefix id:id raw-module-path)
                               `(prefix-all-except ,(syntax-e #'id)
                                                   ,(parse-raw-module-path #'raw-module-path env))]
                              [(all-except raw-module-path ids:id ...)
                               `(all-except ,(parse-raw-module-path #'raw-module-path)
                                            ,(map (curryr parse-expr env)
                                                  (syntax->list #'(ids ...))) ...)]
                              [(prefix-all-except id:id raw-module-path ids:id ...)
                               `(prefix-all-except
                                 ,(syntax-e #'id)
                                 ,(parse-raw-module-path #'raw-module-path env)
                                 ,(map (curryr parse-expr env) (syntax->list #'(ids ...))) ...)]
                              [(rename raw-module-path id1:id id2:id)
                               `(rename ,(parse-raw-module-path #'raw-module-path)
                                        ,(parse-expr #'id1 env)
                                        ,(parse-expr #'id2 env))]
                              [else (parse-raw-module-path #'else env)]))

  (parse-raw-provide-spec : * (form env) -> raw-provide-spec ()
                          (syntax-parse form
                            #:literals (for-meta for-syntax for-label)
                            #:datum-literals (protect)
                            [(for-meta phase-level phaseless-prov-spec)
                             `(for-meta* ,(syntax-e #'phase-level)
                                         ,(parse-phaseless-prov-spec #'phaseless-prov-spec env))]
                            [(for-syntax phaseless-prov-spec)
                             `(for-meta* ,1 ,(parse-phaseless-prov-spec #'phaseless-prov-spec env))]
                            [(for-label phaseless-prov-spec)
                             `(for-meta* ,#f ,(parse-phaseless-prov-spec #'phaseless-prov-spec env))]
                            [(protect raw-provide-spec)
                             `(protect ,(parse-raw-provide-spec #'raw-provide-spec env))]
                            [else (parse-phaseless-prov-spec #'else env)]))

  (parse-raw-module-path : * (form env) -> raw-module-path ()
                         (syntax-parse form
                           #:literals (submod)
                           [(submod path ids:id ...+)
                            `(submod ,(parse-raw-root-module-path #'path env)
                                     ,(for/list ([i (in-list (syntax->list #'(ids ...)))])
                                        (syntax-e i)) ...)]
                           [else (parse-raw-root-module-path #'else env)]))

  (parse-raw-root-module-path : * (form env) -> raw-root-module-path ()
                              (syntax-parse form
                                #:literals (quote lib file planet)
                                [i:id (syntax-e #'i)]
                                ; [s:string (syntax-e #'s)] TODO proper string syntax calss
                                [(quote id:id) `(quote* ,(syntax-e #'id))]
                                [(lib s ...)
                                 `(lib ,(for/list ([i (in-list (syntax->list #'(s ...)))])
                                          (syntax-e i)) ...)]
                                [(file s) `(file ,(syntax-e #'s))]
                                [(planet s1
                                         (s2 s3 s4 ...))
                                 `(planet ,(syntax-e #'s1)
                                          (,(syntax-e #'s2)
                                           ,(syntax-e #'s3)
                                           ,(for/list ([i (in-list (syntax->list #'(s4 ...)))])
                                              (syntax-e i)) ...))]
                                [else (syntax-e #'path)]))

  (parse-phaseless-prov-spec : * (form env) -> phaseless-prov-spec ()
                             (syntax-parse form
                               #:datum-literals (rename struct all-from all-from-except all-define
                                                        all-defined-except prefix-all-defined
                                                        prefix-all-defined-except expand protect)
                               [id:id (parse-expr #'id env)]
                               [(rename id1:id id2:id)
                                `(rename* ,(parse-expr #'id1 env) ,(parse-expr #'id2 env))]
                               [(struct name:id (fields:id ...))
                                `(struct ,(parse-expr #'name env)
                                   (,(map (curryr parse-expr env)
                                          (syntax->list #'(fields ...))) ...))]
                               [(all-from raw-module-path)
                                `(all-from-except ,(parse-raw-module-path #'raw-module-path env))]
                               [(all-from-except raw-module-path ids:id ...)
                                `(all-from-except
                                  ,(parse-raw-module-path #'raw-module-path env)
                                  ,(map (curryr parse-expr env) (syntax->list #'(ids ...))) ...)]
                               [(all-defined) `(all-defined-except)]
                               [(all-defined-except ids:id ...)
                                `(all-defined-except
                                  ,(map (curryr parse-expr env) (syntax->list #'(ids ...))) ...)]
                               [(prefix-all-defined prefix:id)
                                `(prefix-all-defined-except ,(syntax-e #'prefix))]
                               [(prefix-all-defined-except prefix:id ids:id ...)
                                `(prefix-all-defined-except
                                  ,(syntax-e #'prefix)
                                  ,(map (curryr parse-expr env) (syntax->list #'(ids ...))) ...)]
                               [(protect spec ...)
                                `(protect*
                                  ,(map (curryr parse-phaseless-prov-spec env)
                                        (syntax->list #'(spec ...))) ...)]))

  (parse-top form initial-env))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x (make-variable 'x))
    (define a (make-variable 'a))
    (define b (make-variable 'b))
    (define c (make-variable 'c))
    (define-compiler-test current-target top-level-form
      (check-equal?
       (current-compile #'(lambda (x) x))
       `(#%expression (#%plain-lambda (,x) ,x)))
      (check-equal?
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
      (check-equal?
       (current-compile #'(begin-for-syntax
                            (define x 5)))
       `(begin-for-syntax*
          (define-values (,x) '5)))
      (check-equal?
       (current-compile #'(module test racket
                            (#%plain-module-begin
                             (begin-for-syntax
                               (define x 5)))))
       `(module test racket
          ((begin-for-syntax
             (define-values (,x) '5)))))
      (check-equal?
       (current-compile #'(lambda (a b . c)
                            (apply + a b c)))
       `(#%expression (#%plain-lambda (,a ,b . ,c)
                                      (#%plain-app (primitive apply) (primitive +) ,a ,b ,c))))
      (check-equal?
       (current-compile #'(module foo racket/base
                            (#%plain-module-begin
                             (require racket/match)
                             (#%provide (all-from-except racket/match match)))))
       `(module foo racket/base
          ((#%require racket/match)
           (#%provide (all-from-except racket/match ,(make-variable 'match))))))
      (check-equal?
       (current-compile #'(module bar racket
                            (#%plain-module-begin
                             (define x 5)
                             (provide x))))
       `(module bar racket
          ((define-values (,x) '5)
           (#%provide ,x))))
      (let*-values ([(code) (current-compile #'(begin (define x 5)
                                                      x))]
                    [(v1 v2) (nanopass-case (current-target top-level-form) code
                                            [(begin* (define-values (,var1) ,expr)
                                                     ,var2)
                                             (values var1 var2)])])
        (check-true (eq? v1 v2)))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (top-level-form (top-level-form)
                  (- (module id module-path
                       (module-level-form ...)))
                  (+ submodule-form))
  (module-level-form (module-level-form)
                     (- submodule-form))
  (submodule-form (submodule-form)
                  (- (submodule id module-path
                                (module-level-form ...))
                     (submodule* id module-path
                                 (module-level-form ...))
                     (submodule* id
                                 (module-level-form ...)))
                  (+ (module id module-path
                       (module-level-form ...)
                       (submodule-form ...)
                       (submodule-form* ...)))))

(define-pass lift-submodules : current-source (e) -> current-target ()
  (TopLevelForm : top-level-form (e) -> top-level-form ()
                [(module ,id ,module-path
                   (,[module-level-form pre post] ...))
                 `(module ,id ,module-path
                    (,module-level-form ...)
                    (,(append* pre) ...)
                    (,(append* post) ...))])
  (SubmoduleForm : submodule-form (e) -> module-level-form ('() '())
                 [(submodule ,id ,module-path
                             (,[module-level-form pre post] ...))
                  (values `(#%plain-app (primitive void))
                          (list (with-output-language (L1 submodule-form)
                                  `(module ,id ,module-path
                                     (,module-level-form ...)
                                     (,(append* pre) ...)
                                     (,(append* post) ...))))
                          null)]
                 [(submodule* ,id ,module-path
                              (,[module-level-form pre post] ...))
                  (values `(#%plain-app (primitive void))
                          null
                          (list (with-output-language (L1 submodule-form)
                                  `(module ,id ,module-path
                                     (,module-level-form ...)
                                     (,(append* pre) ...)
                                     (,(append* post) ...)))))]
                 [(submodule* ,id
                              (,[module-level-form pre post] ...))
                  (values `(#%plain-app (primitive void))
                          null
                          (list (with-output-language (L1 submodule-form)
                                  `(module ,id #f
                                     (,module-level-form ...)
                                     (,(append* pre) ...)
                                     (,(append* post) ...)))))])
  (ModuleLevelForm : module-level-form (e) -> module-level-form ('() '())
                   [(begin-for-syntax ,[module-level-form pre post] ...)
                    (values `(begin-for-syntax ,module-level-form ...)
                            (append* pre)
                            (append* post))])
  (GeneralTopLevelForm : general-top-level-form (e) -> general-top-level-form ('() '()))
  (Expr : expr (e) -> expr ('() '())))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x (make-variable 'x))
    (define-compiler-test current-target top-level-form
      (check-equal?
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
      (check-equal?
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
      (check-equal?
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
      (check-equal?
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
          ()))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (top-level-form (top-level-form)
                  (+ (#%require raw-require-spec ...)))
  (general-top-level-form (general-top-level-form)
                          (- (#%require raw-require-spec ...)))
  (module-level-form (module-level-form)
                     (- (#%provide raw-provide-spec ...)))
  (submodule-form (submodule-form)
                  (- (module id module-path
                       (module-level-form ...)
                       (submodule-form ...)
                       (submodule-form* ...)))
                  (+ (module id module-path
                       (raw-provide-spec ...)
                       (raw-require-spec ...)
                       (module-level-form ...)
                       (submodule-form ...)
                       (submodule-form* ...)))))

(define-pass lift-require-provide : current-source (e) -> current-target ()
  (TopLevelForm : top-level-form (e) -> top-level-form ()
                [(#%require ,[raw-require-spec] ...)
                 `(#%require ,raw-require-spec ...)])
  (GeneralTopLevelForm : general-top-level-form (e [meta-level 0]) -> general-top-level-form ('() '())
                       [(#%require ,raw-require-spec ...)
                        (values `(#%plain-app (primitive void))
                                null
                                (for/list ([rrs (in-list raw-require-spec)])
                                  (RawRequireSpec rrs meta-level)))])
  (ModuleLevelForm : module-level-form (e [meta-level 0]) -> module-level-form ('() '())
                   [(begin-for-syntax
                      ,[module-level-form (+ meta-level 1) -> module-level-form prov req] ...)
                    (values `(begin-for-syntax ,module-level-form ...)
                            (append* prov)
                            (append* req))]
                   [(#%provide ,raw-provide-spec ...)
                    (values `(#%plain-app (primitive void))
                            (for/list ([rps (in-list raw-provide-spec)])
                              (RawProvideSpec rps meta-level))
                            null)])
  (SubmoduleForm : submodule-form (e) -> submodule-form ()
                 [(module ,id ,module-path
                    (,[module-level-form prov req] ...)
                    (,[submodule-form] ...)
                    (,[submodule-form*] ...))
                  `(module ,id ,module-path
                     (,(append* prov) ...)
                     (,(append* req) ...)
                     (,module-level-form ...)
                     (,submodule-form ...)
                     (,submodule-form* ...))])
  (Expr : expr (e) -> expr ('() '()))
  (RawRequireSpec : raw-require-spec (e [meta-level 0]) -> raw-require-spec ()
                  [(for-meta ,phase-level ,[phaseless-req-spec] ...)
                   (if (exact-integer? phase-level)
                       `(for-meta ,(+ meta-level phase-level) ,phaseless-req-spec ...)
                       `(for-meta #f ,phaseless-req-spec ...))]
                  [(just-meta ,phase-level ,[raw-require-spec] ...)
                   `(just-meta ,(+ meta-level phase-level) ,raw-require-spec ...)]
                  [,phaseless-req-spec
                   (if (= meta-level 0)
                       (PhaselessReqSpec phaseless-req-spec)
                       `(for-meta ,meta-level ,(PhaselessReqSpec phaseless-req-spec)))])
  (RawProvideSpec : raw-provide-spec (e [meta-level 0]) -> raw-provide-spec ()
                  [(for-meta* ,phase-level ,[phaseless-prov-spec])
                   (if (exact-integer? phase-level)
                       `(for-meta* ,(+ meta-level phase-level) ,phaseless-prov-spec)
                       `(for-meta* #f ,phaseless-prov-spec))]
                  [,phaseless-prov-spec
                   (if (= meta-level 0)
                       (PhaselessProvSpec phaseless-prov-spec)
                       `(for-meta* ,meta-level ,(PhaselessProvSpec phaseless-prov-spec)))])
  (PhaselessProvSpec : phaseless-prov-spec (e) -> phaseless-prov-spec ())
  (PhaselessReqSpec : phaseless-req-spec (e) -> phaseless-req-spec ()))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x (make-variable 'x))
    (define-compiler-test current-target top-level-form
      (check-equal?
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
      (check-equal?
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
          () ()))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (submodule-form (submodule-form)
                  (- (module id module-path
                       (raw-provide-spec ...)
                       (raw-require-spec ...)
                       (module-level-form ...)
                       (submodule-form ...)
                       (submodule-form* ...)))
                 (+ (module id module-path
                       (raw-provide-spec ...)
                       (raw-require-spec ...)
                       (module-level-form ...)
                       (syntax-level-form ...)
                       (submodule-form ...)
                       (submodule-form* ...))))
  (syntax-level-form (syntax-level-form)
                     (+ (syntax eni (syntax-body ...))))
  (syntax-body (syntax-body)
               (+ (begin-for-syntax module-level-form ...)
                  (define-syntaxes (v ...) expr)))
  (module-level-form (module-level-form)
                     (- (begin-for-syntax module-level-form ...)))
  (general-top-level-form (general-top-level-form)
                          (- (define-syntaxes (v ...) expr)))
  (top-level-form (top-level-form)
                  (+ (define-syntaxes* (v ...) expr))))

(define-pass lift-syntax-sequences : current-source (e) -> current-target ()
  (definitions
    (define (merge-syntax-tables tables)
      (apply hash-union (hash) tables
             #:combine (lambda (v1 v2)
                         (append v1 v2))))
    (define (build-from-table syntax-table)
      (for/list ([(k v) (in-hash syntax-table)])
        (with-output-language (current-target syntax-level-form)
          `(syntax ,k (,v ...)))))
    (define (syntax-add-body syntax-bodies meta-level . body)
      (dict-update syntax-bodies meta-level
                   (lambda (existing) (append existing body))
                   (lambda () null))))
  (SubmoduleForm : submodule-form (e) -> submodule-form ()
                 [(module ,id ,module-path
                    (,[raw-provide-spec] ...)
                    (,[raw-require-spec] ...)
                    (,[module-level-form syntaxes] ...)
                    (,[submodule-form] ...)
                    (,[submodule-form*] ...))
                  `(module ,id ,module-path
                     (,raw-provide-spec ...)
                     (,raw-require-spec ...)
                     (,module-level-form ...)
                     (,(build-from-table (merge-syntax-tables syntaxes)) ...)
                     (,submodule-form ...)
                     (,submodule-form* ...))])
  (ModuleLevelForm : module-level-form (e [meta-level 0] [syntax-table (hash)])
                   -> module-level-form ((hash))
                   [(begin-for-syntax
                      ,[module-level-form syntax-table (+ meta-level 1)
                                          -> module-level-form* syntax-table*] ...)
                    (values `(#%plain-app (primitive void))
                            (syntax-add-body (merge-syntax-tables syntax-table*)
                                             (+ meta-level 1)
                                             (with-output-language (current-target syntax-body)
                                               `(begin-for-syntax ,module-level-form* ...))))])
  (TopLevelForm : top-level-form (e) -> top-level-form ()
                [(define-syntaxes (,v ...) ,[expr])
                 `(define-syntaxes* (,v ...) ,expr)])
  (GeneralTopLevelForm : general-top-level-form (e [meta-level 0] [syntax-table (hash)])
                       -> general-top-level-form ((hash))
                       [(define-syntaxes (,v ...) ,[expr])
                        (values `(#%plain-app (primitive void))
                                (syntax-add-body syntax-table
                                                 (+ meta-level 1)
                                                 (with-output-language (current-target syntax-body)
                                                   `(define-syntaxes (,v ...) ,expr))))])
  (Expr : expr (e) -> expr ((hash))))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x (make-variable 'x))
    (define-compiler-test current-target top-level-form
      (check-equal?
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
          () ()))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (submodule-form (submodule-form)
                  (- (module id module-path
                       (raw-provide-spec ...)
                       (raw-require-spec ...)
                       (module-level-form ...)
                       (syntax-level-form ...)
                       (submodule-form ...)
                       (submodule-form* ...)))
                  (+ (module id module-path (v* ...) (v** ...)
                       (raw-provide-spec ...)
                       (raw-require-spec ...)
                       (module-level-form ...)
                       (syntax-level-form ...)
                       (submodule-form ...)
                       (submodule-form* ...))))
  (syntax-level-form (syntax-level-form)
                     (- (syntax eni (syntax-body ...)))
                     (+ (syntax eni (v ...) (v* ...)
                                (syntax-body ...)))))

(define-pass identify-module-variables : current-source (e) -> current-target ()
  (SubmoduleForm : submodule-form (e) -> submodule-form ()
                 [(module ,id ,module-path
                    (,[raw-provide-spec] ...)
                    (,[raw-require-spec] ...)
                    (,[module-level-form bindings] ...)
                    (,syntax-level-form ...)
                    (,[submodule-form] ...)
                    (,[submodule-form*] ...))
                  (define-values (form bindings* syntaxes)
                    (for/fold ([form null]
                               [bindings* null]
                               [syntaxes null])
                              ([slf (in-list (reverse syntax-level-form))])
                      (define-values (f b s) (SyntaxLevelForm slf syntaxes))
                      (values (cons f form) b s)))
                  `(module ,id ,module-path (,(apply set-union '() bindings) ...) (,syntaxes ...)
                           (,raw-provide-spec ...)
                           (,raw-require-spec ...)
                           (,module-level-form ...)
                           (,form ...)
                           (,submodule-form ...)
                           (,submodule-form* ...))])
  (SyntaxLevelForm : syntax-level-form (e previous-syntaxes) -> syntax-level-form ('() '())
                   [(syntax ,eni (,[syntax-body bindings syntaxes] ...))
                    (define flattened-bindings (apply set-union '() bindings))
                    (values `(syntax ,eni
                                     (,flattened-bindings ...)
                                     (,previous-syntaxes ...)
                                     (,syntax-body ...))
                            flattened-bindings
                            (apply set-union '() syntaxes))])
  (SyntaxBody : syntax-body (e) -> syntax-body ('() '())
              [(define-syntaxes (,v ...) ,[expr])
               (values `(define-syntaxes (,v ...) ,expr)
                       null
                       v)]
              [(begin-for-syntax ,[module-level-form bindings] ...)
               (values `(begin-for-syntax ,module-level-form ...)
                       (apply set-union '() bindings)
                       null)])
  (ModuleLevelForm : module-level-form (e) -> module-level-form ('()))
  (GeneralTopLevelForm : general-top-level-form (e) -> general-top-level-form ('())
                       [(define-values (,v ...) ,[expr])
                        (values `(define-values (,v ...) ,expr)
                                v)])
  (Expr : expr (e) -> expr ('())))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x* (make-variable 'x))
    (define y (make-variable 'y))
    (define z (make-variable 'z))
    (define-compiler-test current-target top-level-form
      (check-equal?
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
      (check-equal?
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
          ,x*))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (raw-require-spec (raw-require-spec rrs)
                    (- phaseless-req-spec
                       (just-meta phase-level raw-require-spec ...)))
  (phaseless-req-spec (phaseless-req-spec)
                      (- (only raw-module-path v ...)
                         (all-except raw-module-path v ...)
                         (prefix-all-except id raw-module-path v* ...)))
  (raw-provide-spec (raw-provide-spec rps)
                    (- phaseless-prov-spec
                       (for-meta* phase-level phaseless-prov-spec)
                       (protect raw-provide-spec))
                    (+ (for-meta* phase-level phaseless-prov-spec ...)))
  (phaseless-prov-spec (phaseless-prov-spec)
                       (- (all-from-except raw-module-path v ...)
                          (all-defined-except v ...)
                          (struct v (v* ...))
                          (prefix-all-defined-except id v* ...)
                          (protect* phaseless-prov-spec ...))
                       (+ (protect v)
                          (protect-rename* v1 v2))))

(define-pass scrub-require-provide : current-source (e) -> current-target ()
  (definitions
    (define not-projected
      (block
       (struct not-projected ())
       (not-projected)))
    (define (projected? p)
      (not (equal? p not-projected))))
  (RawRequireSpec : raw-require-spec (e [project not-projected]) -> raw-require-spec ()
                  [(for-meta ,phase-level ,phaseless-req-spec)
                   `(for-meta ,phase-level ,(if (equal? project phase-level)
                                                (PhaselessReqSpec phaseless-req-spec project)
                                                null) ...)])
  (PhaselessReqSpec : phaseless-req-spec (e [project not-projected]) -> * ()
                    [,raw-module-path
                     (list)] ;; TODO
                    [(only ,raw-module-path ,v ...)
                     (list)] ;; TODO
                    [(all-except ,raw-module-path ,v* ...)
                     (list)] ;; TODO
                    [(prefix-all-except ,id ,raw-module-path ,v* ...)
                     (list)] ;; TODO
                    [(rename ,raw-module-path ,v1 ,v2)
                     (list)]) ;; TODO
  (RawProvideSpec : raw-provide-spec (e [protected? #f]) -> raw-provide-spec ()
                  [,phaseless-prov-spec
                   `(for-meta* 0 ,(PhaselessProvSpec phaseless-prov-spec protected?) ...)]
                  [(for-meta* ,phase-level ,phaseless-prov-spec)
                   `(for-meta* ,phase-level ,(PhaselessProvSpec phaseless-prov-spec protected?))]
                  [(protect ,[raw-provide-spec #t -> raw-provide-spec])
                   raw-provide-spec])
 (PhaselessProvSpec : phaseless-prov-spec (e [protected? #f]) -> * ()
                    [,v
                     (with-output-language (current-target phaseless-prov-spec)
                       (if protected?
                           (list `(protect ,v))
                           (list v)))]
                     [(rename* ,v1 ,v2)
                      (list `(rename* ,v1 ,v2))]
                     [(struct ,v (,v* ...))
                      (list)] ;; TODO
                     [(all-from-except ,raw-module-path ,v ...)
                      (list)] ;; TODO
                     [(all-defined-except ,v ...)
                      (list)] ;; TODO
                     [(prefix-all-defined-except ,id ,v* ...)
                      (list)] ;; TODO
                     [(protect* ,phaseless-prov-spec ...)
                      (append
                       (for/list ([pps (in-list phaseless-prov-spec)])
                         (PhaselessProvSpec pps #t)))]))

;; TODO, these tests
(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    #;(block
    (define x (make-variable 'x))
    (define-compiler-test current-target top-level-form
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
          () () ()))))))

;; ===================================================================================================


(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (lambda (lambda)
    (+ (#%plain-lambda formals expr)))
  (expr (expr)
        (- (#%plain-lambda formals expr* ... expr)
           (case-lambda (formals expr* ... expr) ...)
           (let-values ([(v ...) expr1] ...)
             expr* ... expr)
           (letrec-values ([(v ...) expr1] ...)
             expr* ... expr))
        (+ lambda
           (case-lambda lambda ...)
           (let-values ([(v ...) expr1] ...)
             expr)
           (letrec-values ([(v ...) expr1] ...)
             expr))))

;; Makes explicit begins so that only they need to deal with expression blocks.
;; Could probably be dealt with in parse-and-rename
;; Also marks variables as being referenced.
(define-pass make-begin-explicit : current-source (e) -> current-target ()
  (Expr : expr (e) -> expr ()
        [,v (set-variable-referenced?! v #t) v]
        [(#%plain-lambda ,[formals] ,[expr*] ... ,[expr])
         (if (= (length expr*) 0)
             `(#%plain-lambda ,formals ,expr)
             `(#%plain-lambda ,formals (begin ,expr* ... ,expr)))]
        [(case-lambda (,formals ,expr* ... ,expr))
         (with-output-language (current-source expr)
           (make-begin-explicit `(#%plain-lambda ,formals ,expr* ... ,expr)))]
        [(case-lambda (,formals ,expr* ... ,expr) ...)
         `(case-lambda ,(for/list ([f (in-list formals)]
                                   [e* (in-list expr*)]
                                   [e (in-list expr)])
                          (with-output-language (current-source expr)
                            (make-begin-explicit `(#%plain-lambda ,f ,e* ... ,e))))
                       ...)]
        [(let-values ([(,v ...) ,[expr1]] ...)
           ,[expr*] ... ,[expr])
         (if (= (length expr*) 0)
             `(let-values ([(,v ...) ,expr1] ...)
                ,expr)
             `(let-values ([(,v ...) ,expr1] ...)
                (begin ,expr* ... ,expr)))]
        [(letrec-values ([(,v ...) ,[expr1]] ...)
           ,[expr*] ... ,[expr])
         (if (= (length expr*) 0)
             `(letrec-values ([(,v ...) ,expr1] ...)
                ,expr)
             `(letrec-values ([(,v ...) ,expr1] ...)
                (begin ,expr* ... ,expr)))]))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define f (make-variable 'f))
    (define-compiler-test current-target top-level-form
      (check-equal?
       (current-compile #'(lambda (x) x x))
       `(#%expression (#%plain-lambda (,x) (begin ,x ,x))))
      (check-equal?
       (current-compile #'(case-lambda [(x) (+ x 1) (begin0 x (set! x 42))]))
       `(#%plain-lambda (,x)
                        (begin (#%plain-app (primitive +) ,x'1)
                               (begin0 ,x
                                       (set! ,x '42)))))
      (check-equal?
       (current-compile #'(case-lambda [(x) (+ x 1)]
                                       [(x y) x (+ x y)]))
       `(case-lambda (#%plain-lambda (,x) (#%plain-app (primitive +) ,x '1))
                     (#%plain-lambda (,x ,y) (begin ,x (#%plain-app (primitive +) ,x ,y)))))
      (check-equal?
       (current-compile #'(letrec ([f 5])
                      (display "Hello")
                      f))
       `(letrec-values ([(,f) '5])
          (begin
            (#%plain-app (primitive display) '"Hello")
            ,f)))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
   (lambda (lambda)
     (- (#%plain-lambda formals expr))
     (+ (#%plain-lambda formals abody)))
   (expr (expr)
         (- (let-values ([(v ...) expr1] ...)
              expr)
            (letrec-values ([(v ...) expr1] ...)
              expr))
         (+ (let-values ([(v ...) expr1] ...)
              abody)
            (letrec-values ([(v ...) expr1] ...)
              abody)))
   (assigned-body (abody)
                  (+ (assigned (v ...) expr))))

(define-pass identify-assigned-variables : current-source (e) -> current-target ()
  (definitions
    (define-syntax-rule (formals->identifiers* fmls)
      (formals->identifiers current-target fmls)))
  (Lambda : lambda (e) -> lambda ('())
          [(#%plain-lambda ,[formals] ,[expr assigned*])
           (values `(#%plain-lambda ,formals
                                    (assigned (,(set-intersect assigned*
                                                               (formals->identifiers* formals))
                                               ...)
                                              ,expr))
                   (set-remove assigned* (formals->identifiers* formals)))])
  (Expr : expr (e) -> expr ('())
        [(set! ,v ,[expr assigned*])
         (set-variable-assigned?! v #t)
         (values `(set! ,v ,expr)
                 (set-add assigned* v))]
        [(let-values ([(,v ...) ,[expr assigned]] ...) ,[expr* assigned*])
         (values `(let-values ([(,v ...) ,expr] ...)
                    (assigned (,(set-intersect assigned* (apply set-union '() v)) ...) ,expr*))
                 (apply set-union '() (set-remove assigned* v) assigned))]
        [(letrec-values ([(,v ...) ,[expr assigned]] ...) ,[expr* assigned*])
         (values `(letrec-values ([(,v ...) ,expr] ...)
                    (assigned (,(set-intersect assigned* (apply set-union '() v)) ...) ,expr*))
                 (apply set-union '() (set-remove assigned* v) assigned))]
        ;; Really *should* be generated
        [(if ,[expr1 assigned1] ,[expr2 assigned2] ,[expr3 assigned3])
         (values `(if ,expr1 ,expr2 ,expr3)
                 (set-union assigned1 assigned2 assigned3))]
        [(begin ,[expr* assigned*] ... ,[expr assigned])
         (values `(begin ,expr* ... ,expr)
                 (apply set-union assigned assigned*))]
        [(begin0 ,[expr assigned] ,[expr* assigned*] ...)
         (values `(begin0 ,expr ,expr* ...)
                 (apply set-union assigned assigned*))]
        [(#%plain-app ,[expr assigned] ,[expr* assigned*] ...)
         (values `(#%plain-app ,expr ,expr* ...)
                 (apply set-union assigned assigned*))]
        [(case-lambda ,[lambda assigned] ...)
         (values `(case-lambda ,[lambda assigned] ...)
                 (apply set-union '() assigned))])
  ;; Also *should* really be generated
  (TopLevelForm : top-level-form (e) -> top-level-form ('())
                [(begin* ,[top-level-form assigned] ...)
                 (values `(begin* ,top-level-form ...)
                         (apply set-union '() assigned))]
                [(begin-for-syntax* ,[top-level-form assigned] ...)
                 (values `(begin-for-syntax* ,top-level-form ...)
                         (apply set-union '() assigned))]
                [(#%expression ,[expr assigned])
                 (values `(#%expression ,expr)
                         assigned)]
                [(define-syntaxes* (,v ...) ,[expr assigned])
                 (values `(define-syntaxes* (,v ...) ,expr)
                         (set-subtract assigned v))])
  (GeneralTopLevelForm : general-top-level-form (e) -> general-top-level-form ('())
                       [(define-values (,v ...) ,[expr assigned])
                        (values `(define-values (,v ...) ,expr)
                                (set-subtract assigned v))])
  (SubmoduleForm : submodule-form (e) -> submodule-form ('()))
  (ModuleLevelForm : module-level-form (e) -> module-level-form ('()))
  (let-values ([(e* free*) (TopLevelForm e)])
    e*))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define-compiler-test current-target top-level-form
      (check-equal?
       (current-compile #'(letrec ([y 8])
                            y))
       `(letrec-values ([(,y) '8])
          (assigned ()
                    ,y)))
      (check-equal?
       (current-compile #'(let ([x 8])
                            (set! x 5)
                            (+ x 42)))
       `(let-values ([(,x) '8])
          (assigned (,x)
                    (begin (set! ,x '5)
                           (#%plain-app (primitive +) ,x '42)))))
      (check-equal?
       (current-compile #'(let ([x 1])
                            (letrec ([y (lambda (x) y)])
                              (+ x y))))
       `(let-values ([(,x) '1])
          (assigned ()
                    (letrec-values ([(,y) (#%plain-lambda (,x) (assigned () ,y))])
                      (assigned ()
                                (#%plain-app (primitive +) ,x ,y))))))
      (check-equal?
       (current-compile #'(lambda x
                            (set! x 42)
                            x))
       `(#%expression (#%plain-lambda ,x
                                      (assigned (,x)
                                                (begin
                                                  (set! ,x '42)
                                                  ,x)))))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (- (let-values ([(v ...) expr1] ...)
             abody)
           (letrec-values ([(v ...) expr1] ...)
             abody)
           (set! v expr)
           (quote datum))
        (+ set-expr
           (undefined)
           (let ([v expr1] ...)
             set-abody)
           (letrec ([v lambda] ...)
             expr)))
  (lambda (lambda)
    (+ (quote datum)))
  (set-expr (set-expr)
            (+ (set!-values (v ...) expr)))
  (set-abody (set-abody)
             (+ (begin-set! set-expr ... abody))))

(define-pass purify-letrec : current-source (e) -> current-target ()
  (Expr : expr (e) -> expr ()
        [(set! ,v ,[expr])
         `(set!-values (,v) ,expr)]
        [(letrec-values ([(,v) ,[lambda]] ...)
           (assigned (,v* ...) ,[expr]))
         (guard (set-empty? (set-intersect v* v)))
         `(letrec ([,v ,lambda] ...)
            ,expr)]
        [(letrec-values ([(,v ...) ,[expr]] ...)
           (assigned (,v* ...) ,[expr*]))
         (define flattened-ids (apply append v))
         `(let ([,flattened-ids ,(make-list (length flattened-ids) `(undefined))] ...)
            (begin-set!
              (set!-values (,v ...) ,expr) ...
              (assigned (,(apply set-union v* v) ...)
                        ,expr*)))]
        [(let-values ([(,v) ,[expr]] ...)
           ,[abody])
         `(let ([,v ,expr] ...)
            (begin-set!
              ,abody))]
        [(let-values ([(,v ...) ,[expr]] ...)
           (assigned (,v* ...) ,[expr*]))
         (define flattened-ids (apply append v))
         `(let ([,flattened-ids ,(make-list (length flattened-ids) `(undefined))] ...)
            (begin-set!
              (set!-values (,v ...) ,expr) ...
              (assigned (,v* ...)
                        ,expr*)))]))

;; TODO: need tests here
;; (Use tests from cp0 pass)
(module+ test
  (update-current-compile!))

;; ===================================================================================================

;; App conetxt, for storing valid functions
;; Valid contexts are 'test 'value 'effect, and other
;;   app contexts
(struct app (operands
             context
             [inlined? #:auto])
  #:mutable
  #:auto-value #f)

(struct counter (value
                 context
                 k)
  #:mutable)
(define (make-counter value #:context [context #f] #:k [k #f])
  (counter value context k))

(define current-inline-size-limit (make-parameter 50))
(define current-inline-effort-limit (make-parameter 100))

(define-pass inline-expressions*
  : current-target (e context env effort-counter size-counter) -> current-target ()
  (definitions

    ;; Environments map source program variables to residual program
    ;;   variables. Bindings not in the environment map directly
    ;;   to themselves
    (define empty-env (hash))
    (define ((env-lookup env) x)
      (dict-ref env x x))
    (define (extend-env env x opnd)
      (define x*
        (make-variable (variable-name x)
                       #:operand opnd
                       #:assigned? #t
                       #:referenced? #t))
      (dict-set env x x*))
    (define (extend-env* env x* opnd*)
      (for/fold ([env env])
                ([x (in-list x*)]
                 [opnd (in-list opnd*)])
        (extend-env env x opnd)))

    ;; Active counters have a continuation and context
    (define (active-counter? counter)
      (and (counter? counter) (counter-context counter)))

    ;; Passive counters are counters with #f as a context, and error as a continuation
    (define passive-counter-default-value 1000)
    (define (make-passive-counter)
      (make-counter passive-counter-default-value
                    #:context #f
                    #:k (lambda x
                          (error 'inline-expressions
                                 "Tried to call continuation on a passive counter"))))
    (define (passive-counter-value counter)
      (- passive-counter-default-value (counter-value counter)))

    ;; Determins if the amount of operands passed into a function
    ;;    matches the amount accepted by the formals
    ;; Formals Opearnds -> Boolean
    (define (operands-match? formals operands)
      (define formals* (formals->identifiers current-target formals))
      (define rest? (formals-rest? current-target formals))
      (if rest?
          ((length formals) . <= . (length operands))
          (= (length formals) (length operands))))

    ;; Determins if a syntactic form is simple and can thus be
    ;;    ignored in a begin statement
    ;; Expr -> Boolean
    (define (simple? e)
      (nanopass-case (current-target expr) e
                     [(quote ,datum) #t]
                     [,v #t]
                     [,lambda #t]
                     [(primitive ,id) #t]
                     [(#%plain-app (primitive ,id) (quote ,datum) ...)
                      (guard (effect-free? id))
                      #t]
                     [else #f]))

    ; Constructs begin expressions, flattening them if possible
    ; (Listof Expr) Expr -> Expr
    (define (make-begin e1 e2)
      (define e1* (filter (negate simple?) e1))
      (cond [(null? e1*) e2]
            [else
             (with-output-language (current-target expr)
               (nanopass-case (current-target expr) e2
                              [(begin ,expr3 ... ,expr4)
                               `(begin ,(append e1* expr3) ,expr4)]
                              [else `(begin ,e1* ... ,e2)]))]))

    ;; Constructs a let binding (to be used by inline)
    ;;   Empty lets are removed, assigned but not referenced
    ;;   variables are kept only for effect.
    ;; (Listof Var-Exprs) (Listof Operands) Expr -> Expr
    (define (make-let vars operands body size-counter)
      (define (set-effect! result)
        (for-each (curryr set-operand-residualized-for-effect?! #t) operands)
        result)
      (define var-map (map cons vars operands))
      (with-output-language (current-target expr)
        (nanopass-case (current-target expr) body
                       [(quote ,datum) (set-effect! body)]
                       [(primitive ,id) (set-effect! body)]
                       [,v
                        (for ([(key val) (in-dict var-map)])
                          (unless (eq? val v)
                            (set-operand-residualized-for-effect?! val #t)))
                        (cond
                          [(set-member? vars v)
                           (score-value-visit-operand! (dict-ref var-map v) size-counter)]
                          [else body])]
                       [else
                        (for ([var (in-list vars)])
                          (when (and (variable-assigned? var)
                                     (not (variable-referenced? var)))
                            (set-operand-residualized-for-effect?! var #t)))
                        (define visited-vars
                          (for/list ([(i j) (in-dict var-map)]
                                     #:when (and (variable-referenced? i)
                                                 (variable-assigned? i)))
                            (if (variable-referenced? i)
                                (cons i (score-value-visit-operand! j size-counter))
                                (cons i `(primitive void)))))
                        (if (dict-empty? visited-vars)
                            body
                            `(let ([,(dict-keys visited-vars) ,(dict-values visited-vars)] ...)
                               ,body))])))
 
    ;; Returns the resulting expression of a sequence of operations.
    ;;   (e.g. the last expression of a begin form)
    ;; Expr -> Expr
    (define (result-expr e)
      (nanopass-case (current-target expr) e
                     [(begin ,expr* ... ,expr) expr]
                     [(begin0 ,expr ,expr* ...) expr]
                     [else e]))

    ;; Contextually aware equality checks for expressions.
    ;;    (For example, all datusm are equal in an effect context)
    ;; Expr Expr Context -> Boolean
    (define (contextual-equal? e1 e2 ctx)
      (nanopass-case (current-target expr) e1
                     [(quote ,datum1)
                      (nanopass-case (current-target expr) e2
                                     [(quote ,datum2)
                                      [match context
                                        ['effect #t]
                                        ['test (if datum1 datum2 (not datum2))]
                                        [else (eq? datum1 datum2)]]]
                                     [else #f])]
                     [else #f]))

    ;; Performs variable inlining
    ;; Variable Context Env Counter Counter -> Expr
    (define (inline-ref v context env effort-counter size-counter)
      (with-output-language (current-target expr)
        (match context
          ['effect `(primitive void)]
          [_
           (define v* ((env-lookup env) v))
           (define opnd (variable-operand v*))
           (cond
             [(and opnd (not (operand-inner-pending? opnd)))
              (dynamic-wind
               (lambda () (set-operand-inner-pending?! opnd #t))
               (lambda () (value-visit-operand! opnd))
               (lambda () (set-operand-inner-pending?! opnd #f)))
              (cond
                [(variable-assigned? v) (residualize-ref v* size-counter)]
                [else
                 (define rhs (result-expr (operand-value opnd)))
                 (nanopass-case (current-target expr) rhs
                                [(quote ,datum) rhs]
                                [,v**
                                 (cond
                                   [(variable-assigned? v**) (residualize-ref v* size-counter)]
                                   [else
                                    (define v-opnd (variable-operand v))
                                    (if (and v-opnd (operand-value v-opnd))
                                        (copy v** v-opnd context effort-counter size-counter)
                                        (residualize-ref v** size-counter))])]
                                [else (copy v opnd context effort-counter size-counter)])])]
             [else (residualize-ref v* size-counter)])])))
      
    ;; Helper for inline-ref, tries to inline references to variables
    ;; Variable Operand Context Counter Counter -> Variable
    (define (copy v opnd context effort-counter size-counter)
      (with-output-language (Lsrc expr)
        (define rhs (result-expr (operand-value opnd)))
        (nanopass-case (current-target expr) rhs
                       [(#%plain-lambda ,formals ,abody)
                        (match context
                          ['value (residualize-ref v size-counter)]
                          ['test `'#t]
                          [(struct* app ())
                           (or (and (not (operand-outer-pending? opnd))
                                    (dynamic-wind
                                     (lambda () (set-operand-outer-pending?! opnd #t))
                                     (lambda ()
                                       (let/cc abort
                                         (define limit (if (active-counter? size-counter)
                                                           (counter-value size-counter)
                                                           (current-inline-size-limit)))
                                         (inline rhs context empty-env
                                                 (if (active-counter? effort-counter)
                                                     effort-counter
                                                     (make-counter (current-inline-effort-limit)
                                                                   #:context context
                                                                   #:k abort))
                                                 (make-counter limit #:context context #:k abort))))
                                     (lambda () (set-operand-outer-pending?! opnd #f))))
                               (residualize-ref v size-counter))])]
                       [(primitive ,id)
                        (match context
                          ['value rhs]
                          ['test `'#t]
                          [(struct* app ()) (fold-prim id context size-counter)])]
                       [else (residualize-ref v size-counter)])))
 
    ;; If an application has been inlined, keep around
    ;;   the expresssions for side effects (in a begin form)
    ;;   otherwise just return the call
    ;; Expr (Listof Operands) Context Env Counter Counter -> Expr
    (define (inline-call e operands context env effort-counter size-counter)
      (define context* (app operands context))
      (define e* (inline-expressions e context* env effort-counter size-counter))
      (if (app-inlined? context*)
          (residualize-operands operands e* size-counter)
          (with-output-language (current-target expr)
            `(#%plain-app ,e*
                          ,(map (curryr score-value-visit-operand! size-counter)
                                operands) ...))))

    ;; Try to inline an expression to a value. Memoizes the result,
    ;;    returns the resulting expression.
    ;; Operand -> Expr
    (define (value-visit-operand! opnd)
      (or (operand-value opnd)
          (let ()
            (define size-counter (make-passive-counter))
            (define e (inline-expressions (operand-exp opnd)
                                          'value
                                          (operand-env opnd)
                                          (operand-effort-counter opnd)
                                          size-counter))
            (set-operand-value! opnd e)
            (set-operand-size! opnd (passive-counter-value size-counter))
            e)))

    ;; A varient of value-visit-operand! that also affects the value
    ;;   of the size-counter given to it.
    ;; Opernad Counter -> Expr
    (define (score-value-visit-operand! opnd size-counter)
      (define val (value-visit-operand! opnd))
      (decrement! size-counter (operand-size opnd))
      val)

    ;; Sets a variable as being referenced
    ;; Ref -> Ref
    (define (residualize-ref v size-counter)
      (decrement! size-counter 1)
      (set-variable-referenced?! v #t)
      v)

    ;; Inlines a call, keeping around operands only when needed
    ;;   for effect
    ;; (Listof Operands) Expr Counter -> Expr
    (define (residualize-operands operands e size-counter)
      (define operands* (filter operand-residualized-for-effect? operands))
      (cond [(null? operands*) e]
            [else
             (define operands** (for/list ([o (in-list operands*)])
                                  (or (operand-value o)
                                      (inline-expressions (operand-exp o)
                                                          'effect
                                                          (operand-env o)
                                                          (operand-effort-counter o)
                                                          size-counter))))
             (define operands***
               (for/list ([o (in-list operands**)]
                          #:unless (simple? o))
                 (decrement! size-counter (operand-size o))
                 o))
             (if (null? operands***) e (make-begin operands*** e))]))

    ;; Performs the actual inlining
    ;; Lambda-Expr App-Context Env -> Exp
    (define (inline proc context env effort-counter size-counter)
      (nanopass-case (current-target lambda) proc
                     [(#%plain-lambda ,formals
                                      (assigned (,v ...) ,expr))
                      (define formals* (formals->identifiers current-target formals))
                      (define rest? (formals-rest? current-target formals))
                      (define opnds (app-operands context))
                      (define opnds*
                        (cond
                          [rest?
                           (define-values (single-opnds rest-opnds)
                             (split-at opnds (- (length formals*) 1)))
                           (append single-opnds
                                   ;; TODO, does this operand need to be
                                   ;;   residulized for effect?
                                   ;;   or recalculate effort counter?
                                   (list
                                    (make-operand
                                     (with-output-language (current-target expr)
                                       `(#%plain-app (primitive list)
                                                     ,(map operand-exp rest-opnds) ...))
                                     (apply hash-union (hash)
                                            (map operand-env rest-opnds))
                                     (operand-effort-counter (first rest-opnds)))))]
                          [else opnds]))
                      (define env* (extend-env* env formals* opnds*))
                      (define body (inline-expressions expr
                                                       (app-context context)
                                                       env*
                                                       effort-counter
                                                       size-counter))
                      (define result (make-let formals* opnds* body size-counter))
                      (set-app-inlined?! context #t)
                      result]))

    ;; Does constant fold on primitives (if possible)
    ;; ID Context Counter -> Expr
    (define (fold-prim prim context size-counter)
      (define operands (app-operands context))
      (with-output-language (current-target expr)
        (define result
          (or (and (effect-free? prim)
                   (match (app-context context)
                     ['effect `(primitive void)]
                     ['test (and (return-true? prim) `(quote #t))]
                     [else #f]))
              (and (foldable? prim)
                   (let ([vals (map value-visit-operand! operands)])
                     (define-values (consts? operands*)
                       (for/fold ([const-vals #t]
                                  [ops null])
                                 ([v (in-list vals)])
                         (values
                          (and const-vals
                               (nanopass-case (current-target expr) v
                                              [(quote ,datum) #t]
                                              [else #f]))
                          (cons
                           (nanopass-case (current-target expr) v
                                          [(quote ,datum) datum]
                                          [else #f])
                           ops))))
                     (define operands** (reverse operands*))
                     (and consts?
                          (with-handlers ([exn? (lambda (x) (displayln "inline failed") #f)])
                            `(quote ,(parameterize ([current-namespace (make-base-namespace)])
                                       (eval (cons prim operands**))))))))))
        (cond
          [result (for-each (curryr set-operand-residualized-for-effect?! #t) operands)
                  (set-app-inlined?! context #t)
                  result]
          [else (decrement! size-counter 1)
                `(primitive ,prim)])))

    ;; Resets the inlined process inside of `app` contexts
    ;;   Recurse all the way to the outer most context.
    ;; App-Context -> Void
    (define (reset-integrated! context)
      (set-app-inlined?! context #f)
      (define context* (app-context context))
      (when (app? context*)
        (reset-integrated! context)))
    
    ;; Decrements the given counter by amount steps
    ;;   If the result goes below 0, then undo the attempt at inlining
    ;;   and call the counters continuation.
    ;; Counter Number -> Void
    (define (decrement! counter amount)
      (define n (- (counter-value counter) amount))
      (set-counter-value! counter n)
      (when (< n 0)
        (when (app? (counter-context counter))
          (reset-integrated! (counter-context counter)))
        ((counter-k counter) #f))))

  (Expr : expr (e [context context]
                  [env env]
                  [effort-counter effort-counter]
                  [size-counter size-counter])
        -> expr ()
        [(quote ,datum) `(quote ,datum)]
        [,v (inline-ref v context env effort-counter size-counter)]
        [(begin ,[expr1 'effect env effort-counter size-counter -> expr1] ...
                ,[expr2 context env -> expr2])
         (make-begin expr1 expr2)]
        [(if ,[expr1 'test env effort-counter size-counter -> expr1] ,expr2 ,expr3)
         (nanopass-case (current-target expr) (result-expr expr1)
                        [(quote ,datum)
                         (make-begin (list expr1)
                                     (inline-expressions (if datum expr2 expr3)
                                                         context
                                                         env
                                                         effort-counter
                                                         size-counter))]
                        [else
                         (define context* (if (app? context) 'value context))
                         (define expr2*
                           (inline-expressions expr2 context* env effort-counter size-counter))
                         (define expr3*
                           (inline-expressions expr3 context* env effort-counter size-counter))
                         (cond [(contextual-equal? expr2* expr3* context*)
                                (make-begin (list expr1) expr2*)]
                               [else
                                (decrement! size-counter 1)
                                `(if ,expr1 ,expr2* ,expr3*)])])]
        [(set!-values (,v ...) ,expr)
         (define v* (map (env-lookup env) v))
         (cond
           [(ormap variable-referenced? v*)
            (define expr* (inline-expressions expr 'value env effort-counter size-counter))
            (map (curryr set-variable-assigned?! #t) v*)
            `(set!-values (,v* ...) ,expr*)]
           [else
            (make-begin
             (list
              (inline-expressions expr 'effect env effort-counter size-counter))
             `(#%plain-app (primitive void)))])]
        [(#%plain-app ,expr ,expr* ...)
         (inline-call expr
                      (map (curryr make-operand env effort-counter) expr*)
                      context
                      env
                      effort-counter
                      size-counter)]
        [(primitive ,id)
         (match context
           ['effect `'#t]
           ['test `'#t]
           ['value (decrement! size-counter 1) e]
           [(struct* app ()) (fold-prim id context size-counter)])]
        [(let ([,v* ,expr*] ...)
           (begin-set!
             (assigned (,v ...)
                       ,expr)))
         (inline-expressions
          `(#%plain-app (#%plain-lambda (,v* ...) ,expr)
                        ,expr* ...)
          context env effort-counter size-counter)]
        [(letrec ([,v ,lambda] ...)
           ,expr)
         (define env* (extend-env* env v (make-list (length v) #f)))
         (define v* (map (env-lookup env*) v))
         (define operands (map (curryr make-operand env* effort-counter) lambda))
         (for ([i (in-list v*)]
               [j (in-list operands)])
           (set-variable-operand! i j))
         (define expr* (inline-expressions expr context env* effort-counter size-counter))
         (define filtered-vars
           (for/list ([i (in-list v*)]
                      [j (in-list operands)]
                      #:when (variable-referenced? i))
             (cons i j)))
         (cond [(or (null? filtered-vars)
                    (nanopass-case (current-target expr) expr*
                                   [(quote ,datum) #t]
                                   [(primitive ,id) #t]
                                   [else #f]))
                expr*]
               [else
                (decrement! size-counter 1)
                `(letrec ([,(dict-keys filtered-vars)
                           ,(map operand-value (dict-values filtered-vars))] ...)
                   ,expr)])])

  (Lambda : lambda (e [context context]
                      [env env]
                      [effort-counter effort-counter]
                      [size-counter size-counter])
          -> lambda ()
          [(#%plain-lambda ,formals (assigned (,v ...) ,expr))
           (match context
             ['effect `'#t]
             ['test `'#t]
             ['value
              (decrement! size-counter 1)
              (define formals* (formals->identifiers current-target formals))
              (define env* (extend-env* env formals* (make-list (length formals*) #f)))
              `(#%plain-lambda ,formals
                               (assigned
                                (,v ...)
                                ,(inline-expressions expr 'value env* effort-counter size-counter)))]
             [(struct* app ()) (inline e context env effort-counter size-counter)])])

  (TopLevelForm : top-level-form (e [context context]
                                    [env env]
                                    [effort-counter effort-counter]
                                    [size-counter size-counter])
                -> top-level-form ())
  
  (begin
    (decrement! effort-counter 1)
    (TopLevelForm e context env effort-counter size-counter)))

(define (inline-expressions e
                            [context 'value]
                            [env (hash)]
                            [effort-counter (make-counter (current-inline-effort-limit))]
                            [size-counter (make-counter (current-inline-size-limit))])
  (inline-expressions* e context env effort-counter size-counter))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
     (define a (make-variable 'a))
     (define b (make-variable 'b))
     (define c (make-variable 'c))
     (define x (make-variable 'x))
     (define y (make-variable 'y))
     (define z (make-variable 'z))
     (define-compiler-test current-target top-level-form
       (check-equal?
        (current-compile #'((lambda (x) 42) 54))
        `'42)
       (check-equal?
        (current-compile #'((lambda (x) x) (lambda (y) y)))
        `(#%plain-lambda (,y) (assigned () ,y)))
       (check-equal?
        (current-compile #'(let ([x 5]
                                 [y 6])
                             (+ x y)))
        `'11)
       (check-equal?
        (current-compile #'(letrec-values ([(a) (lambda (x) a)])
                             a))
        `(letrec ([,a (#%plain-lambda (,x) (assigned () ,a))])
           ,a))
       (check-equal?
        (current-compile #'(letrec-values ([(a) (lambda (x) b)]
                                           [(b) (lambda (y) a)])
                             (a b)))
        `(letrec ([,a (#%plain-lambda (,x) (assigned () ,b))]
                  [,b (#%plain-lambda (,y) (assigned () ,a))])
           (#%plain-app ,a ,b)))
       (check-equal?
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
       (check-equal?
        (current-compile #'(let ([x (if #t 5 6)])
                             (set! x (+ x 1))))
        `(let ([,x '5])
           (begin-set!
             (assigned (,x) (set!-values (,x) (#%plain-app (primitive +) ,x '1))))))
       (check-equal?
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
       (check-equal?
        (current-compile #'(let-values ([(x y) (values 1 2)])
                             (set! x y)
                             y))
        `(let ([,x (undefined)]
               [,y (undefined)])
           (begin-set!
             (set!-values (,x ,y) (#%plain-app (primitive values) '1 '2))
             (assigned (,x)
                       ,y))))
       (check-equal?
        (current-compile #'(letrec ([fact (lambda (x)
                                                 (if (x . <= . 0)
                                                     1
                                                     (* x (fact (- x 1)))))])
                                  (fact 5)))
        `'120)))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (- set-expr
           (let ([v expr1] ...)
             set-abody))
        (+ (quote datum)
           (let ([v expr1] ...)
             expr)
           (#%unbox v)
           (#%box v)
           (set!-values (v ...) expr)
           (set!-boxes (v ...) expr)))
  (lambda (lambda)
    (- (#%plain-lambda formals abody)
       (quote datum))
    (+ (#%plain-lambda formals expr)))
  (set-abody (set-abody)
             (- (begin-set! set-expr ... abody)))
  (set-expr (set-expr)
            (- (set!-values (v ...) expr)))
  (assigned-body (abody)
                 (- (assigned (v ...) expr))))

(define-pass convert-assignments : current-source (e) -> current-target ()
  (definitions
    (define ((lookup-env env) x)
      (dict-ref env x x))
    (define (extend-env env assigned*)
      ;(define temp* (map (fresh) assigned*))
      (define temp* assigned*)
      (append (map cons assigned* temp*) env))
    (with-output-language (current-target expr)
      (define (build-let id* expr* body)
        (if (null? id*)
            body
            `(begin
               (set!-values (,id*) (#%box ,expr*)) ...
               ,body)
            #;`(let ([,id* (#%box ,expr*)] ...)
               ,body)))))
  (Formals : formals (e [env '()]) -> formals ()
           [,v ((lookup-env env) v)]
           [(,v ...)
            `(,(map (lookup-env env) v) ...)]
           [(,v ,v* ... . ,v2)
            `(,((lookup-env env) v) ,(map (lookup-env env) v*) ... . ,((lookup-env env) v2))])
  (Lambda : lambda (e [env '()]) -> expr ()
          [(quote ,datum) `(quote ,datum)]
          [(#%plain-lambda ,formals
                           (assigned (,v ...) ,expr))
           (define env* (extend-env env v))
           `(#%plain-lambda ,(Formals formals env*)
                            ,(build-let v (map (lookup-env env*) v)
                                        (Expr expr env* #t)))])
  [Expr : expr (e [env '()] [boxes? #t]) -> expr ()
        [(let ([,v ,[expr]] ...)
           (begin-set!
             ,set-expr ...
             (assigned (,v* ...) ,expr*)))
         (cond [(null? v) (Expr expr* env #t)]
               [else (define env* (extend-env env v*))
                     (define let* (build-let v* (map (lookup-env env*) v*)
                                             (Expr expr* env* #t)))
                     (if (= (length set-expr) 0)
                         `(let ([,(map (lookup-env env*) v) ,expr] ...)
                            ,let*)
                         `(let ([,(map (lookup-env env*) v) ,expr] ...)
                            (begin
                              ,(for/list ([e (in-list set-expr)])
                                 (Expr e env* #f)) ...
                              ,let*)))])]
        [,v
         (if (dict-has-key? env v) `(#%unbox ,v) v)]
        [(set!-values (,v ...) ,expr)
         (define expr* (Expr expr env #f))
         (if boxes?
             `(set!-boxes (,v ...) ,expr*)
             `(set!-values (,(map (lookup-env env) v) ...) ,expr*))]])

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define-compiler-test current-target top-level-form
      (check-equal?
       (current-compile #'(let ([x 5])
                            (set! x 6)
                            x))
       `(let ([,x '5])
          (begin
            (set!-values (,x) (#%box ,x))
            (begin
              (set!-boxes (,x) '6)
              (#%unbox ,x)))))
      (check-equal?
       (current-compile #'(lambda (x y)
                            (set! x 5)
                            (list x y)))
       `(#%expression (#%plain-lambda (,x ,y)
                                      (begin
                                        (set!-values (,x) (#%box ,x))
                                        (begin
                                          (set!-boxes (,x) '5)
                                          (#%plain-app (primitive list) (#%unbox ,x) ,y))))))
      (check-equal?
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
      (check-equal?
       (current-compile #'(let-values ([(x y) (values 1 2)])
                            (set! x y)
                            y))
       `(let ([,x (undefined)]
              [,y (undefined)])
          (begin
            (set!-values (,x ,y) (#%plain-app (primitive values) '1 '2))
            (begin
              (set!-values (,x) (#%box ,x))
              ,y))))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (entry compilation-top)
  (compilation-top (compilation-top)
                   (+ (program (binding ...) top-level-form)))
  (lambda (lambda)
    (- (#%plain-lambda formals expr))
    (+ (#%plain-lambda formals fbody)))
  (binding (binding)
           (+ v
              false))
  (free-body (fbody)
             (+ (free (v ...) (binding* ...) expr))))

(define-pass uncover-free : current-source (e) -> current-target ()
  (definitions
    (define-syntax-rule (formals->identifiers* formals)
      (formals->identifiers current-target formals)))
  (Lambda : lambda (e [env '()]) -> lambda ('() '())
          [(#%plain-lambda ,[formals] ,expr*)
           (define id* (formals->identifiers* formals))
           (define-values (expr free-local free-global) (Expr expr* (set-union env id*)))
           (define free-local* (set-subtract free-local id*))
           (values `(#%plain-lambda ,formals
                                    (free (,free-local* ...) (,free-global ...) ,expr))
                   free-local*
                   free-global)])
  (GeneralTopLevelForm : general-top-level-form (e [env '()]) -> general-top-level-form ('() '())
                       [(define-values (,v ...) ,[expr free-local free-global])
                        (values `(define-values (,v ...) ,expr)
                                free-local
                                (set-union free-global v))])
  (Expr : expr (e [env '()]) -> expr ('() '())
        [,v (if (set-member? env v)
                 (values v (list v) '())
                 (values v '() (list v)))]
        [(let ([,v* ,[expr* env -> expr* free-local* free-global*]] ...)
           ,expr**)
         (define-values (expr free-local free-global) (Expr expr** (set-union env v*)))
         (values
          `(let ([,v* ,expr*] ...)
             ,expr)
          (apply set-union (set-subtract free-local v*) free-local*)
          (apply set-union free-global free-global*))]
        [(letrec ([,v* ,lambda**] ...)
           ,expr**)
         (define env* (set-union env v*))
         (define-values (expr free-local free-global) (Expr expr** env*))
         (define-values (lambda* free-local* free-global*)
           (for/fold ([lambda* null]
                      [free-local* null]
                      [free-global* null])
                     ([i (in-list lambda**)])
             (define-values (l fl fg) (Lambda i env*))
             (values (cons l lambda*) (cons fl free-local*) (cons fg free-global*))))
         (values `(letrec ([,v* ,(reverse lambda*)] ...)
                    ,expr)
                 (apply set-union (set-subtract free-local v*) (reverse free-local*))
                 (apply set-union (set-subtract free-global v*) (reverse free-global*)))]
        [(set!-boxes (,v) ,[expr free-local free-global])
         (if (set-member? env v)
             (values `(set!-boxes (,v) ,expr) (set-add free-local v) free-global)
             (values `(set!-values (,v) ,expr) free-local (set-add free-global v)))]
        [(set!-boxes (,v ...) ,[expr free-local free-global])
         (values `(set!-boxes (,v ...) ,expr)
                 (set-union free-local (set-intersect v env))
                 (set-union free-global (set-subtract v env)))]
        [(set!-values (,v ...) ,[expr free-local free-global])
         (values `(set!-values (,v ...) ,expr)
                 (set-union free-local (set-intersect v env))
                 (set-union free-global (set-subtract v env)))]
        [(#%box ,v)
         (if (set-member? env v)
             (values `(#%box ,v) (list v) '())
             (values `(#%box ,v) '() (list v)))]
        [(#%unbox ,v)
         (if (set-member? env v)
             (values `(#%unbox ,v) (list v) '())
             (values `(#%unbox ,v) '() (list v)))]
        [(#%top . ,v)
         (values `(#%top . ,v) '() (list v))]
        [(#%variable-reference)
         (values `(#%variable-reference)
                 null
                 '(#f))]
        [(#%variable-reference ,v)
         (if (set-member? env v)
             (values `(#%variable-reference ,v) (list v) '())
             (values `(#%variable-reference ,v) '() (list v)))]
        [(#%variable-reference-top ,v)
         (values `(#%variable-reference-top ,v) '() (list v))]
        ;; Everything below here really is boilerplate
        [(case-lambda ,[lambda free-local free-global] ...)
         (values `(case-lambda ,lambda ...)
                 (apply set-union '() free-local)
                 (apply set-union '() free-global))]
        [(if ,[expr1 free-local1 free-global1]
             ,[expr2 free-local2 free-global2]
             ,[expr3 free-local3 free-global3])
         (values `(if ,expr1 ,expr2 ,expr3)
                 (set-union free-local1 free-local2 free-local3)
                 (set-union free-global1 free-global2 free-global3))]
        [(begin ,[expr* free-local* free-global*] ...
                ,[expr free-local free-global])
         (values `(begin ,expr* ... ,expr)
                 (apply set-union free-local free-local*)
                 (apply set-union free-global free-global*))]
        [(begin0 ,[expr free-local free-global]
                 ,[expr* free-local* free-global*] ...)
         (values `(begin0 ,expr ,expr* ...)
                 (apply set-union free-local free-local*)
                 (apply set-union free-global free-global*))]
        [(with-continuation-mark ,[expr1 free-local1 free-global1]
           ,[expr2 free-local2 free-global2]
           ,[expr3 free-local3 free-global3])
         (values `(with-continuation-mark ,expr1 ,expr2 ,expr3)
                 (set-union free-local1 free-local2 free-local3)
                 (set-union free-global1 free-global2 free-global3))]
        [(#%plain-app ,[expr free-local free-global]
                      ,[expr* free-local* free-global*] ...)
         (values `(#%plain-app ,expr ,expr* ...)
                 (apply set-union free-local free-local*)
                 (apply set-union free-global free-global*))])
  (TopLevelForm : top-level-form (e [env '()]) -> top-level-form ('() '())
                [(begin* ,[top-level-form free-local free-global] ...)
                 (values `(begin* ,top-level-form ...)
                         (apply set-union '() free-local)
                         (apply set-union '() free-global))]
                [(begin-for-syntax* ,[top-level-form free-local free-global])
                 (values `(begin-for-syntax* ,top-level-form ...)
                         (apply set-union '() free-local)
                         (apply set-union '() free-global))]
                [(#%expression ,[expr free-local free-global])
                 (values `(#%expression ,expr) free-local free-global)]
                [(define-syntaxes* (,v ...) ,[expr free-local free-global])
                 (values `(define-syntaxes* (,v ...) ,expr)
                         free-local
                         (set-union free-global v))])
  (ModuleLevelForm : module-level-form (e [env '()]) -> module-level-form ('() '()))
  (SubmoduleForm : submodule-form (e env) -> submodule-form ('() '()))
  (SyntaxLevelForm : syntax-level-form (e env) -> syntax-level-form ('() '()))
  (let-values ([(e* local* global*) (TopLevelForm e '())])
    `(program (,global* ...) ,e*)))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define z (make-variable 'z))
    (define w (make-variable 'w))
    (define f (make-variable 'f))
    (define-compiler-test current-target compilation-top
      (check-equal?
       (current-compile #'(lambda (x)
                            (lambda (y)
                              x)))
       `(program () (#%expression
                     (#%plain-lambda (,x)
                                     (free () ()
                                           (#%plain-lambda (,y)
                                                           (free (,x) ()
                                                                 ,x)))))))
      (check-equal?
       (current-compile #'(let ([x 5])
                            (lambda (y)
                              x)))
       `(program () (let ([,x '5])
                      (#%plain-lambda (,y)
                                      (free () ()
                                            '5)))))
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (lambda y (if x 4 5))))
       `(program (,x) (begin*
                       (define-values (,x) '5)
                       (#%expression
                        (#%plain-lambda ,y
                                        (free () (,x)
                                              (if ,x '4 '5)))))))
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (set! x 6)))
       `(program (,x) (begin*
                        (define-values (,x) '5)
                        (#%plain-app (primitive void)))))
      (check-equal?
       (current-compile #'(letrec ([f (lambda (x) x)])
                            (f 12)))
       `(program () '12))
      (check-equal?
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
      (check-equal?
       (current-compile #'(lambda (x)
                            (#%variable-reference)))
       `(program (#f) (#%expression
                       (#%plain-lambda (,x)
                                       (free () (#f)
                                             (#%variable-reference))))))
      (check-equal?
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
                            () ())))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (+ (set!-global v expr))))

(define-pass raise-toplevel-variables : current-source (e) -> current-target ()
  [CompilationTop : compilation-top (e [globals '()]) -> compilation-top ()
                  [(program (,binding ...) ,top-level-form)
                   `(program (,binding ...) ,(TopLevelForm top-level-form binding))]]
  (Expr : expr (e [globals '()]) -> expr ()
        [(set!-values (,v) ,[expr])
         (guard (set-member? globals v))
         `(set!-global ,v ,expr)]
        [,v (guard (set-member? globals v)) `(#%top . ,v)]
        [(#%variable-reference ,v)
         (guard (set-member? globals v))
         `(#%variable-reference-top ,v)])
  (FBody : free-body (e [globals '()]) -> free-body ())
  (Lambda : lambda (e [globals '()]) -> lambda ()
          #;[(#%plain-lambda (,id ...) ,[fbody])
           (displayln globals)
           `(#%plain-lambda (,id ...) ,fbody)])
  (TopLevelForm : top-level-form (e [globals '()]) -> top-level-form ()
                [,expr (Expr e globals)])
                #;[(#%expression ,[expr])
                 `(#%expression ,expr)]
  (ModuleLevelForm : module-level-form (e [globals '()]) -> module-level-form ())
  (SubmoduleForm : submodule-form (e [globals '()]) -> submodule-form ()
                 [(module ,id ,module-path (,v* ...) (,v** ...)
                          (,[raw-provide-spec] ...)
                          (,[raw-require-spec] ...)
                          (,module-level-form ...)
                          (,[syntax-level-form] ...)
                          (,[submodule-form1 (set-union globals v*) -> submodule-form] ...)
                          (,[submodule-form1* (set-union globals v*) -> submodule-form*] ...))
                  `(module ,id ,module-path (,v* ...) (,v** ...)
                           (,raw-provide-spec ...)
                           (,raw-require-spec ...)
                           (,(for/list ([mlf (in-list module-level-form)])
                               (ModuleLevelForm mlf v*)) ...)
                           (,syntax-level-form ...)
                           (,submodule-form ...)
                           (,submodule-form* ...))]))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define z (make-variable 'z))
    (define-compiler-test current-target compilation-top
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (set! x 6)
                            x))
       `(program (,x) (begin*
                        (define-values (,x) '5)
                        (set!-global ,x '6)
                        (#%top . ,x))))
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (#%variable-reference x)))
       `(program (,x) (begin*
                        (define-values (,x) '5)
                        (#%variable-reference-top ,x))))
      (check-equal?
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
      (check-equal?
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
                             (#%plain-app (primitive +) (#%top . ,x) (#%unbox ,y))))))))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (+ (closure v lambda))))

(define-pass closurify-letrec : current-source (e) -> current-target ()
  (definitions
    (define (remove-index l index)
      (append (take l index) (drop l (+ 1 index)))))
  (Formals : formals (e) -> formals ())
  [Expr : expr (e) -> expr ()
        [(letrec () ,[expr])
         expr]
        [(letrec ([,v (#%plain-lambda ,formals (free (,v1* ...) (,binding2* ...) ,expr*))] ...)
           ,expr)
         (define empty-index
           (for/fold ([acc #f])
                     ([i (in-list v1*)]
                      [iter (in-range (length v1*))])
             (if (null? i) iter acc)))
         (if empty-index
             `(let ([,(list-ref v empty-index)
                     (closure ,(list-ref v empty-index)
                              ,(Expr (with-output-language (current-source expr)
                                       `(#%plain-lambda ,(list-ref formals empty-index)
                                                        (free (,(list-ref v1* empty-index) ...)
                                                              (,(list-ref binding2* empty-index) ...)
                                                              ,(list-ref expr* empty-index))))))])
                ,(Expr (with-output-language (current-source expr)
                         `(letrec ([,(remove-index v empty-index)
                                    (#%plain-lambda ,(remove-index formals empty-index)
                                                    (free (,(remove-index v1* empty-index) ...)
                                                          (,(remove-index binding2* empty-index) ...)
                                                          ,(remove-index expr* empty-index)))]
                                   ...)
                            ,expr))))
             `(letrec ([,v (#%plain-lambda ,(map Formals formals)
                                            (free (,v1* ...) (,binding2* ...)
                                                  ,(map Expr expr*)))] ...)
                ,(Expr expr)))]])

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
     (define x (make-variable 'x))
     (define f (make-variable 'f))
     (define-compiler-test current-target compilation-top
       (check-equal?
        (current-compile #'(letrec ([f (lambda (x) x)])
                             (f 12)))
        `(program () '12))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (- (let ([v expr1] ...) expr)
           (undefined))
        (+ (let ([v expr1]) expr)
           (let-void (v ...) expr))))

(define-pass void-lets : current-source (e) -> current-target ()
  (Expr : expr (e) -> expr ()
        [(letrec ([,v ,[lambda]] ...)
           ,[expr])
         `(let-void (,v ...)
                    (letrec ([,v ,lambda] ...)
                      ,expr))]
        [(let ([,v ,[expr1]]) ,[expr])
         `(let ([,v ,expr1]) ,expr)]
        [(let ([,v (undefined)] ...) ,[expr])
         `(let-void (,v ...)
                    ,expr)]
        [(let ([,v ,[expr1]] ...) ,[expr])
         `(let-void (,v ...)
                    (begin
                      (set!-values (,v) ,expr1) ...
                      ,expr))]))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
    (define x (make-variable 'x))
    (define y (make-variable 'y))
    (define z (make-variable 'z))
    (define-compiler-test current-target compilation-top
      (check-equal?
       (current-compile #'(let ([x 1]) x))
       `(program () '1))
      (check-equal?
       (current-compile #'(let ([x 1]
                                [y 2])
                            (+ x y)))
       `(program () '3))
      (check-equal?
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
      (check-equal?
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
                                                             (#%unbox ,x) ,y))))))))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (- v
           (primitive id)
           (let-void (v ...) expr)
           (let ([v expr1]) expr)
           (letrec ([v lambda] ...)
             expr)
           (set!-boxes (v ...) expr)
           (set!-values (v ...) expr)
           (set!-global v expr)
           (#%box v)
           (#%unbox v)
           (#%top . v)
           (#%variable-reference)
           (#%variable-reference v)
           (#%variable-reference-top v))
        (+ binding
           (primitive eni)
           (let-void eni expr)
           (let-one expr1 expr)
           (letrec (lambda ...)
             expr)
           (set!-boxes eni1 eni2 expr)
           (set!-values eni1 eni2 expr)
           (set!-global eni1 eni2 expr)
           (#%box eni)
           (#%unbox eni)
           (#%top eni1 eni2)
           (#%variable-reference-none eni1 eni2)
           (#%variable-reference eni)
           (#%variable-reference-top eni)))
  (general-top-level-form (general-top-level-form)
                          (- (define-values (v ...) expr))
                          (+ (define-values (eni ...) expr)))
  (lambda (lambda)
    (- (#%plain-lambda formals fbody))
    (+ (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) expr)))
  (binding (binding)
           (+ eni
              (primitive eni)))
  (formals (formals)
           (- v
              (v ...)
              (v v* ... . v2)))
  (free-body (fbody)
             (- (free (v ...) (binding* ...) expr))))

(define-pass debruijn-indices : current-source (e) -> current-target ()
  (definitions
    (define-syntax-rule (formals->identifiers* fmls)
      (formals->identifiers current-source fmls))
    (define-syntax-rule (formals-rest?* fmls)
      (formals-rest? current-source fmls))
    (define (extend-env env start ids)
      (for/fold ([env env] [ref start])
                ([i (in-list ids)])
        (values (dict-set env i (+ ref 1)) (+ ref 1))))
    (define (lookup-env env id)
      (dict-ref env id))
    (define (make-global-env ids)
      (for/fold ([env (hash)])
                ([i (in-list ids)] [index (in-range (length ids))])
        (hash-set env i index)))
    (define ((var->index env frame global-env) id)
      (if (dict-has-key? env id)
          (- frame (lookup-env env id))
          (error "Variable not bound")))
    ;; Convert a list of identifiers to it's range and offset
    ;; (valid because list ids should be consecutive
    ;; (list symbol) -> (values exact-nonnegative-integer exact-nonnegative-integer)
    (define (ids->range env frame ids)
      (define indices (map (var->index env frame '()) ids)) ;; TODO '() should be global env
      (values (length indices) (car indices))))
  (Lambda : lambda (e [env '()] [frame 0] [global-env '()] [prefix-frame 0]) -> lambda ()
          [(#%plain-lambda ,formals
                           (free (,v2 ...) (,binding3 ...)
                                 ,expr))
           (define params (formals->identifiers* formals))
           (define rest? (formals-rest?* formals))
           (define-values (env* frame*) (extend-env env frame (reverse (append v2 params))))
           (define frame** (if (= (length binding3) 0) frame* (+ frame* 1)))
           (define locals (map (var->index env frame global-env) v2))
           `(#%plain-lambda ,(length params)
                            ,rest?
                            (,(if (= (length binding3) 0)
                                  locals
                                  (cons (- frame prefix-frame) locals)) ...)
                            (,(map ((curry dict-ref) global-env) binding3) ...)
                            ,(Expr expr env* frame** global-env frame**))])
  (Expr : expr (e [env '()] [frame 0] [global-env '()] [prefix-frame 0]) -> expr ()
        [,v ((var->index env frame global-env) v)]
        [(primitive ,id) `(primitive ,(dict-ref primitive-table* id))]
        [(#%box ,v) `(#%box ,((var->index env frame global-env) v))]
        [(#%unbox ,v) `(#%unbox ,((var->index env frame global-env) v))]
        [(set!-values (,v ...) ,[expr])
         (define-values (count offset) (ids->range env frame v))
         `(set!-values ,count ,offset ,expr)]
        [(set!-boxes (,v ...) ,[expr])
         (define-values (count offset) (ids->range env frame v))
         `(set!-boxes ,count ,offset ,expr)]
        [(set!-global ,v ,[expr])
         `(set!-global ,(- frame prefix-frame) ,(dict-ref global-env v) ,expr)]
        [(#%top . ,v) `(#%top ,(- frame prefix-frame) ,(dict-ref global-env v))]
        [(#%variable-reference)
         `(#%variable-reference-none ,(- frame prefix-frame) ,(hash-ref global-env #f))]
        [(#%variable-reference-top ,v) `(#%variable-reference-top 0)] ;; TODO: Global vars
        [(#%variable-reference ,v) `(#%variable-reference ,((var->index env frame) v))]
        [(let ([,v ,expr1])
           ,expr)
         (define-values (env* frame*) (extend-env env frame (list v)))
         `(let-one ,(Expr expr1 env (+ frame 1) global-env prefix-frame)
                   ,(Expr expr env* frame* global-env prefix-frame))]
        [(let-void (,v ...)
                   ,expr)
         (define-values (env* frame*) (extend-env env frame (reverse v)))
         `(let-void ,(length v)
                    ,(Expr expr env* frame* global-env prefix-frame))]
        [(letrec ([,v ,[lambda]] ...)
           ,[expr])
         `(letrec (,lambda ...)
            ,expr)]
        [(#%plain-app ,expr ,expr* ...)
         (define expr1 (Expr expr env (+ frame (length expr*)) global-env prefix-frame))
         (define expr*1 (map (lambda (e)
                               (Expr e env (+ frame (length expr*)) global-env prefix-frame))
                             expr*))
         `(#%plain-app ,expr1 ,expr*1 ...)])
  (GeneralTopLevelForm : general-top-level-form (e [env '()] [frame 0] [global-env '()])
                       -> general-top-level-form ()
                       [(define-values (,v ...) ,[expr])
                        `(define-values (,(map ((curry dict-ref) global-env) v) ...) ,expr)])
  (TopLevelForm : top-level-form (e [env '()] [frame 0] [global-env '()] [prefix-frame 0])
                -> top-level-form ()
                #;[(begin* ,top-level-form ...)
                 (displayln "got here")
                 `(begin* ,(map TopLevelForm top-level-form) ...)])
  (SubmoduleForm : submodule-form (e [env '()] [frame 0] [global-env '()] [prefix-frame '()])
                 -> submodule-form ()
                 [(module ,id ,module-path (,v* ...) (,v** ...)
                          (,[raw-provide-spec] ...)
                          (,[raw-require-spec] ...)
                          (,module-level-form ...)
                          (,[syntax-level-form] ...)
                          (,submodule-form ...)
                          (,submodule-form* ...))
                  (define global-env* (hash-union global-env (make-global-env v*)
                                                  #:combine (lambda (v1 v2) v2)))
                  `(module ,id ,module-path (,v* ...) (,v** ...)
                           (,raw-provide-spec ...)
                           (,raw-require-spec ...)
                           (,(for/list ([mlf (in-list module-level-form)])
                               (ModuleLevelForm mlf env frame global-env* prefix-frame)) ...)
                           (,syntax-level-form ...)
                           (,(for/list ([sf (in-list submodule-form)])
                               (SubmoduleForm sf env frame global-env* prefix-frame)) ...)
                           (,(for/list ([sf (in-list submodule-form*)])
                               (SubmoduleForm sf env frame global-env* prefix-frame)) ...))])
  (ModuleLevelForm : module-level-form (e [env '()] [frame 0] [global-env '()] [prefix-frame 0])
                   -> module-level-form ())
  (CompilationTop : compilation-top (e) -> compilation-top ()
                  [(program (,binding ...) ,top-level-form)
                   `(program (,binding ...)
                             ,(TopLevelForm top-level-form '() 0 (make-global-env binding) 0))]))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (block
     (define x* (make-variable 'x))
    (define-compiler-test current-target compilation-top
      (check-equal?
       (current-compile #'(lambda (x) x))
       `(program () (#%expression (#%plain-lambda 1 #f () () 0))))
      (check-equal?
       (current-compile #'(let ([x 5])
                       (lambda (y . z) x)))
       `(program () (let-one '5 (#%plain-lambda 2 #t () () '5))))
      (check-equal?
       (current-compile #'(let ([x 5]
                           [y 6])
                       (+ x y)))
       `(program () '11))
      (check-equal?
       (current-compile #'(begin
                       (define x 5)
                       (+ x 5)))
       `(program (,x*) (begin*
                       (define-values (0) '5)
                       (#%plain-app (primitive ,(dict-ref primitive-table* '+)) (#%top 2 0) '5))))
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (lambda (y)
                              y x)))
       `(program (,x*) (begin*
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
                      (#%top 0 0))))))))

;; ===================================================================================================

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (entry compilation-top)
  (compilation-top (compilation-top)
                   (- (program (binding ...) top-level-form))
                   (+ (program eni (binding ...) top-level-form)))
  (submodule-form (submodule-form)
                  (- (module id module-path (v* ...) (v** ...)
                             (raw-provide-spec ...)
                             (raw-require-spec ...)
                             (module-level-form ...)
                             (syntax-level-form ...)
                             (submodule-form ...)
                             (submodule-form* ...)))
                  (+ (module id module-path (v* ...) (v** ...) eni
                             (raw-provide-spec ...)
                             (raw-require-spec ...)
                             (module-level-form ...)
                             (syntax-level-form ...)
                             (submodule-form ...)
                             (submodule-form* ...))))
  (lambda (lambda)
    (- (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) expr))
    (+ (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) eni4 expr))))

(define-pass find-let-depth : current-source (e) -> current-target ()
  (Lambda : lambda (e) -> lambda (0)
          [(#%plain-lambda ,eni1 ,boolean (,[binding2] ...) (,[binding3] ...) ,[expr depth])
           (define depth* (+ eni1 (length binding2) depth))
           (values `(#%plain-lambda ,eni1 ,boolean (,binding2 ...) (,binding3 ...)
                                    ,(+ 5
                                        eni1
                                        (if boolean 1 0)
                                        (length binding2)
                                        (length binding3)
                                        depth*)
                                    ,expr)
                   1)])
  [Binding : binding (e) -> binding (0)]
  (Expr : expr (e) -> expr (0)
        [(closure ,v ,[lambda depth])
         (values `(closure ,v ,lambda) depth)]
        [(let-void ,eni ,[expr depth])
         (values `(let-void ,eni ,expr)
                 (+ eni depth))]
        [(let-one ,[expr depth] ,[expr1 depth1])
         (values `(let-one ,expr ,expr1)
                 (+ 1 (max depth depth1)))]
        [(letrec (,[lambda depth*] ...) ,[expr depth])
         (values `(letrec (,lambda ...) ,expr)
                 (+ depth (length lambda) (apply max 0 depth*)))]
        ;; Everything below this line is boilerplate (except the main body)
        [(set!-values ,eni1 ,eni2 ,[expr depth])
         (values `(set!-values ,eni1 ,eni2 ,expr) depth)]
        [(set!-boxes ,eni1 ,eni2 ,[expr depth])
         (values `(set!-boxes ,eni1 ,eni2 ,expr) depth)]
        [(set!-global ,eni1 ,eni2 ,[expr depth])
         (values `(set!-global ,eni1 ,eni2 ,expr) depth)]
        [(case-lambda ,[lambda depth] ...)
         (values `(case-lambda ,lambda ...)
                 (apply max 0 depth))]
        [(if ,[expr1 depth1] ,[expr2 depth2] ,[expr3 depth3])
         (values `(if ,expr1 ,expr2 ,expr3)
                 (max depth1 depth2 depth3))]
        [(begin ,[expr* depth*] ... ,[expr depth])
         (values `(begin ,expr* ... ,expr)
                 (apply max depth depth*))]
        [(begin0 ,[expr depth] ,[expr* depth*] ...)
         (values `(begin0 ,expr ,expr* ...)
                 (apply max depth depth*))]
        [(with-continuation-mark ,[expr1 depth1] ,[expr2 depth2] ,[expr3 depth3])
         (values `(with-continuation-mark ,expr1 ,expr2 ,expr3)
                 (max depth1 depth2 depth3))]
        [(#%plain-app ,[expr depth] ,[expr* depth*] ...)
         (values `(#%plain-app ,expr ,expr* ...)
                 (+ (length depth*) (apply max depth depth*)))])
  (TopLevelForm : top-level-form (e) -> top-level-form (0)
                [,submodule-form (SubmoduleForm submodule-form)]
                [(#%expression ,[expr depth])
                 (values `(#%expression ,expr) depth)]
                [(begin* ,[top-level-form depth] ...)
                 (values `(begin* ,top-level-form ...)
                         (apply max 0 depth))]
                [(begin-for-syntax* ,[top-level-form depth] ...)
                 (values `(begin-for-syntax* ,top-level-form ...)
                         (apply max 0 depth))]
                [(define-syntaxes* (,v ...) ,[expr depth])
                 (values `(define-syntaxes* (,v ...) ,expr) depth)])
  (ModuleLevelForm : module-level-form (e) -> module-level-form (0))
  (SubmoduleForm : submodule-form (e) -> submodule-form (0)
                 [(module ,id ,module-path (,v* ...) (,v** ...)
                          (,[raw-provide-spec] ...)
                          (,[raw-require-spec] ...)
                          (,[module-level-form depth] ...)
                          (,[syntax-level-form] ...)
                          (,[submodule-form** depth**] ...)
                          (,[submodule-form* depth*] ...))
                  (values `(module ,id ,module-path (,v* ...) (,v** ...) ,(apply max 0 depth)
                                   (,raw-provide-spec ...)
                                   (,raw-require-spec ...)
                                   (,module-level-form ...)
                                   (,syntax-level-form ...)
                                   (,submodule-form** ...)
                                   (,submodule-form* ...))
                          0)])
  (GeneralTopLevelForm : general-top-level-form (e) -> general-top-level-form (0)
                       [(define-values (,eni ...) ,[expr depth])
                        (values `(define-values (,eni ...) ,expr) depth)])
  (CompilationTop : compilation-top (e) -> compilation-top ()
                  [(program (,binding ...) ,[top-level-form depth])
                   `(program ,depth (,binding ...) ,top-level-form)]))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target compilation-top
      (check-equal?
       (current-compile #'(lambda (x) (let ([y 5]) (+ x y))))
       `(program 1 () (#%expression
                       (#%plain-lambda 1 #f () () 10
                                       (let-one '5 (#%plain-app
                                                    (primitive ,(dict-ref primitive-table* '+))
                                                    3 '5))))))
      (check-equal?
       (current-compile #'(if (= 5 6)
                              (let ([x '5]
                                    [y '6])
                                y)
                              (let ([x '6])
                                x)))
       `(program 0 () '6)))))

(define tmp-prefix
  (zo:prefix 0 '() '() 'missing))

(update-current-languages! L)

(define-pass generate-zo-structs : current-source (e) -> * ()
  (definitions
    (define zo-void
      (zo:primval 35)))
  (CompilationTop : compilation-top (e) -> * ()
                  [(program ,eni (,binding ...) ,top-level-form)
                   (zo:compilation-top eni
                                       (hash)
                                       (zo:prefix
                                        0
                                        (map (lambda (x) (and x (variable-name x))) binding)
                                        '()
                                        'missing)
                                       (TopLevelForm top-level-form))])
  (TopLevelForm : top-level-form (e) -> * ()
                [(#%expression ,expr)
                 (Expr expr)]
                [(begin* ,top-level-form ...)
                 (zo:splice (map TopLevelForm top-level-form))]
                [(#%require ,raw-require-spec ...)
                 (void)]
                [(begin-for-syntax* ,top-level-form ...)
                 (void)]
                [(define-syntaxes* (,v ...) ,expr)
                 (void)])
  (ModuleLevelForm : module-level-form (e) -> * ()
                   [(#%declare ,declaration-keyword ...)
                    (void)])
  (SubmoduleForm : submodule-form (e) -> * ()
                 [(module ,id ,module-path (,v* ...) (,v** ...) ,eni
                          (,raw-provide-spec ...)
                          (,raw-require-spec ...)
                          (,module-level-form ...)
                          (,syntax-level-form ...)
                          (,submodule-form ...)
                          (,submodule-form* ...))
                  (zo:mod id
                          id
                          (module-path-index-join #f #f #f)
                          (zo:prefix 0 (map variable-name v*) '() 'missing)
                          (map RawProvideSpec raw-provide-spec)
                          (map RawRequireSpec raw-require-spec)
                          (map ModuleLevelForm module-level-form)
                          '()
                          '()
                          eni
                          (zo:toplevel 0 0 #f #f)
                          #f
                          #f
                          (hash)
                          '()
                          (map SubmoduleForm submodule-form)
                          (map SubmoduleForm submodule-form*))])
  (GeneralTopLevelForm : general-top-level-form (e) -> * ()
                       [(define-values (,eni ...) ,expr)
                        (zo:def-values (for/list ([i (in-list eni)])
                                         (zo:toplevel 0 i #f #f))
                                       (Expr expr))])
  (Bidnding : binding (e) -> * ()
            [,false false]
            [,v v]
            [,eni eni]
            [(primitive ,eni)
             (zo:primval eni)])
  (Expr : expr (e) -> * ()
        [,eni (zo:localref #f eni #f #f #f)]
        [(closure ,v ,lambda) (zo:closure (Lambda lambda) (variable-name v))]
        [(primitive ,eni)
         (zo:primval eni)]
        [(#%top ,eni1 ,eni2) (zo:toplevel eni1 eni2 #f #f)]
        [(#%unbox ,eni)
         (zo:localref #t eni #f #f #f)]
        [(#%box ,eni)
         (zo:boxenv eni zo-void)]
        [(begin
           (set!-values ,eni1 ,eni2 (#%box ,eni3))
           ,expr)
         (guard (and (= eni2 eni3) (= eni1 1)))
         (zo:boxenv eni2 (Expr expr))]
        [(begin
           (set!-boxes ,eni1 ,eni2 ,expr)
           ,expr*)
         (zo:install-value eni1 eni2 #t (Expr expr) (Expr expr*))]
        [(set!-values ,eni1 ,eni2 ,expr)
         (zo:install-value eni1 eni2 #f (Expr expr) zo-void)]
        [(set!-boxes ,eni1 ,eni2 ,expr)
         (zo:install-value eni1 eni2 #t (Expr expr) zo-void)]
        [(set!-global ,eni1 ,eni2 ,expr)
         (zo:assign (zo:toplevel eni1 eni2 #f #f) (Expr expr) #f)]
        [(letrec (,lambda ...) ,expr)
         (zo:let-rec (map Lambda lambda) (Expr expr))]
        [(let-one ,expr1 ,expr)
         (zo:let-one (Expr expr1) (Expr expr) #f #f)]
        [(let-void ,eni ,expr)
         (zo:let-void eni #f (Expr expr))]
        [(case-lambda ,lambda ...)
         (zo:case-lam #() (map Lambda lambda))]
        [(if ,expr1 ,expr2 ,expr3)
         (zo:branch (Expr expr1) (Expr expr2) (Expr expr3))]
        [(begin ,expr* ... ,expr)
         (zo:seq (append (map Expr expr*)
                         (list (Expr expr))))]
        [(begin0 ,expr ,expr* ...)
         (zo:beg0 (cons (Expr expr) (map Expr expr*)))]
        [(quote ,datum) datum]
        [(quote-syntax ,datum)
         (void)]
        [(with-continuation-mark ,expr1 ,expr2 ,expr3)
         (zo:with-cont-mark (Expr expr1) (Expr expr2) (Expr expr3))]
        [(#%plain-app ,expr ,expr* ...)
         (zo:application (Expr expr) (map Expr expr*))]
        [(#%variable-reference-top ,eni)
         (zo:varref (zo:toplevel 0 0 #f #f) (zo:toplevel 0 0 #f #f))]
        [(#%variable-reference ,eni)
         (zo:varref (zo:toplevel 0 0 #f #f) (zo:toplevel 0 0 #f #f))]
        [(#%variable-reference-none ,eni1 ,eni2)
         (zo:varref (zo:toplevel eni1 eni2 #f #f) (zo:toplevel eni1 eni2 #f #f))])
  (Lambda : lambda (e) -> * ()
          [(#%plain-lambda ,eni ,boolean (,binding2 ...) (,binding3 ...) ,eni4 ,expr)
           (zo:lam (gensym)
                   null
                   (if boolean (- eni 1) eni)
                   (for/list ([i (in-range (if boolean (- eni 1) eni))])
                     'val)
                   boolean
                   (list->vector binding2)
                   (map (lambda (x) 'val/ref) binding2)
                   (if (null? binding3) #f (list->set binding3))
                   eni4
                   (Expr expr))])
  (RawProvideSpec : raw-provide-spec (e) -> * ()
                  [(for-meta* ,phase-level ,phaseless-prov-spec ...)
                   (void)])
  (PhaselessProvSpec : phaseless-prov-spec (e) -> * ()
                     [,v (void)]
                     [(rename* ,v1 ,v2)
                      (void)]
                     [(protect ,v)
                      (void)]
                     [(protect-rename* ,v1 ,v2)
                      (void)])
  (RawRequireSpec : raw-require-spec (e) -> * ()
                  [(for-meta ,phase-level ,phaseless-req-spec ...)
                   (void)])
  (PhaselessReqSpec : phaseless-req-spec (e) -> * ()
                    [(rename ,raw-module-path ,v1 ,v2)
                     (void)])
  (RawModulePath : raw-module-path (e) -> * ()
                 [(submod ,raw-root-module-path ,id ...)
                  (void)])
  (RawRootModulePath : raw-root-module-path (e) -> * ()
                     [,id (void)]
                     [,string (void)]
                     [(quote* ,id) (void)]
                     [(lib ,string ...) (void)]
                     [(file ,string) (void)]
                     [(planet ,string1
                              (,string2 ,string3 ,string* ...))
                      (void)]
                     [,path (void)]))

(module+ test
  (parameterize ({current-environment-variables
                  (environment-variables-copy (current-environment-variables))})
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
             (compile-compare #'((lambda x (car x)) '(84 91 514)))
             (compile-compare #'(let ([x (lambda () 42)])
                                  (x)))
             (compile-compare #'(let ([x 5])
                                  (set! x 6)
                                  x))
             (compile-compare #'(letrec ([f (lambda (x) x)])
                                  (f 12)))
             (compile-compare #'(letrec ([fact (lambda (x)
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
             (compile-compare #'(begin
                                  (module foo racket
                                    (#%plain-module-begin
                                     (provide x)
                                     (define x 481)))
                                  (require 'foo)
                                  x)))
           all-compiler-tests))))

;; ===================================================================================================

(begin-for-syntax
  (define-syntax-class pass
    (pattern name:id
             #:attr [components 1] '())
    (pattern (name:id components:id ...))))

;; Expand syntax fully, even at the top level
(define (expand-syntax* stx)
  (parameterize ([current-namespace (make-base-namespace)])
    (namespace-require 'racket/undefined)
    (expand-syntax-top-level-with-compile-time-evals
     (namespace-syntax-introduce stx))))

(define (bytes->compiled-expression zo)
  (parameterize ([read-accept-compiled #t])
    (with-input-from-bytes zo
      (lambda () (read)))))

(define-compiler-component closure-conversion)
(define-compiler-component optimizer)
(define-compiler-component mutable-variable-elimination)
(define-compiler-component debruijn)
(define-compiler-component parse)
(define-compiler-component generate-bytecode)
(define-compiler-component modules)

(define-compiler compile
  expand-syntax*
  (parse-and-rename parse)
  (lift-submodules modules)
  (lift-require-provide modules)
  (lift-syntax-sequences modules)
  (identify-module-variables modules)
  (scrub-require-provide modules)
  (make-begin-explicit parse)
  (identify-assigned-variables mutable-variable-elimination)
  purify-letrec
  (inline-expressions optimizer)
  ;(convert-assignments mutable-variable-elimination)
  ;(uncover-free closure-conversion)
  ;raise-toplevel-variables
  ;closurify-letrec
  ;void-lets
  ;(debruijn-indices debruijn)
  ;(find-let-depth debruijn)
  ;(generate-zo-structs generate-bytecode)
  ;(zo-marshal generate-bytecode)
  ;bytes->compiled-expression
  )

(module+ test
  (run-all-compiler-tests))
