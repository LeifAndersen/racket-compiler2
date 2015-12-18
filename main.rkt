#lang racket/base

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
         rackunit
         (prefix-in zo: compiler/zo-structs)
         (rename-in racket/base
                    [compile base:compile])
         (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     racket/stxparam
                     racket/stxparam-exptime))

(require/expose compiler/decompile (primitive-table))

(define primitive-table*
  (for/hash ([(k v) (in-hash primitive-table)])
    (values v k)))

(define (maybe-module-path? m)
  (or (module-path? m) (not m)))

(define (raw-provide-spec? rps)
  #t)

(define (raw-require-spec? rrs)
  #t)

(define (declaration-keyword? dk)
  #t)

(define (datum? d)
  #t)

(define primitive-module
  (car (identifier-binding #'+)))

(define (primitive-identifier? identifier)
  (define binding (identifier-binding identifier))
  (and (list? binding) (eq? (car binding) primitive-module)))

(define (primitive->symbol identifier)
  (define binding (identifier-binding identifier))
  (cadr binding))

(define id? symbol?)

(define fresh (make-parameter gensym))

(module+ test
  (require rackunit
           rackunit/text-ui
           (submod ".." test-compiler-bindings))

  (provide (all-defined-out))

  ; Counter for a version of fresh that is deterministic (for tests)
  (define deterministic-fresh/count 0)
  (define (deterministic-fresh symb)
    (set! deterministic-fresh/count (+ deterministic-fresh/count 1))
    (string->symbol (format "~a.~a" symb deterministic-fresh/count)))

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
                     #:before (lambda () (set! deterministic-fresh/count 0))
                     (parameterize ([fresh deterministic-fresh])
                       (test-case (format "Test case for: ~a" '#,(syntax->datum #'lang))
                         (set! deterministic-fresh/count 0)
                         body) ...)))))
           (set! all-compiler-tests (cons name all-compiler-tests)))]))

  ;; Run all tests defined with define-compiler-test
  (define-syntax-rule (run-all-compiler-tests)
    (let ()
      (define res (map run-tests all-compiler-tests))
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
                (eval (bytes->compiled-expression (compile expression)))
                (eval expression))))]))

  (define (bytes->compiled-expression zo)
    (parameterize ([read-accept-compiled #t])
      (with-input-from-bytes zo
        (lambda () (read)))))

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
                 [,id                         (list id)]
                 [(,id (... ...))             id]
                 [(,id ,id* (... ...) . ,id2) (set-union (list id id2) id*)]))

; lang formals -> boolean
(define-syntax-rule (formals-rest? lang fmls)
  (nanopass-case (lang formals) fmls
                 [,id                         #t]
                 [(,id (... ...))             #f]
                 [(,id ,id* (... ...) . ,id2) #t]))

(begin-for-syntax
  (struct language-box (language)
    #:mutable
    #:transparent
    #:property prop:rename-transformer
    (lambda (inst)
      (syntax-property (language-box-language inst)
                       'not-free-identifier=?
                       #t))))
(define-syntax (set-language! stx)
  (syntax-parse stx
    [(_ box language)
     #'(begin-for-syntax
         (define-values (val trans) (syntax-local-value/immediate #'box))
         (set-language-box-language! val #'language))]))

(define-syntax (update-current-languages! stx)
  (syntax-parse stx
    [(_ language:id)
     #`(begin-for-syntax
         (define-values (val trans) (syntax-local-value/immediate #'current-source-top))
         (define-values (val* trans*) (syntax-local-value/immediate #'current-target-top))
         (set! current-language-number (+ current-language-number 1))
         (set-language-box-language! val #'#,(format-id stx "~a~a" #'language
                                                      (if (= current-language-number 0)
                                                          "src"
                                                          current-language-number)))
         (set-language-box-language! val* #'#,(format-id stx "~a~a" #'language
                                                       (if (= (+ current-language-number 1) 0)
                                                           "src"
                                                           (+ current-language-number 1)))))
     #;#`(begin
         (set-language! current-source-top #,(format-id stx "~a~a" #'language
                                                        (if (= current-language-number 0)
                                                            "src"
                                                            current-language-number)))
         (set-language! current-target-top #,(format-id stx "~a~a" #'language
                                                        (if (= (+ current-language-number 1) 0)
                                                            "src"
                                                            (+ current-language-number)))))]))

(define-syntax current-source-top (language-box #'Lsrc))
(define-syntax current-target-top (language-box #'Lsrc))
(define-for-syntax current-language-number 0)

(define-syntax (define-language stx)
  (syntax-parse stx
    [(_ name:id rest ...)
     #:with current-source (format-id stx "current-source")
     #:with current-target (format-id stx "current-target")
     #`(splicing-let-syntax ([current-source (syntax-local-value #'current-source-top (lambda () #f))]
                             [current-target (syntax-local-value #'current-target-top (lambda () #f))])
         #,(cond [(free-identifier=? #'name #'current-target)
                  (define-values (val trans) (syntax-local-value/immediate #'current-target-top))
                  (with-syntax ([new-name (format-id stx "~a" trans)])
                    #'(nanopass:define-language new-name rest ...))]
                 [(free-identifier=? #'name #'current-source)
                  (define-values (val trans) (syntax-local-value/immediate #'current-source-top))
                  (with-syntax ([new-name (format-id stx "~a" trans)])
                    #'(nanopass:define-language new-name rest ...))]
                 [else
                  #'(nanopass:define-language name rest ...)]))]))

(define-syntax (define-pass stx)
  (syntax-parse stx
    [(_ rest ...)
     #:with current-source (format-id stx "current-source")
     #:with current-target (format-id stx "current-target")
     #'(splicing-let-syntax ([current-source (syntax-local-value #'current-source-top (lambda () #f))]
                             [current-target (syntax-local-value #'current-target-top (lambda () #f))])
         (nanopass:define-pass rest ...))]))

(define-language current-target
  (terminals
   (raw-require-spec (raw-require-spec))
   (raw-provide-spec (raw-provide-spec))
   (maybe-module-path (maybe-module-path module-path))
   (declaration-keyword (declaration-keyword))
   (datum (datum))
   (id (id))
   (false (false)))
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
                          (define-values (id ...) expr)
                          (define-syntaxes (id ...) expr)
                          (#%require raw-require-spec ...))
  (expr (expr)
        id
        (primitive id)
        (#%plain-lambda formals expr* ... expr)
        (case-lambda (formals expr* ... expr) ...)
        (if expr1 expr2 expr3)
        (begin expr* ... expr)
        (begin0 expr* ... expr)
        (let-values ([(id ...) expr1] ...)
          expr* ... expr)
        (letrec-values ([(id ...) expr1] ...)
          expr* ... expr)
        (set! id expr)
        (quote datum)
        (quote-syntax datum)
        (with-continuation-mark expr1 expr2 expr3)
        (#%plain-app expr expr* ...)
        (#%top . id)
        (#%variable-reference id)
        (#%variable-reference-top id)
        (#%variable-reference))
  (formals (formals)
           id
           (id ...)
           (id id* ... . id2)))

;; Parse and alpha-rename expanded program
(define-pass parse-and-rename : * (form) -> current-target ()
  (definitions
    (define initial-env (hash))
    (define (extend-env env vars)
      (for/fold ([acc env])
                ([var (in-list vars)])
        (define var* (syntax->datum var))
        (dict-set acc var* ((fresh) var*))))
    (define ((lookup-env env) var)
      (dict-ref env (syntax->datum var)
                (syntax->datum var))))

  (parse-top : * (form env) -> top-level-form ()
             (syntax-parse form
               #:literals (#%expression module #%plain-module-begin begin begin-for-syntax)
               [(#%expression body)
                `(#%expression ,(parse-expr #'body env))]
               [(module id:id path
                  (#%plain-module-begin body ...))
                (define env* (extend-env env (list #'id)))
                `(module ,(syntax->datum #'id) ,(syntax->datum #'path)
                   (,(for/list ([i (in-list (syntax->list #'(body ...)))])
                      (parse-mod i env*)) ...))]
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
                `(#%provide ,(syntax->list #'(spec ...)) ...)]
               [(begin-for-syntax body ...)
                `(begin-for-syntax ,(for/list ([i (in-list (syntax->list #'(body ...)))])
                                      (parse-mod (syntax-shift-phase-level i -1) env)) ...)]
               [(#%declare keyword ...)
                `(#%declare ,(syntax->list #'(keyword ...)) ...)]
               [(module id:id path
                  (#%plain-module-begin body ...))
                (define env* (extend-env env (list #'id)))
                `(submodule ,(syntax->datum #'id) ,(syntax->datum #'path)
                            (,(for/list ([i (in-list (syntax->list #'(body ...)))])
                                (parse-mod i env*)) ...))]
               [(module* id:id path
                  (#%plain-module-begin body ...))
                (define env* (extend-env env (list #'id)))
                `(submodule* ,(syntax->datum #'id) ,(syntax->datum #'path)
                             (,(for/list ([i (in-list (syntax->list #'(body ...)))])
                                 (parse-mod i env*)) ...))]
               [(module* id:id path
                  (#%plain-module-begin body ...))
                (define env* (extend-env env (list #'id)))
                `(submodule* ,(syntax->datum #'id)
                             (,(for/list ([i (in-list (syntax->list #'(body ...)))])
                                 (parse-mod i env*)) ...))]
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
                   ,(parse-expr #'body env))]
               [(#%require spec ...)
                `(#%require ,(syntax->list #'(spec ...)))]
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
                [(begin0 body* ... body)
                 `(begin0 ,(for/list ([b (in-list (syntax->list #'(body* ...)))])
                             (parse-expr b env)) ...
                          ,(parse-expr #'body env))]
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
                 `(#%top . ,(syntax->datum #'id))]
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

  (parse-top form initial-env))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target top-level-form
      (check-equal?
       (current-compile #'(lambda (x) x))
       `(#%expression (#%plain-lambda (x.1) x.1)))
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
          (define-values (x) '5)))
      (check-equal?
       (current-compile #'(module test racket
                            (#%plain-module-begin
                             (begin-for-syntax
                               (define x 5)))))
       `(module test racket
          ((begin-for-syntax
             (define-values (x) '5)))))
      (check-equal?
       (current-compile #'(lambda (a b . c)
                            (apply + a b c)))
       `(#%expression (#%plain-lambda (a.1 b.3 . c.2)
                                      (#%plain-app (primitive apply) (primitive +) a.1 b.3 c.2)))))))

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
                  (values `(#%plain-app void)
                          (list (with-output-language (L1 submodule-form)
                                  `(module ,id ,module-path
                                     (,module-level-form ...)
                                     (,(append* pre) ...)
                                     (,(append* post) ...))))
                          null)]
                 [(submodule* ,id ,module-path
                              (,[module-level-form pre post] ...))
                  (values `(#%plain-app void)
                          null
                          (list (with-output-language (L1 submodule-form)
                                  `(module ,id ,module-path
                                     (,module-level-form ...)
                                     (,(append* pre) ...)
                                     (,(append* post) ...)))))]
                 [(submodule* ,id
                              (,[module-level-form pre post] ...))
                  (values `(#%plain-app void)
                          null
                          (list (with-output-language (L1 submodule-form)
                                  `(module ,id #f
                                     (,module-level-form ...)
                                     (,(append* pre) ...)
                                     (,(append* post) ...)))))])
  (ModuleLevelForm : module-level-form (e) -> module-level-form (#f #f)
                   [(begin-for-syntax ,[module-level-form pre post] ...)
                    (values `(begin-for-syntax ,module-level-form ...)
                            (append* pre)
                            (append* post))])
  (GeneralTopLevelForm : general-top-level-form (e) -> general-top-level-form ('() '()))
  (Expr : expr (e) -> expr ('() '())))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
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
          ((#%plain-app void)
           (define-values (x) '5)
           (#%plain-app void))
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
             (define-values (x) '6)
             (#%plain-app void)))
          ()
          ((module test #f
             (x) () ()))))
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
          ((#%plain-app void)
           (#%plain-app void)
           (define-values (x) '5)
           x)
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
          ((#%plain-app void))
          ((module bar racket/base
             ((#%plain-app void))
             ((module baz racket/base
                ('42)
                () ()))
             ()))
          ())))))

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (lambda (lambda)
    (+ (#%plain-lambda formals expr)))
  (expr (expr)
        (- (#%plain-lambda formals expr* ... expr)
           (case-lambda (formals expr* ... expr) ...)
           (let-values ([(id ...) expr1] ...)
             expr* ... expr)
           (letrec-values ([(id ...) expr1] ...)
             expr* ... expr))
        (+ lambda
           (case-lambda lambda ...)
           (let-values ([(id ...) expr1] ...)
             expr)
           (letrec-values ([(id ...) expr1] ...)
             expr))))

(define-pass make-begin-explicit : current-source (e) -> current-target ()
  (Expr : expr (e) -> expr ()
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
        [(let-values ([(,id ...) ,[expr1]] ...)
           ,[expr*] ... ,[expr])
         (if (= (length expr*) 0)
             `(let-values ([(,id ...) ,expr1] ...)
                ,expr)
             `(let-values ([(,id ...) ,expr1] ...)
                (begin ,expr* ... ,expr)))]
        [(letrec-values ([(,id ...) ,[expr1]] ...)
           ,[expr*] ... ,[expr])
         (if (= (length expr*) 0)
             `(letrec-values ([(,id ...) ,expr1] ...)
                ,expr)
             `(letrec-values ([(,id ...) ,expr1] ...)
                (begin ,expr* ... ,expr)))]))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target top-level-form
      (check-equal?
       (current-compile #'(lambda (x) x x))
       `(#%expression (#%plain-lambda (x.1) (begin x.1 x.1))))
      (check-equal?
       (current-compile #'(case-lambda [(x) (+ x 1) (begin0 x (set! x 42))]))
       `(#%plain-lambda (x.1)
                        (begin (#%plain-app (primitive +) x.1 '1)
                               (begin0 x.1
                                 (set! x.1 '42)))))
      (check-equal?
       (current-compile #'(case-lambda [(x) (+ x 1)]
                                       [(x y) x (+ x y)]))
       `(case-lambda (#%plain-lambda (x.1) (#%plain-app (primitive +) x.1 '1))
                     (#%plain-lambda (x.2 y.3) (begin x.2 (#%plain-app (primitive +) x.2 y.3)))))
      (check-equal?
       (current-compile #'(letrec ([f 5])
                      (display "Hello")
                      f))
       `(letrec-values ([(f.1) '5])
          (begin
            (#%plain-app (primitive display) '"Hello")
            f.1))))))

(update-current-languages! L)

(define-language current-target
  (extends current-source)
   (lambda (lambda)
     (- (#%plain-lambda formals expr))
     (+ (#%plain-lambda formals abody)))
   (expr (expr)
         (- (let-values ([(id ...) expr1] ...)
              expr)
            (letrec-values ([(id ...) expr1] ...)
              expr))
         (+ (let-values ([(id ...) expr1] ...)
              abody)
            (letrec-values ([(id ...) expr1] ...)
              abody)))
   (assigned-body (abody)
                  (+ (assigned (id ...) expr))))

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
        [(set! ,id ,[expr assigned*])
         (values `(set! ,id ,expr)
                 (set-add assigned* id))]
        [(let-values ([(,id ...) ,[expr assigned]] ...) ,[expr* assigned*])
         (values `(let-values ([(,id ...) ,expr] ...)
                    (assigned (,(set-intersect assigned* (apply set-union '() id)) ...) ,expr*))
                 (apply set-union '() (set-remove assigned* id) assigned))]
        [(letrec-values ([(,id ...) ,[expr assigned]] ...) ,[expr* assigned*])
         (values `(letrec-values ([(,id ...) ,expr] ...)
                    (assigned (,(set-intersect assigned* (apply set-union '() id)) ...) ,expr*))
                 (apply set-union '() (set-remove assigned* id) assigned))]
        ;; Really *should* be generated
        [(if ,[expr1 assigned1] ,[expr2 assigned2] ,[expr3 assigned3])
         (values `(if ,expr1 ,expr2 ,expr3)
                 (set-union assigned1 assigned2 assigned3))]
        [(begin ,[expr* assigned*] ... ,[expr assigned])
         (values `(begin ,expr* ... ,expr)
                 (apply set-union assigned assigned*))]
        [(begin0 ,[expr* assigned*] ... ,[expr assigned])
         (values `(begin0 ,expr* ... ,expr)
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
                         assigned)])
  (ModuleLevelForm : module-level-form (e) -> module-level-form ('())
                   [(begin-for-syntax ,[module-level-form assigned] ...)
                    (values `(begin-for-syntax ,module-level-form ...)
                            (apply set-union '() assigned))])
  (GeneralTopLevelForm : general-top-level-form (e) -> general-top-level-form ('())
                       [(define-values (,id ...) ,[expr assigned])
                        (values `(define-values (,id ...) ,expr)
                                (set-subtract assigned id))]
                       [(define-syntaxes (,id ...) ,[expr assigned])
                        (values `(define-syntaxes (,id ...) ,expr)
                                (set-subtract assigned id))])
  (SubmoduleForm : submodule-form (e) -> submodule-form ('()))
  (let-values ([(e* free*) (TopLevelForm e)])
    e*))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target top-level-form
      (check-equal?
       (current-compile #'(letrec ([y 8])
                            y))
       `(letrec-values ([(y.1) '8])
          (assigned ()
                    y.1)))
      (check-equal?
       (current-compile #'(let ([x 8])
                            (set! x 5)
                            (+ x 42)))
       `(let-values ([(x.1) '8])
          (assigned (x.1)
                    (begin (set! x.1 '5)
                           (#%plain-app (primitive +) x.1 '42)))))
      (check-equal?
       (current-compile #'(let ([x 1])
                            (letrec ([y (lambda (x) y)])
                              (+ x y))))
       `(let-values ([(x.1) '1])
          (assigned ()
                    (letrec-values ([(y.2) (#%plain-lambda (x.3) (assigned () y.2))])
                      (assigned ()
                                (#%plain-app (primitive +) x.1 y.2))))))
      (check-equal?
       (current-compile #'(lambda x
                            (set! x 42)
                            x))
       `(#%expression (#%plain-lambda x.1
                                      (assigned (x.1)
                                                (begin
                                                  (set! x.1 '42)
                                                  x.1))))))))

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (- (let-values ([(id ...) expr1] ...)
             abody)
           (letrec-values ([(id ...) expr1] ...)
             abody)
           (set! id expr))
        (+ (undefined)
           (let ([id expr1] ...)
             set-abody)
           (letrec ([id lambda] ...)
             expr)
           (set!-values (id ...) expr)))
  (set-abody (set-abody)
             (+ (begin-set! expr ... abody))))

(define-pass purify-letrec : current-source (e) -> current-target ()
  (Expr : expr (e) -> expr ()
        [(set! ,id ,[expr])
         `(set!-values (,id) ,expr)]
        [(letrec-values ([(,id) ,[lambda]] ...)
           (assigned (,id* ...) ,[expr]))
         (guard (set-empty? (set-intersect id* id)))
         `(letrec ([,id ,lambda] ...)
            ,expr)]
        [(letrec-values ([(,id ...) ,[expr]] ...)
           (assigned (,id* ...) ,[expr*]))
         (define flattened-ids (apply append id))
         (define undef (for/list ([i (in-range (length flattened-ids))])
                         `(undefined)))
         `(let ([,flattened-ids ,undef] ...)
            (begin-set!
              (set!-values (,id ...) ,expr) ...
              (assigned (,(apply set-union id* id) ...)
                        ,expr*)))]
        [(let-values ([(,id) ,[expr]] ...)
           ,[abody])
         `(let ([,id ,expr] ...)
            (begin-set!
              ,abody))]
        [(let-values ([(,id ...) ,[expr]] ...)
           (assigned (,id* ...) ,[expr*]))
         (define flattened-ids (apply append id))
         (define undef (for/list ([i (in-range (length flattened-ids))])
                         `(undefined)))
         `(let ([,flattened-ids ,undef] ...)
            (begin-set!
              (set!-values (,id ...) ,expr) ...
              (assigned (,id* ...)
                        ,expr*)))]))

(module+ test
  (update-current-compile!))

(define-pass optimize-direct-call : current-target (e) -> current-target ()
  (Expr : expr (e) -> expr ()
        [(#%plain-app (#%plain-lambda (,id ...) ,[abody])
                      ,[expr* -> expr*] ...)
         (guard (= (length id) (length expr*)))
         `(let ([,id ,expr*] ...)
            (begin-set!
              ,abody))]))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target top-level-form
      (check-equal?
       (current-compile #'((lambda (x) x) (lambda (y) y)))
       `(let ([x.2 (#%plain-lambda (y.1) (assigned () y.1))])
          (begin-set!
            (assigned () x.2))))
      (check-equal?
       (current-compile #'(letrec-values ([(a) (lambda (x) b)]
                                          [(b) (lambda (y) a)])
                            (a b)))
       `(letrec ([a.1 (#%plain-lambda (x.3) (assigned () b.2))]
                 [b.2 (#%plain-lambda (y.4) (assigned () a.1))])
          (#%plain-app a.1 b.2)))
      (check-equal?
       (current-compile #'(letrec-values ([(a) 5]
                                          [(b c) (values 6 7)])
                            (+ a b c)))
       `(let ([a.1 (undefined)]
              [b.2 (undefined)]
              [c.3 (undefined)])
          (begin-set!
            (set!-values (a.1) '5)
            (set!-values (b.2 c.3) (#%plain-app (primitive values) '6 '7))
            (assigned (c.3 b.2 a.1)
                      (#%plain-app (primitive +) a.1 b.2 c.3)))))
      (check-equal?
       (current-compile #'(let ([x (if #t 5 6)])
                            (set! x (+ x 1))))
       `(let ([x.1 (if '#t '5 '6)])
          (begin-set!
            (assigned (x.1) (set!-values (x.1) (#%plain-app (primitive +) x.1 '1))))))
      (check-equal?
       (current-compile #'(let-values ([(x y) (values 1 2)]
                                       [(z) 3])
                            (set! x 5)
                            (+ y z)))
       `(let ([x.1 (undefined)]
              [y.2 (undefined)]
              [z.3 (undefined)])
          (begin-set!
            (set!-values (x.1 y.2) (#%plain-app (primitive values) '1 '2))
            (set!-values (z.3) '3)
            (assigned (x.1)
                      (begin
                        (set!-values (x.1) '5)
                        (#%plain-app (primitive +) y.2 z.3))))))
      (check-equal?
       (current-compile #'(let-values ([(x y) (values 1 2)])
                            (set! x y)
                            y))
       `(let ([x.1 (undefined)]
              [y.2 (undefined)])
          (begin-set!
            (set!-values (x.1 y.2) (#%plain-app (primitive values) '1 '2))
            (assigned (x.1)
                      (begin
                        (set!-values (x.1) y.2)
                        y.2))))))))

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (- (let ([id expr1] ...)
             set-abody))
        (+ (let ([id expr1] ...)
             expr)
           (#%unbox id)
           (#%box id)
           (set!-boxes (id ...) expr)))
  (lambda (lambda)
    (- (#%plain-lambda formals abody))
    (+ (#%plain-lambda formals expr)))
  (set-abody (set-abody)
             (- (begin-set! expr ... abody)))
  (assigned-body (abody)
                 (- (assigned (id ...) expr))))

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
           [,id ((lookup-env env) id)]
           [(,id ...)
            `(,(map (lookup-env env) id) ...)]
           [(,id ,id* ... . ,id2)
            `(,((lookup-env env) id) ,(map (lookup-env env) id*) ... . ,((lookup-env env) id2))])
  (Lambda : lambda (e [env '()]) -> lambda ()
          [(#%plain-lambda ,formals
                           (assigned (,id ...) ,expr))
           (define env* (extend-env env id))
           `(#%plain-lambda ,(Formals formals env*)
                            ,(build-let id (map (lookup-env env*) id)
                                        (Expr expr env* #t)))])
  [Expr : expr (e [env '()] [boxes? #t]) -> expr ()
        [(let ([,id ,[expr]] ...)
           (begin-set!
             ,expr** ...
             (assigned (,id* ...) ,expr*)))
         (cond [(null? id) (Expr expr* env #t)]
               [else (define env* (extend-env env id*))
                     (define let* (build-let id* (map (lookup-env env*) id*)
                                             (Expr expr* env* #t)))
                     (if (= (length expr**) 0)
                         `(let ([,(map (lookup-env env*) id) ,expr] ...)
                            ,let*)
                         `(let ([,(map (lookup-env env*) id) ,expr] ...)
                            (begin
                              ,(for/list ([e (in-list expr**)])
                                 (Expr e env* #f)) ...
                              ,let*)))])]
        [,id
         (if (dict-has-key? env id) `(#%unbox ,id) id)]
        [(set!-values (,id ...) ,expr)
         (define expr* (Expr expr env #f))
         (if boxes?
             `(set!-boxes (,id ...) ,expr*)
             `(set!-values (,(map (lookup-env env) id) ...) ,expr*))]])

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target top-level-form
      (check-equal?
       (current-compile #'(let ([x 5])
                            (set! x 6)
                            x))
       `(let ([x.1 '5])
          (begin
            (set!-values (x.1) (#%box x.1))
            (begin
              (set!-boxes (x.1) '6)
              (#%unbox x.1)))))
      (check-equal?
       (current-compile #'(lambda (x y)
                            (set! x 5)
                            (list x y)))
       `(#%expression (#%plain-lambda (x.1 y.2)
                                      (begin
                                        (set!-values (x.1) (#%box x.1))
                                        (begin
                                          (set!-boxes (x.1) '5)
                                          (#%plain-app (primitive list) (#%unbox x.1) y.2))))))
      (check-equal?
       (current-compile #'(lambda x
                            (let ()
                              (set! x 42)
                              (+ x 8))))
       `(#%expression (#%plain-lambda x.1
                                      (begin
                                        (set!-values (x.1) (#%box x.1))
                                        (begin
                                          (set!-boxes (x.1) '42)
                                          (#%plain-app (primitive +) (#%unbox x.1) '8))))))
      (check-equal?
       (current-compile #'(let-values ([(x y) (values 1 2)])
                            (set! x y)
                            y))
       `(let ([x.1 (undefined)]
              [y.2 (undefined)])
          (begin
            (set!-values (x.1 y.2) (#%plain-app (primitive values) '1 '2))
            (begin
              (set!-values (x.1) (#%box x.1))
              (begin
                (set!-boxes (x.1) y.2)
                y.2))))))))

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (entry compilation-top)
  (compilation-top (compilation-top)
                   (+ (program (binding ...) top-level-form)))
  (submodule-form (submodule-form)
                  (- (module id module-path
                       (module-level-form ...)
                       (submodule-form ...)
                       (submodule-form* ...)))
                  (+ (module id module-path (id* ...)
                             (module-level-form ...)
                             (submodule-form ...)
                             (submodule-form* ...))))
  (lambda (lambda)
    (- (#%plain-lambda formals expr))
    (+ (#%plain-lambda formals fbody)))
  (binding (binding)
           (+ id
              false))
  (free-body (fbody)
             (+ (free (id ...) (binding* ...) expr))))

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
                       [(define-values (,id ...) ,[expr free-local free-global])
                        (values `(define-values (,id ...) ,expr)
                                free-local
                                (set-union free-global id))]
                       [(define-syntaxes (,id ...) ,[expr free-local free-global])
                        (values `(define-syntaxes (,id ...) ,expr)
                                free-local
                                (set-union free-global id))])
  (Expr : expr (e [env '()]) -> expr ('() '())
        [,id (if (set-member? env id)
                 (values id (list id) '())
                 (values id '() (list id)))]
        [(let ([,id* ,[expr* env -> expr* free-local* free-global*]] ...)
           ,expr**)
         (define-values (expr free-local free-global) (Expr expr** (set-union env id*)))
         (values
          `(let ([,id* ,expr*] ...)
             ,expr)
          (apply set-union (set-subtract free-local id*) free-local*)
          (apply set-union free-global free-global*))]
        [(letrec ([,id* ,lambda**] ...)
           ,expr**)
         (define env* (set-union env id*))
         (define-values (expr free-local free-global) (Expr expr** env*))
         (define-values (lambda* free-local* free-global*)
           (for/fold ([lambda* null]
                      [free-local* null]
                      [free-global* null])
                     ([i (in-list lambda**)])
             (define-values (l fl fg) (Lambda i env*))
             (values (cons l lambda*) (cons fl free-local*) (cons fg free-global*))))
         (values `(letrec ([,id* ,(reverse lambda*)] ...)
                    ,expr)
                 (apply set-union (set-subtract free-local id*) (reverse free-local*))
                 (apply set-union (set-subtract free-global id*) (reverse free-global*)))]
        [(set!-boxes (,id) ,[expr free-local free-global])
         (if (set-member? env id)
             (values `(set!-boxes (,id) ,expr) (set-add free-local id) free-global)
             (values `(set!-values (,id) ,expr) free-local (set-add free-global id)))]
        [(set!-boxes (,id ...) ,[expr free-local free-global])
         (values `(set!-boxes (,id ...) ,expr)
                 (set-union free-local (set-intersect id env))
                 (set-union free-global (set-subtract id env)))]
        [(set!-values (,id ...) ,[expr free-local free-global])
         (values `(set!-values (,id ...) ,expr)
                 (set-union free-local (set-intersect id env))
                 (set-union free-global (set-subtract id env)))]
        [(#%box ,id)
         (if (set-member? env id)
             (values `(#%box ,id) (list id) '())
             (values `(#%box ,id) '() (list id)))]
        [(#%unbox ,id)
         (if (set-member? env id)
             (values `(#%unbox ,id) (list id) '())
             (values `(#%unbox ,id) '() (list id)))]
        [(#%top . ,id)
         (values `(#%top . ,id) '() (list id))]
        [(#%variable-reference)
         (values `(#%variable-reference)
                 null
                 '(#f))]
        [(#%variable-reference ,id)
         (if (set-member? env id)
             (values `(#%variable-reference ,id) (list id) '())
             (values `(#%variable-reference ,id) '() (list id)))]
        [(#%variable-reference-top ,id)
         (values `(#%variable-reference-top ,id) '() (list id))]
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
        [(begin0 ,[expr* free-local* free-global*] ...
                 ,[expr free-local free-global])
         (values `(begin0 ,expr* ... ,expr)
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
                 (values `(#%expression ,expr) free-local free-global)])
  (ModuleLevelForm : module-level-form (e [env '()]) -> module-level-form ('() '())
                   [(begin-for-syntax ,[module-level-form free-local free-global])
                    (values `(begin-for-syntax module-level-form) free-local free-global)])
  (SubmoduleForm : submodule-form (e env) -> submodule-form ('() '())
                 [(module ,id ,module-path
                    (,[module-level-form free-local free-global] ...)
                    (,[submodule-form** free-local** free-global**] ...)
                    (,[submodule-form* free-local* free-global*] ...))
                  (values `(module ,id ,module-path (,(apply set-union '() free-global) ...)
                                   (,module-level-form ...)
                                   (,submodule-form** ...)
                                   (,submodule-form* ...))
                          '() '())])
  (let-values ([(e* local* global*) (TopLevelForm e '())])
    `(program (,global* ...) ,e*)))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target compilation-top
      (check-equal?
       (current-compile #'(lambda (x)
                            (lambda (y)
                              x)))
       `(program () (#%expression
                     (#%plain-lambda (x.1)
                                     (free () ()
                                           (#%plain-lambda (y.2)
                                                           (free (x.1) ()
                                                                 x.1)))))))
      (check-equal?
       (current-compile #'(let ([x 5])
                            (lambda (y)
                              x)))
       `(program () (let ([x.1 '5])
                      (#%plain-lambda (y.2)
                                      (free (x.1) ()
                                            x.1)))))
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (lambda y (if x 4 5))))
       `(program (x) (begin*
                       (define-values (x) '5)
                       (#%expression
                        (#%plain-lambda y.1
                                        (free () (x)
                                              (if x '4 '5)))))))
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (set! x 6)))
       `(program (x) (begin*
                       (define-values (x) '5)
                       (set!-values (x) '6))))
      (check-equal?
       (current-compile #'(letrec ([f (lambda (x) x)])
                            (f 12)))
       `(program () (letrec ([f.1 (#%plain-lambda (x.2) (free () () x.2))])
                      (#%plain-app f.1 '12))))
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (define y 6)
                            (module foo racket/base
                              (#%plain-module-begin
                               (define x 12)
                               (define z 13)))))
       `(program (y x) (begin*
                         (define-values (x) '5)
                         (define-values (y) '6)
                         (module foo racket/base (z x)
                                 ((define-values (x) '12)
                                  (define-values (z) '13))
                                 () ()))))
      (check-equal?
       (current-compile #'(lambda (x)
                            (#%variable-reference)))
       `(program (#f) (#%expression
                       (#%plain-lambda (x.1)
                                       (free () (#f)
                                             (#%variable-reference)))))))))

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (+ (set!-global id expr))))

(define-pass raise-toplevel-variables : current-source (e) -> current-target ()
  [CompilationTop : compilation-top (e [globals '()]) -> compilation-top ()
                  [(program (,binding ...) ,top-level-form)
                   `(program (,binding ...) ,(TopLevelForm top-level-form binding))]]
  (Expr : expr (e [globals '()]) -> expr ()
        [(set!-values (,id) ,[expr])
         (guard (set-member? globals id))
         `(set!-global ,id ,expr)]
        [,id (guard (set-member? globals id)) `(#%top . ,id)]
        [(#%variable-reference ,id)
         (guard (set-member? globals id))
         `(#%variable-reference-top ,id)])
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
                 [(module ,id ,module-path (,id* ...)
                          (,module-level-form ...)
                          (,[submodule-form] ...)
                          (,[submodule-form*] ...))
                  `(module ,id ,module-path (,id* ...)
                           (,(for/list ([mlf (in-list module-level-form)])
                               (ModuleLevelForm mlf id*)) ...)
                           (,(for/list ([sf (in-list submodule-form)])
                               (SubmoduleForm sf id*)) ...)
                           (,(for/list ([sf (in-list submodule-form*)])
                               (SubmoduleForm sf id*)) ...))]))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target compilation-top
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (set! x 6)
                            x))
       `(program (x) (begin*
                       (define-values (x) '5)
                       (set!-global x '6)
                       (#%top . x))))
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (#%variable-reference x)))
       `(program (x) (begin*
                       (define-values (x) '5)
                       (#%variable-reference-top x))))
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (lambda (y)
                              (lambda (z)
                                (+ x y z)))))
       `(program (x) (begin*
                       (define-values (x) '5)
                       (#%expression
                        (#%plain-lambda (y.1)
                                        (free () (x)
                                              (#%plain-lambda (z.2)
                                                              (free (y.1) (x)
                                                                    (#%plain-app
                                                                     (primitive +) (#%top . x) y.1 z.2)))))))))
      (check-equal?
       (current-compile #'(begin
                            (define x 5)
                            (let ([y 6])
                              (set! x (+ x 1))
                              (set! y (+ y 1))
                              (+ x y))))
       `(program (x) (begin*
                       (define-values (x) '5)
                       (let ([y.1 '6])
                         (begin
                           (set!-values (y.1) (#%box y.1))
                           (begin
                             (set!-global x (#%plain-app (primitive +) (#%top . x) '1))
                             (set!-boxes (y.1) (#%plain-app (primitive +) (#%unbox y.1) '1))
                             (#%plain-app (primitive +) (#%top . x) (#%unbox y.1)))))))))))

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (+ (closure id lambda))))

(define-pass closurify-letrec : current-source (e) -> current-target ()
  (definitions
    (define (remove-index l index)
      (append (take l index) (drop l (+ 1 index)))))
  (Formals : formals (e) -> formals ())
  [Expr : expr (e) -> expr ()
        [(letrec () ,[expr])
         expr]
        [(letrec ([,id (#%plain-lambda ,formals (free (,id1* ...) (,binding2* ...) ,expr*))] ...)
           ,expr)
         (define empty-index
           (for/fold ([acc #f])
                     ([i (in-list id1*)]
                      [iter (in-range (length id1*))])
             (if (null? i) iter acc)))
         (if empty-index
             `(let ([,(list-ref id empty-index)
                     (closure ,(list-ref id empty-index)
                              ,(Expr (with-output-language (current-source expr)
                                       `(#%plain-lambda ,(list-ref formals empty-index)
                                                        (free (,(list-ref id1* empty-index) ...)
                                                              (,(list-ref binding2* empty-index) ...)
                                                              ,(list-ref expr* empty-index))))))])
                ,(Expr (with-output-language (current-source expr)
                         `(letrec ([,(remove-index id empty-index)
                                    (#%plain-lambda ,(remove-index formals empty-index)
                                                    (free (,(remove-index id1* empty-index) ...)
                                                          (,(remove-index binding2* empty-index) ...)
                                                          ,(remove-index expr* empty-index)))]
                                   ...)
                            ,expr))))
             `(letrec ([,id (#%plain-lambda ,(map Formals formals)
                                            (free (,id1* ...) (,binding2* ...)
                                                  ,(map Expr expr*)))] ...)
                ,(Expr expr)))]])

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target compilation-top
      (check-equal?
       (current-compile #'(letrec ([f (lambda (x) x)])
                            (f 12)))
       `(program () (let ([f.1 (closure f.1 (#%plain-lambda (x.2) (free () () x.2)))])
                      (#%plain-app f.1 '12)))))))

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (expr (expr)
        (- (let ([id expr1] ...) expr)
           (undefined))
        (+ (let ([id expr1]) expr)
           (let-void (id ...) expr))))

(define-pass void-lets : current-source (e) -> current-target ()
  (Expr : expr (e) -> expr ()
        [(letrec ([,id ,[lambda]] ...)
           ,[expr])
         `(let-void (,id ...)
                    (letrec ([,id ,lambda] ...)
                      ,expr))]
        [(let ([,id ,[expr1]]) ,[expr])
         `(let ([,id ,expr1]) ,expr)]
        [(let ([,id (undefined)] ...) ,[expr])
         `(let-void (,id ...)
                    ,expr)]
        [(let ([,id ,[expr1]] ...) ,[expr])
         `(let-void (,id ...)
                    (begin
                      (set!-values (,id) ,expr1) ...
                      ,expr))]))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target compilation-top
      (check-equal?
       (current-compile #'(let ([x 1]) x))
       `(program () (let ([x.1 '1]) x.1)))
      (check-equal?
       (current-compile #'(let ([x 1]
                                [y 2])
                            (+ x y)))
       `(program () (let-void (x.1 y.2)
                              (begin
                                (set!-values (x.1) '1)
                                (set!-values (y.2) '2)
                                (#%plain-app (primitive +) x.1 y.2)))))
      (check-equal?
       (current-compile #'(let-values ([(x y) (values 1 2)]
                                       [(z) 3])
                            (set! x 5)
                            (+ x y z)))
       `(program () (let-void (x.1 y.2 z.3)
                              (begin
                                (set!-values (x.1 y.2) (#%plain-app (primitive values) '1 '2))
                                (set!-values (z.3) '3)
                                (begin
                                  (set!-values (x.1) (#%box x.1))
                                  (begin
                                    (set!-boxes (x.1) '5)
                                    (#%plain-app (primitive +) (#%unbox x.1) y.2 z.3)))))))
      (check-equal?
       (current-compile #'(let ([x 5])
                            (lambda (y)
                              (set! x 6)
                              (+ x y))))
       `(program () (let ([x.1 '5])
                      (begin
                        (set!-values (x.1) (#%box x.1))
                        (#%plain-lambda (y.2)
                                        (free (x.1) ()
                                              (begin
                                                (set!-boxes (x.1) '6)
                                                (#%plain-app (primitive +) (#%unbox x.1) y.2)))))))))))

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (terminals
   (+ (exact-nonnegative-integer (exact-nonnegative-integer eni))
      (boolean (boolean))))
  (expr (expr)
        (- id
           (primitive id)
           (let-void (id ...) expr)
           (let ([id expr1]) expr)
           (letrec ([id lambda] ...)
             expr)
           (set!-boxes (id ...) expr)
           (set!-values (id ...) expr)
           (set!-global id expr)
           (#%box id)
           (#%unbox id)
           (#%top . id)
           (#%variable-reference)
           (#%variable-reference id)
           (#%variable-reference-top id))
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
                          (- (define-values (id ...) expr))
                          (+ (define-values (eni ...) expr)))
  (lambda (lambda)
    (- (#%plain-lambda formals fbody))
    (+ (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) expr)))
  (binding (binding)
           (+ eni
              (primitive eni)))
  (formals (formals)
           (- id
              (id ...)
              (id id* ... . id2)))
  (free-body (fbody)
             (- (free (id ...) (binding* ...) expr))))

(define-pass debruijn-indices : current-source (e) -> current-target ()
  (definitions
    (define-syntax-rule (formals->identifiers* fmls)
      (formals->identifiers current-source fmls))
    (define-syntax-rule (formals-rest?* fmls)
      (formals-rest? L9 fmls))
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
                           (free (,id2 ...) (,binding3 ...)
                                 ,expr))
           (define params (formals->identifiers* formals))
           (define rest? (formals-rest?* formals))
           (define-values (env* frame*) (extend-env env frame (reverse (append id2 params))))
           (define frame** (if (= (length binding3) 0) frame* (+ frame* 1)))
           (define locals (map (var->index env frame global-env) id2))
           `(#%plain-lambda ,(length params)
                            ,rest?
                            (,(if (= (length binding3) 0) locals (cons (- frame prefix-frame) locals)) ...)
                            (,(map ((curry dict-ref) global-env) binding3) ...)
                            ,(Expr expr env* frame** global-env frame**))])
  (Expr : expr (e [env '()] [frame 0] [global-env '()] [prefix-frame 0]) -> expr ()
        [,id ((var->index env frame global-env) id)]
        [(primitive ,id) `(primitive ,(dict-ref primitive-table* id))]
        [(#%box ,id) `(#%box ,((var->index env frame global-env) id))]
        [(#%unbox ,id) `(#%unbox ,((var->index env frame global-env) id))]
        [(set!-values (,id ...) ,[expr])
         (define-values (count offset) (ids->range env frame id))
         `(set!-values ,count ,offset ,expr)]
        [(set!-boxes (,id ...) ,[expr])
         (define-values (count offset) (ids->range env frame id))
         `(set!-boxes ,count ,offset ,expr)]
        [(set!-global ,id ,[expr])
         `(set!-global ,(- frame prefix-frame) ,(dict-ref global-env id) ,expr)]
        [(#%top . ,id) `(#%top ,(- frame prefix-frame) ,(dict-ref global-env id))]
        [(#%variable-reference)
         `(#%variable-reference-none ,(- frame prefix-frame) ,(hash-ref global-env #f))]
        [(#%variable-reference-top ,id) `(#%variable-reference-top 0)] ;; TODO: Global vars
        [(#%variable-reference ,id) `(#%variable-reference ,((var->index env frame) id))]
        [(let ([,id ,expr1])
           ,expr)
         (define-values (env* frame*) (extend-env env frame (list id)))
         `(let-one ,(Expr expr1 env (+ frame 1) global-env prefix-frame)
                   ,(Expr expr env* frame* global-env prefix-frame))]
        [(let-void (,id ...)
                   ,expr)
         (define-values (env* frame*) (extend-env env frame (reverse id)))
         `(let-void ,(length id)
                    ,(Expr expr env* frame* global-env prefix-frame))]
        [(letrec ([,id ,[lambda]] ...)
           ,[expr])
         `(letrec (,lambda ...)
            ,expr)]
        [(#%plain-app ,expr ,expr* ...)
         (define expr1 (Expr expr env (+ frame (length expr*)) global-env prefix-frame))
         (define expr*1 (map (lambda (e) (Expr e env (+ frame (length expr*)) global-env prefix-frame)) expr*))
         `(#%plain-app ,expr1 ,expr*1 ...)])
  (GeneralTopLevelForm : general-top-level-form (e [env '()] [frame 0] [global-env '()])
                       -> general-top-level-form ()
                       [(define-values (,id ...) ,[expr])
                        `(define-values (,(map ((curry dict-ref) global-env) id) ...) ,expr)])
  (TopLevelForm : top-level-form (e [env '()] [frame 0] [global-env '()] [prefix-frame 0])
                -> top-level-form ())
  (SubmoduleForm : submodule-form (e [env '()] [frame 0] [global-env '()] [prefix-frame '()])
                 -> submodule-form ()
                 [(module ,id ,module-path (,id* ...)
                          (,module-level-form ...)
                          (,submodule-form ...)
                          (,submodule-form* ...))
                  (define global-env* (make-global-env id*))
                  `(module ,id ,module-path (,id* ...)
                              (,(for/list ([mlf (in-list module-level-form)])
                                  (ModuleLevelForm mlf env frame global-env prefix-frame)) ...)
                              (,(for/list ([sf (in-list submodule-form)])
                                  (SubmoduleForm sf env frame global-env prefix-frame)) ...)
                              (,(for/list ([sf (in-list submodule-form*)])
                                  (SubmoduleForm sf env frame global-env prefix-frame)) ...))])
  (ModuleLevelForm : module-level-form (e [env '()] [frame 0] [global-env '()] [prefix-frame 0])
                   -> module-level-form ())
  (CompilationTop : compilation-top (e) -> compilation-top ()
                  [(program (,binding ...) ,top-level-form)
                   `(program (,binding ...) ,(TopLevelForm top-level-form '() 0 (make-global-env binding) 0))]))

(splicing-let-syntax ([current-target (syntax-local-value #'current-target-top)])
  (module+ test
    (update-current-compile!)
    (define-compiler-test current-target compilation-top
      (check-equal?
       (current-compile #'(lambda (x) x))
       `(program () (#%expression (#%plain-lambda 1 #f () () 0))))
      (check-equal?
       (current-compile #'(let ([x 5])
                       (lambda (y . z) x)))
       `(program () (let-one '5 (#%plain-lambda 2 #t (0) () 0))))
      (check-equal?
       (current-compile #'(let ([x 5]
                           [y 6])
                       (+ x y)))
       `(program () (let-void 2
                              (begin
                                (set!-values 1 0 '5)
                                (set!-values 1 1 '6)
                                (#%plain-app (primitive 247) 2 3)))))
      (check-equal?
       (current-compile #'(begin
                       (define x 5)
                       (+ x 5)))
       `(program (x) (begin*
                       (define-values (0) '5)
                       (#%plain-app (primitive 247) (#%top 2 0) '5))))
      (check-equal?
       (current-compile #'(begin
                       (define x 5)
                       (lambda (y)
                         y x)))
       `(program (x) (begin*
                       (define-values (0) '5)
                       (#%expression
                        (#%plain-lambda 1 #f (0) (0)
                                        (begin 1 (#%top 0 0))))))))))

(update-current-languages! L)

(define-language current-target
  (extends current-source)
  (entry compilation-top)
  (compilation-top (compilation-top)
                   (- (program (binding ...) top-level-form))
                   (+ (program eni (binding ...) top-level-form)))
  (submodule-form (submodule-form)
                  (- (module id module-path (id* ...)
                             (module-level-form ...)
                             (submodule-form ...)
                             (submodule-form* ...)))
                  (+ (module id module-path (id* ...) eni
                             (module-level-form ...)
                             (submodule-form ...)
                             (submodule-form* ...))))
  (lambda (lambda)
    (- (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) expr))
    (+ (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) eni4 expr))))

(define-pass find-let-depth : current-source (e) -> current-target ()
  (Lambda : lambda (e) -> lambda (0)
          [(#%plain-lambda ,eni1 ,boolean (,[binding2] ...) (,[binding3] ...) ,[expr depth])
           (define depth* (+ eni1 (length binding2) depth))
           (values `(#%plain-lambda ,eni1 ,boolean (,binding2 ...) (,binding3 ...) ,(+ 5
                                                                                       eni1
                                                                                       (if boolean 1 0)
                                                                                       (length binding2)
                                                                                       (length binding3)
                                                                                       depth*)
                                    ,expr)
                   1)])
  [Binding : binding (e) -> binding (0)]
  (Expr : expr (e) -> expr (0)
        [(closure ,id ,[lambda depth])
         (values `(closure ,id ,lambda) depth)]
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
        [(begin0 ,[expr* depth*] ... ,[expr depth])
         (values `(begin0 ,expr* ... ,expr)
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
                         (apply max 0 depth))])
  (ModuleLevelForm : module-level-form (e) -> module-level-form (0)
                   [(begin-for-syntax ,[module-level-form depth] ...)
                    (values `(begin-for-syntax ,module-level-form ...)
                            (apply max 0 depth))])
  (SubmoduleForm : submodule-form (e) -> submodule-form (0)
                 [(module ,id ,module-path (,id* ...)
                          (,[module-level-form depth] ...)
                          (,[submodule-form** depth**] ...)
                          (,[submodule-form* depth*] ...))
                  (values `(module ,id ,module-path (,id* ...) ,(apply max '() depth)
                                   (,module-level-form ...)
                                   (,submodule-form** ...)
                                   (,submodule-form* ...))
                          0)])
  (GeneralTopLevelForm : general-top-level-form (e) -> general-top-level-form (0)
                       [(define-values (,eni ...) ,[expr depth])
                        (values `(define-values (,eni ...) ,expr) depth)]
                       [(define-syntaxes (,id ...) ,[expr depth])
                        (values `(define-syntaxes (,id ...) ,expr) depth)])
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
                       (#%plain-lambda 1 #f () () 10 (let-one '5 (#%plain-app (primitive 247) 3 2))))))
      (check-equal?
       (current-compile #'(if (= 5 6)
                              (let ([x '5]
                                    [y '6])
                                y)
                              (let ([x '6])
                                x)))
       `(program 2 () (if (#%plain-app (primitive 256) '5 '6)
                          (let-void 2
                                    (begin
                                      (set!-values 1 0 '5)
                                      (set!-values 1 1 '6)
                                      1))
                          (let-one '6 0)))))))

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
                                       (zo:prefix 0 binding '() 'missing)
                                       (TopLevelForm top-level-form))])
  (TopLevelForm : top-level-form (e) -> * ()
                [(#%expression ,expr)
                 (Expr expr)]
                [(begin* ,top-level-form ...)
                 (zo:splice (map TopLevelForm top-level-form))]
                [(begin-for-syntax* ,top-level-form ...)
                 (void)])
  (ModuleLevelForm : module-level-form (e) -> * ()
                   [(#%provide ,raw-provide-spec ...)
                    (void)]
                   [(begin-for-syntax ,module-level-form ...)
                    (void)]
                   [(#%declare ,declaration-keyword ...)
                    (void)])
  (SubmoduleForm : submodule-form (e) -> * ()
                 [(module ,id ,module-path (,id* ...) ,eni
                          (,module-level-form ...)
                          (,submodule-form ...)
                          (,submodule-form* ...))
                  (void)])
  (GeneralTopLevelForm : general-top-level-form (e) -> * ()
                       [(define-values (,eni ...) ,expr)
                        (zo:def-values (for/list ([i (in-list eni)])
                                         (zo:toplevel 0 i #f #f))
                                       (Expr expr))]
                       [(define-syntaxes (,id ...) ,expr)
                        (void)]
                       [(#%require ,raw-require-spec ...)
                        (void)])
  (Bidnding : binding (e) -> * ()
            [,false false]
            [,id id]
            [,eni eni]
            [(primitive ,eni)
             (zo:primval eni)])
  (Expr : expr (e) -> * ()
        [,eni (zo:localref #f eni #f #f #f)]
        [(closure ,id ,lambda) (zo:closure (Lambda lambda) id)]
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
        [(begin0 ,expr* ... ,expr)
         (zo:beg0 (append (map Expr expr*)
                          (list (Expr expr))))]
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
                   (Expr expr))]))

(module+ test
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
                                    (random 1)
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
                                (define x 5)
                                (let ([x 6])
                                  (#%top . x))))
           (compile-compare #'(call-with-current-continuation (lambda (x) 5)))
           (compile-compare #'(begin
                                (module foo racket
                                  (provide x)
                                  (define x 5))
                                (require 'foo)
                                x)))
         all-compiler-tests)))

(define-syntax (define-compiler stx)
  (syntax-parse stx
    [(_ name:id passes* ...+)
    #:with compilers (format-id stx "compilers")
     (define passes (reverse (syntax->list #'(passes* ...))))
     #`(begin (define name (compose #,@passes))
              (module* test-compiler-bindings #f
                (provide (all-defined-out))
                (define compilers null)
                #,@(let build-partial-compiler ([passes passes]
                                                [pass-count (length passes)])
                     (if (= pass-count 0)
                         '()
                         (with-syntax ([name* (format-id stx "~a/~a" #'name (- pass-count 1))])
                           (list* #`(define name* (compose #,@passes))
                                  #`(set! compilers (cons name* compilers))
                                  (if (identifier? (car passes))
                                      (with-syntax ([name** (format-id stx
                                                                       "~a/~a"
                                                                       #'name
                                                                       (car passes))])
                                        (cons #`(define name** name*)
                                              (build-partial-compiler (cdr passes) (- pass-count 1))))
                                      (build-partial-compiler (cdr passes) (- pass-count 1)))))))))]))

;; Expand syntax fully, even at the top level
(define (expand-syntax* stx)
  (parameterize ([current-namespace (make-base-namespace)])
    (namespace-require 'racket/undefined)
    (expand-syntax-top-level-with-compile-time-evals
     (namespace-syntax-introduce stx))))

(define-compiler compile
  expand-syntax*
  parse-and-rename
  lift-submodules
  make-begin-explicit
  identify-assigned-variables
  purify-letrec
  optimize-direct-call
  convert-assignments
  uncover-free
  raise-toplevel-variables
  closurify-letrec
  void-lets
  debruijn-indices
  find-let-depth
  generate-zo-structs
  zo-marshal)

(module+ test
  (run-all-compiler-tests))
