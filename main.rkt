#lang racket/base

(require nanopass/base
         syntax/parse
         racket/match
         racket/set
         racket/dict
         racket/port
         compiler/zo-marshal
         rackunit
         (prefix-in zo: compiler/zo-structs)
         (rename-in racket/base
                    [compile base:compile])
         (for-syntax racket/base
                     syntax/parse
                     racket/syntax))

(require/expose compiler/decompile (primitive-table))

(define primitive-table*
  (for/hash ([(k v) (in-hash primitive-table)])
    (values v k)))

(define (raw-provide-spec? rps)
  #t)

(define (raw-require-spec? rrs)
  #t)

(define (declaration-keyword? dk)
  #t)

(define (datum? d)
  #t)

(define id? symbol?)

(define fresh (make-parameter gensym))

(module+ test
  (require rackunit
           rackunit/text-ui)

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
       #`(begin
           (define name
               (with-output-language (lang form)
                 (test-suite
                     (format "Test suite for: ~a" '#,(syntax->datum #'lang))
                   #:before (lambda () (set! deterministic-fresh/count 0))
                   (parameterize ([fresh deterministic-fresh])
                     (test-case (format "Test case for: ~a" '#,(syntax->datum #'lang))
                       (set! deterministic-fresh/count 0)
                       body) ...))))
           (set! all-compiler-tests (cons name all-compiler-tests)))]))

  ;; Run all tests defined with define-compiler-test
  (define-syntax-rule (run-all-compiler-tests)
    (let ()
      (map run-tests all-compiler-tests)
      (void)))

  ;; Compare result of current compiler to regular compiler
  (define-syntax (compile-compare stx)
    (syntax-case stx ()
      [(_ expression)
       #`(test-case "Test case for finished compiler"
           #,(syntax/loc stx
               (check-equal?
                (eval (bytes->compiled-expression (compile expression)))
                (eval expression))))])))

; TODO Move back into test submodule.
(define (bytes->compiled-expression zo)
  (parameterize ([read-accept-compiled #t])
    (with-input-from-bytes zo
      (lambda () (read)))))

(define-language Lsrc
  (terminals
   (raw-require-spec (raw-require-spec))
   (raw-provide-spec (raw-provide-spec))
   (module-path (module-path))
   (declaration-keyword (declaration-keyword))
   (datum (datum))
   (id (id)))
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
        (#%variable-reference-top (id))
        (#%variable-reference))
  (formals (formals)
           id
           (id ...)
           (id id* ... . id2)))

(define-language L1
  (extends Lsrc)
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

(define-language L2
  (extends L1)
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

(define-language L3
  (extends L2)
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

(define-language L4
  (extends L3)
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

(define-language L5
  (extends L4)
  (lambda (lambda)
    (- (#%plain-lambda formals expr))
    (+ (#%plain-lambda formals fbody)))
  (free-body (fbody)
             (+ (free (id ...) (id* ...) expr))))

(define-language L6
  (extends L5)
  (expr (expr)
        (- (let ([id expr1] ...) expr)
           (undefined))
        (+ (let ([id expr1]) expr)
           (let-void (id ...) expr))))

(define-language L7
  (extends L6)
  (terminals
   (+ (exact-nonnegative-integer (exact-nonnegative-integer eni))
      (boolean (boolean))))
  (expr (expr)
        (- id
           (let-void (id ...) expr)
           (let ([id expr1]) expr)
           (letrec ([id lambda] ...)
             expr)
           (set!-boxes (id ...) expr)
           (set!-values (id ...) expr)
           (#%box id)
           (#%unbox id)
           (#%top . id)
           (#%variable-reference id)
           (#%variable-reference-top (id)))
        (+ binding
           (primitive eni)
           (let-void eni expr)
           (let-one expr1 expr)
           (letrec (lambda ...)
             expr)
           (set!-boxes eni1 eni2 expr)
           (set!-values eni1 eni2 expr)
           (#%box eni)
           (#%unbox eni)
           (#%top . eni)
           (#%variable-reference eni)
           (#%variable-reference-top (eni))))
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
             (- (free (id ...) (id* ...) expr))))

(define-language L8
  (extends L7)
  (entry compilation-top)
  (compilation-top (compilation-top)
                   (+ (program eni top-level-form)))
  (lambda (lambda)
    (- (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) expr))
    (+ (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) eni4 expr))))

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

;; Parse and alpha-rename expanded program
(define-pass parse-and-rename : * (form) -> Lsrc ()
  (definitions
    (define initial-env (hash))
    (define (extend-env env vars)
      (for/fold ([acc env])
                ([var vars])
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
                   (,(for/list ([i (syntax->list #'(body ...))])
                      (parse-mod i env*)) ...))]
               [(begin body ...)
                `(begin* ,(for/list ([i (syntax->list #'(body ...))])
                            (parse-top i env)) ...)]
               [(begin-for-syntax body ...)
                `(begin-for-syntax* ,(for/list ([i (syntax->list #'(body ...))])
                                       (parse-top i env)) ...)]
               [else
                (parse-gen #'else env)]))

  (parse-mod : * (form env) -> module-level-form ()
             (syntax-parse form
               #:literals (#%provide begin-for-syntax #%declare module module*
                                     #%plain-module-begin)
               [(#%provide spec ...)
                `(#%provide ,(syntax->list #'(spec ...)) ...)]
               [(begin-for-syntax body ...)
                `(begin-for-syntax ,(for/list ([i (syntax->list #'(body ...))])
                                      (parse-mod i env)) ...)]
               [(#%declare keyword ...)
                `(#%declare ,(syntax->list #'(keyword ...)) ...)]
               [(module id:id path
                  (#%plain-module-begin body ...))
                (define env* (extend-env env (list #'id)))
                `(submodule ,(syntax->datum #'id) ,(syntax->datum #'path)
                            (,(for/list ([i (syntax->list #'(body ...))])
                                (parse-mod i env*)) ...))]
               [(module* id:id path
                  (#%plain-module-begin body ...))
                (define env* (extend-env env (list #'id)))
                `(submodule* ,(syntax->datum #'id) ,(syntax->datum #'path)
                             (,(for/list ([i (syntax->list #'(body ...))])
                                 (parse-mod i env*)) ...))]
               [(module* id:id path
                  (#%plain-module-begin body ...))
                (define env* (extend-env env (list #'id)))
                `(submodule* ,(syntax->datum #'id)
                             (,(for/list ([i (syntax->list #'(body ...))])
                                 (parse-mod i env*)) ...))]
               [else
                (parse-gen #'else env)]))

  (parse-gen : * (form env) -> general-top-level-form ()
             (syntax-parse form
               #:literals (define-values define-syntaxes #%require)
               [(define-values (id:id ...) body)
                ;(define env* (extend-env env (syntax->list #'(id ...))))
                `(define-values (,(for/list ([i (syntax->list #'(id ...))])
                                   (parse-expr i env)) ...)
                   ,(parse-expr #'body env))]
               [(define-syntaxes (id:id ...) body)
                ;(define env* (extend-env env (syntax->list #'(id ...))))
                `(define-syntaxes (,(for/list ([i (syntax->list #'(id ...))])
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
                [id:id ((lookup-env env) #'id)]
                [(#%plain-lambda formals body* ... body)
                 (define-values (formals* env*) (parse-formals #'formals env))
                 `(#%plain-lambda ,formals*
                                  ,(for/list ([b (syntax->list #'(body* ...))])
                                     (parse-expr b env*)) ...
                                  ,(parse-expr #'body env*))]
                [(case-lambda (formals body* ... body) ...)
                 (match (for/list ([formal (syntax->list #'(formals ...))]
                                   [b1 (syntax->list #'(body ...))]
                                   [b (syntax->list #'((body* ...) ...))])
                          (define-values (formals* env*) (parse-formals formal env))
                          (list formals*
                                (for/list ([b* (syntax->list b)])
                                  (parse-expr b* env*))
                                (parse-expr b1 env*)))
                   [`((,formal ,body* ,body) ...)
                    `(case-lambda (,formal ,body* ... ,body) ...)])]
                [(if test tbranch fbranch)
                 `(if ,(parse-expr #'test env)
                      ,(parse-expr #'tbranch env)
                      ,(parse-expr #'fbranch env))]
                [(begin body* ... body)
                 `(begin ,(for/list ([b (syntax->list #'(body* ...))])
                            (parse-expr b env)) ...
                         ,(parse-expr #'body env))]
                [(begin0 body* ... body)
                 `(begin0 ,(for/list ([b (syntax->list #'(body* ...))])
                             (parse-expr b env)) ...
                          ,(parse-expr #'body env))]
                [(let-values ([(ids:id ...) val] ...)
                   body* ... body)
                 (define env* (extend-env env
                                          (apply
                                           append
                                           (map syntax->list (syntax->list #'((ids ...) ...))))))
                 (match (for/list ([i (syntax->list #'((ids ...) ...))]
                                   [v (syntax->list #'(val ...))])
                          (list (map (lookup-env env*) (syntax->list i))
                                (parse-expr v env)))
                   [`([(,args ...) ,exp] ...)
                    `(let-values ([(,args ...) ,exp] ...)
                       ,(for/list ([b (syntax->list #'(body* ...))])
                          (parse-expr b env*)) ...
                       ,(parse-expr #'body env*))])]
                [(letrec-values ([(ids:id ...) val] ...)
                   body* ... body)
                 (define env* (extend-env env
                                          (apply
                                           append
                                           (map syntax->list (syntax->list #'((ids ...) ...))))))
                 (match (for/list ([i (syntax->list #'((ids ...) ...))]
                                   [v (syntax->list #'(val ...))])
                          (list (map (lookup-env env*) (syntax->list i))
                                (parse-expr v env*)))
                   [`([(,args ...) ,exp] ...)
                    `(letrec-values ([(,args ...) ,exp] ...)
                       ,(for/list ([b (syntax->list #'(body* ...))])
                          (parse-expr b env*)) ...
                       ,(parse-expr #'body env*))])]
                [(set! id:id body)
                 `(set! ,(parse-expr #'id env) ,(parse-expr #'body env))]
                [(quote datum)
                 `(quote ,(syntax->datum #'datum))]
                [(with-continuation-mark key val result)
                 `(with-continuation-mark ,(parse-expr #'key) ,(parse-expr #'val)
                    ,(parse-expr #'result))]
                [(#%plain-app func body ...)
                 `(#%plain-app ,(parse-expr #'func env)
                               ,(for/list ([i (syntax->list #'(body ...))])
                                  (parse-expr i env)) ...)]
                [(#%top . id:id)
                 `(#%top . ,(parse-expr #'id env))]
                [(#%variable-reference . id:id)
                 `(#%variable-reference ,(parse-expr #'id env))]
                [(#%variable-reference (#%top . id:id))
                 `(#%variable-reference-top (,((lookup-env env) #'id)))]
                [(#%variable-reference)
                 `(#%variable-reference)]))

  (parse-formals : * (formals env) -> formals (env)
                (syntax-parse formals
                  [(ids:id ...)
                   (define env* (extend-env env (syntax->list #'(ids ...))))
                   (values
                    `(,(for/list ([i (syntax->list #'(ids ...))])
                         (parse-expr i env*)) ...)
                    env*)]
                  [(id:id ids:id ... . rest:id)
                   (define env* (extend-env env (list* #'id #'rest (syntax->list #'(ids ...)))))
                   (values
                    `(,(parse-expr #'id env*)
                      ,(for/list ([i (syntax->list #'(ids ...))])
                         (parse-expr i env*)) ...
                      . ,(parse-expr #'rest env*))
                    env*)]
                  [rest:id
                   (define env* (extend-env env (list #'rest)))
                   (values (parse-expr #'rest env*) env*)]))

  (parse-top form initial-env))

(module+ test
  (define-compiler-test Lsrc top-level-form
    (check-equal?
     (compile/1 #'(lambda (x) x))
     `(#%expression (#%plain-lambda (x.1) x.1)))
    (check-equal?
     (compile/1 #'(module outer racket
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
                     ((#%plain-app + '1 '2)))
         (#%plain-app + '3 '4)
         (submodule pre racket
                    ((#%plain-app + '5 '6))))))
    (check-equal?
     (compile/1 #'(lambda (a b . c)
                    (apply + a b c)))
     `(#%expression (#%plain-lambda (a.1 b.3 . c.2)
                                    (#%plain-app apply + a.1 b.3 c.2))))))

(define-pass make-begin-explicit : Lsrc (e) -> L1 ()
  (Expr : expr (e) -> expr ()
        [(#%plain-lambda ,[formals] ,[expr*] ... ,[expr])
         (if (= (length expr*) 0)
             `(#%plain-lambda ,formals ,expr)
             `(#%plain-lambda ,formals (begin ,expr* ... ,expr)))]
        [(case-lambda (,formals ,expr* ... ,expr))
         (with-output-language (Lsrc expr)
           (make-begin-explicit `(#%plain-lambda ,formals ,expr* ... ,expr)))]
        [(case-lambda (,formals ,expr* ... ,expr) ...)
         `(case-lambda ,(for/list ([f (in-list formals)]
                                   [e* (in-list expr*)]
                                   [e (in-list expr)])
                          (with-output-language (Lsrc expr)
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

(module+ test
  (define-compiler-test L1 top-level-form
    (check-equal?
     (compile/2 #'(case-lambda [(x) (+ x 1) (begin0 x (set! x 42))]))
     `(#%plain-lambda (x.1)
                      (begin (#%plain-app + x.1 '1)
                             (begin0 x.1
                               (set! x.1 '42)))))
    (check-equal?
     (compile/2 #'(case-lambda [(x) (+ x 1)]
                               [(x y) x (+ x y)]))
     `(case-lambda (#%plain-lambda (x.1) (#%plain-app + x.1 '1))
                   (#%plain-lambda (x.2 y.3) (begin x.2 (#%plain-app + x.2 y.3)))))))

(define-pass identify-assigned-variables : L1 (e) -> L2 ()
  (definitions
    (define-syntax-rule (formals->identifiers* fmls)
      (formals->identifiers L2 fmls)))
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

(module+ test
  (define-compiler-test L2 top-level-form
    (check-equal?
     (compile/3 #'(letrec ([y 8])
                    y))
     `(letrec-values ([(y.1) '8])
        (assigned ()
          y.1)))
    (check-equal?
     (compile/3 #'(let ([x 8])
                    (set! x 5)
                    (+ x 42)))
     `(let-values ([(x.1) '8])
        (assigned (x.1)
                  (begin (set! x.1 '5)
                         (#%plain-app + x.1 '42)))))
    (check-equal?
     (compile/3 #'(let ([x 1])
                    (letrec ([y (lambda (x) y)])
                      (+ x y))))
     `(let-values ([(x.1) '1])
        (assigned ()
          (letrec-values ([(y.2) (#%plain-lambda (x.3) (assigned () y.2))])
            (assigned ()
                      (#%plain-app + x.1 y.2))))))
    (check-equal?
     (compile/3 #'(lambda x
                    (set! x 42)
                    x))
     `(#%expression (#%plain-lambda x.1
                                    (assigned (x.1)
                                              (begin
                                                (set! x.1 '42)
                                                x.1)))))))

(define-pass purify-letrec : L2 (e) -> L3 ()
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

(define-pass optimize-direct-call : L3 (e) -> L3 ()
  (Expr : expr (e) -> expr ()
        [(#%plain-app (#%plain-lambda (,id ...) ,[abody])
                      ,[expr* -> expr*] ...)
         (guard (= (length id) (length expr*)))
         `(let ([,id ,expr*] ...)
            (begin-set!
              ,abody))]))

(module+ test
  (define-compiler-test L3 top-level-form
    (check-equal?
     (compile/5 #'((lambda (x) x) (lambda (y) y)))
     `(let ([x.2 (#%plain-lambda (y.1) (assigned () y.1))])
        (begin-set!
          (assigned () x.2))))
    (check-equal?
     (compile/5 #'(letrec-values ([(a) (lambda (x) b)]
                                  [(b) (lambda (y) a)])
                    (a b)))
     `(letrec ([a.1 (#%plain-lambda (x.3) (assigned () b.2))]
               [b.2 (#%plain-lambda (y.4) (assigned () a.1))])
        (#%plain-app a.1 b.2)))
    (check-equal?
     (compile/5 #'(letrec-values ([(a) 5]
                                  [(b c) (values 6 7)])
                    (+ a b c)))
     `(let ([a.1 (undefined)]
            [b.2 (undefined)]
            [c.3 (undefined)])
        (begin-set!
          (set!-values (a.1) '5)
          (set!-values (b.2 c.3) (#%plain-app values '6 '7))
          (assigned (c.3 b.2 a.1)
                    (#%plain-app + a.1 b.2 c.3)))))
    (check-equal?
     (compile/5 #'(let ([x (if #t 5 6)])
                    (set! x (+ x 1))))
     `(let ([x.1 (if '#t '5 '6)])
        (begin-set!
          (assigned (x.1) (set!-values (x.1) (#%plain-app + x.1 '1))))))
    (check-equal?
     (compile/5 #'(let-values ([(x y) (values 1 2)]
                               [(z) 3])
                    (set! x 5)
                    (+ y z)))
     `(let ([x.1 (undefined)]
            [y.2 (undefined)]
            [z.3 (undefined)])
        (begin-set!
          (set!-values (x.1 y.2) (#%plain-app values '1 '2))
          (set!-values (z.3) '3)
          (assigned (x.1)
                    (begin
                      (set!-values (x.1) '5)
                      (#%plain-app + y.2 z.3))))))
    (check-equal?
     (compile/5 #'(let-values ([(x y) (values 1 2)])
                    (set! x y)
                    y))
     `(let ([x.1 (undefined)]
            [y.2 (undefined)])
        (begin-set!
          (set!-values (x.1 y.2) (#%plain-app values '1 '2))
          (assigned (x.1)
                    (begin
                      (set!-values (x.1) y.2)
                      y.2)))))))

(define-pass convert-assignments : L3 (e) -> L4 ()
  (definitions
    (define ((lookup-env env) x)
      (dict-ref env x x))
    (define (extend-env env assigned*)
      ;(define temp* (map (fresh) assigned*))
      (define temp* assigned*)
      (append (map cons assigned* temp*) env))
    (with-output-language (L4 expr)
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

(module+ test
  (define-compiler-test L4 top-level-form
    (check-equal?
     (compile/6 #'(let ([x 5])
                    (set! x 6)
                    x))
     `(let ([x.1 '5])
        (begin
          (set!-values (x.1) (#%box x.1))
          (begin
            (set!-boxes (x.1) '6)
            (#%unbox x.1)))))
    (check-equal?
     (compile/6 #'(lambda (x y)
                    (set! x 5)
                    (list x y)))
     `(#%expression (#%plain-lambda (x.1 y.2)
                                    (begin
                                      (set!-values (x.1) (#%box x.1))
                                      (begin
                                        (set!-boxes (x.1) '5)
                                        (#%plain-app list (#%unbox x.1) y.2))))))
    (check-equal?
     (compile/6 #'(lambda x
                    (let ()
                      (set! x 42)
                      (+ x 8))))
     `(#%expression (#%plain-lambda x.1
                                    (begin
                                      (set!-values (x.1) (#%box x.1))
                                      (begin
                                        (set!-boxes (x.1) '42)
                                        (#%plain-app + (#%unbox x.1) '8))))))
    (check-equal?
     (compile/6 #'(let-values ([(x y) (values 1 2)])
                    (set! x y)
                    y))
     `(let ([x.1 (undefined)]
            [y.2 (undefined)])
        (begin
          (set!-values (x.1 y.2) (#%plain-app values '1 '2))
          (begin
            (set!-values (x.1) (#%box x.1))
            (begin
              (set!-boxes (x.1) y.2)
              y.2)))))))

(define-pass uncover-free : L4 (e) -> L5 ()
  (definitions
    (define-syntax-rule (formals->identifiers* formals)
      (formals->identifiers L5 formals)))
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
                                (set-subtract free-global id))]
                       [(define-syntaxes (,id ...) ,[expr free-local free-global])
                        (values `(define-syntaxes (,id ...) ,expr)
                                free-local
                                (set-subtract free-global id))])
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
        [(#%variable-reference ,id)
         (if (set-member? env id)
             (values `(#%variable-reference ,id) (list id) '())
             (values `(#%variable-reference ,id) '() (list id)))]
        [(#%variable-reference-top (,id))
         (values `(#%variable-reference-top (,id)) '() (list id))]
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
  (SubmoduleForm : submodule-form (e env) -> submodule-form ('() '()))
  (let-values ([(e* local* global*) (TopLevelForm e '())])
    e*))

(module+ test
  (define-compiler-test L5 top-level-form
    (check-equal?
     (compile/7 #'(lambda (x)
                    (lambda (y)
                      x)))
     `(#%expression
       (#%plain-lambda (x.1)
                       (free () ()
                             (#%plain-lambda (y.2)
                                             (free (x.1) ()
                                                   x.1))))))
    (check-equal?
     (compile/7 #'(let ([x 5])
                    (lambda (y)
                      x)))
     `(let ([x.1 '5])
        (#%plain-lambda (y.2)
                        (free (x.1) ()
                              x.1))))
    (check-equal?
     (compile/7 #'(begin
                    (define x 5)
                    (lambda y (if x 4 5))))
     `(begin*
        (define-values (x) '5)
        (#%expression
         (#%plain-lambda y.1
                         (free () (x)
                               (if (#%top . x) '4 '5))))))
    (check-equal?
     (compile/7 #'(begin
                    (define x 5)
                    (set! x 6)))
     `(begin*
        (define-values (x) '5)
        (set!-values (x) '6)))
    (check-equal?
     (compile/7 #'(letrec ([f (lambda (x) x)])
                    (f 12)))
     `(letrec ([f.1 (#%plain-lambda (x.2) (free () () x.2))])
        (#%plain-app f.1 '12)))))

;(define-pass closurify-letrec : L5 (e) -> L6 ())

(define-pass void-lets : L5 (e) -> L6 ()
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

(module+ test
  (define-compiler-test L6 top-level-form
    (check-equal?
     (compile/8 #'(let ([x 1]) x))
     `(let ([x.1 '1]) x.1))
    (check-equal?
     (compile/8 #'(let ([x 1]
                        [y 2])
                    (+ x y)))
     `(let-void (x.1 y.2)
                (begin
                  (set!-values (x.1) '1)
                  (set!-values (y.2) '2)
                  (#%plain-app + x.1 y.2))))
    (check-equal?
     (compile/8 #'(let-values ([(x y) (values 1 2)]
                               [(z) 3])
                    (set! x 5)
                    (+ x y z)))
     `(let-void (x.1 y.2 z.3)
                (begin
                  (set!-values (x.1 y.2) (#%plain-app values '1 '2))
                  (set!-values (z.3) '3)
                  (begin
                    (set!-values (x.1) (#%box x.1))
                    (begin
                      (set!-boxes (x.1) '5)
                      (#%plain-app + (#%unbox x.1) y.2 z.3))))))
    (check-equal?
     (compile/8 #'(let ([x 5])
                    (lambda (y)
                      (set! x 6)
                      (+ x y))))
     `(let ([x.1 '5])
        (begin
          (set!-values (x.1) (#%box x.1))
          (#%plain-lambda (y.2)
                          (free (x.1) (+)
                                (begin
                                  (set!-boxes (x.1) '6)
                                  (#%plain-app + (#%unbox x.1) y.2)))))))))

(define-pass debruijn-indices : L6 (e) -> L7 ()
  (definitions
    (define-syntax-rule (formals->identifiers* fmls)
      (formals->identifiers L6 fmls))
    (define-syntax-rule (formals-rest?* fmls)
      (formals-rest? L6 fmls))
    (define (extend-env env start ids)
      (for/fold ([env env] [ref start])
                ([i ids])
        (values (dict-set env i (+ ref 1)) (+ ref 1))))
    (define (lookup-env env id)
      (dict-ref env id))
    (define ((var->index env frame) id)
      (if (dict-has-key? env id)
          (- frame (lookup-env env id))
          (with-output-language (L7 binding)
            `(primitive ,(dict-ref primitive-table* id)))))
    ;; Convert a list of identifiers to it's range and offset
    ;; (valid because list ids should be consecutive
    ;; (list symbol) -> (values exact-nonnegative-integer exact-nonnegative-integer)
    (define (ids->range env frame ids)
      (define indices (map (var->index env frame) ids))
      (values (length indices) (car indices))))
  (Lambda : lambda (e [env '()] [frame 0]) -> lambda ()
          [(#%plain-lambda ,formals
                           (free (,id2 ...) (,id3 ...)
                                 ,expr))
           (define params (formals->identifiers* formals))
           (define rest? (formals-rest?* formals))
           (define-values (env* frame*) (extend-env env frame (reverse (append id2 params))))
           `(#%plain-lambda ,(length params)
                            ,rest?
                            (,(map (var->index env frame) id2) ...)
                            (,(map (var->index env frame) id3) ...)
                            ,(Expr expr env* frame*))])
  (Expr : expr (e [env '()] [frame 0]) -> expr ()
        [,id ((var->index env frame) id)]
        [(#%box ,id) `(#%box ,((var->index env frame) id))]
        [(#%unbox ,id) `(#%unbox ,((var->index env frame) id))]
        [(set!-values (,id ...) ,[expr])
         (define-values (count offset) (ids->range env frame id))
         `(set!-values ,count ,offset ,expr)]
        [(set!-boxes (,id ...) ,[expr])
         (define-values (count offset) (ids->range env frame id))
         `(set!-boxes ,count ,offset ,expr)]
        [(#%top . ,id) `(#%top . 0)] ;; TODO: Global Vars
        [(#%variable-reference-top (,id)) `(#%variable-reference-top (0))] ;; TODO: Global vars
        [(#%variable-reference ,id) `(#%variable-reference ,((var->index env frame) id))]
        [(let ([,id ,[expr1]])
           ,expr)
         (define-values (env* frame*) (extend-env env frame (list id)))
         `(let-one ,expr1 ,(Expr expr env* frame*))]
        [(let-void (,id ...)
                   ,expr)
         (define-values (env* frame*) (extend-env env frame (reverse id)))
         `(let-void ,(length id)
                    ,(Expr expr env* frame*))]
        [(letrec ([,id ,[lambda]] ...)
           ,[expr])
         `(letrec (,lambda ...)
            ,expr)]
        [(#%plain-app ,expr ,expr* ...)
         (define expr1 (Expr expr env (+ frame (length expr*))))
         (define expr*1 (map (lambda (e) (Expr e env (+ frame (length expr*)))) expr*))
         `(#%plain-app ,expr1 ,expr*1 ...)]))

(module+ test
  (define-compiler-test L7 top-level-form
    (check-equal?
     (compile/9 #'(lambda (x) x))
     `(#%expression (#%plain-lambda 1 #f () () 0)))
    (check-equal?
     (compile/9 #'(let ([x 5])
                    (lambda (y . z) x)))
     `(let-one '5 (#%plain-lambda 2 #t (0) () 0)))
    (check-equal?
     (compile/9 #'(let ([x 5]
                        [y 6])
                    (+ x y)))
     `(let-void 2
                (begin
                  (set!-values 1 0 '5)
                  (set!-values 1 1 '6)
                  (#%plain-app (primitive 247) 2 3))))))

(define-pass find-let-depth : L7 (e) -> L8 ()
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
        [(case-lambda ,[lambda depth] ...)
         (values `(case-lambda ,lambda ...)
                 (apply max 0 depth))]
        [(if ,[expr1 depth1] ,[expr2 depth2] ,[expr3 depth3])
         (values `(if ,expr1 ,expr2 ,expr3)
                 (max depth1 depth2 depth3))]
        [(with-continuation-mark ,[expr1 depth1] ,[expr2 depth2] ,[expr3 depth3])
         (values `(with-continuation-mark ,expr1 ,expr2 ,expr3)
                 (max depth1 depth2 depth3))]
        [(#%plain-app ,[expr depth] ,[expr* depth*] ...)
         (values `(#%plain-app ,expr ,expr* ...)
                 (+ (length depth*) (apply max depth depth*)))])
  (TopLevelForm : top-level-form (e) -> top-level-form (0)
                [(#%expression ,[expr depth])
                 (values `(#%expression ,expr) depth)]
                [(module ,id ,module-path (,[module-level-form depth] ...))
                 (values `(module ,id ,module-path (,module-level-form ...))
                         (apply max 0 depth))]
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
  [SubmoduleForm : submodule-form (e) -> module-level-form (0)
                 [(submodule ,id ,module-path (,[module-level-form depth] ...))
                  (values `(submodule ,id ,module-path (,module-level-form ...))
                          (apply max 0 depth))]
                 [(submodule* ,id ,module-path (,[module-level-form depth] ...))
                  (values `(submodule* ,id ,module-path (,module-level-form ...))
                          (apply max 0 depth))]
                 [(submodule* ,id (,[module-level-form depth] ...))
                  (values `(submodule* ,id (,module-level-form ...))
                          (apply max 0 depth))]]
  (GeneralTopLevelForm : general-top-level-form (e) -> general-top-level-form (0)
                       [(define-values (,id ...) ,[expr depth])
                        (values `(define-values (,id ...) ,expr) depth)]
                       [(define-syntaxes (,id ...) ,[expr depth])
                        (values `(define-syntaxes (,id ...) ,expr) depth)])
  (let-values ([(top depth) (TopLevelForm e)])
    `(program ,depth ,top)))

(module+ test
  (define-compiler-test L8 compilation-top
    (check-equal?
     (compile/10 #'(lambda (x) (let ([y 5]) (+ x y))))
     `(program 1 (#%expression
                  (#%plain-lambda 1 #f () ((primitive 247)) 11 (let-one '5 (#%plain-app (primitive 247) 3 2))))))
    (check-equal?
     (compile/10 #'(if (= 5 6)
                       (let ([x '5]
                             [y '6])
                         y)
                       (let ([x '6])
                         x)))
     `(program 2 (if (#%plain-app (primitive 256) '5 '6)
                     (let-void 2
                               (begin
                                 (set!-values 1 0 '5)
                                 (set!-values 1 1 '6)
                                 1))
                     (let-one '6 0))))))

(define tmp-prefix
  (zo:prefix 0 '() '() 'missing))

(define-pass generate-zo-structs : L8 (e) -> * ()
  (definitions
    (define zo-void
      (zo:primval 35)))
  (CompilationTop : compilation-top (e) -> * ()
                  [(program ,eni ,top-level-form)
                   (zo:compilation-top eni (hash) tmp-prefix (TopLevelForm top-level-form))])
  (TopLevelForm : top-level-form (e) -> * ()
                [(#%expression ,expr)
                 (Expr expr)]
                [(module ,id ,module-path (,module-level-form ...))
                 (void)]
                [(begin* ,top-level-form ...)
                 (void)]
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
                 [(submodule ,id ,module-path (,module-level-form ...))
                  (void)]
                 [(submodule* ,id ,module-path (,module-level-form ...))
                  (void)]
                 [(submodule* ,id (,module-level-form ...))
                  (void)])
  (GeneralTopLevelForm : general-top-level-form (e) -> * ()
                       [(define-values (,id ...) ,expr)
                        (void)]
                       [(define-syntaxes (,id ...) ,expr)
                        (void)]
                       [(#%require ,raw-require-spec ...)
                        (void)])
  [Binding : binding (e) -> * ()
           [,eni eni]
           [(primitive ,eni)
            (zo:primval eni)]]
  (Expr : expr (e) -> * ()
        [,eni (zo:localref #f eni #f #f #f)]
        [(primitive ,eni)
         (zo:primval eni)]
        [(#%variable-reference-top (,eni))
         (void)]
        [(#%variable-reference ,eni)
         (void)]
        [(#%top . ,eni) (void)]
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
        ;[(letrec (,lambda) ,expr)
        ; (zo:closure (Lambda lambda)
        ;             (gensym))]
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
        [(#%variable-reference)
         (void)])
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
                   #f
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
                                (fact 5))))
         all-compiler-tests)))

(define-syntax (define-compiler stx)
  (syntax-parse stx
    [(_ name:id passes* ...+)
     (define passes (reverse (syntax->list #'(passes* ...))))
     #`(begin (define name (compose #,@passes))
              (begin ;(module+ test
                #,@(let build-partial-compiler ([passes passes]
                                                [pass-count (length passes)])
                     (if (= pass-count 0)
                         '()
                         (with-syntax ([name* (format-id stx "~a/~a" #'name (- pass-count 1))])
                           (cons #`(define name* (compose #,@passes))
                                 (if (identifier? (car passes))
                                     (with-syntax ([name** (format-id stx
                                                                      "~a/~a"
                                                                      #'name
                                                                      (car passes))])
                                       (cons #`(define name** name*)
                                             (build-partial-compiler (cdr passes) (- pass-count 1))))
                                     (build-partial-compiler (cdr passes) (- pass-count 1)))))))))]))

(define (expand-syntax* stx)
  (parameterize ([current-namespace (make-base-namespace)])
    (expand-syntax stx)))

(define-compiler compile
  expand-syntax*
  parse-and-rename
  make-begin-explicit
  identify-assigned-variables
  purify-letrec
  optimize-direct-call
  convert-assignments
  uncover-free
  void-lets
  debruijn-indices
  find-let-depth
  generate-zo-structs
  zo-marshal)

(module+ test
  (run-all-compiler-tests))
