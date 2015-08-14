#lang racket/base

(require nanopass/base
         syntax/parse
         racket/match
         racket/set
         (for-syntax racket/base
                     syntax/parse
                     racket/syntax))

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
  (define deterministic-fresh/count 0)
  (define (deterministic-fresh symb)
    (set! deterministic-fresh/count (+ deterministic-fresh/count 1))
    (string->symbol (format "~a.~a" symb deterministic-fresh/count)))
  (define all-compiler-tests '())
  (define-syntax (define-compiler-test stx)
    (syntax-parse stx
      [(_ lang body ...+)
       #:with with-output-language (format-id stx "with-output-language")
       #:with name (format-id stx "~a-tests" #'lang)
       #`(begin
           (define name
               (with-output-language (lang top-level-form)
                 (test-suite
                     (format "Test suite for: ~a" '#,(syntax->datum #'lang))
                   #:before (lambda () (set! deterministic-fresh/count 0))
                   (parameterize ([fresh deterministic-fresh])
                     (test-case (format "Test case for: ~a" '#,(syntax->datum #'lang))
                       (set! deterministic-fresh/count 0)
                       body) ...))))
           (set! all-compiler-tests (cons name all-compiler-tests)))]))
  (define-syntax-rule (run-all-compiler-tests)
    (map run-tests all-compiler-tests)))

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
                  (begin top-level-form ...)
                  (begin-for-syntax top-level-form ...))
  (module-level-form (module-level-form)
                     general-top-level-form
                     (#%provide raw-provide-spec ...)
                     (begin-for-syntax module-level-form ...)
                     submodule-form
                     (#%declare declaration-keyword ...))
  (submodule-form (submodule-form)
                  (module id module-path
                    (module-level-form ...))
                  (module* id module-path
                    (module-level-form ...))
                  (module* id
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
        (- (letrec-values ([(id ...) expr1] ...)
             abody))
        (+ (letrec ([id lambda])
             expr))))

;; Parse and alpha-rename expanded program
(define-pass parse-and-rename : * (form) -> Lsrc ()
  (definitions
    (define initial-env (hash))
    (define (extend-env env vars)
      (for/fold ([acc env])
                ([var vars])
        (define var* (syntax->datum var))
        (hash-set acc var* ((fresh) var*))))
    (define (lookup-env env var)
      (hash-ref env (syntax->datum var)
                (syntax->datum var))))

  (parse-top : * (form env) -> top-level-form ()
             (syntax-parse form
               #:literals (#%expression module #%plain-module-begin begin begin-for-syntax)
               [(#%expression body)
                `(#%expression ,(parse-expr #'body env))]
               [(module id:id path
                  (#%plain-module-begin body ...))
                (define env* (extend-env env (list #'id)))
                `(module ,(parse-expr #'id env*) ,(syntax->datum #'path)
                   (,(for/list ([i (syntax->list #'(body ...))])
                      (parse-mod i env*)) ...))]
               [(begin body ...)
                `(begin ,(for/list ([i (syntax->list #'(body ...))])
                           (parse-top i env)) ...)]
               [(begin-for-syntax body ...)
                `(begin-for-syntax ,(for/list ([i (syntax->list #'(body ...))])
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
                `(module ,(parse-expr #'id env*) ,(syntax->datum #'path)
                   (,(for/list ([i (syntax->list #'(body ...))])
                      (parse-mod i env*)) ...))]
               [(module* id:id path
                  (#%plain-module-begin body ...))
                (define env* (extend-env env (list #'id)))
                `(module* ,(parse-expr #'id env*) ,(syntax->datum #'path)
                   (,(for/list ([i (syntax->list #'(body ...))])
                       (parse-mod i env*)) ...))]
               [(module* id:id path
                  (#%plain-module-begin body ...))
                (define env* (extend-env env (list #'id)))
                `(module* ,(parse-expr #'id env*)
                    (,(for/list ([i (syntax->list #'(body ...))])
                       (parse-mod i env*)) ...))]
               [else
                (parse-gen #'else env)]))

  (parse-gen : * (form env) -> general-top-level-form ()
             (syntax-parse form
               #:literals (define-values define-syntaxes #%require)
               [(define-values (id:id ...) body)
                (define env* (extend-env env (syntax->list #'(id ...))))
                `(define-values (,(for/list ([i (syntax->list #'(id ...))])
                                   (parse-expr i env*)) ...)
                   ,(parse-expr #'body env*))]
               [(define-syntaxes (id:id ...) body)
                (define env* (extend-env env (syntax->list #'(id ...))))
                `(define-syntaxes (,(for/list ([i (syntax->list #'(id ...))])
                                     (parse-expr i env*)) ...)
                   ,(parse-expr #'body env*))]
               [(#%require spec ...)
                `(#%require ,(syntax->list #'(spec ...)))]
               [else
                (parse-expr #'else env)]))

  (parse-expr : * (form env) -> expr ()
              (syntax-parse form
                #:literals (#%plain-lambda case-lambda if begin begin0 let-values letrec-values set!
                                           quote quote-syntax with-continuation-mark #%plain-app
                                           #%top #%variable-reference)
                [id:id (lookup-env env #'id)]
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
                   [`((,formal ,body* ... ,body) ...)
                    `(case-lambda (,formal ,body* ... ,body) ...)])]
                [(if test tbranch fbranch)
                 `(if ,(parse-expr #'test env)
                      ,(parse-expr #'tbranch env)
                      ,(parse-expr #'fbranch env))]
                [(begin body* ... body)
                 `(begin ,(for/list ([b (syntax->list #'(body* ...))])
                            (parse-expr b env))
                         ,(parse-expr #'body env))]
                [(begin0 body* ... body)
                 `(begin0 ,(for/list ([b (syntax->list #'(body* ...))])
                             (parse-expr b env))
                          ,(parse-expr #'body env))]
                [(let-values ([(ids:id ...) val] ...)
                   body* ... body)
                 (define env* (extend-env env
                                          (apply
                                           append
                                           (map syntax->list (syntax->list #'((ids ...) ...))))))
                 (match (for/list ([i (syntax->list #'((ids ...) ...))]
                                   [v (syntax->list #'(val ...))])
                          (list (for/list ([i* (syntax->list i)])
                                  (lookup-env env* i*))
                                (parse-expr v env*)))
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
                          (list (for/list ([i* (syntax->list i)])
                                  (lookup-env env* i*))
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
                 `(#%variable-reference-top (,(lookup-env env #'id)))]
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
                   (define env* (extend-env env (cons #'id (cons #'rest (syntax->list #'(ids ...))))))
                   (values
                    `(,(parse-expr #'id env* )
                      ,(for ([i (syntax->list #'(ids ...))])
                         (parse-expr i env*)) ...
                      . ,(parse-expr #'rest env*))
                    env*)]
                  [rest:id
                   (define env* (extend-env env (list #'rest)))
                   (values (parse-expr #'rest env*) env*)]))

  (parse-top form initial-env))

(module+ test
  (define-compiler-test Lsrc
    (check-equal?
     (compile/1 #'(lambda (x) x))
     `(#%expression (#%plain-lambda (x.1) x.1)))))

(define-pass make-begin-explicit : Lsrc (e) -> L1 ()
  (Expr : expr (e) -> expr ()
        [(#%plain-lambda ,[formals] ,[expr*] ... ,[expr])
         (if (= (length expr*) 0)
             `(#%plain-lambda ,formals ,expr)
             `(#%plain-lambda ,formals (begin ,expr* ... ,expr)))]
        [(case-lambda (,[formals] ,[expr*] ... ,[expr]))
         (with-output-language (Lsrc expr)
           (make-begin-explicit `(#%plain-lambda ,formals ,expr* ... ,expr)))]
        [(case-lambda (,[formals] ,[expr*] ... ,[expr]) ...)
         `(case-lambda ,(with-output-language (Lsrc expr)
                          (make-begin-explicit `(#%plain-lambda ,formals ,expr* ... ,expr))) ...)]
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

;(define-syntax-rule (formals->identifiers lang fmls)
(define-syntax-rule (formals->identifiers lang fmls)
  (nanopass-case (lang formals) fmls
                 [,id (list id)]
                 [(,id (... ...)) id]
                 [(,id ,id* (... ...) . ,id2) (set-union (list id id2) id*)]))

(define-pass identify-assigned-variables : L1 (e) -> L2 ()
  (definitions
    (define-syntax-rule (formals->identifiers* fmls)
      (formals->identifiers L2 fmls)))
  (Lambda : lambda (e) -> lambda ('())
          [(#%plain-lambda ,[formals] ,[expr assigned*])
           (values `(#%plain-lambda ,formals
                                    (assigned (,(set-intersect assigned* (formals->identifiers* formals)) ...) ,expr))
                   (set-remove assigned* (formals->identifiers* formals)))])
  (Expr : expr (e) -> expr ('())
        [(set! ,id ,[expr assigned*])
         (values `(set! id expr)
                 (set-add id assigned*))]
        [(let-values ([(,id ...) ,[expr assigned]] ...) ,[expr* assigned*])
         (values `(let-values ([(,id ...) ,expr] ...)
                    (assigned (,(set-intersect assigned* id) ...) ,expr*))
                 (apply set-union (set-remove assigned* id) assigned))]
        [(letrec-values ([(,id ...) ,[expr assigned]] ...) ,[expr* assigned*])
         (values `(letrec-values ([(,id ...) ,expr] ...)
                    (assigned (,(set-intersect assigned* id) ...) ,expr*))
                 (apply set-union (set-remove assigned* id) assigned))]
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
                 (apply set-union assigned))])
  ;; Also *should* really be generated
  (TopLevelForm : top-level-form (e) -> top-level-form ('())
                [(begin ,[top-level-form assigned] ...)
                 (values `(begin ,top-level-form ...)
                         (apply set-union assigned))]
                [(begin-for-syntax ,[top-level-form assigned] ...)
                 (values `(begin-for-syntax ,top-level-form ...)
                         (apply set-union assigned))]
                [(#%expression ,[expr assigned])
                 (values `(#%expression ,expr)
                         assigned)])
  (ModuleLevelForm : module-level-form (e) -> module-level-form ('())
                   [(begin-for-syntax ,[module-level-form assigned] ...)
                    (values `(begin-for-syntax ,module-level-form ...)
                            (apply set-union assigned))])
  (GeneralTopLevelForm : general-top-level-form (e) -> general-top-level-form ('())
                       [(define-values (,id ...) ,[expr assigned])
                        (values `(define-values (,id ...) ,expr)
                                (set-subtract assigned expr))]
                       [(define-syntaxes (,id ...) ,[expr assigned])
                        (values `(define-syntaxes (,id ...) ,expr)
                                (set-subtract assigned id))])
  (SubmoduleForm : submodule-form (e) -> submodule-form ('()))
  (let-values ([(e* free*) (TopLevelForm e)])
    e*))

(module+ test
  (define-compiler-test L2
    (check-equal?
     (compile/3 #'(letrec ([y 8])
                    y))
     `(letrec-values ([(y.1) '8])
        (assigned ()
          y.1)))
    (check-equal?
     (compile/3 #'(let ([x 1])
                    (letrec ([y (lambda (x) y)])
                      (+ x y))))
     `(let-values ([(x.1) '1])
        (assigned ()
          (letrec-values ([(y.2) (#%plain-lambda (x.3) (assigned () y.2))])
            (assigned ()
              (#%plain-app + x.1 y.2))))))))

(define-pass purify-letrec : L2 (e) -> L3 ())

(define-syntax (define-compiler stx)
  (syntax-parse stx
    [(_ name:id passes*:id ...+)
     (define passes (reverse (syntax->list #'(passes* ...))))
     #`(begin (define name (compose #,@passes))
              #,@(let build-partial-compiler ([passes passes]
                                              [pass-count (length passes)])
                   (if (= pass-count 0)
                       '()
                       (with-syntax ([name* (format-id stx "~a/~a" #'name (- pass-count 1))])
                         (cons #`(define name* (compose #,@passes))
                               (build-partial-compiler (cdr passes) (- pass-count 1)))))))]))

(define-compiler compile
  expand-syntax
  parse-and-rename
  make-begin-explicit
  identify-assigned-variables
  purify-letrec)

(module+ test
  (run-all-compiler-tests))
