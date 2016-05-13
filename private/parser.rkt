#lang racket/base

(provide parse-and-rename)

(require nanopass/base
         syntax/parse
         racket/match
         racket/dict
         racket/function
         "languages.rkt"
         "utils.rkt")

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
                            x))))))

;; Parse and alpha-rename expanded program
(define-pass parse-and-rename : * (form) -> Lsrc ()
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
                [(quote-syntax datum)
                 `(quote-syntax ,#'datum)]
                [(quote-syntax datum #:local)
                 `(quote-syntax-local ,#'datum)]
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
                               ,-1
                               ,(for/list ([i (in-list (syntax->list #'(phaseless-req-spec ...)))])
                                  (parse-phaseless-req-spec i env)) ...)]
                            [(for-label phaseless-req-spec ...)
                             `(for-meta
                               ,#f
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
                               `(all-except ,(parse-raw-module-path #'raw-module-path env)
                                            ,(map (curryr parse-expr env)
                                                  (syntax->list #'(ids ...))) ...)]
                              [(prefix-all-except id:id raw-module-path ids:id ...)
                               `(prefix-all-except
                                 ,(syntax-e #'id)
                                 ,(parse-raw-module-path #'raw-module-path env)
                                 ,(map (curryr parse-expr env) (syntax->list #'(ids ...))) ...)]
                              [(rename raw-module-path id1:id id2:id)
                               `(rename ,(parse-raw-module-path #'raw-module-path env)
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