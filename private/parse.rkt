#lang racket/base

(provide parse)

(require racket/pretty)

(require syntax/parse
         "structs.rkt")

(define initial-env (hash))

(define (extend-env env vars)
  (for/fold ([acc env])
            ([var vars])
    (define var* (syntax->datum var))
    (hash-set acc var* (gensym var*))))

(define (lookup-env env var)
  (hash-ref env (syntax->datum var)
            (lambda ()
              (define binding (identifier-binding var))
              (if (pair? binding)
                  (syntax->datum var)
                  (error "Not bound" var)))))

(define (parse form)
  (parse-top form initial-env))

(define (parse-top form env)
  (syntax-parse form
    #:literals (#%expression module #%plain-module-begin begin begin-for-syntax)
    [(#%expression body)
     (topexpr (parse-expr #'body env))]
    [(module id:id path
       (#%plain-module-begin body ...))
     (define env* (extend-env env (list #'id)))
     (topmod (parse-expr #'id env*) (syntax->datum #'path)
             (for/list ([i (syntax->list #'(body ...))])
               (parse-mod i env*)))]
    [(begin body ...)
     (topbeg (for/list ([i (syntax->list #'(body ...))])
               (parse-top i env)))]
    [(begin-for-syntax body ...)
     (topbegfs (for/list ([i (syntax->list #'(body ...))])
                 (parse-top i env)))]
    [else
     (topgenform (parse-gen #'else env))]))

(define (parse-mod form env)
  (syntax-parse form
    #:literals (#%provide begin-for-syntax #%declare module module*
                          #%plain-module-begin)
    [(#%provide spec ...)
     (pro (syntax->list #'(spec ...)))]
    [(begin-for-syntax body ...)
     (modbegfs (for/list ([i (syntax->list #'(body ...))])
                 (parse-mod i env)))]
    [(#%declare keyword ...)
     (decl (syntax->list #'(keyword ...)))]
    [(module id:id path
       (#%plain-module-begin body ...))
     (define env* (extend-env env (list #'id)))
     (submod (parse-expr #'id env*) (syntax->datum #'path)
             (for/list ([i (syntax->list #'(body ...))])
               (parse-mod i env*)))]
    [(module* id:id path
       (#%plain-module-begin body ...))
     (define env* (extend-env env (list #'id)))
     (submod* (parse-expr #'id env*) (syntax->datum #'path)
              (for/list ([i (syntax->list #'(body ...))])
                (parse-mod i env*)))]
    [else
     (modgenform (parse-gen #'else env))]))

(define (parse-gen form env)
  (syntax-parse form
    #:literals (define-values define-syntaxes #%require)
    [(define-values (id:id ...) body)
     (define env* (extend-env env (for/list ([i (syntax->list #'(id ...))]) i)))
     (defv (for/list ([i (syntax->list #'(id ...))])
             (parse-expr i env*))
       (parse-expr #'body env*))]
    [(define-syntaxes (id:id ...) body)
     (define env* (extend-env env (for/list ([i (syntax->list #'(id ...))]) i)))
     (defsyntaxs (for/list ([i (syntax->list #'(id ...))])
                    (parse-expr i env*))
       (parse-expr #'body env*))]
    [(#%require spec ...)
     (req (syntax->list #'(spec ...)))]
    [else
     (parse-expr #'else env)]))

(define (parse-expr form env)
  (syntax-parse form
    #:literals (#%plain-lambda case-lambda if begin begin0 let-values
                letrec-values set! quote quote-syntax with-continuation-mark
                #%plain-app #%top #%variable-reference)
    [id:id (ide (lookup-env env #'id)
                (identifier-binding #'id)
                (syntax->datum #'id))]
    [(#%plain-lambda formals body ...+)
     (parse-lambda #'formals #'(body ...) env)]
    [(case-lambda (formals body ...+) ...)
     (caselam
      (for/list ([formal (syntax->list #'(formals ...))]
                 [b (syntax->list #'((body ...) ...))])
        (parse-lambda formal b)))]
    [(if test tbranch fbranch)
     (branch (parse-expr #'test env)
             (parse-expr #'tbranch env)
             (parse-expr #'fbranch env))]
    [(begin body ...+)
     (beg (for/list ([b (syntax->list #'(body ...))])
            (parse-expr b env)))]
    [(begin0 body ...+)
     (beg0 (for/list ([b (syntax->list #'(body ...))])
             (parse-expr b env)))]
    [(let-values ([(ids:id ...) val] ...)
       body ...+)
     (define env* (extend-env env
                              (apply
                               append
                               (for/list ([i (syntax->list #'((ids ...) ...))])
                                 (for/list ([i* (syntax->list i)])
                                   i*)))))
     (letv (for/list ([i (syntax->list #'((ids ...) ...))]
                      [v (syntax->list #'(val ...))])
             (defv (for/list ([i* (syntax->list i)])
                     (parse-expr i* env*))
               (parse-expr v env)))
           (beg (for/list ([b (syntax->list #'(body ...))])
                  (parse-expr b env*))))]
    [(letrec-values ([(ids:id ...) val] ...)
       body ...+)
     (define env* (extend-env env
                              (apply
                               append
                               (for/list ([i (syntax->list #'((ids ...) ...))])
                                 (for/list ([i* (syntax->list i)])
                                   i*)))))
     (letrecv (for/list ([i (syntax->list #'((ids ...) ...))]
                         [v (syntax->list #'(val ...))])
                (defv (for/list ([i* (syntax->list i)])
                        (parse-expr i* env*))
                  (parse-expr v env*)))
              (beg (for/list ([b (syntax->list #'(body ...))])
                     (parse-expr b env*))))]
    [(set! id:id body)
     (setv (list (parse-expr #'id env)) (parse-expr #'body env))]
    [(quote datum)
     (quo (syntax->datum #'datum))]
    [(with-continuation-mark key val result)
     (withcm (parse-expr #'key) (parse-expr #'val) (parse-expr #'result))]
    [(#%plain-app func body ...)
     (app (parse-expr #'func env)
          (for/list ([i (syntax->list #'(body ...))])
            (parse-expr i env)))]
    [(#%top . id:id)
     (top (parse-expr #'id env))]
    [(#%variable-reference . id:id)
     (varref (parse-expr #'id env))]
    [(#%variable-reference (#%top . id:id))
     (varref (top (parse-expr #'id env)))]
    [(#%variable-reference)
     (varref #f)]))

(define (parse-lambda formals body env)
  (define (body* env)
    (for/list ([i (syntax->list body)])
      (parse-expr i env)))
  (syntax-parse formals
    [(ids:id ...)
     (define env* (extend-env env
                              (for/list ([i (syntax->list #'(ids ...))])
                                i)))
     (lam (for/list ([i (syntax->list #'(ids ...))])
            (parse-expr i env*))
          #f (beg (body* env*)))]
    [(ids:id ... . rest:id)
     (define env* (extend-env env
                              (append #'rest
                                      (for/list ([i (syntax->list #'(ids ...))])
                                        i))))
     (lam (for ([i (syntax->list #'(ids ...))])
            (parse-expr i env*))
          (parse-expr #'rest env*) (beg (body* env*)))]
    [rest:id
     (define env* (extend-env env #'rest))
     (lam null (parse-expr #'rest env*) (beg (body* env*)))]))
