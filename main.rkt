#lang racket/base

(require racket/match
         racket/pretty
         syntax/parse
         compiler/zo-marshal
         (prefix-in zo: compiler/zo-structs)
         "structs.rkt")

(define cc (current-compile))

(define (parse-top form)
  (syntax-parse form
    #:literals (#%expression module #%plain-module-begin begin begin-for-syntax)
    [(#%expression body)
     (topexpr (parse-expr #'body))]
    [(module id:id path
       (#%plain-module-begin body ...))
     (topmod #'id (syntax->datum #'path)
             (for/list ([i (syntax->list #'(body ...))])
               (parse-mod i)))]
    [(begin body ...)
     (topbeg (for/list ([i (syntax->list #'(body ...))])
               (parse-top i)))]
    [(begin-for-syntax body ...)
     (topbegfs (for/list ([i (syntax->list #'(body ...))])
                 (parse-top i)))]
    [else
     (topgenform (parse-gen #'else))]))

(define (parse-mod form)
  (syntax-parse form
    #:literals (#%provide begin-for-syntax #%declare module module*
                          #%plain-module-begin)
    [(#%provide spec ...)
     (pro (syntax->list #'(spec ...)))]
    [(begin-for-syntax body ...)
     (modbegfs (for/list ([i (syntax->list #'(body ...))])
                 (parse-mod i)))]
    [(#%declare keyword ...)
     (decl (syntax->list #'(keyword ...)))]
    [(module id:id path
       (#%plain-module-begin body ...))
     (submod #'id (syntax->datum #'path)
             (for/list ([i (syntax->list #'(body ...))])
               (parse-mod i)))]
    [(module* id:id path
       (#%plain-module-begin body ...))
     (submod* #'id (syntax->datum #'path)
              (for/list ([i (syntax->list #'(body ...))])
                (parse-mod i)))]
    [else
     (modgenform (parse-gen #'else))]))

(define (parse-gen form)
  (syntax-parse form
    #:literals (define-values define-syntaxes #%require)
    [(define-values (id:id ...) body)
     (defv (syntax->list #'(id ...)) (parse-expr #'body))]
    [(define-syntaxes (id:id ...) body)
     (defsyntaxs (syntax->list #'(id ...)) (parse-expr #'body))]
    [(#%require spec ...)
     (req (syntax->list #'(spec ...)))]
    [else
     (parse-expr #'else)]))

(define (parse-expr form)
  (syntax-parse form
    #:literals (#%plain-lambda case-lambda if begin begin0 let-values
                letrec-values set! quote quote-syntax with-continuation-mark
                #%plain-app #%top #%variable-reference)
    [id:id (ide #'id)]
    [(#%plain-lambda formals body ...+)
     (parse-lambda #'formals #'(body ...))]
    [(case-lambda (formals body ...+) ...)
     (caselam
      (for/list ([formal (syntax->list #'(formals ...))]
                 [b (syntax->list #'((body ...) ...))])
        (parse-lambda formal b)))]
    [(if test tbranch fbranch)
     (branch (parse-expr #'test) (parse-expr #'tbranch) (parse-expr #'fbranch))]
    [(begin body ...+)
     (beg (for/list ([b (syntax->list #'(body ...))])
            (parse-expr b)))]
    [(begin0 body ...+)
     (beg0 (for/list ([b (syntax->list #'(body ...))])
             (parse-expr b)))]
    [(let-values ([(ids:id ...) val] ...)
       body ...+)
     (letv (for/list ([i (syntax->list #'((ids ...) ...))]
                      [v (syntax->list #'(val ...))])
             (defv (syntax->list i) (parse-expr v)))
           (for/list ([b (syntax->list #'(body ...))])
             (parse-expr b)))]
    [(letrec-values ([(ids:id ...) val] ...)
       body ...+)
     (letrecv (for/list ([i (syntax->list #'((ids ...) ...))]
                         [v (syntax->list #'(val ...))])
                (defv (syntax->list i) (parse-expr v)))
              (for/list ([b (syntax->list #'(body ...))])
                (parse-expr b)))]
    [(set! id:id body)
     (setv #'id (parse-expr #'body))]
    [(quote datum)
     (quo (syntax->datum #'datum))]
    [(with-continuation-mark key val result)
     (withcm (parse-expr #'key) (parse-expr #'val) (parse-expr #'result))]
    [(#%plain-app func body ...)
     (app (parse-expr #'func)
          (for/list ([i (syntax->list #'(body ...))])
            (parse-expr i)))]
    [(#%top . id:id)
     (top #'id)]
    [(#%variable-reference . id:id)
     (varref #'id:id)]
    [(#%variable-reference (#%top . id:id))
     (varref (top #'id))]
    [(#%variable-reference)
     (varref #f)]))

(define (parse-lambda formals body)
  (define body* (for/list ([i (syntax->list body)])
                  (parse-expr i)))
  (syntax-parse formals
    [(ids:id ...)
     (lam (syntax->list #'(ids ...)) #f body*)]
    [(ids:id ... . rest:id)
     (lam (syntax->list #'(ids ...)) #'rest body*)]
    [rest:id
     (lam null #'rest body*)]))

(define (new-cc form y)
  (define expanded-form (expand form))
  (define parsed (parse-top expanded-form))
  (pretty-write form)
  (cc form y))

(current-compile new-cc)
