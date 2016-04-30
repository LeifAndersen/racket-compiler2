#lang racket/base

(provide (rename-out [~inline-expressions inline-expressions]))

(require nanopass/base
         racket/match
         racket/set
         racket/dict
         racket/hash
         racket/port
         racket/list
         racket/function
         syntax/strip-context
         (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     racket/stxparam
                     racket/stxparam-exptime)
         "languages.rkt"
         "utils.rkt"
         "components.rkt")

;(current-variable-printer debug-variable-printer)

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
(define current-inline-app-limit (make-parameter 100))

; Converts formals to use the new environment
; Environment Formals-Expr -> Formals-Expr
(define (convert-formals env fmls)
  (with-output-language (Lpurifyletrec formals)
    (nanopass-case (Lpurifyletrec formals) fmls
                   [,v ((env-lookup env) v)]
                   [(,v ...) `(,(map (env-lookup env) v) ...)]
                   [(,v ,v* ... . ,v2)`(,((env-lookup env) v)
                                        ,(map (env-lookup env) v*) ...
                                        . ,((env-lookup env) v2))])))

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
                   #:assigned? (variable-assigned? x)
                   #:referenced? (variable-referenced? x)))
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
  (define formals* (formals->identifiers Lpurifyletrec formals))
  (define rest? (formals-rest? Lpurifyletrec formals))
  (if rest?
      ((length formals) . <= . (length operands))
      (= (length formals) (length operands))))

;; Determins if a syntactic form is simple and can thus be
;;    ignored in a begin statement
;; Expr -> Boolean
(define (simple? e)
  (nanopass-case (Lpurifyletrec expr) e
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
         (with-output-language (Lpurifyletrec expr)
           (nanopass-case (Lpurifyletrec expr) e2
                          [(begin ,expr3 ... ,expr4)
                           `(begin ,(append e1* expr3) ,expr4)]
                          [else `(begin ,e1* ... ,e2)]))]))

;; Constructs a let binding (to be used by inline)
;;   Empty lets are removed, assigned but not referenced
;;   variables are kept only for effect.
;; (Listof Var-Exprs) (Listof Operands) Expr -> Expr
(define (make-let vars operands free-vars body size-counter)
  (define (set-effect! result)
    (for-each (curryr set-operand-residualized-for-effect?! #t) operands)
    result)
  (define var-map (map cons vars operands))
  ;(printf "make-let:~n var-map: ~a~n body: ~a~n~n" var-map body)
  (with-output-language (Lpurifyletrec expr)
    (nanopass-case (Lpurifyletrec expr) body
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
                           (begin-set!
                             (assigned (,free-vars ...)
                                       ,body))))])))

;; Returns the resulting expression of a sequence of operations.
;;   (e.g. the last expression of a begin form)
;; Expr -> Expr
(define (result-expr e)
  (nanopass-case (Lpurifyletrec expr) e
                 [(begin ,expr* ... ,expr) expr]
                 [(begin0 ,expr ,expr* ...) expr]
                 [else e]))

;; Contextually aware equality checks for expressions.
;;    (For example, all datusm are equal in an effect context)
;; Expr Expr Context -> Boolean
(define (contextual-equal? e1 e2 context)
  (nanopass-case (Lpurifyletrec expr) e1
                 [(quote ,datum1)
                  (nanopass-case (Lpurifyletrec expr) e2
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
  (with-output-language (Lpurifyletrec expr)
    (match context
      ['effect `(primitive void)]
      [_
       (define v* ((env-lookup env) v))
       (define opnd (variable-operand v*))
       ;(printf "inline-ref:~n v*: ~a~n opnd: ~a~n opnd-exp: ~a~n~n" v* opnd (and opnd (operand-exp opnd)))
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
             ;(printf "inline-ref2:~n v*: ~a~n rhs: ~a~n~n" v* rhs)
             (nanopass-case (Lpurifyletrec expr) rhs
                            [(quote ,datum) rhs]
                            [,v**
                             (cond
                               [(variable-assigned? v**) (residualize-ref v* size-counter)]
                               [else
                                (define v-opnd (variable-operand v))
                                (if (and v-opnd (operand-value v-opnd))
                                    (copy v** v-opnd context effort-counter size-counter)
                                    (residualize-ref v** size-counter))])]
                            [else (copy v* opnd context effort-counter size-counter)])])]
         [else (residualize-ref v* size-counter)])])))

;; Helper for inline-ref, tries to inline references to variables
;; Variable Operand Context Counter Counter -> Variable
(define (copy v opnd context effort-counter size-counter)
  (with-output-language (Lsrc expr)
    (define rhs (result-expr (operand-value opnd)))
    ;(printf "copy:~n v: ~a~n opnd: ~a~n ctx: ~a~n rhs: ~a~n opnd-outer-pending: ~a~n~n" v opnd context rhs (operand-outer-pending opnd))
    (nanopass-case (Lpurifyletrec expr) rhs
                   [(#%plain-lambda ,formals ,abody)
                    (match context
                      ['value (residualize-ref v size-counter)]
                      ['test `'#t]
                      [(struct* app ())
                       (or (and ((operand-outer-pending opnd) . > . 0)
                                (dynamic-wind
                                 (lambda () (set-operand-outer-pending!
                                             opnd (- (operand-outer-pending opnd) 1)))
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
                                 (lambda () (set-operand-outer-pending!
                                             opnd(+ (operand-outer-pending opnd) 1)))))
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
  ;(printf "inline-call:~n e: ~a~n ctx: ~a~n opnds: ~a~n~n" e context operands)
  (define context* (app operands context))
  (define e* (inline-expressions e context* env effort-counter size-counter))
  ;(printf "inline-call2:~n e: ~a~n e*: ~a~n inlined: ~a~n~n" e e* (app-inlined? context*))
  (if (app-inlined? context*)
      (residualize-operands operands e* size-counter)
      (with-output-language (Lpurifyletrec expr)
        `(#%plain-app ,e*
                      ,(map (curryr score-value-visit-operand! size-counter)
                            operands) ...))))

;; Try to inline an expression to a value. Memoizes the result,
;;    returns the resulting expression.
;; Operand -> Expr
(define (value-visit-operand! opnd)
  ;(printf "value-visit-operand!:~n opnd: ~a~n operand-value: ~a~n~n" opnd (operand-value opnd))
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
        ;(printf "value-visit-operand2:~n opnd: ~a~n operand-value: ~a~n~n" opnd (operand-value opnd))
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
  ;(printf "inline:~n proc: ~a~n ctx: ~a~n env: ~a~n~n" proc context env)
  (nanopass-case (Lpurifyletrec lambda) proc
                 [(#%plain-lambda ,formals
                                  (assigned (,v ...) ,expr))
                  (define formals* (formals->identifiers Lpurifyletrec formals))
                  (define rest? (formals-rest? Lpurifyletrec formals))
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
                                 (with-output-language (Lpurifyletrec expr)
                                   `(#%plain-app (primitive list)
                                                 ,(map operand-exp rest-opnds) ...))
                                 (apply hash-union (hash)
                                        (map operand-env rest-opnds))
                                 (operand-effort-counter (first rest-opnds)))))]
                      [else opnds]))
                  (define env* (extend-env* env formals* opnds*))
                  ;(printf "inline2:~n expr: ~a~n fml*: ~a~n opnds*: ~a~n env*: ~a~n~n" expr formals* opnds* env*)
                  (define body (inline-expressions expr
                                                   (app-context context)
                                                   env*
                                                   effort-counter
                                                   size-counter))
                  ;(printf "inline3:~n body: ~a~n~n" body)
                  (define result
                    (make-let (map (env-lookup env*) formals*)
                              opnds*
                              (map (env-lookup env*) v)
                              body
                              size-counter))
                  ;(printf "inline4:~n result: ~a~n~n" result)
                  (set-app-inlined?! context #t)
                  result]))

;; Does constant fold on primitives (if possible)
;; ID Context Counter -> Expr
(define (fold-prim prim context size-counter)
  (define operands (app-operands context))
  ;(printf "fold-prim:~n prim: ~a~n ctx: ~a~n operands: ~a~n operand-vals: ~a~n~n" prim context operands (map operand-value operands))
  (with-output-language (Lpurifyletrec expr)
    (define result
      (or (and (effect-free? prim)
               (match (app-context context)
                 ['effect `(primitive void)]
                 ['test (and (return-true? prim) `(quote #t))]
                 [else #f]))
          (and (foldable? prim)
               (let ([vals (map value-visit-operand! operands)])
                 ;(printf "fold-prim2:~n vals: ~a~n~n" vals)
                 (define-values (consts? operands*)
                   (for/fold ([const-vals #t]
                              [ops null])
                             ([v (in-list vals)])
                     (values
                      (and const-vals
                           (nanopass-case (Lpurifyletrec expr) v
                                          [(quote ,datum) #t]
                                          [else #f]))
                      (cons
                       (nanopass-case (Lpurifyletrec expr) v
                                      [(quote ,datum) datum]
                                      [else #f])
                       ops))))
                 ;(printf "consts?: ~a~n" consts?)
                 (define operands** (reverse operands*))
                 (and consts?
                      (with-handlers ([exn? (lambda (x) (displayln "inline failed") #f)])
                        `(quote ,(parameterize ([current-namespace (make-base-namespace)])
                                   (eval (cons prim operands**))))))))))
    ;(printf "fold-prim3: ~n result: ~a~n~n" result)
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
    ((counter-k counter) #f)))

(define-pass inline-expressions
  : Lpurifyletrec (e context env effort-counter size-counter) -> Lpurifyletrec ()
  
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
         (nanopass-case (Lpurifyletrec expr) (result-expr expr1)
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
          `(#%plain-app (#%plain-lambda (,v* ...)
                                        (assigned (,v ...)
                                                  ,expr))
                        ,expr* ...)
          context env effort-counter size-counter)]
        [(let ([,v* ,expr*] ...)
           (begin-set!
             ,set-expr ...
             (assigned (,v ...)
                       ,expr)))
         (define env* (extend-env* env v* (make-list (length v*) #f)))
         (define ie* (curryr inline-expressions context env* effort-counter size-counter))
         `(let ([,(map (env-lookup env*) v*) ,(map ie* expr*)]  ...)
            (begin-set!
              ,(map ie* set-expr) ...
              (assigned (,(map (env-lookup env*) v) ...)
                        ,(ie* expr))))]
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
                    (nanopass-case (Lpurifyletrec expr) expr*
                                   [(quote ,datum) #t]
                                   [(primitive ,id) #t]
                                   [else #f]))
                expr*]
               [else
                (decrement! size-counter 1)
                `(letrec ([,(dict-keys filtered-vars)
                           ,(map operand-value (dict-values filtered-vars))] ...)
                   ,expr*)])])
  
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
              (define formals* (formals->identifiers Lpurifyletrec formals))
              (define env* (extend-env* env formals* (make-list (length formals*) #f)))
              `(#%plain-lambda ,(convert-formals env* formals)
                               (assigned
                                (,(map (env-lookup env*) v) ...)
                                ,(inline-expressions expr 'value env* effort-counter size-counter)))]
             [(struct* app ()) (inline e context env effort-counter size-counter)])])
  
  (TopLevelForm : top-level-form (e [context context]
                                    [env env]
                                    [effort-counter effort-counter]
                                    [size-counter size-counter])
                -> top-level-form ())
  
  (begin
    ;(printf "inline-expressions:~n exp: ~a~n env: ~a~n ctx: ~a~n~n" e env context)
    (decrement! effort-counter 1)
    (TopLevelForm e context env effort-counter size-counter)))

(define (~inline-expressions e
                             [context 'value]
                             [env (hash)]
                             [effort-counter (make-counter (current-inline-effort-limit))]
                             [size-counter (make-counter (current-inline-size-limit))])
  (inline-expressions e context env effort-counter size-counter))
