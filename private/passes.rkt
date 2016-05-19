#lang racket/base

(provide (all-defined-out))

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
         "utils.rkt")

(define-pass lift-submodules : Lsrc (e) -> Lsubmodules ()
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
                          (list (with-output-language (Lsubmodules submodule-form)
                                  `(module ,id ,module-path
                                     (,module-level-form ...)
                                     (,(append* pre) ...)
                                     (,(append* post) ...))))
                          null)]
                 [(submodule* ,id ,module-path
                              (,[module-level-form pre post] ...))
                  (values `(#%plain-app (primitive void))
                          null
                          (list (with-output-language (Lsubmodules submodule-form)
                                  `(module ,id ,module-path
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

(define-pass lift-require-provide : Lsubmodules (e) -> Lreqprov ()
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

(define-pass lift-syntax-sequences : Lreqprov (e) -> Lsyntax ()
  (definitions
    (define (merge-syntax-tables tables)
      (apply hash-union (hash) tables
             #:combine (lambda (v1 v2)
                         (append v1 v2))))
    (define (build-from-table syntax-table)
      (for/list ([(k v) (in-hash syntax-table)])
        (with-output-language (Lsyntax syntax-level-form)
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
                                             (with-output-language (Lsyntax syntax-body)
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
                                                 (with-output-language (Lsyntax syntax-body)
                                                   `(define-syntaxes (,v ...) ,expr))))])
  (Expr : expr (e) -> expr ((hash))))

(define-pass identify-module-variables : Lsyntax (e) -> Lmodulevars ()
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

(define-pass scrub-require-provide : Lmodulevars (e) -> Lscrubreqprov ()
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
                     (with-output-language (Lscrubreqprov phaseless-prov-spec)
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

;; Makes explicit begins so that only they need to deal with expression blocks.
;; Could probably be dealt with in parse-and-rename
;; Also marks variables as being referenced.
(define-pass make-begin-explicit : Lscrubreqprov (e) -> Lbeginexplicit ()
  (Expr : expr (e) -> expr ()
        [,v (set-binding-referenced?! (variable-binding v) #t) v]
        [(#%plain-lambda ,[formals] ,[expr*] ... ,[expr])
         (if (= (length expr*) 0)
             `(#%plain-lambda ,formals ,expr)
             `(#%plain-lambda ,formals (begin ,expr* ... ,expr)))]
        [(case-lambda (,formals ,expr* ... ,expr))
         (with-output-language (Lscrubreqprov expr)
           (make-begin-explicit `(#%plain-lambda ,formals ,expr* ... ,expr)))]
        [(case-lambda (,formals ,expr* ... ,expr) ...)
         `(case-lambda ,(for/list ([f (in-list formals)]
                                   [e* (in-list expr*)]
                                   [e (in-list expr)])
                          (with-output-language (Lscrubreqprov expr)
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

(define-pass identify-assigned-variables : Lbeginexplicit (e) -> Lidentifyassigned ()
  (definitions
    (define-syntax-rule (formals->identifiers* fmls)
      (formals->identifiers Lidentifyassigned fmls)))
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
         (set-binding-assigned?! (variable-binding v) #t)
         (values `(set! ,v ,expr)
                 (set-add assigned* v))]
        [(let-values ([(,v ...) ,[expr assigned]] ...)
           ,[expr* assigned*])
         (values `(let-values ([(,v ...) ,expr] ...)
                    (assigned (,(set-intersect assigned* (apply set-union '() v)) ...) ,expr*))
                 (apply set-union '() (set-remove assigned* v) assigned))]
        [(letrec-values ([(,v ...) ,[expr assigned]] ...)
           ,[expr* assigned*])
         (values `(letrec-values ([(,v ...) ,expr] ...)
                    (assigned (,(set-intersect assigned* (apply set-union '() v)) ...) ,expr*))
                 (apply set-union '() (set-remove assigned* v) assigned))]
        ;; Really *should* be generated
        [(if ,[expr1 assigned1] ,[expr2 assigned2] ,[expr3 assigned3])
         (values `(if ,expr1 ,expr2 ,expr3)
                 (set-union assigned1 assigned2 assigned3))]
        [(with-continuation-mark ,[expr1 assigned1] ,[expr2 assigned2] ,[expr3 assigned3])
         (values `(with-continuation-mark ,expr1 ,expr2 ,expr3)
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
         (values `(case-lambda ,lambda ...)
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

(define-pass purify-letrec : Lidentifyassigned (e) -> Lpurifyletrec ()
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

(define-pass convert-assignments : Lpurifyletrec (e) -> Lconvertassignments ()
  (definitions
    (define ((lookup-env env) x)
      (dict-ref env x x))
    (define (extend-env env assigned*)
      ;(define temp* (map (fresh) assigned*))
      (define temp* assigned*)
      (append (map cons assigned* temp*) env))
    (with-output-language (Lconvertassignments expr)
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

  ; We can assume quote will never happen, as it's only there for the optimizer
  (Lambda : lambda (e [env '()]) -> lambda ()
          [(#%plain-lambda ,formals
                           (assigned (,v ...) ,expr))
           (define env* (extend-env env v))
           `(#%plain-lambda ,(Formals formals env*)
                            ,(build-let v (map (lookup-env env*) v)
                                        (Expr expr env* #t)))])
  (Expr : expr (e [env '()] [boxes? #t]) -> expr ()
        [(quote ,datum) `(quote ,datum)]
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
             `(set!-values (,(map (lookup-env env) v) ...) ,expr*))]))

(define-pass uncover-free : Lconvertassignments (e) -> Luncoverfree ()
  (definitions
    (define-syntax-rule (formals->identifiers* formals)
      (formals->identifiers Luncoverfree formals)))
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

(define-pass raise-toplevel-variables : Luncoverfree (e) -> Lraisetoplevel ()
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
                [,expr (Expr e globals)]
                #;[(begin* ,top-level-form ...)
                 (displayln globals)
                 `(begin* ,(map (curryr TopLevelForm globals) top-level-form) ...)])
                #;[(#%expression ,[expr])
                 `(#%expression ,expr)]
  (GeneralTopLevelForm : general-top-level-form (e [globals '()]) -> top-level-form ())
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

(define-pass closurify-letrec : Lraisetoplevel (e) -> Lclosurify ()
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
                              ,(Expr (with-output-language (Lraisetoplevel expr)
                                       `(#%plain-lambda ,(list-ref formals empty-index)
                                                        (free (,(list-ref v1* empty-index) ...)
                                                              (,(list-ref binding2* empty-index) ...)
                                                              ,(list-ref expr* empty-index))))))])
                ,(Expr (with-output-language (Lraisetoplevel expr)
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

(define-pass void-lets : Lclosurify (e) -> Lvoidlets ()
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

(define-pass scrub-syntax : Lvoidlets (e) -> Lscrubsyntax ()
  (definitions

    ;; Syntax Table maps integers to syntax objects
    (struct syntax-table (ticket
                          objects)
      #:mutable)

    ;; Constructs a new Syntax Table
    ;; -> Syntax-Table
    (define (make-syntax-table)
      (syntax-table 0 '()))

    ;; Add an element to the syntax table, returning the object's ticket,
    ;;   and raising the ticket value for the next insertion
    ;; Syntax-Table Any -> Syntax-Table
    (define (add-syntax-to-table! table object)
      (define ticket (syntax-table-ticket table))
      (set-syntax-table-ticket! table (+ ticket 1))
      (set-syntax-table-objects! table (cons object (syntax-table-objects table)))
      ticket)

    ;; Global table tat will store all of syntax objects for pre-compiling
    ;;  with internal Racket compiler
    ;;  (Should really be changed to handle the compilation on its own)
    (define global-table (make-syntax-table))

    ;; Module level syntax table for mapping syntax objects to their location in the
    ;;  prefix struct.
    (define current-module-table (make-parameter (make-syntax-table))))
  (CompilationTop : compilation-top (e) -> compilation-top ()
                  [(program (,binding ...) ,[top-level-form])
                   `(program (,binding ...)
                             (,(reverse (syntax-table-objects global-table)) ...)
                             (,(reverse (syntax-table-objects (current-module-table))) ...)
                             ,top-level-form)])
  (TopLevelForm : top-level-form (e) -> top-level-form ()
                [,submodule-form
                 (parameterize ([current-module-table (make-syntax-table)])
                   (SubmoduleForm submodule-form))])
  (SubmoduleForm : submodule-form (e) -> submodule-form ()
                 [(module ,id ,module-path (,v ...) (,v* ...)
                    (,[raw-provide-spec] ...)
                    (,[raw-require-spec] ...)
                    (,[module-level-form] ...)
                    (,[syntax-level-form] ...)
                    (,submodule-form ...)
                    (,submodule-form* ...))
                  (define sf (parameterize ([current-module-table (make-syntax-table)])
                               (SubmoduleForm submodule-form)))
                  (define sf* (parameterize ([current-module-table (make-syntax-table)])
                                (SubmoduleForm submodule-form)))
                  `(module ,id ,module-path (,v ...) (,v* ...)
                     (,(reverse (syntax-table-objects (current-module-table))) ...)
                     (,raw-provide-spec ...)
                     (,raw-require-spec ...)
                     (,module-level-form ...)
                     (,syntax-level-form ...)
                     (,sf ...)
                     (,sf* ...))])
  (Expr : expr (e) -> expr ()
        [(quote-syntax ,syntax-object)
         (define key (add-syntax-to-table! global-table syntax-object))
         `(quote-syntax ,(add-syntax-to-table! (current-module-table) key))]
        [(quote-syntax-local ,syntax-object)
         (define key (add-syntax-to-table! global-table syntax-object))
         `(quote-syntax ,(add-syntax-to-table! (current-module-table) key))]))

(define-pass reintroduce-syntax : Lscrubsyntax (e) -> Lreintroducesyntax ()
  (definitions
    (define global-syntax-table (make-parameter '())))
  (CompilationTop : compilation-top (e) -> compilation-top ()
                  [(program (,binding ...)
                            (,syntax-object ...)
                            (,eni ...)
                            ,top-level-form)
                   (define compiled (car (toplevel-syntax->zo
                                          #`(list #,@(for/list ([s (in-list syntax-object)])
                                                       #`(quote-syntax #,s #:local))))))
                   (define syntax-table (zo:prefix-stxs
                                         (zo:compilation-top-prefix compiled)))
                   (parameterize ([global-syntax-table syntax-table])
                     `(program (,binding ...)
                               (,(map (curry list-ref (global-syntax-table)) eni) ...)
                               ,(TopLevelForm top-level-form)))])
  (TopLevelForm : top-level-form (e) -> top-level-form ())
  (SubmoduleForm : submodule-form (e) -> submodule-form ()
                 [(module ,id ,module-path (,v ...) (,v* ...) (,eni ...)
                    (,[raw-provide-spec] ...)
                    (,[raw-require-spec] ...)
                    (,[module-level-form] ...)
                    (,[syntax-level-form] ...)
                    (,[submodule-form] ...)
                    (,[submodule-form*] ...))
                  `(module ,id ,module-path (,v ...) (,v* ...)
                     (,(map (curry list-ref (global-syntax-table)) eni) ...)
                     (,raw-provide-spec ...)
                     (,raw-require-spec ...)
                     (,module-level-form ...)
                     (,syntax-level-form ...)
                     (,submodule-form ...)
                     (,submodule-form* ...))]))

(define-pass debruijn-indices : Lreintroducesyntax (e) -> Ldebruijn ()
  (definitions
    (define-syntax-rule (formals->identifiers* fmls)
      (formals->identifiers Lreintroducesyntax fmls))
    (define-syntax-rule (formals-rest?* fmls)
      (formals-rest? Lreintroducesyntax fmls))
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
          (error 'compiler "Variable not bound ~a" id)))
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
        [(quote-syntax ,eni) `(quote-syntax ,(- frame prefix-frame) ,eni)]
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
                 [(module ,id ,module-path (,v* ...) (,v** ...) (,stx ...)
                          (,[raw-provide-spec] ...)
                          (,[raw-require-spec] ...)
                          (,module-level-form ...)
                          (,[syntax-level-form] ...)
                          (,submodule-form ...)
                          (,submodule-form* ...))
                  (define global-env* (hash-union global-env (make-global-env v*)
                                                  #:combine (lambda (v1 v2) v2)))
                  `(module ,id ,module-path (,v* ...) (,v** ...) (,stx ...)
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
                  [(program (,binding ...) (,stx ...) ,top-level-form)
                   `(program (,binding ...) (,stx ...)
                             ,(TopLevelForm top-level-form '() 0 (make-global-env binding) 0))]))

(define-pass find-let-depth : Ldebruijn (e) -> Lfindletdepth ()
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
                 [(module ,id ,module-path (,v* ...) (,v** ...) (,stx ...)
                          (,[raw-provide-spec] ...)
                          (,[raw-require-spec] ...)
                          (,[module-level-form depth] ...)
                          (,[syntax-level-form] ...)
                          (,[submodule-form** depth**] ...)
                          (,[submodule-form* depth*] ...))
                  (values `(module ,id ,module-path (,v* ...) (,v** ...) (,stx ...)
                             ,(apply max 0 depth)
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
                  [(program (,binding ...) (,stx ...) ,[top-level-form depth])
                   `(program ,depth (,binding ...) (,stx ...) ,top-level-form)]))

