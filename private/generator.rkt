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
         syntax/modresolve
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

(define (variable->zo-variable v)
  (define binding (variable-binding v))
  (cond [(module-binding? binding)
         (zo:module-variable (module-binding-source-mod binding)
                             (module-binding-source-id binding)
                             (module-binding->offset (module-binding-source-mod binding)
                                                     (module-binding-source-id binding)
                                                     (module-binding-source-phase binding))
                             (module-binding-source-phase binding)
                             #f)]
        [else
         (variable-name v)]))

; Module-Path Symbol Exact-Nonneagtive-Integer -> Exact-Nonnegative-Integer
(define (module-binding->offset mod v phase)
  (parameterize ([current-namespace (make-base-namespace)])
    (namespace-require 'racket)
    (define mod* (let ([m (resolve-module-path-index mod (current-directory))])
                   (if (symbol? m) mod m)))
    (dynamic-require mod* (void))
    (define-values (exports transformers)
      (module->exports mod*))
    (define indirect-exports (module->indirect-exports mod*))
    (define exports* (dict-ref exports phase #f))
    (define transformers* (dict-ref exports phase #f))
    (define indirect-exports* (dict-ref indirect-exports phase #f))
    (cond
      [(not exports*) -1]
      [(dict-has-key? exports* v)
       (define e (dict-keys exports*))
       (- (length e) (length (memq v e)))]
      [(set-member? indirect-exports* v)
       (define e indirect-exports*)
       (+ (length (dict-keys exports*))
          (- (length e) (length (memq v e))))]
      [else -1])))

(define zo-void
  (zo:primval 35))

(define-pass generate-zo-structs : Lfindletdepth (e) -> * ()
  (CompilationTop : compilation-top (e) -> * ()
                  [(program ,prefix-form ,top-level-form)
                   (define-values (prefix max-let-depth) (PrefixForm prefix-form))
                   (zo:compilation-top
                    max-let-depth
                    (hash)
                    prefix
                    (TopLevelForm top-level-form))])
  (PrefixForm : prefix-form (e) -> * (0)
              [(prefix (,binding ...) (,stx ...) ,eni)
               (values
                (zo:prefix
                 0
                 ;; TODO, only need #f if there are modules
                 (append (map (lambda (x) (and x (variable->zo-variable x))) binding)
                         (if (null? stx) '(#f) '()))
                 stx
                 'missing)
                eni)])
  (TopLevelForm : top-level-form (e) -> * ()
                [(#%expression ,expr)
                 (Expr expr)]
                [(begin* ,top-level-form ...)
                 (zo:splice (map TopLevelForm top-level-form))]
                [(#%require ,raw-require-spec ...)
                 (void)]
                [(begin-for-syntax* ,prefix-form ,top-level-form ...)
                 (void)]
                [(define-syntaxes* (,v ...) ,prefix-form ,expr)
                 (void)])
  (ModuleLevelForm : module-level-form (e) -> * ()
                   [(#%declare ,declaration-keyword ...)
                    (void)])
  (SubmoduleForm : submodule-form (e) -> * ()
                 [(module ,id ,module-path ,prefix-form
                    (,raw-provide-spec ...)
                    (,raw-require-spec ...)
                    (,raw-provide-spec* ...)
                    (,module-level-form ...)
                    (,syntax-level-form ...)
                    (,submodule-form ...)
                    (,submodule-form* ...))
                  (define-values (prefix max-let-depth) (PrefixForm prefix-form))
                  (zo:mod id
                          id
                          (module-path-index-join #f #f)
                          prefix
                          (map RawProvideSpec raw-provide-spec)
                          (map RawRequireSpec
                               (cons (with-output-language (Lfindletdepth raw-require-spec)
                                       `(for-meta 0 ,module-path))
                                     raw-require-spec))
                          (map ModuleLevelForm module-level-form)
                          '()
                          '()
                          max-let-depth
                          (zo:toplevel 0 0 #f #f)
                          #f
                          #t
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
        [(quote-syntax ,eni1 ,eni2) (zo:topsyntax eni1 eni2 0)]
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
                   (cons phase-level (map PhaselessReqSpec phaseless-req-spec))])
  (PhaselessReqSpec : phaseless-req-spec (e) -> * ()
                    [(rename ,raw-module-path ,v1 ,v2)
                     (void)])
  (RawModulePath : raw-module-path (e) -> * ()
                 [(submod ,raw-root-module-path ,id ...)
                  (void)])
  (RawRootModulePath : raw-root-module-path (e) -> * ()
                     [,id (module-path-index-join id #f)]
                     [,string (void)]
                     [(quote* ,id) (void)]
                     [(lib ,string ...) (void)]
                     [(file ,string) (void)]
                     [(planet ,string1
                              (,string2 ,string3 ,string* ...))
                      (void)]
                     [,path (void)]))
