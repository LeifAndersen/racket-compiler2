#lang racket

(require (except-in nanopass/base
                    define-language
                    define-pass)
         (rename-in nanopass/base
                    [define-language nanopass:define-language]
                    [define-pass nanopass:define-pass])
         racket/splicing
         rackunit
         (rename-in racket/base
                    [compile base:compile]
                    [current-compile base:current-compile])
         (for-syntax racket/base
                     syntax/parse
                     racket/syntax))

(provide define-compiler-component
         add-pass-to-component!
         define-compiler)

; Representation of a compiler component
(struct compiler-component (passes)
  #:mutable
  #:transparent) ;; TODO: Remove, for debugging

; Construct a compiler component
(define-syntax (define-compiler-component stx)
  (syntax-parse stx
    [(_ name:id)
     #'(define name (compiler-component '()))]))

; Add a compiler pass to a component
;  (to be used by define-language)
;  (Adds back to front)
(define (add-pass-to-component! component pass)
  (set-compiler-component-passes! component (cons pass (compiler-component-passes component))))

(begin-for-syntax
  (define-syntax-class pass
    (pattern name:id
             #:attr [components 1] '())
    (pattern (name:id components:id ...))))

(define-syntax (define-compiler stx)
  (syntax-parse stx
    [(_ name:id passes:pass ...+)
     #:with compilers (format-id stx "compilers")
     (define pass-names (reverse (syntax->list #'(passes.name ...))))
     (define pass-components (reverse (syntax->list #'((passes.components ...) ...))))
     ;; Bind the compiler name to the compiler.
     #`(begin (define name (compose #,@pass-names))

              ;; Add each of the pass to there respective components
              #,@(for/list ([pn (in-list pass-names)]
                            (pc (in-list pass-components)))
                   #`(begin
                       #,@(for/list ([pc* (in-list (syntax->list pc))])
                            #`(add-pass-to-component! #,pc* #,pn))))

              ;; Create intermediate compilers for use in test casses
              (define compilers null)
              #,@(let build-partial-compiler ([passes pass-names]
                                              [pass-count (length pass-names)])
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
                                    (build-partial-compiler (cdr passes) (- pass-count 1))))))))]))
