#lang racket/base

(provide define-language
         define-pass
         define-compiler-component
         add-pass-to-component!)

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
                     racket/stxparam-exptime))

; Varient of define-language that binds current-source and current-target
(define-syntax (define-language stx)
  (syntax-parse stx
    [(_ name:id rest ...)
     #:with current-source (format-id stx "current-source")
     #:with current-target (format-id stx "current-target")
     #`(splicing-let-syntax ([current-source (syntax-local-value #'current-source-top
                                                                 (lambda () #f))]
                             [current-target (syntax-local-value #'current-target-top
                                                                 (lambda () #f))])
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

; Varient of define-pass that binds current-source and current-target
(define-syntax (define-pass stx)
  (syntax-parse stx
    [(_ name:id rest ...)
     #:with current-source (format-id stx "current-source")
     #:with current-target (format-id stx "current-target")
     #'(splicing-let-syntax ([current-source (syntax-local-value #'current-source-top
                                                                 (lambda () #f))]
                             [current-target (syntax-local-value #'current-target-top
                                                                 (lambda () #f))])
         (nanopass:define-pass name rest ...))]))

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

