#lang racket/base

(provide define-language
         define-pass)

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
