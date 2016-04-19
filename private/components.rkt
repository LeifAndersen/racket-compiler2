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

(provide define-language
         define-pass
         define-compiler-component
         add-pass-to-component!
         define-compiler
         update-current-languages!
         start-current-language!
         current-source-top
         current-target-top)

; Language box, for creating current-source and current-target
(begin-for-syntax
  (struct language-box (language)
    #:mutable
    #:transparent
    #:property prop:rename-transformer
    (lambda (inst)
      (syntax-property (language-box-language inst)
                       'not-free-identifier=?
                       #t))))

; Macro used for setting langauge-box
(define-syntax (set-language! stx)
  (syntax-parse stx
    [(_ box language)
     (syntax/loc stx
       (begin-for-syntax
         (define-values (val trans) (syntax-local-value/immediate #'box))
         (set-language-box-language! val #'language)))]))

(define-syntax (start-current-language! stx)
  (syntax-parse stx
    [(_ language:id)
     #`(begin-for-syntax
         (define-values (val trans) (syntax-local-value/immediate #'current-source-top))
         (define-values (val* trans*) (syntax-local-value/immediate #'current-target-top))
         (set-current-language-number! 0)
         (set-language-box-language! val #'#,(format-id stx "~a~a" #'language "src"))
         (set-language-box-language! val* #'#,(format-id stx "~a~a" #'language "src")))]))

; Convenience function for updating current-source and current-target
(define-syntax (update-current-languages! stx)
  (syntax-parse stx
    [(_ language:id)
     #`(begin-for-syntax
         (define-values (val trans) (syntax-local-value/immediate #'current-source-top))
         (define-values (val* trans*) (syntax-local-value/immediate #'current-target-top))
         (set-current-language-number! (+ current-language-number 1))
         (set-language-box-language! val #'#,(format-id stx "~a~a" #'language
                                                      (if (= current-language-number 0)
                                                          "src"
                                                          current-language-number)))
         (set-language-box-language! val* #'#,(format-id stx "~a~a" #'language
                                                       (if (= (+ current-language-number 1) 0)
                                                           "src"
                                                           (+ current-language-number 1)))))
     #;#`(begin
         (set-language! current-source-top #,(format-id stx "~a~a" #'language
                                                        (if (= current-language-number 0)
                                                            "src"
                                                            current-language-number)))
         (set-language! current-target-top #,(format-id stx "~a~a" #'language
                                                        (if (= (+ current-language-number 1) 0)
                                                            "src"
                                                            (+ current-language-number)))))]))

; Top level variables that current-source and current-target parameterize over
(define-syntax current-source-top (language-box #'missing))
(define-syntax current-target-top (language-box #'missing))
(define-for-syntax current-language-number 0)
(define-for-syntax (set-current-language-number! num)
  (set! current-language-number num))

; Varient of define-language that binds current-source and current-target
(define-syntax (define-language stx)
  (syntax-parse stx
    [(_ name:id rest ...)
     #:with current-source (format-id stx "current-source")
     #:with current-target (format-id stx "current-target")
     (quasisyntax/loc stx
       (splicing-let-syntax ([current-source (syntax-local-value #'current-source-top
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
                  #'(nanopass:define-language name rest ...)])))]))

; Varient of define-pass that binds current-source and current-target
(define-syntax (define-pass stx)
  (syntax-parse stx
    [(_ name:id rest ...)
     #:with current-source (format-id stx "current-source")
     #:with current-target (format-id stx "current-target")
     (quasisyntax/loc stx
       (splicing-let-syntax ([current-source (syntax-local-value #'current-source-top
                                                                 (lambda () #f))]
                             [current-target (syntax-local-value #'current-target-top
                                                                 (lambda () #f))])
         #,(syntax/loc stx (nanopass:define-pass name rest ...))))]
    [_
     (raise-syntax-error 'define-pass "Invalid syntax" stx)]))

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
