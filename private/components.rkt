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
                     racket/syntax)
         "utils.rkt")

(provide make-compiler-component
         add-pass-to-component!
         define-compiler
         (struct-out compiler-component)
         add-pass-to-component!
         variable-add-property!
         variable-update-property!
         variable-get-property)

; Representation of a compiler component
; passes : (Listof Procedure)
; insertion-procs : (HashTable Symbol (Setof (-> Any Any))
(struct compiler-component (passes
                            insertion-procs)
  #:mutable)
(define (make-compiler-component [passes '()]
                                 [insertion-procs (make-hash
                                                   (list
                                                    (list 'pre (mutable-set))
                                                    (list 'post (mutable-set))))])
  (compiler-component passes insertion-procs))

; Add a compiler pass to a component
;  (to be used by define-compiler)
;  (Adds back to front)
(define (add-pass-to-component! component pass)
  (set-compiler-component-passes! component (cons pass (compiler-component-passes component))))

(begin-for-syntax
  (define-syntax-class pass
    (pattern name:id
             #:attr [components 1] '())
    (pattern (name:id components:id ...))))

; Key object to be used in variable properties table
(struct key ())

; Adds a property to a variable. Returns a key that must be used
;   to get property out again.
; Variable Any -> Key
(define (variable-add-property! variable property)
  (define k (key))
  (dict-set! (variable-properties variable) k property)
  k)

; Updates the property attached to a specific variable and key.
;   Returns the old property that was there.
;   Errors if variable does not have a property for the key.
; Variable Key (-> Any Any) -> Any
(define (variable-update-property! variable key property-thunk)
  (dict-update!
   (dict-update! (variable-properties variable) key
                 (lambda ()
                   (raise (exn:fail:contract (format "Variable ~a does not contain key ~a"
                                                     variable key)
                                             (current-continuation-marks)))))))

; Retrieves a property from a variable given a key.
;   Errors if variable does not have a property for the key
; Variable Key -> Any
(define (variable-get-property variable key)
  (dict-ref (variable-properties variable) key
            (lambda ()
              (raise (exn:fail:contract (format "Variable ~a does not contain key: ~a" variable key)
                                        (current-continuation-marks))))))

; Adds a procedure to a component
;   The location field is currently either 'pre or 'post
;   As we learn more about what valid locations should be, that will change.
;   Possibly even make it possible for a component to state what valid locations are.
; Component Symbol (-> Any Any) -> Void
(define (component-add-proc! component location proc)
  (define insertion-procs (compiler-component-insertion-procs component))
  (unless (hash-has-key? location)
    (raise (exn:fail:contract (format "Compiler Component ~a does not contain location: ~a"
                                      component location)
                              (current-continuation-marks)))))

; Returns a setof of all valid locations in the compiler component
; Component -> (Setof Symbol)
(define (compiler-component-insert-locations component)
  (dict-keys (compiler-component-insertion-procs component)))

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
