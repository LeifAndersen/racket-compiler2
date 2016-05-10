#lang racket/base

(provide primitive-identifier?
         primitive->symbol
         primitive-table*
         maybe-module-path?
         phase-level?
         declaration-keyword?
         datum?
         (struct-out variable)
         make-variable
         debug-variable-printer
         current-variable-printer
         current-variable-equal?
         (struct-out binding)
         make-binding
         (struct-out operand)
         make-operand
         foldable?
         effect-free?
         return-true?
         formals->identifiers
         formals-rest?
         compiler-value?)

(require nanopass/base
         racket/set
         racket/struct
         rackunit
         (rename-in racket/base
                    [compile base:compile]
                    [current-compile base:current-compile]))

(require/expose compiler/decompile (primitive-table))


; Pointer to a primitive module
; For use in primitive-identifier? and primitive->symbol
(define primitive-module
  (car (identifier-binding #'+)))

; Determines if an identifier is a primitive.
; Identifier -> Boolean
(define (primitive-identifier? identifier)
  (define binding (identifier-binding identifier))
  (and (list? binding) (eq? (car binding) primitive-module)))

; Converts a primitive into one in Racket's primitive table
; Identifier -> Symbol
(define (primitive->symbol identifier)
  (define binding (identifier-binding identifier))
  (cadr binding))

(define primitive-table*
  (for/hash ([(k v) (in-hash primitive-table)])
    (values v k)))

(define (maybe-module-path? m)
  (or (module-path? m) (not m)))

(define (phase-level? pl)
  (or (exact-integer? pl) (not pl)))

(define (declaration-keyword? dk)
  #t)

(define (datum? d)
  (not (syntax? d)))

; Represents a variable expression.
; One variable is bound to another if their bindings point point to the same location in memory
; Variables are not assigned or referenced by default, a pass changes that if it occurs
(struct variable (name
                  operand
                  srcloc
                  binding
                  properties
                  assigned?
                  referenced?)
  #:mutable
  #:methods gen:custom-write
  [(define (write-proc data port mode)
     ((current-variable-printer) data port mode))]
  #:methods gen:equal+hash
  [(define (equal-proc a b t) ((current-variable-equal?) a b))
   (define (hash-proc v t) (eq-hash-code v))
   (define (hash2-proc v t) (eq-hash-code v))])
(define (make-variable name
                       #:operand [operand #f]
                       #:properties [properties (make-hash)]
                       #:source-location [srcloc #f]
                       #:binding [binding (make-binding)]
                       #:assigned? [assigned #f]
                       #:referenced? [ref #f])
  (variable name operand srcloc binding properties assigned ref))
(define debug-variable-printer
  (make-constructor-style-printer
   (lambda (obj) 'variable)
   (lambda (obj) (list (variable-name obj)
                       (variable-operand obj)
                       (variable-properties obj)
                       (variable-assigned? obj)
                       (variable-referenced? obj)))))

(define current-variable-equal?
  (make-parameter (lambda (a b) (eq? (variable-binding a) (variable-binding b)))))
(define current-variable-printer
  (make-parameter
   (make-constructor-style-printer
    (lambda (obj) 'variable)
    (lambda (obj) (list (variable-name obj))))))

; Binding object, ensures that two variables are equal.
(struct binding (properties))
(define (make-binding #:properties [properties (make-hash)])
  (binding properties))

(struct operand (exp
                 env
                 effort-counter
                 value
                 residualized-for-effect?
                 size
                 inner-pending?
                 outer-pending)
  #:mutable)
(define (make-operand exp env effort-counter
                      #:value [value #f]
                      #:residualized-for-effect? [residualized-for-effect? #f]
                      #:size [size 0]
                      #:inner-pending? [inner-pending? #f]
                      #:outer-pending [outer-pending 10])
  (operand exp env effort-counter value residualized-for-effect? size inner-pending? outer-pending))

; Determine if this primitive is one that is effect free
;   eg, cons, list, cdr, etc.
; Symbol -> Boolean
(define (effect-free? primitive)
  (define effect-free-set
    (set 'void))
  (cond
    [(set-member? effect-free-set primitive) #t]
    [(foldable? primitive) #t]
    [else #f]))

; Determins if this primitive is one that will always return true
;  eg. list, cons
; Symbol -> Boolean
(define (return-true? primitive)
  (define return-true-set
    (set 'cons 'list 'random))
  (cond [(set-member? return-true-set primitive) #t]
        [else #f]))

; Determine if this primitive is foldable
;   eg +, -, etc.
; Symbol -> Boolean
(define (foldable? primitive)
  (define foldable-set
    (set '+ '- '* '/ '= '< '> '<= '>=))
  (cond
    [(set-member? foldable-set primitive) #t]
    [else #f]))

; Grabs set of identifiers out of formals non-terminal in a language
; lang formals -> (listof identifiers)
(define-syntax-rule (formals->identifiers lang fmls)
  (nanopass-case (lang formals) fmls
                 [,v                       (list v)]
                 [(,v (... ...))           v]
                 [(,v ,v* (... ...) . ,v2) (set-union (list v v2) v*)]))

; lang formals -> boolean
(define-syntax-rule (formals-rest? lang fmls)
  (nanopass-case (lang formals) fmls
                 [,v                       #t]
                 [(,v (... ...))           #f]
                 [(,v ,v* (... ...) . ,v2) #t]))

(define-syntax-rule (compiler-value? lang exp)
  (nanopass-case (lang top-level-form) exp
                 [(quote ,datum) #t]
                 [else #f]))
