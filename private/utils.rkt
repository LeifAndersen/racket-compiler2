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
         current-variable-equal?
         (struct-out operand)
         make-operand
         foldable?
         effect-free?)

(require rackunit
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
; One variable is bound to another if they point to the same location in memory
(struct variable (name
                  operand
                  srcloc
                  assigned?
                  referenced?)
  #:mutable
  #:methods gen:custom-write
  [(define (write-proc data port mode)
     (fprintf port "#(variable: ~a)" (variable-name data)))]
  #:methods gen:equal+hash
  [(define (equal-proc a b t) ((current-variable-equal?) a b))
   (define (hash-proc v t) (eq-hash-code v))
   (define (hash2-proc v t) (eq-hash-code v))])
(define (make-variable name
                       #:operand [operand #f]
                       #:source-location [srcloc #f]
                       #:assigned? [assigned 'unknown]
                       #:referenced? [ref 'unknown])
  (variable name operand srcloc assigned ref))
(define current-variable-equal? (make-parameter (lambda (a b) (eq? a b))))

(struct operand (exp
                 env
                 value
                 residualized-for-effect?)
  #:mutable)
(define (make-operand exp env
                      #:value [value #f]
                      #:residualized-for-effect? [residualized-for-effect? #f])
  (operand exp env value residualized-for-effect?))

; Determine if this primitive is one that is effect free
;   eg, cons, list, cdr, etc.
; Symbol -> Boolean
(define (effect-free? primitive)
  #f) ;; TODO : It may turn out to be effect free

; Determine if this primitive is foldable
;   eg +, -, etc.
; Symbol -> Boolean
(define (foldable? primitive)
  #f) ;; TODO