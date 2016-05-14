#lang racket/base

(provide (protect-out (all-defined-out)))

(require nanopass/base
         racket/set
         racket/struct
         racket/port
         rackunit
         compiler/zo-parse
         syntax/toplevel
         syntax/strip-context)

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
                  properties)
  #:mutable
  #:methods gen:custom-write
  [(define (write-proc data port mode)
     ((current-variable-printer) data port mode))]
  #:methods gen:equal+hash
  [(define (equal-proc a b t) (eq? (variable-binding a) (variable-binding b)))
   (define (hash-proc v t) (eq-hash-code (variable-binding v)))
   (define (hash2-proc v t) (eq-hash-code (variable-binding v)))])
(define (make-variable name
                       #:operand [operand #f]
                       #:properties [properties (make-hash)]
                       #:source-location [srcloc #f]
                       #:binding [binding (make-binding)])
  (variable name operand srcloc binding properties))

(define debug-variable-printer
  (make-constructor-style-printer
   (lambda (obj) 'variable)
   (lambda (obj) (list (variable-name obj)
                       (variable-operand obj)
                       (variable-properties obj)
                       (variable-binding obj)))))

(define current-variable-printer
  (make-parameter
   (make-constructor-style-printer
    (lambda (obj) 'variable)
    (lambda (obj) (list (variable-name obj))))))

; Binding object, ensures that two variables are equal.
(struct binding (properties
                 assigned?
                 referenced?)
  #:mutable
  #:methods gen:custom-write
  [(define (write-proc data port mode)
     ((current-binding-printer) data port mode))])
(define (make-binding #:properties [properties (make-hash)]
                      #:assigned? [assigned? #f]
                      #:referenced? [referenced? #f])
  (binding properties assigned? referenced?))

(define current-binding-printer
  (make-parameter
   (make-constructor-style-printer
    (lambda (obj) 'binding)
    (lambda (obj) (list (binding-properties obj)
                        (binding-assigned? obj)
                        (binding-referenced? obj))))))

; Extenion of binding, stores module level information
; Similar to results returned from `identifier-binding` function
(struct module-binding binding (source-mod
                                source-id
                                nominal-source-mod
                                nominal-source-id
                                source-phase
                                import-phase
                                nominal-export-phase))
(define (make-module-binding source-mod
                             source-id
                             nominal-source-mod
                             nominal-source-id
                             source-phase
                             import-phase
                             nominal-export-phase
                             #:properties [properties (make-hash)]
                             #:assigned? [assigned? #f]
                             #:referenced? [referenced? #f])
  (module-binding properties
                  assigned?
                  referenced?
                  source-mod
                  source-id
                  nominal-source-mod
                  nominal-source-id
                  source-phase
                  import-phase
                  nominal-export-phase))


(define current-outer-pending-default-fuel (make-parameter 1))

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
                      #:outer-pending [outer-pending (current-outer-pending-default-fuel)])
  (operand exp env effort-counter value residualized-for-effect? size inner-pending? outer-pending))

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

; Converts a compiler expression to a ZO file.
;  Similar to zordoz
; Compiled-Expression -> ZO
(define (compiled-expression->zo compiled)
  (define-values (in out) (make-pipe))
  (display compiled out)
  (close-output-port out)
  (define y (port->bytes in))
  (close-input-port in)
  (zo-parse (open-input-bytes y)))

; Compiles a syntax object and converts it to a zo
;  Similar to zordoz
; Syntax -> ZO
(define (syntax->zo stx)
  (compiled-expression->zo (compile-syntax (expand-syntax-top-level-with-compile-time-evals stx))))

(define (toplevel-syntax->zo stx)
  (parameterize ([current-namespace (make-base-namespace)])
    (namespace-require 'racket/undefined)
    (map compiled-expression->zo
         (eval-compile-time-part-of-top-level/compile
           (expand-syntax-top-level-with-compile-time-evals
             (namespace-syntax-introduce (strip-context stx)))))))


;; Taken from Typed Racket
;;   Typed Racket runs after macro expansion, and it must be priviledged,
;;   so it can just disarm all taints (and arm everything afterward).
; Syntax -> Syntax
(define (disarm* stx)
  (let loop ([v stx])
    (cond
     [(syntax? v)
      (let* ([stx (syntax-disarm v orig-insp)]
             [r (loop (syntax-e stx))])
        (if (eq? r (syntax-e stx))
            stx
            (datum->syntax stx r stx stx)))]
     [(pair? v) (let ([a (loop (car v))]
                      [d (loop (cdr v))])
                  (if (and (eq? a (car v))
                           (eq? d (cdr v)))
                      v
                      (cons a d)))]
     [else v])))

(define orig-insp (variable-reference->module-declaration-inspector
                   (#%variable-reference)))
