#lang racket/base

(provide (all-defined-out)
         compile)

(require racket/port
         compiler/zo-marshal
         syntax/toplevel
         "languages.rkt"
         "parser.rkt"
         "passes.rkt"
         "optimizer.rkt"
         "generator.rkt"
         "utils.rkt"
         "components.rkt")

;; Expand syntax fully, even at the top level
(define (expand-syntax* stx)
  (parameterize ([current-namespace (make-base-namespace)])
    (namespace-require 'racket/undefined)
    (namespace-require 'racket)
    (expand-syntax-top-level-with-compile-time-evals
     (namespace-syntax-introduce stx))))

(define (bytes->compiled-expression zo)
  (parameterize ([read-accept-compiled #t])
    (with-input-from-bytes zo
      (lambda () (read)))))

(define closure-conversion (make-compiler-component))
(define optimizer (make-compiler-component))
(define mutable-variable-elimination (make-compiler-component))
(define debruijn (make-compiler-component))
(define parse (make-compiler-component))
(define generate-bytecode (make-compiler-component))
(define modules (make-compiler-component))

(define-compiler compile
  expand-syntax*
  disarm*
  (parse-and-rename parse)
  (lift-submodules modules)
  (lift-require-provide modules)
  (lift-syntax-sequences modules)
  (identify-module-variables modules)
  (scrub-require-provide modules)
  (add-indirect-provide modules)
  (make-begin-explicit parse)
  (identify-assigned-variables mutable-variable-elimination)
  purify-letrec
  (inline-expressions optimizer)
  (convert-assignments mutable-variable-elimination)
  (uncover-free closure-conversion)
  raise-toplevel-variables
  closurify-letrec
  void-lets
  scrub-syntax
  reintroduce-syntax
  (debruijn-indices debruijn)
  (find-let-depth debruijn)
  build-module-registry
  (generate-zo-structs generate-bytecode)
  (zo-marshal generate-bytecode)
  bytes->compiled-expression)

(current-variable-printer debug-variable-printer)
(current-module-binding-printer module-binding-printer)
(current-module-registry-printer debug-module-registry-printer)
(require nanopass/base)

(define code #'(begin
                 (module foo racket
                   (#%plain-module-begin
                    (provide x)
                    (define x 481)))
                 (require 'foo)
                 x))

#;(define code #'(module foo racket
                 (#%plain-module-begin
                  dict-set)))

;(define code #'dict-set)

;(compile/8 code)
;(compile/22 code)
;(compile/23 code)
;(compile code)
;(eval (compile/24 code))
