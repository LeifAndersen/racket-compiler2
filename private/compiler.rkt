#lang racket/base

(provide (all-defined-out))

(require racket/port
         compiler/zo-marshal
         syntax/toplevel
         (rename-in racket/base
                    [compile base:compile])
         "languages.rkt"
         "passes.rkt"
         "optimizer.rkt"
         "utils.rkt"
         "components.rkt")

;; Expand syntax fully, even at the top level
(define (expand-syntax* stx)
  (parameterize ([current-namespace (make-base-namespace)])
    (namespace-require 'racket/undefined)
    (expand-syntax-top-level-with-compile-time-evals
     (namespace-syntax-introduce stx))))

(define (bytes->compiled-expression zo)
  (parameterize ([read-accept-compiled #t])
    (with-input-from-bytes zo
      (lambda () (read)))))

(define-compiler-component closure-conversion)
(define-compiler-component optimizer)
(define-compiler-component mutable-variable-elimination)
(define-compiler-component debruijn)
(define-compiler-component parse)
(define-compiler-component generate-bytecode)
(define-compiler-component modules)

(define-compiler compile
  expand-syntax*
  (parse-and-rename parse)
  (lift-submodules modules)
  (lift-require-provide modules)
  (lift-syntax-sequences modules)
  (identify-module-variables modules)
  (scrub-require-provide modules)
  (make-begin-explicit parse)
  (identify-assigned-variables mutable-variable-elimination)
  purify-letrec
  (inline-expressions optimizer)
  (convert-assignments mutable-variable-elimination)
  (uncover-free closure-conversion)
  raise-toplevel-variables
  closurify-letrec
  void-lets
  (debruijn-indices debruijn)
  (find-let-depth debruijn)
  (generate-zo-structs generate-bytecode)
  (zo-marshal generate-bytecode)
  bytes->compiled-expression)
