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

(define closure-conversion (make-compiler-component))
(define optimizer (make-compiler-component))
(define mutable-variable-elimination (make-compiler-component))
(define debruijn (make-compiler-component))
(define parse (make-compiler-component))
(define generate-bytecode (make-compiler-component))
(define modules (make-compiler-component))

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

(define code
 #;#'(let ()
      (define (fold l init f)
        (if (null? l)
            init
            (fold (cdr l) (f init (car l)) f)))
      (define (pow-sum l n)
        (fold l 0 (lambda (x y) (+ (expt x n) (expt y n)))))
      (pow-sum '(1 2 3) 2))
  #;#'(let ()
      (define (f a)
        (f a))
      (define (g a)
        (f (lambda (x) a)))
      (g '(1 2 3)))
  #'(let ()
    (define (f a)
      (f a))
    (f (lambda (x) '(1 2 3))))
  #;#'(let ([x (read)])
      (let ([x x])
        (+ x x)))
  #;#'(letrec ([fact (lambda (n)
                     (if (= n 0)
                         1
                         (* n (fact (- n 1)))))])
      (fact 5))
  #;#'(let ([x 5])
      (lambda (y)
        x))
 #;#'(let ([x 5])
      (set! x 6)
      x))

;(compile/10 code)
