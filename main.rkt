#lang racket/base

(provide compile)

(require "private/languages.rkt"
         "private/utils.rkt"
         "private/components.rkt"
         "private/compiler.rkt")

(define orig (current-compile))

(define in-compile? (make-parameter #f))

(current-compile
 (λ (prog use)
   (define freeze-in-compile? (in-compile?))
   (parameterize ([in-compile? #t])
     (if freeze-in-compile?
         (orig prog use)
         (compile prog)))))
