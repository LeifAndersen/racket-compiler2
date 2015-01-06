#lang racket/base

(require racket/match
         racket/pretty
         compiler/zo-marshal
         (prefix-in zo: compiler/zo-structs)
         "private/template.rkt"
         "private/parse.rkt"
         "private/structs.rkt"
         "private/letrec.rkt"
         "private/assigned.rkt")

(define cc (current-compile))

(define (new-cc form y)
  (define compiler
    (build-compiler
     expand
     parse
     purify-letrec
     box-mutable-variables))
  (define out (compiler form))
  (pretty-write (decompile-intermediate out))
  (cc form y))

(current-compile new-cc)
