#lang racket/base

(require racket/match
         "structs.rkt")

(require racket/pretty)

(provide build-pass
         build-compiler
         (rename-out [d-i decompile-intermediate]))

(define (build-pass reductions forms)
  (define (bp* e)
    (define (bp-list* l) (for/list ([i (in-list l)]) (bp* i)))
    (cond
     [(forms e) (reductions e)]
     [else
      (match e
        [(topgenform body) (topgenform (bp* body))]
        [(topexpr body) (topexpr (bp* body))]
        [(topmod id path body)
         (topmod (bp* id) path (bp-list* body))]
        [(topbeg body)
         (topbeg (bp-list* body))]
        [(topbegfs body)
         (topbegfs (bp-list* body))]
        [(modgenform body)
         (modgenform (bp* body))]
        [(pro spec) (pro spec)]
        [(decl body) (decl body)]
        [(submod id path body)
         (submod (bp* id) path (bp-list* body))]
        [(submod* id path body)
         (submod* (bp* id) path (bp-list* body))]
        [(defv id body)
         (defv (bp-list* id) (bp* body))]
        [(defsyntaxs id body)
         (defsyntaxs (bp-list* id) (bp* body))]
        [(defv1 id body)
         (defv1 (bp* id) (bp* body))]
        [(deflam id body)
         (deflam (bp* id) (bp* body))]
        [(req spec) (req spec)]
        [(ide id binding name) (ide id binding name)]
        [(var id type) (var (bp* id) type)]
        [(lam args rest body)
         (lam (bp-list* args) (bp* rest) (bp* body))]
        [(caselam lams)
         (caselam (bp-list* lams))]
        [(branch test tb fb)
         (branch (bp* test) (bp* tb) (bp* fb))]
        [(beg body)
         (beg (bp-list* body))]
        [(beg0 body)
         (beg0 (bp-list* body))]
        [(letv defs body)
         (letv (bp-list* defs) (bp* body))]
        [(letrecv defs body)
         (letrecv (bp-list* defs) (bp* body))]
        [(letv1 defs body)
         (letv1 (bp-list* defs) (bp* body))]
        [(letreclam defs body)
         (letreclam (bp-list* defs) (bp* body))]
        [(letvoid defs boxes? body)
         (letvoid defs boxes? (bp* body))]
        [(setv id body)
         (setv (bp* id) (bp* body))]
        [(setb id body)
         (setb (bp* id) (bp* body))]
        [(bo id) (bo (bp* id))]
        [(unbo id) (unbo (bp* id))]
        [(quo datum) (quo datum)]
        [(quosyntax datum) (quosyntax datum)]
        [(withcm key val result)
         (withcm (bp* key) (bp* val) (bp* result))]
        [(app f args)
         (app (bp* f) (bp-list* args))]
        [(top id) (top (bp* id))]
        [(varref id) (varref (bp* id))]
        [#f #f])]))
  bp*)

(define (build-compiler . passes)
  (apply compose (reverse passes)))

(define (d-i e)
  (define (d-i* l) (for/list ([i (in-list l)]) (d-i i)))
  (match e
    [(topgenform body) (d-i body)]
    [(topexpr body) (d-i body)]
    [(topmod id path body)
     `(module ,(d-i id) path ,(d-i* body))]
    [(topbeg body)
     `(begin ,(d-i* body))]
    [(topbegfs body)
     `(begin-for-syntax ,(d-i* body))]
    [(modgenform body) (d-i body)]
    [(pro spec)
     `(provide ,spec)]
    [(decl body)
     `(#%declare ,body)]
    [(submod id path body)
     `(module ,(d-i id) path ,(d-i* body))]
    [(submod* id path body)
     `(module* ,(d-i id) path ,(d-i* body))]
    [(defv id body)
     `(define-values ,(d-i* id) ,(d-i body))]
    [(defsyntaxs id body)
     `(define-syntax ,(d-i* id) ,(d-i body))]
    [(defv1 id body)
     `(define (d-i id) (d-i body))]
    [(deflam id body)
     `(define-lam (d-i id) (d-i body))]
    [(req spec)
     `(require ,spec)]
    [(ide id binding name)
     id]
    [(var id type)
     (d-i id)]
    [(lam args rest body)
     `(lambda (,@(d-i* args) . ,(d-i rest)) ,(d-i body))]
    [(caselam lams)
     `(case-lambda ,@(d-i* lams))]
    [(branch test tb fb)
     `(branch ,(d-i test) ,(d-i tb) ,(d-i fb))]
    [(beg body)
     `(begin ,@(d-i* body))]
    [(beg0 body)
     `(begin0 ,@(d-i* body))]
    [(letv defs body)
     `(let-values ,(d-i* defs) ,(d-i body))]
    [(letrecv defs body)
     `(letrec-values ,(d-i* defs) ,(d-i body))]
    [(letv1 defs body)
     `(let ,(d-i* defs) ,(d-i body))]
    [(letreclam defs body)
     `(letrec-lam ,(d-i* defs) ,(d-i body))]
    [(letvoid defs boxes? body)
     `(let-void ,(d-i* defs) ,boxes? ,(d-i body))]
    [(setv id body)
     `(set!-values ,(d-i* id) ,(d-i body))]
    [(setb id body)
     `(set!-boxes ,(d-i* id) ,(d-i body))]
    [(bo id)
     `(box ,(d-i id))]
    [(unbo id)
     `(unbox ,(d-i id))]
    [(quo datum)
     `(quote ,datum)]
    [(quosyntax datum)
     `(quote-syntax ,datum)]
    [(withcm key val result)
     `(with-continuation-mark ,(d-i key) ,(d-i val) ,(d-i result))]
    [(app f args)
     `(#%app ,(d-i f) ,@(d-i* args))]
    [(top id)
     `(top ,(d-i id))]
    [(varref id)
     `(top ,(d-i id))]
    [#f #f]))
