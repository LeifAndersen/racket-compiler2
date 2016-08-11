#lang racket/base

(provide (all-defined-out))
(require nanopass/base
         racket/bool
         "utils.rkt")

(define-language Lsrc
  (terminals
   (maybe-module-path (maybe-module-path module-path))
   (declaration-keyword (declaration-keyword))
   (datum (datum))
   (symbol (id))
   (vector (vector))
   (variable (v var variable))
   (string (string))
   (path (path))
   (phase-level (phase-level))
   (false (false))
   (exact-nonnegative-integer (exact-nonnegative-integer eni))
   (syntax (syntax-object))
   (boolean (boolean))
   (number (number))
   (bytes (bytes))
   (name (name import-key))
   (procedure (procedure)))
  (linklet-form (linklet-form)
                (linklet (((linklet-reqprov-element import-key) ...) ...) ; require field
                         (linklet-reqprov-element* ...)                   ; provide field
                         name
                         get-import
                         general-top-level-form ...))
  (linklet-reqprov-element (linklet-reqprov-element)
                           id
                           (id id*))
  (get-import (get-import)
              procedure
              false)
  (binding (binding)
           v
           false)
  (general-top-level-form (general-top-level-form)
                          expr
                          (define-values (v ...) expr))
  (expr (expr)
        v
        number
        boolean
        string
        bytes
        lambda
        (primitive id)
        (case-lambda lambda ...)
        (if expr1 expr2 expr3)
        (begin expr* ... expr)
        (begin0 expr expr* ...)
        (let-values ([(v ...) expr1] ...)
          expr)
        (letrec-values ([(v ...) expr1] ...)
          expr)
        (set! v expr)
        (quote datum)
        (with-continuation-mark expr1 expr2 expr3)
        (#%plain-app expr expr* ...)
        (#%variable-reference v)
        (#%variable-reference))
  (lambda (lambda)
    (#%plain-lambda formals expr))
  (formals (formals)
           v
           (v ...)
           (v v* ... . v2))
  (raw-module-path (raw-module-path)
                   raw-root-module-path
                   (submod raw-root-module-path id ...))
  (raw-root-module-path (raw-root-module-path)
                        id
                        string
                        (quote* id)
                        (lib string ...)
                        (file string)
                        (planet string1
                                (string2 string3 string* ...))
                        path))

(define-language Lidentifyassigned
  (extends Lsrc)
  (lambda (lambda)
    (- (#%plain-lambda formals expr))
    (+ (#%plain-lambda formals abody)))
  (expr (expr)
        (- (let-values ([(v ...) expr1] ...)
             expr)
           (letrec-values ([(v ...) expr1] ...)
             expr))
        (+ (let-values ([(v ...) expr1] ...)
             abody)
           (letrec-values ([(v ...) expr1] ...)
             abody)))
  (assigned-body (abody)
                 (+ (assigned (v ...) expr))))

(define-language Lpurifyletrec
  (extends Lidentifyassigned)
  (expr (expr)
        (- (let-values ([(v ...) expr1] ...)
             abody)
           (letrec-values ([(v ...) expr1] ...)
             abody)
           (set! v expr)
           (quote datum))
        (+ set-expr
           (undefined)
           (let ([v expr1] ...)
             set-abody)
           (letrec ([v lambda] ...)
             expr)))
  (lambda (lambda)
    (+ (quote datum)))
  (set-expr (set-expr)
            (+ (set!-values (v ...) expr)))
  (set-abody (set-abody)
             (+ (begin-set! set-expr ... abody))))

(define-language Lconvertassignments
  (extends Lpurifyletrec)
  (expr (expr)
        (- set-expr
           (let ([v expr1] ...)
             set-abody))
        (+ (quote datum)
           (let ([v expr1] ...)
             expr)
           (#%unbox v)
           (#%box v)
           (set!-values (v ...) expr)
           (set!-boxes (v ...) expr)))
  (lambda (lambda)
    (- (#%plain-lambda formals abody)
       (quote datum))
    (+ (#%plain-lambda formals expr)))
  (set-abody (set-abody)
             (- (begin-set! set-expr ... abody)))
  (set-expr (set-expr)
            (- (set!-values (v ...) expr)))
  (assigned-body (abody)
                 (- (assigned (v ...) expr))))

(define-language Luncoverfree
  (extends Lconvertassignments)
  (lambda (lambda)
    (- (#%plain-lambda formals expr))
    (+ (#%plain-lambda formals fbody)))
  (free-body (fbody)
             (+ (free (v ...) (binding* ...) expr))))

(define-language Lraisetoplevel
  (extends Luncoverfree)
  (expr (expr)
        (+ (set!-global v expr))))

(define-language Lclosurify
  (extends Lraisetoplevel)
  (expr (expr)
        (+ (closure v lambda))))

(define-language Lvoidlets
  (extends Lclosurify)
  (expr (expr)
        (- (let ([v expr1] ...) expr)
           (undefined))
        (+ (let ([v expr1]) expr)
           (let-void (v ...) expr))))

(define-language Ldebruijn
  (extends Lvoidlets)
  (expr (expr)
        (- v
           (primitive id)
           (let-void (v ...) expr)
           (let ([v expr1]) expr)
           (letrec ([v lambda] ...)
             expr)
           (set!-boxes (v ...) expr)
           (set!-values (v ...) expr)
           (set!-global v expr)
           (#%box v)
           (#%unbox v)
           (#%variable-reference)
           (#%variable-reference v))
        (+ binding
           (primitive eni)
           (let-void eni expr)
           (let-one expr1 expr)
           (letrec (lambda ...)
             expr)
           (set!-boxes eni1 eni2 expr)
           (set!-values eni1 eni2 expr)
           (set!-global eni1 eni2 expr)
           (#%box eni)
           (#%unbox eni)
           (#%variable-reference eni)))
  (general-top-level-form (general-top-level-form)
                          (- (define-values (v ...) expr))
                          (+ (define-values (eni ...) expr)))
  (lambda (lambda)
    (- (#%plain-lambda formals fbody))
    (+ (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) expr)))
  (binding (binding)
           (+ eni
              (primitive eni)))
  (formals (formals)
           (- v
              (v ...)
              (v v* ... . v2)))
  (free-body (fbody)
             (- (free (v ...) (binding* ...) expr))))

(define-language Lcleanreqprov
  (extends Ldebruijn)
  (terminals
   (- (symbol (id)))
   (+ (symbol (id req-id prov-id intern-id lift-id))))
  (linklet-form (linklet-form)
                (- (linklet (((linklet-reqprov-element import-key) ...) ...)
                            (linklet-reqprov-element* ...)
                            name
                            get-import
                            general-top-level-form ...))
                (+ (linklet (((req-id import-key) ...) ...)  ; Require field
                            (prov-id ...)                    ; Provide field
                            (intern-id ...)                  ; Internal field
                            (lift-id ...)                    ; lifted field
                            name
                            get-import
                            general-top-level-form ...))))

(define-language Lfindletdepth
  (extends Lcleanreqprov)
  (entry compilation-top)
  (linklet-form (linklet-form)
                (- (linklet (((req-id import-key) ...) ...)
                            (prov-id ...)
                            (intern-id ...)
                            (lift-id ...)
                            name
                            get-import
                            general-top-level-form ...))
                (+ (linklet (((req-id import-key) ...) ...)
                            (prov-id ...)
                            (intern-id ...)
                            (lift-id ...)
                            name
                            get-import
                            eni
                            general-top-level-form ...)))
  (lambda (lambda)
    (- (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) expr))
    (+ (#%plain-lambda eni1 boolean (binding2 ...) (binding3 ...) eni4 expr))))
