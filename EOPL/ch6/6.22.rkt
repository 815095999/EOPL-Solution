#lang eopl
(require "expression-grammar.rkt")
(require "cps-grammar.rkt")
(require "base.rkt")

; make-send-to-cont : simpleexp x simpleexp -> tfexp
(define make-send-to-cont
  (lambda (k-exp simple-exp)
    (cases simple-exp k-exp
      (cps-proc-exp (vars body)
                    (cps-let-exp (car vars)
                                 simple-exp
                                 body))
      (else (cps-call-exp k-exp (list simple-exp))))))


; cps-of-exps: listof(inpexp) x (listof(inpexp) -> tfexp) -> tfexp
(define cps-of-exps
  (lambda (exps builder)
    ; cps-of-rest: listof(inpexp) -> tfexp
    (let cps-of-rest ((exps exps))
      (let ((pos (list-index
                  (lambda (exp) (not (inp-exp-simple? exp)))
                  exps)))
        (if (not pos)
            (builder (map cps-of-simple-exp exps))
            (let ((var (fresh-identifier 'var)))
              (cps-of-exp
               (list-ref exps pos)
               (cps-proc-exp (list var)
                             (cps-of-rest (list-set exps pos (var-exp var)))))))))))
(define cps-of-exps*
  (lambda (exps builder)
    ; cps-of-rest: listof(inpexp) -> tfexp
    (let cps-of-rest ((exps exps))
      (let ((pos (list-index
                  (lambda (exp) (not (inp-exp-simple? exp)))
                  exps)))
        (if (not pos)
            (builder (map cps-of-simple-exp exps))
            (let ((var (fresh-identifier 'var)))
              (cps-of-exp
               (list-ref exps pos)
               (cps-proc-exp (list var)
                             (cps-of-rest (list-set exps pos (var-exp var)))))))))))

; inp-exp-simple?: inpexp -> bool
(define inp-exp-simple?
  (lambda (exp)
    (cases expression exp
      (const-exp (num) #t)
      (var-exp (var) #t)
      (diff-exp (exp1 exp2)
                (and (inp-exp-simple? exp1) (inp-exp-simple? exp2)))
      (zero?-exp (exp1) (inp-exp-simple? exp1))
      (proc-exp (ids exp) #t)
      (sum-exp (exps) (every? inp-exp-simple? exps))
      (else #f))))


; cps-of-simple-exp: inpexp -> simpleexp
; usage: assumes (inp-exp-simple? exp)
(define cps-of-simple-exp
  (lambda (exp)
    (cases expression exp
      (const-exp (num) (cps-const-exp num))
      (var-exp (var) (cps-var-exp var))
      (diff-exp (exp1 exp2)
                (cps-diff-exp (cps-of-simple-exp exp1)
                              (cps-of-simple-exp exp2)))
      (zero?-exp (exp1)
                 (cps-zero?-exp (cps-of-simple-exp exp1)))
      (proc-exp (ids exp)
                (cps-proc-exp (append ids (list 'k%00))
                              (cps-of-exp exp (cps-var-exp 'k%00))))
      (sum-exp (exps)
               (cps-sum-exp (map cps-of-simple-exp exps)))
      (else
       (eopl:error 'exp-to-cps-simple-exp exp)))))


; cps-of-exp : inpexp x simpleexp -> tfexp
(define cps-of-exp
  (lambda (exp k-exp)
    (cases expression exp
      (const-exp (num)
                 (make-send-to-cont k-exp (cps-const-exp num)))
      (var-exp (var)
               (make-send-to-cont k-exp (cps-var-exp var)))
      (proc-exp (vars body)
                (make-send-to-cont k-exp
                                   (cps-proc-exp (append vars (list 'k%00))
                                                 (cps-of-exp body (cps-var-exp 'k%00)))))
      (zero?-exp (exp1)
                 (cps-of-zero?-exp exp1 k-exp))
      (diff-exp (exp1 exp2)
                (cps-of-diff-exp exp1 exp2 k-exp))
      (sum-exp (exps)
               (cps-of-sum-exp exps k-exp))
      (if-exp (exp1 exp2 exp3)
              (cps-of-if-exp exp1 exp2 exp3 k-exp))
      (let-exp (var exp1 body)
               (cps-of-let-exp var exp1 body k-exp))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (cps-of-letrec-exp p-names b-varss p-bodies letrec-body k-exp))
      (call-exp (rator rands)
                (cps-of-call-exp rator rands k-exp))
      )))


; cps-of-sum-exp: listof(inpexp) x simpleexp -> tfexp
(define cps-of-sum-exp
  (lambda (exps k-exp)
    (cps-of-exps exps
                 (lambda (simples)
                   (make-send-to-cont k-exp (cps-sum-exp simples))))))
(define cps-of-zero?-exp
  (lambda (exp1 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (make-send-to-cont k-exp (cps-zero?-exp (car simples)))))))
(define cps-of-diff-exp
  (lambda (exp1 exp2 k-exp)
    (cps-of-exps (list exp1 exp2)
                 (lambda (simples)
                   (make-send-to-cont k-exp (cps-diff-exp (car simples) (cadr simples)))))))
(define cps-of-if-exp
  (lambda (exp1 exp2 exp3 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (cps-if-exp (car simples)
                               (cps-of-exp exp2 k-exp)
                               (cps-of-exp exp3 k-exp))))))
(define cps-of-let-exp
  (lambda (var exp1 body k-exp)
    (cps-of-exps* (list exp1)
                  (list var)
                  (lambda (simples)
                    (cps-of-exp body k-exp)))))
(define cps-of-letrec-exp
  (lambda (p-names b-varss p-bodies letrec-body k-exp)
    (cps-letrec-exp p-names
                    (map (lambda (b-vars) (append b-vars (list 'k%00))) b-varss)
                    (map (lambda (p-body) (cps-of-exp p-body (cps-var-exp 'k%00))) p-bodies)
                    (cps-of-exp letrec-body k-exp))))


; cps-of-call-exp: inpexp x listof(inpexp) x simpleexp -> tfexp
(define cps-of-call-exp
  (lambda (rator rands k-exp)
    (cps-of-exps (cons rator rands)
                  (lambda (simples)
                    (cps-call-exp (car simples)
                                  (append (cdr simples) (list k-exp)))))))
