#lang eopl
; (value-of exp env sigma) = (val sigma_1)
; (value-of (let-exp var exp body) env sigma)
; = (value-of body [var=l]env [l=val]sigma_1)