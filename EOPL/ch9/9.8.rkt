#lang eopl
(define identifier? symbol?)
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar
  '((program ((arbno class-decl) expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression)
                          "in" expression) letrec-exp)
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    (expression ("list" "(" (separated-list expression ",") ")" ) list-exp)
    (expression ("empty?" "(" expression ")" ) empty-exp)
    (expression ("car" "(" expression ")" ) car-exp)
    (expression ("cdr" "(" expression ")" ) cdr-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (class-decl ("class" identifier "extends" identifier
                         (arbno "field" identifier) (arbno method-decl)) a-class-decl)
    (method-decl ("method" identifier "("  (separated-list identifier ",") ")" 
                           expression) a-method-decl)
    (expression ("new" identifier "(" (separated-list expression ",") ")") new-object-exp)
    (expression ("self") self-exp)
    (expression ("send" expression identifier
                        "("  (separated-list expression ",") ")") method-call-exp)

    (expression ("super" identifier    "("  (separated-list expression ",") ")") super-call-exp)
    (expression ("fieldref" expression identifier) fieldref-exp)
    (expression ("fieldset" expression identifier "=" expression) fieldset-exp)
    ))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

; ----------------------------------------------------------------------------------------------
; expval

(define-datatype proc proc?
  (procedure
   (vars (list-of symbol?))
   (body expression?)
   (env environment?)))

(define-datatype expval expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?))
  (obj-val (obj object?))
  (list-val (lst (list-of expval?))))

(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (else (expval-extractor-error 'num v)))))

(define expval->bool
  (lambda (v)
    (cases expval v
      (bool-val (bool) bool)
      (else (expval-extractor-error 'bool v)))))

(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc v)))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))


; -------------------------------------------------------------------------------
; reference and store

(define the-store 'uninitialized)

; empty-store : () -> store
(define empty-store
  (lambda () '()))

; initialize-store! : () -> store
; usage: (initialize-store!) sets the-store to the empty-store
(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

; get-store : () -> Sto
(define get-store
  (lambda () the-store))

;; reference? : SchemeVal -> Bool
(define reference?
  (lambda (v)
    (integer? v)))

;; newref : ExpVal -> Ref
(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store
            (append the-store (list val)))
      next-ref)))

;; deref : Ref -> ExpVal
(define deref
  (lambda (ref)
    (list-ref the-store ref)))

;; setref! : Ref * ExpVal -> Unspecified
(define setref!
  (lambda (ref val)
    (set! the-store
          (letrec
              ((setref-inner
                (lambda (store1 ref1)
                  (cond
                    ((null? store1)
                     (report-invalid-reference ref the-store))
                    ((zero? ref1)
                     (cons val (cdr store1)))
                    (else
                     (cons
                      (car store1)
                      (setref-inner
                       (cdr store1) (- ref1 1))))))))
            (setref-inner the-store ref)))))

(define report-invalid-reference
  (lambda (ref the-store)
    (eopl:error 'setref
                "illegal reference ~s in store ~s"
                ref the-store)))
; --------------------------------------------------------------------------------------
; environment

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (bvars (list-of symbol?))
   (bvals (list-of reference?))
   (saved-env environment?))
  (extend-env-rec**
   (proc-names (list-of symbol?))
   (b-varss (list-of (list-of symbol?)))
   (proc-bodies (list-of expression?))
   (saved-env environment?))
  (extend-env-with-self-and-super
   (self object?)
   (super-name symbol?)
   (saved-env environment?)))

(define init-env
  (lambda () (empty-env)))

(define extend-env1
  (lambda (id val env)
    (extend-env (list id) (list val) env)))

(define apply-env
  (lambda (env search-sym)
    (cases environment env
      (empty-env ()
                 (eopl:error 'apply-env "No binding for ~s" search-sym))
      (extend-env (bvars bvals saved-env)
                  (cond
                    ((location search-sym bvars) => (lambda (n) (list-ref bvals n)))
                    (else (apply-env saved-env search-sym))))
      (extend-env-rec** (p-names b-varss p-bodies saved-env)
                        (cond ((location search-sym p-names)
                               => (lambda (n) (newref (proc-val (procedure
                                                                 (list-ref b-varss n)
                                                                 (list-ref p-bodies n)
                                                                 env)))))
                              (else (apply-env saved-env search-sym))))
      (extend-env-with-self-and-super (self super-name saved-env)
                                      (case search-sym
                                        ((%self) self)
                                        ((%super) super-name)
                                        (else (apply-env saved-env search-sym)))))))

;; location : Sym * Listof(Sym) -> Maybe(Int)
;;   else (location sym syms) = #f
(define location
  (lambda (sym syms)
    (cond
      ((null? syms) #f)
      ((eqv? sym (car syms)) 0)
      ((location sym (cdr syms)) => (lambda (n) (+ n 1)))
      (else #f))))

; -----------------------------------------------------------------------------------
; class and method

(define-datatype object object?
  (an-object (class-name identifier?)
             (fields (list-of reference?))))

; new-object : sym -> obj
(define new-object
  (lambda (class-name)
    (an-object class-name
               (map (lambda (field-name) (newref (list 'uninitialized-field field-name)))
                    (class->field-names (lookup-class class-name))))))

(define-datatype method method?
  (a-method (vars (list-of identifier?))
            (body expression?)
            (super-name identifier?)
            (field-names (list-of identifier?))))

;; apply-method : method * obj * listof(expVal) -> expVal
(define apply-method
  (lambda (m self args)
    (cases method m
      (a-method (vars body super-name field-names)
                (value-of body
                          (extend-env vars (map newref args)
                                      (extend-env-with-self-and-super
                                       self super-name
                                       (extend-env field-names (object->fields self)
                                                   (empty-env)))))))))

;; the-calss-env : classenv
(define the-class-env '())

;; add-to-class-env! : classname * class -> Unspecified
(define add-to-class-env!
  (lambda (class-name class)
    (set! the-class-env
          (cons (list class-name class)
                the-class-env))))

;; lookup-class : className -> class
(define lookup-class
  (lambda (name)
    (let ([maybe-pair (assq name the-class-env)])
      (if maybe-pair
          (cadr maybe-pair)
          (report-unknown-class name)))))

(define report-unknown-class
  (lambda (name)
    (eopl:error 'lookup-class "Unknown class ~s" name)))

(define-datatype class class?
  (a-class (super-name (maybe identifier?))
           (field-names (list-of identifier?))
           (method-env method-environment?)))

;; a method environment looks like ((method-name method) ...)
(define method-environment?
  (list-of (lambda (p) (and (pair? p)
                            (symbol? (car p))
                            (method? (cadr p))))))

;; initialize-class-env! : ClassDecl -> Unspecified
(define initialize-class-env!
  (lambda (c-decls)
    (set! the-class-env
          (list
           (list 'object (a-class #f '() '()))))
    (for-each initialize-class-decl! c-decls)))

;; initialize-class-decl! : ClassDecl -> Unspecified
(define initialize-class-decl!
  (lambda (c-decl)
    (cases class-decl c-decl
      (a-class-decl (c-name s-name f-names m-decls)
                    (let ([f-names
                           (append-field-names
                            (class->field-names (lookup-class s-name))
                            f-names)])
                      (add-to-class-env!
                       c-name
                       (a-class s-name f-names
                                (merge-method-envs
                                 (class->method-env (lookup-class s-name))
                                 (method-decls->method-env
                                  m-decls s-name f-names)))))))))

; append-field-names :
; listof(FieldName) * Listof(FieldName) -> Listof(FieldName)
(define append-field-names
  (lambda (super-fields new-fields)
    (cond
      [(null? super-fields) new-fields]
      [else
       (cons
        (if (memq (car super-fields) new-fields)
            (fresh-identifier (car super-fields))
            (car super-fields))
        (append-field-names
         (cdr super-fields) new-fields))])))

; find-method : Sym * Sym -> Method
(define find-method
  (lambda (c-name name)
    (let ([m-env (class->method-env (lookup-class c-name))])
      (let ([maybe-pair (assq name m-env)])
        (if (pair? maybe-pair) (cadr maybe-pair)
            (report-method-not-found name))))))

(define report-method-not-found
  (lambda (name)
    (eopl:error 'find-method "unknown method ~s" name)))

; method-decls -> method-env
(define method-decls->method-env
  (lambda (m-decls super-name field-names)
    (map
     (lambda (m-decl)
       (cases method-decl m-decl
         (a-method-decl (method-name vars body)
                        (list method-name
                              (a-method vars body super-name field-names)))))
     m-decls)))

; merge-method-envs : MethodEnv * MethodEnv -> MethodEnv
(define merge-method-envs
  (lambda (super-m-env new-m-env)
    (append new-m-env super-m-env)))


; selector
(define class->super-name
  (lambda (c-struct)
    (cases class c-struct
	   (a-class (super-name field-names method-env)
		    super-name))))

(define class->field-names
  (lambda (c-struct)
    (cases class c-struct
	   (a-class (super-name field-names method-env)
		    field-names))))

(define class->method-env
  (lambda (c-struct)
    (cases class c-struct
	   (a-class (super-name  field-names method-env)
		    method-env))))


(define object->class-name
  (lambda (obj)
    (cases object obj
	   (an-object (class-name fields)
		      class-name))))

(define object->fields
  (lambda (obj)
    (cases object obj
      (an-object (class-decl fields)
                 fields))))

(define fresh-identifier
  (let ((sn 0))
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append
        (symbol->string identifier)
        "%"             ; this can't appear in an input identifier
        (number->string sn))))))

(define maybe
  (lambda (pred)
    (lambda (v)
      (or (not v) (pred v)))))

(define field-ref
  (lambda (obj f-name)
    (let* ((field-names (class->field-names (lookup-class (object->class-name obj))))
           (new-env (extend-env field-names
                                (object->fields obj)
                                (empty-env))))
      (deref (apply-env new-env f-name)))))
(define field-set
  (lambda (obj f-name val)
    (let* ((field-names (class->field-names (lookup-class (object->class-name obj))))
           (new-env (extend-env field-names
                                (object->fields obj)
                                (empty-env))))
      (setref! (apply-env new-env f-name) val))))



; -------------------------------------------------------------
; interpreter

;; apply-procedure : Proc * Listof(ExpVal) -> ExpVal
(define apply-procedure
    (lambda (proc1 args)
      (cases proc proc1
        (procedure (vars body saved-env)
          (let ((new-env (extend-env vars (map newref args) saved-env)))
            (value-of body new-env))))))

; value-of : exp * env -> expval
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (deref (apply-env env var)))
      (diff-exp (exp1 exp2)
                (let ((val1 (expval->num (value-of exp1 env)))
                      (val2 (expval->num (value-of exp2 env))))
                  (num-val (- val1 val2))))
      (zero?-exp (exp1)
                 (let ((val1 (expval->num (value-of exp1 env))))
                   (if (zero? val1)
                       (bool-val #t)
                       (bool-val #f))))
      (if-exp (exp0 exp1 exp2)
              (if (expval->bool (value-of exp0 env))
                  (value-of exp1 env)
                  (value-of exp2 env)))
      (let-exp (vars exps body)
               (let ((new-env
                      (extend-env vars (map newref (values-of-exps exps env)) env)))
                 (value-of body new-env)))
      (proc-exp (bvars body)
                (proc-val
                 (procedure bvars body env)))
      (call-exp (rator rands)
                (let ((proc (expval->proc (value-of rator env)))
                      (args (values-of-exps rands env)))
                  (apply-procedure proc args)))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (value-of letrec-body
                            (extend-env-rec** p-names b-varss p-bodies env)))
      (begin-exp (exp1 exps)
                 (letrec ((value-of-begins
                           (lambda (e1 es)
                             (let ((v1 (value-of e1 env)))
                               (if (null? es)
                                   v1
                                   (value-of-begins (car es) (cdr es)))))))
                   (value-of-begins exp1 exps)))
      (assign-exp (x e)
                  (begin (setref! (apply-env env x)
                                  (value-of e env))
                         (num-val 27)))
      (list-exp (exps)
                (list-val (values-of-exps exps env)))
      (empty-exp (exp)
                 (let ((val (value-of exp env)))
                   (cases expval val
                     (list-val (vals)
                               (if (null? vals)
                                   (bool-val #t)
                                   (bool-val #f)))
                     (else
                      (eopl:error "empty: error type ~s" exp)))))
      (car-exp (exp)
               (let ((val (value-of exp env)))
                 (cases expval val
                   (list-val (vals)
                             (if (null? vals)
                                 (eopl:error "car: empty list")
                                 (car vals)))
                   (else
                    (eopl:error "car: error type ~s" exp)))))
      (cdr-exp (exp)
               (let ((val (value-of exp env)))
                 (cases expval val
                   (list-val (vals)
                             (if (null? vals)
                                 (eopl:error "cdr: empty list")
                                 (list-val (cdr vals))))
                   (else (eopl:error "cdr: error type ~s" exp)))))
      (cons-exp (arg1 arg2)
                (let ((val1 (value-of arg1 env))
                      (val2 (value-of arg2 env)))
                  (cases expval val2
                    (list-val (vals)
                              (list-val (cons val1 vals)))
                    (else
                     (eopl:error "cons: error type ~s" arg2)))))
      (self-exp () (apply-env env '%self))
      (method-call-exp (obj-exp method-name rands)
                       (let ((args (values-of-exps rands env))
                             (obj (value-of obj-exp env)))
                         (apply-method
                          (find-method (object->class-name obj) method-name) obj args)))
      (super-call-exp (method-name rands)
                      (let ((args (values-of-exps rands env))
                            (obj (apply-env env '%self)))
                        (apply-method
                         (find-method (apply-env env '%super) method-name) obj args)))
      (new-object-exp (class-name rands)
                      (let ([args (values-of-exps rands env)]
                            [obj (new-object class-name)])
                        (apply-method (find-method class-name 'initialize) obj args)
                        obj))
      (fieldref-exp (exp1 f-name)
                    (field-ref (value-of exp1 env) f-name))
      (fieldset-exp (exp1 f-name val)
                    (field-set (value-of exp1 env) f-name val))
      )))

(define values-of-exps
    (lambda (exps env)
      (map (lambda (exp) (value-of exp env)) exps)))


;; value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program pgm
      (a-program (class-decls body)
                 (initialize-class-env! class-decls)
                 (value-of body (init-env))))))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(run "class counter extends object
      field val
      method initialize() set val = 0
      method inc() set val = -(val,-1)
      method cnt() val
    
      class queue extends object
      field q
      field counter
      method empty() begin send counter inc(); empty?(q) end
      method initialize(cnt) begin set q = list(); set counter = cnt end
      method enqueue(x) begin set q = cons(x,q);
                              send counter inc() end
      method dequeue() let a = car(q)
                       in begin set q = cdr(q) ;
                                send counter inc(); 
                                a end
      method cnt() send counter cnt()
      let the_counter = new counter()
      in let q1 = new queue(the_counter)
      in let q2 = new queue(the_counter)
      in begin send q1 enqueue(3);
               send q1 dequeue();
               send q1 empty();
               send q2 enqueue(3);
               send q2 dequeue();
               send q2 empty();
               send q1 cnt();
               fieldref the_counter val;
               fieldset the_counter val = 10;
               fieldref the_counter val end")



