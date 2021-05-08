;;; -*- mode:lisp; coding:utf-8 -*-

;;; This file is part of LISA, the Lisp-based Intelligent Software
;;; Agents platform.
;;; Copyright (C) 2000 David E. Young (de.young@computer.org)
;;; File: compose.lisp
;;; Description: Utilities used to compose anonymous functions.

;;; Modification for JSCL under Electron platform
;;; Copyright (C) 2021 Vladimir K. Mezentsev (@vlad-km)

#+nil
(defun build-lambda-expression (forms)
  (labels ((compose-body (forms &optional (body nil))
             (if (null forms)
                 body
               (compose-body (rest forms)
                             (nconc body
                                    `(,(first forms)))))))
    `(lambda ()
       (progn ,@(compose-body forms)))))
  
#+nil
(defmacro compile-function (forms)
  "Build and compile an anonymous function, using the body provided in
  FORMS."
  `(compile nil (build-lambda-expression ,forms)))

;;; File: utils.lisp

(in-package :lilu)
;;; This version of FIND-BEFORE courtesy of Bob Bane, Global Science and
;;; Technology...
;;;"Returns both that portion of SEQUENCE that occurs before ITEM and
;;;  the rest of SEQUENCE anchored at ITEM, or NIL otherwise."
(defun find-before (item sequence &key (test #'eql))
  (labels ((find-item (obj seq test val valend)
	     (let ((item (first seq)))
               (cond ((null seq)
                      (values nil nil))
                     ((funcall test obj item)
                      (values val seq))
                     (t
                      (let ((newend `(,item)))
                        (nconc valend newend)
                        (find-item obj (rest seq) test val newend)))))))
    (if (funcall test item (car sequence))
        (values nil sequence)
      (let ((head (list (car sequence))))
        (find-item item (cdr sequence) test head head)))))

;;;  "Returns that portion of SEQUENCE that occurs after ITEM, or NIL
;;;  otherwise."
(defun find-after (item sequence &key (test #'eql))
  (cond ((null sequence)
         (values nil))
        ((funcall test item (first sequence))
         (rest sequence))
        (t (find-after item (rest sequence) :test test))))

(defun find-if-after (predicate sequence)
  (cond ((null sequence)
         (values nil))
        ((funcall predicate (first sequence))
         (rest sequence))
        (t
         (find-if-after predicate (rest sequence)))))
(export '(lilu::find-before lilu::find-after lilu::find-if-after))

;;; Courtesy of Paul Graham...
(defun flatten (x)
  (labels ((rec (x acc)
             (cond ((null x) acc)
                   ((atom x) (cons x acc))
                   (t (rec (car x) (rec (cdr x) acc))))))
    (rec x nil)))
(export '(lilu::flatten))
(in-package :cl-user)

#+nil
(defun lsthash (func ht)
  "Applies FUNC to each entry in hashtable HT and, if FUNC so
  indicates, appends the object to a LIST. If NIL is an acceptable
  object, then FUNC should return two values; NIL and T."
  (let ((seq (list)))
    (maphash #'(lambda (key val)
                 (multiple-value-bind (obj use-p)
                     (funcall func key val)
                   (unless (and (null obj)
                                (not use-p))
                     (push obj seq)))) ht)
    (values seq)))

#+nil
(defun collect (predicate list)
  (let ((collection (list)))
    (dolist (obj list)
      (when (funcall predicate obj)
        (push obj collection)))
    (nreverse collection)))

;;; All code below courtesy of the PORT module, CLOCC project.

;;;
;;; Conditions
;;;

;;; (:documentation "An error in the user code.")
(define-condition code (error)
  ((proc :reader code-proc :initarg :proc)
   (mesg :type simple-string :reader code-mesg :initarg :mesg)
   (args :type list :reader code-args :initarg :args))
  ;;(:documentation "An error in the user code.")
  (:report (lambda (cc out)
             (declare (stream out))
             (format out "[~s]~@[ ~?~]" (code-proc cc)
                     (and (slot-boundp cc 'mesg) (code-mesg cc))
                     (and (slot-boundp cc 'args) (code-args cc))))))

;;; An error in a case statement.
;;; This carries the function name which makes the error message more useful.
(define-condition case-error (code)
  ((mesg :type simple-string :reader code-mesg :initform
         "`~s' evaluated to `~s', not one of [~@{`~s'~^ ~}]")))

;;; "Your implementation does not support this functionality."
(define-condition not-implemented (code)
  ((mesg :type simple-string :reader code-mesg :initform
         "not implemented for ~a [~a]")
   (args :type list :reader code-args :initform
         (list (lisp-implementation-type) (lisp-implementation-version)))))

;;;
;;; Extensions
;;;

#+nil
(defmacro mk-arr (type init &optional len)
  "Make array with elements of TYPE, initializing."
  (if len `(make-array ,len :element-type ,type :initial-element ,init)
      `(make-array (length ,init) :element-type ,type
        :initial-contents ,init)))

(in-package :lilu)

(defmacro with-gensyms (syms &body body)
  "Bind symbols to gensyms.  First sym is a string - `gensym' prefix.
Inspired by Paul Graham, <On Lisp>, p. 145."
  `(let (,@(mapcar (lambda (sy) `(,sy (gensym ,(car syms)))) (cdr syms)))
    ,@body))

(defmacro map-in (fn seq &rest seqs)
  "`map-into' the first sequence, evaluating it once.
  (map-in F S) == (map-into S F S)"
  (with-gensyms ("MI-" mi)
    `(let ((,mi ,seq)) (map-into ,mi ,fn ,mi ,@seqs))))

(export '(lilu::with-gensym lilu::map-in))
(in-package :cl-user)

#+nil
(defparameter +eof+ (list '+eof+)
  "*The end-of-file object.
To be passed as the third arg to `read' and checked against using `eq'.")

;;; bug:
#+nil
(defun eof-p (stream)
  "Return T if the stream has no more data in it."
  (null (peek-char nil stream nil nil)))

;;; todo: bug:
#+nil
(defun string-tokens (string &key (start 0) max)
  "Read from STRING repeatedly, starting with START, up to MAX tokens.
Return the list of objects read and the final index in STRING.
Binds `*package*' to the keyword package,
so that the bare symbols are read as keywords."
  ;;(declare (type (or null fixnum) max) (type fixnum start))
  (let ((*package* (find-package :keyword)))
    (if max
        (do ((beg start) obj res (num 0 (1+ num)))
            ((= max num) (values (nreverse res) beg))
          ;;(declare (fixnum beg num))
          ;; bug: setf values
          (setf (values obj beg)
                (read-from-string string nil +eof+ :start beg))
          (if (eq obj +eof+)
              (return (values (nreverse res) beg))
              (push obj res)))
        ;; bug: concatenate
        (read-from-string (jscl::concat "(" string ")")
                          t nil :start start))))

#+nil
(defun required-argument ()
  "A useful default for required arguments and DEFSTRUCT slots."
  (error "A required argument was not supplied."))

(in-package :lilu)
(defmacro compose (&rest functions)
  "Macro: compose functions or macros of 1 argument into a lambda.
E.g., (compose abs (dl-val zz) 'key) ==>
  (lambda (yy) (abs (funcall (dl-val zz) (funcall key yy))))"
  (labels ((rec (xx yy)
             (let ((rr (list (car xx) (if (cdr xx) (rec (cdr xx) yy) yy))))
               (if (consp (car xx))
                   (cons 'funcall (if (eq (caar xx) 'quote)
                                      (cons (cadar xx) (cdr rr)) rr))
                   rr))))
    (with-gensyms ("COMPOSE-" arg)
      (let ((ff (rec functions arg)))
        `(lambda (,arg) ,ff)))))
(export '(lilu::compose))
(in-package :cl-user)

;;; EOF
