;;; -*- mode:lisp; coding:utf-8 -*-

;;; This file is part of LISA, the Lisp-based Intelligent Software
;;; Agents platform.
;;; Copyright (C) 2000 David E. Young (de.young@computer.org)

;;; Modification for JSCL under Electron platform
;;; Copyright (C) 2021 Vladimir K. Mezentsev (@vlad-km)

;;; File: belief.lisp
;;; Description: Common interfaces to Lisa's belief-system interface.

(in-package :belief)

;;; The principal interface by which outside code hooks objects that support some kind of belief-factor
;;; interface into this library.

(defgeneric belief-factor (obj))
(defgeneric adjust-belief (objects rule-belief &optional old-belief))
(defgeneric belief->english (belief-factor))

;;; File: null-belief-system.lisp

;;; interface into the generic belief system.

(defmethod belief-factor ((obj t))
  nil)

(defmethod adjust-belief ((objects t) (rule-belief t) &optional (old-belief nil))
  nil)

(defmethod belief->english ((belief t))
  nil)

(defconstant +true+ 1.0)
(defconstant +false+ -1.0)
(defconstant +unknown+ 0.0)

(defun certainty-factor-p (number)
  (<= +false+ number +true+))

(deftype certainty-factor ()
  `(and (real)
        (satisfies certainty-factor-p)))

(defun true-p (cf)
  (check-type cf certainty-factor)
  (> cf +unknown+))

(defun false-p (cf)
  (check-type cf certainty-factor)
  (< cf +unknown+))

(defun unknown-p (cf)
  (check-type cf certainty-factor)
  (= cf +unknown+))

(defun cf-combine (a b)
  (check-type a certainty-factor)
  (check-type b certainty-factor)
  (cond ((and (plusp a)
              (plusp b))
         (+ a b (* -1 a b)))
        ((and (minusp a)
              (minusp b))
         (+ a b (* a b)))
        (t (/ (+ a b)
              (- 1 (min (abs a) (abs b)))))))

;;;  "Combines the certainty factors of objects matched within a single rule."
(defun conjunct-cf (objects)
  (let ((conjuncts
         (loop for obj in objects
               for cf = (belief-factor obj)
               if cf collect cf)))
    (if conjuncts
        (apply #'min conjuncts)
      nil)))

(defgeneric recalculate-cf (objects rule-cf old-cf))

(defmethod recalculate-cf (objects (rule-cf number) (old-cf number))
   (let* ((combined-cf (conjunct-cf objects))
          (new-cf (if combined-cf (* rule-cf combined-cf) rule-cf)))
     (cf-combine old-cf new-cf)))

(defmethod recalculate-cf (objects (rule-cf number) (old-cf t))
   (let* ((combined-cf (conjunct-cf objects))
          (new-cf (if combined-cf combined-cf rule-cf))
          (factor (if combined-cf rule-cf 1.0)))
     (* new-cf factor)))

(defmethod recalculate-cf (objects (rule-cf t) (old-cf t))
   (let* ((combined-cf (conjunct-cf objects)))
     (if combined-cf
         (* combined-cf 1.0)
       nil)))

(defun cf->english (cf)
  (cond ((= cf 1.0) "certain evidence")
        ((> cf 0.8) "strongly suggestive evidence")
        ((> cf 0.5) "suggestive evidence")
        ((> cf 0.0) "weakly suggestive evidence")
        ((= cf 0.0) "no evidence either way")
        ((< cf 0.0) (jscl::concat (cf->english (- cf)) " against the conclusion"))))

(defmethod adjust-belief (objects (rule-belief number) &optional (old-belief nil))
  (recalculate-cf objects rule-belief old-belief))

(defmethod adjust-belief (objects (rule-belief t) &optional old-belief)
  (declare (ignore objects old-belief))
  nil)

(defmethod belief->english ((cf number))
  (cf->english cf))

(export '(belief::ADJUST-BELIEF belief::BELIEF->ENGLISH
           belief::BELIEF-FACTOR belief::FALSE-P belief::TRUE-P belief::UKNOWN-P))

(in-package :cl-user)

;;; EOF
