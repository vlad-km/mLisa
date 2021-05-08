;;; -*- mode:lisp; coding:utf-8 -*-

;;; This file is part of LISA, the Lisp-based Intelligent Software
;;; Agents platform.
;;; Copyright (C) 2000 David E. Young (de.young@computer.org)
;;; File: config.lisp
;;; Description: User-customisable configuration settings for LISA. It is
;;; expected that developers will edit this file as they see fit.
;;; The reference guide has complete details, but:
;;; * Setting USE-FANCY-ASSERT enables the #? dispatch macro character.
;;; * Setting ALLOW-DUPLICATE-FACTS disables duplicate fact checking during
;;;   assertions.
;;; * Setting CONSIDER-TAXONOMY instructs LISA to consider a CLOS instance's
;;;   ancestors during pattern matching.

;;; Modification for JSCL under Electron platform
;;; Copyright (C) 2021 Vladimir K. Mezentsev (@vlad-km)

(eval-when (:load-toplevel)
  (setf (use-fancy-assert) t)
  (setf (allow-duplicate-facts) t)
  (setf (consider-taxonomy) t))

;;; File: epilogue.lisp
(deftemplate initial-fact ())
(deftemplate query-fact ())

;;; This macro is courtesy of Paul Werkowski. A very nice idea.
#+nil
(defmacro define-lisa-lisp ()
  (flet ((externals-of (pkg)
           (loop for s being each external-symbol in pkg collect s)))
    (let* ((lisa-externs (externals-of "LISA"))
           (lisa-shadows (intersection (package-shadowing-symbols "LISA")
                                       lisa-externs))
           (cl-externs (externals-of "COMMON-LISP")))
      `(defpackage "LISA-LISP"
         (:use "COMMON-LISP")
         (:shadowing-import-from "LISA" ,@lisa-shadows)
         (:import-from "LISA" ,@(set-difference lisa-externs lisa-shadows))
         (:export ,@cl-externs)
         (:export ,@lisa-externs)))))

#+nil
(eval-when (:load-toplevel :execute)
  (make-default-inference-engine)
  (setf *active-context* (initial-context (inference-engine)))
  (define-lisa-lisp)
  (when (use-fancy-assert)
    (set-dispatch-macro-character
     #\# #\? #'(lambda (strm subchar arg)
                 (declare (ignore subchar arg))
                 (list 'identity (read strm t nil t)))))
  (pushnew :lisa *features*))

(eval-when (:load-toplevel :execute)
  (make-default-inference-engine)
  (setf *active-context* (initial-context (inference-engine)))
  #+nil (define-lisa-lisp)
  #+nil
  (when (use-fancy-assert)
    (set-dispatch-macro-character
     #\# #\? #'(lambda (strm subchar arg)
                 (declare (ignore subchar arg))
                 (list 'identity (read strm t nil t)))))
  (pushnew :lisa *features*))


;;; EOF
