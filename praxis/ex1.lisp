;;; -*- mode:lisp; coding:utf-8 -*-

;;; compile as: (load "ex1.lisp" :bin #() :output "ex1.js")

(unless (find :lisa *features*)
  (require "./lisa-0.2.js"))

(deftemplate goal-is () (slot action) (slot detail))

(defrule r-2 ()
  (?g (goal-is (action ?a1 (eq ?a1 :run)) (detail ?d)))
  =>
  (format t "Running ~a~%" ?d)
  (retract ?g))

;;; (cmd-run 'lisp)
(defun cmd-run (what)
  (assert> (goal-is (action :run) (detail `,what)))
  (run))

;;;EOF
