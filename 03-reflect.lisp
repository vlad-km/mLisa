;;; -*- mode:lisp; coding:utf-8 -*-

;;; This file is part of LISA, the Lisp-based Intelligent Software
;;; Agents platform.
;;; Copyright (C) 2000 David E. Young (de.young@computer.org)

;;; File: reflect.lisp
;;; Description: Wrapper functions that provide the MOP functionality needed
;;; by LISA, hiding implementation-specific details.

;;; Modification for JSCL under Electron platform
;;; Copyright (C) 2021 Vladimir K. Mezentsev (@vlad-km)

;;(in-package :reflect)

(defun class-slots* (obj)
  (class-slots
   (typecase obj
     (symbol (find-class obj))
     (standard-class obj)
     (standard-object (find-class (class-name (class-of obj))))
     (t (class-of obj)))))

(defun slot-name (slot) (slot-definition-name slot))
(defun slot-alloc (slot) (slot-definition-allocation slot))
(defun slot-one-initarg (slot) (slot-definition-initargs slot))

(defun class-slot-list (class &optional (all t))
  "Return the list of slots of a CLASS.
CLASS can be a symbol, a class object (as returned by `class-of')
or an instance of a class.
If the second optional argument ALL is non-NIL (default),
all slots are returned, otherwise only the slots with
:allocation type :instance are returned."
  ;;(unless (class-finalized-p class)(finalize-inheritance class))
  (mapcan (if all
              (lilu:compose list slot-name)
              (lambda (slot)
                (when (eq (slot-alloc slot) :instance)
                  (list (slot-name slot)))))
          (class-slots* class)))

(defun class-slot-initargs (class &optional (all t))
  "Return the list of initargs of a CLASS.
CLASS can be a symbol, a class object (as returned by `class-of')
or an instance of a class.
If the second optional argument ALL is non-NIL (default),
initargs for all slots are returned, otherwise only the slots with
:allocation type :instance are returned."
  (mapcan (if all (lilu:compose list slot-one-initarg)
              (lambda (slot)
                (when (eq (slot-alloc slot) :instance)
                  (list (slot-one-initarg slot)))))
          (class-slots* class)))

;;; note: 
(defun ensure-class* (name &key (direct-superclasses '()))
  (eval `(defclass ,name ,direct-superclasses ())))

(defun is-standard-classp (class)
  (or (eq (class-name class) 'standard-object)
       (eq (class-name class) t)))

(defun find-direct-superclasses (class)
  (remove-if #'is-standard-classp (class-direct-superclasses class)))
             
(defun class-all-superclasses (class-or-symbol)
  (labels ((find-superclasses (class-list superclass-list)
             (let ((class (first class-list)))
               (if (or (null class-list)(is-standard-classp class))
                   superclass-list
                   (find-superclasses
                    (find-direct-superclasses class)
                    (find-superclasses (rest class-list) (pushnew class superclass-list)))))))
    (let ((class
            (if (symbolp class-or-symbol)
                (find-class class-or-symbol)
                class-or-symbol)))
      (nreverse (find-superclasses (find-direct-superclasses class) nil)))))

;;; EOF
