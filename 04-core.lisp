;;; -*- mode:lisp; coding:utf-8 -*-

;;; This file is part of LISA, the Lisp-based Intelligent Software
;;; Agents platform.
;;; Copyright (C) 2000 David E. Young (de.young@computer.org)

;;; Modification for JSCL under Electron platform
;;; Copyright (C) 2021 Vladimir K. Mezentsev (@vlad-km)

;;; File: preamble.lisp


(defvar *active-rule* nil)
(defvar *active-engine* nil)
(defvar *active-tokens* nil)
(defvar *active-context* nil)
(defvar *ignore-this-instance*)

(defmacro with-auto-notify ((var instance) &body body)
  `(let* ((,var ,instance)
          (*ignore-this-instance* ,var))
     ,@body))

(defgeneric make-rete-network (&rest args &key &allow-other-keys))

(defun active-context ()  *active-context*)
(defun active-tokens ()  *active-tokens*)
(defun active-rule ()   *active-rule*)
(defun active-engine ()   *active-engine*)
(defun in-rule-firing-p () (not (null (active-rule))))


(defgeneric equals (a b))
(defgeneric slot-value-of-instance (object slot-name))
(defgeneric (setf slot-value-of-instance) (new-value object slot-name))
(defgeneric activation-priority (self))
(defgeneric fire-activation (self))
(defgeneric hash-key (self))
(defgeneric reset-activations (self))
(defgeneric insert-activation (self activation))
(defgeneric lookup-activation (self rule tokens))
(defgeneric get-next-activation (self))
(defgeneric get-all-activations (self))
(defgeneric add-activation (self activation))
(defgeneric find-activation (self rule token))
(defgeneric find-all-activations (self  rule))
(defgeneric next-activation (self))
(defgeneric remove-activations (self))
(defgeneric list-activations (self))
(defgeneric find-rule-in-context (self rule-name))
(defgeneric conflict-set (self))
(defgeneric remove-rule-from-context (self rule-name))
(defgeneric fire-rule (self tokens))
(defgeneric retract (fact-object))
(defgeneric forget-rule (self rule-name))
(defgeneric assert-fact-aux (self  fact))
(defgeneric adjust-belief (rete fact belief-factor))
(defgeneric assert-fact (rete fact &key belief))
(defgeneric modify-fact (rete fact &rest slot-changes))
(defgeneric retract-fact (rete fact-id))
(defgeneric reset-engine (rete))
(defgeneric mark-clos-instance-as-changed (rete instance  &optional (slot-id nil)))
(defgeneric add-activation (rete activation))
(defgeneric disable-activation (rete activation))
(defgeneric run-engine (rete &optional (step -1)))
(defgeneric belief:belief-factor (fact))

(defvar *consider-taxonomy-when-reasoning* nil)
(defvar *allow-duplicate-facts* t)
(defvar *use-fancy-assert* t)

(defun consider-taxonomy ()  *consider-taxonomy-when-reasoning*)

(defun (setf consider-taxonomy) (new-value)
  (setq *consider-taxonomy-when-reasoning* new-value))

(defun allow-duplicate-facts () *allow-duplicate-facts*)

(defun (setf allow-duplicate-facts) (new-value)
  (setq *allow-duplicate-facts* new-value))

(defun use-fancy-assert ()  *use-fancy-assert*)

(defun (setf use-fancy-assert) (new-value)
  (setq *use-fancy-assert* new-value))

(defclass inference-engine-object () ())

(defvar *clear-handlers* (list))

(defmacro register-clear-handler (tag func)
  `(eval-when (:load-toplevel)
     (unless (assoc ,tag *clear-handlers* :test #'string=)
       (setf *clear-handlers*
         (acons ,tag ,func *clear-handlers*)))))

(defun clear-system-environment ()
  (mapc #'(lambda (assoc)
            (funcall (cdr assoc)))
        *clear-handlers*)
  t)

(defun clear-environment-handlers ()
  (setf *clear-handlers* nil))

(defun variable-p (obj)
  (and (symbolp obj)
       (eq (aref (symbol-name obj) 0) #\?)))


(defmacro starts-with-? (sym)
  `(eq (aref (symbol-name ,sym) 0) #\?))

(defmacro variablep (sym)
  `(variable-p ,sym))

(defmacro quotablep (obj)
  `(and (symbolp ,obj)
        (not (starts-with-? ,obj))))

(defmacro literalp (sym)
  `(or (and (symbolp ,sym)
            (not (variablep ,sym))
            (not (null ,sym)))
       (numberp ,sym) (stringp ,sym)))

(defmacro multifieldp (val)
  `(and (listp ,val)
    (eq (first ,val) 'quote)))

(defmacro slot-valuep (val)
  `(or (literalp ,val)
       (consp ,val)
       (variablep ,val)))

(defmacro constraintp (constraint)
  `(or (null ,constraint)
       (literalp ,constraint)
       (consp ,constraint)))

(defun make-default-inference-engine ()
  (when (null *active-engine*)
    (setf *active-engine* (make-inference-engine)))
  *active-engine*)

(defun use-default-engine ()
  (warn "USE-DEFAULT-ENGINE is deprecated. LISA now automatically creates a
  default instance of the inference engine at load time.")
  (when (null *active-engine*)
    (setf *active-engine* (make-inference-engine)))
  *active-engine*)

;;; todo:
;;; bug:
(defun current-engine (&optional (errorp t))
  "Returns the currently-active inference engine. Usually only invoked by code
  running within the context of WITH-INFERENCE-ENGINE."
  (when errorp
    (cl:assert (not (null *active-engine*)) (*active-engine*)
      "The current inference engine has not been established."))
  *active-engine*)

(defun inference-engine (&rest args)
  (apply #'current-engine args))

(defmacro with-inference-engine ((engine) &body body)
  "Evaluates BODY within the context of the inference engine ENGINE. This
    macro is MP-safe."
  `(let ((*active-engine* ,engine))
    (progn ,@body)))

(register-clear-handler
 "environment" 
 #'(lambda ()
     (setf *active-engine* (make-inference-engine))
     (setf *active-context* (find-context (inference-engine) :initial-context))))

;;; File: conditions.lisp


(define-condition duplicate-fact (error)
  ((existing-fact :reader duplicate-fact-existing-fact
                  :initarg :existing-fact))
  (:report (lambda (condition strm)
             (format strm "Lisa detected an attempt to assert a duplicate for: ~S"
                     (duplicate-fact-existing-fact condition)))))
                  
(define-condition parsing-error (error)
  ((text :initarg :text
         :initform nil
         :reader text)
   (location :initarg :location
             :initform nil
             :reader location))
  (:report (lambda (condition strm)
             (format strm "Parsing error: ~A" (text condition)))))

(define-condition slot-parsing-error (parsing-error)
  ((slot-name :initarg :slot-name
              :initform nil
              :reader slot-name))
  (:report (lambda (condition strm)
             (format strm "Slot parsing error: slot ~A, pattern location ~A"
                     (slot-name condition) (location condition))
             (when (text condition)
               (format strm " (~A)" (text condition))))))

(define-condition class-parsing-error (parsing-error)
  ((class-name :initarg :class-name
               :initform nil
               :reader class-name))
  (:report (lambda (condition strm)
             (format strm "Class parsing error: ~A, ~A" (class-name condition) (text condition)))))

(define-condition rule-parsing-error (parsing-error)
  ((rule-name :initarg :rule-name
              :initform nil
              :reader rule-name))
  (:report (lambda (condition strm)
             (format strm "Rule parsing error: rule name ~A, pattern location ~A"
                     (rule-name condition) (location condition))
             (when (text condition)
               (format strm " (~A)" (text condition))))))

;;; File: deffacts.lisp

;;; "This class represents 'autoloaded' facts that are asserted automatically
;;;  as part of an inference engine reset."
(defclass deffacts ()
  ((name :initarg :name
         :reader deffacts-name)
   (fact-list :initarg :fact-list
              :initform nil
              :reader deffacts-fact-list)))

(defmethod print-object ((self deffacts) strm)
  (print-unreadable-object (self strm :type t :identity t)
    (format strm "~S ; ~S" (deffacts-name self) (deffacts-fact-list self))))

(defun make-deffacts (name facts)
  (make-instance 'deffacts :name name :fact-list (copy-list facts)))


;;; File: fact.lisp

;;; "This class represents all facts in the knowledge base."
(defclass fact ()
  ((name :initarg :name
         :reader fact-name)
   (id :initform -1
       :accessor fact-id)
   (slot-table :reader fact-slot-table
               :initform (make-hash-table :test #'equal))
   (belief :initarg :belief
           :initform nil
           :accessor belief-factor)
   (clos-instance :reader fact-clos-instance)
   (shadows :initform nil
            :reader fact-shadowsp)
   (meta-data :reader fact-meta-data)))

;;; bug: EQUALP
(error "EQUALP!!!")
(defmethod equals ((fact-1 fact) (fact-2 fact))
  (and (eq (fact-name fact-1) (fact-name fact-2))
       (equalp (fact-slot-table fact-1) (fact-slot-table fact-2))))

(defmethod hash-key ((self fact))
  (let ((key (list)))
    (maphash #'(lambda (slot value)
                 ;;(declare (ignore slot))
                 (push value key))
             (fact-slot-table self))
    (push (fact-name self) key)
    key))

(defmethod slot-value-of-instance ((object t) slot-name)
  (slot-value object slot-name))

(defmethod (setf slot-value-of-instance) (new-value (object t) slot-name)
  (setf (slot-value object slot-name) new-value))

(defun fact-symbolic-id (fact)
  (format nil "F-~D" (fact-id fact)))

(defun set-slot-value (fact slot-name value)
  "Assigns a new value to a slot in a fact and its associated CLOS
  instance. SLOT-NAME is a symbol; VALUE is the new value for the
  slot."
  (with-auto-notify (object (find-instance-of-fact fact))
    (setf (slot-value-of-instance object slot-name) value)
    (initialize-slot-value fact slot-name value)))

(defun initialize-slot-value (fact slot-name value)
  "Sets the value of a slot in a fact's slot table. FACT is a FACT instance;
  SLOT-NAME is a symbol; VALUE is the slot's new value."
  (setf (gethash slot-name (fact-slot-table fact)) value)
  fact)

(defun set-slot-from-instance (fact instance slot-name)
  "Assigns to a slot the value from the corresponding slot in the fact's CLOS
  instance. FACT is a FACT instance; META-FACT is a META-FACT instance;
  INSTANCE is the fact's CLOS instance; SLOT-NAME is a symbol representing the
  affected slot."
  (initialize-slot-value
   fact slot-name
   (slot-value-of-instance instance slot-name)))

(defun get-slot-values (fact)
  "Returns a list of slot name / value pairs for every slot in a fact. FACT is
  a fact instance."
  (let ((slots (list)))
    (maphash #'(lambda (slot value)
                 (push (list slot value) slots))
             (fact-slot-table fact))
    slots))

;;;   "Returns the value associated with a slot name. FACT is a FACT instance;
;;;  SLOT-NAME is a SLOT-NAME instance."

;;;(defgeneric get-slot-value (self slot-name))

;;; todo: common defmethod with error

(defmethod get-slot-value ((self fact) (slot-name symbol))
  (cond ((keywordp slot-name)
         ;; (slot-name (eql :object))
         (fact-clos-instance self))
        (t (gethash slot-name (fact-slot-table self)))))

;;; bug: (eql)
#+nil
(defmethod get-slot-value ((self fact) (slot-name (eql :object)))
  (fact-clos-instance self))

(defun find-instance-of-fact (fact)
  "Retrieves the CLOS instance associated with a fact. FACT is a FACT
  instance."
  (fact-clos-instance fact))

;;; Corrected version courtesy of Aneil Mallavarapu...

(defun has-superclass (fact symbolic-name) ; fix converts symbolic-name to a class-object
  (find (find-class symbolic-name) (get-superclasses (fact-meta-data fact))))

(defun synchronize-with-instance (fact &optional (effective-slot nil))
  "Makes a fact's slot values and its CLOS instance's slot values match. If a
  slot identifier is provided then only that slot is synchronized. FACT
  is a FACT instance; EFFECTIVE-SLOT, if supplied, is a symbol representing
  the CLOS instance's slot."
  (let ((instance (find-instance-of-fact fact))
        (meta (fact-meta-data fact)))
    (flet ((synchronize-all-slots ()
             (mapc #'(lambda (slot-name)
                       (set-slot-from-instance fact instance slot-name))
                   (get-slot-list meta)))
           (synchronize-this-slot ()
             (set-slot-from-instance fact instance effective-slot)))
      (if (null effective-slot)
          (synchronize-all-slots)
        (synchronize-this-slot)))
    fact))

(defun reconstruct-fact (fact)
  `(,(fact-name fact) ,@(get-slot-values fact)))

(defmethod print-object ((self fact) strm)
  (print-unreadable-object (self strm :type nil :identity t)
    (format strm "~A ; id ~D" (fact-name self) (fact-id self))))

;;;  "Initializes a FACT instance. SLOTS is a list of slot name / value pairs,
;;;  where (FIRST SLOTS) is a symbol and (SECOND SLOT) is the slot's
;;;  value. INSTANCE is the CLOS instance to be associated with this FACT; if
;;;  INSTANCE is NIL then FACT is associated with a template and a suitable
;;;  instance must be created; otherwise FACT is bound to a user-defined class."

(defmethod initialize-instance :after ((self fact) &key (slots nil) (instance nil))
  (with-slots ((slot-table slot-table)
               (meta-data meta-data)) self
    (setf meta-data (find-meta-fact (fact-name self)))
    (mapc #'(lambda (slot-name)
              (setf (gethash slot-name slot-table) nil))
          (get-slot-list meta-data))
    (if (null instance)
        (initialize-fact-from-template self slots meta-data)
        (initialize-fact-from-instance self instance meta-data))
    self))

;;; bug:
(error "ASSERT!")

(defun initialize-fact-from-template (fact slots meta-data)
  "Initializes a template-bound FACT. An instance of the FACT's associated
  class is created and the slots of both are synchronized from the SLOTS
  list. FACT is a FACT instance; SLOTS is a list of symbol/value pairs."
  (let ((instance
         (make-instance (find-class (get-class-name meta-data) nil))))
    ;; bug:
    (cl:assert (not (null instance)) nil
      "No class was found corresponding to fact name ~S." (fact-name fact))
    (setf (slot-value fact 'clos-instance) instance)
    (mapc #'(lambda (slot-spec)
              (let ((slot-name (first slot-spec))
                    (slot-value (second slot-spec)))
                (set-slot-value fact slot-name slot-value)))
          slots)
    fact))

(defun initialize-fact-from-instance (fact instance meta-data)
  "Initializes a fact associated with a user-created CLOS instance. The fact's
  slot values are taken from the CLOS instance. FACT is a FACT instance;
  INSTANCE is the CLOS instance associated with this fact."
  (mapc #'(lambda (slot-name)
            (set-slot-from-instance fact instance slot-name))
        (get-slot-list meta-data))
  (setf (slot-value fact 'clos-instance) instance)
  (setf (slot-value fact 'shadows) t)
  fact)

(defun make-fact (name &rest slots)
  "The default constructor for class FACT. NAME is the symbolic fact name as
  used in rules; SLOTS is a list of symbol/value pairs."
  (make-instance 'fact :name name :slots slots))

(defun make-fact-from-instance (name clos-instance)
  "A constructor for class FACT that creates an instance bound to a
  user-defined CLOS instance. NAME is the symbolic fact name; CLOS-INSTANCE is
  a user-supplied CLOS object."
  (make-instance 'fact :name name :instance clos-instance))
  
(defun make-fact-from-template (fact)
  "Creates a FACT instance using another FACT instance as a
  template. Basically a clone operation useful for such things as asserting
  DEFFACTS."
  (apply #'make-fact
         (fact-name fact)
         (mapcar #'(lambda (slot-name)
                     (list slot-name (get-slot-value fact slot-name)))
                 (get-slot-list (fact-meta-data fact)))))

;;; File: watches.lisp

(defvar *assert-fact* nil)
(defvar *retract-fact* nil)
(defvar *enable-activation* nil)
(defvar *disable-activation* nil)
(defvar *fire-rule* nil)
(defvar *watches* nil)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *trace-output* *standard-output*) )

(defun watch-activation-detail (activation direction)
  (format *trace-output* "~A Activation: ~A : ~A~%"
          direction
          (rule-default-name (activation-rule activation))
          (activation-fact-list activation))
  (values))

(defun watch-enable-activation (activation)
  (watch-activation-detail activation "==>"))

(defun watch-disable-activation (activation)
  (watch-activation-detail activation "<=="))

(defun watch-rule-firing (activation)
  (let ((rule (activation-rule activation)))
    (format *trace-output* "FIRE ~D: ~A ~A~%"
            (rete-firing-count (rule-engine rule))
            (rule-default-name rule)
            (activation-fact-list activation))
    (values)))

(defun watch-fact-detail (fact direction)
  (format *trace-output* "~A ~A ~S~%"
          direction (fact-symbolic-id fact)
          (reconstruct-fact fact))
  (values))

(defun watch-assert (fact)
  (watch-fact-detail fact "==>"))

(defun watch-retract (fact)
  (watch-fact-detail fact "<=="))

(defun watch-event (event)
  (ecase event
    (:facts (setf *assert-fact* #'watch-assert)
            (setf *retract-fact* #'watch-retract))
    (:activations (setf *enable-activation* #'watch-enable-activation)
                  (setf *disable-activation* #'watch-disable-activation))
    (:rules (setf *fire-rule* #'watch-rule-firing))
    (:all (watch-event :facts)
          (watch-event :activations)
          (watch-event :rules)))
  (unless (eq event :all)
    (pushnew event *watches*))
  event)

(defun unwatch-event (event)
  (ecase event
    (:facts
     (setf *assert-fact* nil)
     (setf *retract-fact* nil))
    (:activations
     (setf *enable-activation* nil)
     (setf *disable-activation* nil))
    (:rules (setf *fire-rule* nil))
    (:all
     (unwatch-event :facts)
     (unwatch-event :activations)
     (unwatch-event :rules)))
  (unless (eq event :all)
    (setf *watches*
          ;; bug: ??
          (delete event *watches*)))
  event)

;;; note: ???
(defun watches ()
  *watches*)

(defmacro trace-assert (fact)
  `(unless (null *assert-fact*)
     (funcall *assert-fact* ,fact)))

(defmacro trace-retract (fact)
  `(unless (null *retract-fact*)
     (funcall *retract-fact* ,fact)))

(defmacro trace-enable-activation (activation)
  `(unless (null *enable-activation*)
     (funcall *enable-activation* ,activation)))

(defmacro trace-disable-activation (activation)
  `(unless (null *disable-activation*)
     (funcall *disable-activation* ,activation)))

(defmacro trace-firing (activation)
  `(unless (null *fire-rule*)
     (funcall *fire-rule* ,activation)))

;;; File: activation.lisp

(defvar *activation-timestamp* 0)

;;; "Represents a rule activation."
(defclass activation ()
  ((rule :initarg :rule
         :initform nil
         :reader activation-rule)
   (tokens :initarg :tokens
           :initform nil
           :reader activation-tokens)
   (timestamp :initform (incf *activation-timestamp*)
              :reader activation-timestamp)
   (eligible :initform t
             :accessor activation-eligible)))

(defmethod activation-priority ((self activation))
  (rule-salience (activation-rule self)))

(defmethod fire-activation ((self activation))
  (trace-firing self)
  (fire-rule (activation-rule self) (activation-tokens self)))

(defun eligible-p (activation)
  (activation-eligible activation))

(defun inactive-p (activation)
  (not (eligible-p activation)))

(defun activation-fact-list (activation &key (detailp nil))
  (token-make-fact-list (activation-tokens activation) :detailp detailp))

(defmethod print-object ((self activation) strm)
  (let ((tokens (activation-tokens self))
        (rule (activation-rule self)))
    (print-unreadable-object (self strm :identity t :type t)
      (format strm "(~A ~A ; salience = ~D)"
              (rule-name rule)
              (mapcar #'fact-symbolic-id 
                      (token-make-fact-list tokens))
              (rule-salience rule)))))

(defmethod hash-key ((self activation))
  (hash-key (activation-tokens self)))

(defun make-activation (rule tokens)
  (make-instance 'activation :rule rule :tokens tokens))

;;; $Header: /cvsroot/lisa/lisa/src/core/heap.lisp,v 1.4 2007/09/17 22:42:39 youngde Exp $
;;; Copyright (c) 2002, 2003 Gene Michael Stover.
;;; Adapted for Lisa: 4/3/2006.
;;; Adapted for JSCL 2021 @vlad-km

#+nil
(defpackage "HEAP"
  (:use :cl :cl-user)
  (:export  create-heap heap-clear heap-collect heap-count heap-empty-p
            heap-find heap-insert heap-peek heap-remove))

(in-package :heap)

;;; todo: as a defclass heap
;;; todo: OR DEFSTRUCT type list ?
#+nil
(defclass  heap ()
  ((less-fn :initform nil :accessor heap-less-fn)
  (order :initform 0 :accessor heap-order)
  (a :initform nil :accessor heap-a)
  (max-count :initform 0 :accessor heap-max-count)))

(defstruct (heap :named (:type list))
  less-fn
  order
  a
  max-count)


(defun default-search-predicate (heap obj)
  (declare (ignore heap) (ignore obj))
  t)

(defun percolate-down (heap hole x)
  "Private. Move the HOLE down until it's in a location suitable for X.
Return the new index of the hole."
  (do ((a (heap-a heap))
       (less (heap-less-fn heap))
       (child (lesser-child heap hole) (lesser-child heap hole)))
      ((or (>= child (fill-pointer a)) (funcall less x (aref a child)))
       hole)
    (setf (aref a hole) (aref a child)
      hole child)))

(defun percolate-up (heap hole x)
  "Private.  Moves the HOLE until it's in a location suitable for holding
X.  Does not actually bind X to the HOLE.  Returns the new
index of the HOLE.  The hole itself percolates down; it's the X
that percolates up."
  (let ((d (heap-order heap))
	      (a (heap-a heap))
	      (less (heap-less-fn heap)))
    ;;(print (list d a hole))
    (setf (aref a 0) x)
    (do ((i hole parent)
	       (parent (floor (/ hole d)) (floor (/ parent d))))
        ((not (funcall less x (aref a parent))) i)
      ;;(print (list parent hole d))
      (setf (aref a i) (aref a parent)))))

(defvar *heap* nil)

(defun heap-init (heap less-fn &key (order 2) (initial-contents nil))
  "Initialize the indicated heap.  If INITIAL-CONTENTS is a non-empty
list, the heap's contents are intiailized to the values in that
list; they are ordered according to LESS-FN.  INITIAL-CONTENTS must
be a list or NIL."
  (setf *heap* heap)
  (setf (heap-less-fn heap) less-fn
        (heap-order heap)   order
        (heap-a heap)       (make-array 2 :initial-element nil
                                          :adjustable t :fill-pointer 1)
        (heap-max-count heap)  0)
  (when initial-contents
    (dolist (i initial-contents) (vector-push-extend i (heap-a heap)))
    (loop for i from (floor (/ (length (heap-a heap)) order)) downto 1
	        do (let* ((tmp (aref (heap-a heap) i))
		                (hole (percolate-down heap i tmp)))
	             (setf (aref (heap-a heap) hole) tmp)))
    (setf (heap-max-count heap) (length (heap-a heap))))
  heap)

#+nil
(defun create-heap (less-fn &key (order 2) (initial-contents nil))
  (heap-init (make-instance 'heap)
             less-fn
             :order order
	           :initial-contents initial-contents))

;;; note: Hmm todo:
(defun create-heap (less-fn &key (order 2) (initial-contents nil))
  (heap-init (make-heap)
             less-fn
             :order order
	           :initial-contents initial-contents))

(defun heap-clear (heap)
  "Remove all elements from the heap, leaving it empty.  Faster
(& more convenient) than calling HEAP-REMOVE until the heap is
empty."
  (setf (fill-pointer (heap-a heap)) 1)
  nil)

(defun heap-count (heap)
  (1- (fill-pointer (heap-a heap))))

(defun heap-empty-p (heap)
  "Returns non-NIL if & only if the heap contains no items."
  (= (fill-pointer (heap-a heap)) 1))

(defun heap-insert (heap x)
  "Insert a new element into the heap.  Return the element (which probably
                                                                  isn't very useful)."
  (let ((a (heap-a heap)))
    ;; Append a hole for the new element.
    (vector-push-extend nil a)

    ;; Move the hole from the end towards the front of the
    ;; queue until it is in the right position for the new
    ;; element.
    (setf (aref a (percolate-up heap (1- (fill-pointer a)) x)) x)))

(defun heap-find-idx (heap fnp)
  "Return the index of the element which satisfies the predicate FNP.
If there is no such element, return the fill pointer of HEAP's array A."
  (do* ((a (heap-a heap))
	      (fp (fill-pointer a))
	      (i  1  (1+ i)))
       ((or (>= i fp) (funcall fnp heap (aref a i)))
	      i)))

(defun heap-remove (heap &optional (fn #'default-search-predicate))
  "Remove the minimum (first) element in the heap & return it.  It's
an error if the heap is already empty.  (Should that be an error?)"
  (let ((a (heap-a heap))
	      (i (heap-find-idx heap fn)))
    (cond ((< i (fill-pointer a)) ;; We found an element to remove.
           (let ((x (aref a i))
                 (last-object (vector-pop a)))
             (setf (aref a (percolate-down heap i last-object)) last-object)
             x))
          (t nil)))) ;; Nothing to remove

(defun heap-find (heap &optional (fn #'default-search-predicate))
  (let ((a (heap-a heap))
	      (i (heap-find-idx heap fn)))
    (cond ((< i (fill-pointer a))       ; We found an element to remove.
           (aref a i))
          (t nil))))

#+nil
(defun heap-collect (heap &optional (fn #'default-search-predicate))
  (if (heap-empty-p heap)
      nil
    (loop for obj across (heap-a heap)
          when (funcall fn heap obj)
            collect obj)))

(defun heap-collect (heap &optional (fn #'default-search-predicate))
  (let ((vec (heap-a heap)))
    (if (heap-empty-p heap)
        nil
      (loop for i from 1 below (fill-pointer vec)
            with obj = (aref vec i)
            when (funcall fn heap obj)
              collect obj))))

(defun heap-peek (heap)
  "Return the first element in the heap, but don't remove it.  It'll
be an error if the heap is empty.  (Should that be an error?)"
  (aref (heap-a heap) 1))

(defun lesser-child (heap parent)
  "Return the index of the lesser child.  If there's one child,
return its index.  If there are no children, return 
(FILL-POINTER (HEAP-A HEAP))."
  (let* ((a (heap-a heap))
         (left (* parent (heap-order heap)))
         (right (1+ left))
         (fp (fill-pointer a)))
    (cond ((>= left fp) fp)
          ((= right fp) left)
          ((funcall (heap-less-fn heap) (aref a left) (aref a right)) left)
          (t right))))

(export  '(heap::create-heap heap::heap-clear heap::heap-collect heap::heap-count heap::heap-empty-p
            heap::heap-find heap::heap-insert heap::heap-peek heap::heap-remove))

(in-package :cl-user)

;;; File: strategies.lisp
;;; Description: Classes that implement the various default conflict
;;; resolution strategies for Lisa's RETE implementation.

;;;    "Serves as the base class for all classes implementing conflict
;;;   resolution strategies."

(defclass strategy ()
  ())

(defgeneric add-activation (strategy activation))
(defgeneric find-activation (strategy rule token))
(defgeneric find-all-activations (strategy rule))
(defgeneric next-activation (strategy))
(defgeneric remove-activations (strategy))
(defgeneric list-activations (strategy))

(defclass priority-queue-mixin ()
  ((heap :initarg :heap
         :reader heap)))

;;; bug:
(defmethod reset-activations ((self priority-queue-mixin))
  (heap:heap-clear (heap self)))

(defmethod insert-activation ((self priority-queue-mixin) activation)
  (heap:heap-insert (heap self) activation))

(defmethod lookup-activation ((self priority-queue-mixin) rule tokens)
  (heap:heap-find (heap self) #'(lambda (heap activation)
                                  (declare (ignore heap))
                                  (and (equal (hash-key activation) (hash-key tokens))
                                       (eq (activation-rule activation) rule)))))

(defmethod lookup-activations ((self priority-queue-mixin) rule)
  (heap:heap-collect (heap self) #'(lambda (heap activation)
                                     (declare (ignore heap))
                                     (and activation
                                          (eq rule (activation-rule activation))))))

(defmethod get-next-activation ((self priority-queue-mixin))
  (heap:heap-remove (heap self)))

(defmethod get-all-activations ((self priority-queue-mixin))
  (heap:heap-collect (heap self) (lambda (heap activation)
                                   (declare (ignore heap))
                                   activation)))

;;; "A base class for all LISA builtin conflict resolution strategies."
(defclass builtin-strategy (strategy priority-queue-mixin)
  ())
  
(defmethod add-activation ((self builtin-strategy) activation)
  (insert-activation self activation))

;;; bug:
(defmethod find-activation ((self builtin-strategy) rule token)
  (declare (ignore rule token))
  (cl:assert nil nil "Why are we calling FIND-ACTIVATION?"))

(defmethod find-all-activations ((self builtin-strategy) rule)
  (lookup-activations self rule))

(defmethod next-activation ((self builtin-strategy))
  (get-next-activation self))

(defmethod remove-activations ((self builtin-strategy))
  (reset-activations self))

(defmethod list-activations ((self builtin-strategy))
  (get-all-activations self))

;;; "A depth-first conflict resolution strategy."
(defclass depth-first-strategy (builtin-strategy)
  ())

(defun make-depth-first-strategy ()
  (make-instance 'depth-first-strategy
                 :heap (heap:create-heap #'(lambda (a b)
                                             (cond ((> (activation-priority a)
                                                       (activation-priority b))
                                                    a)
                                                   ((and (= (activation-priority a)
                                                            (activation-priority b))
                                                         (> (activation-timestamp a)
                                                            (activation-timestamp b)))
                                                    a)
                                                   (t nil))))))

;;; "A breadth-first conflict resolution strategy."
(defclass breadth-first-strategy (builtin-strategy)
  ())

(defun make-breadth-first-strategy ()
  (make-instance 'breadth-first-strategy
                 :heap (heap:create-heap #'(lambda (a b)
                                             (cond ((> (activation-priority a)
                                                       (activation-priority b))
                                                    a)
                                                   ((and (= (activation-priority a)
                                                            (activation-priority b))
                                                         (< (activation-timestamp a)
                                                            (activation-timestamp b)))
                                                    a)
                                                   (t nil))))))

;;; File: context.lisp

(defclass context ()
  ((name :initarg :name
         :reader context-name)
   (rules :initform (make-hash-table :test #'equal)
          :reader context-rules)
   (strategy :initarg :strategy
             :reader context-strategy)))

(defmethod print-object ((self context) strm)
  (print-unreadable-object (self strm :type t)
    (if (initial-context-p self)
        (format strm "~S" "The Initial Context")
      (format strm "~A" (context-name self)))))

(defmethod find-rule-in-context ((self context) (rule-name string))
  (values (gethash rule-name (context-rules self))))

(defmethod find-rule-in-context ((self context) (rule-name symbol))
  (values (gethash (symbol-name rule-name) (context-rules self))))

(defun add-rule-to-context (context rule)
  (setf (gethash (symbol-name (rule-name rule)) (context-rules context))
    rule))

(defmethod conflict-set ((self context))
  (context-strategy self))

(defmethod remove-rule-from-context ((self context) (rule-name symbol))
  (remhash (symbol-name rule-name) (context-rules self)))

(defmethod remove-rule-from-context ((self context) (rule t))
  (remove-rule-from-context self (rule-name rule)))

(defun clear-activations (context)
  (remove-activations (context-strategy context)))

(defun context-activation-list (context)
  (list-activations (context-strategy context)))

(defun context-rule-list (context)
  (loop for rule being the hash-values of (context-rules context)
      collect rule))

(defun clear-context (context)
  (clear-activations context)
  (clrhash (context-rules context)))

(defun initial-context-p (context)
  (string= (context-name context) "INITIAL-CONTEXT"))

(defun make-context-name (defined-name)
  (typecase defined-name
    (symbol (symbol-name defined-name))
    (string defined-name)
    (otherwise
     (error "The context name must be a string designator."))))

(defmacro with-context (context &body body)
  `(let ((*active-context* ,context))
     ,@body))

(defmacro with-rule-name-parts ((context short-name long-name) 
                                symbolic-name &body body)
  (let ((qualifier (gensym))
        (rule-name (gensym)))
    `(let* ((,rule-name (symbol-name ,symbolic-name))
            (,qualifier (position #\. ,rule-name))
            (,context (if ,qualifier
                          (subseq ,rule-name 0 ,qualifier)
                        (symbol-name :initial-context)))
            (,short-name (if ,qualifier
                             (subseq ,rule-name (1+ ,qualifier))
                           ,rule-name))
            (,long-name (if ,qualifier
                            ,rule-name
                          (concatenate 'string ,context "." ,short-name))))
       ,@body)))

(defun make-context (name &key (strategy nil))
  (make-instance 'context
    :name (make-context-name name)
    :strategy (if (null strategy)
                  (make-breadth-first-strategy)
                strategy)))

;;; File: rule.lisp

;;;  "Represents production rules after they've been analysed by the language
;;;  parser."

(defclass rule ()
  ((short-name :initarg :short-name
               :initform nil
               :reader rule-short-name)
   (qualified-name :reader rule-name)
   (comment :initform nil
            :initarg :comment
            :reader rule-comment)
   (salience :initform 0
             :initarg :salience
             :reader rule-salience)
   (context :initarg :context
            :reader rule-context)
   (auto-focus :initform nil
               :initarg :auto-focus
               :reader rule-auto-focus)
   (behavior :initform nil
             :initarg :behavior
             :accessor rule-behavior)
   (binding-set :initarg :binding-set
                :initform nil
                :reader rule-binding-set)
   (node-list :initform nil
              :reader rule-node-list)
   (activations :initform (make-hash-table :test #'equal)
                :accessor rule-activations)
   (patterns :initform (list)
             :initarg :patterns
             :reader rule-patterns)
   (actions :initform nil
            :initarg :actions
            :reader rule-actions)
   (logical-marker :initform nil
                   :initarg :logical-marker
                   :reader rule-logical-marker)
   (belief-factor :initarg :belief
                  :initform nil
                  :reader belief-factor)
   (active-dependencies :initform (make-hash-table :test #'equal)
                        :reader rule-active-dependencies)
   (engine :initarg :engine
           :initform nil
           :reader rule-engine)))

;;; todo:
(defmethod fire-rule ((self rule) tokens)
  (let ((*active-rule* self)
        (*active-engine* (rule-engine self))
        (*active-tokens* tokens))
    (unbind-rule-activation self tokens)
    (funcall (rule-behavior self) tokens)))

(defun rule-default-name (rule)
  (if (initial-context-p (rule-context rule))
      (rule-short-name rule)
    (rule-name rule)))

(defun bind-rule-activation (rule activation tokens)
  (setf (gethash (hash-key tokens) (rule-activations rule))
    activation))

(defun unbind-rule-activation (rule tokens)
  (remhash (hash-key tokens) (rule-activations rule)))

(defun clear-activation-bindings (rule)
  (clrhash (rule-activations rule)))

(defun find-activation-binding (rule tokens)
  (gethash (hash-key tokens) (rule-activations rule)))

(defun attach-rule-nodes (rule nodes)
  (setf (slot-value rule 'node-list) nodes))

(defun compile-rule-behavior (rule actions)
  (with-accessors ((behavior rule-behavior)) rule
    (unless behavior
      (setf (rule-behavior rule)
        (make-behavior (rule-actions-actions actions)
                       (rule-actions-bindings actions))))))

;;; todo:
(defmethod conflict-set ((self rule))
  (conflict-set (rule-context self)))

(defmethod print-object ((self rule) strm)
  (print-unreadable-object (self strm :type t)
    (format strm "~A"
            (if (initial-context-p (rule-context self))
                (rule-short-name self)
              (rule-name self)))))

(defun compile-rule (rule patterns actions)
  (compile-rule-behavior rule actions)
  (add-rule-to-network (rule-engine rule) rule patterns)
  rule)

(defun logical-rule-p (rule)
  (numberp (rule-logical-marker rule)))

(defun auto-focus-p (rule)
  (rule-auto-focus rule))

(error "ASSERT")
(defun find-any-logical-boundaries (patterns)
  (flet ((ensure-logical-blocks-are-valid (addresses)
           (cl:assert (and (= (first (last addresses)) 1)
                           (eq (parsed-pattern-class (first patterns))
                               'initial-fact)) nil
             "Logical patterns must appear first within a rule.")
           ;; BUG FIX - FEB 17, 2004 - Aneil Mallavarapu
           ;;         - replaced: 
           ;; (reduce #'(lambda (first second) 
           ;; arguments need to be inverted because address values are PUSHed
           ;; onto the list ADDRESSES, and therefore are in reverse order
           (reduce #'(lambda (second first)
                       ;; bug: ASSERT
                       (cl:assert (= second (1+ first)) nil
                         "All logical patterns within a rule must be contiguous.")
                       second)
                   addresses :from-end t)))
    (let ((addresses (list)))
      (dolist (pattern patterns)
        (when (logical-pattern-p pattern)
          (push (parsed-pattern-address pattern) addresses)))
      (unless (null addresses)
        (ensure-logical-blocks-are-valid addresses))
      (first addresses))))

(defmethod initialize-instance :after ((self rule) &rest initargs)
  (declare (ignore initargs))
  (with-slots ((qual-name qualified-name)) self
    (setf qual-name
      (intern (format nil "~A.~A" 
                      (context-name (rule-context self))
                      (rule-short-name self))))))
                    
(defun make-rule (name engine patterns actions 
                  &key (doc-string nil) 
                       (salience 0) 
                       (context (active-context))
                       (auto-focus nil)
                       (belief nil)
                       (compiled-behavior nil))
  (flet ((make-rule-binding-set ()
           (delete-duplicates
            (loop for pattern in patterns
                append (parsed-pattern-binding-set pattern)))))
    (compile-rule
     (make-instance 'rule 
       :short-name name 
       :engine engine
       :patterns patterns
       :actions actions
       :behavior compiled-behavior
       :comment doc-string
       :belief belief
       :salience salience
       :context (if (null context)
                    (find-context (inference-engine) :initial-context)
                  (find-context (inference-engine) context))
       :auto-focus auto-focus
       :logical-marker (find-any-logical-boundaries patterns)
       :binding-set (make-rule-binding-set))
     patterns actions)))

(defun copy-rule (rule engine)
  (let ((initargs `(:doc-string ,(rule-comment rule)
                    :salience ,(rule-salience rule)
                    :context ,(if (initial-context-p (rule-context rule))
                                  nil
                                (context-name (rule-context rule)))
                    :compiled-behavior ,(rule-behavior rule)
                    :auto-focus ,(rule-auto-focus rule))))
    (with-inference-engine (engine)
      (apply #'make-rule
             (rule-short-name rule)
             engine
             (rule-patterns rule)
             (rule-actions rule)
             initargs))))

;;; File: pattern.lisp
;;; Description: Structures here collectively represent patterns after they've
;;; been analysed by the language parser. This is the canonical representation
;;; of parsed patterns that Rete compilers are intended to see.

;;; Represents the canonical form of a slot within a pattern analysed by the
;;; DEFRULE parser. NAME is the slot identifier; VALUE is the slot's value,
;;; and its type can be one of (symbol number string list) or a LISA variable;
;;; SLOT-BINDING is the binding object, present if VALUE is a LISA variable;
;;; NEGATED is non-NIL if the slot occurs within a NOT form;
;;; INTRA-PATTERN-BINDINGS is a list of binding objects, present if all of the
;;; variables used by the slot reference bindings within the slot's pattern;
;;; CONSTRAINT, if not NIL, represents a constraint placed on the slot's
;;; value. CONSTRAINT should only be non-NIL if VALUE is a variable, and can
;;; be one of the types listed for VALUE or a CONS representing arbitrary
;;; Lisp code; CONSTRAINT-BINDINGS is a list of binding objects that are
;;; present if the slot has a constraint.

;;;  "Represents the canonical form of a slot within a pattern analysed by the
;;;  DEFRULE parser."

;;; todo: as defclass
(defstruct pattern-slot
  (name nil :type symbol)
  (value nil)
  (slot-binding nil :type list)
  (negated nil :type symbol)
  (intra-pattern-bindings nil :type symbol)
  (constraint nil)
  (constraint-bindings nil :type list))

;;; PARSED-PATTERN represents the canonical form of a pattern analysed by the
;;; language parser. CLASS is the name, or head, of the pattern, as a symbol;
;;; SLOTS is a list of PATTERN-SLOT objects representing the analysed slots of
;;; the pattern; ADDRESS is a small integer representing the pattern's
;;; position within the rule form, starting at 0; PATTERN-BINDING, if not NIL,
;;; is the variable to which a fact matching the pattern will be bound during
;;; the match process; TEST-BINDINGS is a list of BINDING objects present if
;;; the pattern is a TEST CE; BINDING-SET is the set of variable bindings used
;;; by the pattern; TYPE is one of (:GENERIC :NEGATED :TEST :OR) and indicates
;;; the kind of pattern represented; SUB-PATTERNS, if non-NIL, is set for an
;;; OR CE and is a list of PARSED-PATTERN objects that represent the branches
;;; within the OR; LOGICAL, if non-NIL, indicates this pattern participates in
;;; truth maintenance.

;;;   "Represents the canonical form of a pattern analysed by the DEFRULE parser."

;;; todo: as defclass
(defstruct parsed-pattern
  (class nil :type symbol)
  (slots nil)
  (address 0 :type integer)
  (pattern-binding nil)
  (test-bindings nil :type list)
  (binding-set nil :type list)
  (logical nil :type symbol)
  (sub-patterns nil :type list)
  (type :generic :type symbol))

;;; todo: as defclass
(defstruct rule-actions
  (bindings nil :type list)
  (actions nil :type list))

(defun generic-pattern-p (pattern)
  (eq (parsed-pattern-type pattern) :generic))

(defun existential-pattern-p (pattern)
  (eq (parsed-pattern-type pattern) :existential))

(defun test-pattern-p (pattern)
  (eq (parsed-pattern-type pattern) :test))

(defun test-pattern-predicate (pattern)
  (parsed-pattern-slots pattern))

(defun negated-pattern-p (pattern)
  (eq (parsed-pattern-type pattern) :negated))

(error "ASSERT")
;;; bug:
(defun parsed-pattern-test-forms (pattern)
  (cl:assert (test-pattern-p pattern) nil
    "This pattern is not a test pattern: ~S" pattern)
  (parsed-pattern-slots pattern))

(defun simple-slot-p (pattern-slot)
  (not (variablep (pattern-slot-value pattern-slot))))

(defun intra-pattern-slot-p (pattern-slot)
  (or (simple-slot-p pattern-slot)
      (pattern-slot-intra-pattern-bindings pattern-slot)))

(defun constrained-slot-p (pattern-slot)
  (not (null (pattern-slot-constraint pattern-slot))))

(defun simple-bound-slot-p (pattern-slot)
  (and (variablep (pattern-slot-value pattern-slot))
       (not (constrained-slot-p pattern-slot))))

(defun negated-slot-p (pattern-slot)
  (pattern-slot-negated pattern-slot))

(defun bound-pattern-p (parsed-pattern)
  (not (null (parsed-pattern-pattern-binding parsed-pattern))))

(defun compound-pattern-p (parsed-pattern)
  (not (null (parsed-pattern-sub-patterns parsed-pattern))))

(defun logical-pattern-p (parsed-pattern)
  (parsed-pattern-logical parsed-pattern))

;;; File: rule-parser.lisp
;;; Description: The Lisa rule parser, completely rewritten for release 3.0.

(defconstant *rule-separator* '=>)

(defvar *binding-table*)
(defvar *current-defrule*)
(defvar *current-defrule-pattern-location*)
(defvar *in-logical-pattern-p* nil)
(defvar *special-initial-elements* '(not exists logical))

(defvar *conditional-elements-table*
  '((exists . parse-exists-pattern)
    (not . parse-not-pattern)
    (test . parse-test-pattern)))

(defun extract-rule-headers (body)
  (if (stringp (first body))
      (values (first body) (rest body))
    (values nil body)))

(defun fixup-runtime-bindings (patterns)
  "Supports the parsing of embedded DEFRULE forms."
  (labels ((fixup-bindings (part result)
             (let* ((token (first part))
                    (new-token token))
               (cond ((null part)
                      (return-from fixup-bindings (nreverse result)))
                     ((and (variablep token)
                           (boundp token))
                      (setf new-token (symbol-value token)))
                     ((consp token)
                      (setf new-token (fixup-bindings token nil))))
               (fixup-bindings (rest part) (push new-token result)))))
    (fixup-bindings patterns nil)))

(defun preprocess-left-side (lhs)
  (when (or (null lhs)
            (find (caar lhs) *special-initial-elements*))
    (push (list 'initial-fact) lhs))
  (if (active-rule)
      (fixup-runtime-bindings lhs)
    lhs))

(defun find-conditional-element-parser (symbol)
  (let ((parser (assoc symbol *conditional-elements-table*)))
    (if parser
        (cdr parser)
      'parse-generic-pattern)))

(defun logical-element-p (pattern)
  (eq (first pattern) 'logical))

(defmacro with-slot-components ((slot-name slot-value constraint) form &body body)
  `(progn
     (unless (consp ,form)
       (error 'slot-parsing-error :slot-name ',slot-name :location *current-defrule-pattern-location*))
     (let ((,slot-name (first ,form))
           (,slot-value (second ,form))
           (,constraint (third ,form)))
       ,@body)))

(defun make-binding-set ()
  (loop for binding being the hash-values of *binding-table*
      collect binding))

(defun find-or-set-slot-binding (var slot-name location)
  "Given a variable, either retrieve the binding object for it or create a new one."
  (multiple-value-bind (binding existsp)
      (gethash var *binding-table*)
    (unless existsp
      (setf binding
        (setf (gethash var *binding-table*)
          (make-binding var location slot-name))))
    (values binding existsp)))

;;; bug:
(defun find-slot-binding (var &key (errorp t))
  "Given a variable, retrieve the binding object for it."
  (let ((binding (gethash var *binding-table*)))
    (when errorp
      (cl:assert binding nil "Missing slot binding for variable ~A" var))
    binding))

;;; bug:
(defun set-pattern-binding (var location)
  (cl:assert (not (gethash var *binding-table*)) nil "This is a duplicate pattern binding: ~A" var)
  (setf (gethash var *binding-table*)
    (make-binding var location :pattern)))

(defun collect-bindings (forms &key (errorp t))
  (let ((bindings (list)))
    (dolist (obj (lilu:flatten forms))
      (when (variablep obj)
        (let ((binding (find-slot-binding obj :errorp errorp)))
          (unless (null binding)
            (push binding bindings)))))
    (nreverse bindings)))

(defmacro with-rule-components (((doc-string lhs rhs) rule-form) &body body)
  (let ((remains (gensym)))
    `(let ((*binding-table* (make-hash-table)))
       (multiple-value-bind (,doc-string ,remains)
           (extract-rule-headers ,rule-form)
         (multiple-value-bind (,lhs ,rhs)
             (parse-rule-body ,remains)
           ,@body)))))

(defun collect-constraint-bindings (constraint)
  (let ((bindings (list)))
    (dolist (obj (lilu:flatten constraint))
      (when (variablep obj)
        (pushnew (find-slot-binding obj) bindings :key #'first)))
    bindings))

;;; the parsing code itself...

(defun parse-one-slot-constraint (var constraint-form)
  "Parses a single slot constraint, eg. (slot-name ?var 1) or (slot-name ?var (equal ?var 1))"
  (let ((head (first constraint-form))
        (args (second constraint-form)))
    (cond ((eq head 'not)
           (values `(equal ,var ,@(if (symbolp args) `(',args) args))
                   `(,(find-slot-binding var)) t))
          (t
           (values constraint-form (collect-constraint-bindings constraint-form) nil)))))

(defun slot-value-is-variable-p (value)
  "Is the slot value a Lisa variable?"
  (variable-p value))

(defun slot-value-is-atom-p (value)
  "Is the slot value a simple constraint?"
  (and (atom value)
       (not (slot-value-is-variable-p value))))

(defun slot-value-is-negated-atom-p (value)
  "Is the slot value a simple negated constraint?"
  (and (consp value)
       (eq (first value) 'not)
       (slot-value-is-atom-p (second value))))

(defun slot-value-is-negated-variable-p (value)
  (and (consp value)
       (eq (first value) 'not)
       (variable-p (second value))))

(defun intra-pattern-bindings-p (bindings location)
  "Is every variable in a pattern 'local'; i.e. does not reference a binding in a previous pattern?"
  (every #'(lambda (b)
             (= location (binding-address b)))
         bindings))

(defun parse-one-slot (form location)
  "Parses a single raw pattern slot"
  (with-slot-components (slot-name slot-value constraint) form
    (cond ((slot-value-is-atom-p slot-value)
           ;; eg. (slot-name "frodo")
           (make-pattern-slot :name slot-name :value slot-value))
          ((slot-value-is-negated-variable-p slot-value)
           ;; eg. (slot-name (not ?value))
           (let ((binding (find-or-set-slot-binding (second slot-value) slot-name location)))
             (make-pattern-slot :name slot-name
                                :value (second slot-value)
                                :negated t
                                :slot-binding binding)))
          ((slot-value-is-negated-atom-p slot-value)
           ;; eg. (slot-name (not "frodo"))
           (make-pattern-slot :name slot-name :value (second slot-value) :negated t))
          ((and (slot-value-is-variable-p slot-value)
                (not constraint))
           ;; eg. (slot-name ?value)
           (let ((binding (find-or-set-slot-binding slot-value slot-name location)))
             (make-pattern-slot :name slot-name :value slot-value :slot-binding binding
                                :intra-pattern-bindings (intra-pattern-bindings-p (list binding) location))))
          ((and (slot-value-is-variable-p slot-value)
                constraint)
           ;; eg. (slot-name ?value (equal ?value "frodo"))
           (let ((binding (find-or-set-slot-binding slot-value slot-name location)))
             (multiple-value-bind (constraint-form constraint-bindings negatedp)
                 (parse-one-slot-constraint slot-value constraint)
               (make-pattern-slot :name slot-name :value slot-value :slot-binding binding
                                  :negated negatedp
                                  :constraint constraint-form
                                  :constraint-bindings constraint-bindings
                                  :intra-pattern-bindings
                                  (intra-pattern-bindings-p (list* binding constraint-bindings) location)))))
          (t (error 'rule-parsing-error
                    :rule-name *current-defrule*
                    :location *current-defrule-pattern-location*
                    :text "malformed slot")))))

(defun parse-rule-body (body)
  (let ((location 0)
        (patterns (list)))
    (labels ((parse-lhs (pattern-list)
               (let ((pattern (first pattern-list))
                     (*current-defrule-pattern-location* location))
                 (unless (listp pattern)
                   (error 'rule-parsing-error
                          :text "pattern is not a list"
                          :rule-name *current-defrule*
                          :location *current-defrule-pattern-location*))
                 (cond ((null pattern-list)
                        ;; note: Hmmm
                        (unless *in-logical-pattern-p* (nreverse patterns)))
                       ;; logical CEs are "special"; they don't have their own parser.
                       ((logical-element-p pattern)
                        (let ((*in-logical-pattern-p* t))
                          (parse-lhs (rest pattern))))
                       (t
                        (push (funcall (find-conditional-element-parser (first pattern)) pattern
                                       (1- (incf location)))
                              patterns)
                        (parse-lhs (rest pattern-list))))))
             (parse-rhs (actions)
               (make-rule-actions
                :bindings (collect-bindings actions :errorp nil)
                :actions actions)))
      (multiple-value-bind (lhs remains)
          (lilu:find-before *rule-separator* body :test #'eq)
        (unless remains
          (error 'rule-parsing-error :text "missing rule separator"))
        (values (parse-lhs (preprocess-left-side lhs))
                (parse-rhs (lilu:find-after *rule-separator* remains :test #'eq)))))))

;;; The conditional element parsers...

(defun parse-generic-pattern (pattern location &optional pattern-binding)
  (let ((head (first pattern)))
    (unless (symbolp head)
      (error 'rule-parsing-error
             :rule-name *current-defrule*
             :location *current-defrule-pattern-location*
             :text "the head of a pattern must be a symbol"))
    (cond ((variable-p head)
           (set-pattern-binding head location)
           (parse-generic-pattern (second pattern) location head))
          (t
           (let ((slots
                  (loop for slot-decl in (rest pattern) collect
                        (parse-one-slot slot-decl location))))
             (make-parsed-pattern :type :generic
                                  :pattern-binding pattern-binding
                                  :slots slots
                                  :binding-set (make-binding-set)
                                  :logical *in-logical-pattern-p*
                                  :address location
                                  :class head))))))

(defun parse-test-pattern (pattern location)
  (flet ((extract-test-pattern ()
           (let ((form (rest pattern)))
             (unless (and (listp form)
                          (= (length form) 1))
               (error 'rule-parsing-error
                      :rule-name *current-defrule*
                      :location *current-defrule-pattern-location*
                      :text "TEST takes a single Lisp form as argument"))
             form)))
    (let* ((form (extract-test-pattern))
           (bindings (collect-bindings form)))
      (make-parsed-pattern :test-bindings bindings
                           :type :test
                           :slots form
                           :pattern-binding nil
                           :binding-set (make-binding-set)
                           :logical *in-logical-pattern-p*
                           :address location))))

(defun parse-exists-pattern (pattern location)
  (let ((pattern (parse-generic-pattern (second pattern) location)))
    (setf (parsed-pattern-type pattern) :existential)
    pattern))

(defun parse-not-pattern (pattern location)
  (let ((pattern (parse-generic-pattern (second pattern) location)))
    (setf (parsed-pattern-type pattern) :negated)
    pattern))

;;; High-level rule definition interfaces...

(defun define-rule (name body &key (salience 0) (context nil) (auto-focus nil) (belief nil))
  (let ((*current-defrule* name))
    (with-rule-components ((doc-string lhs rhs) body)
      (make-rule name (inference-engine) lhs rhs
                 :doc-string doc-string
                 :salience salience
                 :context context
                 :belief belief
                 :auto-focus auto-focus))))

(defun redefine-defrule (name body &key (salience 0) (context nil) (belief nil) (auto-focus nil))
  (define-rule name body :salience salience
               :context context
               :belief belief
               :auto-focus auto-focus))

;;; File: fact-parser.lisp

(defun create-template-class-slots (class-name slot-list)
  (labels ((determine-default (default-form)
             (unless (and (consp default-form)
                          (eq (first default-form) 'default)
                          (= (length default-form) 2))
               (error 'class-parsing-error
                      :class-name class-name
                      :text "malformed DEFAULT keyword"))
             (second default-form))
           (build-one-slot (template)
             (destructuring-bind (keyword slot-name &optional default)
                 template
               (unless (eq keyword 'slot)
                 (error 'class-parsing-error
                        :class-name class-name
                        :text "unrecognized keyword: ~A" keyword))
               `(,slot-name
                 :initarg ,(intern (symbol-name slot-name) 'keyword)
                 :initform
                 ,(if (null default) nil (determine-default default))
                 :reader 
                 ,(intern (format nil "~S-~S" class-name slot-name))))))
    (mapcar #'build-one-slot slot-list)))

(defun redefine-deftemplate (class-name body)
  (let ((class (gensym)))
    `(let ((,class
            (defclass ,class-name (inference-engine-object)
              ,@(list (create-template-class-slots class-name body)))))
       ,class)))

(defun bind-logical-dependencies (fact)
  (add-logical-dependency 
   (inference-engine) fact 
   (make-dependency-set (active-tokens) (rule-logical-marker (active-rule))))
  fact)
  
(defun parse-and-insert-instance (instance &key (belief nil))
  (ensure-meta-data-exists (class-name (class-of instance)))
  (let ((fact
         (make-fact-from-instance (class-name (class-of instance)) instance)))
    (when (and (in-rule-firing-p)
               (logical-rule-p (active-rule)))
      (bind-logical-dependencies fact))
    (assert-fact (inference-engine) fact :belief belief)))

(defun parse-and-retract-instance (instance engine)
  (retract-fact engine instance))

(defun show-deffacts (deffact)
  (format t "~S~%" deffact)
  (values deffact))

(defun parse-and-insert-deffacts (name body)
  (let ((deffacts (gensym)))
    `(let ((,deffacts (list)))
       (dolist (fact ',body)
         (let ((head (first fact)))
           (ensure-meta-data-exists head)
           (push 
            (apply #'make-fact head (rest fact))
            ,deffacts)))
       (add-autofact (inference-engine) (make-deffacts ',name (nreverse ,deffacts))))))
       
;;; File: language.lisp
;;; Description: Code that implements the Lisa programming language.

(defmacro defrule (name (&key (salience 0) (context nil) (belief nil) (auto-focus nil)) &body body)
  (let ((rule-name (gensym)))
    `(let ((,rule-name ,@(if (consp name) `(,name) `(',name))))
       (redefine-defrule ,rule-name
                         ',body
                         :salience ,salience
                         :context ,context
                         :belief ,belief
                         :auto-focus ,auto-focus))))

(defun undefrule (rule-name)
  (with-rule-name-parts (context short-name long-name) rule-name
    (forget-rule (inference-engine) long-name)))

(defmacro deftemplate (name (&key) &body body)
  (redefine-deftemplate name body))

(defmacro defcontext (context-name &optional (strategy nil))
  `(unless (find-context (inference-engine) ,context-name nil)
     (register-new-context (inference-engine) 
                           (make-context ,context-name :strategy ,strategy))))

(defmacro undefcontext (context-name)
  `(forget-context (inference-engine) ,context-name))

(defun focus-stack ()
  (rete-focus-stack (inference-engine)))

(defun focus (&rest args)
  (if (null args)
      (current-context (inference-engine))
    (dolist (context-name (reverse args) (focus-stack))
      (push-context
       (inference-engine) 
       (find-context (inference-engine) context-name)))))

(defun refocus ()
  (pop-context (inference-engine)))

(defun contexts ()
  (let ((contexts (retrieve-contexts (inference-engine))))
    (dolist (context contexts)
      (format t "~S~%" context))
    (format t "For a total of ~D context~:P.~%" (length contexts))
    (values)))

(defun dependencies ()
  (maphash #'(lambda (dependent-fact dependencies)
               (format *trace-output* "~S:~%" dependent-fact)
               (format *trace-output* "  ~S~%" dependencies))
           (rete-dependency-table (inference-engine)))
  (values))

(defun expand-slots (body)
  (mapcar #'(lambda (pair)
              (destructuring-bind (name value) pair
                `(list (identity ',name) 
                       (identity 
                        ,@(if (quotablep value)
                              `(',value)
                            `(,value))))))
          body))

;;; todo: bug: ASSERT
(defmacro assert ((name &body body) &key (belief nil))
  (let ((fact (gensym))
        (fact-object (gensym)))
    `(let ((,fact-object 
            ,@(if (or (consp name)
                      (variablep name))
                  `(,name)
                `(',name))))
       (if (typep ,fact-object 'standard-object)
           (parse-and-insert-instance ,fact-object :belief ,belief)
         (progn
           (ensure-meta-data-exists ',name)
           (let ((,fact (make-fact ',name ,@(expand-slots body))))
             (when (and (in-rule-firing-p)
                        (logical-rule-p (active-rule)))
               (bind-logical-dependencies ,fact))
             (assert-fact (inference-engine) ,fact :belief ,belief)))))))

(defmacro deffacts (name (&key &allow-other-keys) &body body)
  (parse-and-insert-deffacts name body))

(defun engine ()
  (active-engine))

(defun rule ()
  (active-rule))

(defun assert-instance (instance)
  (parse-and-insert-instance instance))

(defun retract-instance (instance)
  (parse-and-retract-instance instance (inference-engine)))

(defun facts ()
  (let ((facts (get-fact-list (inference-engine))))
    (dolist (fact facts)
      (format t "~S~%" fact))
    (format t "For a total of ~D fact~:P.~%" (length facts))
    (values)))

(defun rules (&optional (context-name nil))
  (let ((rules (get-rule-list (inference-engine) context-name)))
    (dolist (rule rules)
      (format t "~S~%" rule))
    (format t "For a total of ~D rule~:P.~%" (length rules))
    (values)))

(defun agenda (&optional (context-name nil))
  (let ((activations 
         (get-activation-list (inference-engine) context-name)))
    (dolist (activation activations)
      (format t "~S~%" activation))
    (format t "For a total of ~D activation~:P.~%" (length activations))
    (values)))

(defun reset ()
  (reset-engine (inference-engine)))

(defun clear ()
  (clear-system-environment))

(defun run (&optional (contexts nil))
  (unless (null contexts)
    (apply #'focus contexts))
  (run-engine (inference-engine)))

(defun walk (&optional (step 1))
  (run-engine (inference-engine) step))

(defmethod retract ((fact-object fact))
  (retract-fact (inference-engine) fact-object))

(defmethod retract ((fact-object number))
  (retract-fact (inference-engine) fact-object))

(defmethod retract ((fact-object t))
  (parse-and-retract-instance fact-object (inference-engine)))

(defmacro modify (fact &body body)
  `(modify-fact (inference-engine) ,fact ,@(expand-slots body)))

(defun watch (event)
  (watch-event event))

(defun unwatch (event)
  (unwatch-event event))

(defun watching ()
  (let ((watches (watches)))
    (format *trace-output* "Watching ~A~%"
            (if watches watches "nothing"))
    (values)))

(defun halt ()
  (halt-engine (inference-engine)))

(defun mark-instance-as-changed (instance &key (slot-id nil)) 
  (mark-clos-instance-as-changed (inference-engine) instance slot-id))

;;; File: tms-support.lisp
;;; Description: Support functions for LISA's Truth Maintenance System (TMS).

(defvar *scheduled-dependencies*)

;;; bug: todo:
(define-symbol-macro scheduled-dependencies *scheduled-dependencies*)

(defun add-logical-dependency (rete fact dependency-set)
  (setf (gethash dependency-set (rete-dependency-table rete))
        (push fact (gethash dependency-set (rete-dependency-table rete)))))

(defun find-logical-dependencies (rete dependency-set)
  (gethash dependency-set (rete-dependency-table rete)))

(defun make-dependency-set (tokens marker)
  (let ((dependencies (list)))
    (loop for i from 1 to marker
          do (push (token-find-fact tokens i) dependencies))
    (nreverse dependencies)))

(defun schedule-dependency-removal (dependency-set)
  (push dependency-set scheduled-dependencies))

(defmacro with-truth-maintenance ((rete) &body body)
  (let ((rval (gensym)))
    `(let* ((*scheduled-dependencies* (list))
            (,rval
              (progn ,@body)))
       (dolist (dependency scheduled-dependencies)
         (with-accessors ((table rete-dependency-table)) ,rete
           (dolist (dependent-fact
                    (gethash dependency table)
                    (remhash dependency table))
             (retract-fact ,rete dependent-fact))))
       ,rval)))

;;; File: rete.lisp
;;; Description: Class representing the inference engine itself.

(defclass rete ()
  ((fact-table :initform (make-hash-table :test #'equalp)
               :accessor rete-fact-table)
   (fact-id-table :initform (make-hash-table)
                  :accessor fact-id-table)
   (instance-table :initform (make-hash-table)
                   :reader rete-instance-table)
   (rete-network :initform (make-rete-network)
                 :reader rete-network)
   (next-fact-id :initform -1
                 :accessor rete-next-fact-id)
   (autofacts :initform (list)
              :accessor rete-autofacts)
   (meta-data :initform (make-hash-table)
              :reader rete-meta-data)
   (dependency-table :initform (make-hash-table :test #'equal)
                     :accessor rete-dependency-table)
   (contexts :initform (make-hash-table :test #'equal)
             :reader rete-contexts)
   (focus-stack :initform (list)
                :accessor rete-focus-stack)
   (halted :initform nil
           :accessor rete-halted)
   (firing-count :initform 0
                 :accessor rete-firing-count)))

(defmethod initialize-instance :after ((self rete) &rest initargs)
  (declare (ignore initargs))
  (register-new-context self (make-context :initial-context))
  (reset-focus-stack self)
  self)

;;; FACT-META-OBJECT represents data about facts. Every Lisa fact is backed by
;;; a CLOS instance that was either defined by the application or internally
;;; by Lisa (via DEFTEMPLATE).

(defstruct fact-meta-object
  (class-name nil :type symbol)
  (slot-list nil :type list)
  (superclasses nil :type list))

(defun register-meta-object (rete key meta-object)
  (setf (gethash key (rete-meta-data rete)) meta-object))

(defun find-meta-object (rete symbolic-name)
  (gethash symbolic-name (rete-meta-data rete)))

(defun rete-fact-count (rete)
  (hash-table-count (rete-fact-table rete)))

(defun find-rule (rete rule-name)
  (with-rule-name-parts (context-name short-name long-name) rule-name
    (find-rule-in-context (find-context rete context-name) long-name)))

(defun add-rule-to-network (rete rule patterns)
  (flet ((load-facts (network)
           (maphash #'(lambda (key fact)
                        (declare (ignore key))
                        (add-fact-to-network network fact))
                    (rete-fact-table rete))))
    (when (find-rule rete (rule-name rule))
      (forget-rule rete rule))
    (if (zerop (rete-fact-count rete))
        (compile-rule-into-network (rete-network rete) patterns rule)
      (merge-rule-into-network 
       (rete-network rete) patterns rule :loader #'load-facts))
    (add-rule-to-context (rule-context rule) rule)
    rule))

(defmethod forget-rule ((self rete) (rule-name symbol))
  (flet ((disable-activations (rule)
           (mapc #'(lambda (activation)
                     (setf (activation-eligible activation) nil))
                 (find-all-activations
                  (context-strategy (rule-context rule)) rule))))
    (let ((rule (find-rule self rule-name)))
      (cl:assert (not (null rule)) nil
        "The rule named ~S is not known to be defined." rule-name)
      (remove-rule-from-network (rete-network self) rule)
      (remove-rule-from-context (rule-context rule) rule)
      (disable-activations rule)
      rule)))

(defmethod forget-rule ((self rete) (rule rule))
  (forget-rule self (rule-name rule)))

(defmethod forget-rule ((self rete) (rule-name string))
  (forget-rule self (find-symbol rule-name)))

(defun remember-fact (rete fact)
  (with-accessors ((fact-table rete-fact-table)
                   (id-table fact-id-table)) rete
    (setf (gethash (hash-key fact) fact-table) fact)
    (setf (gethash (fact-id fact) id-table) fact)))

(defun forget-fact (rete fact)
  (with-accessors ((fact-table rete-fact-table)
                   (id-table fact-id-table)) rete
    (remhash (hash-key fact) fact-table)
    (remhash (fact-id fact) id-table)))

(defun find-fact-by-id (rete fact-id)
  (gethash fact-id (fact-id-table rete)))

(defun find-fact-by-name (rete fact-name)
  (gethash fact-name (rete-fact-table rete)))

(defun forget-all-facts (rete)
  (clrhash (rete-fact-table rete))
  (clrhash (fact-id-table rete)))

(defun get-fact-list (rete)
  (delete-duplicates
   (sort
    (loop for fact being the hash-values of (rete-fact-table rete)
        collect fact)
    #'(lambda (f1 f2) (< (fact-id f1) (fact-id f2))))))

(defun duplicate-fact-p (rete fact)
  (let ((f (gethash (hash-key fact) (rete-fact-table rete))))
    (if (and f (equals f fact))
        f
      nil)))

(defmacro ensure-fact-is-unique (rete fact)
  (let ((existing-fact (gensym)))
    `(unless *allow-duplicate-facts*
       (let ((,existing-fact
              (gethash (hash-key ,fact) (rete-fact-table ,rete))))
         (unless (or (null ,existing-fact)
                     (not (equals ,fact ,existing-fact)))
           (error (make-condition 'duplicate-fact :existing-fact ,existing-fact)))))))
  
(defmacro with-unique-fact ((rete fact) &body body)
  (let ((body-fn (gensym))
        (existing-fact (gensym)))
    `(flet ((,body-fn ()
              ,@body))
       (if *allow-duplicate-facts*
           (,body-fn)
         (let ((,existing-fact (duplicate-fact-p ,rete ,fact)))
           (if (not ,existing-fact)
               (,body-fn)
             (error (make-condition 'duplicate-fact
                                    :existing-fact ,existing-fact))))))))
  
(defun next-fact-id (rete)
  (incf (rete-next-fact-id rete)))

(defun add-autofact (rete deffact)
  (pushnew deffact (rete-autofacts rete) :key #'deffacts-name))

(defun remove-autofacts (rete)
  (setf (rete-autofacts rete) nil))

(defun assert-autofacts (rete)
  (mapc #'(lambda (deffact)
            (mapc #'(lambda (fact)
                      (assert-fact rete (make-fact-from-template fact)))
                  (deffacts-fact-list deffact)))
        (rete-autofacts rete)))

(defmethod assert-fact-aux ((self rete) fact)
  (with-truth-maintenance (self)
    (setf (fact-id fact) (next-fact-id self))
    (remember-fact self fact)
    (trace-assert fact)
    (add-fact-to-network (rete-network self) fact)
    (when (fact-shadowsp fact)
      (register-clos-instance self (find-instance-of-fact fact) fact)))
  fact)
  
(defmethod adjust-belief (rete fact (belief-factor number))
   (with-unique-fact (rete fact)
     (setf (belief-factor fact) belief-factor)))

(defmethod adjust-belief (rete fact (belief-factor t))
  (declare (ignore rete))
  (when (in-rule-firing-p)
    (let ((rule-belief (belief-factor (active-rule)))
          (facts (token-make-fact-list *active-tokens*)))
      (setf (belief-factor fact) (belief:adjust-belief facts rule-belief (belief-factor fact))))))

(defmethod assert-fact ((self rete) fact &key belief)
  (let ((duplicate (duplicate-fact-p self fact)))
    (cond (duplicate
           (adjust-belief self duplicate belief))
          (t
           (adjust-belief self fact belief)
           (assert-fact-aux self fact)))
    (if duplicate duplicate fact)))

(defmethod retract-fact ((self rete) (fact fact))
  (with-truth-maintenance (self)
    (forget-fact self fact)
    (trace-retract fact)
    (remove-fact-from-network (rete-network self) fact)
    (when (fact-shadowsp fact)
      (forget-clos-instance self (find-instance-of-fact fact)))
    fact))

(defmethod retract-fact ((self rete) (instance standard-object))
  (let ((fact (find-fact-using-instance self instance)))
    (cl:assert (not (null fact)) nil
      "This CLOS instance is unknown to LISA: ~S" instance)
    (retract-fact self fact)))

(defmethod retract-fact ((self rete) (fact-id integer))
  (let ((fact (find-fact-by-id self fact-id)))
    (and (not (null fact))
         (retract-fact self fact))))

(defmethod modify-fact ((self rete) fact &rest slot-changes)
  (retract-fact self fact)
  (mapc #'(lambda (slot)
            (set-slot-value fact (first slot) (second slot)))
        slot-changes)
  (assert-fact self fact)
  fact)

(defun clear-contexts (rete)
  (loop for context being the hash-values of (rete-contexts rete)
      do (clear-activations context)))

(defun clear-focus-stack (rete)
  (setf (rete-focus-stack rete) (list)))

(defun initial-context (rete)
  (find-context rete :initial-context))

(defun reset-focus-stack (rete)
  (setf (rete-focus-stack rete)
    (list (initial-context rete))))

(defun set-initial-state (rete)
  (forget-all-facts rete)
  (clear-contexts rete)
  (reset-focus-stack rete)
  (setf (rete-next-fact-id rete) -1)
  (setf (rete-firing-count rete) 0)
  t)

(defmethod reset-engine ((self rete))
  (reset-network (rete-network self))
  (set-initial-state self)
  (assert (initial-fact))
  (assert-autofacts self)
  t)

(defun get-rule-list (rete &optional (context-name nil))
  (if (null context-name)
      (loop for context being the hash-values of (rete-contexts rete)
          append (context-rule-list context))
    (context-rule-list (find-context rete context-name))))

(defun get-activation-list (rete &optional (context-name nil))
  (if (not context-name)
      (loop for context being the hash-values of (rete-contexts rete)
            for activations = (context-activation-list context)
            when activations
              nconc activations)
    (context-activation-list (find-context rete context-name))))

(defun find-fact-using-instance (rete instance)
  (gethash instance (rete-instance-table rete)))

(defun register-clos-instance (rete instance fact)
  (setf (gethash instance (rete-instance-table rete)) fact))

(defun forget-clos-instance (rete instance)
  (remhash instance (rete-instance-table rete)))

(defun forget-clos-instances (rete)
  (clrhash (rete-instance-table rete)))

(defmethod mark-clos-instance-as-changed ((self rete) instance
                                          &optional (slot-id nil))
  (let ((fact (find-fact-using-instance self instance))
        (network (rete-network self)))
    (cond ((null fact)
           (warn "This instance is not known to Lisa: ~S." instance))
          (t
           (remove-fact-from-network network fact)
           (synchronize-with-instance fact slot-id)
           (add-fact-to-network network fact)))
    instance))

(defun find-context (rete defined-name &optional (errorp t))
  (let ((context
         (gethash (make-context-name defined-name) (rete-contexts rete))))
    (if (and (null context) errorp)
        (error "There's no context named: ~A" defined-name)
      context)))

(defun register-new-context (rete context)
  (setf (gethash (context-name context) (rete-contexts rete)) context))

(defun forget-context (rete context-name)
  (let ((context (find-context rete context-name)))
    (dolist (rule (context-rule-list context))
      (forget-rule rete rule))
    (remhash context-name (rete-contexts rete))
    context))

(defun current-context (rete)
  (first (rete-focus-stack rete)))

(defun next-context (rete)
  (with-accessors ((focus-stack rete-focus-stack)) rete
    (pop focus-stack)
    (setf *active-context* (first focus-stack))))

(defun starting-context (rete)
  (first (rete-focus-stack rete)))

(defun push-context (rete context)
  (push context (rete-focus-stack rete))
  (setf *active-context* context))

(defun pop-context (rete)
  (next-context rete))

(defun retrieve-contexts (rete)
  (loop for context being the hash-values of (rete-contexts rete)
      collect context))

(defmethod add-activation ((self rete) activation)
  (let ((rule (activation-rule activation)))
    (trace-enable-activation activation)
    (add-activation (conflict-set rule) activation)
    (when (auto-focus-p rule)
      (push-context self (rule-context rule)))))

(defmethod disable-activation ((self rete) activation)
  (when (eligible-p activation)
    (trace-disable-activation activation)
    (setf (activation-eligible activation) nil))
  activation)

(defmethod run-engine ((self rete) &optional (step -1))
  (with-context (starting-context self)
    (setf (rete-halted self) nil)
    (do ((count 0))
        ((or (= count step) (rete-halted self)) count)
      (let ((activation 
             (next-activation (conflict-set (active-context)))))
        (cond ((null activation)
               (next-context self)
               (when (null (active-context))
                 (reset-focus-stack self)
                 (halt-engine self)))
              ((eligible-p activation)
               (incf (rete-firing-count self))
               (fire-activation activation)
               (incf count)))))))

(defun halt-engine (rete)
  (setf (rete-halted rete) t))

(defun make-rete ()
  (make-instance 'rete))

(defun make-inference-engine ()
  (make-rete))

(defun copy-network (engine)
  (let ((new-engine (make-inference-engine)))
    (mapc #'(lambda (rule)
              (copy-rule rule new-engine))
          (get-rule-list engine))
    new-engine))

(defun make-query-engine (source-rete)
  (let* ((query-engine (make-inference-engine)))
    (loop for fact being the hash-values of (rete-fact-table source-rete)
        do (remember-fact query-engine fact))
    query-engine))

;;; File: belief-interface.lisp

(defmethod belief:belief-factor ((self fact))
  (belief-factor self))

(defmethod belief:belief-factor ((self rule))
  (belief-factor self))

;;; File: meta.lisp
;;; Description: Meta operations that LISA uses to support the manipulation of
;;; facts and instances.

(defun get-class-name (meta-object)
  (fact-meta-object-class-name meta-object))

(defun get-slot-list (meta-object)
  (fact-meta-object-slot-list meta-object))

(defun get-superclasses (meta-object)
  (fact-meta-object-superclasses meta-object))

(defun find-meta-fact (symbolic-name &optional (errorp t))
  "Locates the META-FACT instance associated with SYMBOLIC-NAME. If ERRORP is
  non-nil, signals an error if no binding is found."
  (let ((meta-fact (find-meta-object (inference-engine) symbolic-name)))
    (when errorp
      (cl:assert (not (null meta-fact)) nil
        "This fact name does not have a registered meta class: ~S"
        symbolic-name))
    meta-fact))

;;; Corrected version courtesy of Aneil Mallavarapu...

(defun acquire-meta-data (actual-name)
  (labels ((build-meta-object (class all-superclasses) ;  NEW LINE (AM 9/19/03)
             (let* ((class-name (class-name class))
                    (meta-data
                     (make-fact-meta-object
                      :class-name class-name
                      :slot-list (reflect:class-slot-list class)
                      :superclasses all-superclasses))) ; new line (AM 9/19/03)
               (register-meta-object (inference-engine) class-name meta-data)
               meta-data))
           (examine-class (class-object)
             (let ((superclasses
                    (if *consider-taxonomy-when-reasoning*
                        (reflect:class-all-superclasses class-object) ; NEW LINE (AM 9/19/03)
                      nil)))
               (build-meta-object class-object superclasses)
               (dolist (super superclasses)
                 (examine-class super)))))
    (examine-class (find-class actual-name))))

;;; Corrected version courtesy of Aneil Mallavarapu...

(defun import-class-specification (class-name)
  (labels ((import-class-object (class-object) ; defined this internal function
             (let ((class-symbols (list class-name)))
               (dolist (slot-name (reflect:class-slot-list class-object))
                 (push slot-name class-symbols))
               (import class-symbols)
               (when *consider-taxonomy-when-reasoning*
                 (dolist (ancestor (reflect:find-direct-superclasses class-object))
                   (import-class-object ancestor))) ; changed to import-class-object
               class-object)))
    (import-class-object (find-class class-name))))

;;; todo: bug:
(defun ensure-meta-data-exists (class-name)
  (flet ((ensure-class-definition ()
           (loop
             (when (find-class class-name nil)
               (acquire-meta-data class-name)
               (return))
             (cerror "Enter a template definition now."
                     "LISA doesn't know about the template named by (~S)." class-name)
             (format t "Enter a DEFTEMPLATE form: ")
             (eval (read))
             (fresh-line))))
    (let ((meta-data (find-meta-object (inference-engine) class-name)))
      (when (null meta-data)
        (ensure-class-definition)
        (setf meta-data 
          (find-meta-object (inference-engine) class-name)))
      meta-data)))

;;; File: binding.lisp

(defstruct (binding
            (:type list)
            (:constructor %make-binding))
  variable address slot-name)

(defun make-binding (var address slot-name)
  (%make-binding :variable var :address address :slot-name slot-name))

(defun pattern-binding-p (binding)
  (eq (binding-slot-name binding) :pattern))

;;; File: token.lisp

(defclass token ()
  ((facts :initform
          (make-array 0 :adjustable t :fill-pointer t)
          :accessor token-facts)
   (not-counter :initform 0
                :accessor token-not-counter)
   (exists-counter :initform 0
                   :accessor token-exists-counter)
   (hash-code :initform (list)
              :accessor token-hash-code)
   (contents :initform nil
             :reader token-contents)))

(defclass add-token (token) ())
(defclass remove-token (token) ())
(defclass reset-token (token) ())

(defun token-increment-exists-counter (token)
  (incf (token-exists-counter token)))

;;; bug: assert
(defun token-decrement-exists-counter (token)
  (cl:assert (plusp (token-exists-counter token)) nil
    "The EXISTS join node logic is busted.")
  (decf (token-exists-counter token)))

(defun token-increment-not-counter (token)
  (values token (incf (token-not-counter token))))

(defun token-decrement-not-counter (token)
  (cl:assert (plusp (token-not-counter token)) nil
    "The negated join node logic is busted.")
  (values token (decf (token-not-counter token))))

(defun token-negated-p (token)
  (plusp (token-not-counter token)))

(defun token-make-fact-list (token &key (detailp t) (debugp nil))
  (let* ((facts (list))
         (vector (token-facts token))
         (length (length vector)))
    (dotimes (i length)
      (let ((fact (aref vector i)))
        (if debugp
            (push fact facts)
          (when (typep fact 'fact)
            (push (if detailp fact (fact-symbolic-id fact)) 
                  facts)))))
    (nreverse facts)))

(defun token-fact-count (token)
  (length (token-facts token)))

(defun token-find-fact (token address)
  (aref (slot-value token 'facts) address))

(defun token-top-fact (token)
  (with-slots ((fact-vector facts)) token
    (aref fact-vector (1- (length fact-vector)))))

(defun token-push-fact (token fact)
  (with-accessors ((fact-vector token-facts)
                   (hash-code token-hash-code)) token
    (vector-push-extend fact fact-vector)
    (push fact hash-code)
    token))

(defun token-pop-fact (token)
  (with-accessors ((fact-vector token-facts)
                   (hash-code token-hash-code)) token
    (unless (zerop (fill-pointer fact-vector))
      (pop hash-code)
      (aref fact-vector (decf (fill-pointer fact-vector))))))

(defun replicate-token (token &key (token-class nil))
  (let ((new-token 
         (make-instance (if token-class
                            (find-class token-class)
                          (class-of token)))))
    (with-slots ((existing-fact-vector facts)) token
      (let ((length (length existing-fact-vector)))
        (dotimes (i length)
          (token-push-fact new-token (aref existing-fact-vector i)))))
    new-token))

(defmethod hash-key ((self token))
  (token-hash-code self))

(defmethod make-add-token ((fact fact))
  (token-push-fact (make-instance 'add-token) fact))

(defmethod make-remove-token ((fact fact))
  (token-push-fact (make-instance 'remove-token) fact))

(defmethod make-remove-token ((token token))
  (replicate-token token :token-class 'remove-token))

(defmethod make-reset-token ((fact t))
  (token-push-fact (make-instance 'reset-token) t))


;;; File: retrieve.lisp

(defvar *query-result* nil
  "Holds the results of query firings.")

;;; bug: todo: LISA ASSERT
(defun run-query (query-rule)
  "Runs a query (RULE instance), and returns both the value of *QUERY-RESULT*
  and the query name itself."
  ;;(declare (ignorable query-rule))
  (let ((*query-result* (list)))
    (assert (query-fact))
    (run)
    *query-result*))

(defmacro defquery (name &body body)
  "Defines a new query identified by the symbol NAME."
  `(define-rule ,name ',body))

;;; Queries fired by RETRIEVE collect their results in the special variable
;;; *QUERY-RESULT*. As an example, one firing of this query, 
;;;
;;;   (retrieve (?x ?y) 
;;;     (?x (rocky (name ?name)))
;;;     (?y (hobbit (name ?name))))
;;;
;;; will produce a result similar to,
;;;
;;; (((?X . #<ROCKY @ #x7147b70a>) (?Y . #<HOBBIT @ #x7147b722>)))

(defmacro retrieve ((&rest varlist) &body body)
  (flet ((make-query-binding (var)
           `(cons ',var ,var)))
    (let ((query-name (gensym))
          (query (gensym)))
      `(with-inference-engine
          ((make-query-engine (inference-engine)))
         (let* ((,query-name (gensym))
                (,query
                 (defquery ',query-name
                           (query-fact)
                           ,@body
                           =>
                           (push (list ,@(mapcar #'(lambda (var)
                                                     var)
                                                 varlist))
                                 *query-result*))))
           (run-query ,query))))))

(defmacro with-simple-query ((var value) query &body body)
  "For each variable/instance pair in a query result, invoke BODY with VAR
  bound to the query variable and VALUE bound to the instance."
  (let ((result (gensym)))
    `(let ((,result ,query))
       (dolist (match ,result)
         (dolist (binding match)
           (let ((,var (car binding))
                 (,value (cdr binding)))
             ,@body))))))


;;; EOF
